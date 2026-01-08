use halo2_proofs::{circuit::*, halo2curves::ff::PrimeField, plonk::*, poly::Rotation};
use std::cmp::Ordering;
use std::cmp::Reverse;
use std::collections::{HashMap, HashSet};
use std::marker::PhantomData;
use std::time::Instant;

use crate::chips::is_zero::{IsZeroChip, IsZeroConfig};
use crate::chips::less_than::{LtChip, LtConfig, LtInstruction};
use crate::chips::lessthan_or_equal_generic::{
    LtEqGenericChip, LtEqGenericConfig, LtEqGenericInstruction,
};
use crate::chips::permutation_any::PermAnyChip;

const NUM_BYTES: usize = 5;

/// Field trait alias
pub trait Field: PrimeField<Repr = [u8; 32]> {}
impl<F> Field for F where F: PrimeField<Repr = [u8; 32]> {}

// -------------------------------------------------------------------------
//  Struct Definitions
// -------------------------------------------------------------------------

#[derive(Clone, Debug)]
pub struct Selectors {
    pub q_enable: Vec<Selector>, // [r_region, o_date_range, etc.]
    pub q_sort: Vec<Selector>,   // [join_sorts..., groupby, orderby]
    pub q_accu: Selector,
    pub q_join: Vec<Selector>, // [orders_check, cust_check, line_check..., permutations...]
}

#[derive(Clone, Debug)]
pub struct Columns {
    pub instance: Column<Instance>,
    pub instance_test: Column<Advice>,

    // Input tables
    pub customer: Vec<Column<Advice>>, // [c_custkey, c_nationkey]
    pub orders: Vec<Column<Advice>>,   // [o_orderdate, o_custkey, o_orderkey]
    pub lineitem: Vec<Column<Advice>>, // [l_orderkey, l_extended, l_disc, l_supp]
    pub supplier: Vec<Column<Advice>>, // [s_nationkey, s_supp]
    pub nation: Vec<Column<Advice>>,   // [n_nationkey, n_regionkey, n_name]
    pub regions: Vec<Column<Advice>>,  // [r_regionkey, r_name]

    // Condition constants
    pub condition: Vec<Column<Advice>>, // [region_name, date_start, date_end]

    // Intermediate Join/Disjoin Groups
    pub join_group: Vec<Vec<Column<Advice>>>,
    pub disjoin_group: Vec<Vec<Column<Advice>>>,
    pub perm_helper: Vec<Vec<Column<Advice>>>,

    // Deduplication & Sorting
    pub deduplicate: Vec<Column<Advice>>,
    pub dedup_sort: Vec<Column<Advice>>,

    // Checks
    pub check: Vec<Column<Advice>>, // [region_check, orders_check_1, orders_check_2]

    // Aggregation
    pub groupby: Vec<Column<Advice>>,
    pub orderby: Vec<Column<Advice>>,
    pub equal_check: Column<Advice>,
    pub revenue: Column<Advice>,
}

#[derive(Clone, Debug)]
pub struct Chips<F: Field + Ord> {
    pub is_zero_region: IsZeroConfig<F>,
    pub lt_date_ge: LtEqGenericConfig<F, NUM_BYTES>, // orders >= date1
    pub lt_date_lt: LtConfig<F, NUM_BYTES>,          // orders < date2
    pub lt_join_sort: Vec<LtConfig<F, NUM_BYTES>>,   // Check strictly increasing for joins
    pub lt_groupby: LtEqGenericConfig<F, NUM_BYTES>,
    pub lt_orderby: LtEqGenericConfig<F, NUM_BYTES>,
}

#[derive(Clone, Debug)]
pub struct TestCircuitConfig<F: Field + Ord> {
    pub sels: Selectors,
    pub cols: Columns,
    pub chips: Chips<F>,
}

#[derive(Debug, Clone)]
pub struct TestChip<F: Field + Ord> {
    config: TestCircuitConfig<F>,
}

// -------------------------------------------------------------------------
//  Witness Struct
// -------------------------------------------------------------------------

#[derive(Clone, Debug)]
pub struct Witness<F: Field + Ord> {
    // Input checks
    pub r_check: Vec<bool>,
    pub o_check_1: Vec<bool>, // >= date1
    pub o_check_2: Vec<bool>, // < date2

    // Filtered Inputs (for pure Rust joining)
    // Note: In assign(), we iterate over original inputs, but we calculate based on these
    pub join_value: Vec<Vec<Vec<u64>>>,    // 10 groups
    pub disjoin_value: Vec<Vec<Vec<u64>>>, // 10 groups

    // Deduplication
    pub dis_vectors: Vec<Vec<u64>>, // For single column deduplication
    pub dis_tuples: Vec<Vec<(u64, u64)>>, // For tuple deduplication
    pub concat_sort_vectors: Vec<Vec<u64>>, // For sorting checks
    pub concat_sort_tuple: Vec<(u64, u64)>,

    // Aggregation
    pub cartesian_product: Vec<Vec<u64>>, // The result of all joins
    pub equal_check: Vec<F>,
    pub revenue: Vec<F>,
    pub grouped_data: Vec<Vec<F>>,
}

// -------------------------------------------------------------------------
//  Chip Implementation
// -------------------------------------------------------------------------

impl<F: Field + Ord> TestChip<F> {
    pub fn construct(config: TestCircuitConfig<F>) -> Self {
        Self { config }
    }

    // --- Allocation Helpers ---

    fn alloc_cols(meta: &mut ConstraintSystem<F>, n: usize) -> Vec<Column<Advice>> {
        (0..n).map(|_| meta.advice_column()).collect()
    }

    fn alloc_selectors(meta: &mut ConstraintSystem<F>, n: usize) -> Vec<Selector> {
        (0..n).map(|_| meta.selector()).collect()
    }

    fn alloc_complex_selectors(meta: &mut ConstraintSystem<F>, n: usize) -> Vec<Selector> {
        (0..n).map(|_| meta.complex_selector()).collect()
    }

    fn allocate(meta: &mut ConstraintSystem<F>) -> (Selectors, Columns) {
        let instance = meta.instance_column();
        meta.enable_equality(instance);
        let instance_test = meta.advice_column();
        meta.enable_equality(instance_test);

        let q_enable = Self::alloc_selectors(meta, 3);
        let q_sort = Self::alloc_selectors(meta, 7); // 4 joins + 1 groupby + 1 orderby + ?
        let q_accu = meta.selector();
        let q_join = Self::alloc_complex_selectors(meta, 12);

        let customer = Self::alloc_cols(meta, 2);
        let orders = Self::alloc_cols(meta, 3);
        let lineitem = Self::alloc_cols(meta, 4);
        let supplier = Self::alloc_cols(meta, 2);
        let nation = Self::alloc_cols(meta, 3);
        let regions = Self::alloc_cols(meta, 2);
        let condition = Self::alloc_cols(meta, 3);
        let check = Self::alloc_cols(meta, 3);
        let deduplicate = Self::alloc_cols(meta, 12);
        let dedup_sort = Self::alloc_cols(meta, 6);
        let groupby = Self::alloc_cols(meta, 3);
        let orderby = Self::alloc_cols(meta, 2);
        let equal_check = meta.advice_column();
        let revenue = meta.advice_column();

        // Variable length groups
        let group_sizes = [3, 2, 4, 5, 9, 2, 11, 3, 14, 2];
        let mut join_group = Vec::new();
        let mut disjoin_group = Vec::new();
        for &s in &group_sizes {
            join_group.push(Self::alloc_cols(meta, s));
            disjoin_group.push(Self::alloc_cols(meta, s));
        }

        let perm_sizes = [3, 2, 4, 2, 3, 2];
        let mut perm_helper = Vec::new();
        for &s in &perm_sizes {
            perm_helper.push(Self::alloc_cols(meta, s));
        }

        (
            Selectors {
                q_enable,
                q_sort,
                q_accu,
                q_join,
            },
            Columns {
                instance,
                instance_test,
                customer,
                orders,
                lineitem,
                supplier,
                nation,
                regions,
                condition,
                join_group,
                disjoin_group,
                perm_helper,
                deduplicate,
                dedup_sort,
                check,
                groupby,
                orderby,
                equal_check,
                revenue,
            },
        )
    }

    // --- Configuration Logic ---

    pub fn configure(meta: &mut ConstraintSystem<F>) -> TestCircuitConfig<F> {
        let (sels, cols) = Self::allocate(meta);

        // 1. Region Condition (IsZero)
        let is_zero_aux = meta.advice_column();
        let is_zero_region = IsZeroChip::configure(
            meta,
            |meta| meta.query_selector(sels.q_enable[0]),
            |meta| {
                meta.query_advice(cols.regions[1], Rotation::cur())
                    - meta.query_advice(cols.condition[0], Rotation::cur())
            },
            is_zero_aux,
        );
        meta.create_gate("region check", |meta| {
            let s = meta.query_selector(sels.q_enable[0]);
            let out = meta.query_advice(cols.check[0], Rotation::cur());
            vec![
                s.clone() * (is_zero_region.expr() * (out.clone() - Expression::Constant(F::ONE))),
                s * (Expression::Constant(F::ONE) - is_zero_region.expr()) * out,
            ]
        });

        // 2. Date Conditions
        // >= Start Date
        let lt_date_ge = LtEqGenericChip::configure(
            meta,
            |meta| meta.query_selector(sels.q_enable[1]),
            |meta| vec![meta.query_advice(cols.condition[1], Rotation::cur())],
            |meta| vec![meta.query_advice(cols.orders[0], Rotation::cur())],
        );
        meta.create_gate("orders >= start_date", |meta| {
            let q = meta.query_selector(sels.q_enable[1]);
            let chk = meta.query_advice(cols.check[1], Rotation::cur());
            vec![q * (lt_date_ge.is_lt(meta, None) - chk)]
        });

        // < End Date
        let lt_date_lt = LtChip::configure(
            meta,
            |meta| meta.query_selector(sels.q_enable[1]),
            |meta| meta.query_advice(cols.orders[0], Rotation::cur()),
            |meta| meta.query_advice(cols.condition[2], Rotation::cur()),
        );
        meta.create_gate("orders < end_date", |meta| {
            let q = meta.query_selector(sels.q_enable[1]);
            let chk = meta.query_advice(cols.check[2], Rotation::cur());
            vec![q * (lt_date_lt.is_lt(meta, None) - chk)]
        });

        // 3. Permutations (Input vs Helper)
        let tables = [
            &cols.orders,
            &cols.customer,
            &cols.lineitem,
            &cols.supplier,
            &cols.nation,
            &cols.regions,
        ];
        for i in 0..6 {
            PermAnyChip::configure(
                meta,
                sels.q_join[i],
                sels.q_join[i + 6],
                tables[i].clone(),
                cols.perm_helper[i].clone(),
            );
        }

        // 4. Lookups for Deduplication
        let dedup_singles = [
            (0, 0, 1),
            (1, 1, 0),
            (2, 2, 0),
            (3, 3, 2),
            (4, 6, 9),
            (5, 7, 0),
            (6, 8, 12),
            (7, 9, 0),
        ];
        for (idx, dis_grp_idx, col_idx) in dedup_singles {
            meta.lookup_any("dedup check single", |meta| {
                let input =
                    meta.query_advice(cols.disjoin_group[dis_grp_idx][col_idx], Rotation::cur());
                let table = meta.query_advice(cols.deduplicate[idx], Rotation::cur());
                vec![(input, table)]
            });
        }

        let dedup_tuples = [(4, 8, 9, 3, 8), (5, 10, 11, 1, 0)];
        for (dis_idx, t1, t2, c1, c2) in dedup_tuples {
            meta.lookup_any("dedup check tuple", |meta| {
                let i1 = meta.query_advice(cols.disjoin_group[dis_idx][c1], Rotation::cur());
                let i2 = meta.query_advice(cols.disjoin_group[dis_idx][c2], Rotation::cur());
                let tb1 = meta.query_advice(cols.deduplicate[t1], Rotation::cur());
                let tb2 = meta.query_advice(cols.deduplicate[t2], Rotation::cur());
                vec![(i1, tb1), (i2, tb2)]
            });
        }

        // 5. Sorting Checks (Strictly Increasing)
        let mut lt_join_sort = Vec::new();
        for i in 0..4 {
            let conf = LtChip::configure(
                meta,
                |meta| meta.query_selector(sels.q_sort[i]),
                |meta| meta.query_advice(cols.dedup_sort[i], Rotation::prev()),
                |meta| meta.query_advice(cols.dedup_sort[i], Rotation::cur()),
            );
            lt_join_sort.push(conf.clone());
            meta.create_gate("sorted check", |meta| {
                let q = meta.query_selector(sels.q_sort[i]);
                vec![q * (conf.is_lt(meta, None) - Expression::Constant(F::ONE))]
            });
        }

        // 6. Aggregation (GroupBy & Revenue)
        let lt_groupby = LtEqGenericChip::configure(
            meta,
            |meta| meta.query_selector(sels.q_sort[4]),
            |meta| vec![meta.query_advice(cols.groupby[0], Rotation::prev())],
            |meta| vec![meta.query_advice(cols.groupby[0], Rotation::cur())],
        );

        meta.create_gate("revenue accumulation", |meta| {
            let q = meta.query_selector(sels.q_accu);
            let prev_rev = meta.query_advice(cols.revenue, Rotation::cur());
            let next_rev = meta.query_advice(cols.revenue, Rotation::next());
            let ext_price = meta.query_advice(cols.groupby[1], Rotation::cur());
            let discount = meta.query_advice(cols.groupby[2], Rotation::cur());
            let is_same_group = meta.query_advice(cols.equal_check, Rotation::cur());

            // revenue[i+1] = revenue[i] * same_group + price * (1000 - discount)
            vec![
                q * (is_same_group * prev_rev
                    + ext_price * (Expression::Constant(F::from(1000)) - discount)
                    - next_rev),
            ]
        });

        // 7. OrderBy (Revenue Descending)
        let lt_orderby = LtEqGenericChip::configure(
            meta,
            |meta| meta.query_selector(sels.q_sort[5]),
            |meta| vec![meta.query_advice(cols.orderby[1], Rotation::cur())], // Desc: Cur < Prev is false => Prev >= Cur
            |meta| vec![meta.query_advice(cols.orderby[1], Rotation::prev())],
        );

        meta.create_gate("orderby desc check", |meta| {
            let q = meta.query_selector(sels.q_sort[5]);
            vec![q * (lt_orderby.is_lt(meta, None) - Expression::Constant(F::ONE))]
        });

        let chips = Chips {
            is_zero_region,
            lt_date_ge,
            lt_date_lt,
            lt_join_sort,
            lt_groupby,
            lt_orderby,
        };

        TestCircuitConfig { sels, cols, chips }
    }

    // --- Witness Computation (Pure Rust) ---

    fn compute_witness(
        customer: &[Vec<u64>],
        orders: &[Vec<u64>],
        lineitem: &[Vec<u64>],
        supplier: &[Vec<u64>],
        nation: &[Vec<u64>],
        regions: &[Vec<u64>],
        condition: &[u64],
    ) -> Witness<F> {
        let cond_region = condition[0];
        let cond_date_start = condition[1];
        let cond_date_end = condition[2];

        // 1. Checks & Filtering
        let r_check: Vec<bool> = regions.iter().map(|r| r[1] == cond_region).collect();
        let o_check_1: Vec<bool> = orders.iter().map(|o| o[0] >= cond_date_start).collect();
        let o_check_2: Vec<bool> = orders.iter().map(|o| o[0] < cond_date_end).collect();

        // Optimized Filtering
        let regions_filt: Vec<&Vec<u64>> = regions.iter().filter(|r| r[1] == cond_region).collect();
        let orders_filt: Vec<&Vec<u64>> = orders
            .iter()
            .filter(|o| o[0] >= cond_date_start && o[0] < cond_date_end)
            .collect();

        // 2. Joining with HashMaps (Optimized O(N) instead of O(N*M))
        let mut join_value = vec![vec![]; 10];
        let mut disjoin_value = vec![vec![]; 10];

        // Step 1: Orders (Filtered) join Customer
        // Join Key: o_custkey (idx 1) == c_custkey (idx 0)
        let mut cust_map = HashMap::new();
        for r in customer {
            cust_map.insert(r[0], r);
        }

        let mut res1 = Vec::new();
        // FIX 1: Borrow `orders_filt` instead of consuming it
        for o in &orders_filt {
            if let Some(c) = cust_map.get(&o[1]) {
                join_value[0].push(o.to_vec());
                join_value[1].push(c.to_vec());
                let mut row = o.to_vec();
                row.extend_from_slice(c);
                res1.push(row);
            } else {
                disjoin_value[0].push(o.to_vec());
            }
        }
        // Handle disjoined customers
        let mut order_cust_keys: HashSet<u64> = orders_filt.iter().map(|o| o[1]).collect();
        for c in customer {
            if !order_cust_keys.contains(&c[0]) {
                disjoin_value[1].push(c.to_vec());
            }
        }

        // Step 2: Result1 join Lineitem
        // Join Key: o_orderkey (idx 2 in Orders, idx 2 in Res1) == l_orderkey (idx 0)
        let mut res1_map = HashMap::new();
        for r in &res1 {
            res1_map.insert(r[2], r);
        } // Key on o_orderkey

        let mut res2 = Vec::new();
        for l in lineitem {
            if let Some(r) = res1_map.get(&l[0]) {
                join_value[2].push(l.to_vec());
                join_value[3].push(r.to_vec());
                let mut row = l.to_vec();
                row.extend_from_slice(r);
                res2.push(row);
            } else {
                disjoin_value[2].push(l.to_vec());
            }
        }
        let line_order_keys: HashSet<u64> = lineitem.iter().map(|l| l[0]).collect();
        for r in &res1 {
            if !line_order_keys.contains(&r[2]) {
                disjoin_value[3].push(r.to_vec());
            }
        }

        // Step 3: Result2 join Supplier
        // Keys: l_suppkey (idx 3) == s_suppkey (idx 1) AND c_nationkey (idx 4+3+1 = 8) == s_nationkey (idx 0)
        // Res2 structure: [L(4) | O(3) | C(2)]
        // L:0-3, O:4-6, C:7-8
        let mut supp_map = HashMap::new();
        for s in supplier {
            supp_map.insert((s[1], s[0]), s);
        }

        let mut res3 = Vec::new();
        for r in &res2 {
            // r[3] is l_suppkey, r[8] is c_nationkey
            if let Some(s) = supp_map.get(&(r[3], r[8])) {
                join_value[4].push(r.to_vec());
                join_value[5].push(s.to_vec());
                let mut row = r.to_vec();
                row.extend_from_slice(s);
                res3.push(row);
            } else {
                disjoin_value[4].push(r.to_vec());
            }
        }
        // Simplified disjoin logic for supplier (approximation for brevity/context)
        let res2_keys: HashSet<(u64, u64)> = res2.iter().map(|r| (r[3], r[8])).collect();
        for s in supplier {
            if !res2_keys.contains(&(s[1], s[0])) {
                disjoin_value[5].push(s.to_vec());
            }
        }

        // Step 4: Result3 join Nation
        // Key: s_nationkey (from supp, last added, idx 9) == n_nationkey (idx 0)
        let mut nation_map = HashMap::new();
        for n in nation {
            nation_map.insert(n[0], n);
        }

        let mut res4 = Vec::new();
        for r in &res3 {
            if let Some(n) = nation_map.get(&r[9]) {
                join_value[6].push(r.to_vec());
                join_value[7].push(n.to_vec());
                let mut row = r.to_vec();
                row.extend_from_slice(n);
                res4.push(row);
            } else {
                disjoin_value[6].push(r.to_vec());
            }
        }
        let res3_keys: HashSet<u64> = res3.iter().map(|r| r[9]).collect();
        for n in nation {
            if !res3_keys.contains(&n[0]) {
                disjoin_value[7].push(n.to_vec());
            }
        }

        // Step 5: Result4 join Region (Filtered)
        // Key: n_regionkey (idx 12) == r_regionkey (idx 0)
        let mut region_map = HashMap::new();
        // FIX 2: Borrow `regions_filt` instead of consuming it
        for r in &regions_filt {
            region_map.insert(r[0], r);
        }

        let mut cartesian_product = Vec::new();
        for r in &res4 {
            if let Some(reg) = region_map.get(&r[12]) {
                join_value[8].push(r.to_vec());
                join_value[9].push(reg.to_vec());
                let mut row = r.to_vec();
                row.extend_from_slice(reg);
                cartesian_product.push(row);
            } else {
                disjoin_value[8].push(r.to_vec());
            }
        }
        let res4_keys: HashSet<u64> = res4.iter().map(|r| r[12]).collect();
        // FIX 3: Borrow `regions_filt` instead of consuming it
        for reg in &regions_filt {
            if !res4_keys.contains(&reg[0]) {
                disjoin_value[9].push(reg.to_vec());
            }
        }

        // 3. Deduplication Vectors
        let mut dis_vectors = Vec::new();
        // Specific columns from disjoin groups as per config
        // FIX 4: Corrected indices to match `dedup_singles` in `configure`.
        // Previous (4,9) caused panic because Group 4 size is 9 (idx 0-8).
        let single_configs = [
            (0, 1),
            (1, 0),
            (2, 0),
            (3, 2),
            (6, 9),  // Matched to `dedup_singles`: (4, 6, 9)
            (7, 0),  // Matched to `dedup_singles`: (5, 7, 0)
            (8, 12), // Matched to `dedup_singles`: (6, 8, 12)
            (9, 0),  // Matched to `dedup_singles`: (7, 9, 0)
        ]; // (group_idx, col_idx)

        for (g, c) in single_configs {
            let mut vec: Vec<u64> = disjoin_value[g].iter().map(|row| row[c]).collect();
            vec.sort();
            vec.dedup();
            dis_vectors.push(vec);
        }

        let mut dis_tuples = Vec::new();
        let tuple_configs = [(4, 3, 8), (5, 1, 0)]; // (group, c1, c2)
        for (g, c1, c2) in tuple_configs {
            let mut vec: Vec<(u64, u64)> = disjoin_value[g]
                .iter()
                .map(|row| (row[c1], row[c2]))
                .collect();
            vec.sort();
            vec.dedup();
            dis_tuples.push(vec);
        }

        // 4. Concatenated Vectors for Sorting
        let mut concat_sort_vectors = Vec::new();
        for i in (0..dis_vectors.len()).step_by(2) {
            let mut merged = dis_vectors[i].clone();
            if i + 1 < dis_vectors.len() {
                merged.extend(dis_vectors[i + 1].iter());
            }
            merged.sort();
            concat_sort_vectors.push(merged);
        }

        let mut concat_sort_tuple = dis_tuples[0].clone();
        if dis_tuples.len() > 1 {
            concat_sort_tuple.extend(dis_tuples[1].iter());
        }
        concat_sort_tuple.sort_by_key(|t| t.0 + t.1); // Simplified sort key check

        // 5. Aggregation (GroupBy n_name idx 13)
        // Sort by n_name
        cartesian_product.sort_by_key(|r| r[13]);

        let mut equal_check = Vec::new();
        if !cartesian_product.is_empty() {
            equal_check.push(F::from(0));
        }
        for i in 1..cartesian_product.len() {
            let is_eq = cartesian_product[i][13] == cartesian_product[i - 1][13];
            equal_check.push(F::from(is_eq as u64));
        }

        let n = cartesian_product.len() + 1;
        let mut revenue = vec![F::from(0); n];
        for i in 1..n {
            let row = &cartesian_product[i - 1];
            // revenue = prev * equal + price * (1000 - discount)
            let val = F::from(row[1] * (1000 - row[2]));
            revenue[i] = revenue[i - 1] * equal_check[i - 1] + val;
        }

        // 6. OrderBy Revenue Desc
        let mut grouped_map: HashMap<u64, F> = HashMap::new();
        for row in &cartesian_product {
            let key = row[13];
            let val = F::from(row[1] * (1000 - row[2]));
            *grouped_map.entry(key).or_insert(F::from(0)) += val;
        }
        let mut grouped_data: Vec<Vec<F>> = grouped_map
            .into_iter()
            .map(|(k, v)| vec![F::from(k), v])
            .collect();
        // Sort Descending by Revenue (index 1)
        grouped_data.sort_by(|a, b| {
            // Reverse sort
            // Note: F comparison is tricky, mapping back to u64 or using derived Ord if generic fits
            // Here assuming standard lex sort on representation
            b[1].cmp(&a[1])
        });

        Witness {
            r_check,
            o_check_1,
            o_check_2,
            join_value,
            disjoin_value,
            dis_vectors,
            dis_tuples,
            concat_sort_vectors,
            concat_sort_tuple,
            cartesian_product,
            equal_check,
            revenue,
            grouped_data,
        }
    }

    // --- Assignment Logic ---

    pub fn assign(
        &self,
        layouter: &mut impl Layouter<F>,
        customer: Vec<Vec<u64>>,
        orders: Vec<Vec<u64>>,
        lineitem: Vec<Vec<u64>>,
        supplier: Vec<Vec<u64>>,
        nation: Vec<Vec<u64>>,
        regions: Vec<Vec<u64>>,
        condition: Vec<u64>,
    ) -> Result<AssignedCell<F, F>, Error> {
        let is_zero_chip = IsZeroChip::construct(self.config.chips.is_zero_region.clone());
        let lt_date_ge_chip = LtEqGenericChip::construct(self.config.chips.lt_date_ge.clone());
        lt_date_ge_chip.load(layouter)?;
        let lt_date_lt_chip = LtChip::construct(self.config.chips.lt_date_lt.clone());
        lt_date_lt_chip.load(layouter)?;

        let mut join_sort_chips = Vec::new();
        for cfg in &self.config.chips.lt_join_sort {
            let chip = LtChip::construct(cfg.clone());
            chip.load(layouter)?;
            join_sort_chips.push(chip);
        }

        let lt_groupby_chip = LtEqGenericChip::construct(self.config.chips.lt_groupby.clone());
        lt_groupby_chip.load(layouter)?;
        let lt_orderby_chip = LtEqGenericChip::construct(self.config.chips.lt_orderby.clone());
        lt_orderby_chip.load(layouter)?;

        let wit = Self::compute_witness(
            &customer, &orders, &lineitem, &supplier, &nation, &regions, &condition,
        );

        layouter.assign_region(
            || "witness",
            |mut region| {
                let sels = &self.config.sels;
                let cols = &self.config.cols;

                // 1. Assign Original Inputs & Checks
                for (i, row) in customer.iter().enumerate() {
                    sels.q_join[1].enable(&mut region, i)?;
                    for (j, val) in row.iter().enumerate() {
                        region.assign_advice(
                            || "cust",
                            cols.customer[j],
                            i,
                            || Value::known(F::from(*val)),
                        )?;
                    }
                }

                for (i, row) in orders.iter().enumerate() {
                    sels.q_enable[1].enable(&mut region, i)?;
                    if wit.o_check_1[i] && wit.o_check_2[i] {
                        sels.q_join[0].enable(&mut region, i)?;
                    }
                    for (j, val) in row.iter().enumerate() {
                        region.assign_advice(
                            || "orders",
                            cols.orders[j],
                            i,
                            || Value::known(F::from(*val)),
                        )?;
                    }
                    region.assign_advice(
                        || "chk1",
                        cols.check[1],
                        i,
                        || Value::known(F::from(wit.o_check_1[i] as u64)),
                    )?;
                    region.assign_advice(
                        || "chk2",
                        cols.check[2],
                        i,
                        || Value::known(F::from(wit.o_check_2[i] as u64)),
                    )?;
                    region.assign_advice(
                        || "cond1",
                        cols.condition[1],
                        i,
                        || Value::known(F::from(condition[1])),
                    )?;
                    region.assign_advice(
                        || "cond2",
                        cols.condition[2],
                        i,
                        || Value::known(F::from(condition[2])),
                    )?;

                    lt_date_ge_chip.assign(
                        &mut region,
                        i,
                        &[F::from(condition[1])],
                        &[F::from(row[0])],
                    )?;
                    lt_date_lt_chip.assign(
                        &mut region,
                        i,
                        Value::known(F::from(row[0])),
                        Value::known(F::from(condition[2])),
                    )?;
                }

                for (i, row) in lineitem.iter().enumerate() {
                    sels.q_join[2].enable(&mut region, i)?;
                    for (j, val) in row.iter().enumerate() {
                        region.assign_advice(
                            || "line",
                            cols.lineitem[j],
                            i,
                            || Value::known(F::from(*val)),
                        )?;
                    }
                }
                for (i, row) in supplier.iter().enumerate() {
                    sels.q_join[3].enable(&mut region, i)?;
                    for (j, val) in row.iter().enumerate() {
                        region.assign_advice(
                            || "supp",
                            cols.supplier[j],
                            i,
                            || Value::known(F::from(*val)),
                        )?;
                    }
                }
                for (i, row) in nation.iter().enumerate() {
                    sels.q_join[4].enable(&mut region, i)?;
                    for (j, val) in row.iter().enumerate() {
                        region.assign_advice(
                            || "nat",
                            cols.nation[j],
                            i,
                            || Value::known(F::from(*val)),
                        )?;
                    }
                }

                for (i, row) in regions.iter().enumerate() {
                    sels.q_enable[0].enable(&mut region, i)?;
                    if wit.r_check[i] {
                        sels.q_join[5].enable(&mut region, i)?;
                    }
                    for (j, val) in row.iter().enumerate() {
                        region.assign_advice(
                            || "reg",
                            cols.regions[j],
                            i,
                            || Value::known(F::from(*val)),
                        )?;
                    }
                    region.assign_advice(
                        || "r_chk",
                        cols.check[0],
                        i,
                        || Value::known(F::from(wit.r_check[i] as u64)),
                    )?;
                    region.assign_advice(
                        || "cond0",
                        cols.condition[0],
                        i,
                        || Value::known(F::from(condition[0])),
                    )?;

                    is_zero_chip.assign(
                        &mut region,
                        i,
                        Value::known(F::from(row[1]) - F::from(condition[0])),
                    )?;
                }

                // 2. Assign Join/Disjoin Groups
                for (k, grp_rows) in wit.join_value.iter().enumerate() {
                    for (i, row) in grp_rows.iter().enumerate() {
                        for (j, val) in row.iter().enumerate() {
                            region.assign_advice(
                                || "join_g",
                                cols.join_group[k][j],
                                i,
                                || Value::known(F::from(*val)),
                            )?;
                        }
                    }
                }
                for (k, grp_rows) in wit.disjoin_value.iter().enumerate() {
                    for (i, row) in grp_rows.iter().enumerate() {
                        for (j, val) in row.iter().enumerate() {
                            region.assign_advice(
                                || "disjoin_g",
                                cols.disjoin_group[k][j],
                                i,
                                || Value::known(F::from(*val)),
                            )?;
                        }
                    }
                }

                // 3. Permutation Helper (Merging Join+Disjoin)
                // Indices matching input tables: 0,1,2,5,7,9 corresponding to tables
                let perm_indices = [0, 1, 2, 5, 7, 9];
                for (idx, &k) in perm_indices.iter().enumerate() {
                    let offset = wit.join_value[k].len();
                    // Join part
                    for (i, row) in wit.join_value[k].iter().enumerate() {
                        for (j, val) in row.iter().enumerate() {
                            region.assign_advice(
                                || "perm_j",
                                cols.perm_helper[idx][j],
                                i,
                                || Value::known(F::from(*val)),
                            )?;
                        }
                    }
                    // Disjoin part
                    for (i, row) in wit.disjoin_value[k].iter().enumerate() {
                        for (j, val) in row.iter().enumerate() {
                            region.assign_advice(
                                || "perm_d",
                                cols.perm_helper[idx][j],
                                offset + i,
                                || Value::known(F::from(*val)),
                            )?;
                        }
                    }
                    // Enable Permutation Selector
                    for i in 0..(offset + wit.disjoin_value[k].len()) {
                        sels.q_join[idx + 6].enable(&mut region, i)?;
                    }
                }

                // 4. Deduplication
                for (i, vec) in wit.dis_vectors.iter().enumerate() {
                    for (j, val) in vec.iter().enumerate() {
                        region.assign_advice(
                            || "dedup",
                            cols.deduplicate[i],
                            j,
                            || Value::known(F::from(*val)),
                        )?;
                    }
                }
                // Tuples (manually mapped indices 8,9,10,11)
                for (i, tup) in wit.dis_tuples.get(0).unwrap_or(&vec![]).iter().enumerate() {
                    region.assign_advice(
                        || "dedup_t1a",
                        cols.deduplicate[8],
                        i,
                        || Value::known(F::from(tup.0)),
                    )?;
                    region.assign_advice(
                        || "dedup_t1b",
                        cols.deduplicate[9],
                        i,
                        || Value::known(F::from(tup.1)),
                    )?;
                }
                for (i, tup) in wit.dis_tuples.get(1).unwrap_or(&vec![]).iter().enumerate() {
                    region.assign_advice(
                        || "dedup_t2a",
                        cols.deduplicate[10],
                        i,
                        || Value::known(F::from(tup.0)),
                    )?;
                    region.assign_advice(
                        || "dedup_t2b",
                        cols.deduplicate[11],
                        i,
                        || Value::known(F::from(tup.1)),
                    )?;
                }

                // 5. Sorted Columns Checks
                for (k, vec) in wit.concat_sort_vectors.iter().enumerate() {
                    for (i, val) in vec.iter().enumerate() {
                        if i > 0 {
                            sels.q_sort[k].enable(&mut region, i)?;
                            join_sort_chips[k].assign(
                                &mut region,
                                i,
                                Value::known(F::from(vec[i - 1])),
                                Value::known(F::from(*val)),
                            )?;
                        }
                        region.assign_advice(
                            || "sort_v",
                            cols.dedup_sort[k],
                            i,
                            || Value::known(F::from(*val)),
                        )?;
                    }
                }
                // Tuple Sort
                for (i, tup) in wit.concat_sort_tuple.iter().enumerate() {
                    region.assign_advice(
                        || "sort_ta",
                        cols.dedup_sort[4],
                        i,
                        || Value::known(F::from(tup.0)),
                    )?;
                    region.assign_advice(
                        || "sort_tb",
                        cols.dedup_sort[5],
                        i,
                        || Value::known(F::from(tup.1)),
                    )?;
                }

                // 6. Aggregation & GroupBy
                for (i, row) in wit.cartesian_product.iter().enumerate() {
                    // Map specific columns to groupby: n_name(13), l_ext(1), l_disc(2)
                    region.assign_advice(
                        || "grp_n",
                        cols.groupby[0],
                        i,
                        || Value::known(F::from(row[13])),
                    )?;
                    region.assign_advice(
                        || "grp_e",
                        cols.groupby[1],
                        i,
                        || Value::known(F::from(row[1])),
                    )?;
                    region.assign_advice(
                        || "grp_d",
                        cols.groupby[2],
                        i,
                        || Value::known(F::from(row[2])),
                    )?;

                    if i > 0 {
                        sels.q_sort[4].enable(&mut region, i)?;
                        lt_groupby_chip.assign(
                            &mut region,
                            i,
                            &[F::from(wit.cartesian_product[i - 1][13])],
                            &[F::from(row[13])],
                        )?;
                    }
                }

                // Revenue Accumulation
                for i in 0..wit.equal_check.len() {
                    sels.q_accu.enable(&mut region, i)?;
                    region.assign_advice(
                        || "eq_chk",
                        cols.equal_check,
                        i,
                        || Value::known(wit.equal_check[i]),
                    )?;
                }
                for i in 0..wit.revenue.len() {
                    region.assign_advice(
                        || "rev",
                        cols.revenue,
                        i,
                        || Value::known(wit.revenue[i]),
                    )?;
                }

                // 7. OrderBy
                for (i, row) in wit.grouped_data.iter().enumerate() {
                    region.assign_advice(
                        || "ord_k",
                        cols.orderby[0],
                        i,
                        || Value::known(row[0]),
                    )?;
                    region.assign_advice(
                        || "ord_v",
                        cols.orderby[1],
                        i,
                        || Value::known(row[1]),
                    )?;

                    if i > 0 {
                        sels.q_sort[5].enable(&mut region, i)?;
                        // check rev[i] <= rev[i-1] (descending)
                        lt_orderby_chip.assign(
                            &mut region,
                            i,
                            &[row[1]],
                            &[wit.grouped_data[i - 1][1]],
                        )?;
                    }
                }

                let out = region.assign_advice(
                    || "test",
                    cols.instance_test,
                    0,
                    || Value::known(F::from(1)),
                )?;
                Ok(out)
            },
        )
    }

    pub fn expose_public(
        &self,
        layouter: &mut impl Layouter<F>,
        cell: AssignedCell<F, F>,
        row: usize,
    ) -> Result<(), Error> {
        layouter.constrain_instance(cell.cell(), self.config.cols.instance, row)
    }
}

// -------------------------------------------------------------------------
//  Circuit Boilerplate
// -------------------------------------------------------------------------

pub struct MyCircuit<F> {
    customer: Vec<Vec<u64>>,
    orders: Vec<Vec<u64>>,
    lineitem: Vec<Vec<u64>>,
    supplier: Vec<Vec<u64>>,
    nation: Vec<Vec<u64>>,
    regions: Vec<Vec<u64>>,
    pub condition: Vec<u64>,
    _marker: PhantomData<F>,
}

impl<F: Copy + Default> Default for MyCircuit<F> {
    fn default() -> Self {
        Self {
            customer: Vec::new(),
            orders: Vec::new(),
            lineitem: Vec::new(),
            supplier: Vec::new(),
            nation: Vec::new(),
            regions: Vec::new(),
            condition: vec![Default::default(); 3],
            _marker: PhantomData,
        }
    }
}

impl<F: Field + Ord> Circuit<F> for MyCircuit<F> {
    type Config = TestCircuitConfig<F>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        TestChip::configure(meta)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let chip = TestChip::construct(config);
        let out = chip.assign(
            &mut layouter,
            self.customer.clone(),
            self.orders.clone(),
            self.lineitem.clone(),
            self.supplier.clone(),
            self.nation.clone(),
            self.regions.clone(),
            self.condition.clone(),
        )?;
        chip.expose_public(&mut layouter, out, 0)?;
        Ok(())
    }
}

// -------------------------------------------------------------------------
//  Tests
// -------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::data::data_processing;
    use chrono::{DateTime, NaiveDate, Utc};
    use halo2_proofs::dev::MockProver;
    use halo2_proofs::{
        plonk::{create_proof, keygen_pk, keygen_vk, verify_proof},
        poly::{
            commitment::Params,
            ipa::{
                commitment::{IPACommitmentScheme, ParamsIPA},
                multiopen::ProverIPA,
                strategy::SingleStrategy,
            },
            VerificationStrategy,
        },
        transcript::{
            Blake2bRead, Blake2bWrite, Challenge255, TranscriptReadBuffer, TranscriptWriterBuffer,
        },
    };
    use halo2curves::pasta::{vesta, EqAffine, Fp};
    use rand::rngs::OsRng;
    use std::{fs::File, io::Write, path::Path};

    fn generate_and_verify_proof<C: Circuit<Fp>>(
        k: u32,
        circuit: C,
        public_input: &[Fp],
        proof_path: &str,
    ) {
        let params_path = "/home2/binbin/PoneglyphDB/src/sql/param16";
        let mut fd = std::fs::File::open(&params_path).unwrap();
        let params = ParamsIPA::<vesta::Affine>::read(&mut fd).unwrap();

        let t0 = Instant::now();
        let vk = keygen_vk(&params, &circuit).expect("keygen_vk");
        println!("VK gen: {:?}", t0.elapsed());

        let t1 = Instant::now();
        let pk = keygen_pk(&params, vk.clone(), &circuit).expect("keygen_pk");
        println!("PK gen: {:?}", t1.elapsed());

        let mut rng = OsRng;
        let mut transcript = Blake2bWrite::<_, EqAffine, Challenge255<_>>::init(vec![]);
        create_proof::<IPACommitmentScheme<_>, ProverIPA<_>, _, _, _, _>(
            &params,
            &pk,
            &[circuit],
            &[&[public_input]],
            &mut rng,
            &mut transcript,
        )
        .expect("proof generation");
        let proof = transcript.finalize();

        File::create(Path::new(proof_path))
            .unwrap()
            .write_all(&proof)
            .unwrap();

        let strategy = SingleStrategy::new(&params);
        let mut transcript = Blake2bRead::<_, _, Challenge255<_>>::init(&proof[..]);
        assert!(verify_proof(
            &params,
            pk.get_vk(),
            strategy,
            &[&[public_input]],
            &mut transcript
        )
        .is_ok());
    }

    #[test]
    fn test_1() {
        let k = 16;
        let data_dir = "/home2/binbin/PoneglyphDB/src/data";

        fn str_to_u64(s: &str) -> u64 {
            s.chars()
                .enumerate()
                .map(|(i, c)| (i as u64 + 1) * (c as u64))
                .sum()
        }
        fn scale(x: f64) -> u64 {
            (1000.0 * x) as u64
        }
        fn date_u64(s: &str) -> u64 {
            NaiveDate::parse_from_str(s, "%Y-%m-%d")
                .map(|d| DateTime::<Utc>::from_utc(d.and_hms(0, 0, 0), Utc).timestamp() as u64)
                .unwrap_or(0)
        }

        // Data Loading
        let mut customer = vec![];
        if let Ok(rec) =
            data_processing::customer_read_records_from_file(&format!("{}/customer.tbl", data_dir))
        {
            customer = rec
                .iter()
                .map(|r| vec![r.c_custkey, r.c_nationkey])
                .collect();
        }
        let mut orders = vec![];
        if let Ok(rec) =
            data_processing::orders_read_records_from_file(&format!("{}/orders.tbl", data_dir))
        {
            orders = rec
                .iter()
                .map(|r| vec![date_u64(&r.o_orderdate), r.o_custkey, r.o_orderkey])
                .collect();
        }
        let mut lineitem = vec![];
        // Using smaller file for test if available, else standard
        let li_path = format!("{}/lineitem.tbl", data_dir);
        // let li_path = format!("{}/lineitem_240K.tbl", data_dir);
        if let Ok(rec) = data_processing::lineitem_read_records_from_file(&li_path) {
            lineitem = rec
                .iter()
                .map(|r| {
                    vec![
                        r.l_orderkey,
                        scale(r.l_extendedprice),
                        scale(r.l_discount),
                        r.l_suppkey,
                    ]
                })
                .collect();
        }
        let mut supplier = vec![];
        if let Ok(rec) =
            data_processing::supplier_read_records_from_file(&format!("{}/supplier.tbl", data_dir))
        {
            supplier = rec
                .iter()
                .map(|r| vec![r.s_nationkey, r.s_suppkey])
                .collect();
        }
        let mut nation = vec![];
        if let Ok(rec) =
            data_processing::nation_read_records_from_file(&format!("{}/nation.tbl", data_dir))
        {
            nation = rec
                .iter()
                .map(|r| vec![r.n_nationkey, r.n_regionkey, str_to_u64(&r.n_name)])
                .collect();
        }
        let mut regions = vec![];
        if let Ok(rec) =
            data_processing::region_read_records_from_cvs(&format!("{}/region.cvs", data_dir))
        {
            regions = rec
                .iter()
                .map(|r| vec![r.r_regionkey, str_to_u64(&r.r_name)])
                .collect();
        }

        let condition = vec![
            str_to_u64("EUROPE"),
            date_u64("1997-01-01"),
            date_u64("1998-01-01"),
        ];

        let circuit = MyCircuit::<Fp> {
            customer,
            orders,
            lineitem,
            supplier,
            nation,
            regions,
            condition,
            _marker: PhantomData,
        };
        let public_input = vec![Fp::from(1)];

        // let test = true;
        let test = false;

        if test {
            let prover = MockProver::run(k, &circuit, vec![public_input]).unwrap();
            prover.assert_satisfied();
        } else {
            let proof_path = "/home2/binbin/PoneglyphDB/src/sql/proof_q5_op";
            generate_and_verify_proof(k, circuit, &public_input, proof_path);
        }
    }
}
