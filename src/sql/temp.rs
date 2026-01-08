// use eth_types::Field;

use halo2_proofs::{halo2curves::ff::PrimeField, plonk::Expression};

use crate::chips::is_zero::{IsZeroChip, IsZeroConfig};
// use crate::chips::less_than_vector::{LtVecChip, LtVecConfig, LtVecInstruction};
// use crate::chips::lessthan_or_equal_vector::{LtEqVecChip, LtEqVecConfig, LtEqVecInstruction};
use crate::chips::less_than::{LtChip, LtConfig, LtInstruction};
use crate::chips::lessthan_or_equal_generic::{
    LtEqGenericChip, LtEqGenericConfig, LtEqGenericInstruction,
};
use crate::chips::permutation_any::{PermAnyChip, PermAnyConfig};

use std::thread::sleep;
use std::{default, marker::PhantomData};

// use crate::chips::is_zero_v1::{IsZeroChip, IsZeroConfig};

use halo2_proofs::{circuit::*, plonk::*, poly::Rotation};
use std::cmp::Ordering;
use std::collections::{HashMap, HashSet};
use std::mem;
use std::process;
use std::time::Instant;

const NUM_BYTES: usize = 5;

pub trait Field: PrimeField<Repr = [u8; 32]> {}

impl<F> Field for F where F: PrimeField<Repr = [u8; 32]> {}

// #[derive(Default)]

#[derive(Clone, Debug)]
pub struct TestCircuitConfig<F: Field + Ord> {
    q_enable: Vec<Selector>,
    q_join: Vec<Selector>,
    // q_perm: Vec<Selector>,
    q_sort: Vec<Selector>,
    q_accu: Selector,
    q_flagged_lookup: Selector,
    q_lookup_complex: Selector,

    customer: Vec<Column<Advice>>, // c_mkt, c_custkey
    orders: Vec<Column<Advice>>,   // o_orderdate, o_shippri, o_custkey, o_orderkey

    // We REMOVE lineitem_old. The single `lineitem` table stores the filtered rows (l_combined),
    // and we enforce the l_shipdate predicate on those rows.
    lineitem: Vec<Column<Advice>>, // l_orderkey, l_extended, l_dis, l_ship

    flag_o_in_lc: Vec<Column<Advice>>,
    range_low_high: Vec<Column<Advice>>,

    join_group: Vec<Vec<Column<Advice>>>,
    disjoin_group: Vec<Vec<Column<Advice>>>,
    perm_helper: Vec<Vec<Column<Advice>>>, // used for aggregate two groups of columns into one for permutation check
    check: Vec<Column<Advice>>,

    deduplicate: Vec<Column<Advice>>, // deduplicate disjoint values of l_orderkey
    deduplicate_helper: Vec<Column<Advice>>, // merging adjacent two groups of columns into one for permutation check
    dedup_sort: Vec<Column<Advice>>,

    condition: Vec<Column<Advice>>, // conditional value for l, c and o

    o_join: Vec<Column<Advice>>,
    o_disjoin: Vec<Column<Advice>>,
    c_join: Vec<Column<Advice>>,
    c_disjoin: Vec<Column<Advice>>,
    l_join: Vec<Column<Advice>>,
    l_disjoin: Vec<Column<Advice>>,

    groupby: Vec<Column<Advice>>,
    orderby: Vec<Column<Advice>>,
    // // cartesian: Vec<Column<Advice>>,
    equal_check: Column<Advice>, // check if sorted_revenue[i-1] = sorted_revenue[i]
    revenue: Column<Advice>,
    lt_compare_condition: Vec<LtConfig<F, NUM_BYTES>>,
    // lt_compare_condition: Vec<LtVecConfig<F, NUM_BYTES>>,
    equal_condition: Vec<IsZeroConfig<F>>,
    // compare_condition: Vec<LtEqVecConfig<F, NUM_BYTES>>,
    compare_condition: Vec<LtEqGenericConfig<F, NUM_BYTES>>,
    // perm: Vec<PermAnyConfig>,
    instance: Column<Instance>,
    instance_test: Column<Advice>,
    // instance_test1: Column<Advice>,
    // instance_test2: Column<Advice>,
}

#[derive(Debug, Clone)]
pub struct TestChip<F: Field + Ord> {
    config: TestCircuitConfig<F>,
}

impl<F: Field + Ord> TestChip<F> {
    pub fn construct(config: TestCircuitConfig<F>) -> Self {
        Self { config }
    }

    pub fn configure(meta: &mut ConstraintSystem<F>) -> TestCircuitConfig<F> {
        let instance = meta.instance_column();
        meta.enable_equality(instance);
        let instance_test = meta.advice_column();
        meta.enable_equality(instance_test);

        let q_flagged_lookup = meta.selector(); // Simple (for gates)
        let q_lookup_complex = meta.complex_selector(); // Complex (for lookup arguments)

        let mut q_enable = Vec::new();
        for _ in 0..4 {
            q_enable.push(meta.selector());
        }

        let mut q_sort = Vec::new();
        for _ in 0..4 {
            q_sort.push(meta.selector());
        }

        let mut q_join = Vec::new();
        for i in 0..8 {
            if i < 2 {
                q_join.push(meta.selector());
            } else {
                q_join.push(meta.complex_selector());
            }
        }
        for _ in 0..5 {
            q_sort.push(meta.selector());
        }

        let q_accu = meta.selector();

        let mut customer = Vec::new();
        let mut orders = Vec::new();
        let mut lineitem = Vec::new();

        for _ in 0..2 {
            customer.push(meta.advice_column());
        }
        for _ in 0..4 {
            orders.push(meta.advice_column());
            lineitem.push(meta.advice_column());
        }

        let mut condition = Vec::new();
        for _ in 0..3 {
            // use meta.equality() for copying check, so we do not need three conditions here
            condition.push(meta.advice_column());
        }
        meta.enable_equality(condition[2]);

        let mut deduplicate = Vec::new();
        let mut deduplicate_helper = Vec::new();
        let mut dedup_sort = Vec::new();

        for _ in 0..2 {
            dedup_sort.push(meta.advice_column());
            deduplicate_helper.push(meta.advice_column());
        }
        for _ in 0..4 {
            deduplicate.push(meta.advice_column());
        }

        let mut join_group = Vec::new();
        let mut disjoin_group = Vec::new();

        for l in [4, 2, 4, 6] {
            let mut col = Vec::new();
            for _ in 0..l {
                col.push(meta.advice_column());
            }
            join_group.push(col);
        }
        for l in [4, 2, 4, 6] {
            let mut col = Vec::new();
            for _ in 0..l {
                col.push(meta.advice_column());
            }
            disjoin_group.push(col);
        }

        let mut perm_helper = Vec::new();
        for l in [4, 2, 4] {
            let mut col = Vec::new();
            for _ in 0..l {
                col.push(meta.advice_column());
            }
            perm_helper.push(col);
        }

        let mut flag_o_in_lc = Vec::new();
        let mut range_low_high = Vec::new();
        // flag_o_in_lc[0]: flag_o_in_c
        // flag_o_in_lc[1]: flag_o_in_l
        for _ in 0..2 {
            flag_o_in_lc.push(meta.advice_column());
            range_low_high.push(meta.advice_column());
        }

        let mut c_join = Vec::new(); // for c table
        let mut c_disjoin = Vec::new();
        for _ in 0..2 {
            c_join.push(meta.advice_column());
            c_disjoin.push(meta.advice_column());
        }
        let mut o_join = Vec::new(); //
        let mut o_disjoin = Vec::new();
        let mut l_join = Vec::new();
        let mut l_disjoin = Vec::new();
        for _ in 0..4 {
            o_join.push(meta.advice_column());
            o_disjoin.push(meta.advice_column());
            l_join.push(meta.advice_column());
            l_disjoin.push(meta.advice_column());
        }

        let mut groupby = Vec::new();
        let mut orderby = Vec::new();
        for _ in 0..5 {
            groupby.push(meta.advice_column());
        }
        for _ in 0..4 {
            orderby.push(meta.advice_column());
        }
        let equal_check = meta.advice_column();
        let revenue = meta.advice_column();

        let mut is_zero_advice_column = Vec::new();
        for _ in 0..2 {
            is_zero_advice_column.push(meta.advice_column());
        }

        let mut check = Vec::new();
        for _ in 0..4 {
            check.push(meta.advice_column());
        }

        // c_mktsegment = ':1'
        let mut equal_condition = Vec::new();
        let config = IsZeroChip::configure(
            meta,
            |meta| meta.query_selector(q_enable[0]), // this is the q_enable
            |meta| {
                meta.query_advice(customer[0], Rotation::cur())
                    - meta.query_advice(condition[0], Rotation::cur())
            }, // this is the value
            is_zero_advice_column[0], // this is the advice column that stores value_inv
        );
        equal_condition.push(config.clone());

        meta.create_gate("f(a, b) = if a == b {1} else {0}", |meta| {
            let s = meta.query_selector(q_enable[0]);
            let output = meta.query_advice(check[0], Rotation::cur());
            vec![
                s.clone() * (config.expr() * (output.clone() - Expression::Constant(F::ONE))), // output == 1
                s * (Expression::Constant(F::ONE) - config.expr()) * (output), // output == 0
            ]
        });

        let mut lt_compare_condition = Vec::new();
        // o_orderdate < date ':2'
        let config = LtChip::configure(
            meta,
            |meta| meta.query_selector(q_enable[1]),
            |meta| meta.query_advice(orders[0], Rotation::cur()),
            |meta| meta.query_advice(condition[1], Rotation::cur()),
        );

        meta.create_gate("verifies o_orderdate < date ':2'", |meta| {
            let q_enable = meta.query_selector(q_enable[1]);
            let check = meta.query_advice(check[1], Rotation::cur());
            vec![q_enable.clone() * (config.is_lt(meta, None) - check)]
        });

        lt_compare_condition.push(config);

        // l_shipdate > date ':2'
        // We encode "condition[2] < l_shipdate" using LtChip.
        let config: LtConfig<F, NUM_BYTES> = LtChip::configure(
            meta,
            |meta| meta.query_selector(q_enable[2]),
            |meta| meta.query_advice(condition[2], Rotation::cur()),
            |meta| meta.query_advice(lineitem[3], Rotation::cur()),
        );

        meta.create_gate("verifies l_shipdate > date ':2'", |meta| {
            let q_enable = meta.query_selector(q_enable[2]);
            let check = meta.query_advice(check[2], Rotation::cur());
            vec![q_enable * (config.is_lt(meta, None) - check)]
        });
        lt_compare_condition.push(config);

        // // disjoin sort check
        // // dedup check
        // let lookup_configs = [
        //     (0, 2), // (disjoin_group index, column index)
        //     (1, 1),
        //     (2, 0),
        //     (3, 3),
        // ];

        // for (disjoin_index, column_index) in lookup_configs.iter() {
        //     meta.lookup_any("dedup check", |meta| {
        //         let input = meta.query_advice(
        //             disjoin_group[*disjoin_index][*column_index],
        //             Rotation::cur(),
        //         );
        //         let table = meta.query_advice(deduplicate[*disjoin_index], Rotation::cur());
        //         vec![(input, table)]
        //     });
        // }

        // // three permutation checks: orders, customer, lineitem(filtered)
        // PermAnyChip::configure(
        //     meta,
        //     q_join[2],
        //     q_join[5],
        //     orders.clone(),
        //     perm_helper[0].clone(),
        // );

        // PermAnyChip::configure(
        //     meta,
        //     q_join[3],
        //     q_join[6],
        //     customer.clone(),
        //     perm_helper[1].clone(),
        // );

        // PermAnyChip::configure(
        //     meta,
        //     q_join[4],
        //     q_join[7],
        //     lineitem.clone(),
        //     perm_helper[2].clone(),
        // );

        // // two dedup permutation check: deduplicate and dedup_sort
        // meta.lookup_any("dedup permutation check", |meta| {
        //     let input = meta.query_advice(deduplicate_helper[0], Rotation::cur());
        //     let table = meta.query_advice(dedup_sort[0], Rotation::cur());
        //     vec![(input, table)]
        // });
        // meta.lookup_any("dedup permutation check", |meta| {
        //     let input = meta.query_advice(deduplicate_helper[1], Rotation::cur());
        //     let table = meta.query_advice(dedup_sort[1], Rotation::cur());
        //     vec![(input, table)]
        // });

        // // join1 check
        // meta.create_gate("verify join1 values match'", |meta| {
        //     let q = meta.query_selector(q_join[0]);
        //     let p1 = meta.query_advice(join_group[0][2], Rotation::cur());
        //     let p2 = meta.query_advice(join1[1], Rotation::cur());
        //     vec![q * (p1 - p2)]
        // });

        // // all values of join1 are in join_group[1]
        // meta.lookup_any("check join1", |meta| {
        //     let inputs: Vec<_> = join_group[1]
        //         .iter()
        //         .map(|&idx| meta.query_advice(idx, Rotation::cur()))
        //         .collect();

        //     let tables: Vec<_> = join1
        //         .iter()
        //         .map(|&idx| meta.query_advice(idx, Rotation::cur()))
        //         .collect();

        //     inputs
        //         .iter()
        //         .zip(tables.iter())
        //         .map(|(input, table)| (input.clone(), table.clone()))
        //         .collect()
        // });

        // // join2 check
        // meta.create_gate("verify join2 values match'", |meta| {
        //     let q = meta.query_selector(q_join[1]);
        //     let p1 = meta.query_advice(join_group[2][0], Rotation::cur());
        //     let p2 = meta.query_advice(join2[3], Rotation::cur());
        //     vec![q * (p1 - p2)]
        // });

        // meta.lookup_any("check join2", |meta| {
        //     let inputs: Vec<_> = join2
        //         .iter()
        //         .map(|&idx| meta.query_advice(idx, Rotation::cur()))
        //         .collect();

        //     let tables: Vec<_> = join_group[3]
        //         .iter()
        //         .map(|&idx| meta.query_advice(idx, Rotation::cur()))
        //         .collect();

        //     inputs
        //         .iter()
        //         .zip(tables.iter())
        //         .map(|(input, table)| (input.clone(), table.clone()))
        //         .collect()
        // });

        // // two dedup sort check
        // for i in 0..2 {
        //     let config = LtChip::configure(
        //         meta,
        //         |meta| meta.query_selector(q_sort[i]),
        //         |meta| meta.query_advice(dedup_sort[i], Rotation::prev()),
        //         |meta| meta.query_advice(dedup_sort[i], Rotation::cur()),
        //     );
        //     lt_compare_condition.push(config.clone());
        //     meta.create_gate("t[i-1]<t[i]'", |meta| {
        //         let q_enable = meta.query_selector(q_sort[i]);
        //         vec![q_enable * (config.is_lt(meta, None) - Expression::Constant(F::ONE))]
        //     });
        // }

        // group by compare (lexicographic <=)
        let mut compare_condition = Vec::new();
        // let config = LtEqGenericChip::configure(
        //     meta,
        //     |meta| meta.query_selector(q_sort[2]),
        //     |meta| {
        //         vec![
        //             meta.query_advice(groupby[0], Rotation::prev()),
        //             meta.query_advice(groupby[1], Rotation::prev()),
        //             meta.query_advice(groupby[2], Rotation::prev()),
        //         ]
        //     },
        //     |meta| {
        //         vec![
        //             meta.query_advice(groupby[0], Rotation::cur()),
        //             meta.query_advice(groupby[1], Rotation::cur()),
        //             meta.query_advice(groupby[2], Rotation::cur()),
        //         ]
        //     },
        // );
        // compare_condition.push(config);

        // // orderby: revenue desc, o_orderdate asc
        // let config = LtEqGenericChip::configure(
        //     meta,
        //     |meta| meta.query_selector(q_sort[3]),
        //     |meta| vec![meta.query_advice(orderby[3], Rotation::cur())], // revenue cur
        //     |meta| vec![meta.query_advice(orderby[3], Rotation::prev())], // revenue prev
        // );
        // compare_condition.push(config.clone());

        // let equal_v1 = IsZeroChip::configure(
        //     meta,
        //     |meta| meta.query_selector(q_sort[3]),
        //     |meta| {
        //         meta.query_advice(orderby[3], Rotation::prev())
        //             - meta.query_advice(orderby[3], Rotation::cur())
        //     },
        //     is_zero_advice_column[1],
        // );
        // equal_condition.push(equal_v1.clone());

        // let config_lt = LtEqGenericChip::configure(
        //     meta,
        //     |meta| meta.query_selector(q_sort[3]),
        //     |meta| vec![meta.query_advice(orderby[0], Rotation::prev())], // o_orderdate prev
        //     |meta| vec![meta.query_advice(orderby[0], Rotation::cur())],  // o_orderdate cur
        // );
        // compare_condition.push(config_lt.clone());

        // meta.create_gate("verifies orderby scenarios", |meta| {
        //     let q_sort = meta.query_selector(q_sort[3]);
        //     vec![
        //         q_sort.clone()
        //             * (config.is_lt(meta, None) - Expression::Constant(F::ONE))
        //             * (equal_v1.expr() * config_lt.is_lt(meta, None)
        //                 - Expression::Constant(F::ONE)),
        //     ]
        // });

        TestCircuitConfig {
            q_enable,
            q_join,
            q_sort,
            q_accu,
            customer,
            orders,
            lineitem,
            join_group,
            disjoin_group,
            perm_helper,
            check,
            deduplicate,
            deduplicate_helper,
            dedup_sort,
            condition,
            o_join,
            o_disjoin,
            c_join,
            c_disjoin,
            l_join,
            l_disjoin,
            groupby,
            orderby,
            equal_check,
            revenue,
            lt_compare_condition,
            equal_condition,
            compare_condition,
            instance,
            instance_test,
            flag_o_in_lc,
            range_low_high,
            q_flagged_lookup,
            q_lookup_complex,
        }
    }

    pub fn assign(
        &self,
        layouter: &mut impl Layouter<F>,
        customer: Vec<Vec<u64>>,
        orders: Vec<Vec<u64>>,
        lineitem: Vec<Vec<u64>>,
        condition: [u64; 2],
    ) -> Result<AssignedCell<F, F>, Error> {
        let mut equal_chip = Vec::new();
        let mut compare_chip = Vec::new();
        let mut lt_compare_chip = Vec::new();

        for i in 0..self.config.equal_condition.len() {
            let chip = IsZeroChip::construct(self.config.equal_condition[i].clone());
            equal_chip.push(chip);
        }
        for i in 0..self.config.compare_condition.len() {
            let chip = LtEqGenericChip::construct(self.config.compare_condition[i].clone());
            chip.load(layouter)?;
            compare_chip.push(chip);
        }

        for i in 0..self.config.lt_compare_condition.len() {
            let chip = LtChip::construct(self.config.lt_compare_condition[i].clone());
            chip.load(layouter)?;
            lt_compare_chip.push(chip);
        }

        // witness local computation
        let start = Instant::now();

        let mut o_check = Vec::new(); // t/f
        let mut c_check = Vec::new(); // 0, 1
        let mut l_check = Vec::new();

        for i in 0..customer.len() {
            if customer[i][0] == condition[0] {
                c_check.push(1);
            } else {
                c_check.push(0);
            }
        }
        for i in 0..orders.len() {
            if orders[i][0] < condition[1] {
                o_check.push(true);
            } else {
                o_check.push(false);
            }
        }

        for i in 0..lineitem.len() {
            if lineitem[i][3] > condition[1] {
                l_check.push(true);
            } else {
                l_check.push(false);
            }
        }

        // filtered tables (these are what the circuit uses downstream)
        let c_combined: Vec<Vec<_>> = customer
            .clone()
            .into_iter()
            .filter(|row| row[0] == condition[0])
            .collect();

        let o_combined: Vec<Vec<_>> = orders
            .clone()
            .into_iter()
            .filter(|row| row[0] < condition[1])
            .collect();

        let l_combined: Vec<Vec<_>> = lineitem
            .clone()
            .into_iter()
            .filter(|row| row[3] > condition[1])
            .collect();

        let mut combined = Vec::new();
        combined.push(c_combined); // 2 cols
        combined.push(o_combined); // 4 cols
        combined.push(l_combined.clone()); // 4 cols

        let index = [
            (0, 1, 1, 2), // c_custkey = o_custkey
            (1, 2, 3, 0), // l_orderkey = o_orderkey
        ];

        let join_index = [
            (0, 1, 1, 2),     // c_custkey = o_custkey
            (1, 2, 2 + 3, 0), // l_orderkey = o_orderkey (offset into joined row)
        ];

        let mut join_value: Vec<Vec<_>> = vec![vec![]; 4];
        let mut disjoin_value: Vec<Vec<_>> = vec![vec![]; 4];

        // Indices in your row layout:
        let C_CUSTKEY: usize = 1; // customer row: [c_mktsegment, c_custkey]
        let O_CUSTKEY: usize = 2; // orders row:   [o_orderdate, o_shippriority, o_custkey, o_orderkey]
        let O_ORDERKEY: usize = 3;
        let L_ORDERKEY: usize = 0; // lineitem row: [l_orderkey, l_extendedprice, l_discount, l_shipdate]

        // Build lookup sets from filtered inputs
        let c_keys: HashSet<u64> = combined[0].iter().map(|c| c[C_CUSTKEY]).collect();
        let l_orderkeys: HashSet<u64> = combined[2].iter().map(|l| l[L_ORDERKEY]).collect();

        // 1) Contributing orders = have BOTH a customer match and a lineitem match
        let mut contributing_orders: Vec<Vec<u64>> = Vec::new();
        let mut noncontributing_orders: Vec<Vec<u64>> = Vec::new();

        for o in combined[1].iter() {
            let ok = c_keys.contains(&o[O_CUSTKEY]) && l_orderkeys.contains(&o[O_ORDERKEY]);
            if ok {
                contributing_orders.push(o.clone());
            } else {
                noncontributing_orders.push(o.clone());
            }
        }

        // Collect keys from contributing orders
        let contributing_o_custkeys: HashSet<u64> =
            contributing_orders.iter().map(|o| o[O_CUSTKEY]).collect();
        let contributing_o_orderkeys: HashSet<u64> =
            contributing_orders.iter().map(|o| o[O_ORDERKEY]).collect();

        // 2) Contributing customers = appear in contributing orders
        let mut contributing_customers: Vec<Vec<u64>> = Vec::new();
        let mut noncontributing_customers: Vec<Vec<u64>> = Vec::new();

        for c in combined[0].iter() {
            if contributing_o_custkeys.contains(&c[C_CUSTKEY]) {
                contributing_customers.push(c.clone());
            } else {
                noncontributing_customers.push(c.clone());
            }
        }

        // 3) Contributing lineitems = orderkey appears in contributing orders
        let mut contributing_lineitems: Vec<Vec<u64>> = Vec::new();
        let mut noncontributing_lineitems: Vec<Vec<u64>> = Vec::new();

        for l in combined[2].iter() {
            if contributing_o_orderkeys.contains(&l[L_ORDERKEY]) {
                contributing_lineitems.push(l.clone());
            } else {
                noncontributing_lineitems.push(l.clone());
            }
        }

        // Use only the first 3 buckets for base tables:
        join_value[0] = contributing_orders; // orders
        disjoin_value[0] = noncontributing_orders;

        join_value[1] = contributing_customers; // customer
        disjoin_value[1] = noncontributing_customers;

        join_value[2] = contributing_lineitems; // lineitem
        disjoin_value[2] = noncontributing_lineitems;

        for i in 0..join_value.len() {
            println!("join value {:?}", join_value[i].len());
            println!("join value {:?}", disjoin_value[i].len());
        }

        layouter.assign_region(
            || "witness",
            |mut region| {
                // customer
                for i in 0..customer.len() {
                    self.config.q_enable[0].enable(&mut region, i)?;
                    if c_check[i] == 1 {
                        self.config.q_join[3].enable(&mut region, i)?;
                    }
                    for j in 0..customer[0].len() {
                        region.assign_advice(
                            || "customer",
                            self.config.customer[j],
                            i,
                            || Value::known(F::from(customer[i][j])),
                        )?;
                    }

                    region.assign_advice(
                        || "check0",
                        self.config.check[0],
                        i,
                        || Value::known(F::from(c_check[i])),
                    )?;

                    region.assign_advice(
                        || "condition for customer",
                        self.config.condition[0],
                        i,
                        || Value::known(F::from(condition[0])),
                    )?;
                }

                // orders
                for i in 0..orders.len() {
                    self.config.q_enable[1].enable(&mut region, i)?;
                    if o_check[i] == true {
                        self.config.q_join[2].enable(&mut region, i)?;
                    }
                    for j in 0..orders[0].len() {
                        region.assign_advice(
                            || "orders",
                            self.config.orders[j],
                            i,
                            || Value::known(F::from(orders[i][j])),
                        )?;
                    }

                    region.assign_advice(
                        || "check1",
                        self.config.check[1],
                        i,
                        || Value::known(F::from(o_check[i] as u64)),
                    )?;

                    region.assign_advice(
                        || "condition1",
                        self.config.condition[1],
                        i,
                        || Value::known(F::from(condition[1])),
                    )?;
                }

                // lineitem
                for i in 0..lineitem.len() {
                    // enable filter predicate gate
                    self.config.q_enable[2].enable(&mut region, i)?;

                    // // enable permutation selector for lineitem table
                    // self.config.q_join[4].enable(&mut region, i)?;

                    // store condition[2] = condition[1] for l_shipdate comparison
                    region.assign_advice(
                        || "condition2",
                        self.config.condition[2],
                        i,
                        || Value::known(F::from(condition[1])),
                    )?;

                    for j in 0..lineitem[0].len() {
                        region.assign_advice(
                            || "lineitem",
                            self.config.lineitem[j],
                            i,
                            || Value::known(F::from(lineitem[i][j])),
                        )?;
                    }

                    // check column for predicate
                    region.assign_advice(
                        || "check2",
                        self.config.check[2],
                        i,
                        || Value::known(F::from(l_check[i] as u64)),
                    )?;
                }

                macro_rules! assign_2d {
                    ($tag:expr, $cols:expr, $rows:expr) => {{
                        for (i, r) in $rows.iter().enumerate() {
                            for (j, &v) in r.iter().enumerate() {
                                region.assign_advice(
                                    || $tag,
                                    $cols[j],
                                    i,
                                    || Value::known(F::from(v)),
                                )?;
                            }
                        }
                        Ok::<(), Error>(())
                    }};
                }

                // orders
                assign_2d!("orders join", &self.config.o_join, &join_value[0])?;
                assign_2d!("orders disjoin", &self.config.o_disjoin, &disjoin_value[0])?;

                assign_2d!("customer join", &self.config.c_join, &join_value[1])?;
                assign_2d!(
                    "customer disjoin",
                    &self.config.c_disjoin,
                    &disjoin_value[1]
                )?;

                assign_2d!("lineitem join", &self.config.l_join, &join_value[2])?;
                assign_2d!(
                    "lineitem disjoin",
                    &self.config.l_disjoin,
                    &disjoin_value[2]
                )?;

                // chip assign
                for i in 0..customer.len() {
                    equal_chip[0].assign(
                        &mut region,
                        i,
                        Value::known(F::from(customer[i][0]) - F::from(condition[0])),
                    )?; // c_mktsegment = ':1'
                }

                for i in 0..orders.len() {
                    lt_compare_chip[0].assign(
                        &mut region,
                        i,
                        Value::known(F::from(orders[i][0])),
                        Value::known(F::from(condition[1])),
                    )?;
                }

                for i in 0..lineitem.len() {
                    lt_compare_chip[1].assign(
                        &mut region,
                        i,
                        Value::known(F::from(condition[1])),
                        Value::known(F::from(lineitem[i][3])),
                    )?;
                }

                let out = region.assign_advice(
                    || "instance_test",
                    self.config.instance_test,
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
        layouter.constrain_instance(cell.cell(), self.config.instance, row)
    }
}

struct MyCircuit<F> {
    customer: Vec<Vec<u64>>,
    orders: Vec<Vec<u64>>,
    lineitem: Vec<Vec<u64>>,
    pub condition: [u64; 2],
    _marker: PhantomData<F>,
}

impl<F: Copy + Default> Default for MyCircuit<F> {
    fn default() -> Self {
        Self {
            customer: Vec::new(),
            orders: Vec::new(),
            lineitem: Vec::new(),
            condition: [Default::default(); 2],
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
        let test_chip = TestChip::construct(config);

        let out_cells = test_chip.assign(
            &mut layouter,
            self.customer.clone(),
            self.orders.clone(),
            self.lineitem.clone(),
            self.condition.clone(),
        )?;

        test_chip.expose_public(&mut layouter, out_cells, 0)?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::MyCircuit;
    use crate::data::data_processing;
    use chrono::{DateTime, NaiveDate, Utc};
    use halo2_proofs::dev::MockProver;
    use std::marker::PhantomData;

    use crate::circuits::utils::full_prover;

    use halo2curves::pasta::{pallas, vesta, EqAffine, Fp};

    use halo2_proofs::{
        circuit::{Layouter, SimpleFloorPlanner, Value},
        plonk::{
            create_proof, keygen_pk, keygen_vk, verify_proof, Advice, Circuit, Column,
            ConstraintSystem, Error, Instance,
        },
        poly::{
            commitment::{Params, ParamsProver},
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
    use rand::rngs::OsRng;
    use std::process;
    use std::time::Instant;
    use std::{fs::File, io::Write, path::Path};

    fn generate_and_verify_proof<C: Circuit<Fp>>(
        k: u32,
        circuit: C,
        public_input: &[Fp],
        proof_path: &str,
    ) {
        let params_path = "/home2/binbin/PoneglyphDB/src/proof/param16";
        let mut fd = std::fs::File::open(&params_path).unwrap();
        let params = ParamsIPA::<vesta::Affine>::read(&mut fd).unwrap();

        let params_time_start = Instant::now();
        let vk = keygen_vk(&params, &circuit).expect("keygen_vk should not fail");
        let params_time = params_time_start.elapsed();
        println!("Time to generate vk {:?}", params_time);

        let params_time_start = Instant::now();
        let pk = keygen_pk(&params, vk.clone(), &circuit).expect("keygen_pk should not fail");
        let params_time = params_time_start.elapsed();
        println!("Time to generate pk {:?}", params_time);

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
        .expect("proof generation should not fail");
        let proof = transcript.finalize();

        File::create(Path::new(proof_path))
            .expect("Failed to create proof file")
            .write_all(&proof)
            .expect("Failed to write proof");
        println!("Proof written to: {}", proof_path);

        let strategy = SingleStrategy::new(&params);
        let mut transcript = Blake2bRead::<_, _, Challenge255<_>>::init(&proof[..]);
        assert!(
            verify_proof(
                &params,
                pk.get_vk(),
                strategy,
                &[&[public_input]],
                &mut transcript
            )
            .is_ok(),
            "Proof verification failed"
        );
    }

    #[test]
    fn test_1() {
        let k = 16;

        fn string_to_u64(s: &str) -> u64 {
            let mut result = 0;
            for (i, c) in s.chars().enumerate() {
                result += (i as u64 + 1) * (c as u64);
            }
            result
        }
        fn scale_by_1000(x: f64) -> u64 {
            (1000.0 * x) as u64
        }
        fn date_to_timestamp(date_str: &str) -> u64 {
            match NaiveDate::parse_from_str(date_str, "%Y-%m-%d") {
                Ok(date) => {
                    let datetime: DateTime<Utc> =
                        DateTime::<Utc>::from_utc(date.and_hms(0, 0, 0), Utc);
                    datetime.timestamp() as u64
                }
                Err(_) => 0,
            }
        }

        let customer_file_path = "/home2/binbin/PoneglyphDB/src/data/customer.tbl";
        let orders_file_path = "/home2/binbin/PoneglyphDB/src/data/orders.tbl";
        let lineitem_file_path = "/home2/binbin/PoneglyphDB/src/data/lineitem.tbl";

        // customer rows: 1500
        // orders rows:   15000
        // lineitem rows: 60175

        let mut customer: Vec<Vec<u64>> = Vec::new();
        let mut orders: Vec<Vec<u64>> = Vec::new();
        let mut lineitem: Vec<Vec<u64>> = Vec::new();

        if let Ok(records) = data_processing::customer_read_records_from_file(customer_file_path) {
            customer = records
                .iter()
                .map(|record| vec![string_to_u64(&record.c_mktsegment), record.c_custkey])
                .collect();
        }
        if let Ok(records) = data_processing::orders_read_records_from_file(orders_file_path) {
            orders = records
                .iter()
                .map(|record| {
                    vec![
                        date_to_timestamp(&record.o_orderdate),
                        record.o_shippriority,
                        record.o_custkey,
                        record.o_orderkey,
                    ]
                })
                .collect();
        }
        if let Ok(records) = data_processing::lineitem_read_records_from_file(lineitem_file_path) {
            lineitem = records
                .iter()
                .map(|record| {
                    vec![
                        record.l_orderkey,
                        scale_by_1000(record.l_extendedprice),
                        scale_by_1000(record.l_discount),
                        date_to_timestamp(&record.l_shipdate),
                    ]
                })
                .collect();
        }

        let condition = [string_to_u64("HOUSEHOLD"), date_to_timestamp("1995-03-25")];

        let circuit = MyCircuit::<Fp> {
            customer,
            orders,
            lineitem,
            condition,
            _marker: PhantomData,
        };

        let public_input = vec![Fp::from(1)];

        let test = true;
        // let test = false;

        if test {
            let prover = MockProver::run(k, &circuit, vec![public_input]).unwrap();
            prover.assert_satisfied();
        } else {
            let proof_path = "/home2/binbin/PoneglyphDB/src/proof/proof_obj";
            generate_and_verify_proof(k, circuit, &public_input, proof_path);
        }
    }
}
