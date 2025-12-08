# PoneglyphDB: Efficient Non-interactive Zero-Knowledge Proofs for Arbitrary SQL-Query Verification

**PoneglyphDB** provides efficient non-interactive zero-knowledge proofs (NIZKs) for verifying arbitrary SQL queries. This repository includes Halo2 circuits for TPC-H workloads and end-to-end proof generation.

## Halo2-TPCH Instructions

To generate the proofs for SQL queries Q1, Q3, Q5, Q8, Q9, and Q18, please run the following commands at the root of the project:

```bash
# Query 1
cargo test --package halo2-experiments --lib -- sql::q1_final_v4::tests::test_1 --exact --nocapture

# Query 3
cargo test --package halo2-experiments --lib -- sql::q3_final_v7::tests::test_1 --exact --nocapture

# Query 5
cargo test --package halo2-experiments --lib -- sql::q5_final_v4::tests::test_1 --exact --nocapture

# Query 8
cargo test --package halo2-experiments --lib -- sql::q8_final_v3::tests::test_1 --exact --nocapture

# Query 9
cargo test --package halo2-experiments --lib -- sql::q9_final_v2::tests::test_1 --exact --nocapture

# Query 18
cargo test --package halo2-experiments --lib -- sql::q18_final_v2::tests::test_1 --exact --nocapture



## Notes
# Prerequisites: Stack Size
Please enable sufficient RUST_MIN_STACK before running proofs:
Please enable sufficient RUST_MIN_STACK by running, e.g., "export RUST_MIN_STACK=33554432"

export RUST_MIN_STACK=33554432

Public Parameter Selection (k)For different datasets, please choose the correct public parameters (k).Dataset SizeQ1, Q5, Q8, Q9, Q18Q360k Rowsk = 16k = 15120k Rowsk = 17k = 16240k Rowsk = 18k = 17


## Citation

If you find our work helpful, please consider citing:

```bibtex
@article{gu2025poneglyphdb,
  title={PoneglyphDB: Efficient Non-interactive Zero-Knowledge Proofs for Arbitrary SQL-Query Verification},
  author={Gu, Binbin and Fang, Juncheng and Nawab, Faisal},
  journal={Proceedings of the ACM on Management of Data},
  volume={3},
  number={1},
  pages={1--27},
  year={2025},
  publisher={ACM New York, NY, USA}
}

