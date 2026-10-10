# Solver integer ranges, measured

Each file here asks one solver a question whose answer depends on reading an integer
past 32, 53, or 64 bits correctly. The results below were measured on 2026-10-06 with the
solvers installed then: RoundingSat from `~/.local/bin` (it prints no version),
clingo 5.8.2, clasp 3.4.1, and MiniZinc 2.10.1 with Chuffed 0.14.0, Gecode 6.4.0, CP-SAT
9.15, HiGHS 1.15.1, COIN-BC 2.10.13, and SCIP 10.1.0, each under `tools/guard.sh 2000` or
`4000`.

| file | question | right answer |
| --- | --- | --- |
| `opb_big_objective.opb` | x1 costs 2^70, x2 costs 1, one must hold | x2, cost 1 |
| `opb_big_forced.opb` | both forced | cost 2^70 + 1 |
| `opb_big_constraint.opb` | 2^100·x1 + x2 >= 2^100 | x1 forced, cost 1 |
| `asp_big_weight.lp` | a costs 3e9, b costs 5 | b, cost 5 |
| `asp_big_sum.lp` | two weights of 2e9, both forced | cost 4e9 |
| `mzn_2_40.mzn` | x costs 2^40, y costs 5 | y |
| `mzn_2_53.mzn` | x costs 2^53 + 1, y costs 2^53 | y |
| `mzn_big.mzn`, `mzn_var_overflow.mzn` | an objective past 2^63 | an error |

| solver | result | range used by `crate::extraction` |
| --- | --- | --- |
| RoundingSat | all three OPB files exact (2^70 + 1, 2^100) | arbitrary precision |
| clasp (OPB) | 2^70 read as 0: optimum 0 with x1; the 2^100 constraint ignored; no error | 32-bit |
| clingo | 3e9 read as -1294967296, reported `OPTIMUM FOUND`; the 4e9 sum is right | 32-bit per value |
| MiniZinc compiler | `integer overflow` on both 2^63 files, every solver | 64-bit, reports |
| CP-SAT | 2^40 and 2^53 right | 64-bit |
| Chuffed | 2^40: chose x, no error | 32-bit |
| Gecode | 2^40: "out of range (-2147483646..2147483646)" | 32-bit |
| COIN-BC | 2^53: chose x, no error | exact to 2^53 |
| HiGHS | 2^53: "Unable to add linear constraint" | exact to 2^53 |
| SCIP | 2^53 right on this test | exact to 2^53 (computes in doubles) |

Semper refuses, before the solver runs, any value the dump or the OPB file would
write outside the chosen solver's range (`solve::SolverRange`, `OpbCommand::opb_range`,
`OpbCommand::mzn_range`, `asp::clingo_int`). Not checked: what user-written ASP or
MiniZinc criteria compute from in-range values inside a 32-bit or double-precision
solver. A sum of in-range values can still leave the solver's range there.
