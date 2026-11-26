# int_sum — integer sums

`int_sum` is the fold at integer addition. Its recursion laws are
`monoidal.Clauses` read at `int_real_lift.MonoidalAdd`; the neutral
is the integer zero. The chapter also carries this sum into the reals:
`monoidal.Homomorphic` at `real_of_int` gives the real sum of the
embedded summands.

| Member | Statement |
|---|---|
| `IntSumDef` | Integer summation is `iterated_op` at integer addition |
| `IntSumClauses` | The empty-set and insertion clauses |
| `IntSumBridge` | For finite `s`, embedding its integer sum into ℝ equals summing its embedded values |
