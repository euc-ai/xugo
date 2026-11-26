# real_ordered_instance — the real numbers as an ordered field

The real numbers with their strict order are an ordered field on the universal carrier: the field is ℝ's own, read on the whole line, and each order axiom is the matching law of ℝ's order. It is the fact through which the real chapters read the laws of `ordered_field` at ℝ, and the weak order those laws speak of is ℝ's own ≤. The chapter needs only ℝ's field and order laws, so it sits below continuity: `real_continuous` reads through it that a continuous injection on an interval is strictly monotone, and `real_closed_instance` builds the real closed field on it. The instance is not a member of the near-namesake `real_order_field`: `ordered_field` itself rests on that chapter, so the instance there would close a cycle. Framework mechanics are the constitution's.

| Member | Statement |
|---|---|
| `RealOrderedField` | The concrete real field is an ordered carrier field. |
| `RealOrderedLe` | The weak order of the real strict order is ≤. |
