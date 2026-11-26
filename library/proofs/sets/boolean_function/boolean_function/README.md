# boolean_function — sensitivity on a finite set of Boolean coordinates

An input `X ⊆ U` specifies which coordinates carry a one. The function
`f : set(A) → bool` is evaluated at this input and at each neighboring input
`set_toggle(i, X)` for `i ∈ U`. The local sensitivity
`local_sensitivity(U, f, X)` counts the coordinates where the two values differ.

For finite `U`, `SensitivityMaximum` gives an input attaining
`sensitivity(U, f)`. `SensitivityBounds` and `SensitivityLeCard` give
`local_sensitivity(U, f, X) ≤ sensitivity(U, f) ≤ card(U)` for every
`X ⊆ U`. A constant function has sensitivity zero. When `U = ∅`, the
empty set is the only input and every function has sensitivity zero.
