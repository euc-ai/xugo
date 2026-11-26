# boolean_degree — the degree of a Boolean function and parity on a face

For a Boolean function `f : set(A) → bool`, encode false as the integer
zero and true as one. Then `boolean_coefficient(f, S)` is the coefficient
of the monomial indexed by `S` in the integer multilinear representation.
`RealBooleanCoefficient` shows that embedding this integer into the reals
gives the coefficient of the real multilinear representation of the same
zero-one data. For finite `U`, `boolean_degree(U, f)` is the maximum of zero and the
sizes of sets `S ⊆ U` with nonzero coefficient. At positive degree,
`DegreeFace` supplies such an `S` with `card(S) = boolean_degree(U, f)`.
Fixing the coordinates outside `S` to zero gives the face of all `X ⊆ S`.

On this face the coefficient is the sum of the encoded values at `X`,
with sign determined by the parity of `card(S ∖ X)`. If `S` is nonempty,
the face contains equally many positive and negative signs.
`CoefficientMajority` proves that a nonzero signed sum makes one of the two
classes strictly larger than half the face. Those classes group the inputs
where `f(X)` agrees or disagrees with the evenness of `card(X)`.
`MajorityFace` therefore supplies a highest-degree face and a Boolean
`b` for which `2 * card(boolean_parity_class(S, f, b))` exceeds the number
of vertices of the face. A coordinate flip changes parity, so adjacent
vertices in the same class have opposite function values (`ParityClassEdge`).
