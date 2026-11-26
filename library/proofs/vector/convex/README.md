# convex — convex sets, and the combinations they are closed under

A set of vectors is convex when it contains, with any two of its points,
every weighted average of the two. The definition names both weights
rather than one: `c • x + d • y ∈ s` for nonnegative `c` and `d`
totalling one. That is the symmetric form, and it is the form a fold's
recursion produces — a new point arrives with its own weight beside the
total weight of everything already summed, two numbers with no
subtraction between them. The familiar one-parameter test, with `t` and
`&1 - t`, is the same condition and is a theorem here.

The chapter works at ℝ, where the weights live: the family binds the
real ring's components once (`WithInstance(comm_ring.CommRing,
real_ring.CommRing)`), so a statement spells `c • x` and `x + y` and
means `vec_scalar_mul(real_mul, c, x)` and `vec_add(real_add, x, y)`. No dimension
appears anywhere. Convexity reads no active range — it is a condition on
a set of sequences, not on a set of n-vectors — so every theorem below
holds at every dimension at once, and `vec⟨n⟩(·)` is never mentioned.

`Σ` resolves by its summand's type, as `+` and `•` do by their operands'.
The two in one equation below are two different folds: `Σ_{i∈k} u(i) • x(i)`
is `iterated_op(vec_add, …)`, the fold over the module, and `Σ_{i∈k} u(i)` beside it
is the Σ chapter's `real_sum`, the fold over ℝ. That they step together over the
same index set is what the chapter's induction runs on.

What the chapter is for is the last theorem: a convex set holds every
convex combination of finitely many of its points. The route to it does
not go through the definition repeatedly. It goes through the CONE over
the set — the points of `s` scaled to an arbitrary height, each read
together with the height it was scaled to — because the cone is what a
fold can accumulate. A fold of weighted points is not itself a point of
`s`, and there is nothing about it to carry from one step to the next
except that it stands at some height above some point of `s`; that pair
is what the induction carries, and convexity is what combines two of
them into one.

The alternative, and the reason for the cone: one can instead induct on the
headline directly, dividing the surviving weights by their running total at
each step so that they total one again.
That route needs the scalar action to commute with the fold, and it rescales
every remaining weight at every step. Carrying the cone rescales nothing: the
step hands two weights to a law that takes them as they stand, and the only
division in the chapter is the one inside that law's witness.

## The definitional layer (definitions.go)

| constant | reading |
|---|---|
| `convex(s)` | every weighted average of two points of `s`, at nonnegative weights totalling one, is a point of `s` |

## What the definition says directly (sets.go)

Nothing here is constructed. Each member is the definition read back — at
a different pair of weights, or at a set whose membership settles the
question before the weights are looked at. In none of them does the
module enter: the weighted average is carried from hypothesis to
conclusion as it stands and is never expanded.

| member | statement |
|---|---|
| `Segment` | `convex(s)` exactly when `(&1 - t) • x + t • y ∈ s` for all `x`, `y` in `s` and every `t` between `&0` and `&1` — a pair of weights is a parameter and its complement, and renaming them is the whole proof |
| `Empty` | `convex(∅)` — the condition asks for two points of the set, and there are none, so the average it would have been read at is never formed |
| `Univ` | `convex(𝕌)` — the condition's conclusion is a membership every vector satisfies, so it holds before anything asked of the weights is read |
| `Inter` | `convex(s) ⇒ convex(t) ⇒ convex(s ∩ t)` — the condition on the intersection is the conjunction of the two conditions, asked of the same average of the same two points |

## The cone, and the two facts a fold needs of it (cone.go)

Above a convex set sits its cone: the points `t • w` with `w` in the set,
each read at the height `t` it was scaled to. `PositiveCombination` is the
law that makes it a cone, and convexity is what supplies the underlying
point — the two heights, taken against their total, are weights totalling
one, and the witness is the average they take of the two given points.
Scaling that average back to the summed height undoes the rescaling and
returns the sum it came from.

Neither height is required to be positive, only their total. That is what
a fold needs: at each step it holds the weight of a new point beside the
total weight of everything already summed, either of which may be zero,
and it applies the law to those two numbers as they stand.
`VanishingWeights` is the one case the law cannot reach — a total weight
of zero, where there is no point to carry at all.

| member | statement |
|---|---|
| `PositiveCombination` | for `s` convex, `p` and `q` in `s`, and nonnegative `a`, `b` with `&0 < a + b`: `a • p + b • q = (a + b) • w` for some `w ∈ s` |
| `VanishingWeights` | for `k` finite with `&0 ≤ u(i)` at every `i ∈ k`: if `Σ_{i∈k} u(i) = &0` then `Σ_{i∈k} u(i) • x(i) = vec_zero` — the weights are each zero, so every point enters scaled by zero, and a fold whose terms are all the element it starts from is that element. Convexity takes no part in it, and the points are unconstrained |

## The cone along a fold, and the theorem (fold.go)

The cone is closed not only under addition but under finite sums, and
that is the chapter's one induction — over the index set, in the strong
form, with the fold over ℝ and the fold over the module stepping
together. Each step hands `PositiveCombination` the new point at its own
height beside the point the rest already stands above, and their total is
the enlarged total. The pair fails in exactly one place, a total height of
zero, where every term is weightless and the fold is the zero vector:
there any point of `s` will do, and the one just laid in is one.

The headline is that theorem read at total weight one. Weights totalling
one total more than nothing, so the cone applies; and a weight of one
scales nothing, so the height that carried the whole induction
disappears, leaving the combination equal to the point it stands above.

| member | statement |
|---|---|
| `ConeIterate` | for `s` convex, `k` finite, and `&0 ≤ u(i)` with `x(i) ∈ s` at every `i ∈ k`: if `&0 < Σ_{i∈k} u(i)` then `Σ_{i∈k} u(i) • x(i) = (Σ_{i∈k} u(i)) • w` for some `w ∈ s` |
| `Combination` | under the same hypotheses with `Σ_{i∈k} u(i) = &1`: `Σ_{i∈k} u(i) • x(i) ∈ s` — a convex set holds every convex combination of finitely many of its points |
