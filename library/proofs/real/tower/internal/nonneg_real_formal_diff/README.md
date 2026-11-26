# nonneg_real_formal_diff — formal differences (the real tower's third level)

The `nonneg_real_formal_diff` family represents real numbers as **formal
differences** of nonneg reals: a `treal` value is a pair
`(a, b) : hreal × hreal`, morally `a − b`. Two pairs name the same
difference iff their cross-sums agree, and both the layer's
equivalence and its order are cross-sum comparisons:

    treal_eq(x, y)  ⇔  fst(x) + snd(y) = fst(y) + snd(x)
    treal_le(x, y)  ⇔  hreal_le(fst(x) + snd(y), fst(y) + snd(x))

The constants are all the chapter's own definitions
(`definitions.go`), written through `fst` and `snd`. The same
equations stated by matching a pair pattern would mint identical
constants, since a pattern definition reduces to exactly this form.

The ring operations are componentwise / bilinear on the pair:

    treal_add(x, y) = (fst(x) + fst(y),  snd(x) + snd(y))
    treal_neg(x)    = (snd(x),           fst(x))
    treal_mul(x, y) = (fst(x)·fst(y) + snd(x)·snd(y),
                       fst(x)·snd(y) + snd(x)·fst(y))
    treal_of_num(k) = (hreal_of_num(k),  hreal_of_num(0))

`treal_inv` breaks that pattern: it is a **three-way case split** on
how the pair's components compare. Equal components (a representative
of zero) map to the zero pair; each strict branch inverts the
Hilbert-chosen GAP between the components — the ε-witness of strict
dominance, `gap u v = εd. u = v + d`:

    treal_inv(x) = (0, 0)                                if fst x = snd x
                 = (hreal_inv(gap (fst x) (snd x)), 0)   if snd x ≤ fst x
                 = (0, hreal_inv(gap (snd x) (fst x)))   otherwise

This one idea — reason about the chosen gap through its ε-defining
equation — carries the family's two hardest files: MulLeftInverse's
`gapUnit` (`1 + inv(ε)·x = inv(ε)·y` for the gap ε of a strictly
dominated pair) and InvWellDef's `gapTransport` (the x-side ε-witness
ALSO realizes the y-side gap across a cross-sum equation).

The chapter proves, always **up to `treal_eq`**: the equivalence tier
(TrealEqRefl / TrealEqSym / TrealEqTrans, assembled as TrealEqEquivalence — `treal_eq` is an equivalence relation, an instance of relations/equivalence);
the commutative-ring laws with additive inverse and multiplicative
inverse away from zero (plus the strict-equality forms AddSymEq /
MulSymEq, where the pair identity happens to hold on the nose); the
total order with its add/mul compatibility laws; the ℕ-embedding
morphism laws (OfNum*); and — the chapter's actual export — the
**welldef tier**: Add / Neg / Mul / LessEq / Inv / OfNum all respect
`treal_eq`.

Those movements are the chapter's parts, and each welldef theorem lives with
the operation it is about rather than in a tier of its own:
the equivalence relation, addition (with negation), multiplication,
the order, the numeral embedding, and the inverse.

Unlike `nonneg_real`, this is NOT a quotient layer: everything lives on
the raw pair type, and `treal_eq` is passed forward unquotiented. The
next layer (`real_construction`) constructs `real` as the quotient
`treal/treal_eq` (via `mk_real ∘ treal_eq`), and the welldef theorems
are precisely the **descent data** that quotient consumes: each
operation descends to `real` exactly because it respects `treal_eq` —
which is why AddWellDef and its siblings exist as members here. The
component calculations unfold treal constants and use nonnegative-real
laws. `LessEqWellDef` instead reads `treal_eq` as two-sided order and
transports comparisons by transitivity.

## Mechanics

Statement vocabulary is vocab.go's rows, handed to a body by `ops(ctx)`
(`treal_{add, mul, neg, inv, of_num, eq, le}` plus the hreal-side
subset `hreal_{add, mul, inv, le, of_num}`). The pair
projections come from `cartesian/pairs`: a proof that needs them
reads `pairs.Fst` / `pairs.Snd` and claims the certs
with `ctx.Dep(pairs.Fst)` (members that never project pairs read
neither). Where the
projections sit over literal pairs, `PairCollapse` drives them out and
that is all the proof needs; a proof that must name the monomorphic
constants in its own statement text declares them via `ctx.Const`.
Entry vars are
CamelCase, no prefix; registered names are dot-qualified
`nonneg_real_formal_diff.<Var>`.
