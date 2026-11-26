# carrier — dimensioned tuples with the dimension as a number

A tuple of dimension `n` here is an ordinary function `num → A` whose
entries outside the active range `0..n-1` are pinned to `junk`, the
default element sets/functions mints. That convention — membership
`tuple`, not a type — is the chapter's one idea: the dimension is a
TERM, so a statement may quantify over it, compute with it, and relate
tuples of different dimensions by plain index arithmetic, none of
which the type-level `A^N` of the sibling chapters can spell.

## The definitional layer (definitions.go)

The chapter owns four constants, each defined through the define door
(`family.Define`) and cited in proof bodies through its definition entry
or its defining theorem (`ctx.ConstDefNormalized`):

    tuple      : num → (num → A) → bool                membership: junk past the range
    tuple_cat  : num → (num → A) → (num → A) → num → A concatenation at a cut
    tuple_take : num → (num → A) → num → A             the low block / the normalizer
    tuple_drop : num → (num → A) → num → A             the high block, shifted past the cut

## The members

The members are term-level twins of the statements a development with
the dimension in the type makes:

- **Extensionality** — two tuples of one dimension are
  equal exactly when their active entries agree. The junk convention
  is what makes this plain `=`: past the range neither tuple says
  anything of its own.
- **HighBlockRoundTrip** — the high block of a
  concatenation reads back. The dimension arithmetic (`i + n`,
  `(i + n) - n`) is ordinary nat arithmetic where the type-level original
  moves between `finite_sum` types.
- **ConcatInjectivity** — a concatenation determines
  its blocks. Proved THROUGH another member (both directions close
  through Extensionality, once per dimension), and written in the
  dimension-refined vocabulary — see below.

`ConcatClosed` is deliberately not a twin. It is the native term-level
closure law needed by the refined face: inhabited blocks concatenate to
an inhabited block of the sum dimension.

## The dimension-refined face (vectors.go)

A proof body here may opt into `dimtypes`' refinement: `Inhabit[A, DimN]`
combines a statement binder with its membership antecedent into one
`InhabitedVec[A,N]` — checked, so the phantom label is made TRUE at the
adoption site and cannot later be crossed with another vector — and a
theorem's `AtVec` cites at vectors whose dimension witnesses write themselves
(read off the checked memberships), with the evidence traveling inside
the citation as one premise group. Citing the low-tuple law at the
high dimension is a compile error; crossed evidence is unrepresentable
because it is no longer a separate value. The refinement never reaches
the kernel: an AtVec lowers to exactly the untyped cite plus the membership
premises.

The same face composes evidence rather than dropping it: `Concat`
uses `ConcatClosed` to return an inhabited `(n+m)`-vector, and
`Recast` transports that membership through an explicit resident
dimension equality. Bare `dimtypes.Vec` remains evidence-free; only
the proof-layer wrapper promises inhabitation.

## How this chapter stands to the type-level one

Indexing is 0-BASED throughout — the chapter's own convention: one-atom
guards (`i < n`), a COND-free `tuple_drop`, no index-zero case in any
second-block law, and exponent alignment with the words face and the nat
substrate. The type-level statements guard their components 1-based; the
difference is a change of index variable.
