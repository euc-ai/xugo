# pairs — the binary cartesian product

Everything in this chapter is one construction seen from above. Inside
`A → B → bool` sits the family of predicates that hold of exactly one
argument pair — `mk_pair(x, y)` is the one picking out `(x, y)` — and
`prod(A, B)` is declared to be a type in bijection with that family,
via `mk_prod` / `dest_prod`. The pairing constructor `(x, y)` is
nothing but `mk_prod(mk_pair(x, y))`.

The chapter unfolds in five parts:

- **Construction.** Two facts pin
  the type down: pairing is injective (`PairEq` — components can be
  read back off a pair), and it is surjective (`PairSurjective` —
  there is nothing else in the type). Together they say `prod(A, B)` is exactly the pairs, and
  they are the only members that argue below the type; everything above
  is transport. Both take their input from the two facts the type
  definition comes with — `ProdDef.Retraction` and `ProdDef.Membership`
  in [definitions.go](definitions.go), where the chapter mints the type
  and every constant stated over it (`mk_pair`, `,`, `fst`, `snd`,
  `pattern_abstraction`) — so this chapter's floor is the kernel, not another theorem.
- **Projections.** `Fst`
  and `Snd` turn the construction's existence claim into maps: the components a
  pair determines can now be NAMED, which is what every later
  statement about pairs is written with. `PairEta` closes the loop —
  `(fst p, snd p) = p` — so constructor and projections are mutually
  inverse and nothing is lost either way round. Both projections are
  choice terms, and the file says what each proof has to show about
  the choice. `PairInjectiveLeft` and `PairInjectiveRight` read `PairEq`
  as a map's property: pairing with a fixed component, on either side, is
  one-to-one.
- **Structure.** The pair
  type's recursion and induction, and the quantifier transports
  (`∀p. P(p) ⇔ ∀x y. P((x, y))` and kin) that let every later chapter
  state pair facts componentwise. Every member here rests on the same
  fact — `PairEta` — and most are a single justified step;
  the file says which cost more and why.
- **Paired binders.** Writing
  `λ(x, y). body` is not a primitive: it names some function on the
  product agreeing with `body` at every literal pairing, if one exists.
  This part says what that comes to — `PairedLambdaEta`, that every
  function on a product already IS its own paired abstraction, and
  `PairedLambda`, that the abstraction of a two-argument `g` is the map
  which projects and applies. Below the abbreviation the argument is
  about a choice; above it, it is `PairEta` from the projections once more —
  pinned at every pairing is pinned everywhere, because every point is
  a pairing.
- **Currying.** A function of two
  arguments and a function on the product carry the same data written
  two ways, and the quantifiers cannot tell the two ways apart: what
  holds of every two-argument function holds of every function on the
  product read through currying, and dually for a witness. The reason
  is that currying is ONTO — every two-argument function is somebody's
  curry — which is the recursion principle from the structure part and is the only
  thing the ∀ half uses; the ∃ half is that same statement read at a
  complement. Nothing here opens `λ(x, y). body` at all.

## The definitional layer

The chapter defines its own vocabulary, in [definitions.go](definitions.go):

| entry | defines |
|---|---|
| `MkPairDef` | `mk_pair(x, y) = λa b. a = x ∧ b = y`, a pair as the predicate of its components |
| `ProdDef` | the type `prod(A, B)` — the predicates of that shape; `ProdDef.Retraction` and `ProdDef.Membership` are its two axioms |
| `PairDef` | `(x, y) = mk_prod(mk_pair(x, y))` — the constructor `,`, minted from a Go payload since the DSL cannot spell `,` in head position |
| `FstDef`, `SndDef` | the projections as choice terms |
| `PatternAbstractionDef` | `pattern_abstraction(P) = εx. P(x)`, the abstraction a pair-pattern λ lowers to |

The inhabitation of `prod` is trivial — any `mk_pair(a, b)` has the
shape — and is proved at the mint by normalization.

## Members without a public name

The exported members — `PairEq`, `PairSurjective`, `Fst`, `Snd`,
`PairEta`, `PairInjectiveLeft`, `PairInjectiveRight`, `PairRecursion`,
`ForallPair`, `ForallPairFun`, `PairedLambdaEta` and `PairedLambda` — are the
chapter's public API,
not its full membership. Further theorems are proved and verified here
without a public name,
because nothing outside this chapter cites them: the induction
principle and two ∃-mirrors (`pairInduct`, `existsPair`,
`existsPairFun`, with the structure part), and the ∀ and ∃
forms of the uncurrying transport (`forallUncurry`, `existsUncurry`, in
with currying). They are lowerCamel entry vars. A name is for
the facts later chapters reach for, and these are not yet among them —
which for the uncurrying pair is worth saying out loud, since currying
is one of the five parts above and a reader could reasonably go looking
for it among the exported names.

## What is not here

**The curry direction.** The transport above runs one way — from a
function on the product to the two-argument function it induces. The
reverse reading is the same correspondence turned round, and no
chapter states it, because no chapter has yet needed to cite it that
way.

**The product of two SETS.** A set of pairs drawn from a set of first
coordinates and a set of second ones is a different subject from the
pair type, and it lives where sets do rather than here: the counting
laws a reader is most likely to be after — how many pairs such a
rectangle holds — are `sets/cardinality`'s `CardProduct` and
`HasSizeProduct`. The finite cartesian POWERS, where a dimension is a
type, are the `cartesian/carrier` chapter's subject and are built
term-level there. What this chapter carries is the type itself: how a
pair is built, taken apart, and quantified over.

## Using the chapter from elsewhere

Two surfaces, and a consumer usually needs both. The THEOREM surface is
the exported entry vars, cited by name. The DECLARATION
surface is [alphabet.go](alphabet.go), which serves the chapter's
constants at whatever component types the consumer works at:

- `pairs.ProdType(a, b)` — the type `prod(a, b)`.
- `pairs.ProjectionsAt(ctx, a, b)` — `fst` and `snd` declared at those
  components, handles returned.
- `pairs.PairAt(ctx, a, b)` — the pairing constructor, for building
  pair terms (statements get `(x, y)` from the text-DSL for free).
- `pairs.Collapse(ctx)` — drive every `fst`/`snd`-of-a-literal-pair
  redex out of the goal, at this chapter's projection theorems. The
  caller reads `pairs.Fst` and `pairs.Snd` through its own script, so
  its recorded deps carry them and bound its replay.

The second surface exists because a consumer builds in its own script,
which does not carry this chapter's vocabulary, and meets `prod` at its
own instance: the integer division chapter at `(int, int)`, the monoidal
iterates at `(A, C)`. The spelling of `prod` and of its constants at any
instance lives here, not at the call sites.

## One note for readers of consumers

An entry's headline is what a reader sees and what the dep model serves.
It is not always the form a citation INSTALLS. Naming a dep — in a
`Cite`, in a `By` premise list, as a `Simp` rule — resolves it to its
canonical install form, which is `Normalize`'s, and `Normalize` is free
to move things the headline does not advertise. Two of its moves show up
in this chapter:

- **Orientation.** `Fst` READS `fst((x, y)) = x` and INSTALLS as
  `x = fst((x, y))`.
- **Extensionality.** `PairedLambdaEta` READS as an equation between
  functions — `∀t. t = λ(x, y). t((x, y))` — and INSTALLS as the
  pointwise reading, with a `∀` over points in front of it.

Most consumers meet neither. Where projections sit over literal pairs —
by far the common case — the `PairCollapse` primitive drives them out to
fixpoint and orientation is its problem, not the caller's. Orientation
matters only for a consumer that hands the rule to `Simp` and must flip
it; the two gcd chapters under `int_num/` are the corpus's only such
sites, and both say so at the call. Extensionality matters only where
the goal is itself an equation between functions, and there the move is
to cite the proved headline rather than the entry — the final calc leg
among the paired binders is this chapter's one such site, and says
why.

Mechanics (typed cites, recorded deps, the shared CNF blob, replay) are the standard
family framework — see `library/registry` and the constitution.
