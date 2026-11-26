# peano — the construction of ℕ

This is `nat_num`'s basement. Every other chapter in the domain — the
arithmetic operations, the order predicate, everything standing on
them — quantifies over `num` and uses induction on it. This chapter is
where `num` comes from and why induction is available.

The story has three acts, and the interesting thing about it is how
little it assumes: one axiom, one type definition (made here, on a
proved inhabitant), and an inductive predicate. Exactly one step reaches outside the chapter — turning the
graph of a recursion into a function needs "a relation with one value
per argument is a function's graph", which is pure logic over two
arbitrary types and belongs to no chapter of ℕ.

## Act I — an infinite type

The only thing postulated outright is the **axiom of infinity**,
`Infinity`, the corpus's one postulate: there is a function
`f : ind → ind` that is injective and a point `z` it misses. That is the
entire input. `ind` is otherwise an opaque type with no structure at
all.

It is the right hypothesis because it hands us both Peano axioms in
embryo: `z` behaves like zero (nothing maps to it) and `f` like
successor (distinct inputs, distinct outputs). "Injective and not
surjective" is the same content up to classical logic; stated with the
missed point, the axiom names what the zero has to be. Injectivity is
stated as the implication alone — its converse is congruence, a theorem
of the logic, which an axiom does not assert. The first act's work is
to NAME the pair: `ind_suc` and `ind_zero` are Hilbert choices of an `f`
and a `z` witnessing the axiom.

Naming them is what makes the two facts stateable without an existential
in front: `ind_suc` never hits `ind_zero`, and `ind_suc` is injective.
Those two are the whole harvest of Act I, and they are jointly one
statement — the specification of the chosen pair — of which each is a
projection.

The choice is sequential rather than simultaneous, and the proof's shape
follows: `ind_suc` is chosen first, from the injections that miss some
point, and `ind_zero` is then chosen from the points that *this* injection
misses. So the second choice's inhabitation obligation is exactly what
the first one produced.

## Act II — carving ℕ out of `ind`

`ind` is far too big: it contains the numerals but also whatever else.
`is_num` is the predicate cutting them out, defined as the *smallest*
subset of `ind` containing `ind_zero` and closed under `ind_suc`. Being
smallest is not a side condition here — it is the load-bearing half.
A definition by rules comes with its theorems, and their asymmetry is
the point:

- **rules** — `is_num` really does contain `ind_zero` and really is closed
  under `ind_suc`. This is what "the set exists" buys.
- **induction** — any *other* predicate with those two closure
  properties contains all of `is_num`. This is what "smallest" buys,
  and it is already the induction principle, one type down. Its
  strengthened form, which tells the step that the point it climbs from
  is itself a representative, is what carries the principle up into
  `num`.
- **cases** — the two rules are exhaustive as well as sound. Nothing in
  the chapter needs it; it is here because the definition comes with it.

`num` is then the type in bijection with `{a : ind | is_num a}`, via
the pair `mk_num` / `dest_num`. `0` and `suc` are transported across:
`0` is `mk_num(ind_zero)`, and `suc n` is `mk_num(ind_suc(dest_num n))` —
go down to `ind`, step, come back.

## Act III — the Peano axioms

With the bridge in place, each Peano axiom is its `ind`-level
counterpart transported through it, and the transport is the actual
work.

- **`suc n ≠ 0`** — because `ind_suc` misses `ind_zero` downstairs.
- **`suc m = suc n ⇒ m = n`** — because `ind_suc` is injective, plus
  the bijection to undo `mk_num`.
- **induction on `num`** — `is_num`'s minimality, with the predicate
  pulled back along `mk_num`.
- **case analysis** (`n = 0` or `n = suc m`) — a first consequence of
  induction rather than a separate construction.
- **primitive recursion** — every `(e, f)` determines a unique function
  `fn` with `fn 0 = e` and `fn (suc n) = f (fn n) n`. This is the
  theorem the rest of `nat_num` is built with: every recursive
  definition in `nat_arith` is an instance of it.

  Its existence half is the chapter's one genuinely different move, and
  worth knowing before reading the file. `fn` cannot be written down —
  it is defined by what it does, not by a formula — so the proof does
  not construct the function at all. It constructs its **graph**: the
  smallest relation containing `(0, e)` and closed under
  `(m, b) ↦ (suc m, f(b, m))`. That is Act II's construction over
  again, one level up, and minimality is again the load-bearing half —
  closure alone makes the graph total, minimality makes it
  single-valued. A total single-valued relation is a function, and the
  recursion equations then read straight off the graph's two rules.
  Uniqueness is a separate and much easier induction.

The transport steps all lean on the same facts about the bijection and
the two definitions, so those are stated once in this chapter rather
than re-derived per theorem.

## Naming note

Only the facts later chapters cite carry a chapter name (see
`../../README.md`) — `SucNotZero`, `SucInjective`, `Induction`, `Cases`
and `Recursion`; everything the construction needs on the way is
demoted to an internal lemma, fully verified and typed-citable inside
the family.

## Reading the files

Two chapter-specific mechanics worth knowing before reading a proof
body:

- **The axiom of infinity is the member `Infinity`**, built by
  `family.Postulate`: its term is assembled in Go from the logic's
  constructors and checked against the stated text, and the registry
  admits no second postulate. It is cited in exactly one place,
  `indSucSpec`, the specification of the chosen pair; nothing else in
  the chapter reaches past that theorem to the axiom itself.
- **Everything else is defined here.** `indSucDef` and `indZeroDef`
  choose the successor and zero of `ind`; `is_num` is the inductive
  predicate, defined by its two rules through `family.DefineInductive`
  — `isNumRules`, `isNumInduct`, `isNumCases` and `isNumInductStrong`
  are its four readings, and nothing unfolds it; `NumDef` is the type definition — `family.DefineType`,
  minted on the promise of `isNumZero` (`is_num(ind_zero)`, the
  inhabitant a type definition must be shown) and yielding
  `NumDef.Retraction` and `NumDef.Membership`, the two halves of the
  bijection; `ZeroDef` and `SucDef` are the constants transported into
  `num`. That is why Act II's rules come before the bridge and not
  after: the inhabitant is proved from them.
