# int_construction — how ℤ is built out of ℝ

The integers are not axiomatized. They are carved out of the reals:
`integer x` says some natural has `x` as its absolute value, `IntDef`
mints the type whose points are exactly those reals, and `real_of_int`
is the map back — a bijection onto `integer`, with `int_of_real` its
inverse there. Every operation on ℤ is then *defined* by transport:
`x + y` is whatever integer represents `real_of_int x + real_of_int y`,
and the theorem saying so (`AddBridge`) is a homomorphism law rather
than a computation.

This chapter is those statements and nothing else. The dividing line is
`real_of_int`: a statement that NAMES it is about the construction and
is this family's — as is a statement in ℤ's own vocabulary whose entire
proof is unfolding definitions made through `real_of_int` (the
comparison flips and the absolute value's conditional), which has no ℤ
mathematics in it to give another chapter; any other statement in ℤ's
own vocabulary belongs to one of the sibling chapters — `int_real_lift` when it is a lift,
`int_embed` when its subject is the ℕ↔ℤ boundary, `int_div_rem` or
`int_divides` when it is native ℤ mathematics.

`int_embed.Image` (`∀x:int. (∃n. x = &n) ∨ (∃n. x = -&n)`) is the one
apparent exception and is not one: its statement is about `&`, and only
its proof reaches down here.

`integer`, `int_of_num`, `int_le`, `int_lt` are definitions, not
theorems — and the four order bridges in particular are definitions
whose defining equation IS the bridge. There is nothing there to prove.

## The chapter's own story

**The definition of `integer` is not the form anyone uses.** Written out
it says "some natural is my absolute value", and no proof in this
chapter or above it reasons about an absolute value. What every later
statement actually wants is the ± form — a real is an integer exactly
when it is `&n` or `-&n` for some natural n — and translating between
the two is the chapter's first member. Opening the conditional hidden
inside `real_abs` is the whole cost of that translation, so it is paid
once, in a lemma, and never again.

**The type comes with two axioms and they are what make ℤ a subset.**
A type definition may only be stamped against a predicate that holds of
something, and the inhabitant here is `&0`. What the stamp returns is a
pair: every integer survives the round trip down to ℝ and back, and a
real survives the round trip up and back exactly when it satisfies the
carving predicate. Together they say ℤ *is* that set of reals rather
than a quotient of it — which is why an argument may state something
about ℤ, prove it about representatives, and read the result back.

**Everything else is those two read at a representative.** A
representative satisfies the predicate; a representative is therefore
±a natural; representatives determine the integers they came from. Then
each operation's bridge is the same move once more: the operation is
*defined* as "transport the ℝ answer", so its law is the membership
axiom read at that answer, and the member's own content is the argument
that the answer is again an integer.

## Public surface

| entry | says |
|---|---|
| `IntegerIffPlusMinusNat` | a real is an integer ⇔ it is ±a natural |
| `IntegerOfNum` | a natural seen in ℝ is an integer |
| `IntegerSquareNatural` | the square of an integer is the square of a natural: `integer(x) ⇒ ∃n. x * x = &n * &n` |
| `IntegerAbsLessOne` | an integer smaller than 1 in size is 0: `integer(k) ∧ \|k\| < &1 ⇒ k = &0` |
| `TypeBijection` | the two axioms `int` was stamped with |
| `RepresentativeIsInteger` | a representative satisfies the carving predicate |
| `RepresentativeIsPlusMinusNat` | a representative is ±a natural |
| `RepresentativeInjective` | equal representatives come from equal integers |
| `OfNumBridge` | `&n`'s representative is `&n` |
| `NegBridge` | negation transports |
| `MaxBridge` | the larger of two transports |
| `MinBridge` | the smaller of two transports |
| `SgnBridge` | the sign transports |
| `AbsBridge` | the absolute value transports |
| `MulBridge` | multiplication transports |
| `AddBridge` | addition transports |
| `SubBridge` | subtraction transports |
| `GreaterIffLess` | `x > y` is `y < x`, by unfolding the definitions |
| `GreaterEqIffLessEq` | `x ≥ y` is `y ≤ x`, likewise |
| `AbsBySign` | the absolute value as a conditional on the sign, read back from ℝ |
| `IntegerClosedUnderAdd` | a sum of integers is an integer |
| `IntegerClosedUnderMul` | a product of integers is an integer |
| `IntegerClosedUnderNeg` | a negated integer is an integer |

Together the last three say ℤ is a SUBRING of ℝ — which is the natural
next thing to know about a set you have just carved out, and the reason
four of the nine bridges spend one of them.

The `…Bridge` group is one theorem in nine instances: `real_of_int` is a
homomorphism, one operation at a time. (The tenth such bridge is
`int_num/int_pow`'s `PowBridge`: ℤ's power is a derived operation, so
its bridge lives with the power chapter, not with the construction.)

**The embedding as one rewrite.** `InReals` is the ring's readings as
a single rule set (`proof.RuleSet`): an integer equation becomes the
equation of the representatives (`RepresentativeInjective`), a comparison
its definition (the four order constants), and a numeral, negation, sum,
difference or product crosses by its bridge. A chapter that borrows a
theorem of ℝ for ℤ writes one move, `Simp(int_construction.InReals, …)`,
and then cites the real theorem — `vector/lattice`'s order facts are the
first consumers. The absolute value, sign, max and min are not ring
operations and keep their own bridges.

## Reading the files

- The predicate and the type: `IntegerIffPlusMinusNat`,
  `IntegerOfNum` (the one integrality fact the chapters above want on
  sight, stated once rather than read out of the ± form at each use)
  and `TypeBijection`. They are one unit because the type's only
  mathematics is its inhabitant, `IntegerOfNum` read at `&0`.
- The three facts about `real_of_int x`, each
  closing in one step off the facts above it.
- `squares.go`: `IntegerSquareNatural`, an integer's square read as a
  natural's, read off the ± form: a negative's square is its
  negation's.
- `magnitude.go`: `IntegerAbsLessOne`, read off the absolute-value
  form of the carving predicate: the natural |k| is below 1.
- What the carved set is closed under. Three ℝ-side laws
  with no `real_of_int` in them at all, and the facts the operation
  bridges spend: a bridge whose ℝ answer combines two representatives
  gets its integrality from here rather than re-deriving it.
- The nine homomorphism laws. Each is its ℤ operation's
  definition unfolded, the membership axiom read at the ℝ answer, and in
  between the one thing that differs: the argument that the answer is
  again an integer. That argument is a named claim in the body, so a
  reader can see what each bridge actually needs, and the file is
  ORDERED BY IT — from the answers that need no argument to the ones
  that need the most:

  nothing at all for `&n`, which is its own representative; then the
  answers selected from something already known to be an integer — the
  negation of a representative, the larger or smaller of two, the sign,
  which is one of three constants; then the absolute value, two ℝ laws
  away from the ± characterization; and last the three that combine two
  representatives and spend a closure law — product, sum, difference.
  (The tenth bridge, the power's, is an induction over the
  multiplicative closure law and lives in `int_num/int_pow`.)

Corpus-wide conventions — ground-cite witnesses, the `↦` marker,
comment policy, statement style — are in
[proofs/README.md](../../README.md) and are not restated here.

Two things specific to this chapter:

**ℤ and ℝ appear as PEERS.** Every statement lives across the
bijection, so both alphabets are declared (`vocab.go`) and `&` is
genuinely ambiguous — `int_of_num` on one side of a ± characterization,
`real_of_num` on the other. The type of the surrounding term is what
resolves it, so a statement whose only content is `&`-terms would be
read entirely in ℝ; where a member BUILDS one of the two it takes the
named vocabulary handle rather than spelling a `ctx.Const`, so which
map is meant is visible in the Go.

**The type-definition axioms come from one call.**
`ctx.TypeDefExpand("int_of_real", <a proof of ∃x. integer x>)` returns
the retraction and the membership criterion together, taking the
inhabitant as its argument — which is why `TypeBijection`'s inhabitant
lemma comes first and why no other member in the chapter calls it. They
cite `TypeBijection` instead.
- The comparisons and the absolute value, read back on ℤ: three
  definitional unfoldings — `>` and `≥` as flips, `int_abs` as a
  conditional on the sign through AbsBridge and NegBridge.

## Why the chapter exists

Not for its readers in the corpus — it has one. `int_embed.Image` is the only
member that cites this layer.

The reason is the lifting. Every `family.Lifted` member of
`int_real_lift` and the lifted members of `int_embed` and `int_div_rem`
are ℝ laws read back through `real_of_int`, and the rewrite that reads
them back is made of the homomorphism bridges proved here. So ℤ's entire
*inherited* algebra — everything the domain does not prove natively —
rests on this layer, reached through the lift rather than through a
citation. That route is invisible to the reader of any file.

The bridges the lift rests on are `int_eq` and the ten `*_th`
homomorphism bridges (nine proved here; `int_pow_th` is
`int_num/int_pow`'s). The predicate and the type bijection are not
among them: they are this chapter's own foundation, and they reach the
lift only through the bridges that cite them.
