# int_embed — the ℕ↔ℤ boundary

The embedding `& : num → int` (`int_of_num`) and its partial inverse
`num_of_int`: the chapter that lets a fact cross between ℕ and ℤ. Its
subject is everything that crossing preserves — each operation in turn,
which integers `&` reaches, and what `num_of_int` brings back.

This is the domain's outward-facing chapter. ℕ's number theory is not
defined by pushing the arguments through `&` and asking the question in
ℤ: ℕ's divisibility, gcd, congruence and primality are defined inside ℕ
(`nat_num/nat_divides`, `nat_gcd`, `nat_congruence`, `nat_prime`), and what
the crossing leaves is a
transport law per relation, each beside the ℤ relation it lands in:
divisibility's in `int_divides`, congruence's in `int_congruence`.

## What `&` preserves

`&` is an embedding of ordered semirings, and the first group of members
is that one sentence, clause by clause: it is injective, it respects
each operation, and it reflects the order.

- **`OfNumEq`** — `∀m n:num. &m = &n ⇔ m = n`. Injectivity, which is
  what lets an equation be argued in ℤ and read back in ℕ.
- **`OfNumAdd`**, **`OfNumMul`** — `&` is additive and multiplicative:
  the ring-map half.
- **`OfNumLe`**, **`OfNumLt`** — `&` reflects `≤` and `<`, so an
  inequality may be argued on either side and read on the other.
- **`OfNumAbs`** — `∀n:num. |&n| = &n`. The image of `&` is where `|·|`
  acts trivially — the fact every descent from ℤ turns on.
- **`OfNumSuc`** — `∀n:num. &(suc n) = &n + &1`. Successor becomes
  adding one, which is what lets an induction be run in ℕ and its
  conclusion read as ℤ arithmetic.
- **`OfNumMax`**, **`OfNumMin`** — `&` commutes with taking the larger
  and the smaller, the two-argument face of the order embedding.

The POWER clause of the same sentence — `&(xⁿ) = (&x)ⁿ` — is
`int_num/int_pow`'s `OfNumPow`: ℤ's power operation has its own
chapter, and its embedding law lives with it. The CONGRUENCE clause —
`x ≡ y (mod n) ⇔ &x ≡ &y (mod &n)` — is `int_num/int_congruence`'s
`OfNumCongruent`, and the DIVISIBILITY clause — `d ∣ n ⇔ &d ∣ &n` —
is `int_num/int_divides`'s `OfNumDivides`, both for the same reason:
the ℤ side of the clause is that chapter's relation, defined above
this one.

Two operations do not cross that cleanly, and they are the interesting
ones.

- **`OfNumSub`** — `∀m n:num. m ≤ n ⇒ &n - &m = &(n - m)`. The only
  transport law carrying a hypothesis. ℕ's difference is truncated at 0
  and ℤ's is not, so `n - m` in ℕ is the honest difference only where
  nothing had to be thrown away; the hypothesis names exactly that
  region. The proof spends it in a sum: ℤ's difference is
  unconditional, so a difference equation there is a sum equation, and
  a sum is where the truncation would declare itself, since putting `m`
  back recovers `n` exactly when the difference kept everything.
The division pair's transport (`OfNumRem`, `OfNumDiv`) lives in
`int_div_rem`, beside the division algorithm: it exhibits ℕ's computed pair to that
chapter's uniqueness law, so it sits above the int_div/int_rem core rather
than in this boundary chapter.

## Which integers `&` reaches

- **`Image`** — `∀x:int. (∃n. x = &n) ∨ (∃n. x = -&n)`. Every integer
  is ±a natural. This is the one member here not inherited from ℝ, and
  it could not be: it is what ℤ has and ℝ lacks. `int` is carved out
  of ℝ by exactly this predicate (`int_construction`), so the theorem is
  the type's own defining property read back through the bijection.

Sharpen it by asking which integers are naturals outright, and the
answer is the nonnegative ones — a single fact the chapter has four
occasions to state, in four grammars. It is proved once, in
the image section, and the other three occasions cite it. One half of it is
free, and is named separately because four different arguments here
lean on that half alone.

- **`embedNonneg`** — `∀n:num. &0 ≤ &n`. The free half: every image of
  `&` is nonnegative, because `0 ≤ n` holds of every natural and `&`
  reflects the order. Unexported; its job is to be cited.
- **`OfNumExists`** — `∀x:int. (∃n:num. x = &n) ⇔ &0 ≤ x`. The fact
  itself. One direction is `embedNonneg` above. The other is the ±
  analysis, and this is the one place the chapter does it — the minus
  branch of `Image` survives only where it agrees with the plus branch,
  since `&0 ≤ -&n` forces `&n ≤ &0`, which against the always-available
  `&0 ≤ &n` pins `n`'s image at `&0`, where `-&0 = &0`.
- **`NumOfIntSection`** — `∀x:int. &0 ≤ x ⇒ &(num_of_int x) = x`.
  Choice makes `num_of_int` total, so it names some natural for every
  integer; it names the RIGHT one exactly on the nonnegatives, which is
  where the ε has something to choose from.
- **`NumOfInt`** — `∀x:int. &(num_of_int x) = x ⇔ &0 ≤ x`. The same
  fact as a property of the partial inverse: `num_of_int` succeeds
  exactly on the nonnegatives, not merely at least there.
  `NumOfIntSection` is its ⇐ direction, and succeeding at all is
  already the guard, since an `x` its own `num_of_int` carries back to
  is an image.
- **`ForallNonneg`**, **`ExistsNonneg`** — the same fact as a change of
  variable: to quantify over the nonnegative integers is to quantify
  over ℕ through `&`. Each direction wants one half of `OfNumExists` —
  that every nonnegative IS some `&n`, and that every `&n` is
  nonnegative — and the ∃ form is the ∀ form read through negation.
- **`OfNumRetract`** — `∀n:num. num_of_int(&n) = n`. Composing the two
  maps the other way round needs no guard at all, a natural's image
  being in range by construction: the ε has the right natural among its
  candidates, and injectivity of `&` leaves it no other.

`>` has no member. It is notation over `<`, whose transport law is
`OfNumLt`, so a `&`-transport law for it would add a spelling rather
than a fact.

## What ℤ inherits through the boundary

Knowing which integers `&` reaches pays off a second time: four
structural facts about ℤ — the ones ℝ cannot supply — come straight
across it.

**`Discrete`** — `x < y ⇔ x + &1 ≤ y`: there is nothing strictly
between consecutive integers, because the gap `y − x`, being positive,
is the image of a positive natural, and ℕ has nothing strictly between
`0` and `1`. **`DiscreteFlipped`** is the same law read through
`int_gt`/`int_ge`'s definitions. **`Archimedean`** — every integer is
below some multiple of every nonzero `d` — follows from the image being
COFINAL (`∀x. ∃n. x < &n`) and one scaling step that is itself
discreteness. **`WellOrderedBelow`** — a nonempty set of nonnegative
integers has a least element — is ℕ's well-ordering carried across the
quantifier transports of the image section. **`MeasureInduction`** — a
predicate holding wherever it holds at all points of strictly smaller
nonnegative integer measure holds everywhere — is well-ordering spent
as descent: the least counterexample measure would have one below it.
**`PairMeasureInduction`** is the same induction for a two-argument
measure, read at the pair type.

None of the six states a NEW ℝ fact: every dep is a ℤ/ℕ statement
(the `int_real_lift` members among them are themselves transports, but
that is those members' business, not these proofs'). That is the point
— these are the facts that make the DIVISION ALGORITHM terminate and
the EUCLIDEAN DESCENT bottom out. `int_div_rem` cites the first three
inheritances, and `int_divides.Bezout` the measure induction, in its
pair form.

## Finite sets of integers

| Member | Statement |
|---|---|
| `FiniteIntegersBoundedBelow` | a finite set of integers lies at or above −N for some N |
| `IntegersBetween` | the integers strictly between a and b number max(b − a − 1, 0) |
| `IntIntervalSize` | the integers from a to b number max(b − a + 1, 0), read off IntegersBetween at (a − 1, b + 1) |
