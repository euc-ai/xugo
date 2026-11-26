# int_divides — divisibility on ℤ

`d ∣ e` over the integers, and the greatest common divisor that stands
on it. ℤ is where these actually live — a common divisor divides every
ℤ-COMBINATION of its arguments, and the coefficients of that
combination are exactly what ℕ does not have — so a ℕ development of
the same material either borrows from here or does without.

The chapter is `∣` in RING vocabulary: everything about divisibility
provable before division exists — what changing a divisor's sign or
size does to the relation, how big a divisor can be, what carries a
divisibility to a new dividend, and the greatest common divisor with
Bézout's identity behind it.

Everything that JOINS divisibility to the division algorithm —
`int_rem(m,n) = &0 ⇔ n ∣ m`, exact quotients, the least common multiple
(whose definition names `int_div`), divisibility by 2 — is `int_div_rem`'s,
in its divisibility and lcm sections. That split is not a matter of
taste: `int_div_rem`'s lcm section reads this chapter's gcd
specification, so this chapter is BELOW the division algorithm and
cannot state a theorem that names `int_div` or `int_rem`.

What remains is coherent rather than residual. `∣` is defined as the
existence of a cofactor — ring vocabulary — and so is Bézout's
identity: the gcd arrives by choice over an existence theorem proved by
well-founded descent, never by dividing. The whole chapter lives in an
ordered ring.

## The elementary laws

All of them turn on the same sentence: `d ∣ e` IS the existence of a
cofactor, so proving a divisibility means naming one and using a
divisibility means being handed one. All but the bound are that move
applied directly; the bound is the one that cannot make the cofactor do
the work and pins it away from &0 instead.

**`AbsDividend`** and **`AbsDivisor`** — a divisibility does not see
the sign of either side:

    ∀d n:int. d ∣ n ⇔ d ∣ int_abs(n)
    ∀d n:int. d ∣ n ⇔ int_abs(d) ∣ n

A sign change is absorbed by negating the cofactor, and `int_abs(x)`
is `x` or `int_neg(x)` and nothing else, so each law is one sentence
applied twice — once to reach the negation and once to come back from
it. What separates the two is only which factor of the defining
product the sign lands on.

**`DividesProduct`** and **`DividesOwnMultiple`** — divisibility
passes to multiples:

    ∀d m n:int. d ∣ m ⇒ d ∣ m * n
    ∀d c:int.   d ∣ c * d

The cofactor absorbs the extra factor; in the second the divisibility
being extended is `d ∣ d`, so the cofactor asked for IS the other
factor and there is nothing to discharge. The lcm strand next door
needs the first twice and the parity strand needs the second three
times.

**`DivisorBoundedByDividend`** — a divisor is no larger than what it
divides, once what it divides is not &0:

    ∀x y:int. x ∣ y ∧ y ≠ &0 ⇒ int_abs(x) ≤ int_abs(y)

The exclusion of &0 is not a technicality. Every integer divides &0,
so without it the statement would be claiming that every integer is
smaller than &0.

This is the chapter's first theorem that is not formal, and it is
worth saying why. In ℝ the corresponding statement is FALSE — every
nonzero real divides every real, so a "divisor" carries no size
information at all — and what makes it true here is that ℤ is
DISCRETE. Divisibility hands over a cofactor; the cofactor is nonzero
because the product is; and a nonzero INTEGER has size at least &1,
there being nothing strictly between. Scaling by something at least
&1 cannot bring a size down. The whole argument is those four
sentences, and only the third is about ℤ rather than about any ordered
ring.

The bound is what turns a divisibility hypothesis into a finiteness
argument — below a given size there are only so many candidates — and
it is what lets a congruence force a small difference to vanish, which
is the use `int_congruence` makes of it.

## ℕ's divisibility, read in ℤ

ℕ has its own divisibility, defined inside ℕ as the existence of a
natural cofactor (`nat_num/nat_divides`), and the embedding carries it
to this chapter's relation:

**`OfNumDivides`** — `∀d n:num. d ∣ n ⇔ &d ∣ &n`.

Going up is free, because `&` is multiplicative. Coming down is the
content: a ℤ factor of `&n` need not be a natural, but its absolute
value is, and taking absolute values leaves the equation intact because
`&n` and `&d` are already nonnegative. The clause belongs to the
sentence "`&` is an embedding of ordered semirings" that `int_embed`
states operation by operation; it sits here because its ℤ side is this
chapter's relation, as congruence's sits in `int_congruence` and the
power's in `int_pow`.

**`UnitPlusMinusOne`** — the units of ℤ are plus and minus one:

    ∀r s:int. r * s = &1 ⇒ r = &1 ∨ r = -&1

A factor of one divides one, so its size, a natural number, divides
one in ℕ (`AbsDivisor`, then `OfNumDivides`), where the only divisor of
one is one; an integer of size one is one or its negation.

## The greatest common divisor

**`Bezout`** — every pair of integers has a common divisor that
Bézout's identity reaches:

    ∀a b:int. ∃d:int. d ∣ a ∧ d ∣ b ∧ ∃x y:int. d = a·x + b·y

The proof first treats nonnegative pairs by well-founded descent on
`|a| + |b|`, without division. A zero argument gives the other as a
witness. Otherwise subtract the smaller argument from the larger;
the size strictly drops, and the smaller pair's common divisor and
coefficients transport back by `a = (a−b) + b`. Symmetry handles the
opposite ordering with the same subtraction argument. Finally apply
this result to `|a|, |b|`: each absolute value is its original integer
times a sign, so those signs can be absorbed into the two coefficients.

**`BezoutNonneg`** — the reachable common divisor can be taken
NONNEGATIVE: pass Bézout's `d` to `|d|`. The size divides whatever `d`
divides (`AbsDivisor`), it is nonnegative outright, and the
combination survives the sign change with its coefficients negated.
This is the existence theorem the choice below picks from.

**`IntGcdSpec`** — what the constant `int_gcd` IS. Of a
pair's common divisors it names one that is nonnegative and that
Bézout's identity reaches:

    ∀a b:int. &0 ≤ int_gcd(a,b) ∧ int_gcd(a,b) ∣ a ∧ int_gcd(a,b) ∣ b
              ∧ ∃x y:int. int_gcd(a,b) = a·x + b·y

Maximality is deliberately absent — no consumer has needed it, and
the four conjuncts above are what the gcd chapters do need.

`int_gcd` arrives by CHOICE rather than by construction: `BezoutNonneg`
proves that every pair HAS such a divisor and the constant names one.
This member is the step between those two sentences, taken through the
define door's spec shape (`family.DefineSpec`): the entry states the
specification and cites the existence; the ε-choice over the pair and
the projection computation run inside the composite.

Its consumer is `int_num/int_div_rem`'s lcm section, which reads the
specification for the gcd's two divisibilities and its nonnegativity.
