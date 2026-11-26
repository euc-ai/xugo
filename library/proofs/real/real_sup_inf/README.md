# real_sup_inf — ℝ's extrema

Completeness says bounded sets of reals have least upper bounds. This
chapter is where that fact stops being an axiom about existence and
becomes a calculus: four operations — `max` and `min` over pairs,
`real_sup` and `real_inf` over sets — together with the two relations
`real_has_sup` and `real_has_inf` that name an attained bound without computing
it, and the laws that let every later chapter compare, squeeze and
approximate through them without ever re-running a completeness
argument.

The story runs in seven movements. A member map follows them, at the
end.

1. **The lattice of two**. `max` and `min` are case
   definitions (`max x y = COND(x ≤ y, y, x)`), and their laws are
   guard algebra: split on the definition's own guard, and the
   operation becomes one of its two arguments. What is left is order
   reasoning, and the only thing the branches need from the order is
   that it is total — which is how a failed guard becomes the reverse
   comparison. This is the same move real_sgn_abs makes on `|·|` and
   `sgn`; these are the third and fourth case definitions at this
   layer.

   `MaxUpperBound` and `MinLowerBound` are the unconditional bounds:
   the max is above both arguments, the min below both. `MaxLessEq`
   and `LessEqMin` are the characterizations that make them EXTREMAL
   — a bound above the max is exactly a bound above both, so no
   smaller value is an upper bound — and `LessThanMin` and `MaxLessThan`
   are their strict forms: strictly below the min is exactly strictly
   below both, so the smaller of two positive radii is positive, and
   strictly above the max is exactly strictly above both.
   `LessEqMax` and `MinLessEq` are
   what the extremum looks like from the other side: since the max is
   attained by an argument, reaching it means reaching one of the two,
   and the conjunctions become disjunctions. `MinLessThan` is the
   strict form of that min law — the min is strictly under a value
   exactly when one of the two is — and the three strict laws are the
   one place the branches consult the mixed transitivity law rather
   than the weak one.
   The clamp `max(a, min(b, x))` of x to ⟦a, b⟧ lands in ⟦a, b⟧, fixes
   its points, sends a point past either end to that end, and brings two
   reals no farther apart (`ClampRange`, `ClampEnds`, `ClampNonexpansive`).

2. **The embedding respects the lattice**.
   `OfNumMax` is `&(nat_max m n) = max (&m) (&n)` and `OfNumMin` its
   mirror. What makes them true is not a fact about maxima at all:
   ℕ's `nat_max` and ℝ's `max` are the same case definition one type
   apart, and `&` carries `m ≤ n` to `&m ≤ &n` in both directions. So
   the proof is to split on ℕ's comparison: with it decided, both
   definitions take the same branch, and each side of the equation is
   the same embedded number. The embedding's order equivalence is the
   only thing cited, and none of movement 1 is used.

3. **Existence, once**. `real_sup s` is ε-chosen;
   `SupLeastUpperBound` turns completeness
   (`tower/real_completeness.RealComplete`) into the working characterization —
   for nonempty bounded s, `real_sup s` is an upper bound below every
   upper bound. `InfGreatestLowerBound` earns its mirror by the
   classical construction: the infimum of s is the supremum of the
   set of lower bounds of s, so the same theorem serves both, grounded
   once per operator, and neither wing ever needs the other again.
   Beside the pair sit eight companions that need no completeness at
   all: `SupSameUpperBounds` / `InfSameLowerBounds` (the operator is
   determined by the bounds alone — it never looks at the members),
   `SupUniqueApproach` / `InfUniqueApproach` (a bound the set
   approaches IS the value — how a supremum is exhibited in practice,
   the pin itself witnessing the existence), and `SupUniqueAttained` /
   `InfUniqueAttained`, which is that pin with its approach clause
   discharged rather than assumed: a bound the set CONTAINS is
   approached by itself, so a value you can point to inside the set is
   the supremum. That last pair is what every later exhibition of an
   extremum goes through — name the greatest element, and the
   supremum is it. `SupUniqueLeastBound` / `InfUniqueGreatestBound`
   close the family with the third way to pin the value: b IS the
   supremum when the values above b are exactly the upper bounds of s.
   That reading is what movement 7's `real_has_sup` relation packages, so
   this pair is where the two halves of the chapter meet.

   The chapter's whole ε-discipline lives in this file: prove
   `∃a. Φ(a)`, and unfolding the definition hands Φ to the chosen
   value, the engine consuming the choice axiom in the unfold — no
   selection law is ever cited.

4. **The comparison calculus** (with the
   approximations that follow it). Everything a consumer actually
   cites: `real_sup s ≤ b` from a bound, `a ≤ sup s` through a member,
   monotonicity under ⊆, the squeeze `a ≤ sup s ≤ b`, and approximation
   (`c < real_sup s` yields a witness above c). Movement 3 states the
   operators hypothetically, in terms of an existence; this movement
   is the translation into the concrete comparisons a consumer holds,
   and into the estimates that approximate them:

   - **`SupLessEqBound`** / **`BoundLessEqInf`** — a bound on the
     members bounds the operator. The first and most cited case, and
     leastness in its working form.
   - **`SupLessEqIff`** / **`LessEqInfIff`** — and that comparison is
     an equivalence: `real_sup s ≤ y` says exactly that y caps every member.
   - **`LessEqSupThroughMember`** / **`InfLessEqThroughMember`** — the
     estimate from below, obtained from a single exhibited member,
     which is also what makes the set nonempty.
   - **`SupBetweenBounds`** / **`InfBetweenBounds`** — the squeeze: a
     set bounded on both sides has its extremum there too, proved by
     using each of the two comparison directions once.
   - **`MemberLessEqSup`** / **`InfLessEqMember`** — the same estimate
     at its degenerate waypoint: a member is itself below the sup.
   - **`TermLessEqSequenceSup`** / **`SequenceSupLessEqBound`** — the
     member and the bound laws read over a sequence's range
     `sup(image(a, 𝕌))`: every term of a sequence bounded above lies at
     or below the supremum of its terms, and a bound of every term bounds
     that supremum. The range of a sequence is never empty and its
     members are its terms, so neither carries a nonemptiness hypothesis.
   - **`SupMonoSubset`** / **`InfAntitoneSubset`** — monotonicity under
     inclusion. `real_sup` grows with the set and `real_inf` shrinks, which is why
     the two names differ: the inf law's conclusion is `real_inf t ≤ real_inf s`.

   The estimates answer the opposite question — given
   where the extremum is, where are the members — and they are the only
   members here that argue by contraposition:

   - **`SupApproach`** / **`InfApproach`** — a value strictly under
     `real_sup s` is exceeded inside s. The member is not constructed but
     read off the failure of c to be a bound.
   - **`SupApproachWithin`** / **`InfApproachWithin`** — the same in the
     form an ε-argument reads it: within any positive margin below the
     supremum lies a member, at or below the supremum as every member is.

5. **Finite sets attain their bounds**. For a general set, the supremum
   need not be attained. On a finite set the
   question of whether it is a member has an answer, and it is the
   strongest one: `SupFiniteAttained` says `real_sup s ∈ s`, so sup and inf
   are the greatest and least ELEMENT. The finite-set argument is general order theory:
   `order.FiniteMaximal` gives a maximal point, and
   `order.MaximalGreatest` makes it greatest in the real total order.
   Reversing the order gives a least point. Movement 3's attainment
   pair identifies these points with `real_sup` and `real_inf`.
   `SupFiniteIffGreatest` then
   reads the two halves back as one equivalence: `real_sup s = a` says
   exactly that a is a greatest member. The eight comparison laws then
   sharpen from bounds to membership — `a ≤ sup s ⇔ ∃x ∈ s. a ≤ x`, and
   its ∀ and strict variants. They need only attainment: each has one
   arm that uses the extremum's own membership — as the witness where
   that arm is existential, as the point of instantiation where it is
   universal — and one arm that is a single step of transitivity.
   Finiteness never enters their proofs at all, being spent entirely by
   the cite that supplies attainment.

6. **The structural equations**. How the operators
   COMPUTE — every headline here is an equation whose left side is a
   supremum of a set built with `insert` or `UNION`, and whose right
   side is arithmetic in the lattice of movement 1. The file runs in
   three sections, divided by what each has to assume.

   The first assumes nothing. `SupSingleton` is the base
   case: a one-point set's supremum is its point, which movement 3's
   attainment pair delivers in a single cite. `SupInsertMax` merges two
   points laid on a set into their maximum, and is hypothesis-free for a
   reason worth stating — `{a, b} ∪ s` and `{max a b} ∪ s` have
   literally the same upper bounds, and a supremum sees nothing else, so
   `SupSameUpperBounds` settles it without ever asking whether the sets
   are bounded or inhabited.

   The second pays for a hypothesis and gets an equation.
   `SupInsertFinite` peels one point off a finite set: the supremum of
   `x insert s` is x when s is empty and `max x (real_sup s)` otherwise,
   proved by splitting on that very guard — and, once split, by taking
   as given that the maximum is one of its two arguments, which
   movement 1 states. `SupUnion` joins two nonempty bounded sets:
   `real_sup (s ∪ t) = max (real_sup s) (real_sup t)`, which is movement 3's
   lub-uniqueness law applied to the union, with the whole content in
   one equivalence — a value caps `s ∪ t` exactly when it lies at or
   above the greater of the two suprema.

   The third section is the chapter's closing act, where the two
   layers meet. **`SupPairIsMax`** / **`InfPairIsMin`** say
   `real_sup {x, y} = max x y` and its mirror — the extremum of a two-point
   set is exactly the lattice operation movement 1 opened with, which
   is what makes that movement a special case of this one rather than a
   separate subject. **`SupEqInfIffSingleton`** closes the circle from
   the other side: a nonempty set bounded on both sides has `real_inf s = real_sup s`
   exactly when it is a singleton, so the two operators agree precisely
   where there is nothing for them to disagree about.

   Membership enters all three sections, and the files distinguish two
   ways it arrives. A step that is set algebra end to end goes to the
   set driver, which closes it in one move. A membership law that is
   instead one premise inside a chain of order facts — the union laws
   are the clearest case — is named at the point it is read, because
   there the chain is the content and the driver has nothing to close.
   The files say which is which at each site.

7. **Attained bounds as a relation**. `real_has_sup s l`
   packages "the upper bounds of s are exactly ⟦l, ∞⟭" — a bound that
   is GIVEN, where movement 3's operators CHOOSE one. Because that
   package says everything at once, every member is it read at a single
   value: at `l` itself the claim is reflexivity and `l` is handed over
   as a cap (`HasSupUpperBound`), at a value the hypothesis puts below
   `l` the package fails and surrenders a member (`HasSupApproach`),
   and at a value the proof must manufacture — `l - &1` — the failure
   is what shows `s` is inhabited at all (`HasSupNonempty`). On that
   base the wing re-reads movements 3–4 relationally: `HasSupIsSup` and
   `HasSupCharacterization` say which sets and bounds the relation
   holds of, `HasSupDominated` compares two of them, `HasSupExists`
   trades the relation for nonempty-and-bounded.

   This movement is where the chapter stops needing `real_sup` and `real_inf` as
   operators at all: everything it proves is about a bound something
   else has already produced, which is why it is last and why nothing
   above it cites back down.

## The members

Every member is listed here with its statement, so a reader who knows
which theorem they want can find its name. Mirrors are given as pairs,
sup first; the inf statement is the same with the order reversed unless
noted.

**1 · The lattice of two** — `MaxUpperBound`/`MinLowerBound`
(`x ≤ max x y ∧ y ≤ max x y`) · `MaxLessEq`/`LessEqMin`
(`max x y ≤ z ⇔ x ≤ z ∧ y ≤ z`) · `LessThanMin`/`MaxLessThan`
(`z < min x y ⇔ z < x ∧ z < y`, `max x y < z ⇔ x < z ∧ y < z`) · `LessEqMax`/`MinLessEq`
(`z ≤ max x y ⇔ z ≤ x ∨ z ≤ y`) · `MinLessThan`
(`min x y < z ⇔ x < z ∨ y < z`) · `MaxIsArgument`/`MinIsArgument`
(`max x y = x ∨ max x y = y`) · `ClampRange`
(`a ≤ b ⇒ a ≤ max(a, min(b, x)) ∧ max(a, min(b, x)) ≤ b ∧ (a ≤ x ∧ x ≤ b ⇒ max(a, min(b, x)) = x)`) ·
`ClampEnds` (`a ≤ b ⇒ (x ≤ a ⇒ max(a, min(b, x)) = a) ∧ (b ≤ x ⇒ max(a, min(b, x)) = b)`) ·
`ClampNonexpansive` (`|max(a, min(b, x)) - max(a, min(b, y))| ≤ |x - y|`).

**2 · The embedding** — `OfNumMax`/`OfNumMin`
(`&(nat_max m n) = max (&m) (&n)`).

**3 · What sup and inf ARE** — `SupLeastUpperBound`/`InfGreatestLowerBound`
(nonempty and bounded ⇒ `real_sup s` caps s and is under every cap) ·
`SupSameUpperBounds`/`InfSameLowerBounds` (same caps ⇒ same supremum) ·
`SupUniqueApproach`/`InfUniqueApproach` (a cap approached from inside IS
the supremum) · `SupUniqueAttained`/`InfUniqueAttained` (a cap that is a
MEMBER is the supremum) · `SupUniqueLeastBound`/`InfUniqueGreatestBound`
(`(∀c. c caps s ⇔ b ≤ c) ⇒ real_sup s = b`).

**4 · The comparison calculus** — `SupLessEqBound`/`BoundLessEqInf`
(`real_sup s ≤ b` from a cap) · `SupLessEqIff`/`LessEqInfIff`
(`real_sup s ≤ y ⇔ ∀x ∈ s. x ≤ y`) · `LessEqSupThroughMember`/`InfLessEqThroughMember`
(`a ≤ y` for some `y ∈ s` ⇒ `a ≤ sup s`) · `MemberLessEqSup`/`InfLessEqMember`
(`a ∈ s ⇒ a ≤ sup s`) · `SupMonoSubset`/`InfAntitoneSubset`
(`s ⊆ t ⇒ real_sup s ≤ real_sup t`) · `SupBetweenBounds`/`InfBetweenBounds`
(`a ≤ x ≤ b` throughout ⇒ `a ≤ sup s ≤ b`) · `TermLessEqSequenceSup`
(`(∀m. a(m) ≤ b) ⇒ a(n) ≤ sup(image(a, 𝕌))`) · `SequenceSupLessEqBound`
(`(∀n. a(n) ≤ b) ⇒ sup(image(a, 𝕌)) ≤ b`).

**4 · The estimates** — `SupApproach`/`InfApproach`
(`c < real_sup s ⇒ ∃x ∈ s. c < x`) · `SupApproachWithin`/`InfApproachWithin`
(`&0 < δ ⇒ ∃x ∈ s. sup s − δ < x ∧ x ≤ sup s`).

**5 · Finite sets attain their bounds** — `SupFiniteAttained`/`InfFiniteAttained`
(finite nonempty ⇒ `real_sup s ∈ s` and caps s) ·
`SupFiniteIffGreatest`/`InfFiniteIffLeast` (`sup s = a ⇔ a ∈ s ∧ a` is
greatest) · and the eight comparison laws, ordered by relation then arm
shape: `LessEqSupFinite`/`InfLessEqFinite` (`a ≤ sup s ⇔ ∃x ∈ s. a ≤ x`)
· `SupLessEqFinite`/`LessEqInfFinite` (`sup s ≤ a ⇔ ∀x ∈ s. x ≤ a`) ·
`LessThanSupFinite`/`InfLessThanFinite` (`a < sup s ⇔ ∃x ∈ s. a < x`) ·
`SupLessThanFinite`/`LessThanInfFinite` (`sup s < a ⇔ ∀x ∈ s. x < a`).

**6 · The structural equations** — `SupSingleton`/`InfSingleton` (`real_sup {a} = a`) ·
`SupInsertMax`/`InfInsertMin`
(`sup (b insert a insert s) = sup (max a b insert s)`) ·
`SupInsertFinite`/`InfInsertFinite`
(`real_sup (x insert s) = COND(s = ∅, x, max x (real_sup s))` for finite s) ·
`SupUnion`/`InfUnion` (`real_sup (s ∪ t) = max (real_sup s) (real_sup t)`) ·
`SupPairIsMax`/`InfPairIsMin` (`real_sup {x, y} = max x y`) ·
`SupEqInfIffSingleton` (`real_sup s = real_inf s ⇔ s` is a singleton).

**7 · Attained bounds as a relation** — `HasSupNonempty`/`HasInfNonempty`
(`real_has_sup s l ⇒ s ≠ ∅`) · `HasSupUpperBound`/`HasInfLowerBound`
(`real_has_sup s b ∧ x ∈ s ⇒ x ≤ b`) · `HasSupApproach`/`HasInfApproach`
(`real_has_sup s l ∧ c < l ⇒ ∃x ∈ s. c < x`) · `HasSupIsSup`/`HasInfIsInf`
(`real_has_sup s l ⇔ s ≠ ∅ ∧ bounded ∧ real_sup s = l`) ·
`HasSupCharacterization`/`HasInfCharacterization`
(`real_has_sup s l ⇔ s ≠ ∅ ∧ l` caps s ∧ l approached) ·
`HasSupDominated`/`HasInfDominated` (s dominates t pointwise ⇒
`m ≤ l`) · `HasSupExists`/`HasInfExists`
(`∃l. real_has_sup s l ⇔ s ≠ ∅ ∧ bounded`).

Framework mechanics (family manifest, shared CNF cache, replay) are
family.go's header + the registry docs.
