# nat_order — the order theory of ℕ

This chapter is ℕ's ≤ and <: their definitions, how each interacts
with addition and multiplication, the growth-bounds
tier that comes out of that, and the well-foundedness
of `<` itself. The clause projections at the definitions layer are
exported — `sets/num_segment` reads ℕ's order recursion off them,
which makes them chapter API.

The mathematical development, tier by tier — which is also the
reading order:

- **Definitions.** ≤ and < — the entries LessEq and
  LessThan — are defined by their recursion clauses on the right
  argument (`family.Define`, compiled against peano.Recursion, the
  primitive recursion of ℕ read at predicates); `>` and `≥` are their
  mirrors (GtDef, GeDef) and nat_max / nat_min the conditional picks (NatMaxDef,
  NatMinDef). The four defining clauses

  - `m ≤ 0 ⇔ m = 0` and `m ≤ suc n ⇔ (m ≤ n ∨ m = suc n)`
  - `¬(m < 0)` and `m < suc n ⇔ (m < n ∨ m = n)`

  are then stated once as projection lemmas — the rewrite rules the
  rest of the family cites instead of re-deriving.
  They are exported:
  `sets/num_segment` builds the interval `m .. n` by this same
  recursion and reads each of its own clauses off one of these.
- **Successor/zero lemmas.** The two successor
  bridges — `m < n ⇔ suc m ≤ n` (strict order is successor bound)
  and `m < suc n ⇔ m ≤ n` — are the tier's mathematical content,
  each one induction over the projections; everything else is a one-
  or two-cite consequence: suc-invariance of both orders chains the
  two bridges, positivity of every successor composes a bridge with
  ZeroLessEq, and ZeroLessEq itself (0 is the bottom element) is its
  own small induction.
- **Order axioms.** Two layers. The inductive
  core — reflexivity (LessEqRefl with its corollary LessEqOfEq,
  LessThanIrrefl), transitivity
  (LessEqTrans, LessThanTrans) and the antisymmetry
  characterization LessEqAntisym — each an induction from the
  clause projections; LessEqTrans shows the shape: induct on p with
  m, n held fixed, so the IH is exactly what the step case
  consumes. Above it a composition layer — LessThanAsym plus the
  internal mixed-order corollaries (the <, ≤ antisymmetry, the two
  mixed transitivities, and "strict implies distinct") — where
  nothing is proved by induction at all: each is a
  two-to-four-cite consequence of transitivity, irreflexivity and
  the suc-bridge (the statements have no inductive content).
- **Totality.** LessEqTotal (≤ is total) is the
  tier's one induction — the nested case-analysis shape again.
  Everything else is a zero-induction corollary: LessThanTrichotomy
  composes totality with the successor bridge and clause (once ≤ is
  known total, trichotomy has no inductive content of its own), and
  the internal mixed-totality lemma does the same one bridge
  shorter.
- **Duality/positivity.** The layer names three ⇔ that
  consumers cite by name — NotLessEq / NotLessThan (each order is the
  negation of the other's flipped-argument twin — the sub-tier's basis
  nodes), LessEqSplit (the non-strict order decomposes into
  strict-or-equal, the composed decomposition the totality layer kept synthesizing
  on the fly), joined by LessEqOfLessThan — the ⇐ half of LessEqSplit,
  promoted once the tower started citing it, and by PosIffNonzero
  (positivity IS non-zeroness), which four other chapters cite.
  `m < n ⇔ m ≤ n ∧ m ≠ n` is one cite from LessEqSplit and drew no
  consumer, so the chapter states the split once and lets a caller
  take the face it needs. `m = n ⇒ m ≤ n` is
  stated as LessEqOfEq in the order-axioms layer — reflexivity after
  one rewrite — because the ℕ arithmetic engine's derived adapters read the
  statement in exactly that ⇒ shape.
- **Order × addition.** Two shapes. The
  characterizations LessEqExists and LessThanExists (each order IS
  the existence of an additive shift — d for ≤, suc(d) for <) are
  the tier's heavy inductions, each one bidirectional-iff over the
  clause projections plus a nested induction on the ∃-witness for
  the ⇐ direction. Above them a composition layer: the two-sided
  monotonicity LessEqAdd2 chains two applications of leftMonoAdd
  (the internal ∀m p n. m ≤ p ⇒ m+n ≤ p+n primitive) through
  LessEqTrans; the one-sided monotonicity LessEqAdd and the
  cancellation LessEqAddCancel are near-cite-only consequences of
  LessEqExists; the mixed strict/non-strict pairwise LessEqLessThanAdd2 and
  lessThanLessEqAdd2 compose through the suc-bridge over LessEqAdd2; the
  right-cancellation LessEqAddRightCancel and the strict-strict
  LessThanAdd2 are pure AddSym- or weakening-mirrors of the ≤
  siblings. Once the ∃-characterizations exist, the remaining
  members are all 3–7-tactic linear Chains — the tier's inductive
  content lives in LessEqExists, LessThanExists, and leftMonoAdd.

- **The order along a map.** LessEqStrictlyIncreasing: a strictly
  increasing f : ℕ → ℕ never falls below the identity, `n ≤ f(n)` —
  one induction, whose step turns `n < f(n + 1)` into
  `n + 1 ≤ f(n + 1)` across the successor bridge. It is what makes the
  indices of a subsequence reach every tail. LessThanStrictlyIncreasing: a map that
  rises at every step, `f(k) < f(k + 1)`, rises between any two indices,
  `m < n ⇒ f(m) < f(n)` — one induction on n, below n + 1 lying n itself
  or an index below n. It is what makes a subsequence of a subsequence
  one.

- **Order × multiplication.** The tier where the
  ≤/+ interface pays off: every member but the factorial's is
  induction-free. An order statement about products is transported through the
  existence characterizations into an equation between sums, where
  the nat_arith family's distributivity and the +-cancellation
  finish. LessEqMulCancel (a common left factor cancels through ≤,
  up to m = 0) case-splits each ⇔ direction, extracting an
  ∃-shift witness where a shift is needed; LessEqMul2 (pairwise ≤-monotonicity
  of ×, the ×-side twin of LessEqAdd2) distributes the rectangle
  (m+d₀)·(p+d₁) and bounds — its proof is even refutation-free,
  every leaf closing by equation-chaining. Four one-`By`
  corollaries complete the tier: LessEqMulMono (a common left
  factor preserves ≤ — the ⇐ of the cancel, sparing callers that
  scale a SINGLE inequality the reflexive t ≤ t guard LessEqMul2
  forces), LessEqSelfMul (m ≤ m·n when 1 ≤ n, through nat_arith's
  MulOne unit law), and LessEqMulRightCancel (the right-factor
  cancel, transported onto the left cancel by commutativity — stated
  here because slope's reciprocal-growth bound cites it across the
  family boundary), and LessThanMulCancel (the strict left cancel: NotLessEq
  reads m·n < m·p as ¬(m·p ≤ m·n), the ≤-cancel decides it, and
  NotLessEq negates the residue). FactorialMonotone (m ≤ n ⇒ m! ≤ n!)
  is the tier's one induction: (k + 1)! = k·k! + k! has k! among its
  summands, so one step never shrinks a factorial, and from m the
  factorial climbs the distance d with n = m + d, one transitivity per
  step.

- **Numeral evaluation.** The digit-by-digit laws for ≤ and <
  on binary numerals (NumeralLessEq, NumeralLessThan): under the digit
  equations each two-digit clause compares two doubles, so the part opens with
  the two facts the packs halve through — doubling preserves and
  reflects each order (doublingLessEqIff, doublingLessThanIff, internal) —
  and the clauses are then the successor/zero facts and the ≤/< bridges
  read on a double.
- **The order against exponentiation.** The order reads nat_pow through
  positivity and the two characterizations: PowPositive
  (`0 < nat_pow(m,n) ⇔ m ≠ 0 ∨ n = 0`) composes PosIffNonzero at the
  power with nat_arith's vanishing characterization; LessThanPow is the
  strict trichotomy (`nat_pow(x,m) < nat_pow(x,n) ⇔ 2 ≤ x ∧ m < n ∨ x = 0 ∧
  (m ≠ 0 ∧ n = 0)`), proved without induction off nat_arith's exponent
  laws, and LessEqPow its ¬<-reading (the COND form). Two instances
  the words chapters spend live beside them: PowTwoMonotone (the
  base-2 monotonicity, one cite of LessEqPow) and LessThanPowTwoSelf
  (`n < 2^n`, one cite of LessThanPowSelf, the same bound at any base
  of at least two). A power grows with its base as well:
  PowBaseMonotone (`x ≤ y ⇒ x^k ≤ y^k`), and a positive power is at
  least its base: LessEqSelfPow (`0 < k ⇒ x ≤ x^k`).

- **Growth bounds.** The chapter compared against whole
  growth rates instead of one operation at a time: a linear function
  dominates another iff its slope does (BoundsLinear, and its
  zero-slope corollary BoundsLinear0), a bound holding eventually
  holds everywhere (BoundsIgnore, by induction on the ignored
  block), and a pointwise bound and a divided-through linear bound
  carry the same information (BoundsDivided, with BoundsNotZero
  absorbing an affine constant into the slope). The strict-mult
  step they share — x = 0 ∨ b ≤ b·x — is stated once as
  LessEqMulNonzero, which nat_divides also cites. These are the
  estimates the real tower's nadd construction runs on; they are
  order statements from binder to bone, which is why they sit in this
  chapter rather than with the arithmetic.

- **Well-foundedness.** The chapter's last tier
  says what all of it rests on: `<` has no infinite descent, in the
  two readings that make it usable. StrongInduction is the induction
  reading — a property holding at n whenever it holds strictly below
  n holds everywhere — and its proof is the one move worth
  remembering: ordinary induction cannot carry that closure
  hypothesis, but it can carry the strengthened property "P holds
  below n", which is vacuous at 0 and whose successor step is
  exactly the clause `m < suc n ⇔ m < n ∨ m = n` read as "the old
  points, plus n itself". WellOrdering is the least-element reading,
  and it is StrongInduction at the COMPLEMENT: if P holds anywhere,
  ¬P cannot be closed under the strong-induction step, and a point
  where that closure fails is a least point satisfying P. This is
  the tier where the chapter first quantifies over a predicate
  rather than over numbers; the alphabet does not change, which is
  why it is an order-chapter tier and not a chapter of its own.

  Two consequences follow, and neither needs an induction of its
  own. MaximumExists reads well-ordering UPWARD: a predicate that
  holds somewhere and is bounded above attains its bound. The
  pleasing part is how — the numbers BOUNDING P are themselves a
  predicate, non-empty precisely because the hypothesis supplies a
  bound, so well-ordering returns their LEAST member, and the tier's
  longest proof is then spent showing that P actually reaches it (by
  cases on that least bound). DownwardInduction runs from a fixed
  level down: if P holds from m upward, and P at a point below m
  follows from P everywhere strictly above it, then P holds
  everywhere. Its proof is the tier's shortest — a counterexample
  cannot sit at or above m, so MaximumExists hands over a GREATEST
  counterexample, and its MAXIMALITY half is exactly the downward
  step's premise, which then puts P at that point after all. The
  four members form one chain, each the previous read from a new
  angle. Beside them, BoundedIndexEnumeration lists a predicate
  bounded by k by a strictly increasing map from an initial segment
  — one plain induction on k, which appends k to the listing when k
  has the property. ConsecutiveBracket finds a crossing of N by a
  natural-valued sequence f: if f(0) ≤ N and some f(k + 1) > N, then
  f(i) ≤ N < f(i + 1) for some i. WellOrdering chooses the least
  next-term crossing; no monotonicity is required. PowerBracket reads
  this at f(i) = b^i for b ≥ 2 and N ≥ 1, and SquareBracket at
  f(i) = i² for every N.

Within one part, siblings are mirror pairs proved mutatis mutandis;
where one member's proof is the other's with AddSym (or the ≤/<
flip) composed in, the file says so instead of abstracting it away.

## Reading the proofs

The corpus-wide reading conventions — the canonical statement style,
the four closing forms, the resident-hypothesis default and its
comment-marked departures, the raw-vs-normalized cite of a
conjunction row, and Skolem naming — live in
[../../README.md](../../README.md). Exemplars in this chapter, one per
closing form: `LessThanAsym` is the pure cite-and-refute case (no
two numbers are each strictly below the other — immediate from
transitivity and irreflexivity, nothing between the premises and the
conclusion to name); the duality members and the ≤/+ and ≤/· compositions
members argue by ground cites whose witnesses spell the mirrored or
chained instances (`LessEqAdd2`'s named midpoint); and both ≤/·
products obtain their additive shifts inside a `Derive` block before
using them, each close naming its premises in a `By` list.

## Naming note

Names follow the constitution's §"Inventory and names". Registry names
are dot-qualified — the members register as `nat_order.<Name>`;
the bare CamelCase names are the Go entry vars (the package
qualifies them in code). A name is
reserved for the chapter's public API — the facts later chapters
cite; every other theorem is demoted to an internal lemma
(unexported entry var, lowerCamel name), fully verified and
typed-citable within the family. Demotion is a claim about reach, so
it is revoked the moment another chapter cites the lemma: such a
member is exported (Go var and `Name:` together, CamelCase) and joins
the chapter API — constitution §Families, "an entry cited across a
family boundary IS chapter API".

LessEqMulNonzero is the bounds tier's shared
strict-mult step; OneLessEqIffPos is the numeral face of
positivity, stated here so that consumers arriving with a numeral do
not each pay the `1 = suc 0` bridge; and OneLessEqIffNonzero states
the positivity triangle's remaining side (`1 ≤ n ⇔ n ≠ 0`) so a
consumer crossing between the numeral bound and the disequality
spends one cite. The definitional clause projections —
LessEqZeroClause, LessEqSucClause, LessThanZeroClause,
LessThanSucClause — are exported for `sets/num_segment`, which builds the
interval `m .. n` by the same recursion and reads each of its own
clauses off ℕ's. `PowTwoMonotone`, the base-2 exponent's monotonicity,
is exported beside them, and so is `OrderCalc`, the Go kit a chapter
uses to write an estimate in ℕ as a chain of ≤ legs. `leftMonoAdd`, the addition tier's
left-monotonicity primitive, and the two doubling equivalences the
bounds tier runs on stay internal.

Framework, in one line: members register as typed entry vars in a
family sub-package (compiler-checked dep DAG, one shared
`nat_order.cnf.pb`, force-replay as `TestReplayAll/nat_order/…`
underneath) — mechanics in the constitution §Families and
`library/registry/registry.go`.
