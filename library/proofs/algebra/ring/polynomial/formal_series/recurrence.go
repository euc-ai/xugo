// recurrence.go — the recurrence T·a′ = m·a between a series and its
// counting sequence: its sum at n reads only the coefficients below n, it
// determines the counting sequence over any commutative ring and the
// coefficients over an integral domain of characteristic zero, and the
// formal exponential solves it over a field of characteristic zero, so that
// there a series with a counting sequence is the formal exponential of its
// counts over their indices. Then the calculus of counting sequences: the
// Euler derivative is a derivation for convolution, a recurrence is the Euler
// equation with its initial values, and so counting sequences add over
// products, subtract over an invertible factor, go to their images under a ring
// homomorphism, vanish at the unit series and multiply by r over r-th powers.

package formal_series

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/abelian_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_domain"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/relations/well_founded"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
)

// RecurrenceSumCongruence — the recurrence sum at n reads only the
// coefficients below n: two sequences that agree below n give the same sum
// of m(i) times the coefficient at n − i over 0 < i ≤ n. Each index there
// is positive, so n − i lies below n, and the sums agree term by term.
var RecurrenceSumCongruence = recurrenceSumCongruenceThm{family.Add(registry.ProofEntry{
	Name: "RecurrenceSumCongruence",
	Key:  "prop_f30b78c5f336ad42",
	Build: family.Theorem(Statement{
		Binders:    "∀R:ring_ops(A). ∀m a b:(num → A). ∀n:num.",
		Hypotheses: []string{"∀j:num. j < n ⇒ a(j) = b(j)"},
		Conclusion: "module_sum(R.add, R.zero, «indices»(n), λi:num. R.mul(m(i), a(n - i))) = " +
			"module_sum(R.add, R.zero, «indices»(n), λi:num. R.mul(m(i), b(n - i)))",
	}, func(arg *Argument, R *Expr[RingOps[A]], m, a, b *Arrow[Nat, A], n *Expr[Nat], earlier Fact) {
		below := arg.Have(
			"every summand reads a coefficient below n",
			"∀i:num. i ∈ «indices»(n) ⇒ n - i < n",
			ByArith())
		agree := arg.Have(
			"agreement below n identifies every summand",
			"∀i:num. i ∈ «indices»(n) ⇒ R.mul(m(i), a(n - i)) = R.mul(m(i), b(n - i))",
			By(Normalized, earlier, below))
		arg.Show(
			"so the two sums agree term by term",
			By(agree, module.ModuleSumCongruence))
	}),
})}

// RecurrenceDeterminesCounts — a recurrence determines its counting
// sequence: strong induction identifies the earlier counts, and in the sum at
// k the count m(k) is multiplied by a(0), which is one.
var RecurrenceDeterminesCounts = recurrenceDeterminesCountsThm{family.Add(registry.ProofEntry{
	Name: "RecurrenceDeterminesCounts",
	Key:  "prop_3e91d759382b70d8",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀a m₁ m₂:(num → A).",
		Hypotheses: []string{
			"series_recurrence(R, a, m₁)",
			"series_recurrence(R, a, m₂)",
		},
		Conclusion: "m₁ = m₂",
		Abbrev: Abbrev{
			{Name: "earlier", Text: "λj:num. delete(«indices»(j), j)"},
			{Name: "countTerm", Text: "λf:(num → A). λj:num. λi:num. f(i) * a(j - i)"},
			{Name: "countSum", Text: "λf:(num → A). λj:num. " +
				"    module_sum(R.add, R.zero, «indices»(j), «countTerm»(f, j))"},
			{Name: "earlierCountSum", Text: "λf:(num → A). λj:num. " +
				"    module_sum(R.add, R.zero, «earlier»(j), «countTerm»(f, j))"},
		},
	}, func(
		arg *Argument,
		ring comm_ring.CommRingFact[on.R],
		a, m1, m2 *Arrow[Nat, A],
		recurrences Fact,
	) {
		data := arg.Unfolded(recurrences, SeriesRecurrenceDef)
		initial := arg.Have(
			"the constant coefficient is one and both counts start at zero",
			"a(0) = R.one ∧ m₁(0) = R.zero ∧ m₂(0) = R.zero",
			By(data))
		coefficients := arg.Have(
			"all three sequences take values in the ring carrier",
			"∀j:num. a(j) ∈ R.carrier ∧ m₁(j) ∈ R.carrier ∧ m₂(j) ∈ R.carrier",
			By(data))
		additive := comm_ring.AddMonoidOn.Read(ring)
		unit := comm_monoid.RightIdentityOn.Read(comm_ring.MulMonoidOn.Read(ring))
		arg.Do(Funext())
		arg.Show(
			"strong induction compares the counting sequences coefficient by coefficient",
			ByInduction(nat_order.StrongInduction,
				Case(
					"the earlier indices agree, so cancel their contribution to the recurrence",
					Derive(func(arg *Argument) {
						k := arg.FixAs[Nat]("k")
						ih := arg.Assume()
						indexNonzero := arg.Unless(
							arg.Term("k = 0"),
							"at zero both counts equal the additive identity",
							Given(func(arg *Argument, zero Fact) {
								arg.Show(
									"the initial values agree",
									Simp(Fwd(zero), Fwd(initial)),
									Basic())
							}))
						positive := arg.Have(
							"the remaining index is positive",
							"0 < k",
							ByArith(indexNonzero))
						equalSums := arg.Have(
							"the two recurrence sums have the same left hand side",
							"«countSum»(m₁, k) = «countSum»(m₂, k)",
							By(positive, data))
						subset := arg.Have(
							"the positive indices lie among the indices at most k",
							"«indices»(k) ⊆ {i:num | i ≤ k}",
							BySets())
						indices := arg.TermAs[Set[Nat]]("«indices»(k)")
						finite := arg.Have(
							"there are finitely many positive indices up to k",
							"finite(«indices»(k))",
							By(
								subset,
								num_segment.FiniteBelow.At(k),
								finite_set.FiniteSubset.At(indices, arg.TermAs[Set[Nat]]("{i:num | i ≤ k}"))))
						last := arg.Have(
							"k itself is one of the positive indices",
							"k ∈ «indices»(k)",
							BySets(positive, nat_order.LessEqRefl.At(k)))
						difference := arg.Have(
							"the last coefficient uses the constant term of a",
							"k - k = 0",
							ByArith())
						separates := arg.Have(
							"in each recurrence the sum at k is the count at k plus the sum over the earlier indices",
							"∀f:(num → A). series_recurrence(R, a, f) ⇒ «countSum»(f, k) = f(k) + «earlierCountSum»(f, k)",
							Derive(func(arg *Argument) {
								arg.FixAs[Fun[Nat, A]]("f")
								recurrence := arg.Unfolded(arg.Assume(), SeriesRecurrenceDef)
								products := arg.Have(
									"every summand lies in the ring carrier",
									"∀i:num. «countTerm»(f, k, i) ∈ R.carrier",
									By(comm_ring.MulIn.Read(ring), recurrence))
								split := arg.Have(
									"remove the last summand",
									"«countSum»(f, k) = «countTerm»(f, k, k) + «earlierCountSum»(f, k)",
									By(
										finite,
										last,
										products,
										module.ModuleSumDeleteMonoid.Read(additive).At(
											indices, k, arg.TermAs[Fun[Nat, A]]("«countTerm»(f, k)"))))
								lastTerm := arg.Have(
									"the last summand is f at k, as a(0) is one",
									"«countTerm»(f, k, k) = f(k)",
									By(Normalized, unit, difference, recurrence))
								arg.Show(
									"so the sum is f at k plus the earlier sum",
									Simp(Fwd(split), Fwd(lastTerm)),
									Basic())
							}))
						below := arg.Have(
							"an index left after deleting k is strictly below k",
							"∀i:num. i ∈ «earlier»(k) ⇒ i < k",
							BySets(nat_order.LessEqSplit))
						agree := arg.Have(
							"the induction hypothesis identifies every remaining summand",
							"∀i:num. i ∈ «earlier»(k) ⇒ «countTerm»(m₁, k, i) = «countTerm»(m₂, k, i)",
							By(ih, below))
						equalEarlier := arg.Have(
							"the sums of the earlier summands agree",
							"«earlierCountSum»(m₁, k) = «earlierCountSum»(m₂, k)",
							By(agree, module.ModuleSumCongruence))
						finiteEarlier := arg.Have(
							"deleting the last index leaves a finite set",
							"finite(«earlier»(k))",
							By(finite, finite_set.FiniteDelete))
						inEarlier := arg.Have(
							"the common earlier sum lies in the carrier",
							"«earlierCountSum»(m₁, k) ∈ R.carrier",
							By(
								finiteEarlier,
								coefficients,
								comm_ring.MulIn.Read(ring),
								module.ModuleSumInMonoid.Read(additive)))
						balanced := arg.Have(
							"both counts added to the same earlier sum agree",
							"m₁(k) + «earlierCountSum»(m₁, k) = m₂(k) + «earlierCountSum»(m₁, k)",
							CalcEq(
								Leg(
									arg.TermAs[A]("«countSum»(m₁, k)"),
									"m₁'s recurrence gathers m₁(k) and its earlier sum into its sum at k",
									GroupPremises(recurrences, separates.At(m1)).Rw(),
									Basic()),
								Leg(
									arg.TermAs[A]("«countSum»(m₂, k)"),
									"both recurrences equate their sum at k with k·a(k)",
									By(equalSums)),
								Leg(
									arg.TermAs[A]("m₂(k) + «earlierCountSum»(m₂, k)"),
									"m₂'s recurrence splits its sum at k into m₂(k) and its earlier sum",
									GroupPremises(recurrences, separates.At(m2)).Rw(),
									Basic()),
								FinalLeg(
									"and the earlier sums agree, by the induction hypothesis",
									equalEarlier.Rw(),
									Basic())))
						arg.Show(
							"cancel the common earlier sum in the additive group",
							By(
								balanced,
								inEarlier,
								coefficients.At(k),
								group.RightCancelOn.Read(abelian_group.GroupOn.Read(comm_ring.AddGroupOn.Read(ring))).AsFact().At(
									arg.TermAs[A]("«earlierCountSum»(m₁, k)"), m1.Apply(k), m2.Apply(k))))
					}))))
	}),
})}

// RecurrenceDeterminesCoefficients — over an integral domain of
// characteristic zero a recurrence determines its coefficients: strong
// induction identifies the sums, then the nonzero index cancels.
var RecurrenceDeterminesCoefficients = recurrenceDeterminesCoefficientsThm{family.Add(registry.ProofEntry{
	Name: "RecurrenceDeterminesCoefficients",
	Key:  "prop_b267c54aefe9244",
	Build: integral_domain.IntegralDomainOn.Law(Statement{
		Binders: "∀a b m:(num → A).",
		Hypotheses: []string{
			"characteristic_zero(R)",
			"series_recurrence(R, a, m)",
			"series_recurrence(R, b, m)",
		},
		Conclusion: "a = b",
		Abbrev: Abbrev{
			{Name: "term", Text: "λf:(num → A). λj:num. λi:num. m(i) * f(j - i)"},
			{Name: "sum", Text: "λf:(num → A). λj:num. module_sum(R.add, R.zero, «indices»(j), «term»(f, j))"},
		},
	}, func(
		arg *Argument,
		domain integral_domain.IntegralDomainFact[on.R],
		a, b, m *Arrow[Nat, A],
		characteristicZero, aRecurrence, bRecurrence Fact,
	) {
		aData := arg.Unfolded(aRecurrence, SeriesRecurrenceDef)
		bData := arg.Unfolded(bRecurrence, SeriesRecurrenceDef)
		initial := arg.Have(
			"both constant coefficients are one",
			"a(0) = R.one ∧ b(0) = R.one",
			By(aData, bData))
		coefficients := arg.Have(
			"both coefficient sequences take values in the domain's carrier",
			"∀j:num. a(j) ∈ R.carrier ∧ b(j) ∈ R.carrier",
			By(aData, bData))
		ring := integral_domain.Ring.Read(domain)
		R := arg.TermAs[RingOps[A]]("R")
		arg.Do(Funext())
		arg.Show(
			"strong induction compares the two coefficient sequences",
			ByInduction(nat_order.StrongInduction,
				Case(
					"agreement below the index identifies the recurrence sums",
					Derive(func(arg *Argument) {
						k := arg.FixAs[Nat]("k")
						ih := arg.Assume()
						indexNonzero := arg.Unless(
							arg.Term("k = 0"),
							"the constant coefficients agree",
							Given(func(arg *Argument, zero Fact) {
								arg.Show(
									"the initial values are the same identity",
									Simp(Fwd(zero), Fwd(initial)),
									Basic())
							}))
						positive := arg.Have(
							"the remaining index is positive",
							"0 < k",
							ByArith(indexNonzero))
						equalSums := arg.Have(
							"the recurrence sums read only the coefficients below k, where a and b agree",
							"«sum»(a, k) = «sum»(b, k)",
							By(ih, RecurrenceSumCongruence.At(R, m, a, b, k)))
						balanced := arg.Have(
							"the recurrences give equal scalar multiples of the coefficients",
							"monoid_pow(R.add, R.zero, R.one, k) * a(k) = monoid_pow(R.add, R.zero, R.one, k) * b(k)",
							By(positive, aData, bData, equalSums))
						scalarNonzero := arg.Have(
							"characteristic zero makes the positive index a nonzero scalar",
							"monoid_pow(R.add, R.zero, R.one, k) ≠ R.zero",
							By(positive, characteristicZero, comm_ring.CharacteristicZeroDef.At(R)))
						inCarrier := arg.Have(
							"the natural scalar belongs to the additive monoid carrier",
							"monoid_pow(R.add, R.zero, R.one, k) ∈ R.carrier",
							By(
								comm_ring.OneIn.Read(ring),
								comm_monoid.PowIn.Read(comm_ring.AddMonoidOn.Read(ring)).AsFact().At(arg.TermAs[A]("R.one"), k)))
						arg.Show(
							"cancel the nonzero scalar in the integral domain",
							By(
								inCarrier,
								scalarNonzero,
								balanced,
								coefficients.At(k),
								integral_domain.MulCancelLeft.Read(domain).AsFact().At(
									arg.TermAs[A]("monoid_pow(R.add, R.zero, R.one, k)"), a.Apply(k), b.Apply(k))))
					}))))
	}),
})}

// FormalExpCoefficients — over a field of characteristic zero, the formal
// exponential of a series x with x(0) = 0 satisfies the recurrence with
// counting sequence n·x(n). Natural recursion constructs a solution, a(0) = 1
// and a(n) = (1/n)·Σ_{0<i≤n} i·x(i)·a(n − i), the inverse of n existing in
// characteristic zero; and the formal exponential is the solution Hilbert
// choice selects.
var FormalExpCoefficients = formalExpCoefficientsThm{family.Add(registry.ProofEntry{
	Name: "FormalExpCoefficients",
	Key:  "prop_edd3d297de3e18c6",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀x:(num → A).",
		Hypotheses: []string{
			"characteristic_zero(field_ring(L))",
			"x(0) = L.zero",
			"∀n:num. x(n) ∈ L.carrier",
		},
		Conclusion: "series_recurrence(field_ring(L), " +
			"    formal_exp_zero(field_ring(L), x), " +
			"    λn:num. monoid_pow(L.add, L.zero, L.one, n) * x(n))",
		Abbrev: Abbrev{
			{Name: "sum", Text: "λf:(num → A). λn:num. " +
				"    module_sum(L.add, L.zero, «indices»(n), λi:num. counts(i) * f(n - i))"},
		},
	}, func(
		arg *Argument,
		L field.FieldFact[on.L],
		x *Arrow[Nat, A],
		characteristicZero, noConstantTerm, xIn Fact,
	) {
		ring := field.RingOn.Read(L)
		fieldRing := arg.TermAs[RingOps[A]]("field_ring(L)")
		additive := comm_ring.AddMonoidOn.Read(ring)
		multiplicative := comm_ring.MulMonoidOn.Read(ring)
		_, scalarDef := arg.LetAs[Fun[Nat, A]]("scalar", "λn:num. monoid_pow(L.add, L.zero, L.one, n)")
		counts, countsDef := arg.LetAs[Fun[Nat, A]]("counts", "λn:num. scalar(n) * x(n)")
		step, stepDef := arg.LetAs[Fun2[Fun[Nat, A], Nat, A]](
			"step", "λf:(num → A). λn:num. COND(n = 0, L.one, L.inv(scalar(n)) * «sum»(f, n))")
		extensional := arg.Have(
			"the recursive step depends only on earlier coefficients",
			"∀f g:(num → A). ∀n:num. (∀j:num. j < n ⇒ f(j) = g(j)) ⇒ step(f, n) = step(g, n)",
			Derive(func(arg *Argument) {
				f := arg.FixAs[Fun[Nat, A]]("f")
				g := arg.FixAs[Fun[Nat, A]]("g")
				n := arg.FixAs[Nat]("n")
				earlier := arg.Assume()
				equalSums := arg.Have(
					"the two recurrence sums read only the coefficients below n, where f and g agree",
					"«sum»(f, n) = «sum»(g, n)",
					By(earlier, RecurrenceSumCongruence.At(fieldRing, counts, f, g, n)))
				arg.Show(
					"equal sums give the same recursive step",
					Simp(Fwd(stepDef), Fwd(equalSums)),
					Basic())
			}))
		coeff, recursive := arg.ObtainAs[Fun[Nat, A]](
			"natural recursion constructs the coefficient sequence",
			"∃a:(num → A). ∀n:num. a(n) = step(a, n)",
			Named("coeff"),
			By(extensional, well_founded.NatRecursion.At(step)))
		initial := arg.Have(
			"the recursive sequence starts at one",
			"coeff(0) = L.one",
			By(Normalized, recursive.At(arg.TermAs[Nat]("0")), stepDef))
		scalarsIn := arg.Have(
			"natural scalars lie in the field carrier",
			"∀n:num. scalar(n) ∈ L.carrier",
			By(comm_ring.OneIn.Read(ring), comm_monoid.PowIn.Read(additive), scalarDef))
		countsIn := arg.Have(
			"the counting coefficients lie in the field carrier",
			"∀n:num. counts(n) ∈ L.carrier",
			By(comm_ring.MulIn.Read(ring), scalarsIn, countsDef, xIn))
		finite := arg.Have(
			"every recurrence index set is finite",
			"∀n:num. finite(«indices»(n))",
			Derive(func(arg *Argument) {
				n := arg.FixAs[Nat]("n")
				subset := arg.Have(
					"positive bounded indices lie in an initial segment",
					"«indices»(n) ⊆ {i:num | i ≤ n}",
					BySets())
				arg.Show(
					"a subset of the finite initial segment is finite",
					By(
						subset,
						num_segment.FiniteBelow.At(n),
						finite_set.FiniteSubset.At(
							arg.TermAs[Set[Nat]]("«indices»(n)"), arg.TermAs[Set[Nat]]("{i:num | i ≤ n}"))))
			}))
		formula := arg.Have(
			"the recursive coefficient at a nonzero index is the inverse scalar times its recurrence sum",
			"∀n:num. n ≠ 0 ⇒ coeff(n) = L.inv(scalar(n)) * «sum»(coeff, n)",
			Derive(func(arg *Argument) {
				n := arg.FixAs[Nat]("n")
				indexNonzero := arg.Assume()
				arg.Show(
					"the recursive step takes its second branch",
					recursive.Simp(Fwd(stepDef)),
					By(indexNonzero, recursive.At(n)))
			}))
		sumIn := arg.Have(
			"a recurrence sum lies in the carrier once the coefficients below its index do",
			"∀n:num. (∀j:num. j < n ⇒ coeff(j) ∈ L.carrier) ⇒ «sum»(coeff, n) ∈ L.carrier",
			Derive(func(arg *Argument) {
				n := arg.FixAs[Nat]("n")
				earlier := arg.Assume()
				below := arg.Have(
					"every recursive summand uses an earlier index",
					"∀i:num. i ∈ «indices»(n) ⇒ n - i < n",
					ByArith())
				products := arg.Have(
					"so each product lies in the carrier",
					"∀i:num. i ∈ «indices»(n) ⇒ counts(i) * coeff(n - i) ∈ L.carrier",
					By(comm_ring.MulIn.Read(ring), countsIn, earlier, below))
				arg.Show(
					"a finite sum of carrier elements lies in the carrier",
					By(
						finite.At(n),
						products,
						module.ModuleSumInMonoid.Read(additive).At(
							arg.TermAs[Set[Nat]]("«indices»(n)"), arg.TermAs[Fun[Nat, A]]("λi:num. counts(i) * coeff(n - i)"))))
			}))
		coefficientsIn := arg.Have(
			"the recursive coefficients lie in the field carrier",
			"∀n:num. coeff(n) ∈ L.carrier",
			ByInduction(nat_order.StrongInduction,
				Case(
					"earlier carrier values keep the next recursive coefficient in the carrier",
					Derive(func(arg *Argument) {
						k := arg.FixAs[Nat]("k")
						ih := arg.Assume()
						indexNonzero := arg.Unless(
							arg.Term("k = 0"),
							"the constant coefficient is the field unit",
							Given(func(arg *Argument, zero Fact) {
								arg.Show(
									"the field unit belongs to the carrier",
									By(Normalized, comm_ring.OneIn.Read(ring), initial, zero))
							}))
						arg.Show(
							"inverse and multiplication closure keep the coefficient in the carrier",
							By(
								comm_ring.MulIn.Read(ring),
								scalarsIn.At(k),
								ih,
								sumIn.At(k),
								indexNonzero,
								formula.At(k),
								field.InvIn.Read(L).AsFact().At(arg.TermAs[A]("scalar(k)"))))
					}))))
		countsZero := arg.Have(
			"the counting sequence starts at zero",
			"counts(0) = L.zero",
			By(
				Normalized,
				comm_ring.MulRightZeroOn.Read(ring),
				scalarsIn.At(arg.TermAs[Nat]("0")),
				countsDef,
				noConstantTerm))
		positiveRecurrence := arg.Have(
			"multiplication by the positive index clears its inverse",
			"∀n:num. 0 < n ⇒ scalar(n) * coeff(n) = «sum»(coeff, n)",
			Derive(func(arg *Argument) {
				n := arg.FixAs[Nat]("n")
				positive := arg.Assume()
				scalarNonzero := arg.Have(
					"characteristic zero makes the positive natural scalar nonzero",
					"scalar(n) ≠ L.zero",
					By(positive, scalarDef, characteristicZero, comm_ring.CharacteristicZeroDef.At(fieldRing)))
				inverse := arg.Have(
					"the nonzero scalar has a multiplicative inverse",
					"scalar(n) * L.inv(scalar(n)) = L.one",
					By(
						scalarNonzero,
						scalarsIn.At(n),
						field.MulRightInverseOn.Read(L).AsFact().At(arg.TermAs[A]("scalar(n)"))))
				indexNonzero := arg.Have(
					"a positive index is nonzero",
					"n ≠ 0",
					ByArith(positive))
				scalarAndInverseIn := arg.Have(
					"the scalar and its inverse belong to the field carrier",
					"scalar(n) ∈ L.carrier ∧ L.inv(scalar(n)) ∈ L.carrier",
					By(scalarsIn.At(n), field.InvIn.Read(L).AsFact().At(arg.TermAs[A]("scalar(n)"))))
				sum := arg.TermAs[A]("«sum»(coeff, n)")
				sumInCarrier := arg.Have(
					"the recurrence sum lies in the field carrier",
					"«sum»(coeff, n) ∈ L.carrier",
					By(coefficientsIn, sumIn.At(n)))
				arg.Show(
					"the inverse scalar cancels against the scalar",
					CalcEq(
						Leg(
							arg.TermAs[A]("scalar(n) * (L.inv(scalar(n)) * «sum»(coeff, n))"),
							"at the nonzero index n the coefficient is the inverse scalar times the sum",
							By(indexNonzero, formula.At(n))),
						Leg(
							arg.TermAs[A]("scalar(n) * L.inv(scalar(n)) * «sum»(coeff, n)"),
							"the product associates",
							By(
								scalarAndInverseIn,
								sumInCarrier,
								comm_monoid.AssocOn.Read(multiplicative).AsFact().At(
									arg.TermAs[A]("scalar(n)"), arg.TermAs[A]("L.inv(scalar(n))"), sum))),
						FinalLeg(
							"the scalar times its inverse is one, the unit of the product",
							By(inverse, sumInCarrier, comm_monoid.LeftIdentityOn.Read(multiplicative).AsFact().At(sum))),
					))
			}))
		recurrence := arg.Have(
			"the constructed sequence satisfies every recurrence clause",
			"series_recurrence(field_ring(L), coeff, counts)",
			By(
				coefficientsIn,
				countsIn,
				positiveRecurrence,
				initial,
				countsZero,
				scalarDef,
				SeriesRecurrenceDef.At(fieldRing, coeff, counts)))
		arg.Show(
			"Hilbert choice selects a sequence satisfying the recurrence",
			By(recurrence, countsDef, scalarDef, FormalExpDef.At(fieldRing, x)))
	}),
})}

// FormalExpOfCounts — over a field of characteristic zero, a series with
// counting sequence m is the formal exponential of m(n)/n, the count of
// index zero read as zero. The exponential of that series solves the
// recurrence whose counting sequence is n times m(n)/n, which is m again:
// the index cancels off zero, and at zero both sides vanish. A recurrence
// determines its coefficients, so the two series agree.
var FormalExpOfCounts = formalExpOfCountsThm{family.Add(registry.ProofEntry{
	Name: "FormalExpOfCounts",
	Key:  "prop_1a803288829e6a85",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀a m:(num → A).",
		Hypotheses: []string{
			"characteristic_zero(field_ring(L))",
			"series_recurrence(field_ring(L), a, m)",
		},
		Conclusion: "a = " +
			"formal_exp_zero(field_ring(L), " +
			"    λn:num. COND(n = 0, L.zero, m(n) / monoid_pow(L.add, L.zero, L.one, n)))",
	}, func(
		arg *Argument,
		L field.FieldFact[on.L],
		a, m *Arrow[Nat, A],
		characteristicZero, recurrence Fact,
	) {
		ring := field.RingOn.Read(L)
		fieldRing := arg.TermAs[RingOps[A]]("field_ring(L)")
		data := arg.Unfolded(recurrence, SeriesRecurrenceDef)
		x, xDef := arg.LetAs[Fun[Nat, A]](
			"x", "λn:num. COND(n = 0, L.zero, m(n) / monoid_pow(L.add, L.zero, L.one, n))")
		atZero := arg.Have(
			"the series x starts at zero",
			"x(0) = L.zero",
			By(xDef))
		scalarsIn := arg.Have(
			"natural scalars lie in the field carrier",
			"∀n:num. monoid_pow(L.add, L.zero, L.one, n) ∈ L.carrier",
			By(comm_ring.OneIn.Read(ring), comm_monoid.PowIn.Read(comm_ring.AddMonoidOn.Read(ring))))
		pointwise := arg.Have(
			"each x(n) lies in the carrier, and n times x(n) is m(n)",
			"∀n:num. x(n) ∈ L.carrier ∧ monoid_pow(L.add, L.zero, L.one, n) * x(n) = m(n)",
			Derive(func(arg *Argument) {
				n := arg.FixAs[Nat]("n")
				arg.Cases(arg.Term("n = 0"))
				arg.When(
					"at zero x is zero, a zero factor kills the product, and m starts at zero",
					func(arg *Argument, zero Fact) {
						arg.Show(
							"so the two claims read the carrier's zero and m(0) = L.zero",
							zero.Rw(),
							atZero.Rw(),
							By(
								data,
								comm_ring.ZeroIn.Read(ring),
								comm_ring.MulRightZeroOn.Read(ring),
								scalarsIn.At(arg.TermAs[Nat]("0"))))
					})
				arg.Otherwise(
					"off zero x is the quotient, and the nonzero index cancels",
					func(arg *Argument, nonzero Fact) {
						quotient := arg.Have(
							"the conditional takes its second branch",
							"x(n) = m(n) / monoid_pow(L.add, L.zero, L.one, n)",
							By(Normalized, nonzero, xDef))
						scalarNonzero := arg.Have(
							"characteristic zero makes the positive index a nonzero scalar",
							"monoid_pow(L.add, L.zero, L.one, n) ≠ L.zero",
							By(
								characteristicZero,
								nonzero,
								nat_order.PosIffNonzero,
								comm_ring.CharacteristicZeroDef.At(fieldRing)))
						arg.Show(
							"the quotient of two carrier elements lies in the carrier, and the index cancels",
							quotient.Rw(),
							By(data, scalarNonzero, scalarsIn.At(n), field.DivIn.Read(L), field.DivLeftMulOn.Read(L)))
					})
			}))
		counts := arg.Have(
			"so the counting sequence n·x(n) is m",
			"(λn:num. monoid_pow(L.add, L.zero, L.one, n) * x(n)) = m",
			Funext(),
			By(pointwise))
		exponential := arg.Have(
			"the formal exponential of x solves the recurrence with counting sequence m",
			"series_recurrence(field_ring(L), formal_exp_zero(field_ring(L), x), m)",
			By(characteristicZero, atZero, pointwise, counts, FormalExpCoefficients.Read(L).At(x)))
		arg.Show(
			"a recurrence determines its coefficients",
			By(
				characteristicZero,
				recurrence,
				exponential,
				RecurrenceDeterminesCoefficients.Read(integral_domain.FieldIntegralDomain.Read(L))))
	}),
})}

// EulerDerivativeProduct — the Euler derivative, which weights the n-th
// coefficient by n, is a derivation for convolution: at i ≤ n the weight n of
// the term p(i) * q(n - i) is the numeral i added to the numeral n - i, the
// first weighting p(i) and the second q(n - i), and a finite sum of sums is
// the sum of the two sums.
var EulerDerivativeProduct = eulerDerivativeProductThm{family.Add(registry.ProofEntry{
	Name: "EulerDerivativeProduct",
	Key:  "prop_77d743964fd1226d",
	Build: family.Theorem(Statement{
		Binders:    "∀R:comm_ring_on(A). ∀p q:(num → A).",
		Hypotheses: []string{"∀i:num. p(i) ∈ R.carrier ∧ q(i) ∈ R.carrier"},
		Conclusion: "«euler»(polynomial_mul(p, q)) = " +
			"polynomial_mul(«euler»(p), q) + polynomial_mul(p, «euler»(q))",
	}, func(arg *Argument, ring comm_ring.CommRingFact[on.R], p, q *Arrow[Nat, A], coefficients Fact) {
		regular := module.RegularModuleOn.Read(ring)
		additive := comm_ring.AddMonoidOn.Read(ring)
		mulIn := comm_ring.MulIn.Read(ring)
		numerals := arg.Have(
			"every numeral lies in the ring",
			"∀k:num. «numeral»(k) ∈ R.carrier",
			By(comm_ring.OneIn.Read(ring), comm_monoid.PowIn.Read(additive)))
		one := arg.MemberOf[on.R](arg.TermAs[A]("R.one"), comm_ring.OneIn.Read(ring))
		arg.Do(Funext())
		n := arg.FixAs[Nat]("n")
		weightSplits := arg.Have(
			"at i ≤ n the weight of the term at i is the numeral i plus the numeral n - i",
			Statement{
				Binders:    "∀i:num.",
				Hypotheses: []string{"i ≤ n"},
				Conclusion: "«numeral»(n) * (p(i) * q(n - i)) = " +
					"«euler»(p, i) * q(n - i) + p(i) * «euler»(q, n - i)",
			},
			Derive(func(arg *Argument) {
				i := arg.FixAs[Nat]("i")
				below := arg.Assume()
				rest := arg.TermAs[Nat]("n - i")
				indices := arg.Have(
					"the index i and its complement add back to n",
					"i + (n - i) = n",
					ByArith(below))
				weights := arg.Have(
					"so the numeral n is the sum of their numerals",
					"«numeral»(n) = «numeral»(i) + «numeral»(n - i)",
					By(indices, comm_monoid.PowAddOn.Read(additive).At(one, i, rest)))
				arg.Show(
					"and the ring distributes that sum over the term",
					ByArith(
						ring,
						Scaled(arg.TermAs[A]("p(i) * q(n - i)"), weights),
						numerals.At(n),
						numerals.At(i),
						numerals.At(rest),
						coefficients.At(i),
						coefficients.At(rest)))
			}))
		indices := arg.TermAs[Set[Nat]]("{i:num | i ≤ n}")
		weight := arg.MemberOf[on.R](arg.TermAs[A]("«numeral»(n)"), numerals.At(n))
		arg.Show(
			"the coefficients at n agree",
			Simp(Fwd(polynomial.PolynomialMulDef), Fwd(vec_space.VecAddDef)),
			CalcEq(
				Leg(
					arg.TermAs[A](
						"module_sum(R.add, R.zero, {i:num | i ≤ n}, λi:num. «numeral»(n) * (p(i) * q(n - i)))"),
					"the numeral n passes into the finite sum",
					By(
						mulIn,
						coefficients,
						num_segment.FiniteBelow.At(n),
						module.ModuleSumSmul.Read(regular).At(
							indices, weight, arg.TermAs[Fun[Nat, A]]("λi:num. p(i) * q(n - i)")))),
				Leg(
					arg.TermAs[A](
						"module_sum(R.add, "+
							"    R.zero, "+
							"    {i:num | i ≤ n}, "+
							"    λi:num. «euler»(p, i) * q(n - i) + p(i) * «euler»(q, n - i))"),
					"split the weight of each term",
					By(weightSplits, module.ModuleSumCongruence)),
				FinalLeg(
					"a finite sum of sums is the sum of the two sums",
					By(
						mulIn,
						numerals,
						coefficients,
						num_segment.FiniteBelow.At(n),
						module.ModuleSumAdd.Read(regular).At(
							indices,
							arg.TermAs[Fun[Nat, A]]("λi:num. «euler»(p, i) * q(n - i)"),
							arg.TermAs[Fun[Nat, A]]("λi:num. p(i) * «euler»(q, n - i)")))),
			))
	}),
})}

// RecurrenceEuler — a recurrence is the Euler equation, the Euler derivative
// of a as m times a, together with its initial values and with every term of
// a and m in the ring: m(0) = 0 makes the missing zeroth summand vanish in the
// full convolution, and at n = 0 both sides of the equation vanish.
var RecurrenceEuler = recurrenceEulerThm{family.Add(registry.ProofEntry{
	Name: "RecurrenceEuler",
	Key:  "prop_409a790dc79157ae",
	Build: family.Sections(Statement{
		Binders: "∀R:comm_ring_on(A). ∀a m:(num → A).",
		Conclusion: "series_recurrence(R, a, m) ⇔ " +
			"a(0) = R.one ∧ " +
			"m(0) = R.zero ∧ " +
			"(∀n:num. a(n) ∈ R.carrier ∧ m(n) ∈ R.carrier) ∧ " +
			"«euler»(a) = polynomial_mul(m, a)",
	}, func(ctx *Script, headline string) *GoalStackNode {
		restricted := ctx.Lemma(Statement{
			Binders:    "∀R:comm_ring_on(A). ∀m a:(num → A). ∀n:num.",
			Hypotheses: []string{"m(0) = R.zero", "∀i:num. m(i) ∈ R.carrier ∧ a(i) ∈ R.carrier"},
			Conclusion: "polynomial_mul(m, a, n) = " +
				"module_sum(R.add, R.zero, «indices»(n), λi:num. m(i) * a(n - i))",
		}, func(
			arg *Argument,
			ring comm_ring.CommRingFact[on.R],
			m, a *Arrow[Nat, A],
			n *Expr[Nat],
			zeroCount, coefficients Fact,
		) {
			vanishing := arg.Have(
				"the one index up to n that is not positive is 0, where m(0) = 0 annihilates the summand",
				"∀i:num. i ∈ {j:num | j ≤ n} ∧ i ∉ «indices»(n) ⇒ m(i) * a(n - i) = R.zero",
				Derive(func(arg *Argument) {
					arg.FixAs[Nat]("i")
					outside := arg.Assume()
					isZero := arg.Have(
						"an index up to n that is not positive is 0",
						"i = 0",
						ByArith(outside))
					arg.Show(
						"so the summand is zero times a member of the ring",
						isZero.Rw(),
						zeroCount.Rw(),
						By(coefficients.At(arg.TermAs[Nat]("n - 0")), comm_ring.MulLeftZeroOn.Read(ring)))
				}))
			within := arg.Have(
				"the positive indices lie among the indices up to n",
				"«indices»(n) ⊆ {i:num | i ≤ n}",
				BySets())
			arg.Show(
				"so the convolution sums only over the positive indices",
				Simp(Fwd(polynomial.PolynomialMulDef)),
				By(
					vanishing,
					coefficients,
					within,
					comm_ring.MulIn.Read(ring),
					num_segment.FiniteBelow.At(n),
					module.ModuleSumSupport.Read(module.RegularModuleOn.Read(ring)).At(
						arg.TermAs[Set[Nat]]("{i:num | i ≤ n}"),
						arg.TermAs[Set[Nat]]("«indices»(n)"),
						arg.TermAs[Fun[Nat, A]]("λi:num. m(i) * a(n - i)"))))
		})
		return ctx.Theorem(headline, func(
			arg *Argument,
			ring comm_ring.CommRingFact[on.R],
			a, m *Arrow[Nat, A],
		) {
			R := arg.TermAs[RingOps[A]]("R")
			arg.Do(Simp(Fwd(SeriesRecurrenceDef)))
			arg.Iff()
			arg.Forward(
				"the recurrence gives the Euler equation at every coefficient",
				func(arg *Argument, recurrence Fact) {
					equation := arg.Have(
						"the positive recurrence and m(0) = 0 give the full convolution",
						"«euler»(a) = polynomial_mul(m, a)",
						Funext(),
						Derive(func(arg *Argument) {
							n := arg.FixAs[Nat]("n")
							nonzero := arg.Unless(
								arg.TermAs[Bool]("n = 0"),
								"at zero the weight is zero and the product's constant coefficient is m(0) * a(0)",
								Given(func(arg *Argument, isZero Fact) {
									arg.Show(
										"both sides vanish",
										isZero.Rw(),
										By(
											recurrence,
											polynomial.PolynomialMulAtZero.Read(ring).At(m, a),
											comm_monoid.MonoidPowDef,
											comm_ring.MulLeftZeroOn.Read(ring)))
								}))
							arg.Show(
								"at a positive index the recurrence's sum is the convolution coefficient",
								By(ring, recurrence, nonzero, nat_order.PosIffNonzero, At(restricted, R, m, a, n)))
						}))
					arg.Show(
						"the initial values and the memberships carry over",
						By(recurrence, equation))
				})
			arg.Backward(
				"the initial values carry over and the Euler equation "+
					"restricts to the recurrence's positive indices",
				func(arg *Argument, data Fact) {
					arg.Show(
						"the recurrence holds at every positive index",
						By(ring, data, At(restricted, R, m, a)))
				})
		})
	}),
})}

// RecurrenceProduct — convolution adds counting sequences: the Euler derivative
// of the product splits by EulerDerivativeProduct, the two Euler equations put
// m and k in front of p and q, and the convolution distributes over m + k.
var RecurrenceProduct = recurrenceProductThm{family.Add(registry.ProofEntry{
	Name: "RecurrenceProduct",
	Key:  "prop_3966f0f17d8fdc4e",
	Build: family.Theorem(Statement{
		Binders:    "∀R:comm_ring_on(A). ∀p q m k:(num → A).",
		Hypotheses: []string{"series_recurrence(R, p, m)", "series_recurrence(R, q, k)"},
		Conclusion: "series_recurrence(R, polynomial_mul(p, q), λn:num. m(n) + k(n))",
	}, func(
		arg *Argument,
		ring comm_ring.CommRingFact[on.R],
		p, q, m, k *Arrow[Nat, A],
		pRecurrence, qRecurrence Fact,
	) {
		R := arg.TermAs[RingOps[A]]("R")
		pData := arg.Simplified(pRecurrence, Fwd(RecurrenceEuler))
		qData := arg.Simplified(qRecurrence, Fwd(RecurrenceEuler))
		productIn := arg.Have(
			"every coefficient of the product lies in the ring",
			"∀n:num. polynomial_mul(p, q, n) ∈ R.carrier",
			By(ring, pData, qData, polynomial.SeriesMulIn))
		arg.Show(
			"read as an Euler equation, the product's clauses are those of its two factors",
			Simp(Fwd(RecurrenceEuler)),
			SplitConjAll(Case(
				"the two constant coefficients multiply to one",
				By(
					pData,
					qData,
					comm_ring.OneIn.Read(ring),
					polynomial.PolynomialMulAtZero.Read(ring).At(p, q),
					comm_monoid.LeftIdentityOn.Read(comm_ring.MulMonoidOn.Read(ring)))),
				Case(
					"both counting sequences start at zero, so their sum does",
					ByArith(ring, pData, qData)),
				Case(
					"the coefficients of the product lie in the ring",
					By(productIn)),
				Case(
					"and so does every term of the sum of the counting sequences",
					By(pData, qData, comm_ring.AddIn.Read(ring))),
				Case(
					"the product satisfies the Euler equation with the sum of the counting sequences",
					Derive(func(arg *Argument) {
						sum := arg.Have(
							"the pointwise sum of the counting sequences is their sum as sequences",
							"(λn:num. m(n) + k(n)) = m + k",
							Funext(),
							Simp(Fwd(vec_space.VecAddDef)),
							Basic())
						productRule := arg.Have(
							"the Euler derivative of the product splits, each part by its Euler equation",
							"«euler»(polynomial_mul(p, q)) = "+
								"polynomial_mul(polynomial_mul(m, p), q) + polynomial_mul(p, polynomial_mul(k, q))",
							By(ring, pData, qData, EulerDerivativeProduct.At(R, p, q)))
						arg.Show(
							"reassociate the two terms and distribute the sum of the counting sequences",
							sum.Rw(),
							By(
								productRule,
								productIn,
								pData,
								qData,
								polynomial.PolynomialMulAssoc.Read(ring).At(m, p, q),
								polynomial.PolynomialMulLeftComm.Read(ring).At(p, k, q),
								polynomial.PolynomialMulDistribLeft.Read(ring).At(
									m, k, arg.TermAs[Fun[Nat, A]]("polynomial_mul(p, q)"))))
					})),
			))
	}),
})}

// RecurrenceQuotient — an invertible factor's counting sequence can be
// subtracted from that of a product: the Euler derivative of the product
// splits by EulerDerivativeProduct, the two Euler equations put k and m in
// front, the inverse h cancels the common factor p, and the convolution
// distributes over k - m.
var RecurrenceQuotient = recurrenceQuotientThm{family.Add(registry.ProofEntry{
	Name: "RecurrenceQuotient",
	Key:  "prop_fe1f854e06ce2412",
	Build: family.Theorem(Statement{
		Binders: "∀R:comm_ring_on(A). ∀p q h m k:(num → A).",
		Hypotheses: []string{
			"series_recurrence(R, p, m)",
			"series_recurrence(R, polynomial_mul(p, q), k)",
			"∀n:num. q(n) ∈ R.carrier ∧ h(n) ∈ R.carrier",
			"polynomial_mul(h, p) = basis_vector(0)",
		},
		Conclusion: "series_recurrence(R, q, λn:num. k(n) - m(n))",
	}, func(
		arg *Argument,
		ring comm_ring.CommRingFact[on.R],
		p, q, h, m, k *Arrow[Nat, A],
		denominator, numerator, coefficients, inverse Fact,
	) {
		R := arg.TermAs[RingOps[A]]("R")
		pData := arg.Simplified(denominator, Fwd(RecurrenceEuler))
		productData := arg.Simplified(numerator, Fwd(RecurrenceEuler))
		arg.Show(
			"read as an Euler equation, the quotient's clauses come from those of p and of the product",
			Simp(Fwd(RecurrenceEuler)),
			SplitConjAll(Case(
				"the constant coefficient is one: the product's is p(0) times q(0), and both it and p(0) are one",
				By(
					pData,
					productData,
					coefficients,
					polynomial.PolynomialMulAtZero.Read(ring).At(p, q),
					comm_monoid.LeftIdentityOn.Read(comm_ring.MulMonoidOn.Read(ring)))),
				Case(
					"both counting sequences start at zero, so their difference does",
					ByArith(ring, pData, productData)),
				Case(
					"the terms of q lie in the ring",
					By(coefficients)),
				Case(
					"and so does every difference of counts",
					By(pData, productData, comm_ring.SubIn.Read(ring))),
				Case(
					"cancelling p from the two Euler equations leaves that of q",
					Derive(func(arg *Argument) {
						difference := arg.Have(
							"the pointwise difference of the counting sequences is their difference as sequences",
							"(λn:num. k(n) - m(n)) = k - m",
							Funext(),
							Simp(Fwd(vec_space.VecSubDef)),
							Basic())
						terms := arg.Have(
							"every term of p, q, h, m and k lies in the ring",
							"∀n:num. "+
								"    p(n) ∈ R.carrier ∧ q(n) ∈ R.carrier ∧ h(n) ∈ R.carrier ∧ m(n) ∈ R.carrier ∧ k(n) ∈ R.carrier",
							By(pData, productData, coefficients))
						numerals := arg.Have(
							"every numeral lies in the ring",
							"∀j:num. «numeral»(j) ∈ R.carrier",
							By(comm_ring.OneIn.Read(ring), comm_monoid.PowIn.Read(comm_ring.AddMonoidOn.Read(ring))))
						products := arg.Have(
							"the products of k and of m with q and the Euler derivative of q lie in the ring",
							"∀n:num. "+
								"    polynomial_mul(k, q, n) ∈ R.carrier ∧ "+
								"    polynomial_mul(m, q, n) ∈ R.carrier ∧ "+
								"    «euler»(q, n) ∈ R.carrier",
							By(ring, terms, numerals, polynomial.SeriesMulIn, comm_ring.MulIn.Read(ring)))
						sum := arg.Have(
							"and so does the sum of the last two",
							"∀n:num. (polynomial_mul(m, q) + «euler»(q))(n) ∈ R.carrier",
							Simp(Fwd(vec_space.VecAddDef)),
							By(products, comm_ring.AddIn.Read(ring)))
						productRule := arg.Have(
							"the Euler derivative of the product splits, its first part by the Euler equation of p",
							"polynomial_mul(k, polynomial_mul(p, q)) = "+
								"polynomial_mul(polynomial_mul(m, p), q) + polynomial_mul(p, «euler»(q))",
							By(ring, pData, productData, coefficients, EulerDerivativeProduct.At(R, p, q)))
						left := arg.TermAs[Fun[Nat, A]]("polynomial_mul(k, q)")
						right := arg.TermAs[Fun[Nat, A]]("polynomial_mul(m, q) + «euler»(q)")
						lifted := arg.Have(
							"put the common factor p at the left of both sides",
							"polynomial_mul(p, polynomial_mul(k, q)) = polynomial_mul(p, polynomial_mul(m, q) + «euler»(q))",
							By(
								productRule,
								terms,
								products,
								polynomial.PolynomialMulLeftComm.Read(ring).At(k, p, q),
								polynomial.PolynomialMulLeftComm.Read(ring).At(m, p, q),
								polynomial.PolynomialMulAssoc.Read(ring).At(m, p, q),
								polynomial.PolynomialMulDistrib.Read(ring).At(
									p, arg.TermAs[Fun[Nat, A]]("polynomial_mul(m, q)"), arg.TermAs[Fun[Nat, A]]("«euler»(q)"))))
						cancelled := arg.Have(
							"the inverse removes the common factor",
							"polynomial_mul(k, q) = polynomial_mul(m, q) + «euler»(q)",
							By(
								inverse,
								lifted,
								terms,
								products,
								sum,
								polynomial.PolynomialMulAssoc.Read(ring).At(h, p, left),
								polynomial.PolynomialMulAssoc.Read(ring).At(h, p, right),
								polynomial.PolynomialOneMul.Read(ring).At(left),
								polynomial.PolynomialOneMul.Read(ring).At(right)))
						subtraction := arg.Have(
							"the product distributes over the difference of the counting sequences",
							"polynomial_mul(k - m, q) = polynomial_mul(k, q) - polynomial_mul(m, q)",
							By(terms, polynomial.PolynomialMulSubLeft.Read(ring).At(k, m, q)))
						arg.Do(difference.Rw(), subtraction.Rw(), cancelled.Rw(), Simp(
							Fwd(vec_space.VecSubDef),
							Fwd(vec_space.VecAddDef)), Funext())
						n := arg.FixAs[Nat]("n")
						arg.Show(
							"subtracting the term of m leaves the quotient's Euler derivative",
							ByArith(ring, products.At(n), numerals.At(n), coefficients.At(n)))
					})),
			))
	}),
})}

// RecurrenceRingMap — a ring homomorphism carries a recurrence to the recurrence
// of the images: it keeps the initial values and the memberships, and read as an
// Euler equation the recurrence of a goes across term by term, the map keeping
// the numeral n and the product by it on one side and the convolution of m and a
// on the other (ConvolutionRingMap).
var RecurrenceRingMap = recurrenceRingMapThm{family.Add(registry.ProofEntry{
	Name: "RecurrenceRingMap",
	Key:  "prop_2210721f52fe19f5",
	Build: family.Theorem(Statement{
		Binders:    "∀R:comm_ring_on(A). ∀S:comm_ring_on(B). ∀ι:(A → B). ∀a m:(num → A).",
		Hypotheses: []string{"ring_homomorphism(R, S, ι)", "series_recurrence(R, a, m)"},
		Conclusion: "series_recurrence(S, λn:num. ι(a(n)), λn:num. ι(m(n)))",
	}, func(
		arg *Argument,
		source comm_ring.CommRingFact[on.R],
		target comm_ring.CommRingFact[on.S],
		ι *Arrow[A, B],
		a, m *Arrow[Nat, A],
		hom, recurrence Fact,
	) {
		R, S := arg.TermAs[RingOps[A]]("R"), arg.TermAs[RingOps[B]]("S")
		data := arg.Simplified(recurrence, Fwd(RecurrenceEuler))
		coefficients := arg.Have(
			"both sequences take values in the source ring",
			"∀n:num. a(n) ∈ R.carrier ∧ m(n) ∈ R.carrier",
			By(data))
		convolution := arg.Have(
			"the map carries the convolution of m and a to that of the images",
			"(λn:num. ι(polynomial_mul(m, a, n))) = polynomial_mul(λi:num. ι(m(i)), λi:num. ι(a(i)))",
			By(source, target, hom, coefficients, polynomial.ConvolutionRingMap.At(R, S, ι, m, a)))
		numerals := arg.Have(
			"every numeral lies in the source ring",
			"∀k:num. «numeral»(k) ∈ R.carrier",
			By(comm_ring.OneIn.Read(source), comm_monoid.PowIn.Read(comm_ring.AddMonoidOn.Read(source))))
		arg.Show(
			"read as an Euler equation, the clauses of the images come from those of a and m",
			Simp(Fwd(RecurrenceEuler)),
			SplitConjAll(Case(
				"the map keeps the one, so the constant coefficient stays one",
				By(Normalized, data, ring_homomorphism.MapOne.Read(hom))),
				Case(
					"the map keeps the zero, so the counting sequence stays zero at zero",
					By(Normalized, data, ring_homomorphism.MapZero.Read(hom))),
				Case(
					"the images of the terms of a lie in the target ring",
					By(coefficients, ring_homomorphism.MapIn.Read(hom))),
				Case(
					"and so do those of m",
					By(coefficients, ring_homomorphism.MapIn.Read(hom))),
				Case(
					"the map carries the Euler equation of a term by term",
					Derive(func(arg *Argument) {
						arg.Do(convolution.RwRev(), Funext())
						n := arg.FixAs[Nat]("n")
						equation := arg.Have(
							"the Euler equation of a at n",
							"«euler»(a, n) = polynomial_mul(m, a, n)",
							By(data))
						arg.Show(
							"the map keeps the numeral n and its product with a(n)",
							By(
								equation,
								numerals.At(n),
								coefficients.At(n),
								ring_homomorphism.RingMapNumeral.Read(hom).At(n),
								ring_homomorphism.MapMul.Read(hom).AsFact().At(
									arg.TermAs[A]("«numeral»(n)"), a.Apply(n))))
					})),
			))
	}),
})}

// RecurrenceUnit — the unit series has the zero sequence as its counting
// sequence: the Euler derivative of the unit vanishes, the numeral being zero
// at 0 and the unit zero off 0, and so does its product with the zero series.
var RecurrenceUnit = recurrenceUnitThm{family.Add(registry.ProofEntry{
	Name: "RecurrenceUnit",
	Key:  "prop_83264d14f6c3410d",
	Build: family.Theorem(Statement{
		Binders:    "∀R:comm_ring_on(A).",
		Conclusion: "series_recurrence(R, basis_vector(0), λn:num. R.zero)",
	}, func(arg *Argument, ring comm_ring.CommRingFact[on.R]) {
		zero, origin := arg.TermAs[A]("R.zero"), arg.TermAs[Nat]("0")
		one := arg.MemberOf[on.R](arg.TermAs[A]("R.one"), comm_ring.OneIn.Read(ring))
		equation := arg.Have(
			"the Euler derivative of the unit and its product with the zero series agree",
			"∀n:num. «numeral»(n) * basis_vector(0, n) = polynomial_mul(λj:num. R.zero, basis_vector(0), n)",
			Derive(func(arg *Argument) {
				n := arg.FixAs[Nat]("n")
				arg.Show(
					"the numeral is zero at 0, the unit is zero off 0, "+
						"and the product by the unit keeps the zero series",
					By(
						comm_ring.ZeroIn.Read(ring),
						polynomial.PolynomialMulBasisVector.Read(ring).At(
							arg.TermAs[Fun[Nat, A]]("λj:num. R.zero"), origin, n),
						comm_monoid.MonoidPowDef,
						vec_space.BasisVectorDef.At(zero, one, origin, n),
						comm_monoid.PowIn.Read(comm_ring.AddMonoidOn.Read(ring)).At(one, n),
						comm_ring.MulLeftZeroOn.Read(ring),
						comm_ring.MulRightZeroOn.Read(ring)))
			}))
		arg.Show(
			"the initial values and the coefficients are read off the unit",
			Simp(Fwd(RecurrenceEuler)),
			By(
				Normalized,
				equation,
				vec_space.BasisVectorDef,
				comm_ring.ZeroIn.Read(ring),
				polynomial.BasisVectorOver.Read(ring).At(origin),
				polynomial.PolynomialOverDef))
	}),
})}

// RecurrencePower — the r-th power multiplies the counting sequence by r, by
// induction on r: the empty power is the unit series, whose counting sequence
// is zero, and that is the zero multiple of m; and each further factor adds m,
// by RecurrenceProduct, the numeral r + 1 being one more than r.
var RecurrencePower = recurrencePowerThm{family.Add(registry.ProofEntry{
	Name: "RecurrencePower",
	Key:  "prop_3680c9832f435ee5",
	Build: family.Theorem(Statement{
		Binders:    "∀R:comm_ring_on(A). ∀a m:(num → A). ∀r:num.",
		Hypotheses: []string{"series_recurrence(R, a, m)"},
		Conclusion: "series_recurrence(R, polynomial_pow(a, r), λn:num. «numeral»(r) * m(n))",
	}, func(
		arg *Argument,
		ring comm_ring.CommRingFact[on.R],
		a, m *Arrow[Nat, A],
		r *Expr[Nat],
		recurrence Fact,
	) {
		counts := arg.Have(
			"every term of the counting sequence lies in the ring",
			"∀n:num. m(n) ∈ R.carrier",
			By(arg.Unfolded(recurrence, SeriesRecurrenceDef)))
		zeroCounts := arg.Have(
			"the zero multiple of each count is zero",
			"∀n:num. R.zero * m(n) = R.zero",
			By(counts, comm_ring.MulLeftZeroOn.Read(ring)))
		arg.Induct(r)
		arg.Base(
			"the empty power is the unit series, and the zero multiple of m is the zero sequence",
			Simp(Fwd(polynomial.PolynomialPowZero.Read(ring)), Fwd(comm_monoid.MonoidPowDef), Fwd(zeroCounts)),
			By(ring, RecurrenceUnit))
		arg.Step(
			"one more factor of a adds m to the counting sequence",
			func(arg *Argument, previous Fact) {
				next := arg.Have(
					"the numeral r + 1 is one more than r, and the ring distributes it over m(n)",
					"∀n:num. «numeral»(suc(r)) * m(n) = m(n) + «numeral»(r) * m(n)",
					arg.ForEach(func(n *Expr[Nat]) Action {
						return Chain(Simp(Fwd(comm_monoid.MonoidPowDef)), ByArith(ring, counts.At(n)))
					}))
				arg.Show(
					"the next power is a times the last one, and the product adds their counting sequences",
					Simp(Fwd(polynomial.PolynomialPowSuc.Read(ring)), Fwd(next)),
					By(ring, recurrence, previous, RecurrenceProduct))
			})
	}),
})}
