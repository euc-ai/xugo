// growth.go — moduli and power sums of a finite spectrum: an eventually bounded sum
// of exponentials has its bases in the unit disk, a common power absorbs the
// root-of-unity collisions, the bound carries over to radius c along a progression,
// a bound on the moduli bounds the power sums, and factors whose product reaches
// the bound all attain it.

package finite_spectrum

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_abs"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	"github.com/euc-ai/xugo/library/proofs/iterate/nat/nat_sum"
	"github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_divides"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/real/real_archimedean"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_pow"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// BoundedScaledPowers — an eventually bounded nonzero scalar multiple of
// complex powers has base of modulus at most one: Bernoulli's inequality
// contradicts the bound when the modulus exceeds one.
var BoundedScaledPowers = boundedScaledPowersThm{family.Add(registry.ProofEntry{
	Name: "BoundedScaledPowers",
	Key:  "prop_898ad78dad48b7a3",
	Build: family.Theorem(Statement{
		Binders: "∀z c:complex.",
		Hypotheses: []string{
			"c ≠ &0",
			"∃B:real. ∃N:num. ∀n:num. N ≤ n ⇒ |c * z ^ n| ≤ B",
		},
		Conclusion: "|z| ≤ &1",
	}, func(arg *Argument, z, c *Expr[Complex], nonzero, bounded Fact) {
		B, N, bound := arg.Unpack2As[Real, Nat](bounded, "B", "N")
		denied := arg.SupposeNot()
		signs := arg.Have(
			"the scalar modulus and the excess of the base modulus are positive",
			"&0 < |c| ∧ &1 < |z|",
			ByArith(nonzero, denied, complex_abs.AbsNonneg.At(c), complex_abs.AbsEqZero.At(c)))
		m, large := arg.ObtainAs[Nat](
			"choose a linear growth term beyond the bound",
			"∃m:num. B < &m * (|c| * (|z| - &1))",
			ByArith(signs, real_archimedean.Archimedean.At(arg.TermAs[Real]("|c| * (|z| - &1)"), B)))
		bernoulli := arg.Have(
			"Bernoulli gives a linear lower bound on a power in the tail",
			"&1 + &(m + N) * (|z| - &1) ≤ |z| ^ (m + N)",
			ByArith(
				signs,
				real_pow.Bernoulli.At(arg.TermAs[Real]("|z| - &1"), arg.TermAs[Nat]("m + N")),
				real_ring.SubAddLeft.At(arg.TermAs[Real]("|z|"), arg.TermAs[Real]("&1"))))
		upper := arg.Have(
			"multiplicativity of the modulus transfers the tail bound to real powers",
			"|c| * |z| ^ (m + N) ≤ B",
			ByArith(
				nat_order.LessEqAddLeft.At(m, N),
				bound.At(arg.TermAs[Nat]("m + N")),
				complex_abs.AbsMul.At(c, arg.TermAs[Complex]("z ^ (m + N)")),
				complex_abs.AbsPow.At(z, arg.TermAs[Nat]("m + N"))))
		lower := arg.Have(
			"the positive scalar modulus scales Bernoulli's lower bound",
			"|c| * (&1 + &(m + N) * (|z| - &1)) ≤ |c| * |z| ^ (m + N)",
			ByArith(
				bernoulli,
				signs,
				real_order_ring.LessEqMulLeft.At(
					arg.TermAs[Real]("|c|"),
					arg.TermAs[Real]("&1 + &(m + N) * (|z| - &1)"),
					arg.TermAs[Real]("|z| ^ (m + N)"))))
		exceeds := arg.Have(
			"the linear lower bound already exceeds the proposed uniform bound",
			"B < |c| * (&1 + &(m + N) * (|z| - &1))",
			ByArith(
				large,
				signs,
				nat_order.LessEqAdd.At(m, N),
				real_order_ring.LessEqMulLeft.At(
					arg.TermAs[Real]("|c| * (|z| - &1)"), arg.TermAs[Real]("&m"), arg.TermAs[Real]("&(m + N)"))))
		arg.Show(
			"the lower and upper bounds are incompatible",
			ByArith(lower, upper, exceeds))
	}),
})}

// FiniteExponentialSumDifference — subtracting a(j) times an exponential
// sum from its shift removes the j term and multiplies every other
// coefficient by a(i)-a(j).
var FiniteExponentialSumDifference = finiteExponentialSumDifferenceThm{family.Add(registry.ProofEntry{
	Name: "FiniteExponentialSumDifference",
	Key:  "prop_d2394b9612d2e8eb",
	Build: family.Theorem(Statement{
		Binders:    "∀a c:(A → complex). ∀T:set(A). ∀j:A. ∀n:num.",
		Hypotheses: []string{"finite(T)", "j ∈ T"},
		Conclusion: "«exponentialSum»(delete(T, j), λi:A. c(i) * (a(i) - a(j)), n) = " +
			"«exponentialSum»(T, c, n + 1) - a(j) * «exponentialSum»(T, c, n)",
		Abbrev: Abbrev{
			{Name: "exponentialSum", Text: "λE:set(A). λd:(A → complex). λn:num. " +
				"    module_sum(complex_add, complex_of_real(&0), E, λi:A. d(i) * a(i) ^ n)"},
			{Name: "shiftTerm", Text: "λm:num. λi:A. c(i) * a(i) ^ (m + 1) + -(a(j) * (c(i) * a(i) ^ m))"},
		},
	}, func(
		arg *Argument,
		a, c *Arrow[A, Complex],
		T *Expr[Set[A]],
		j *Expr[A],
		n *Expr[Nat],
		finite, member Fact,
	) {
		regular := module.RegularModuleOn.Read(complex_field.CommRingOn)
		_, weightDef := arg.LetAs[Fun[A, Complex]]("w", "λi:A. c(i) * (a(i) - a(j))")
		pointwise := arg.Have(
			"the coefficient difference equals the shifted term minus its scalar multiple",
			"∀i:A. w(i) * a(i) ^ n = «shiftTerm»(n, i)",
			Derive(func(b *Argument) {
				b.FixAs[A]("i")
				b.Show(
					"expand the successor power and distribute the difference",
					weightDef.Rw(),
					Simp(
						Fwd(comm_monoid.PowAdd.Read(complex_field.MulMonoid)),
						Fwd(comm_monoid.PowOne.Read(complex_field.MulMonoid))),
					ByArith(complex_field.CommRing))
			}))
		summed := arg.Have(
			"the same difference identity holds after summing over the finite set",
			"«exponentialSum»(T, w, n) = «exponentialSum»(T, c, n + 1) - a(j) * «exponentialSum»(T, c, n)",
			CalcEq(
				Leg(
					arg.TermAs[Complex]("module_sum(complex_add, complex_of_real(&0), T, «shiftTerm»(n))"),
					"sum the pointwise identity",
					By(pointwise, module.ModuleSumCongruence)),
				FinalLeg(
					"distribute the sum over addition, negation, and scalar multiplication",
					Simp(Fwd(complex_field.ComplexSubDef)),
					BySets(
						finite,
						module.ModuleSumAdd.Read(regular).At(
							T,
							arg.TermAs[Fun[A, Complex]]("λi:A. c(i) * a(i) ^ (n + 1)"),
							arg.TermAs[Fun[A, Complex]]("λi:A. -(a(j) * (c(i) * a(i) ^ n))")),
						module.ModuleSumNeg.Read(regular).At(
							T, arg.TermAs[Fun[A, Complex]]("λi:A. a(j) * (c(i) * a(i) ^ n)")),
						module.ModuleSumSmul.Read(regular).AsFact().At(
							T, a.Apply(j), arg.TermAs[Fun[A, Complex]]("λi:A. c(i) * a(i) ^ n"))))))
		vanishes := arg.Have(
			"the selected coefficient becomes zero",
			"w(j) = &0",
			weightDef.Rw(),
			ByArith(complex_field.CommRing))
		deleted := arg.Have(
			"deleting the zero summand does not change the sum",
			"«exponentialSum»(delete(T, j), w, n) = «exponentialSum»(T, w, n)",
			BySets(
				finite,
				vanishes,
				member,
				module.ModuleSumDelete.Read(regular).At(T, j, arg.TermAs[Fun[A, Complex]]("λi:A. w(i) * a(i) ^ n")),
				comm_ring.MulLeftZero.Read(complex_field.CommRing),
				comm_monoid.LeftIdentity.Read(comm_ring.AddMonoid.Read(complex_field.CommRing))))
		arg.Show(
			"the sum on the deletion is the difference of the original sum and its shift",
			By(summed, deleted))
	}),
})}

// BoundedFiniteExponentialSumGrowth — an eventually bounded finite sum of
// exponentials with distinct bases and nonzero coefficients has every base
// in the closed unit disk: a shift difference removes one other base.
var BoundedFiniteExponentialSumGrowth = boundedFiniteExponentialSumGrowthThm{family.Add(registry.ProofEntry{
	Name: "BoundedFiniteExponentialSumGrowth",
	Key:  "prop_e90294609f0cd159",
	Build: family.Sections(Statement{
		Binders: "∀a c:(A → complex). ∀T:set(A). ∀k:A.",
		Hypotheses: []string{
			"finite(T)",
			"∀i:A. i ∈ T ⇒ c(i) ≠ &0",
			"injective_on(T, a)",
			"∃B:real. ∃N:num. ∀n:num. N ≤ n ⇒ |«exponentialSum»(T, c, n)| ≤ B",
			"k ∈ T",
		},
		Conclusion: "|a(k)| ≤ &1",
		Abbrev: Abbrev{
			{Name: "exponentialSum", Text: "λE:set(A). λd:(A → complex). λn:num. " +
				"    module_sum(complex_add, complex_of_real(&0), E, λi:A. d(i) * a(i) ^ n)"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		deletion := ctx.Lemma(Statement{
			Binders: "∀a d:(A → complex). ∀U:set(A). ∀j k:A.",
			Hypotheses: []string{
				"finite(U)",
				"∀i:A. i ∈ U ⇒ d(i) ≠ &0",
				"injective_on(U, a)",
				"∃B:real. ∃N:num. ∀n:num. N ≤ n ⇒ |«exponentialSum»(U, d, n)| ≤ B",
				"k ∈ U",
				"j ∈ U",
				"j ≠ k",
			},
			Conclusion: "(∀i:A. i ∈ delete(U, j) ⇒ d(i) * (a(i) - a(j)) ≠ &0) ∧ " +
				"injective_on(delete(U, j), a) ∧ " +
				"(∃B:real. ∃N:num. ∀n:num. " +
				"    N ≤ n ⇒ |«exponentialSum»(delete(U, j), λi:A. d(i) * (a(i) - a(j)), n)| ≤ B) ∧ " +
				"k ∈ delete(U, j)",
		}, func(
			arg *Argument,
			a, d *Arrow[A, Complex],
			U *Expr[Set[A]],
			j, k *Expr[A],
			finite, coefficients, injective, bounded, member, selected, distinct Fact,
		) {
			retained := arg.Have(
				"all coefficients on the deletion remain nonzero",
				"∀i:A. i ∈ delete(U, j) ⇒ d(i) * (a(i) - a(j)) ≠ &0",
				Derive(func(r *Argument) {
					i := r.FixAs[A]("i")
					inDeletion := r.Assume()
					factors := r.Have(
						"the original coefficient is nonzero and the two bases are distinct",
						"d(i) ≠ &0 ∧ a(i) ≠ a(j)",
						BySets(coefficients.At(i), injective, inDeletion, selected, functions.InjectiveOnDef.At(U, a)))
					r.Show(
						"neither factor of the new coefficient can vanish",
						ByArith(
							factors,
							field.MulEqZero.Read(complex_field.Field).At(
								r.TermAs[Complex]("d(i)"), r.TermAs[Complex]("a(i) - a(j)")),
							complex_field.CommRing))
				}))
			restriction := arg.Have(
				"the restricted base map is injective and still contains the distinguished index",
				"injective_on(delete(U, j), a) ∧ k ∈ delete(U, j)",
				BySets(injective, member, distinct, functions.InjectiveOnSubset))
			_, N, bound := arg.Unpack2As[Real, Nat](bounded, "B", "N")
			newBound := arg.Have(
				"a fixed difference of two bounded shifts is eventually bounded",
				"∃D:real. ∃L:num. ∀n:num. "+
					"    L ≤ n ⇒ |«exponentialSum»(delete(U, j), λi:A. d(i) * (a(i) - a(j)), n)| ≤ D",
				Derive(func(r *Argument) {
					r.Take(r.TermAs[Real]("B + |a(j)| * B"))
					r.Take(N)
					n := r.FixAs[Nat]("n")
					tail := r.Assume()
					bothBounded := r.Have(
						"both shifted indices lie in the tail, where the sum is bounded",
						"|«exponentialSum»(U, d, n)| ≤ B ∧ |«exponentialSum»(U, d, n + 1)| ≤ B",
						ByArith(tail, bound.At(n), bound.At(r.TermAs[Nat]("n + 1"))))
					shift := r.Have(
						"the eliminated sum is the original shift minus its scalar multiple",
						"«exponentialSum»(delete(U, j), λi:A. d(i) * (a(i) - a(j)), n) = "+
							"«exponentialSum»(U, d, n + 1) - a(j) * «exponentialSum»(U, d, n)",
						By(finite, selected, FiniteExponentialSumDifference.At(a, d, U, j, n)))
					r.Show(
						"the triangle inequality gives the inherited uniform bound",
						shift.Rw(),
						Simp(Fwd(complex_field.ComplexSubDef)),
						ByArith(
							bothBounded,
							complex_abs.AbsTriangle.At(
								r.TermAs[Complex]("«exponentialSum»(U, d, n + 1)"),
								r.TermAs[Complex]("-(a(j) * «exponentialSum»(U, d, n))")),
							complex_abs.AbsNeg.At(r.TermAs[Complex]("a(j) * «exponentialSum»(U, d, n)")),
							complex_abs.AbsMul.At(a.Apply(j), r.TermAs[Complex]("«exponentialSum»(U, d, n)")),
							complex_abs.AbsNonneg.At(a.Apply(j))))
				}))
			arg.Show(
				"the coefficients, the bases and the bound all survive the deletion",
				By(retained, restriction, newBound))
		})
		singleton := ctx.Lemma(Statement{
			Binders: "∀a d:(A → complex). ∀U:set(A). ∀k:A.",
			Hypotheses: []string{
				"finite(U)",
				"∀i:A. i ∈ U ⇒ d(i) ≠ &0",
				"∃B:real. ∃N:num. ∀n:num. N ≤ n ⇒ |«exponentialSum»(U, d, n)| ≤ B",
				"k ∈ U",
				"∀j:A. j ∈ U ⇒ j = k",
			},
			Conclusion: "|a(k)| ≤ &1",
		}, func(
			arg *Argument,
			a, d *Arrow[A, Complex],
			U *Expr[Set[A]],
			k *Expr[A],
			finite, coefficients, bounded, member, only Fact,
		) {
			regular := module.RegularModuleOn.Read(complex_field.CommRingOn)
			single := arg.Have(
				"the only possible summand is the distinguished exponential",
				"∀n:num. «exponentialSum»(U, d, n) = d(k) * a(k) ^ n",
				Derive(func(r *Argument) {
					r.FixAs[Nat]("n")
					r.Show(
						"all other summands are absent",
						BySets(
							finite,
							member,
							only,
							module.ModuleSumSingle.Read(regular).At(U, k, r.TermAs[Fun[A, Complex]]("λi:A. d(i) * a(i) ^ n"))))
				}))
			arg.Show(
				"the scalar bounded-power theorem applies",
				By(
					coefficients.At(k),
					member,
					single,
					bounded,
					BoundedScaledPowers.At(a.Apply(k), arg.TermAs[Complex]("d(k)"))))
		})
		return ctx.Theorem(headline, func(
			arg *Argument,
			a, c *Arrow[A, Complex],
			T *Expr[Set[A]],
			k *Expr[A],
			finite, coefficients, injective, bounded, member Fact,
		) {
			allCoefficients := arg.Have(
				"prove the claim for every coefficient family so that deletion may change it",
				Statement{
					Binders: "∀d:(A → complex).",
					Hypotheses: []string{
						"∀i:A. i ∈ T ⇒ d(i) ≠ &0",
						"injective_on(T, a)",
						"∃B:real. ∃N:num. ∀n:num. N ≤ n ⇒ |«exponentialSum»(T, d, n)| ≤ B",
						"k ∈ T",
					},
					Conclusion: "|a(k)| ≤ &1",
				},
				ByInduction(finite_set.FiniteInductDelete, finite,
					Case(
						"the distinguished index cannot belong to the empty set",
						BySets()),
					Case(
						"remove another index or reduce to a single exponential",
						Derive(func(b *Argument) {
							U := b.FixAs[Set[A]]("U")
							finiteNonempty := b.Assume()
							b.Cases(b.Term("∃j:A. j ∈ U ∧ j ≠ k"))
							b.When(
								"another base can be eliminated by a shift difference",
								func(branch *Argument, another Fact) {
									j, selected := branch.UnpackAs[A](another, "j")
									branch.Take(j)
									branch.Show(
										"delete the selected index and invoke the claim for the changed coefficients",
										SplitConj(
											Case(
												"the selected index belongs to the set",
												By(selected)),
											Case(
												"the claim on the deletion controls the original distinguished base",
												Derive(func(q *Argument) {
													ih := q.Assume()
													d := q.FixAs[Fun[A, Complex]]("d")
													data := q.Assume()
													q.Show(
														"apply the deletion hypothesis to the transformed coefficients",
														By(
															data,
															selected,
															finiteNonempty,
															At(deletion, a, d, U, j, k),
															ih.At(q.TermAs[Fun[A, Complex]]("λi:A. d(i) * (a(i) - a(j))"))))
												}))))
								})
							b.Otherwise(
								"there is only the distinguished base",
								func(branch *Argument, noOther Fact) {
									branch.Take(k)
									branch.Show(
										"the distinguished index is the only one, so no deletion is needed",
										SplitConj(
											Case(
												"nonemptiness forces the distinguished index to belong",
												BySets(noOther, finiteNonempty)),
											Case(
												"a bounded singleton exponential has base in the unit disk",
												Derive(func(q *Argument) {
													q.Assume()
													d := q.FixAs[Fun[A, Complex]]("d")
													data := q.Assume()
													q.Show(
														"apply the single-index section to this coefficient family",
														By(data, noOther, finiteNonempty, At(singleton, a, d, U, k)))
												}))))
								})
						}))))
			arg.Show(
				"specialize the coefficient family in the finite-set claim",
				By(coefficients, allCoefficients.At(c), bounded, injective, member))
		})
	}),
})}

// BoundedExponentialSumGrowth — eventual boundedness of a finite sum of
// exponentials with distinct bases and nonzero coefficients forces every
// base into the closed unit disk: apply the finite-set growth theorem.
var BoundedExponentialSumGrowth = boundedExponentialSumGrowthThm{family.Add(registry.ProofEntry{
	Name: "BoundedExponentialSumGrowth",
	Key:  "prop_10c335ab347e4f2b",
	Build: family.Theorem(Statement{
		Binders: "∀s:num. ∀a c:(num → complex). ∀k:num.",
		Hypotheses: []string{
			"∀i:num. i < s ⇒ c(i) ≠ &0",
			"∀i j:num. i < s ∧ j < s ∧ a(i) = a(j) ⇒ i = j",
			"∃B:real. ∃N:num. ∀n:num. " +
				"    N ≤ n ⇒ " +
				"    |module_sum(complex_add, complex_of_real(&0), {i:num | i < s}, λi:num. c(i) * a(i) ^ n)| ≤ B",
			"k < s",
		},
		Conclusion: "|a(k)| ≤ &1",
	}, func(arg *Argument, s *Expr[Nat], a, c *Arrow[Nat, Complex], k *Expr[Nat], hypotheses Fact) {
		arg.Show(
			"the bounded index segment is a finite set with the stated distinct bases",
			BySets(
				hypotheses,
				BoundedFiniteExponentialSumGrowth.At(a, c, arg.TermAs[Set[Nat]]("{i:num | i < s}"), k),
				num_segment.FiniteBelowStrict.At(s),
				functions.InjectiveOnDef.At(arg.TermAs[Set[Nat]]("{i:num | i < s}"), a)))
	}),
})}

// RootOfUnityRatiosKilledByPower — a positive multiple R of the prescribed
// exponent makes every collision at a positive exponent already occur at R:
// take a common multiple of one collision exponent for each pair. A collision
// of a(i) and a(j) at m is a(i)^m = a(j)^m, that is, when both are nonzero,
// a(i)/a(j) is a root of unity; R kills every such ratio, as the name says.
var RootOfUnityRatiosKilledByPower = rootOfUnityRatiosKilledByPowerThm{family.Add(registry.ProofEntry{
	Name: "RootOfUnityRatiosKilledByPower",
	Key:  "prop_32086c26221fb071",
	Build: family.Theorem(Statement{
		Binders:    "∀s R₀:num. ∀a:(num → complex).",
		Hypotheses: []string{"0 < R₀"},
		Conclusion: "∃R:num. " +
			"    0 < R ∧ " +
			"    R₀ ∣ R ∧ " +
			"    (∀m i j:num. 0 < m ∧ i < s ∧ j < s ∧ a(i) ^ m = a(j) ^ m ⇒ a(i) ^ R = a(j) ^ R)",
	}, func(arg *Argument, s, R0 *Expr[Nat], a *Arrow[Nat, Complex], positive Fact) {
		pointwise := arg.Have(
			"every pair with a positive power collision has an exponent witnessing it",
			"∀i j:num. ∃n:num. (∃m:num. 0 < m ∧ a(i) ^ m = a(j) ^ m) ⇒ 0 < n ∧ a(i) ^ n = a(j) ^ n",
			BySets())
		f, chosen := arg.ObtainAs[Fun2[Nat, Nat, Nat]](
			"choose a collision exponent simultaneously for every pair",
			"∃f:(num → num → num). ∀i j:num. "+
				"    (∃m:num. 0 < m ∧ a(i) ^ m = a(j) ^ m) ⇒ 0 < f(i, j) ∧ a(i) ^ f(i, j) = a(j) ^ f(i, j)",
			By(pointwise))
		T, exponentSet := arg.LetAs[Set[Nat]]("T", "{f(i, j) | i:num, j:num | i < s ∧ j < s}")
		finite := arg.Have(
			"the finitely many index pairs give finitely many selected exponents",
			"finite(T)",
			By(
				exponentSet,
				num_segment.FiniteBelowStrict.At(s),
				finite_set.FiniteProductDependent.At(
					f,
					arg.TermAs[Set[Nat]]("{i:num | i < s}"),
					arg.TermAs[Fun2[Nat, Nat, Bool]]("λi:num. {j:num | j < s}"))))
		M, multiple := arg.ObtainAs[Nat](
			"take a positive common multiple of the prescribed exponent and the selected exponents",
			"∃M:num. 0 < M ∧ (∀n:num. n ∈ insert(R₀, T) ∧ 0 < n ⇒ n ∣ M)",
			By(
				finite,
				finite_set.FiniteInsert.At(R0, T),
				nat_sum.FinitePositiveCommonMultiple.At(arg.TermAs[Set[Nat]]("insert(R₀, T)"))))
		parts := arg.Conjuncts(
			multiple,
			"the common multiple is positive",
			"every positive member of the enlarged set divides it")
		positiveMultiple, divides := parts[0], parts[1]
		arg.Take(M)
		arg.Show(
			"this common multiple has the prescribed divisibility and stabilizes every collision",
			SplitConj(
				Case(
					"the common multiple is positive and divisible by the prescribed exponent",
					BySets(positiveMultiple, positive, divides.At(R0))),
				Case(
					"a collision at any positive exponent already occurs at the common multiple",
					Derive(func(b *Argument) {
						m := b.FixAs[Nat]("m")
						i := b.FixAs[Nat]("i")
						j := b.FixAs[Nat]("j")
						given := b.Assume()
						eligible := b.Have(
							"the given collision is a positive collision for this pair",
							"∃m:num. 0 < m ∧ a(i) ^ m = a(j) ^ m",
							Witness(m),
							By(given))
						selected := b.Have(
							"the selected exponent is positive and gives the same collision",
							"0 < f(i, j) ∧ a(i) ^ f(i, j) = a(j) ^ f(i, j)",
							By(chosen.At(i, j), eligible))
						q, cofactor := b.ObtainAs[Nat](
							"the selected exponent divides the common multiple",
							"∃q:num. M = f(i, j) * q",
							BySets(
								exponentSet,
								divides.At(b.TermAs[Nat]("f(i, j)")),
								selected,
								given,
								nat_divides.DividesFactor.At(b.TermAs[Nat]("f(i, j)"), M)))
						b.Show(
							"raise the selected collision to its cofactor",
							By(
								cofactor,
								selected,
								comm_monoid.PowPow.Read(complex_field.MulMonoid).At(a.Apply(i), b.TermAs[Nat]("f(i, j)"), q),
								comm_monoid.PowPow.Read(complex_field.MulMonoid).At(a.Apply(j), b.TermAs[Nat]("f(i, j)"), q)))
					}))))
	}),
})}

// BoundedProgressionPowerSums — bounded power sums along a progression
// force every base into the closed unit disk when equality of h-th powers
// identifies equal bases: group the repeated bases and apply exponential
// growth to their h-th powers. The exponent is 1 + h * n because
// a^(1 + h * n) = a * (a^h)^n is exponential in n with base a^h: grouped by
// value z, the leading 1 becomes the factor z in the coefficient c(z), the
// multiplicity times z. Exponential growth needs that coefficient nonzero,
// which is where a(i) ≠ 0 is read.
var BoundedProgressionPowerSums = boundedProgressionPowerSumsThm{family.Add(registry.ProofEntry{
	Name: "BoundedProgressionPowerSums",
	Key:  "prop_400dd6f8b21b72d9",
	Build: family.Theorem(Statement{
		Binders: "∀s h:num. ∀a:(num → complex). ∀k:num.",
		Hypotheses: []string{
			"0 < h",
			"∀i:num. i < s ⇒ a(i) ≠ &0",
			"∀i j:num. i < s ∧ j < s ∧ a(i) ^ h = a(j) ^ h ⇒ a(i) = a(j)",
			"∃B:real. ∃N:num. ∀n:num. N ≤ n ⇒ |finite_power_sum(s, a, 1 + h * n)| ≤ B",
			"k < s",
		},
		Conclusion: "|a(k)| ≤ &1",
		Abbrev: Abbrev{
			{Name: "groupedSummand", Text: "λz:complex. λn:num. c(z) * b(z) ^ n"},
		},
	}, func(
		arg *Argument,
		s, h *Expr[Nat],
		a *Arrow[Nat, Complex],
		k *Expr[Nat],
		positive, nonzero, collisions, bounded, member Fact,
	) {
		regular := module.RegularModuleOn.Read(complex_field.CommRingOn)
		S, indexDef := arg.LetAs[Set[Nat]]("S", "{i:num | i < s}")
		U, imageDef := arg.LetAs[Set[Complex]]("U", "image(a, S)")
		_, fibreDef := arg.LetAs[Fun[Complex, Set[Nat]]]("E", "λz:complex. {i:num | i ∈ S ∧ a(i) = z}")
		b, baseDef := arg.LetAs[Fun[Complex, Complex]]("b", "λz:complex. z ^ h")
		c, coefficientDef := arg.LetAs[Fun[Complex, Complex]]("c", "λz:complex. &card(E(z)) * z")
		finiteData := arg.Have(
			"the index set and its image are finite and contain the distinguished base",
			"finite(S) ∧ finite(U) ∧ a(k) ∈ U",
			BySets(
				Normalized,
				member,
				imageDef,
				indexDef,
				num_segment.FiniteBelowStrict.At(s),
				finite_set.FiniteImage.At(a, S)))
		fibres := arg.Have(
			"each image value has a finite nonempty fibre and is nonzero",
			"∀z:complex. z ∈ U ⇒ finite(E(z)) ∧ E(z) ≠ ∅ ∧ z ≠ &0",
			Derive(func(d *Argument) {
				d.FixAs[Complex]("z")
				inU := d.Assume()
				d.Show(
					"a representative gives nonemptiness and nonvanishing; the fibre lies in the finite segment",
					fibreDef.Rw(),
					imageDef.Rw(),
					indexDef.Rw(),
					BySets(
						nonzero,
						inU,
						finiteData,
						finite_set.FiniteSubset.At(
							d.TermAs[Set[Nat]]("{i:num | i ∈ {j:num | j < s} ∧ a(i) = z}"),
							d.TermAs[Set[Nat]]("{i:num | i < s}"))))
			}))
		coefficients := arg.Have(
			"every grouped coefficient is nonzero",
			"∀z:complex. z ∈ U ⇒ c(z) ≠ &0",
			Derive(func(d *Argument) {
				z := d.FixAs[Complex]("z")
				inU := d.Assume()
				count := d.Have(
					"a nonempty fibre has nonzero cardinality and nonzero value",
					"card(E(z)) ≠ 0 ∧ z ≠ &0",
					By(Normalized, inU, fibres.At(z), cardinality.CardEqZero.At(d.TermAs[Set[Nat]]("E(z)"))))
				d.Show(
					"a nonzero natural multiplicity times a nonzero complex value is nonzero",
					coefficientDef.Rw(),
					By(
						count,
						field.MulEqZero.Read(complex_field.Field).At(d.TermAs[Complex]("complex_of_real(&card(E(z)))"), z),
						complex_field.OfRealInjective.At(d.TermAs[Real]("&card(E(z))"), d.TermAs[Real]("&0")),
						real_construction.OfNumEq.At(d.TermAs[Nat]("card(E(z))"), d.TermAs[Nat]("0"))))
			}))
		injective := arg.Have(
			"the h-th powers of distinct image values are distinct",
			"injective_on(U, b)",
			Derive(func(d *Argument) {
				d.Do(baseDef.Rw(), imageDef.Rw(), indexDef.Rw(), Unfold(functions.InjectiveOnDef))
				d.FixAs[Complex]("x")
				d.FixAs[Complex]("y")
				paired := d.Assume()
				i, j, representatives := d.Obtain2As[Nat, Nat](
					"choose original indices representing the two image values",
					"∃i j:num. i < s ∧ j < s ∧ x = a(i) ∧ y = a(j)",
					BySets(paired))
				d.Show(
					"the power collision hypothesis identifies their representatives",
					By(paired, representatives, collisions.At(i, j)))
			}))
		grouped := arg.Have(
			"each progression sum is an exponential sum over the distinct image values",
			"∀n:num. "+
				"    finite_power_sum(s, a, 1 + h * n) = "+
				"    module_sum(complex_add, complex_of_real(&0), U, λz:complex. «groupedSummand»(z, n))",
			Derive(func(d *Argument) {
				d.FixAs[Nat]("n")
				F, summandDef := d.LetAs[Fun[Nat, Complex]]("F", "λi:num. a(i) * b(a(i)) ^ n")
				pointwise := d.Have(
					"split each progression power into its initial factor and an h-th power",
					"∀i:num. a(i) ^ (1 + h * n) = F(i)",
					Derive(func(e *Argument) {
						e.FixAs[Nat]("i")
						e.Show(
							"expand the exponent sum and the iterated power",
							summandDef.Rw(),
							baseDef.Rw(),
							Simp(
								Fwd(comm_monoid.PowAdd.Read(complex_field.MulMonoid)),
								Fwd(comm_monoid.PowOne.Read(complex_field.MulMonoid)),
								Fwd(comm_monoid.PowPow.Read(complex_field.MulMonoid))),
							Refl())
					}))
				fibreTerms := d.Have(
					"each fibre contributes its multiplicity times the common summand",
					Statement{
						Binders:    "∀z:complex.",
						Hypotheses: []string{"z ∈ U"},
						Conclusion: "module_sum(complex_add, complex_of_real(&0), E(z), F) = «groupedSummand»(z, n)",
					},
					Derive(func(e *Argument) {
						z := e.FixAs[Complex]("z")
						inU := e.Assume()
						constant := e.Have(
							"the summand is constant on this fibre",
							"module_sum(complex_add, complex_of_real(&0), E(z), F) = "+
								"module_sum(complex_add, complex_of_real(&0), E(z), λi:num. z * b(z) ^ n)",
							summandDef.Rw(),
							fibreDef.Rw(),
							BySets(module.ModuleSumCongruence))
						e.Show(
							"sum the constant and combine its multiplicity with the initial factor",
							coefficientDef.Rw(),
							ByArith(
								constant,
								inU,
								fibres.At(z),
								set_basic.InUniv,
								module.ModuleSumConstant.Read(regular).AsFact().At(
									e.TermAs[Set[Nat]]("E(z)"), e.TermAs[Complex]("z * b(z) ^ n")),
								complex_field.AddPowOne.At(e.TermAs[Nat]("card(E(z))")),
								complex_field.CommRing))
					}))
				d.Show(
					"group the finite index sum by its image values",
					Simp(Fwd(PowerSumDef)),
					indexDef.RwRev(),
					CalcEq(
						Leg(
							d.TermAs[Complex]("module_sum(complex_add, complex_of_real(&0), S, F)"),
							"replace the powers by their split forms",
							By(pointwise, module.ModuleSumCongruence)),
						Leg(
							d.TermAs[Complex](
								"module_sum(complex_add, "+
									"    complex_of_real(&0), "+
									"    U, "+
									"    λz:complex. module_sum(complex_add, complex_of_real(&0), E(z), F))"),
							"partition the indices into fibres",
							imageDef.Rw(),
							fibreDef.Rw(),
							By(finiteData, set_basic.InUniv, module.ModuleSumFibres.Read(regular).At(S, a, F))),
						FinalLeg(
							"replace each fibre sum by its grouped exponential term",
							By(fibreTerms, module.ModuleSumCongruence))))
			}))
		newBound := arg.Have(
			"the grouped exponential sums inherit the eventual bound",
			"∃B:real. ∃N:num. ∀n:num. "+
				"    N ≤ n ⇒ "+
				"    |module_sum(complex_add, complex_of_real(&0), U, λz:complex. «groupedSummand»(z, n))| ≤ B",
			By(bounded, grouped))
		powered := arg.Have(
			"the distinguished h-th power lies in the closed unit disk",
			"|b(a(k))| ≤ &1",
			By(
				coefficients,
				newBound,
				injective,
				finiteData,
				BoundedFiniteExponentialSumGrowth.At(b, c, U, a.Apply(k))))
		arg.Show(
			"a positive power can have modulus at most one only when its base does",
			baseDef.Rw(),
			ByArith(
				positive,
				powered,
				complex_abs.AbsPow.At(a.Apply(k), h),
				complex_abs.AbsNonneg.At(a.Apply(k)),
				real_pow.OnePow.At(h),
				real_pow.PowMonoBaseStrict.At(arg.TermAs[Real]("&1"), arg.TermAs[Real]("|a(k)|"), h),
				nat_order.PosIffNonzero.At(h)))
	}),
})}

// PowerSumModulusBound — s numbers of modulus at most c have power sums of
// modulus at most s times the same power of c: the triangle inequality over s
// terms, each bounded by c^m since the modulus of a power is the power of the
// modulus.
var PowerSumModulusBound = powerSumModulusBoundThm{family.Add(registry.ProofEntry{
	Name: "PowerSumModulusBound",
	Key:  "prop_267dbb2c01ed49e8",
	Build: family.Theorem(Statement{
		Binders: "∀s m:num. ∀a:(num → complex). ∀c:real.",
		Hypotheses: []string{
			"∀i:num. i < s ⇒ |a(i)| ≤ c",
		},
		Conclusion: "|finite_power_sum(s, a, m)| ≤ &s * c ^ m",
	}, func(arg *Argument, s, m *Expr[Nat], a *Arrow[Nat, Complex], c *Expr[Real], bounded Fact) {
		below := arg.TermAs[Set[Nat]]("{i:num | i < s}")
		dominated := arg.Have(
			"each power has modulus at most c^m",
			"∀i:num. i < s ⇒ |a(i) ^ m| ≤ c ^ m",
			Derive(func(term *Argument) {
				i := term.FixAs[Nat]("i")
				root := a.Apply(i)
				term.Show(
					"its modulus is the power of a modulus at most c",
					ByArith(
						bounded.At(i),
						complex_abs.AbsPow.At(root, m),
						complex_abs.AbsNonneg.At(root),
						real_pow.PowMonoBase.At(term.TermAs[Real]("|a(i)|"), c, m)))
			}))
		arg.Show(
			"so the triangle inequality bounds the sum by s terms c^m",
			Simp(Fwd(PowerSumDef)),
			By(
				dominated,
				num_segment.FiniteBelowStrict.At(s),
				complex_abs.AbsSumDominated.At(
					below,
					arg.TermAs[Fun[Nat, Complex]]("λi:num. a(i) ^ m"),
					arg.TermAs[Fun[Nat, Real]]("λi:num. c ^ m")),
				real_sum.ConstBelow.At(s, arg.TermAs[Real]("c ^ m"))))
	}),
})}

// ScaledProgressionModulusBound — BoundedProgressionPowerSums at radius c and
// exponent step R: for nonzero bases, power sums along the multiples R(1 + hn) that
// grow no faster than c to those exponents put every base in the closed disk of
// radius c, when a collision of the R·h-th powers is already one of the R-th
// powers. Dividing the R-th powers by c^R gives a normalized spectrum b whose power
// sums along the progression are bounded, so the unit-disk theorem applies to b; a
// modulus past c would then make the R-th power of the modulus exceed c^R.
var ScaledProgressionModulusBound = scaledProgressionModulusBoundThm{family.Add(registry.ProofEntry{
	Name: "ScaledProgressionModulusBound",
	Key:  "prop_ce8eaabf78f987fc",
	Build: family.Theorem(Statement{
		Binders: "∀s R h:num. ∀c:real. ∀a:(num → complex). ∀k:num.",
		Hypotheses: []string{
			"0 < R",
			"0 < h",
			"&0 < c",
			"∀i:num. i < s ⇒ a(i) ≠ &0",
			"∀i j:num. i < s ∧ j < s ∧ a(i) ^ (R * h) = a(j) ^ (R * h) ⇒ a(i) ^ R = a(j) ^ R",
			"∃B:real. ∃N:num. ∀n:num. " +
				"    N ≤ n ⇒ |finite_power_sum(s, a, R * (1 + h * n))| ≤ B * c ^ (R * (1 + h * n))",
			"k < s",
		},
		Conclusion: "|a(k)| ≤ c",
	}, func(
		arg *Argument,
		s, R, h *Expr[Nat],
		c *Expr[Real],
		a *Arrow[Nat, Complex],
		k *Expr[Nat],
		positiveR, positiveH, positiveC, nonzero, collisions, bounded, member Fact,
	) {
		regular := module.RegularModuleOn.Read(complex_field.CommRingOn)
		p, scaleDef := arg.LetAs[Complex]("p", "complex_of_real(c ^ R)")
		b, normalizedDef := arg.LetAs[Fun[Nat, Complex]]("b", "λi:num. a(i) ^ R / p")
		positiveScale := arg.Have(
			"the radius and so its power are positive",
			"&0 < c ^ R",
			By(positiveC, real_pow.PowPos.At(c, R)))
		modulus := arg.Have(
			"so p, the positive power read in ℂ, is its own modulus c^R",
			"|p| = c ^ R",
			scaleDef.Rw(),
			ByArith(positiveScale, complex_abs.AbsOfNonnegReal.At(arg.TermAs[Real]("c ^ R"))))
		scale := arg.Have(
			"p has modulus c^R and is not zero",
			"|p| = c ^ R ∧ p ≠ &0",
			ByArith(modulus, positiveScale, complex_abs.AbsEqZero.At(p)))
		factored := arg.Have(
			"each R-th power is p times its normalized value",
			"∀i:num. a(i) ^ R = p * b(i)",
			Derive(func(d *Argument) {
				d.FixAs[Nat]("i")
				d.Show(
					"p cancels against the quotient by p",
					normalizedDef.Rw(),
					By(scale, field.DivLeftMul.Read(complex_field.Field).At(d.TermAs[Complex]("a(i) ^ R"), p)))
			}))
		scaled := arg.Have(
			"so every power of a at a multiple of R is p^m times that power of b",
			"∀i m:num. a(i) ^ (R * m) = p ^ m * b(i) ^ m",
			Derive(func(d *Argument) {
				i := d.FixAs[Nat]("i")
				m := d.FixAs[Nat]("m")
				d.Show(
					"split the exponent, then the power of the product",
					By(
						factored.At(i),
						comm_monoid.PowPow.Read(complex_field.MulMonoid).At(a.Apply(i), R, m),
						comm_monoid.MulPow.Read(complex_field.MulMonoid).At(p, d.TermAs[Complex]("b(i)"), m)))
			}))
		moduli := arg.Have(
			"in moduli, the R-th power of a base is c^R times its normalized modulus",
			"∀i:num. |a(i)| ^ R = c ^ R * |b(i)|",
			Derive(func(d *Argument) {
				i := d.FixAs[Nat]("i")
				d.Show(
					"the modulus carries powers and products",
					By(
						factored.At(i),
						scale,
						complex_abs.AbsPow.At(a.Apply(i), R),
						complex_abs.AbsMul.At(p, d.TermAs[Complex]("b(i)"))))
			}))
		normalizedNonzero := arg.Have(
			"the normalized bases are nonzero",
			"∀i:num. i < s ⇒ b(i) ≠ &0",
			Derive(func(d *Argument) {
				i := d.FixAs[Nat]("i")
				inRange := d.Assume()
				size := d.TermAs[Real]("|a(i)|")
				d.Show(
					"a nonzero base has positive modulus, and c^R is positive, so the normalized modulus is too",
					Simp(Rev(complex_abs.AbsPosIffNonzero)),
					ByArith(
						inRange,
						moduli.At(i),
						nonzero.At(i),
						positiveScale,
						complex_abs.AbsPosIffNonzero.At(a.Apply(i)),
						real_pow.PowPos.At(size, R)))
			}))
		normalizedCollisions := arg.Have(
			"a collision of normalized bases at h is a collision of the bases at R·h, so already at R",
			"∀i j:num. i < s ∧ j < s ∧ b(i) ^ h = b(j) ^ h ⇒ b(i) = b(j)",
			Derive(func(d *Argument) {
				i := d.FixAs[Nat]("i")
				j := d.FixAs[Nat]("j")
				given := d.Assume()
				d.Show(
					"equal R-th powers have equal quotients by p",
					normalizedDef.Rw(),
					By(given, scaled.At(i, h), scaled.At(j, h), collisions.At(i, j)))
			}))
		sums := arg.Have(
			"so the power sums of a at multiples of R are p^m times those of b",
			"∀m:num. finite_power_sum(s, a, R * m) = p ^ m * finite_power_sum(s, b, m)",
			Derive(func(d *Argument) {
				d.FixAs[Nat]("m")
				d.Show(
					"replace each term, then take the common factor out of the sum",
					Simp(Fwd(PowerSumDef)),
					CalcEq(
						Leg(
							d.TermAs[Complex](
								"module_sum(complex_add, complex_of_real(&0), {i:num | i < s}, λi:num. p ^ m * b(i) ^ m)"),
							"each term is p^m times the term of b",
							By(scaled, module.ModuleSumCongruence)),
						FinalLeg(
							"p^m comes out of the finite sum",
							By(
								num_segment.FiniteBelowStrict.At(s),
								set_basic.InUniv,
								module.ModuleSumSmul.Read(regular).AsFact().At(
									d.TermAs[Set[Nat]]("{i:num | i < s}"),
									d.TermAs[Complex]("p ^ m"),
									d.TermAs[Fun[Nat, Complex]]("λi:num. b(i) ^ m"))))))
			}))
		sumModuli := arg.Have(
			"in moduli, the factor is c^(R·m)",
			"∀m:num. |finite_power_sum(s, a, R * m)| = c ^ (R * m) * |finite_power_sum(s, b, m)|",
			Derive(func(d *Argument) {
				m := d.FixAs[Nat]("m")
				d.Show(
					"the modulus carries the product and the power of p, and a power of c^R multiplies the exponents",
					By(
						sums.At(m),
						scale,
						complex_abs.AbsMul.At(d.TermAs[Complex]("p ^ m"), d.TermAs[Complex]("finite_power_sum(s, b, m)")),
						complex_abs.AbsPow.At(p, m),
						real_pow.PowPow.At(c, R, m)))
			}))
		normalizedBound := arg.Have(
			"so the normalized power sums are bounded along the progression",
			"∃B:real. ∃N:num. ∀n:num. N ≤ n ⇒ |finite_power_sum(s, b, 1 + h * n)| ≤ B",
			Derive(func(d *Argument) {
				B, N, tail := d.Unpack2As[Real, Nat](bounded, "B", "N")
				d.Take(B)
				d.Take(N)
				n := d.FixAs[Nat]("n")
				exponent := d.TermAs[Nat]("1 + h * n")
				d.Show(
					"the positive factor c^(R(1 + hn)) cancels from the given bound",
					ByArith(
						tail.At(n),
						sumModuli.At(exponent),
						positiveC,
						real_pow.PowPos.At(c, d.TermAs[Nat]("R * (1 + h * n)"))))
			}))
		unit := arg.Have(
			"the unit-disk theorem bounds the normalized base at k",
			"|b(k)| ≤ &1",
			By(
				positiveH,
				normalizedNonzero,
				normalizedCollisions,
				normalizedBound,
				member,
				BoundedProgressionPowerSums.At(s, h, b, k)))
		arg.Show(
			"a modulus past c would make |a(k)|^R exceed c^R, against |a(k)|^R = c^R |b(k)|",
			ByArith(
				unit,
				moduli.At(k),
				positiveC,
				positiveScale,
				positiveR,
				real_pow.PowMonoBaseStrict.At(c, arg.TermAs[Real]("|a(k)|"), R),
				nat_order.PosIffNonzero.At(R)))
	}),
})}

// ProductModulusAtBound — factors bounded by c > 0 whose product has modulus c^s
// all have modulus c. Induction proves two things together: the product's modulus
// is at most c^s, and attaining c^s forces every factor to c. At suc(s) the modulus
// is |a(s)| times the modulus below, each at most its bound with c and c^s positive,
// so equality in the product forces equality in each.
var ProductModulusAtBound = productModulusAtBoundThm{family.Add(registry.ProofEntry{
	Name: "ProductModulusAtBound",
	Key:  "prop_dd814aca9fb342ec",
	Build: family.Sections(Statement{
		Binders: "∀s:num. ∀a:(num → complex). ∀c:real. ∀k:num.",
		Hypotheses: []string{
			"&0 < c",
			"∀i:num. i < s ⇒ |a(i)| ≤ c",
			"|«product»(s, a)| = c ^ s",
			"k < s",
		},
		Conclusion: "|a(k)| = c",
		Abbrev: Abbrev{
			{Name: "product", Text: "λs:num. λa:(num → complex). product({i:num | i < s}, a)"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		clauses := ctx.Lemma(
			"∀a:(num → complex). ∀s:num. "+
				"    «product»(0, a) = complex_of_real(&1) ∧ «product»(suc(s), a) = a(s) * «product»(s, a)",
			func(arg *Argument, a *Arrow[Nat, Complex], s *Expr[Nat]) {
				monoid := comm_ring.MulMonoidOn.Read(complex_field.CommRingOn)
				below := arg.TermAs[Set[Nat]]("{i:num | i < s}")
				fold := arg.Have(
					"below a bound the product is the module chapter's fold",
					"∀t:num. module_sum(complex_mul, complex_of_real(&1), {i:num | i < t}, a) = «product»(t, a)",
					Derive(func(b *Argument) {
						t := b.FixAs[Nat]("t")
						b.Show(
							"a segment is finite",
							By(
								num_segment.FiniteBelowStrict.At(t),
								complex_field.ComplexProductModuleSum.At(a, b.TermAs[Set[Nat]]("{i:num | i < t}"))))
					}))
				arg.Do(Simp(Rev(fold)))
				arg.Do(SplitConj(
					Case(
						"the empty product is one",
						Simp(Fwd(num_segment.BelowStrictClauses)),
						Cite(module.ModuleSumEmpty)),
					Case(
						"the next index contributes its factor",
						Simp(Fwd(num_segment.BelowStrictClauses)),
						By(
							set_basic.InUniv,
							num_segment.FiniteBelowStrict.At(s),
							nat_order.LessThanIrrefl.At(s),
							module.ModuleSumInsertMonoid.Read(monoid).AsFact().At(below, s, a))),
				))
			})
		squeeze := ctx.Lemma(Statement{
			Binders: "∀x y b c:real.",
			Hypotheses: []string{
				"&0 ≤ x",
				"x ≤ b",
				"&0 ≤ y",
				"y ≤ c",
				"&0 < b",
				"&0 < c",
				"x * y = b * c",
			},
			Conclusion: "x = b ∧ y = c",
		}, func(arg *Argument, x, y, b, c *Expr[Real], hypotheses Fact) {
			arg.Show(
				"two nonnegative factors at most b and c multiply to bc only at b and c",
				ByArith(hypotheses))
		})
		bound := ctx.Lemma(Statement{
			Binders:    "∀s:num. ∀a:(num → complex). ∀c:real.",
			Hypotheses: []string{"&0 < c", "∀i:num. i < s ⇒ |a(i)| ≤ c"},
			Conclusion: "|«product»(s, a)| ≤ c ^ s ∧ (|«product»(s, a)| = c ^ s ⇒ ∀k:num. k < s ⇒ |a(k)| = c)",
		}, func(arg *Argument, s *Expr[Nat], a *Arrow[Nat, Complex], c *Expr[Real]) {
			arg.Induct(s)
			arg.Base(
				"the empty product has modulus one, which is c to the zero",
				ByArith(At(clauses, a, arg.TermAs[Nat]("0")), complex_abs.AbsOfReal.At(arg.TermAs[Real]("&1"))))
			arg.Step(
				"the next modulus is |a(s)| times the modulus below",
				func(step *Argument, ih Fact) {
					given := step.Conjuncts(
						step.Assume(),
						"c is positive",
						"the factors below suc(s) are bounded")
					positive := given[0]
					bounds := step.Conjuncts(
						step.Have(
							"so are those below s, and a(s)",
							"(∀i:num. i < s ⇒ |a(i)| ≤ c) ∧ |a(s)| ≤ c",
							ByArith(given[1])),
						"the factors below s are bounded",
						"and so is a(s)")
					below := step.Conjuncts(
						step.Have(
							"the induction reads the product below",
							"|«product»(s, a)| ≤ c ^ s ∧ (|«product»(s, a)| = c ^ s ⇒ ∀k:num. k < s ⇒ |a(k)| = c)",
							By(Normalized, ih, positive, bounds[0])),
						"the modulus below is at most c^s",
						"and attaining c^s forces the factors below to c")
					root := step.TermAs[Complex]("a(s)")
					product := step.TermAs[Complex]("«product»(s, a)")
					modulus := step.Have(
						"the modulus of a product is the product of the moduli",
						"|«product»(suc(s), a)| = |a(s)| * |«product»(s, a)|",
						ByArith(At(clauses, a, s), complex_abs.AbsMul.At(root, product)))
					power := step.Have(
						"c^s is positive, and c^suc(s) is c times it",
						"c ^ suc(s) = c * c ^ s ∧ &0 < c ^ s",
						By(positive, real_pow.PowExpSucClause.At(c, s), real_pow.PowPos.At(c, s)))
					signs := step.Have(
						"moduli are not negative",
						"&0 ≤ |a(s)| ∧ &0 ≤ |«product»(s, a)|",
						By(complex_abs.AbsNonneg.At(root), complex_abs.AbsNonneg.At(product)))
					step.Do(SplitConj(
						Case(
							"two factors at most c and c^s multiply to at most c^suc(s)",
							ByArith(modulus, power, signs, positive, bounds[1], below[0])),
						Case(
							"equality in the product forces equality in each factor",
							Derive(func(equal *Argument) {
								attained := equal.Assume()
								both := equal.Have(
									"two such factors that multiply to c·c^s are c and c^s",
									"|a(s)| = c ∧ |«product»(s, a)| = c ^ s",
									By(
										attained,
										modulus,
										power,
										signs,
										positive,
										bounds[1],
										below[0],
										At(
											squeeze,
											equal.TermAs[Real]("|a(s)|"),
											equal.TermAs[Real]("|«product»(s, a)|"),
											c,
											equal.TermAs[Real]("c ^ s"))))
								equal.Show(
									"an index below suc(s) is s or lies below s",
									By(both, below[1], nat_order.LessThanSucClause))
							})),
					))
				})
		})
		return ctx.Theorem(headline, func(
			arg *Argument,
			s *Expr[Nat],
			a *Arrow[Nat, Complex],
			c *Expr[Real],
			k *Expr[Nat],
			hypotheses Fact,
		) {
			arg.Show(
				"the product attains c^s, and k lies below s",
				By(hypotheses, At(bound, s, a, c)))
		})
	}),
})}
