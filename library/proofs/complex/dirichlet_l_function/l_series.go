// l_series.go — the L-series of a Dirichlet character χ, the Dirichlet
// series of χ: it converges and is holomorphic on Re s > 0 when χ is not
// principal, its derivative is minus itself times the series of Λ·χ, and it
// does not vanish for Re s > 1. At s = 1 it does not vanish when χ is not
// principal: by Mertens' inequality for a character that is not real-valued,
// and by Monsky's argument for a real one.

package dirichlet_l_function

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/complex/cauchy_integral"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_derivative"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_topology"
	"github.com/euc-ai/xugo/library/proofs/complex/dirichlet_character"
	"github.com/euc-ai/xugo/library/proofs/complex/dirichlet_series"
	"github.com/euc-ai/xugo/library/proofs/complex/riemann_zeta"
	"github.com/euc-ai/xugo/library/registry"
)

// partialSumsBounded — the partial sums of a non-principal character χ mod q
// are at most φ(q) in size.
func partialSumsBounded(
	a *Argument,
	q *Expr[Nat],
	χ *Arrow[Nat, Complex],
	character, qPositive, nonprincipal Fact,
) Fact {
	return a.Have(
		"the character's partial sums are bounded by the number of units modulo q",
		"∀M:num. |Σ_{k∈1 .. M} χ(k)| ≤ &totient(q)",
		By(
			character,
			qPositive,
			nonprincipal,
			Where(dirichlet_character.CharacterPartialSumsBounded, "q", q).Where("χ", χ)))
}

// valuesBounded — the values of a character χ mod q have modulus at most 1.
func valuesBounded(
	a *Argument,
	q *Expr[Nat],
	χ *Arrow[Nat, Complex],
	character, qPositive Fact,
) Fact {
	return a.Have(
		"the character's values have modulus at most 1",
		"∀n:num. |χ(n)| ≤ &1",
		By(character, qPositive, Where(dirichlet_character.CharacterAbsLessEqOne, "q", q).Where("χ", χ)))
}

// multiplicativeOnPositives — a character χ is multiplicative at positive
// arguments, being completely multiplicative; the Dirichlet-series laws read
// it so.
func multiplicativeOnPositives(
	a *Argument,
	q *Expr[Nat],
	χ *Arrow[Nat, Complex],
	character Fact,
) Fact {
	return a.Have(
		"the character is multiplicative on positive indices",
		"∀m n:num. 0 < m ∧ 0 < n ⇒ χ(m * n) = χ(m) * χ(n)",
		By(character, Where(dirichlet_character.CharacterMul, "q", q).Where("χ", χ)))
}

// LSeriesConverges — the L-series of a non-principal character converges
// for Re s > 0.
var LSeriesConverges = lSeriesConvergesThm{family.Add(registry.ProofEntry{
	Name: "LSeriesConverges",
	Key:  "prop_eaf9ae6db459f75b",
	Build: family.Theorem(Statement{
		Binders: "∀q:num. ∀χ:(num → complex). ∀s:complex.",
		Hypotheses: []string{
			"dirichlet_character(q, χ)",
			"0 < q",
			"∃n:num. nat_coprime(n, q) ∧ χ(n) ≠ &1",
			"&0 < re(s)",
		},
		Conclusion: "∃v:complex. dirichlet_sums(χ, s, v)",
	},
		func(
			a *Argument,
			q *Expr[Nat],
			χ *Arrow[Nat, Complex],
			s *Expr[Complex],
			character, qPositive, nonprincipal, right Fact,
		) {
			bounded := partialSumsBounded(a, q, χ, character, qPositive, nonprincipal)
			a.Show(
				"the convergence estimate started at the modulus q, positive by hypothesis, supplies a sum",
				By(
					Normalized,
					bounded,
					qPositive,
					right,
					dirichlet_series.BoundedSumsConverge.At(χ, a.TermAs[Real]("&totient(q)"), s, q)))
		}),
	Reading: "On 0 < Re s ≤ 1 the convergence is conditional. For " +
		"the principal character the series converges only for Re s > 1.",
})}

// LSeriesHolomorphic — the L-series of a non-principal character is
// holomorphic on Re s > 0.
var LSeriesHolomorphic = lSeriesHolomorphicThm{family.Add(registry.ProofEntry{
	Name: "LSeriesHolomorphic",
	Key:  "prop_689fefd8877d949c",
	Build: family.Theorem(Statement{
		Binders: "∀q:num. ∀χ:(num → complex).",
		Hypotheses: []string{
			"dirichlet_character(q, χ)",
			"0 < q",
			"∃n:num. nat_coprime(n, q) ∧ χ(n) ≠ &1",
		},
		Conclusion: "holomorphic_on({s:complex | &0 < re(s)}, λs:complex. dirichlet_series(χ, s))",
	},
		func(a *Argument, q *Expr[Nat], χ *Arrow[Nat, Complex], character, qPositive, nonprincipal Fact) {
			bounded := partialSumsBounded(a, q, χ, character, qPositive, nonprincipal)
			a.Show(
				"bounded partial sums give holomorphy in the right half-plane",
				By(bounded, dirichlet_series.BoundedSumsHolomorphic.At(χ, a.TermAs[Real]("&totient(q)"))))
		}),
})}

// LSeriesMangoldt — for Re s > 1 the derivative of an L-series is minus
// itself times the Dirichlet series of Λ·χ: a character is completely
// multiplicative and bounded by 1, and for such a sequence the derivative
// of its Dirichlet series has that form.
var LSeriesMangoldt = lSeriesMangoldtThm{family.Add(registry.ProofEntry{
	Name: "LSeriesMangoldt",
	Key:  "prop_123e72e30338deac",
	Reading: "The series of Λ·χ is minus the logarithmic " +
		"derivative of the L-series, in the form that needs no division.",
	Build: family.Theorem(Statement{
		Binders: "∀q:num. ∀χ:(num → complex). ∀s:complex.",
		Hypotheses: []string{
			"dirichlet_character(q, χ)",
			"0 < q",
			"&1 < re(s)",
		},
		Conclusion: "complex_derivative_at(λz:complex. dirichlet_series(χ, z), " +
			"    s, " +
			"    -(dirichlet_series(χ, s) * dirichlet_series(λn:num. &(von_mangoldt(n)) * χ(n), s)))",
	},
		func(
			a *Argument,
			q *Expr[Nat],
			χ *Arrow[Nat, Complex],
			s *Expr[Complex],
			character, qPositive, right Fact,
		) {
			multiplicative := multiplicativeOnPositives(a, q, χ, character)
			bounded := valuesBounded(a, q, χ, character, qPositive)
			a.Show(
				"the logarithmic derivative of the series of a completely multiplicative sequence bounded by 1",
				By(multiplicative, bounded, right, dirichlet_series.LogarithmicDerivative.At(χ, s)))
		}),
})}

// LSeriesNonzeroRight — an L-series has no zero in Re s > 1: a character is
// completely multiplicative, takes the value 1 at 1 and is bounded by 1, and
// the Dirichlet series of such a sequence does not vanish there.
var LSeriesNonzeroRight = lSeriesNonzeroRightThm{family.Add(registry.ProofEntry{
	Name: "LSeriesNonzeroRight",
	Key:  "prop_47387c0bbcf21256",
	Build: family.Theorem(Statement{
		Binders: "∀q:num. ∀χ:(num → complex). ∀s:complex.",
		Hypotheses: []string{
			"dirichlet_character(q, χ)",
			"0 < q",
			"&1 < re(s)",
		},
		Conclusion: "dirichlet_series(χ, s) ≠ &0",
	},
		func(
			a *Argument,
			q *Expr[Nat],
			χ *Arrow[Nat, Complex],
			s *Expr[Complex],
			character, qPositive, right Fact,
		) {
			multiplicative := multiplicativeOnPositives(a, q, χ, character)
			bounded := valuesBounded(a, q, χ, character, qPositive)
			a.Show(
				"the series of a completely multiplicative sequence "+
					"with value 1 at 1 and bounded by 1 has no zero there",
				By(
					multiplicative,
					character,
					dirichlet_character.CharacterAtOne.At(q, χ),
					bounded,
					right,
					dirichlet_series.DirichletSeriesNonzero.At(χ, s)))
		}),
})}

// LSeriesNonzeroAtOneComplex — the L-series of a character that is not
// real-valued does not vanish at 1: χ and its square are both nonprincipal,
// so the series of χ is differentiable at 1 and the series of χ² continuous
// there, and Mertens' inequality at χ is the 3-4-1 lower bound that forbids
// a zero at 1.
var LSeriesNonzeroAtOneComplex = lSeriesNonzeroAtOneComplexThm{family.Add(registry.ProofEntry{
	Name: "LSeriesNonzeroAtOneComplex",
	Key:  "prop_33c1cfcfb6b4ce4b",
	Reading: "A character with a non-real value is not principal: that value is at a number " +
		"coprime to q and is not 1. For a real character χ² is principal, its L-series has a pole at " +
		"1, and the count 3 − 4 + 1 no longer forces anything; that case is LSeriesNonzeroAtOneReal.",
	Build: family.Theorem(Statement{
		Binders: "∀q:num. ∀χ:(num → complex).",
		Hypotheses: []string{
			"dirichlet_character(q, χ)",
			"0 < q",
			"∃n:num. im(χ(n)) ≠ &0",
		},
		Conclusion: "dirichlet_series(χ, complex_of_real(&1)) ≠ &0",
		Abbrev: Abbrev{
			{Name: "characterSquare", Text: "λn:num. χ(n) * χ(n)"},
			{Name: "L", Text: "λz:complex. dirichlet_series(χ, z)"},
			{Name: "squareL", Text: "λz:complex. dirichlet_series(«characterSquare», z)"},
			{Name: "halfPlane", Text: "{z:complex | &0 < re(z)}"},
			{Name: "mertensProduct", Text: "λσ:real. |riemann_zeta(&σ)| ^ 3 * |«L»(&σ)| ^ 4 * |«squareL»(&σ)|"},
		},
	},
		func(a *Argument, q *Expr[Nat], χ *Arrow[Nat, Complex], character, qPositive, nonreal Fact) {
			zero := a.TermAs[Real]("&0")
			one := a.TermAs[Real]("&1")
			center := a.TermAs[Complex]("complex_of_real(&1)")
			halfPlane := a.TermAs[Set[Complex]]("«halfPlane»")
			squared := a.TermAs[Fun[Nat, Complex]]("«characterSquare»")
			L := a.TermAs[Fun[Complex, Complex]]("«L»")
			squareL := a.TermAs[Fun[Complex, Complex]]("«squareL»")
			nonprincipal := a.Have(
				"a value with nonzero imaginary part occurs at a unit and differs from 1",
				"∃n:num. nat_coprime(n, q) ∧ χ(n) ≠ &1",
				Derive(func(b *Argument) {
					n, imaginary := b.UnpackAs[Nat](nonreal, "n")
					b.Take(n)
					b.Do(By(
						Normalized,
						imaginary,
						character,
						dirichlet_character.CharacterEqZero.At(q, n, χ),
						complex_field.PartsOfReal.At(zero),
						complex_field.PartsOfReal.At(one)))
				}))
			squareCharacter := a.Have(
				"the pointwise square is a Dirichlet character",
				"dirichlet_character(q, «characterSquare»)",
				By(character, dirichlet_character.CharacterClosure.At(q, χ, χ)))
			squareNonprincipal := a.Have(
				"a nonreal character has a nonprincipal square",
				"∃n:num. nat_coprime(n, q) ∧ «characterSquare»(n) ≠ &1",
				By(character, nonreal, dirichlet_character.NonRealCharacterSquare.At(q, χ)))
			centerInside := a.Have(
				"1 lies in the half-plane of positive real part",
				"complex_of_real(&1) ∈ «halfPlane»",
				ByArith(complex_field.PartsOfReal.At(one)))
			d, derivative := a.ObtainAs[Complex](
				"holomorphy supplies the derivative of the character series at 1",
				"∃d:complex. complex_derivative_at(«L», complex_of_real(&1), d)",
				By(
					character,
					qPositive,
					nonprincipal,
					centerInside,
					LSeriesHolomorphic.At(q, χ),
					At(complex_derivative.HolomorphicOnDef, halfPlane, L)))
			continuous := a.Have(
				"holomorphy gives continuity at 1 for the series of the squared character",
				"complex_continuous_at(«squareL», complex_of_real(&1))",
				By(
					squareCharacter,
					qPositive,
					squareNonprincipal,
					centerInside,
					LSeriesHolomorphic.At(q, squared),
					complex_derivative.HolomorphicOnContinuousAt.At(halfPlane, squareL, center)))
			multiplicative := multiplicativeOnPositives(a, q, χ, character)
			bounded := valuesBounded(a, q, χ, character, qPositive)
			mertens := a.Have(
				"Mertens' inequality at the character, at every real σ > 1",
				"∀σ:real. &1 < σ ⇒ &1 ≤ «mertensProduct»(σ)",
				Derive(func(b *Argument) {
					σ := b.FixAs[Real]("σ")
					right := b.Assume()
					b.Show(
						"Mertens' inequality read at χ",
						By(
							multiplicative,
							bounded,
							right,
							character,
							dirichlet_character.CharacterAtOne.At(q, χ),
							riemann_zeta.MertensInequality.At(χ, σ)))
				}))
			a.Show(
				"the 3-4-1 bound forbids a zero of the character series at 1",
				By(mertens, derivative, continuous, riemann_zeta.MertensNonvanishing.At(L, squareL, d)))
		}),
})}

// LSeriesNonzeroAtOne — the L-series of a non-principal Dirichlet
// character does not vanish at 1.
var LSeriesNonzeroAtOne = lSeriesNonzeroAtOneThm{family.Add(registry.ProofEntry{
	Name: "LSeriesNonzeroAtOne",
	Key:  "prop_9e9eebc9608338b5",
	Reading: "This is the fact Dirichlet's theorem turns on. For " +
		"the principal character the series does not converge at 1.",
	Build: family.Theorem(Statement{
		Binders: "∀q:num. ∀χ:(num → complex).",
		Hypotheses: []string{
			"dirichlet_character(q, χ)",
			"0 < q",
			"∃n:num. nat_coprime(n, q) ∧ χ(n) ≠ &1",
		},
		Conclusion: "dirichlet_series(χ, complex_of_real(&1)) ≠ &0",
	},
		func(a *Argument, q *Expr[Nat], χ *Arrow[Nat, Complex], character, qPositive, nonprincipal Fact) {
			a.Cases(a.TermAs[Bool]("∀n:num. im(χ(n)) = &0"))
			a.When(
				"the character is real-valued",
				func(b *Argument, realValued Fact) {
					b.Do(By(character, qPositive, realValued, nonprincipal, LSeriesNonzeroAtOneReal.At(q, χ)))
				})
			a.Otherwise(
				"the character takes a nonreal value",
				func(b *Argument, notRealValued Fact) {
					nonrealValue := b.Have(
						"some character value has nonzero imaginary part",
						"∃n:num. im(χ(n)) ≠ &0",
						By(Normalized, notRealValued))
					b.Do(By(character, qPositive, nonrealValue, LSeriesNonzeroAtOneComplex.At(q, χ)))
				})
		}),
})}

// NonprincipalMangoldtContinuous — for a non-principal character χ the
// series of Λ·χ, which converges for Re s > 1, extends continuously to
// s = 1: it is −L′/L to the right of 1 for the L-series L of χ, and −L′/L
// is continuous at 1, where L is holomorphic and does not vanish.
var NonprincipalMangoldtContinuous = nonprincipalMangoldtContinuousThm{family.Add(registry.ProofEntry{
	Name: "NonprincipalMangoldtContinuous",
	Key:  "prop_51f977cd2e453e5c",
	Reading: "The series of Λ·χ is minus the logarithmic derivative of the L-series, " +
		"so this is where the non-vanishing of the L-series at 1 is spent: a zero there " +
		"would give the series a pole of residue −1. For the principal character the " +
		"series is that of Λ on the numbers coprime to q, which has a pole at 1.",
	Build: family.Theorem(Statement{
		Binders: "∀q:num. ∀χ:(num → complex).",
		Hypotheses: []string{
			"dirichlet_character(q, χ)",
			"0 < q",
			"∃n:num. nat_coprime(n, q) ∧ χ(n) ≠ &1",
		},
		Conclusion: "∃Q:(complex → complex). " +
			"    complex_continuous_at(Q, complex_of_real(&1)) ∧ " +
			"    ∀s:complex. " +
			"        &1 < re(s) ⇒ Q(s) = dirichlet_series(λn:num. complex_of_real(von_mangoldt(n)) * χ(n), s)",
	},
		func(a *Argument, q *Expr[Nat], χ *Arrow[Nat, Complex], character, qPositive, nonprincipal Fact) {
			H := a.TermAs[Set[Complex]]("{z:complex | &0 < re(z)}")
			one := a.TermAs[Complex]("complex_of_real(&1)")
			oneReal := a.TermAs[Real]("&1")
			holomorphic := a.Have(
				"the nonprincipal L-series is holomorphic in the right half-plane",
				"holomorphic_on({z:complex | &0 < re(z)}, λz:complex. dirichlet_series(χ, z))",
				By(character, qPositive, nonprincipal, LSeriesHolomorphic.At(q, χ)))
			open := complex_topology.RightHalfPlaneOpen.At(a.TermAs[Real]("&0"))
			L, lDefinition := a.LetAs[Fun[Complex, Complex]]("L", "λz:complex. dirichlet_series(χ, z)")
			g, derivative := a.ObtainAs[Fun[Complex, Complex]](
				"the derivative of L is holomorphic on the same half-plane",
				"∃g:(complex → complex). "+
					"    (∀z:complex. z ∈ {w:complex | &0 < re(w)} ⇒ complex_derivative_at(L, z, g(z))) ∧ "+
					"    holomorphic_on({z:complex | &0 < re(z)}, g)",
				By(open, holomorphic, cauchy_integral.HolomorphicDerivative.At(H, L)),
				Named("g"))
			oneIn := a.Have(
				"one is in the right half-plane",
				"complex_of_real(&1) ∈ {z:complex | &0 < re(z)}",
				ByArith(complex_field.PartsOfReal.At(oneReal)))
			lContinuous := a.Have(
				"L is continuous at one",
				"complex_continuous_at(L, complex_of_real(&1))",
				By(holomorphic, oneIn, complex_derivative.HolomorphicOnContinuousAt.At(H, L, one)))
			gContinuous := a.Have(
				"its derivative is continuous at one",
				"complex_continuous_at(g, complex_of_real(&1))",
				By(derivative, oneIn, complex_derivative.HolomorphicOnContinuousAt.At(H, g, one)))
			lNonzero := a.Have(
				"the nonprincipal L-series is nonzero at one",
				"L(complex_of_real(&1)) ≠ complex_of_real(&0)",
				By(Normalized, lDefinition, character, qPositive, nonprincipal, LSeriesNonzeroAtOne.At(q, χ)))
			inverseContinuous := a.Have(
				"the reciprocal of L is continuous at one",
				"complex_continuous_at(λz:complex. complex_inv(L(z)), complex_of_real(&1))",
				By(lContinuous, lNonzero, complex_topology.ContinuousAtInv.At(L, one)))
			negContinuous := a.Have(
				"the negative derivative is continuous at one",
				"complex_continuous_at(λz:complex. -g(z), complex_of_real(&1))",
				By(gContinuous, complex_topology.ContinuousAtNeg.At(g, one)))
			Q, quotient := a.LetAs[Fun[Complex, Complex]]("Q", "λz:complex. -g(z) * complex_inv(L(z))")
			quotientContinuous := a.Have(
				"so the negative logarithmic derivative Q is continuous at one",
				"complex_continuous_at(Q, complex_of_real(&1))",
				By(
					quotient,
					inverseContinuous,
					negContinuous,
					complex_topology.ContinuousAtMul.At(a.TermAs[Fun[Complex, Complex]]("λz:complex. -g(z)"),
						a.TermAs[Fun[Complex, Complex]]("λz:complex. complex_inv(L(z))"), one)))
			a.Show(
				"the negative logarithmic derivative is the Mangoldt series to the right of one",
				Witness(Q),
				SplitConj(
					Case(
						"Q is continuous at one",
						By(quotientContinuous)),
					Case(
						"Q agrees with the series to the right of one",
						Derive(func(b *Argument) {
							s := b.FixAs[Complex]("s")
							right := b.Assume()
							inHalfPlane := b.Have(
								"the argument is in the half-plane",
								"s ∈ {z:complex | &0 < re(z)}",
								ByArith(right))
							gDerivative := b.Have(
								"g gives the derivative at this point",
								"complex_derivative_at(L, s, g(s))",
								By(derivative, inHalfPlane))
							v, value := b.LetAs[Complex]("v",
								"dirichlet_series(λn:num. complex_of_real(von_mangoldt(n)) * χ(n), s)")
							mangoldt := b.Have(
								"the differentiated series gives another expression for the derivative",
								"complex_derivative_at(L, s, -(L(s) * v))",
								By(Normalized, character, qPositive, right, lDefinition, value, LSeriesMangoldt.At(q, χ, s)))
							lAtS := b.TermAs[Complex]("L(s)")
							gValue := b.Have(
								"uniqueness of the derivative equates the two expressions",
								"g(s) = -(L(s) * v)",
								By(
									gDerivative,
									mangoldt,
									complex_derivative.DerivativeUnique.At(L, s,
										b.TermAs[Complex]("g(s)"), b.TermAs[Complex]("-(L(s) * v)"))))
							nonzero := b.Have(
								"L has no zero to the right of one",
								"L(s) ≠ complex_of_real(&0)",
								By(Normalized, character, qPositive, right, lDefinition, LSeriesNonzeroRight.At(q, χ, s)))
							inverse := b.Have(
								"the value of L cancels its inverse",
								"complex_inv(L(s)) * L(s) = complex_of_real(&1)",
								By(nonzero, field.MulLeftInverse.Read(complex_field.Field).At(lAtS)))
							b.Show(
								"the negative logarithmic derivative is the Mangoldt series",
								Simp(Fwd(quotient), Fwd(gValue)),
								Derive(func(c *Argument) {
									regroup := c.Have(
										"regroup the product to pair L with its inverse",
										"--(L(s) * v) * complex_inv(L(s)) = v * (complex_inv(L(s)) * L(s))",
										ByArith())
									c.Show(
										"cancel the inverse pair",
										By(regroup, inverse, comm_monoid.RightIdentity.Read(complex_field.MulMonoid).At(v)))
								}))
						}))))
		}),
})}
