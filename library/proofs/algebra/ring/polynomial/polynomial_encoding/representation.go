// representation.go — every degree-bounded polynomial is decoded from a
// carrier-valued environment, finitely many of them from one environment
// block by block, and a finite family has a common degree bound; a degree
// bound is a bound at every larger degree, and the bounds of two factors add
// to a bound of their product.

package polynomial_encoding

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_algebra"
	"github.com/euc-ai/xugo/library/proofs/datatypes/first_order"
	"github.com/euc-ai/xugo/library/proofs/iterate/nat/nat_sum"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_div_mod"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// CoefficientBlockRepresentation — finitely many degree-bounded polynomials are encoded by one
// environment, block by block: the j-th block starts at c + j·coefficient_count(n, d), and the slot
// of a bounded monomial lies below the coefficient count, so division by the block length reads a
// position's block and slot back, and the slots tell bounded monomials apart. A position therefore
// holds the slot of at most one block and one bounded monomial; the environment takes that
// polynomial's coefficient there and zero at every other position.
var CoefficientBlockRepresentation = coefficientBlockRepresentationThm{family.Add(registry.ProofEntry{
	Name: "CoefficientBlockRepresentation",
	Key:  "prop_d1a4ce8bb052635f",
	Reading: "The blocks start at c and have length coefficient_count(n, d), at " +
		"least one because the zero monomial is always bounded, so they are " +
		"disjoint; at k = 0 any carrier-valued environment works. comm_ring_on is " +
		"used only for R.zero ∈ R.carrier, which pads the environment off the blocks.",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀n d c k:num. ∀P:(num → (num → num) → A).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"∀j:num. j < k ⇒ polynomial_bound(R, n, d, P(j))",
		},
		Conclusion: "∃ρ:(num → A). " +
			"    fo_env_ok(R.carrier, 𝕌, ρ) ∧ (∀j:num. j < k ⇒ decode_polynomials(R, n, d, c, ρ, j) = P(j))",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			n, d, c, k *Expr[Nat],
			P *Arrow2[Nat, _Monomial, A],
			ring, bounded Fact,
		) {
			positions := a.Have(
				"a position in the blocks is the slot of one block and one bounded monomial",
				Statement{
					Binders: "∀j₁ j₂:num. ∀m₁ m₂:(num → num).",
					Hypotheses: []string{
						"m₁ ∈ bounded_monomials(n, d)",
						"m₂ ∈ bounded_monomials(n, d)",
						"c + j₁ * coefficient_count(n, d) + monomial_slot(n, d, m₁) = " +
							"c + j₂ * coefficient_count(n, d) + monomial_slot(n, d, m₂)",
					},
					Conclusion: "j₁ = j₂ ∧ m₁ = m₂",
				},
				Derive(func(b *Argument) {
					j1 := b.FixAs[Nat]("j₁")
					j2 := b.FixAs[Nat]("j₂")
					b.FixAs[_Monomial]("m₁")
					b.FixAs[_Monomial]("m₂")
					given := b.Conjuncts(
						b.Assume(),
						"m₁ is bounded",
						"m₂ is bounded",
						"and the two positions are one")
					offsets := b.Have(
						"past c the two positions are j₁ blocks and the slot of m₁, and j₂ blocks and the slot of m₂",
						"j₁ * coefficient_count(n, d) + monomial_slot(n, d, m₁) = "+
							"j₂ * coefficient_count(n, d) + monomial_slot(n, d, m₂)",
						ByArith(given[2]))
					slotsBelow := b.Have(
						"both slots lie below the block length",
						"monomial_slot(n, d, m₁) < coefficient_count(n, d) ∧ "+
							"monomial_slot(n, d, m₂) < coefficient_count(n, d)",
						By(given[0], given[1], MonomialSlots.At(n, d)))
					position := b.TermAs[Nat]("j₁ * coefficient_count(n, d) + monomial_slot(n, d, m₁)")
					count := b.TermAs[Nat]("coefficient_count(n, d)")
					slot1 := b.TermAs[Nat]("monomial_slot(n, d, m₁)")
					slot2 := b.TermAs[Nat]("monomial_slot(n, d, m₂)")
					sameSlot := b.Have(
						"division by the block length reads off the block and the slot",
						"j₁ = j₂ ∧ monomial_slot(n, d, m₁) = monomial_slot(n, d, m₂)",
						By(
							offsets,
							slotsBelow,
							nat_div_mod.DivModUniq.At(position, count, j1, slot1),
							nat_div_mod.DivModUniq.At(position, count, j2, slot2)))
					b.Show(
						"and the slots tell bounded monomials apart",
						By(sameSlot, given[0], given[1], MonomialSlots.At(n, d), functions.InjectiveOnDef))
				}))
			coefficients := a.Have(
				"each P(j) has its coefficients in the carrier and vanishes off the bounded monomials",
				Statement{
					Binders: "∀j:num. ∀m:(num → num).",
					Hypotheses: []string{
						"j < k",
					},
					Conclusion: "P(j, m) ∈ R.carrier ∧ (m ∉ bounded_monomials(n, d) ⇒ P(j, m) = R.zero)",
				},
				Derive(func(b *Argument) {
					j := b.FixAs[Nat]("j")
					b.FixAs[_Monomial]("m")
					bound := b.Conjuncts(
						b.Unfolded(GroupPremises(b.Assume(), bounded.At(j)), PolynomialBoundDef),
						"P(j) is a polynomial in the variables below n",
						"and its support lies among the bounded monomials")
					pj := b.TermAs[Fun[_Monomial, A]]("P(j)")
					b.Show(
						"a polynomial's coefficients lie in the carrier, and off its support P(j) is zero",
						By(
							bound[0],
							bound[1],
							polynomial_algebra.PolynomialAlgebraMember.At(R, b.TermAs[Set[Nat]]("{i:num | i < n}"), pj),
							set_basic.SubsetDef.At(
								b.TermAs[Set[_Monomial]]("fun_support(R.zero, P(j))"),
								b.TermAs[Set[_Monomial]]("bounded_monomials(n, d)"))))
				}))
			pointwise := a.Have(
				"at each position some carrier value agrees with every coefficient placed there",
				"∀w:num. ∃v:A. "+
					"    v ∈ R.carrier ∧ "+
					"    (∀j:num. ∀m:(num → num). "+
					"        j < k ∧ "+
					"        m ∈ bounded_monomials(n, d) ∧ "+
					"        w = c + j * coefficient_count(n, d) + monomial_slot(n, d, m) ⇒ "+
					"        v = P(j, m))",
				Derive(func(b *Argument) {
					b.FixAs[Nat]("w")
					b.Cases(b.TermAs[Bool](
						"∃j:num. ∃m:(num → num). " +
							"    j < k ∧ " +
							"    m ∈ bounded_monomials(n, d) ∧ " +
							"    w = c + j * coefficient_count(n, d) + monomial_slot(n, d, m)"))
					b.When(
						"w is the slot of a bounded m in the j-th block: take P(j)'s coefficient at m",
						func(e *Argument, placed Fact) {
							j, m, at := e.Unpack2As[Nat, _Monomial](placed, "j", "m")
							e.Take(e.TermAs[A]("P(j, m)"))
							only := e.Have(
								"any block and bounded monomial placed at w are j and m",
								Statement{
									Binders: "∀j₁:num. ∀m₁:(num → num).",
									Hypotheses: []string{
										"j₁ < k",
										"m₁ ∈ bounded_monomials(n, d)",
										"w = c + j₁ * coefficient_count(n, d) + monomial_slot(n, d, m₁)",
									},
									Conclusion: "P(j, m) = P(j₁, m₁)",
								},
								Derive(func(f *Argument) {
									j1 := f.FixAs[Nat]("j₁")
									m1 := f.FixAs[_Monomial]("m₁")
									other := f.Assume()
									f.Show(
										"both placements are the position w",
										By(at, other, positions.At(j, j1, m, m1)))
								}))
							e.Show(
								"so P(j)'s coefficient at m lies in the carrier and agrees with every coefficient placed at w",
								By(at, coefficients.At(j, m), only))
						})
					b.Otherwise(
						"no coefficient is placed at w: take zero, which lies in the carrier",
						func(e *Argument, empty Fact) {
							e.Take(e.TermAs[A]("R.zero"))
							e.Show(
								"and nothing placed at w is to agree with",
								By(empty, comm_ring.ZeroIn.Read(ring)))
						})
				}))
			ρ, chosen := a.ObtainAs[Fun[Nat, A]](
				"choose such a value at every position",
				"∃ρ:(num → A). "+
					"    (∀w:num. ρ(w) ∈ R.carrier) ∧ "+
					"    (∀j:num. ∀m:(num → num). "+
					"        j < k ∧ m ∈ bounded_monomials(n, d) ⇒ "+
					"        ρ(c + j * coefficient_count(n, d) + monomial_slot(n, d, m)) = P(j, m))",
				By(pointwise))
			values := a.Conjuncts(
				chosen,
				"ρ takes its values in the carrier",
				"and at the slot of a bounded m in the j-th block it reads P(j)'s coefficient at m")
			carrierValued, blockValue := values[0], values[1]
			a.Take(ρ)
			decoded := a.Have(
				"the j-th block decodes to P(j)",
				"∀j:num. j < k ⇒ decode_polynomial(R, n, d, c + j * coefficient_count(n, d), ρ) = P(j)",
				Derive(func(b *Argument) {
					j := b.FixAs[Nat]("j")
					below := b.Assume()
					b.Do(Funext())
					m := b.FixAs[_Monomial]("m")
					start := b.TermAs[Nat]("c + j * coefficient_count(n, d)")
					b.Show(
						"at a bounded m the block reads P(j)'s coefficient at m, and elsewhere both sides are zero",
						By(below, blockValue.At(j, m), coefficients.At(j, m), decodePolynomialDef.At(R, n, d, start, ρ, m)))
				}))
			a.Show(
				"ρ is a carrier environment, and each block decodes to its polynomial",
				Simp(Fwd(DecodePolynomialsDef)),
				By(carrierValued, first_order.EnvOKDef, decoded))
		}),
})}

// CoefficientRepresentation — every degree-bounded polynomial over the ring is decoded from a
// carrier-valued environment at any block start c: the block representation of the one-member
// family, whose block 0 starts at c.
var CoefficientRepresentation = coefficientRepresentationThm{family.Add(registry.ProofEntry{
	Name: "CoefficientRepresentation",
	Key:  "prop_1b72f8ad3a6e9caf",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀n d c:num. ∀p:((num → num) → A).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"polynomial_bound(R, n, d, p)",
		},
		Conclusion: "∃ρ:(num → A). fo_env_ok(R.carrier, 𝕌, ρ) ∧ decode_polynomial(R, n, d, c, ρ) = p",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			n, d, c *Expr[Nat],
			p *Arrow[_Monomial, A],
			ring, bound Fact,
		) {
			ρ, chosen := a.ObtainAs[Fun[Nat, A]](
				"one environment encodes the one-member family p in a single block at c",
				"∃ρ:(num → A). "+
					"    fo_env_ok(R.carrier, 𝕌, ρ) ∧ (∀j:num. j < 1 ⇒ decode_polynomials(R, n, d, c, ρ, j) = p)",
				By(
					ring,
					bound,
					CoefficientBlockRepresentation.At(
						R, n, d, c, a.TermAs[Nat]("1"), a.TermAs[Fun2[Nat, _Monomial, A]]("λj:num. p"))))
			values := a.Conjuncts(
				chosen,
				"ρ takes its values in the carrier",
				"and its one block decodes to p")
			a.Take(ρ)
			a.Show(
				"block 0 starts at c + 0 · coefficient_count(n, d), which is c",
				ByArith(values[0], a.Simplified(values[1].At(a.TermAs[Nat]("0")), Fwd(DecodePolynomialsDef))))
		}),
})}

// CommonDegreeBound — finitely many polynomials in n variables have a common bound on their total
// degrees: each is nonzero at finitely many monomials, all of them monomials of the variables below
// n, and a summand of a finite sum of numbers is at most the sum, so the sum over the polynomials
// of the total degrees of the monomials where each is nonzero bounds every one.
var CommonDegreeBound = commonDegreeBoundThm{family.Add(registry.ProofEntry{
	Name: "CommonDegreeBound",
	Key:  "prop_60d292fd4991eed7",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀n k:num. ∀P:(num → (num → num) → A).",
		Hypotheses: []string{
			"∀j:num. j < k ⇒ P(j) ∈ polynomial_algebra(R, {i:num | i < n})",
		},
		Conclusion: "∃d:num. ∀j:num. j < k ⇒ polynomial_bound(R, n, d, P(j))",
		Abbrev: Abbrev{
			{Name: "degree", Text: "λm:(num → num). nat_sum({i:num | i < n}, m)"},
			{Name: "degreeSum", Text: "λj:num. nat_sum(fun_support(R.zero, P(j)), «degree»)"},
			{Name: "total", Text: "nat_sum({j:num | j < k}, «degreeSum»)"},
		},
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			n, k *Expr[Nat],
			P *Arrow2[Nat, _Monomial, A],
			polynomials Fact,
		) {
			below := a.TermAs[Set[Nat]]("{i:num | i < n}")
			total := a.TermAs[Nat]("«total»")
			a.Take(total)
			j := a.FixAs[Nat]("j")
			index := a.Assume()
			support := a.Conjuncts(
				a.Simplified(
					GroupPremises(index, polynomials.At(j)),
					Fwd(polynomial_algebra.PolynomialAlgebraMember)),
				"P(j) is a polynomial below n: it is nonzero at finitely many monomials",
				"each of them a monomial of the variables below n",
				"and its coefficients lie in the carrier")
			bounded := a.Have(
				"every monomial where P(j) is nonzero is bounded by «total»",
				"fun_support(R.zero, P(j)) ⊆ bounded_monomials(n, «total»)",
				Unfold(set_basic.SubsetDef),
				Derive(func(b *Argument) {
					m := b.FixAs[_Monomial]("m")
					inSupport := b.Assume()
					vanishes := b.Have(
						"m is a monomial of the variables below n, so it vanishes from n on",
						"∀i:num. n ≤ i ⇒ m(i) = 0",
						ByArith(inSupport, support[1], polynomial_algebra.MonomialSupport.At(below, m)))
					degree := b.Have(
						"the degree of m is a summand of P(j)'s degree sum, which is a summand of «total»",
						"«degree»(m) ≤ «total»",
						ByArith(
							inSupport,
							support[0],
							index,
							nat_sum.TermLeSum.At(
								b.TermAs[Fun[_Monomial, Nat]]("«degree»"),
								b.TermAs[Set[_Monomial]]("fun_support(R.zero, P(j))"),
								m),
							nat_sum.TermLeSum.At(
								b.TermAs[Fun[Nat, Nat]]("«degreeSum»"),
								b.TermAs[Set[Nat]]("{j:num | j < k}"),
								j),
							num_segment.FiniteBelowStrict.At(k)))
					b.Show(
						"so m vanishes from n on and has total degree at most «total»",
						BySets(vanishes, degree, BoundedMonomialsDef.At(n, total)))
				}))
			a.Show(
				"P(j) is a polynomial below n supported in the monomials bounded by «total»",
				By(index, polynomials.At(j), bounded, PolynomialBoundDef))
		}),
})}

// PolynomialBoundMono — a degree bound is a bound at every larger degree: the polynomial is the
// same member of the algebra, and its support, inside the monomials of total degree at most d,
// lies inside those of total degree at most e.
var PolynomialBoundMono = polynomialBoundMonoThm{family.Add(registry.ProofEntry{
	Name: "PolynomialBoundMono",
	Key:  "prop_c692ec0d37d54df5",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀n d e:num. ∀p:((num → num) → A).",
		Hypotheses: []string{
			"polynomial_bound(R, n, d, p)",
			"d ≤ e",
		},
		Conclusion: "polynomial_bound(R, n, e, p)",
	}, func(
		a *Argument,
		R *Expr[RingOps[A]],
		n, d, e *Expr[Nat],
		p *Arrow[_Monomial, A],
		bound, below Fact,
	) {
		degrees := a.Have(
			"a total degree at most d is at most e",
			"∀t:num. t ≤ d ⇒ t ≤ e",
			ByArith(below))
		wider := a.Have(
			"the monomials of total degree at most d have total degree at most e",
			"bounded_monomials(n, d) ⊆ bounded_monomials(n, e)",
			Simp(Fwd(BoundedMonomialsDef)),
			BySets(degrees))
		parts := a.Conjuncts(
			a.Simplified(bound, Fwd(PolynomialBoundDef)),
			"p lies in the polynomial algebra below n",
			"its support lies in the monomials of total degree at most d")
		a.Show(
			"the same member of the algebra, its support in the wider set",
			Simp(Fwd(PolynomialBoundDef)),
			By(parts[0], parts[1], wider, set_order.SubsetTrans))
	}),
})}

// PolynomialBoundMul — the product of a polynomial of degree at most d and one of degree at most e
// has degree at most d + e. A monomial m where the product is nonzero is m₁ + (m − m₁) with p
// nonzero at m₁ and q nonzero at m − m₁ (polynomial_algebra.PolynomialAlgebraMulSupport), so both
// vanish from n on, their degrees are at most d and e, and the degree of m is their sum.
var PolynomialBoundMul = polynomialBoundMulThm{family.Add(registry.ProofEntry{
	Name: "PolynomialBoundMul",
	Key:  "prop_a2131c0c2cc416f6",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀n d e:num. ∀p q:((num → num) → A).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"polynomial_bound(R, n, d, p)",
			"polynomial_bound(R, n, e, q)",
		},
		Conclusion: "polynomial_bound(R, n, d + e, polynomial_algebra_mul(R, p, q))",
	}, func(
		a *Argument,
		R *Expr[RingOps[A]],
		n, d, e *Expr[Nat],
		p, q *Arrow[_Monomial, A],
		ring, pBound, qBound Fact,
	) {
		pParts := a.Conjuncts(
			a.Simplified(pBound, Fwd(PolynomialBoundDef)),
			"p is a polynomial in the variables below n",
			"p is nonzero only at monomials of degree at most d")
		qParts := a.Conjuncts(
			a.Simplified(qBound, Fwd(PolynomialBoundDef)),
			"q is a polynomial in the variables below n",
			"q is nonzero only at monomials of degree at most e")
		coefficients := a.Have(
			"every coefficient of p and of q lies in R",
			"(∀m:(num → num). p(m) ∈ R.carrier) ∧ (∀m:(num → num). q(m) ∈ R.carrier)",
			By(pParts[0], qParts[0], polynomial_algebra.PolynomialAlgebraMember))
		degree := a.Have(
			"a monomial where the product is nonzero has degree at most d + e",
			"∀m:(num → num). polynomial_algebra_mul(R, p, q, m) ≠ R.zero ⇒ m ∈ bounded_monomials(n, d + e)",
			Derive(func(b *Argument) {
				m := b.FixAs[_Monomial]("m")
				nonzero := b.Assume()
				split := b.Conjuncts(
					GroupPremises(
						ring, coefficients, nonzero, At(polynomial_algebra.PolynomialAlgebraMulSupport, R, p, q, m)),
					"m is finitely supported",
					"some m₁ below m has p(m₁) and q(m − m₁) nonzero")
				m1, term := b.UnpackAs[_Monomial](split[1], "m₁")
				pieces := b.Conjuncts(
					term,
					"m₁ lies below m",
					"p is nonzero at m₁",
					"q is nonzero at m − m₁")
				bounded := b.Have(
					"so m₁ has degree at most d and m − m₁ degree at most e",
					"m₁ ∈ bounded_monomials(n, d) ∧ (λx:num. m(x) - m₁(x)) ∈ bounded_monomials(n, e)",
					BySets(pieces[1], pieces[2], pParts[1], qParts[1]))
				exponents := b.Have(
					"exponent by exponent, m is m₁ plus m − m₁",
					"(λx:num. m₁(x) + (m(x) - m₁(x))) = m",
					Funext(),
					ByArith(pieces[0]))
				degrees := b.Have(
					"so the degree of m is that of m₁ plus that of m − m₁",
					"sum({i:num | i < n}, m) = sum({i:num | i < n}, m₁) + sum({i:num | i < n}, λx:num. m(x) - m₁(x))",
					By(
						exponents,
						nat_sum.Add.At(
							m1, b.TermAs[Fun[Nat, Nat]]("λx:num. m(x) - m₁(x)"), b.TermAs[Set[Nat]]("{i:num | i < n}")),
						num_segment.FiniteBelowStrict))
				b.Show(
					"m vanishes from n on, as m₁ and m − m₁ do, and its degree is at most d + e",
					Simp(Fwd(BoundedMonomialsDef)),
					ByArith(pieces[0], degrees, b.Unfolded(bounded, BoundedMonomialsDef)))
			}))
		a.Show(
			"the product is a polynomial in the variables below "+
				"n, nonzero only at monomials of degree at most d + e",
			Unfold(PolynomialBoundDef),
			BySets(ring, degree, pParts[0], qParts[0], polynomial_algebra.PolynomialAlgebraMulIn))
	}),
})}

// TupleOfPolynomial — a polynomial in one variable over the carrier is a ring tuple of some
// length: its coefficients vanish from some index n on and lie in the carrier, which is what a
// ring tuple of length n asks.
var TupleOfPolynomial = tupleOfPolynomialThm{family.Add(registry.ProofEntry{
	Name: "TupleOfPolynomial",
	Key:  "prop_7d61fa2f8112efaa",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀p:(num → A).",
		Hypotheses: []string{
			"polynomial_over(R.zero, R.carrier, p)",
		},
		Conclusion: "∃n:num. ring_tuple(R, n, p)",
	}, func(a *Argument, R *Expr[RingOps[A]], p *Arrow[Nat, A], over Fact) {
		parts := a.Conjuncts(
			a.Unfolded(over, polynomial.PolynomialOverDef),
			"p vanishes from some length on",
			"and its coefficients lie in the carrier")
		n, vanishes := a.UnpackAs[Nat](parts[0], "n")
		a.Take(n)
		a.Show(
			"so p is a ring tuple of that length",
			By(vanishes, parts[1], RingTupleDef))
	}),
})}
