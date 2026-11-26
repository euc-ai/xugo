// degree.go — the degree: a polynomial vanishes past it and it is the
// least such bound; truncation below the degree, and the image of a
// polynomial under a map killing its leading coefficient; the polynomials
// of degree zero are the constants; how the degree behaves under
// products and scaling, and the polynomials over a domain forming a
// domain; and the monic polynomials, which are nonzero and are reached by
// scaling a nonzero polynomial over a field.

package polynomial

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_domain"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/nat_num/peano"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// DegreeVec — a polynomial vanishes past its degree. It is an n-vector
// for some n, so a suc(n)-vector; well-ordering then gives a least d with
// p a suc(d)-vector, and the degree is the choice of such a least d.
var DegreeVec = degreeVecThm{family.Add(registry.ProofEntry{
	Name: "DegreeVec",
	Key:  "prop_1f760f24931372ea",
	Build: family.Theorem(Statement{
		Binders: "∀zero:A. ∀c:set(A). ∀p:(num → A).",
		Hypotheses: []string{
			"polynomial_over(zero, c, p)",
		},
		Conclusion: "vec⟨suc(polynomial_degree(zero, p))⟩(zero, p)",
	},
		func(a *Argument, zero *Expr[A], c *Expr[Set[A]], p *Arrow[Nat, A], poly Fact) {
			// The definition at p supplies its existential half.
			n, vanishes := a.ObtainAs[Nat](
				"p vanishes from some index n on",
				"∃n:num. vec⟨n⟩(zero, p)",
				By(poly, PolynomialOverDef.At(zero, c, p)))
			bound := a.Have(
				"so from the later index suc(n) on as well",
				"vec⟨suc(n)⟩(zero, p)",
				By(
					vanishes,
					vec_space.VecMono.At(zero, n, a.TermAs[Nat]("suc(n)"), p),
					nat_order.LessEqSucClause.At(n, n),
					nat_order.LessEqRefl.At(n)))
			least := a.Have(
				"by well-ordering some d is least with p vanishing from suc(d) on",
				"∃d:num. vec⟨suc(d)⟩(zero, p) ∧ (∀m:num. vec⟨suc(m)⟩(zero, p) ⇒ d ≤ m)",
				By(
					bound,
					nat_order.WellOrdering.At(a.TermAs[Set[Nat]]("λd:num. vec⟨suc(d)⟩(zero, p)")),
					nat_order.NotLessThan))
			a.Do(Unfold(PolynomialDegreeDef))
			_, chosen := a.ObtainChosen(
				"the degree is such a least d, the one the definition chooses",
				"∃d:num. vec⟨suc(d)⟩(zero, p) ∧ (∀m:num. vec⟨suc(m)⟩(zero, p) ⇒ d ≤ m)",
				least)
			a.Show(
				"so p vanishes from its successor on",
				By(chosen))
		}),
})}

// DegreeLeast — a polynomial vanishing past m has degree at most m: m is
// one of the d past which p vanishes, so there is a least one, and the
// degree is the least one the definition chooses.
var DegreeLeast = degreeLeastThm{family.Add(registry.ProofEntry{
	Name: "DegreeLeast",
	Key:  "prop_5d6cff352b7b444d",
	Build: family.Theorem(Statement{
		Binders: "∀zero:A. ∀p:(num → A). ∀m:num.",
		Hypotheses: []string{
			"vec⟨suc(m)⟩(zero, p)",
		},
		Conclusion: "polynomial_degree(zero, p) ≤ m",
	},
		func(a *Argument, zero *Expr[A], p *Arrow[Nat, A], m *Expr[Nat], bounded Fact) {
			vanishesPast := a.TermAs[Set[Nat]]("λd:num. vec⟨suc(d)⟩(zero, p)")
			least := a.Have(
				"p vanishes past m, so there is a least d past which it vanishes (well-ordering)",
				"∃d:num. vec⟨suc(d)⟩(zero, p) ∧ (∀k:num. vec⟨suc(k)⟩(zero, p) ⇒ d ≤ k)",
				By(bounded, nat_order.WellOrdering.At(vanishesPast), nat_order.NotLessThan))
			a.Do(Unfold(PolynomialDegreeDef))
			_, chosen := a.ObtainChosen(
				"the degree is such a least d, the one the definition chooses",
				"∃d:num. vec⟨suc(d)⟩(zero, p) ∧ (∀k:num. vec⟨suc(k)⟩(zero, p) ⇒ d ≤ k)",
				least)
			a.Show(
				"p vanishes past m, so the least such d is at most m",
				By(chosen, bounded))
		}),
})}

// DegreeExact — a polynomial vanishing past n whose coefficient at n is not
// zero has degree n: vanishing past n bounds the degree above, and p vanishes
// past its degree, which therefore is not below n.
var DegreeExact = degreeExactThm{family.Add(registry.ProofEntry{
	Name: "DegreeExact",
	Key:  "prop_b86d8bfc1cf2e882",
	Build: family.Theorem(Statement{
		Binders: "∀zero:A. ∀c:set(A). ∀p:(num → A). ∀n:num.",
		Hypotheses: []string{
			"polynomial_over(zero, c, p)",
			"vec⟨suc(n)⟩(zero, p)",
			"p(n) ≠ zero",
		},
		Conclusion: "polynomial_degree(zero, p) = n",
	},
		func(
			a *Argument,
			zero *Expr[A],
			c *Expr[Set[A]],
			p *Arrow[Nat, A],
			n *Expr[Nat],
			over, past, nonzero Fact,
		) {
			atMost := a.Have(
				"p vanishes past n, so its degree is at most n",
				"polynomial_degree(zero, p) ≤ n",
				By(past, DegreeLeast.At(zero, p, n)))
			pastDegree := a.Have(
				"p vanishes past its degree",
				"vec⟨suc(polynomial_degree(zero, p))⟩(zero, p)",
				By(over, DegreeVec.At(zero, c, p)))
			atLeast := a.Have(
				"p does not vanish at n, so its degree is not below n",
				"¬(suc(polynomial_degree(zero, p)) ≤ n)",
				By(a.Unfolded(pastDegree, vec_space.VecDef).At(n), nonzero))
			a.Show(
				"the two bounds agree at n",
				ByArith(atMost, atLeast))
		}),
})}

// DegreeVecZero — the zero polynomial has degree 0: it vanishes past 0,
// and the degree is at most every index past which a sequence vanishes
// (DegreeLeast).
var DegreeVecZero = degreeVecZeroThm{family.Add(registry.ProofEntry{
	Name: "DegreeVecZero",
	Key:  "prop_5cf560e55aa92118",
	Build: family.Theorem("∀zero:A. polynomial_degree(zero, vec_zero(zero)) = 0",
		func(a *Argument, zero *Expr[A]) {
			zeroth := a.TermAs[Nat]("0")
			a.Show(
				"vec_zero vanishes past 0, so its degree is at most 0, and a number at most 0 is 0",
				By(
					vec_space.VecZero.At(zero, a.TermAs[Nat]("suc(0)")),
					DegreeLeast.At(zero, a.TermAs[Fun[Nat, A]]("vec_zero(zero)"), zeroth),
					nat_order.LessEqZeroClause.At(a.TermAs[Nat]("polynomial_degree(zero, vec_zero(zero))"))))
		}),
})}

// DegreeBelow — a nonzero sequence that vanishes from n on has degree
// below n. A sequence vanishing from 0 on is the zero sequence, so n is
// not 0; it is suc(m) for some m, p vanishes past m, and the degree, the
// least index past which p vanishes, is at most m (DegreeLeast).
var DegreeBelow = degreeBelowThm{family.Add(registry.ProofEntry{
	Name:    "DegreeBelow",
	Reading: "p ≠ vec_zero is what excludes n = 0: vec_zero vanishes from 0 on and has degree 0.",
	Key:     "prop_36346e5b76e994ca",
	Build: family.Theorem(Statement{
		Binders: "∀zero:A. ∀p:(num → A). ∀n:num.",
		Hypotheses: []string{
			"vec⟨n⟩(zero, p)",
			"¬(p = vec_zero(zero))",
		},
		Conclusion: "polynomial_degree(zero, p) < n",
	},
		func(a *Argument, zero *Expr[A], p *Arrow[Nat, A], n *Expr[Nat], hypotheses Fact) {
			parts := a.Conjuncts(
				hypotheses,
				"p vanishes from n on",
				"p is not the zero sequence")
			vanishes, nonzero := parts[0], parts[1]
			a.Cases(a.Term("n = 0"))
			a.When(
				"n = 0 is impossible: a sequence vanishing from 0 on is the zero sequence",
				func(b *Argument, atZero Fact) {
					fromZero := b.Have(
						"p would vanish from 0 on",
						"vec⟨0⟩(zero, p)",
						atZero.RwRev(),
						By(vanishes))
					b.Show(
						"and so be the zero sequence, which it is not",
						By(Normalized, fromZero, nonzero, vec_space.VecDimZero.At(zero, p)))
				})
			a.Otherwise(
				"at a positive n the degree is at most its predecessor",
				func(b *Argument, positive Fact) {
					m, isSuc := b.ObtainAs[Nat](
						"n is the successor of some m",
						"∃m:num. n = suc(m)",
						By(Normalized, positive, peano.Cases.At(n)))
					atMost := b.Have(
						"p vanishes from suc(m) on, so its degree is at most m",
						"polynomial_degree(zero, p) ≤ m",
						By(Normalized, isSuc, vanishes, DegreeLeast.At(zero, p, m)))
					b.Show(
						"which is below suc(m) = n",
						ByArith(atMost, isSuc))
				})
		}),
})}

// VecOfDegreeBelow — a polynomial that is zero, or of degree below n,
// vanishes from n on, the converse of DegreeBelow: the zero sequence
// vanishes everywhere, and a polynomial vanishes past its degree, so at
// every index from n on.
var VecOfDegreeBelow = vecOfDegreeBelowThm{family.Add(registry.ProofEntry{
	Name: "VecOfDegreeBelow",
	Key:  "prop_e36e6150abc723de",
	Build: family.Theorem(Statement{
		Binders: "∀zero:A. ∀c:set(A). ∀p:(num → A). ∀n:num.",
		Hypotheses: []string{
			"polynomial_over(zero, c, p)",
			"p = vec_zero(zero) ∨ polynomial_degree(zero, p) < n",
		},
		Conclusion: "vec⟨n⟩(zero, p)",
	}, func(
		a *Argument,
		zero *Expr[A],
		c *Expr[Set[A]],
		p *Arrow[Nat, A],
		n *Expr[Nat],
		over, small Fact,
	) {
		a.Do(small.SplitDisj(
			LeftHolds(
				"the zero sequence vanishes at every index",
				Given(func(b *Argument, isZero Fact) {
					b.Show(
						"so from n on",
						isZero.Rw(),
						Cite(vec_space.VecZero))
				})),
			RightHolds(
				"p vanishes past its degree, which is below n",
				Given(func(b *Argument, below Fact) {
					b.Show(
						"so at every index from n on",
						Unfold(vec_space.VecDef),
						Derive(func(d *Argument) {
							d.FixAs[Nat]("i")
							from := d.Assume()
							beyond := d.Have(
								"an index from n on lies past the degree",
								"suc(polynomial_degree(zero, p)) ≤ i",
								ByArith(below, from))
							d.Show(
								"where p vanishes",
								By(
									beyond,
									over,
									DegreeVec.At(zero, c, p),
									vec_space.VecDef.Inst[A]().At(zero, d.TermAs[Nat]("suc(polynomial_degree(zero, p))"), p)))
						}))
				}))))
	}),
})}

// TruncateBelow — cutting a polynomial off below a positive n leaves a
// polynomial of degree below n: the truncation vanishes from n on, its
// coefficients are p's or the zero, and a sequence vanishing from n on is
// either the zero sequence, of degree zero, or nonzero and of degree below
// n (DegreeBelow).
var TruncateBelow = truncateBelowThm{family.Add(registry.ProofEntry{
	Name: "TruncateBelow",
	Key:  "prop_34ab2ab183481bd8",
	Build: family.Theorem(Statement{
		Binders: "∀zero:A. ∀c:set(A). ∀p:(num → A). ∀n:num.",
		Hypotheses: []string{
			"polynomial_over(zero, c, p)",
			"zero ∈ c",
			"0 < n",
		},
		Conclusion: "polynomial_over(zero, c, λi:num. COND(i < n, p(i), zero)) ∧ " +
			"polynomial_degree(zero, λi:num. COND(i < n, p(i), zero)) < n",
	}, func(
		a *Argument,
		zero *Expr[A],
		c *Expr[Set[A]],
		p *Arrow[Nat, A],
		n *Expr[Nat],
		over, zeroIn, positive Fact,
	) {
		vanishes := a.Have(
			"the truncation vanishes from n on",
			"vec⟨n⟩(zero, λi:num. COND(i < n, p(i), zero))",
			Unfold(vec_space.VecDef),
			By(nat_order.NotLessThan))
		truncated := a.Have(
			"its coefficients are those of p below n and the zero from n on, so it is a polynomial over c",
			"polynomial_over(zero, c, λi:num. COND(i < n, p(i), zero))",
			By(zeroIn, over, vanishes, PolynomialOverDef))
		degree := a.Have(
			"its degree is below n",
			"polynomial_degree(zero, λi:num. COND(i < n, p(i), zero)) < n",
			Derive(func(b *Argument) {
				b.Cases(b.Term("(λi:num. COND(i < n, p(i), zero)) = vec_zero(zero)"))
				b.When(
					"the zero sequence has degree zero, below the positive n",
					func(d *Argument, isZero Fact) {
						d.Show(
							"by the degree of the zero sequence",
							isZero.Rw(),
							ByArith(positive, DegreeVecZero.At(zero)))
					})
				b.Otherwise(
					"a nonzero sequence vanishing from n on has degree below n",
					func(d *Argument, nonzero Fact) {
						d.Show(
							"its last nonzero coefficient comes before n",
							By(nonzero, vanishes, DegreeBelow))
					})
			}))
		a.Show(
			"the truncation is a polynomial over c of degree below n",
			By(truncated, degree))
	}),
})}

// TruncationImage — a map σ keeping zero that sends the leading coefficient
// of q to zero sends q and its truncation below the degree to one sequence:
// below the degree the two agree, at the degree σ kills the leading
// coefficient, and past it q vanishes as the truncation does.
var TruncationImage = truncationImageThm{family.Add(registry.ProofEntry{
	Name: "TruncationImage",
	Key:  "prop_816f68e1525de305",
	Build: family.Theorem(Statement{
		Binders: "∀zero:B. ∀c:set(B). ∀z:A. ∀σ:(B → A). ∀q:(num → B).",
		Hypotheses: []string{
			"polynomial_over(zero, c, q)",
			"σ(zero) = z",
			"σ(q(polynomial_degree(zero, q))) = z",
		},
		Conclusion: "(λi:num. σ(COND(i < polynomial_degree(zero, q), q(i), zero))) = (λi:num. σ(q(i)))",
	}, func(
		a *Argument,
		zero *Expr[B],
		c *Expr[Set[B]],
		z *Expr[A],
		σ *Arrow[B, A],
		q *Arrow[Nat, B],
		over, keepsZero, leading Fact,
	) {
		vanishes := a.Have(
			"q vanishes past its degree",
			"vec⟨suc(polynomial_degree(zero, q))⟩(zero, q)",
			By(over, DegreeVec))
		a.Do(Funext())
		a.FixAs[Nat]("i")
		a.Cases(a.Term("i < polynomial_degree(zero, q)"))
		a.When(
			"below the degree the truncation is q",
			func(b *Argument, below Fact) {
				b.Show(
					"its coefficient there is that of q",
					By(below))
			})
		a.Otherwise(
			"from the degree on the truncation is zero, and σ sends q(i) to z as it sends zero",
			func(b *Argument, notBelow Fact) {
				coefficient := b.Have(
					"σ sends q(i) to z: at the degree by assumption, past it since q vanishes there",
					"σ(q(i)) = z",
					Derive(func(d *Argument) {
						d.Cases(d.Term("i = polynomial_degree(zero, q)"))
						d.When(
							"at the degree q(i) is the leading coefficient",
							func(e *Argument, atDegree Fact) {
								e.Show(
									"which σ sends to z",
									By(Normalized, leading, atDegree))
							})
						d.Otherwise(
							"past the degree the coefficient of q is zero",
							func(e *Argument, pastDegree Fact) {
								beyond := e.Have(
									"i lies past the degree of q",
									"suc(polynomial_degree(zero, q)) ≤ i",
									ByArith(notBelow, pastDegree))
								e.Show(
									"where q vanishes, and σ sends zero to z",
									By(beyond, vanishes, keepsZero, vec_space.VecDef))
							})
					}))
				b.Show(
					"both sides are z",
					By(Normalized, notBelow, coefficient, keepsZero))
			})
	}),
})}

// DegreeLeading — a nonzero polynomial's coefficient at its degree is
// not zero: p vanishes past its degree d, so were its coefficient at d
// zero it would vanish from d on, and a nonzero sequence vanishing from d
// on has degree below d (DegreeBelow) — d would be below itself.
var DegreeLeading = degreeLeadingThm{family.Add(registry.ProofEntry{
	Name: "DegreeLeading",
	Key:  "prop_9e404c8c980d4dbe",
	Build: family.Theorem(Statement{
		Binders: "∀zero:A. ∀c:set(A). ∀p:(num → A).",
		Hypotheses: []string{
			"polynomial_over(zero, c, p)",
			"¬(p = vec_zero(zero))",
		},
		Conclusion: "¬(p(polynomial_degree(zero, p)) = zero)",
	},
		func(a *Argument, zero *Expr[A], c *Expr[Set[A]], p *Arrow[Nat, A], hypotheses Fact) {
			d, degree := a.LetAs[Nat]("d", "polynomial_degree(zero, p)")
			past := a.Have(
				"p vanishes past its degree d",
				"vec⟨suc(d)⟩(zero, p)",
				By(Normalized, degree, hypotheses, DegreeVec.At(zero, c, p)))
			leadingZero := a.SupposeNot()
			from := a.Have(
				"so with its coefficient at d zero, p vanishes from d on",
				"vec⟨d⟩(zero, p)",
				Derive(func(b *Argument) {
					b.Do(Simp(Fwd(vec_space.VecDef)))
					b.FixAs[Nat]("i")
					atLeast := b.Assume()
					b.Cases(b.Term("i = d"))
					b.When(
						"at d itself the coefficient is zero by supposition",
						func(e *Argument, atD Fact) {
							e.Show(
								"so p(i) = p(d) = zero",
								atD.Rw(),
								By(leadingZero))
						})
					b.Otherwise(
						"past d, p vanishes",
						func(e *Argument, notD Fact) {
							beyond := e.Have(
								"i is past d",
								"suc(d) ≤ i",
								ByArith(atLeast, notD))
							e.Show(
								"so p(i) = zero",
								By(beyond, past, vec_space.VecDef))
						})
				}))
			below := a.Have(
				"p is not zero and vanishes from d on, so its degree d is below d",
				"d < d",
				By(Normalized, degree, hypotheses, DegreeBelow.At(zero, proof.InhabitFrom(p, from))))
			a.Show(
				"but d is not below itself",
				By(below, nat_order.LessThanIrrefl.At(d)))
		}),
})}

// LeadingCoefficientNonzero — the leading coefficient of a nonzero
// polynomial over c lies in c and is not zero: every coefficient of p lies
// in c, and the one at its degree is not zero (DegreeLeading).
var LeadingCoefficientNonzero = leadingCoefficientNonzeroThm{family.Add(registry.ProofEntry{
	Name: "LeadingCoefficientNonzero",
	Key:  "prop_220a8df2c2911999",
	Build: family.Theorem(Statement{
		Binders: "∀zero:A. ∀c:set(A). ∀p:(num → A).",
		Hypotheses: []string{
			"polynomial_over(zero, c, p)",
			"p ≠ vec_zero(zero)",
		},
		Conclusion: "p(polynomial_degree(zero, p)) ∈ c ∧ p(polynomial_degree(zero, p)) ≠ zero",
	}, func(a *Argument, zero *Expr[A], c *Expr[Set[A]], p *Arrow[Nat, A], over, nonzero Fact) {
		a.Show(
			"every coefficient of p lies in c, and the one at its degree is not zero",
			By(over, nonzero, PolynomialOverDef, DegreeLeading.At(zero, c, p)))
	}),
})}

// FirstNonconstantTerm — a polynomial of positive degree has a first
// nonzero coefficient past the constant one. It is not the zero polynomial,
// whose degree is 0, so its leading coefficient is nonzero (DegreeLeading);
// that index is positive, and well-ordering takes the least such index.
var FirstNonconstantTerm = firstNonconstantTermThm{family.Add(registry.ProofEntry{
	Name: "FirstNonconstantTerm",
	Key:  "prop_358d3b41c3aad085",
	Build: family.Theorem(Statement{
		Binders: "∀zero:A. ∀c:set(A). ∀p:(num → A).",
		Hypotheses: []string{
			"polynomial_over(zero, c, p)",
			"0 < polynomial_degree(zero, p)",
		},
		Conclusion: "∃k:num. 0 < k ∧ p(k) ≠ zero ∧ (∀i:num. 0 < i ∧ i < k ⇒ p(i) = zero)",
	},
		func(a *Argument, zero *Expr[A], c *Expr[Set[A]], p *Arrow[Nat, A], hypotheses Fact) {
			zeroImpossible := a.Have(
				"the zero polynomial cannot have positive degree",
				"p = vec_zero(zero) ⇒ ⊥",
				Derive(func(b *Argument) {
					eq := b.Assume()
					degreeZero := b.Simplified(hypotheses, Fwd(eq), Fwd(DegreeVecZero))
					b.Show(
						"its degree would be zero",
						By(degreeZero))
				}))
			nonzero := a.Have(
				"the coefficient sequence is nonzero",
				"p ≠ vec_zero(zero)",
				By(Normalized, zeroImpossible))
			positive := a.Have(
				"the leading coefficient supplies a positive nonzero index",
				"∃n:num. 0 < n ∧ p(n) ≠ zero",
				Derive(func(b *Argument) {
					b.Take(b.TermAs[Nat]("polynomial_degree(zero, p)"))
					b.Show(
						"the leading coefficient is nonzero",
						By(nonzero, hypotheses, DegreeLeading.At(zero, c, p)))
				}))
			a.Show(
				"take the least positive nonzero coefficient",
				By(positive, nat_order.WellOrdering.At(a.TermAs[Set[Nat]]("λn:num. 0 < n ∧ p(n) ≠ zero"))))
		}),
})}

// DegreeZeroIff — a polynomial has degree zero exactly when it is
// constant: vanishing from 1 = suc(0) on is vanishing past 0, and a
// polynomial vanishes past its degree (DegreeVec), which is the least
// index past which it vanishes (DegreeLeast).
var DegreeZeroIff = degreeZeroIffThm{family.Add(registry.ProofEntry{
	Name: "DegreeZeroIff",
	Key:  "prop_a8dc86f4ba5829c0",
	Build: family.Theorem(Statement{
		Binders: "∀zero:A. ∀c:set(A). ∀p:(num → A).",
		Hypotheses: []string{
			"polynomial_over(zero, c, p)",
		},
		Conclusion: "polynomial_degree(zero, p) = 0 ⇔ vec⟨1⟩(zero, p)",
	},
		func(a *Argument, zero *Expr[A], c *Expr[Set[A]], p *Arrow[Nat, A], poly Fact) {
			a.Do(Simp(Fwd(nat_arith.OneIsSucZero)))
			a.Iff()
			a.Forward(
				"of degree 0, p vanishes past 0",
				func(b *Argument, degreeZero Fact) {
					b.Show(
						"p vanishes past its degree, which is 0",
						By(Normalized, degreeZero, poly, DegreeVec.At(zero, c, p)))
				})
			a.Backward(
				"vanishing past 0, p has degree 0",
				func(b *Argument, constant Fact) {
					b.Show(
						"its degree, the least index past which it vanishes, is at most 0, and a number at most 0 is 0",
						By(
							constant,
							DegreeLeast.At(zero, p, b.TermAs[Nat]("0")),
							nat_order.LessEqZeroClause.At(b.TermAs[Nat]("polynomial_degree(zero, p)"))))
				})
		}),
})}

// DegreeZeroConstant — a polynomial of degree 0 is the constant
// polynomial of its coefficient at 0: it vanishes from 1 on
// (DegreeZeroIff), so off the index 0 both sides are zero, and at 0 the
// constant's coefficient is p(0) * one.
var DegreeZeroConstant = degreeZeroConstantThm{family.Add(registry.ProofEntry{
	Name: "DegreeZeroConstant",
	Key:  "prop_27e4ed764c01ca7d",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀p:(num → A).",
		Hypotheses: []string{
			"polynomial_over(R.carrier, p)",
			"polynomial_degree(p) = 0",
		},
		Conclusion: "p = p(0) • basis_vector(0)",
	},
		func(a *Argument, ring comm_ring.CommRingFact[on.R], p *Arrow[Nat, A], hypotheses Fact) {
			parts := a.Conjuncts(
				hypotheses,
				"p is a polynomial over c",
				"of degree 0")
			pOver, degreeZero := parts[0], parts[1]
			zero, one, c, zeroth :=
				a.TermAs[A]("R.zero"), a.TermAs[A]("R.one"), a.TermAs[Set[A]]("R.carrier"), a.TermAs[Nat]("0")
			constant := a.Have(
				"of degree 0, p vanishes from 1 on",
				"vec⟨1⟩(p)",
				By(pOver, degreeZero, DegreeZeroIff.At(zero, c, p)))
			constantIn := a.Have(
				"its coefficient p(0) lies in c",
				"p(0) ∈ R.carrier",
				By(pOver, PolynomialOverDef.At(zero, c, p)))
			a.Do(Funext())
			a.FixAs[Nat]("i")
			a.Do(Simp(Fwd(vec_space.VecScalarMulDef)))
			a.Cases(a.Term("i = 0"))
			a.When(
				"at 0 the constant's coefficient is p(0) * one, which is p(0)",
				func(b *Argument, atZero Fact) {
					b.Show(
						"the one polynomial is one at 0",
						atZero.Rw(),
						ByArith(ring, constantIn, vec_space.BasisVectorDef.At(zero, one, zeroth, zeroth)))
				})
			a.Otherwise(
				"past 0 p vanishes, and the constant's coefficient is p(0) * zero",
				func(b *Argument, offZero Fact) {
					vanishes := b.Have(
						"p(i) is zero",
						"p(i) = R.zero",
						ByArith(offZero, constant, vec_space.VecDef))
					b.Show(
						"so both sides are zero",
						Simp(Fwd(vec_space.BasisVectorDef), Fwd(comm_ring.MulRightZeroOn.Read(ring))),
						By(vanishes))
				})
		}),
})}

// MonicDegreeZero — a monic polynomial of degree 0 is the one
// polynomial: it is the constant polynomial of p(0) (DegreeZeroConstant),
// and p(0), its coefficient at its degree 0, is one.
var MonicDegreeZero = monicDegreeZeroThm{family.Add(registry.ProofEntry{
	Name: "MonicDegreeZero",
	Key:  "prop_4092f52fcc5704df",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀p:(num → A).",
		Hypotheses: []string{
			"polynomial_over(R.carrier, p)",
			"polynomial_monic(p)",
			"polynomial_degree(p) = 0",
		},
		Conclusion: "p = basis_vector(0)",
	},
		func(a *Argument, ring comm_ring.CommRingFact[on.R], p *Arrow[Nat, A], hypotheses Fact) {
			parts := a.Conjuncts(
				hypotheses,
				"p is a polynomial over c",
				"monic",
				"of degree 0")
			pOver, monic, degreeZero := parts[0], parts[1], parts[2]
			zero, one, c := a.TermAs[A]("R.zero"), a.TermAs[A]("R.one"), a.TermAs[Set[A]]("R.carrier")
			onePolynomial := a.TermAs[Fun[Nat, A]]("basis_vector(0)")
			oneCoefficients := a.Have(
				"every coefficient of the one polynomial lies in c",
				"∀i:num. basis_vector(0, i) ∈ R.carrier",
				By(BasisVectorOver.Read(ring).At(a.TermAs[Nat]("0")), PolynomialOverDef.At(zero, c, onePolynomial)))
			a.Show(
				"p is the constant polynomial of p(0), and p(0) is one",
				CalcEq(
					Leg(
						a.TermAs[Fun[Nat, A]]("p(0) • basis_vector(0)"),
						"of degree 0, p is the constant polynomial of p(0)",
						By(pOver, degreeZero, DegreeZeroConstant.Read(ring).At(p))),
					Leg(
						a.TermAs[Fun[Nat, A]]("R.one • basis_vector(0)"),
						"p(0), its coefficient at its degree 0, is one",
						By(Normalized, monic, degreeZero, PolynomialMonicDef.At(zero, one, p))),
					FinalLeg(
						"and one scales nothing",
						By(oneCoefficients, vec_space.SmulOneOn.Read(ring).At(onePolynomial))),
				))
		}),
})}

// MonicNonzero — a monic polynomial is not the zero polynomial: its
// coefficient at its degree is one, every coefficient of vec_zero is
// zero, and in a domain one is not zero.
var MonicNonzero = monicNonzeroThm{family.Add(registry.ProofEntry{
	Name: "MonicNonzero",
	Key:  "prop_1b9d361935ebfa59",
	Reading: "Of the domain only R.one ≠ R.zero is used: in the zero ring " +
		"vec_zero is monic, its coefficient at its degree being R.zero, which is one.",
	Build: integral_domain.IntegralDomainOn.Law(Statement{
		Binders: "∀p:(num → A).",
		Hypotheses: []string{
			"polynomial_monic(p)",
		},
		Conclusion: "p ≠ vec_zero",
	},
		func(a *Argument, domain integral_domain.IntegralDomainFact[on.R], p *Arrow[Nat, A], monic Fact) {
			zero, one := a.TermAs[A]("R.zero"), a.TermAs[A]("R.one")
			a.Show(
				"were p zero, its coefficient one at its degree would be zero",
				By(
					Normalized,
					monic,
					PolynomialMonicDef.At(zero, one, p),
					vec_space.VecZeroDef.At(zero, a.TermAs[Nat]("polynomial_degree(p)")),
					integral_domain.OneNotZero.Read(domain)))
		}),
})}

// DegreeBasisVector — the k-th power of the variable has degree k, over
// a ring whose one is not zero: it vanishes past k, and its coefficient at
// k is one.
var DegreeBasisVector = degreeBasisVectorThm{family.Add(registry.ProofEntry{
	Name: "DegreeBasisVector",
	Key:  "prop_ec9f447b963af2f2",
	Reading: "one ≠ zero is load-bearing: in the zero ring " +
		"basis_vector(k) is the zero polynomial, of degree 0.",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀k:num.",
		Hypotheses: []string{
			"R.one ≠ R.zero",
		},
		Conclusion: "polynomial_degree(basis_vector(k)) = k",
	},
		func(a *Argument, ring comm_ring.CommRingFact[on.R], k *Expr[Nat], oneNonzero Fact) {
			zero, one := a.TermAs[A]("R.zero"), a.TermAs[A]("R.one")
			vanishes := a.Have(
				"the basis vector vanishes past k",
				"vec⟨suc(k)⟩(basis_vector(k))",
				By(
					nat_order.LessEqRefl.At(k),
					nat_order.LessThanSucIffLessEq.At(k, k),
					vec_space.VecBasisVector.At(zero, one, a.TermAs[Nat]("suc(k)"), k)))
			coefficientNonzero := a.Have(
				"its kth coefficient is the ring's one, which is not zero",
				"basis_vector(k, k) ≠ R.zero",
				By(Normalized, oneNonzero, vec_space.BasisVectorDef.At(zero, one, k, k)))
			a.Show(
				"so its degree is exactly k",
				By(
					vanishes,
					coefficientNonzero,
					BasisVectorOver.Read(ring).At(k),
					DegreeExact.At(zero, a.TermAs[Set[A]]("R.carrier"), a.TermAs[Fun[Nat, A]]("basis_vector(k)"), k)))
		}),
})}

// LeadingCoefficientMul — the coefficient of a product at the sum of the
// degrees is the product of the leading coefficients. With m and n the
// degrees, the coefficient at m + n is the sum of p(i) * q(m + n - i) over
// i ≤ m + n, and every term but the one at m has a factor zero: p(i) past
// m, and q(m + n - i) below m, where m + n - i is past n. The sum is its
// term at m (ModuleSumSingle), p(m) * q(n).
var LeadingCoefficientMul = leadingCoefficientMulThm{family.Add(registry.ProofEntry{
	Name: "LeadingCoefficientMul",
	Key:  "prop_63bdec630df3b492",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀p q:(num → A).",
		Hypotheses: []string{
			"polynomial_over(R.carrier, p)",
			"polynomial_over(R.carrier, q)",
		},
		Conclusion: "polynomial_mul(p, q, polynomial_degree(p) + polynomial_degree(q)) = " +
			"p(polynomial_degree(p)) * q(polynomial_degree(q))",
	},
		func(a *Argument, ring comm_ring.CommRingFact[on.R], p, q *Arrow[Nat, A], over Fact) {
			regular := module.RegularModuleOn.Read(ring)
			zero, c := a.TermAs[A]("R.zero"), a.TermAs[Set[A]]("R.carrier")
			mDegree := a.Let("m", a.Term("polynomial_degree(p)"))
			nDegree := a.Let("n", a.Term("polynomial_degree(q)"))
			pPast := a.Have(
				"p vanishes past its degree m",
				"vec⟨suc(m)⟩(p)",
				By(Normalized, mDegree, over, DegreeVec.At(zero, c, p)))
			qPast := a.Have(
				"and q past its degree n",
				"vec⟨suc(n)⟩(q)",
				By(Normalized, nDegree, over, DegreeVec.At(zero, c, q)))
			coefficients := a.Have(
				"every coefficient of p and of q lies in c",
				"∀i:num. p(i) ∈ R.carrier ∧ q(i) ∈ R.carrier",
				By(over, PolynomialOverDef))
			terms := a.Have(
				"and so does every term p(i) * q(m + n - i) of the coefficient at m + n",
				"∀i:num. p(i) * q(m + n - i) ∈ R.carrier",
				By(coefficients, comm_ring.MulIn.Read(ring)))
			vanish := a.Have(
				"off the index m every term has a factor zero",
				"∀i:num. i ≠ m ⇒ p(i) * q(m + n - i) = R.zero",
				Derive(func(b *Argument) {
					b.FixAs[Nat]("i")
					offM := b.Assume()
					b.Cases(b.Term("i < m"))
					b.When(
						"below m, m + n - i is past n, so the factor q(m + n - i) is zero",
						func(d *Argument, below Fact) {
							qZero := d.Have(
								"q vanishes at m + n - i",
								"q(m + n - i) = R.zero",
								ByArith(below, qPast, vec_space.VecDef))
							d.Show(
								"and p(i) * R.zero = R.zero",
								qZero.Rw(),
								By(comm_ring.MulRightZeroOn.Read(ring), coefficients))
						})
					b.Otherwise(
						"past m, the factor p(i) is zero",
						func(d *Argument, notBelow Fact) {
							pZero := d.Have(
								"p vanishes at i",
								"p(i) = R.zero",
								ByArith(notBelow, offM, pPast, vec_space.VecDef))
							d.Show(
								"and R.zero * q(m + n - i) = R.zero",
								pZero.Rw(),
								By(comm_ring.MulLeftZeroOn.Read(ring), coefficients))
						})
				}))
			m, n := a.TermAs[Nat]("m"), a.TermAs[Nat]("n")
			indices, term :=
				a.TermAs[Set[Nat]]("{i:num | i ≤ m + n}"), a.TermAs[Fun[Nat, A]]("λi:num. p(i) * q(m + n - i)")
			mAmong := a.Have(
				"m is one of the indices up to m + n",
				"m ∈ {i:num | i ≤ m + n}",
				BySets(nat_order.LessEqAdd.At(m, n)))
			leavesN := a.Have(
				"taking m from m + n leaves n",
				"m + n - m = n",
				ByArith())
			a.Show(
				"so the coefficient at m + n is its one term at m",
				Simp(Fwd(PolynomialMulDef)),
				CalcEq(
					Leg(
						a.TermAs[A]("p(m) * q(m + n - m)"),
						"the terms off the index m vanish, so the sum over the indices "+
							"up to m + n is its term at m, the ring a module over itself",
						By(
							terms,
							vanish,
							mAmong,
							num_segment.FiniteBelow.At(a.TermAs[Nat]("m + n")),
							module.ModuleSumSingle.Read(regular).At(indices, m, term))),
					FinalLeg(
						"taking m from m + n leaves n",
						By(Normalized, leavesN)),
				))
		}),
})}

// PolynomialMulVec — the degree bound of a product, stated by vanishing:
// p vanishes past m and q past n, so their product vanishes past m + n.
// At an index k past m + n every term p(i) * q(k - i) of the coefficient
// has a factor zero: q(k - i) when i ≤ m, as k - i is then past n, and
// p(i) when i is past m. The coefficient is a finite sum of zeros.
var PolynomialMulVec = polynomialMulVecThm{family.Add(registry.ProofEntry{
	Name: "PolynomialMulVec",
	Key:  "prop_517fe80c8375e3b3",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀m n:num. ∀p q:(num → A).",
		Hypotheses: []string{
			"polynomial_over(R.carrier, p)",
			"polynomial_over(R.carrier, q)",
			"vec⟨suc(m)⟩(p)",
			"vec⟨suc(n)⟩(q)",
		},
		Conclusion: "vec⟨suc(m + n)⟩(polynomial_mul(p, q))",
	},
		func(
			a *Argument,
			ring comm_ring.CommRingFact[on.R],
			m, n *Expr[Nat],
			p, q *Arrow[Nat, A],
			hypotheses Fact,
		) {
			parts := a.Conjuncts(
				hypotheses,
				"p is a polynomial over c",
				"so is q",
				"p vanishes past m",
				"and q past n")
			pOver, qOver, pVec, qVec := parts[0], parts[1], parts[2], parts[3]
			coefficients := a.Have(
				"every coefficient of p and of q lies in c",
				"∀i:num. p(i) ∈ R.carrier ∧ q(i) ∈ R.carrier",
				By(pOver, qOver, PolynomialOverDef))
			a.Do(Simp(Fwd(vec_space.VecDef), Fwd(PolynomialMulDef)))
			k := a.FixAs[Nat]("k")
			past := a.Assume()
			terms := a.Have(
				"every term p(i) * q(k - i) has a factor zero",
				"∀i:num. p(i) * q(k - i) = R.zero",
				Derive(func(b *Argument) {
					b.FixAs[Nat]("i")
					b.Cases(b.Term("i ≤ m"))
					b.When(
						"up to m, k - i is past n, so the factor q(k - i) is zero",
						func(d *Argument, upTo Fact) {
							qZero := d.Have(
								"q vanishes at k - i",
								"q(k - i) = R.zero",
								ByArith(upTo, past, qVec, vec_space.VecDef))
							d.Show(
								"and p(i) * R.zero = R.zero",
								qZero.Rw(),
								By(comm_ring.MulRightZeroOn.Read(ring), coefficients))
						})
					b.Otherwise(
						"past m, the factor p(i) is zero",
						func(d *Argument, beyond Fact) {
							pZero := d.Have(
								"p vanishes at i",
								"p(i) = R.zero",
								ByArith(beyond, pVec, vec_space.VecDef))
							d.Show(
								"and R.zero * q(k - i) = R.zero",
								pZero.Rw(),
								By(comm_ring.MulLeftZeroOn.Read(ring), coefficients))
						})
				}))
			a.Show(
				"so the coefficient at k is a finite sum of zeros, the ring a module over itself",
				By(
					terms,
					module.ModuleSumZero.Read(module.RegularModuleOn.Read(ring)).At(
						a.TermAs[Set[Nat]]("{i:num | i ≤ k}"), a.TermAs[Fun[Nat, A]]("λi:num. p(i) * q(k - i)")),
					num_segment.FiniteBelow.At(k)))
		}),
})}

// DegreeMulLe — a product has degree at most the sum of the degrees: p
// vanishes past its degree and q past its own, so the product vanishes
// past their sum (PolynomialMulVec), and its degree, the least index past
// which it vanishes, is at most that sum.
var DegreeMulLe = degreeMulLeThm{family.Add(registry.ProofEntry{
	Name: "DegreeMulLe",
	Key:  "prop_3d85d48257fae278",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀p q:(num → A).",
		Hypotheses: []string{
			"polynomial_over(R.carrier, p)",
			"polynomial_over(R.carrier, q)",
		},
		Conclusion: "polynomial_degree(polynomial_mul(p, q)) ≤ polynomial_degree(p) + polynomial_degree(q)",
	},
		func(a *Argument, ring comm_ring.CommRingFact[on.R], p, q *Arrow[Nat, A], over Fact) {
			zero, c := a.TermAs[A]("R.zero"), a.TermAs[Set[A]]("R.carrier")
			m, n := a.TermAs[Nat]("polynomial_degree(p)"), a.TermAs[Nat]("polynomial_degree(q)")
			vanishes := a.Have(
				"p and q vanish past their degrees, so the product vanishes past the sum of the degrees",
				"vec⟨suc(polynomial_degree(p) + polynomial_degree(q))⟩(polynomial_mul(p, q))",
				By(
					over,
					DegreeVec.At(zero, c, p),
					DegreeVec.At(zero, c, q),
					PolynomialMulVec.Read(ring).At(m, n, p, q)))
			a.Show(
				"the degree of the product is at most any index past which it vanishes",
				By(
					vanishes,
					DegreeLeast.At(
						zero,
						a.TermAs[Fun[Nat, A]]("polynomial_mul(p, q)"),
						a.TermAs[Nat]("polynomial_degree(p) + polynomial_degree(q)"))))
		}),
})}

// LeadingCoefficientMulNonzero — over an integral domain the product of
// two nonzero polynomials has a nonzero coefficient at the sum of their
// degrees. With m and n the degrees of p and q, that coefficient is
// p(m) * q(n), the product of the leading coefficients
// (LeadingCoefficientMul); neither leading coefficient is zero, p and q
// being nonzero (DegreeLeading), and a domain has no zero divisors.
var LeadingCoefficientMulNonzero = leadingCoefficientMulNonzeroThm{family.Add(registry.ProofEntry{
	Name: "LeadingCoefficientMulNonzero",
	Key:  "prop_252e1aaa98972f4a",
	Reading: "The domain is load-bearing: over ℤ/4, (2x + 1)² = 1 has coefficient zero at 2. " +
		"Both nonzero hypotheses are too: the zero polynomial has degree 0 and no nonzero coefficient.",
	Build: integral_domain.IntegralDomainOn.Law(Statement{
		Binders: "∀p q:(num → A).",
		Hypotheses: []string{
			"polynomial_over(R.carrier, p)",
			"polynomial_over(R.carrier, q)",
			"p ≠ vec_zero",
			"q ≠ vec_zero",
		},
		Conclusion: "polynomial_mul(p, q, polynomial_degree(p) + polynomial_degree(q)) ≠ R.zero",
	},
		func(
			a *Argument,
			domain integral_domain.IntegralDomainFact[on.R],
			p, q *Arrow[Nat, A],
			hypotheses Fact,
		) {
			ring := integral_domain.Ring.Read(domain)
			zero, c := a.TermAs[A]("R.zero"), a.TermAs[Set[A]]("R.carrier")
			mDegree := a.Let("m", a.Term("polynomial_degree(p)"))
			nDegree := a.Let("n", a.Term("polynomial_degree(q)"))
			leading := a.Have(
				"the coefficient at m + n is the product of the leading coefficients",
				"polynomial_mul(p, q, m + n) = p(m) * q(n)",
				By(Normalized, mDegree, nDegree, hypotheses, LeadingCoefficientMul.Read(ring).At(p, q)))
			pNonzero := a.Have(
				"p is not zero, so neither is its leading coefficient",
				"p(m) ≠ R.zero",
				By(Normalized, mDegree, hypotheses, DegreeLeading.At(zero, c, p)))
			qNonzero := a.Have(
				"nor is q's",
				"q(n) ≠ R.zero",
				By(Normalized, nDegree, hypotheses, DegreeLeading.At(zero, c, q)))
			pIn := a.Have(
				"p's leading coefficient lies in c",
				"p(m) ∈ R.carrier",
				By(hypotheses, PolynomialOverDef.At(zero, c, p)))
			qIn := a.Have(
				"and so does q's",
				"q(n) ∈ R.carrier",
				By(hypotheses, PolynomialOverDef.At(zero, c, q)))
			pLeading, qLeading :=
				a.MemberOf[on.R](a.TermAs[A]("p(m)"), pIn), a.MemberOf[on.R](a.TermAs[A]("q(n)"), qIn)
			vanishing := a.SupposeNot()
			factorZero := a.Have(
				"were that coefficient zero, so would be p(m) or q(n), the domain having no zero divisors",
				"p(m) = R.zero ∨ q(n) = R.zero",
				By(
					mDegree,
					nDegree,
					vanishing,
					leading,
					integral_domain.NoZeroDivisors.Read(domain).At(pLeading, qLeading)))
			a.Show(
				"but neither leading coefficient is zero",
				By(factorZero, pNonzero, qNonzero))
		}),
})}

// DegreeMul — over an integral domain degrees add. With m and n the
// degrees of p and q, the product has degree at most m + n (DegreeMulLe);
// it vanishes past its own degree, and its coefficient at m + n is not
// zero (LeadingCoefficientMulNonzero), so that degree is not below m + n.
var DegreeMul = degreeMulThm{family.Add(registry.ProofEntry{
	Name: "DegreeMul",
	Key:  "prop_eb5e08bb7ecd9626",
	Reading: "The domain is load-bearing: over ℤ/4, (2x + 1)² = 1. Both " +
		"nonzero hypotheses are too, the zero polynomial having degree 0.",
	Build: integral_domain.IntegralDomainOn.Law(Statement{
		Binders: "∀p q:(num → A).",
		Hypotheses: []string{
			"polynomial_over(R.carrier, p)",
			"polynomial_over(R.carrier, q)",
			"p ≠ vec_zero",
			"q ≠ vec_zero",
		},
		Conclusion: "polynomial_degree(polynomial_mul(p, q)) = polynomial_degree(p) + polynomial_degree(q)",
	},
		func(
			a *Argument,
			domain integral_domain.IntegralDomainFact[on.R],
			p, q *Arrow[Nat, A],
			hypotheses Fact,
		) {
			ring := integral_domain.Ring.Read(domain)
			zero, c := a.TermAs[A]("R.zero"), a.TermAs[Set[A]]("R.carrier")
			product := a.TermAs[Fun[Nat, A]]("polynomial_mul(p, q)")
			mDegree := a.Let("m", a.Term("polynomial_degree(p)"))
			nDegree := a.Let("n", a.Term("polynomial_degree(q)"))
			atMost := a.Have(
				"the product has degree at most m + n",
				"polynomial_degree(polynomial_mul(p, q)) ≤ m + n",
				By(mDegree, nDegree, hypotheses, DegreeMulLe.Read(ring).At(p, q)))
			leading := a.Have(
				"its coefficient at m + n is not zero",
				"polynomial_mul(p, q, m + n) ≠ R.zero",
				By(Normalized, mDegree, nDegree, hypotheses, LeadingCoefficientMulNonzero.Read(domain).At(p, q)))
			vanishes := a.Have(
				"the product, a polynomial over c, vanishes past its degree",
				"vec⟨suc(polynomial_degree(polynomial_mul(p, q)))⟩(polynomial_mul(p, q))",
				By(hypotheses, PolynomialMulOver.Read(ring).At(p, q), DegreeVec.At(zero, c, product)))
			atLeast := a.Have(
				"so its degree is at least m + n",
				"m + n ≤ polynomial_degree(polynomial_mul(p, q))",
				Derive(func(b *Argument) {
					below := b.SupposeNot()
					coefficientZero := b.Have(
						"were the degree below m + n, the coefficient at m + n would vanish",
						"polynomial_mul(p, q, m + n) = R.zero",
						ByArith(below, vanishes, vec_space.VecDef))
					b.Show(
						"but it does not",
						By(coefficientZero, leading))
				}))
			a.Show(
				"so the degree of the product is m + n",
				ByArith(atMost, atLeast))
		}),
})}

// PolynomialDomain — over an integral domain the polynomials form one:
// they form a commutative ring (PolynomialRingOn); the one polynomial
// basis_vector(0) is not zero, its coefficient at 0 being one; and a
// product of nonzero polynomials is not zero, its coefficient at the sum
// of their degrees not being zero (LeadingCoefficientMulNonzero).
var PolynomialDomain = polynomialDomainThm{family.Add(registry.ProofEntry{
	Name: "PolynomialDomain",
	Key:  "prop_cb1abc5950eeafa0",
	Build: integral_domain.IntegralDomainOn.Law("integral_domain_on(polynomial_ring(R))",
		func(a *Argument, domain integral_domain.IntegralDomainFact[on.R]) {
			ring := integral_domain.Ring.Read(domain)
			zero, one, zeroth := a.TermAs[A]("R.zero"), a.TermAs[A]("R.one"), a.TermAs[Nat]("0")
			oneNonzero := a.Have(
				"the one polynomial is not zero: its coefficient at 0 is R.one, which is not R.zero",
				"basis_vector(0) ≠ vec_zero",
				By(
					Normalized,
					integral_domain.OneNotZero.Read(domain),
					vec_space.BasisVectorDef.At(zero, one, zeroth, zeroth),
					vec_space.VecZeroDef.At(zero, zeroth)))
			noZeroDivisors := a.Have(
				"a vanishing product of polynomials over the domain has a vanishing factor",
				Statement{
					Binders: "∀p q:(num → A).",
					Hypotheses: []string{
						"polynomial_over(R.carrier, p)",
						"polynomial_over(R.carrier, q)",
						"polynomial_mul(p, q) = vec_zero",
					},
					Conclusion: "p = vec_zero ∨ q = vec_zero",
				},
				Derive(func(b *Argument) {
					p := b.FixAs[Fun[Nat, A]]("p")
					q := b.FixAs[Fun[Nat, A]]("q")
					hypotheses := b.Assume()
					neither := b.SupposeNot()
					leading := b.Have(
						"were neither factor zero, the product's coefficient at the sum of their degrees would not be zero",
						"polynomial_mul(p, q, polynomial_degree(p) + polynomial_degree(q)) ≠ R.zero",
						By(hypotheses, neither, LeadingCoefficientMulNonzero.Read(domain).At(p, q)))
					b.Show(
						"but the product is zero, and so is each of its coefficients",
						By(
							hypotheses,
							leading,
							vec_space.VecZeroDef.At(zero, b.TermAs[Nat]("polynomial_degree(p) + polynomial_degree(q)"))))
				}))
			a.Show(
				"the polynomials form a commutative ring, which with "+
					"these two gives the three conditions of a domain",
				By(
					PolynomialRingOn.Read(ring),
					oneNonzero,
					noZeroDivisors,
					integral_domain.IntegralDomainOn.At(a.TermAs[RingOps[Fun[Nat, A]]]("polynomial_ring(R)"))))
		}),
})}

// DegreeScalar — over an integral domain a nonzero scalar keeps the
// degree. The degree is read off the indices past which a sequence
// vanishes, and a • p vanishes exactly where p does: a * zero = zero, and
// a * p(i) = zero with a ≠ zero forces p(i) = zero in a domain.
var DegreeScalar = degreeScalarThm{family.Add(registry.ProofEntry{
	Name: "DegreeScalar",
	Key:  "prop_a6f08da46d0452c2",
	Build: integral_domain.IntegralDomainOn.Law(Statement{
		Binders: "∀a:A. ∀p:(num → A).",
		Hypotheses: []string{
			"a ∈ R.carrier",
			"a ≠ R.zero",
			"polynomial_over(R.carrier, p)",
		},
		Conclusion: "polynomial_degree(a • p) = polynomial_degree(p)",
	},
		func(
			arg *Argument,
			domain integral_domain.IntegralDomainFact[on.R],
			a *Expr[A],
			p *Arrow[Nat, A],
			hypotheses Fact,
		) {
			parts := arg.Conjuncts(
				hypotheses,
				"a lies in c",
				"a is not zero",
				"p is a polynomial over c")
			aIn, aNonzero, pOver := parts[0], parts[1], parts[2]
			zero, c := arg.TermAs[A]("R.zero"), arg.TermAs[Set[A]]("R.carrier")
			scalar := arg.MemberOf[on.R](a, aIn)
			sameZeros := arg.Have(
				"a * p(i) is zero exactly where p(i) is",
				"∀i:num. a * p(i) = R.zero ⇔ p(i) = R.zero",
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]("i")
					coefficientIn := b.Have(
						"p(i) lies in c",
						"p(i) ∈ R.carrier",
						By(pOver, PolynomialOverDef.At(zero, c, p)))
					coefficient := b.MemberOf[on.R](p.Apply(i), coefficientIn)
					b.Iff()
					b.Forward(
						"a zero product a * p(i) of members of the domain has a zero factor",
						func(d *Argument, product Fact) {
							d.Show(
								"and the factor a is not zero, so p(i) is",
								By(product, aNonzero, integral_domain.NoZeroDivisors.Read(domain).At(scalar, coefficient)))
						})
					b.Backward(
						"where p(i) is zero, a * p(i) is a * zero",
						func(d *Argument, vanishes Fact) {
							d.Show(
								"which is zero in the ring",
								vanishes.Rw(),
								By(comm_ring.MulRightZeroOn.Read(integral_domain.Ring.Read(domain)).At(scalar)))
						})
				}))
			arg.Show(
				"the degree is the least index past which a sequence "+
					"vanishes, and a • p vanishes past the same indices as p",
				Unfold(PolynomialDegreeDef),
				Simp(Fwd(vec_space.VecDef), Fwd(vec_space.VecScalarMulDef)),
				By(sameZeros))
		}),
})}

// MonicMultiple — over a field a nonzero polynomial scaled by the
// inverse a of its leading coefficient is a monic polynomial over c of
// the same degree: a is a nonzero member of c, so a • p is over c and
// keeps the degree (DegreeScalar), and its coefficient there is
// a * p(n) = one.
var MonicMultiple = monicMultipleThm{family.Add(registry.ProofEntry{
	Name: "MonicMultiple",
	Key:  "prop_a9c451884e146ce7",
	Build: field.FieldOn.Law(Statement{
		Binders: "∀p:(num → A).",
		Hypotheses: []string{
			"polynomial_over(F.carrier, p)",
			"p ≠ vec_zero",
		},
		Conclusion: "polynomial_over(F.carrier, F.inv(p(polynomial_degree(p))) • p) ∧ " +
			"polynomial_monic(F.inv(p(polynomial_degree(p))) • p) ∧ " +
			"polynomial_degree(F.inv(p(polynomial_degree(p))) • p) = polynomial_degree(p)",
	},
		func(a *Argument, fieldOn field.FieldFact[on.F], p *Arrow[Nat, A], hypotheses Fact) {
			parts := a.Conjuncts(
				hypotheses,
				"p is a polynomial over c",
				"p is not zero")
			pOver, pNonzero := parts[0], parts[1]
			zero, c := a.TermAs[A]("F.zero"), a.TermAs[Set[A]]("F.carrier")
			nDegree := a.Let("n", a.Term("polynomial_degree(p)"))
			leadNonzero := a.Have(
				"p is not zero, so its leading coefficient p(n) is not zero",
				"p(n) ≠ F.zero",
				By(Normalized, nDegree, pOver, pNonzero, DegreeLeading.At(zero, c, p)))
			leadIn := a.Have(
				"p(n) lies in c",
				"p(n) ∈ F.carrier",
				By(pOver, PolynomialOverDef.At(zero, c, p)))
			lead := a.MemberOf[on.F](a.TermAs[A]("p(n)"), leadIn)
			scalar := a.Let("a", a.Term("F.inv(p(n))"))
			aIn := a.Have(
				"a lies in c",
				"a ∈ F.carrier",
				scalar.Rw(),
				By(field.InvIn.Read(fieldOn).At(lead)))
			aNonzero := a.Have(
				"a is not zero",
				"a ≠ F.zero",
				scalar.Rw(),
				By(leadNonzero, field.InvEqZeroOn.Read(fieldOn).At(lead)))
			inverts := a.Have(
				"a inverts p(n)",
				"a * p(n) = F.one",
				scalar.Rw(),
				By(leadNonzero, field.MulLeftInverseOn.Read(fieldOn).At(lead)))
			scaledDegree := a.Have(
				"a • p has p's degree n, a being a nonzero scalar",
				"polynomial_degree(a • p) = n",
				By(
					nDegree,
					aNonzero,
					pOver,
					DegreeScalar.Read(integral_domain.FieldIntegralDomain.Read(fieldOn)).At(
						a.MemberOf[on.F](a.TermAs[A]("a"), aIn), p)))
			a.Show(
				"a • p is over c, monic and of degree n",
				SplitConjAll(
					Case(
						"a • p is a polynomial over c, which form a module over the field",
						BySets(aIn, pOver, module.SmulIn.Read(PolynomialModuleOn.Read(field.RingOn.Read(fieldOn))))),
					Case(
						"a • p is monic: its coefficient at n is a * p(n) = F.one",
						Simp(Fwd(PolynomialMonicDef)),
						scaledDegree.Rw(),
						Simp(Fwd(vec_space.VecScalarMulDef)),
						By(inverts)),
					Case(
						"and of degree n",
						By(scaledDegree)),
				))
		}),
})}

// DegreePow — over an integral domain the degree of a power is the
// exponent times the degree. By induction on the exponent: at each next
// power a zero p leaves the zero polynomial on both sides, and a nonzero
// p has nonzero powers, the polynomials forming a domain, so degrees add.
var DegreePow = degreePowThm{family.Add(registry.ProofEntry{
	Name: "DegreePow",
	Reading: "The domain is load-bearing: over ℤ/4, (2t)² " +
		"= 4t² is the zero polynomial, of degree 0, not 2.",
	Key: "prop_44f5666609f62420",
	Build: integral_domain.IntegralDomainOn.Law(Statement{
		Binders: "∀n:num. ∀p:(num → A).",
		Hypotheses: []string{
			"polynomial_over(R.carrier, p)",
		},
		Conclusion: "polynomial_degree(polynomial_pow(p, n)) = n * polynomial_degree(p)",
	},
		func(
			a *Argument,
			domain integral_domain.IntegralDomainFact[on.R],
			n *Expr[Nat],
			p *Arrow[Nat, A],
			over Fact,
		) {
			ring := integral_domain.Ring.Read(domain)
			polynomials := PolynomialDomain.Read(domain)
			nonzeroPowers := a.Have(
				"the powers of a nonzero p are not zero",
				"∀m:num. p ≠ vec_zero ⇒ polynomial_pow(p, m) ≠ vec_zero",
				Derive(func(b *Argument) {
					m := b.FixAs[Nat]("m")
					pNonzero := b.Assume()
					b.Induct(m)
					b.Base(
						"the zeroth power is the one polynomial, which is not zero in the domain of polynomials",
						By(integral_domain.OneNotZero.Read(polynomials), PolynomialPowZero.Read(ring).At(p)))
					b.Step(
						"a vanishing product of polynomials over the domain has a "+
							"vanishing factor, and neither p nor its m-th power is zero",
						func(c *Argument, previous Fact) {
							c.Show(
								"so the next power, their product, is not zero",
								By(
									pNonzero,
									previous,
									over,
									PolynomialPowSuc.Read(ring).At(m, p),
									PolynomialPowOver.Read(ring).At(m, p),
									integral_domain.NoZeroDivisors.Read(polynomials).AsFact().At(
										p, c.TermAs[Fun[Nat, A]]("polynomial_pow(p, m)"))))
						})
				}))
			a.Induct(n)
			a.Base(
				"the zeroth power is the one polynomial, of degree 0 as one is not zero",
				ByArith(
					integral_domain.OneNotZero.Read(domain),
					PolynomialPowZero.Read(ring).At(p),
					DegreeBasisVector.Read(ring).At(a.TermAs[Nat]("0"))))
			a.Step(
				"the next power is p times the n-th",
				func(b *Argument, previous Fact) {
					power := b.TermAs[Fun[Nat, A]]("polynomial_pow(p, n)")
					product := PolynomialPowSuc.Read(ring).At(n, p)
					powerOver := PolynomialPowOver.Read(ring).At(n, p)
					b.Cases(b.Term("p = vec_zero"))
					b.When(
						"a zero p leaves the zero polynomial on both sides",
						func(c *Argument, isZero Fact) {
							vanishes := c.Have(
								"the next power is zero times the n-th, a polynomial over R.carrier",
								"polynomial_pow(p, suc(n)) = vec_zero",
								By(
									isZero,
									over,
									product,
									powerOver,
									comm_ring.MulLeftZeroOn.Read(PolynomialRingOn.Read(ring)).AsFact().At(power)))
							c.Show(
								"and the zero polynomial has degree 0",
								vanishes.Rw(),
								isZero.Rw(),
								ByArith(DegreeVecZero.At(c.TermAs[A]("R.zero"))))
						})
					b.Otherwise(
						"a nonzero p has a nonzero n-th power, so the degrees of the two factors add",
						func(c *Argument, pNonzero Fact) {
							c.Show(
								"to the degree of p plus n times it",
								ByArith(
									pNonzero,
									nonzeroPowers.At(n),
									previous,
									over,
									product,
									powerOver,
									DegreeMul.Read(domain).AsFact().At(p, power)))
						})
				})
		}),
})}
