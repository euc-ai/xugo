// encoding.go — writing a polynomial's coefficients into a block, slot by
// slot, and decoding that block back to the polynomial; and writing a family
// of k polynomials into k consecutive blocks, each member over the
// environment the earlier ones left.

package polynomial_encoding

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_algebra"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// DecodeEncode — decoding the block a polynomial supported in the bounded monomials was encoded in
// gives the polynomial back: a bounded monomial m has its slot inside the block, the encoding writes
// there the coefficient of the bounded monomial at that slot, and that monomial is m, since distinct
// bounded monomials have distinct slots; off the bounded monomials both sides are zero, the decoding
// by definition and p because its support lies in the bounded monomials.
var DecodeEncode = decodeEncodeThm{family.Add(registry.ProofEntry{
	Name: "DecodeEncode",
	Key:  "prop_65aeebe823ded5a7",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀n d c:num. ∀p:((num → num) → A). ∀ρ:(num → A).",
		Hypotheses: []string{
			"fun_support(R.zero, p) ⊆ bounded_monomials(n, d)",
		},
		Conclusion: "decode_polynomial(R, n, d, c, encode_polynomial(n, d, c, p, ρ)) = p",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			n, d, c *Expr[Nat],
			p *Arrow[_Monomial, A],
			ρ *Arrow[Nat, A],
			supported Fact,
		) {
			slots := a.Conjuncts(
				MonomialSlots.At(n, d),
				"the listing is distinct",
				"it lists the bounded monomials",
				"the slot of a bounded monomial lies below the coefficient count",
				"distinct bounded monomials have distinct slots")
			a.Do(Funext())
			m := a.FixAs[_Monomial]("m")
			a.Cases(a.Term("m ∈ bounded_monomials(n, d)"))
			a.When(
				"a bounded monomial is read back from its own slot",
				func(b *Argument, bounded Fact) {
					inBlock := b.Have(
						"the slot of m lies in the block",
						"c ≤ c + monomial_slot(n, d, m) ∧ c + monomial_slot(n, d, m) < c + coefficient_count(n, d)",
						ByArith(bounded, slots[2].At(m)))
					offset := b.Have(
						"the slot of m is its offset in the block",
						"c + monomial_slot(n, d, m) - c = monomial_slot(n, d, m)",
						ByArith())
					_, chosen := b.ObtainChosen(
						"choose a bounded monomial at the slot of m, m being one",
						"∃k:(num → num). k ∈ bounded_monomials(n, d) ∧ monomial_slot(n, d, k) = monomial_slot(n, d, m)",
						bounded)
					readBack := b.Have(
						"the chosen monomial is m, distinct bounded monomials having distinct slots",
						"(εk:(num → num). "+
							"    k ∈ bounded_monomials(n, d) ∧ monomial_slot(n, d, k) = monomial_slot(n, d, m)) = "+
							"m",
						By(
							bounded,
							chosen,
							slots[3],
							functions.InjectiveOnDef.At(
								b.TermAs[Set[_Monomial]]("bounded_monomials(n, d)"),
								b.TermAs[Fun[_Monomial, Nat]]("monomial_slot(n, d)"))))
					b.Show(
						"the encoding writes p(m) at the slot of m",
						Simp(Fwd(decodePolynomialDef), Fwd(EncodePolynomialDef)),
						offset.Rw(),
						By(Normalized, readBack, inBlock))
				})
			a.Otherwise(
				"off the bounded monomials both sides are zero, p being supported in them",
				func(b *Argument, off Fact) {
					b.Show(
						"the decoding is zero there by definition, and m lies outside the support of p",
						By(
							off,
							supported,
							decodePolynomialDef.At(R, n, d, c, b.TermAs[Fun[Nat, A]]("encode_polynomial(n, d, c, p, ρ)"), m),
							set_basic.SubsetDef))
				})
		}),
})}

// EncodeInCarrier — encoding a polynomial over the carrier keeps a carrier value of the environment
// a carrier value: inside the block the encoding writes a coefficient of the polynomial, and every
// coefficient of a polynomial over the ring lies in the carrier; outside the block it keeps the value.
var EncodeInCarrier = encodeInCarrierThm{family.Add(registry.ProofEntry{
	Name: "EncodeInCarrier",
	Key:  "prop_ce82df6396ca07c",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀n d c:num. ∀p:((num → num) → A). ∀ρ:(num → A). ∀v:num.",
		Hypotheses: []string{
			"p ∈ polynomial_algebra(R, {i:num | i < n})",
			"ρ(v) ∈ R.carrier",
		},
		Conclusion: "encode_polynomial(n, d, c, p, ρ, v) ∈ R.carrier",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			n, d, c *Expr[Nat],
			p *Arrow[_Monomial, A],
			ρ *Arrow[Nat, A],
			v *Expr[Nat],
			polynomial, value Fact,
		) {
			coefficients := a.Conjuncts(
				a.Simplified(polynomial, Fwd(polynomial_algebra.PolynomialAlgebraMember)),
				"p is nonzero at finitely many monomials",
				"those are monomials of the variables below n",
				"every coefficient of p is a carrier value")[2]
			a.Show(
				"inside the block the value is a coefficient of p, and outside it is ρ(v)",
				Simp(Fwd(EncodePolynomialDef)),
				By(coefficients, value))
		}),
})}

// encodePolynomialsDef — write the coefficients of the first k members of a family into k
// consecutive blocks from c, member j at c + j · coefficient_count(n, d), each written over the
// environment the earlier members left.
var encodePolynomialsDef = encodePolynomialsDefThm{family.Define(registry.DefEntry{
	Name: "encodePolynomialsDef", Const: "encode_polynomials", Type: "num → " +
		"num → " +
		"num → " +
		"num → " +
		"(num → (num → num) → A) → " +
		"(num → A) → " +
		"num → " +
		"A",
	Key: "prop_54168cbff28708e8",
	Equations: []string{
		"∀n d c:num. ∀P:(num → (num → num) → A). ∀ρ:(num → A). encode_polynomials(n, d, c, 0, P, ρ) = ρ",
		"∀n d c k:num. ∀P:(num → (num → num) → A). ∀ρ:(num → A). " +
			"    encode_polynomials(n, d, c, suc(k), P, ρ) = " +
			"    encode_polynomial(n, " +
			"        d, " +
			"        c + k * coefficient_count(n, d), " +
			"        P(k), " +
			"        encode_polynomials(n, d, c, k, P, ρ))",
	},
	Deps: []registry.EntryLike{EncodePolynomialDef, coefficientCountDef},
})}

// EncodePolynomialsOutside — encoding a family leaves the environment as it was outside its
// blocks: by induction on the count, the last member's block lies inside the blocks, and so
// away from the name.
var EncodePolynomialsOutside = encodePolynomialsOutsideThm{family.Add(registry.ProofEntry{
	Name: "EncodePolynomialsOutside",
	Key:  "prop_4b9079037025ad59",
	Build: family.Theorem(Statement{
		Binders: "∀n d c k:num. ∀P:(num → (num → num) → A). ∀ρ:(num → A). ∀v:num.",
		Hypotheses: []string{
			"v < c ∨ c + k * coefficient_count(n, d) ≤ v",
		},
		Conclusion: "encode_polynomials(n, d, c, k, P, ρ, v) = ρ(v)",
	}, func(
		a *Argument,
		n, d, c, k *Expr[Nat],
		P *Arrow2[Nat, _Monomial, A],
		ρ *Arrow[Nat, A],
		v *Expr[Nat],
		outside Fact,
	) {
		every := a.Have(
			"for every count t, the encoding of the first t members keeps the names outside their blocks",
			Statement{
				Binders: "∀t:num.",
				Hypotheses: []string{
					"v < c ∨ c + t * coefficient_count(n, d) ≤ v",
				},
				Conclusion: "encode_polynomials(n, d, c, t, P, ρ, v) = ρ(v)",
			},
			Derive(func(b *Argument) {
				t := b.Binder("t")
				b.Induct(t)
				b.Base(
					"no member is written",
					Simp(Fwd(encodePolynomialsDef)),
					CnfRefute())
				b.Step(
					"the member t is written in its block, which lies before c + (t + 1) · coefficient_count(n, d)",
					func(step *Argument, ih Fact) {
						away := step.Assume()
						apart := step.Have(
							"v lies outside the block of the member t, and outside the first t blocks",
							"¬(c + t * coefficient_count(n, d) ≤ v ∧ "+
								"    v < c + t * coefficient_count(n, d) + coefficient_count(n, d)) ∧ "+
								"(v < c ∨ c + t * coefficient_count(n, d) ≤ v)",
							ByArith(away))
						step.Show(
							"the member t leaves v, and the first t leave it too",
							Simp(Fwd(encodePolynomialsDef), Fwd(EncodePolynomialDef)),
							By(apart, ih))
					})
			}))
		a.Show(
			"at the count k",
			By(outside, every.At(k)))
	}),
})}

// EncodePolynomialsInCarrier — encoding a family of polynomials over the carrier keeps a carrier
// value of the environment a carrier value: by induction on the count, each member written is a
// polynomial over the ring (EncodeInCarrier).
var EncodePolynomialsInCarrier = encodePolynomialsInCarrierThm{family.Add(registry.ProofEntry{
	Name: "EncodePolynomialsInCarrier",
	Key:  "prop_e13711c76d991f86",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀n d c k:num. ∀P:(num → (num → num) → A). ∀ρ:(num → A). ∀v:num.",
		Hypotheses: []string{
			"∀j:num. j < k ⇒ P(j) ∈ polynomial_algebra(R, {i:num | i < n})",
			"ρ(v) ∈ R.carrier",
		},
		Conclusion: "encode_polynomials(n, d, c, k, P, ρ, v) ∈ R.carrier",
	}, func(
		a *Argument,
		R *Expr[RingOps[A]],
		n, d, c, k *Expr[Nat],
		P *Arrow2[Nat, _Monomial, A],
		ρ *Arrow[Nat, A],
		v *Expr[Nat],
		polynomials, value Fact,
	) {
		every := a.Have(
			"for every count t up to k, the encoding of the first t members is a carrier value at v",
			"∀t:num. t ≤ k ⇒ encode_polynomials(n, d, c, t, P, ρ, v) ∈ R.carrier",
			Derive(func(b *Argument) {
				t := b.Binder("t")
				b.Induct(t)
				b.Base(
					"no member is written, and ρ(v) is a carrier value",
					Simp(Fwd(encodePolynomialsDef)),
					By(value))
				b.Step(
					"the member t is a polynomial over the ring, written over a carrier value",
					func(step *Argument, ih Fact) {
						within := step.Assume()
						last := step.TermAs[Nat]("c + t * coefficient_count(n, d)")
						member := step.TermAs[Fun[_Monomial, A]]("P(t)")
						earlier := step.TermAs[Fun[Nat, A]]("encode_polynomials(n, d, c, t, P, ρ)")
						index := step.Have(
							"t is below k, and t is at most k",
							"t < k ∧ t ≤ k",
							ByArith(within))
						step.Show(
							"the member t, a polynomial over the ring written over a carrier value, keeps v a carrier value",
							Simp(Fwd(encodePolynomialsDef)),
							By(index, ih, polynomials.At(t), EncodeInCarrier.At(R, n, d, last, member, earlier, v)))
					})
			}))
		a.Show(
			"at the count k",
			By(every.At(k), nat_order.LessEqRefl.At(k)))
	}),
})}

// DecodeEncodePolynomials — the members of a family encoded from c are decoded from their blocks:
// by induction on the count, the member t is decoded from its own block, written last
// (DecodeEncode), and an earlier member's block lies before it, where the last write leaves the
// environment as it was (DecodeCongruence).
var DecodeEncodePolynomials = decodeEncodePolynomialsThm{family.Add(registry.ProofEntry{
	Name: "DecodeEncodePolynomials",
	Key:  "prop_fd136e953e549007",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀n d c k:num. ∀P:(num → (num → num) → A). ∀ρ:(num → A). ∀j:num.",
		Hypotheses: []string{
			"∀i:num. i < k ⇒ fun_support(R.zero, P(i)) ⊆ bounded_monomials(n, d)",
			"j < k",
		},
		Conclusion: "decode_polynomials(R, n, d, c, encode_polynomials(n, d, c, k, P, ρ), j) = P(j)",
	}, func(
		a *Argument,
		R *Expr[RingOps[A]],
		n, d, c, k *Expr[Nat],
		P *Arrow2[Nat, _Monomial, A],
		ρ *Arrow[Nat, A],
		j *Expr[Nat],
		supported, member Fact,
	) {
		every := a.Have(
			"for every count t up to k, the first t members are decoded from the encoding of the first t",
			"∀t:num. "+
				"    t ≤ k ⇒ "+
				"    ∀i:num. "+
				"        i < t ⇒ decode_polynomials(R, n, d, c, encode_polynomials(n, d, c, t, P, ρ), i) = P(i)",
			Derive(func(b *Argument) {
				t := b.Binder("t")
				b.Induct(t)
				b.Base(
					"no member lies below zero",
					By(nat_order.NotLessThan, nat_order.ZeroLessEq))
				b.Step(
					"the member t is read from its own block, written last; "+
						"an earlier one from a block the last write leaves alone",
					func(step *Argument, ih Fact) {
						within := step.Assume()
						i := step.FixAs[Nat]("i")
						below := step.Assume()
						cc := step.TermAs[Nat]("coefficient_count(n, d)")
						last := step.TermAs[Nat]("c + t * coefficient_count(n, d)")
						earlier := step.TermAs[Fun[Nat, A]]("encode_polynomials(n, d, c, t, P, ρ)")
						written := step.TermAs[Fun[Nat, A]](
							"encode_polynomial(n, " +
								"    d, " +
								"    c + t * coefficient_count(n, d), " +
								"    P(t), " +
								"    encode_polynomials(n, d, c, t, P, ρ))")
						index := step.Have(
							"t is below k, and i is t or below it",
							"t < k ∧ t ≤ k ∧ (i = t ∨ i < t)",
							ByArith(within, below))
						step.Cases(step.Term("i = t"))
						step.When(
							"the member t is decoded from the block written last",
							func(e *Argument, same Fact) {
								e.Show(
									"decoding the block written last gives the member t back",
									Simp(Fwd(encodePolynomialsDef), Fwd(DecodePolynomialsDef)),
									same.Rw(),
									By(
										index,
										supported.At(t),
										DecodeEncode.At(R, n, d, last, e.TermAs[Fun[_Monomial, A]]("P(t)"), earlier)))
							})
						step.Otherwise(
							"an earlier member's block ends before the member t's begins",
							func(e *Argument, other Fact) {
								before := e.Have(
									"i lies below t",
									"i + 1 ≤ t",
									ByArith(index, other))
								ends := e.Have(
									"the block of i ends at or before the block of t",
									"(i + 1) * coefficient_count(n, d) ≤ t * coefficient_count(n, d)",
									By(
										before,
										nat_order.LessEqMul2.At(e.TermAs[Nat]("i + 1"), e.TermAs[Nat]("t"), cc, cc),
										nat_order.LessEqRefl.At(cc)))
								kept := e.Have(
									"the last write leaves the block of i as it was",
									Statement{
										Binders: "∀v:num.",
										Hypotheses: []string{
											"c + i * coefficient_count(n, d) ≤ v",
											"v < c + i * coefficient_count(n, d) + coefficient_count(n, d)",
										},
										Conclusion: "encode_polynomial(n, " +
											"    d, " +
											"    c + t * coefficient_count(n, d), " +
											"    P(t), " +
											"    encode_polynomials(n, d, c, t, P, ρ), " +
											"    v) = " +
											"encode_polynomials(n, d, c, t, P, ρ, v)",
									},
									Derive(func(f *Argument) {
										f.FixAs[Nat]("v")
										inBlock := f.Assume()
										away := f.Have(
											"v lies before the block of t",
											"¬(c + t * coefficient_count(n, d) ≤ v ∧ "+
												"    v < c + t * coefficient_count(n, d) + coefficient_count(n, d))",
											ByArith(inBlock, ends))
										f.Show(
											"outside its block the encoding keeps the value",
											Simp(Fwd(EncodePolynomialDef)),
											By(away))
									}))
								e.Show(
									"the block of i decodes the same, and the first t "+
										"members are decoded from the encoding of the first t",
									Simp(Fwd(encodePolynomialsDef), Fwd(DecodePolynomialsDef)),
									By(
										index,
										other,
										kept,
										ih,
										DecodeCongruence.At(R, n, d, e.TermAs[Nat]("c + i * coefficient_count(n, d)"), written, earlier),
										DecodePolynomialsDef.At(R, n, d, c, earlier, i)))
							})
					})
			}))
		a.Show(
			"at the count k, the member j below it",
			By(member, every.At(k), nat_order.LessEqRefl.At(k)))
	}),
})}
