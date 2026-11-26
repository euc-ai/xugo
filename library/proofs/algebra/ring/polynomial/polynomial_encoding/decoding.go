// decoding.go — what a block of an environment decodes to: a coordinate
// block a zero-padded tuple, a coefficient block a polynomial supported in
// the bounded monomials, each depending on the environment on its block
// alone; and a ring homomorphism applied to the environment is applied to
// what its blocks decode to.

package polynomial_encoding

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_algebra"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_algebra_evaluation"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/datatypes/first_order"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
)

// DecodeTupleMonomialValue — a bounded monomial evaluated at a decoded
// coordinate tuple is the product, over the coordinates below n, of the
// environment's value at each coordinate slot raised to the monomial's
// exponent: the monomial's support lies below n, so the product over its
// support extends to all coordinates below n, where the tuple reads ρ.
var DecodeTupleMonomialValue = decodeTupleMonomialValueThm{family.Add(registry.ProofEntry{
	Name: "DecodeTupleMonomialValue",
	Key:  "prop_ff3d850b92c115ad",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀n d x:num. ∀ρ:(num → A). ∀m:(num → num).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"∀i:num. i < n ⇒ ρ(x + i) ∈ R.carrier",
			"m ∈ bounded_monomials(n, d)",
		},
		Conclusion: "monomial_eval(R, decode_tuple(R, n, x, ρ), m) = " +
			"module_sum(R.mul, R.one, {i:num | i < n}, λi:num. monoid_pow(R.mul, R.one, ρ(x + i), m(i)))",
		Abbrev: Abbrev{
			{Name: "powers", Text: "λy:num. monoid_pow(R.mul, R.one, decode_tuple(R, n, x, ρ, y), m(y))"},
		},
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			n, d, x *Expr[Nat],
			ρ *Arrow[Nat, A],
			m *Expr[_Monomial],
			ring, coordinates, bounded Fact,
		) {
			below := a.TermAs[Set[Nat]]("{i:num | i < n}")
			products := comm_ring.MulMonoidOn.Read(ring)
			powers := a.TermAs[Fun[Nat, A]]("«powers»")
			support := a.Have(
				"m is a monomial of the variables below n, so its support lies below n",
				"fun_support(0, m) ⊆ {i:num | i < n}",
				By(
					bounded,
					BoundedMonomialsAreMonomials.At(n, d),
					polynomial_algebra.MonomialsMember.At(below, m),
					set_basic.SubsetDef.At(
						a.TermAs[Set[_Monomial]]("bounded_monomials(n, d)"),
						a.TermAs[Set[_Monomial]]("monomials({i:num | i < n})"))))
			inCarrier := a.Have(
				"below n the decoded tuple reads ρ, so it lies in the carrier",
				"∀i:num. i < n ⇒ decode_tuple(R, n, x, ρ, i) ∈ R.carrier",
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]("i")
					under := b.Assume()
					b.Show(
						"the coordinate is ρ(x + i)",
						By(Normalized, coordinates.At(i), under, DecodeTupleDef.At(R, n, x, ρ, i)))
				}))
			offSupport := a.Have(
				"off the support of m the exponent is zero, so the power is one",
				"∀i:num. i ∉ fun_support(0, m) ⇒ «powers»(i) = R.one",
				By(comm_monoid.MonoidPowDef))
			over := a.Have(
				"so the product over the support of m is the product over all coordinates below n",
				"module_sum(R.mul, R.one, fun_support(0, m), «powers») = "+
					"module_sum(R.mul, R.one, {i:num | i < n}, «powers»)",
				By(
					support,
					inCarrier,
					offSupport,
					module.ModuleSumSupportMonoid.Read(products).At(
						below, a.TermAs[Set[Nat]]("fun_support(0, m)"), powers),
					num_segment.FiniteBelowStrict.At(n),
					comm_monoid.PowIn.Read(products)))
			a.Show(
				"and below n each factor is ρ(x + i) raised to m(i)",
				Simp(Fwd(polynomial_algebra_evaluation.MonomialEvalDef)),
				By(
					over,
					module.ModuleSumCongruence.At(
						a.TermAs[Op[A]]("R.mul"),
						a.TermAs[A]("R.one"),
						below,
						powers,
						a.TermAs[Fun[Nat, A]]("λi:num. monoid_pow(R.mul, R.one, ρ(x + i), m(i))")),
					DecodeTupleDef))
		}),
})}

// DecodeTupleRingTuple — a coordinate block of a carrier-valued environment decodes to a ring
// tuple: below n it reads the environment, and from n on it is zero.
var DecodeTupleRingTuple = decodeTupleRingTupleThm{family.Add(registry.ProofEntry{
	Name: "DecodeTupleRingTuple",
	Key:  "prop_5bfdb00a5308e22f",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀n x:num. ∀ρ:(num → A).",
		Hypotheses: []string{
			"fo_env_ok(R.carrier, 𝕌, ρ)",
		},
		Conclusion: "ring_tuple(R, n, decode_tuple(R, n, x, ρ))",
	}, func(a *Argument, R *Expr[RingOps[A]], n, x *Expr[Nat], ρ *Arrow[Nat, A], env Fact) {
		everywhere := a.Unfolded(env, first_order.EnvOKDef)
		a.Show(
			"below n the decoded tuple reads ρ, a carrier value, and from n on it is zero",
			Unfold(RingTupleDef),
			Unfold(vec_space.VecDef),
			Simp(Fwd(DecodeTupleDef)),
			By(everywhere, set_basic.InUniv, nat_order.NotLessThan))
	}),
})}

// DecodeTupleApart — substituting a block of values apart from the coordinate block at x leaves
// the tuple decoded there unchanged: below n the block reads x + i, which lies outside the
// substituted names.
var DecodeTupleApart = decodeTupleApartThm{family.Add(registry.ProofEntry{
	Name: "DecodeTupleApart",
	Key:  "prop_551b3c3b2f8645b3",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀n x s k:num. ∀ρ u:(num → A).",
		Hypotheses: []string{
			"x + n ≤ s ∨ s + k ≤ x",
		},
		Conclusion: "decode_tuple(R, n, x, fo_update_range(ρ, s, k, u)) = decode_tuple(R, n, x, ρ)",
	},
		func(a *Argument, R *Expr[RingOps[A]], n, x, s, k *Expr[Nat], ρ, u *Arrow[Nat, A], apart Fact) {
			outside := a.Have(
				"below n the coordinate x + i lies outside the substituted block",
				"∀i:num. i < n ⇒ ¬(s ≤ x + i ∧ x + i < s + k)",
				ByArith(apart))
			a.Show(
				"the decoded block reads the same values",
				Simp(Fwd(DecodeTupleDef), Fwd(first_order.UpdateRangeDef)),
				By(outside))
		}),
})}

// DecodeUpdatedTuple — substituting a ring tuple into the coordinate block at x and decoding that
// block gives the tuple back: below n the block reads the tuple, and from n on both are zero.
var DecodeUpdatedTuple = decodeUpdatedTupleThm{family.Add(registry.ProofEntry{
	Name: "DecodeUpdatedTuple",
	Key:  "prop_201615d875ee5b80",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀n x:num. ∀ρ y:(num → A).",
		Hypotheses: []string{
			"ring_tuple(R, n, y)",
		},
		Conclusion: "decode_tuple(R, n, x, fo_update_range(ρ, x, n, y)) = y",
	}, func(a *Argument, R *Expr[RingOps[A]], n, x *Expr[Nat], ρ, y *Arrow[Nat, A], tuple Fact) {
		padded := a.Unfolded(a.Unfolded(tuple, RingTupleDef), vec_space.VecDef)
		block := a.Have(
			"the coordinate x + i lies in the block at x exactly when i < n, and reads index i there",
			"∀i:num. x ≤ x + i ∧ x + i - x = i ∧ (x + i < x + n ⇔ i < n)",
			ByArith())
		a.Show(
			"below n the decoded block reads y, and from n on both are zero",
			Simp(Fwd(DecodeTupleDef), Fwd(first_order.UpdateRangeDef), Fwd(block)),
			By(padded, nat_order.NotLessThan))
	}),
})}

// DecodeCongruence — the polynomial decoded from the coefficient block at c depends only on the
// environment on that block: it reads the environment at c plus the slot of each bounded
// monomial, and every slot lies below the coefficient count.
var DecodeCongruence = decodeCongruenceThm{family.Add(registry.ProofEntry{
	Name: "DecodeCongruence",
	Key:  "prop_1591d3d5f9b212d8",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀n d c:num. ∀ρ σ:(num → A).",
		Hypotheses: []string{
			"∀v:num. c ≤ v ∧ v < c + coefficient_count(n, d) ⇒ ρ(v) = σ(v)",
		},
		Conclusion: "decode_polynomial(R, n, d, c, ρ) = decode_polynomial(R, n, d, c, σ)",
	}, func(a *Argument, R *Expr[RingOps[A]], n, d, c *Expr[Nat], ρ, σ *Arrow[Nat, A], agree Fact) {
		slots := a.Have(
			"ρ and σ agree at the slot of every bounded monomial",
			Statement{
				Binders: "∀m:(num → num).",
				Hypotheses: []string{
					"m ∈ bounded_monomials(n, d)",
				},
				Conclusion: "ρ(c + monomial_slot(n, d, m)) = σ(c + monomial_slot(n, d, m))",
			},
			Derive(func(b *Argument) {
				b.FixAs[_Monomial]("m")
				bounded := b.Assume()
				inBlock := b.Have(
					"the slot of a bounded monomial lies in the block at c",
					"c ≤ c + monomial_slot(n, d, m) ∧ c + monomial_slot(n, d, m) < c + coefficient_count(n, d)",
					ByArith(bounded, MonomialSlots.At(n, d)))
				b.Show(
					"the two environments agree there",
					By(agree.At(b.TermAs[Nat]("c + monomial_slot(n, d, m)")), inBlock))
			}))
		a.Show(
			"each decoded coefficient reads one of those slots",
			Simp(Fwd(decodePolynomialDef)),
			By(slots))
	}),
})}

// DecodeTupleCongruence — the tuple decoded from the coordinate block at x depends only on the
// environment on that block: below n it reads the environment at x + i, which lies in the block,
// and from n on it is zero.
var DecodeTupleCongruence = decodeTupleCongruenceThm{family.Add(registry.ProofEntry{
	Name: "DecodeTupleCongruence",
	Key:  "prop_86137ca857fb9745",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀n x:num. ∀ρ σ:(num → A).",
		Hypotheses: []string{
			"∀v:num. x ≤ v ∧ v < x + n ⇒ ρ(v) = σ(v)",
		},
		Conclusion: "decode_tuple(R, n, x, ρ) = decode_tuple(R, n, x, σ)",
	}, func(a *Argument, R *Expr[RingOps[A]], n, x *Expr[Nat], ρ, σ *Arrow[Nat, A], agree Fact) {
		coordinates := a.Have(
			"below n the coordinate x + i lies in the block at x",
			"∀i:num. i < n ⇒ x ≤ x + i ∧ x + i < x + n",
			ByArith())
		a.Show(
			"each decoded coordinate below n reads the two environments at one name of the block",
			Simp(Fwd(DecodeTupleDef)),
			By(coordinates, agree))
	}),
})}

// DecodePolynomialsCongruence — the polynomials decoded from k consecutive blocks from the slot c
// depend only on the environment on those blocks: the j-th reads only the j-th block, which lies
// among them for j < k.
var DecodePolynomialsCongruence = decodePolynomialsCongruenceThm{family.Add(registry.ProofEntry{
	Name: "DecodePolynomialsCongruence",
	Key:  "prop_548357b4020e7092",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀n d c k:num. ∀ρ σ:(num → A). ∀j:num.",
		Hypotheses: []string{
			"∀v:num. c ≤ v ∧ v < c + k * coefficient_count(n, d) ⇒ ρ(v) = σ(v)",
			"j < k",
		},
		Conclusion: "decode_polynomials(R, n, d, c, ρ, j) = decode_polynomials(R, n, d, c, σ, j)",
	}, func(
		a *Argument,
		R *Expr[RingOps[A]],
		n, d, c, k *Expr[Nat],
		ρ, σ *Arrow[Nat, A],
		j *Expr[Nat],
		agree, below Fact,
	) {
		count := a.TermAs[Nat]("coefficient_count(n, d)")
		start := a.TermAs[Nat]("c + j * coefficient_count(n, d)")
		onBlock := a.Have(
			"ρ and σ agree on the j-th block, which lies among the k blocks from c",
			Statement{
				Binders: "∀v:num.",
				Hypotheses: []string{
					"c + j * coefficient_count(n, d) ≤ v ∧ " +
						"v < c + j * coefficient_count(n, d) + coefficient_count(n, d)",
				},
				Conclusion: "ρ(v) = σ(v)",
			},
			Derive(func(b *Argument) {
				v := b.FixAs[Nat]("v")
				inBlock := b.Assume()
				among := b.Have(
					"v lies among the k blocks",
					"c ≤ v ∧ v < c + k * coefficient_count(n, d)",
					ByArith(inBlock, below, nat_order.LessEqMul2.At(b.TermAs[Nat]("suc(j)"), k, count, count)))
				b.Show(
					"so ρ and σ agree at v",
					By(agree.At(v), among))
			}))
		a.Show(
			"the j-th polynomial reads only its own block",
			Simp(Fwd(DecodePolynomialsDef)),
			By(GroupPremises(onBlock, DecodeCongruence.At(R, n, d, start, ρ, σ))))
	}),
})}

// DecodePolynomialBound — the polynomial decoded from a carrier-valued coefficient block is a
// polynomial in the variables below n of degree at most d: it reads the block at the bounded
// monomials and is zero elsewhere, and the bounded monomials are finitely many monomials in the
// variables below n.
var DecodePolynomialBound = decodePolynomialBoundThm{family.Add(registry.ProofEntry{
	Name: "DecodePolynomialBound",
	Key:  "prop_d38838ab7374bccb",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀n d c:num. ∀ρ:(num → A).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"fo_env_ok(R.carrier, «block», ρ)",
		},
		Conclusion: "polynomial_bound(R, n, d, decode_polynomial(R, n, d, c, ρ))",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			n, d, c *Expr[Nat],
			ρ *Arrow[Nat, A],
			ring comm_ring.CommRingFact[on.R],
			env Fact,
		) {
			block := a.Unfolded(env, first_order.EnvOKDef)
			coefficients := a.Have(
				"each coefficient is a carrier value, and zero off the bounded monomials",
				"∀m:(num → num). "+
					"    decode_polynomial(R, n, d, c, ρ, m) ∈ R.carrier ∧ "+
					"    (m ∉ bounded_monomials(n, d) ⇒ decode_polynomial(R, n, d, c, ρ, m) = R.zero)",
				Derive(func(b *Argument) {
					m := b.FixAs[_Monomial]("m")
					b.Cases(b.Term("m ∈ bounded_monomials(n, d)"))
					b.When(
						"at a bounded monomial the coefficient is read at its slot, which lies in the block",
						func(e *Argument, bounded Fact) {
							slot := e.TermAs[Nat]("c + monomial_slot(n, d, m)")
							inBlock := e.Have(
								"the slot lies in the block",
								"c ≤ c + monomial_slot(n, d, m) ∧ c + monomial_slot(n, d, m) < c + coefficient_count(n, d)",
								ByArith(bounded, MonomialSlots.At(n, d)))
							e.Show(
								"the environment is carrier-valued there",
								By(bounded, inBlock, block.At(slot), decodePolynomialDef.At(R, n, d, c, ρ, m)))
						})
					b.Otherwise(
						"off the bounded monomials the coefficient is zero, a carrier value",
						func(e *Argument, off Fact) {
							e.Show(
								"zero lies in the carrier",
								By(Normalized, off, decodePolynomialDef.At(R, n, d, c, ρ, m), comm_ring.ZeroIn.Read(ring)))
						})
				}))
			p := a.TermAs[Fun[_Monomial, A]]("decode_polynomial(R, n, d, c, ρ)")
			support := a.TermAs[Set[_Monomial]]("fun_support(R.zero, decode_polynomial(R, n, d, c, ρ))")
			bounded := a.TermAs[Set[_Monomial]]("bounded_monomials(n, d)")
			vanishes := a.Have(
				"the decoded polynomial vanishes off the bounded monomials",
				"fun_support(R.zero, decode_polynomial(R, n, d, c, ρ)) ⊆ bounded_monomials(n, d)",
				By(coefficients, set_basic.SubsetDef))
			a.Show(
				"its support is a finite set of monomials in the "+
					"variables below n, its coefficients carrier values",
				By(
					coefficients,
					vanishes,
					PolynomialBoundDef.At(R, n, d, p),
					polynomial_algebra.PolynomialAlgebraMember.At(R, a.TermAs[Set[Nat]]("{i:num | i < n}"), p),
					BoundedMonomialsFinite.At(n, d),
					BoundedMonomialsAreMonomials.At(n, d),
					finite_set.FiniteSubset.At(support, bounded),
					set_order.SubsetTrans.At(support, bounded, a.TermAs[Set[_Monomial]]("monomials({i:num | i < n})"))))
		}),
})}

// DecodeImage — decoding commutes with a ring homomorphism applied to the environment: at a
// bounded monomial both sides read the same slot through the homomorphism, and at any other the
// target's zero is the image of the source's.
var DecodeImage = decodeImageThm{family.Add(registry.ProofEntry{
	Name: "DecodeImage",
	Key:  "prop_8aea7c38b6a5e651",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀ι:(A → B). ∀n d c:num. ∀ρ:(num → A).",
		Hypotheses: []string{
			"ring_homomorphism(R, S, ι)",
		},
		Conclusion: "decode_polynomial(S, n, d, c, λv:num. ι(ρ(v))) = " +
			"λm:(num → num). ι(decode_polynomial(R, n, d, c, ρ, m))",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			S *Expr[RingOps[B]],
			ι *Arrow[A, B],
			n, d, c *Expr[Nat],
			ρ *Arrow[Nat, A],
			hom ring_homomorphism.RingHomomorphismFact[on.R, on.S],
		) {
			a.Do(Funext())
			a.FixAs[_Monomial]("m")
			a.Show(
				"a bounded monomial reads the same slot on both sides, and elsewhere S.zero is ι(R.zero)",
				Simp(Fwd(decodePolynomialDef)),
				By(ring_homomorphism.MapZero.Read(hom)))
		}),
})}

// DecodeTupleImage — decoding a coordinate block commutes with a ring homomorphism applied to the
// environment: below n both sides read ρ(x + j) through the homomorphism, and from n on the
// target's zero is the image of the source's.
var DecodeTupleImage = decodeTupleImageThm{family.Add(registry.ProofEntry{
	Name: "DecodeTupleImage",
	Key:  "prop_713b3cbd9fe4c75f",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀ι:(A → B). ∀n x:num. ∀ρ:(num → A).",
		Hypotheses: []string{
			"ring_homomorphism(R, S, ι)",
		},
		Conclusion: "decode_tuple(S, n, x, λv:num. ι(ρ(v))) = λj:num. ι(decode_tuple(R, n, x, ρ, j))",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			S *Expr[RingOps[B]],
			ι *Arrow[A, B],
			n, x *Expr[Nat],
			ρ *Arrow[Nat, A],
			hom ring_homomorphism.RingHomomorphismFact[on.R, on.S],
		) {
			a.Do(Funext())
			a.FixAs[Nat]("j")
			a.Show(
				"below n both sides read ρ(x + j) through ι, and from n on S.zero is ι(R.zero)",
				Simp(Fwd(DecodeTupleDef)),
				By(ring_homomorphism.MapZero.Read(hom)))
		}),
})}
