// holomorphic.go — functions holomorphic on a set, and the laws that keep
// holomorphy: constants, the identity, sums, negatives, differences, products, powers,
// inverses and quotients, composition, agreement with a holomorphic function
// on an open set, and finite sums.

package complex_derivative

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_topology"
	"github.com/euc-ai/xugo/library/proofs/iterate/monoidal"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// HolomorphicOnContinuous — a function holomorphic on a set is continuous
// on it: at each point of s it has a derivative, so it is continuous
// there, and continuity at each point of s is continuity on s.
var HolomorphicOnContinuous = holomorphicOnContinuousThm{family.Add(registry.ProofEntry{
	Name: "HolomorphicOnContinuous",
	Key:  "prop_adb813714f85fbf7",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(complex). ∀f:(complex → complex).",
		Hypotheses: []string{
			"holomorphic_on(s, f)",
		},
		Conclusion: "complex_continuous_on(s, f)",
	},
		func(a *Argument, s *Expr[Set[Complex]], f *Arrow[Complex, Complex], holomorphic Fact) {
			a.Show(
				"f has a derivative at each point of s, so is continuous there, hence on s",
				By(complex_topology.ContinuousAtOn, HolomorphicOnDef, DerivativeContinuous, holomorphic))
		}),
})}

// HolomorphicOnContinuousAt — a function holomorphic on a set is continuous
// at each point of it: it has a derivative there.
var HolomorphicOnContinuousAt = holomorphicOnContinuousAtThm{family.Add(registry.ProofEntry{
	Name: "HolomorphicOnContinuousAt",
	Key:  "prop_463f5ca32f84147d",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(complex). ∀f:(complex → complex). ∀z:complex.",
		Hypotheses: []string{
			"holomorphic_on(s, f)",
			"z ∈ s",
		},
		Conclusion: "complex_continuous_at(f, z)",
	},
		func(
			a *Argument,
			s *Expr[Set[Complex]],
			f *Arrow[Complex, Complex],
			holomorphic Fact,
			z *Expr[Complex],
			zIn Fact,
		) {
			l, derivative := a.UnpackAs[Complex](
				GroupPremises(zIn, a.Unfolded(holomorphic, HolomorphicOnDef).At(z)),
				"l")
			a.Show(
				"f has a derivative l at z, so is continuous there",
				By(derivative, DerivativeContinuous.At(f, z, l)))
		}),
})}

// HolomorphicOnSubset — a function holomorphic on s is holomorphic on
// every subset of s: a point of the subset is a point of s, where f has a
// derivative.
var HolomorphicOnSubset = holomorphicOnSubsetThm{family.Add(registry.ProofEntry{
	Name: "HolomorphicOnSubset",
	Key:  "prop_33e2d26b6c71f884",
	Build: family.Theorem(Statement{
		Binders: "∀s t:set(complex). ∀f:(complex → complex).",
		Hypotheses: []string{
			"holomorphic_on(s, f)",
			"t ⊆ s",
		},
		Conclusion: "holomorphic_on(t, f)",
	},
		func(a *Argument, s, t *Expr[Set[Complex]], f *Arrow[Complex, Complex], given Fact) {
			a.Show(
				"a point of t is a point of s, where f has a derivative",
				By(HolomorphicOnDef, set_basic.SubsetDef, given))
		}),
})}

// HolomorphicOnAgree — on an open set, a function equal to a holomorphic one
// is holomorphic: each point of the set has a disc about it inside the set,
// where the two agree, and a derivative sees a function only on such a disc.
var HolomorphicOnAgree = holomorphicOnAgreeThm{family.Add(registry.ProofEntry{
	Name: "HolomorphicOnAgree",
	Key:  "prop_d2c0893a9ba86488",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(complex). ∀f h:(complex → complex).",
		Hypotheses: []string{
			"s ∈ complex_topology",
			"holomorphic_on(s, h)",
			"∀z:complex. z ∈ s ⇒ f(z) = h(z)",
		},
		Conclusion: "holomorphic_on(s, f)",
	},
		func(
			a *Argument,
			s *Expr[Set[Complex]],
			f, h *Arrow[Complex, Complex],
			open, holomorphic, agree Fact,
		) {
			a.Do(Simp(Fwd(HolomorphicOnDef)))
			z := a.FixAs[Complex]("z")
			inside := a.Assume()
			δ, near := a.ObtainAs[Real](
				"s is open, so some disc about z lies in it",
				"∃δ:real. &0 < δ ∧ ∀w:complex. |w - z| < δ ⇒ w ∈ s",
				By(open, inside, complex_topology.ComplexOpenIff.At(s)))
			l, slope := a.ObtainAs[Complex](
				"h has a derivative l at z",
				"∃l:complex. complex_derivative_at(h, z, l)",
				By(holomorphic, inside, HolomorphicOnDef))
			a.Take(l)
			a.Show(
				"on that disc f is h, so f has the derivative l at z too",
				By(near, agree, slope, DerivativeLocal.At(f, h, z, l, δ)))
		}),
})}

// HolomorphicOnConst — a constant function is holomorphic on every set,
// with derivative 0 at each point.
var HolomorphicOnConst = holomorphicOnConstThm{family.Add(registry.ProofEntry{
	Name: "HolomorphicOnConst",
	Key:  "prop_542df171db433a00",
	Build: family.Theorem("∀s:set(complex). ∀k:complex. holomorphic_on(s, λz:complex. k)",
		func(a *Argument, s *Expr[Set[Complex]], k *Expr[Complex]) {
			a.Show(
				"a constant has derivative 0 at every point",
				By(HolomorphicOnDef, DerivativeConst))
		}),
})}

// HolomorphicOnId — the identity is holomorphic on every set, with
// derivative 1 at each point.
var HolomorphicOnId = holomorphicOnIdThm{family.Add(registry.ProofEntry{
	Name: "HolomorphicOnId",
	Key:  "prop_504e786138596f01",
	Build: family.Theorem("∀s:set(complex). holomorphic_on(s, λz:complex. z)",
		func(a *Argument, s *Expr[Set[Complex]]) {
			a.Show(
				"the identity has derivative 1 at every point",
				By(HolomorphicOnDef, DerivativeId))
		}),
})}

// HolomorphicOnAdd — the sum of two functions holomorphic on s is
// holomorphic on s: at each point the derivatives add.
var HolomorphicOnAdd = holomorphicOnAddThm{family.Add(registry.ProofEntry{
	Name: "HolomorphicOnAdd",
	Key:  "prop_6bcdc913d207c0d2",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(complex). ∀f g:(complex → complex).",
		Hypotheses: []string{
			"holomorphic_on(s, f)",
			"holomorphic_on(s, g)",
		},
		Conclusion: "holomorphic_on(s, λz:complex. f(z) + g(z))",
	},
		func(a *Argument, s *Expr[Set[Complex]], f, g *Arrow[Complex, Complex], given Fact) {
			a.Show(
				"at each point of s, f and g have derivatives l and m, so f + g has l + m",
				By(HolomorphicOnDef, DerivativeAdd, given))
		}),
})}

// HolomorphicOnSub — the difference of two functions holomorphic on s is
// holomorphic on s: at each point the derivatives subtract.
var HolomorphicOnSub = holomorphicOnSubThm{family.Add(registry.ProofEntry{
	Name: "HolomorphicOnSub",
	Key:  "prop_9d87ef8defebe270",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(complex). ∀f g:(complex → complex).",
		Hypotheses: []string{
			"holomorphic_on(s, f)",
			"holomorphic_on(s, g)",
		},
		Conclusion: "holomorphic_on(s, λz:complex. f(z) - g(z))",
	},
		func(a *Argument, s *Expr[Set[Complex]], f, g *Arrow[Complex, Complex], given Fact) {
			a.Show(
				"at each point of s, f and g have derivatives l and m, so f − g has l − m",
				By(HolomorphicOnDef, DerivativeSub, given))
		}),
})}

// HolomorphicOnNeg — the negative of a function holomorphic on s is
// holomorphic on s: at each point the derivative changes sign.
var HolomorphicOnNeg = holomorphicOnNegThm{family.Add(registry.ProofEntry{
	Name: "HolomorphicOnNeg",
	Key:  "prop_3c90a2ec7742526c",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(complex). ∀f:(complex → complex).",
		Hypotheses: []string{
			"holomorphic_on(s, f)",
		},
		Conclusion: "holomorphic_on(s, λz:complex. -f(z))",
	},
		func(a *Argument, s *Expr[Set[Complex]], f *Arrow[Complex, Complex], given Fact) {
			a.Show(
				"at each point of s, f has a derivative l, so −f has −l",
				By(HolomorphicOnDef, DerivativeNeg, given))
		}),
})}

// HolomorphicOnSum — a finite sum of functions holomorphic on a set is
// holomorphic there. By induction on the index set: over ∅ the sum is the
// constant 0, and one index x more adds the holomorphic F(x).
var HolomorphicOnSum = holomorphicOnSumThm{family.Add(registry.ProofEntry{
	Name: "HolomorphicOnSum",
	Key:  "prop_a19efa8871e33667",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(complex). ∀I:set(A). ∀F:(A → complex → complex).",
		Hypotheses: []string{
			"finite(I)",
			"∀i:A. i ∈ I ⇒ holomorphic_on(s, F(i))",
		},
		Conclusion: "holomorphic_on(s, λz:complex. Σ_{i∈I} F(i, z))",
	},
		func(
			a *Argument,
			s *Expr[Set[Complex]],
			I *Expr[Set[A]],
			F *Arrow2[A, Complex, Complex],
			finite, holomorphic Fact,
		) {
			addition := comm_ring.MonoidalAdd.Read(complex_field.CommRing)
			a.Show(
				"by induction on the index set, each F(i) being holomorphic",
				ByInduction(finite_set.FiniteInductFreshOn, finite, holomorphic,
					Case(
						"over ∅ the sum is the constant 0",
						Simp(Fwd(monoidal.Clauses.Read(addition)), Fwd(comm_ring.NeutralAdd.Read(complex_field.CommRing))),
						By(HolomorphicOnConst)),
					Case(
						"one index x more adds the holomorphic F(x) to the sum",
						Derive(func(b *Argument) {
							x, J := b.FixAs[A]("x"), b.FixAs[Set[A]]("J")
							parts := b.Conjuncts(
								b.Assume(),
								"the sum over J is holomorphic",
								"x is not in J",
								"J is finite",
								"F(x) is holomorphic",
								"so is every F(i) for i in J")
							peel := b.Have(
								"x being new, the sum over J with x put in is F(x) plus the sum over J",
								"(λz:complex. Σ_{i∈insert(x, J)} F(i, z)) = (λz:complex. F(x, z) + Σ_{i∈J} F(i, z))",
								Funext(),
								Derive(func(c *Argument) {
									c.FixAs[Complex]("z")
									c.Show(
										"one turn of the sum takes x out",
										By(
											parts[2],
											parts[1],
											monoidal.OneTurn.Read(addition).At(J, x, c.TermAs[Fun[A, Complex]]("λi:A. F(i, z)"))))
								}))
							b.Show(
								"and a sum of two holomorphic functions is holomorphic",
								peel.Rw(),
								By(parts[3], parts[0], HolomorphicOnAdd))
						}))))
		}),
})}

// HolomorphicOnMul — the product of two functions holomorphic on s is
// holomorphic on s, by the product rule at each point.
var HolomorphicOnMul = holomorphicOnMulThm{family.Add(registry.ProofEntry{
	Name: "HolomorphicOnMul",
	Key:  "prop_a12e3d7a66997c44",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(complex). ∀f g:(complex → complex).",
		Hypotheses: []string{
			"holomorphic_on(s, f)",
			"holomorphic_on(s, g)",
		},
		Conclusion: "holomorphic_on(s, λz:complex. f(z) * g(z))",
	},
		func(a *Argument, s *Expr[Set[Complex]], f, g *Arrow[Complex, Complex], given Fact) {
			a.Show(
				"at each point of s, f and g have derivatives, and the product rule gives one for f·g",
				By(HolomorphicOnDef, DerivativeMul, given))
		}),
})}

// HolomorphicOnPow — every power of a function holomorphic on s is
// holomorphic on s. By induction on the exponent: f⁰ is the constant 1,
// and f^(n+1) is f·fⁿ, a product of two functions holomorphic on s.
var HolomorphicOnPow = holomorphicOnPowThm{family.Add(registry.ProofEntry{
	Name: "HolomorphicOnPow",
	Key:  "prop_3c3760ea2f5d8f2f",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(complex). ∀f:(complex → complex). ∀n:num.",
		Hypotheses: []string{
			"holomorphic_on(s, f)",
		},
		Conclusion: "holomorphic_on(s, λz:complex. f(z) ^ n)",
	},
		func(a *Argument, s *Expr[Set[Complex]], f *Arrow[Complex, Complex], holomorphic Fact) {
			a.Induct("n")
			a.Base(
				"f⁰ is the constant 1",
				Simp(Fwd(comm_monoid.MonoidPowDef)),
				Cite(HolomorphicOnConst))
			a.Step(
				"f^(n+1) is f·fⁿ, and a product of functions holomorphic on s is holomorphic on s",
				func(b *Argument, ih Fact) {
					b.Do(Simp(Fwd(comm_monoid.MonoidPowDef)))
					b.Show(
						"f and fⁿ are holomorphic on s",
						By(
							HolomorphicOnMul.At(s, f, b.TermAs[Fun[Complex, Complex]]("λz:complex. f(z) ^ n")),
							holomorphic,
							ih))
				})
		}),
})}

// HolomorphicOnInv — the inverse of a function holomorphic on s and
// nowhere zero there is holomorphic on s, by the reciprocal rule at each
// point.
var HolomorphicOnInv = holomorphicOnInvThm{family.Add(registry.ProofEntry{
	Name: "HolomorphicOnInv",
	Key:  "prop_635d3abc2535500c",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(complex). ∀f:(complex → complex).",
		Hypotheses: []string{
			"holomorphic_on(s, f)",
			"∀z:complex. z ∈ s ⇒ f(z) ≠ &0",
		},
		Conclusion: "holomorphic_on(s, λz:complex. complex_inv(f(z)))",
	},
		func(a *Argument, s *Expr[Set[Complex]], f *Arrow[Complex, Complex], given Fact) {
			a.Show(
				"at each point of s, f has a derivative and is not zero, and the reciprocal rule gives one for 1/f",
				By(HolomorphicOnDef, DerivativeInv, given))
		}),
})}

// HolomorphicOnDiv — the quotient of two functions holomorphic on s, the
// divisor nowhere zero there, is holomorphic on s, by the quotient rule at
// each point.
var HolomorphicOnDiv = holomorphicOnDivThm{family.Add(registry.ProofEntry{
	Name: "HolomorphicOnDiv",
	Key:  "prop_5e4ced38f5dedca4",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(complex). ∀f g:(complex → complex).",
		Hypotheses: []string{
			"holomorphic_on(s, f)",
			"holomorphic_on(s, g)",
			"∀z:complex. z ∈ s ⇒ g(z) ≠ &0",
		},
		Conclusion: "holomorphic_on(s, λz:complex. f(z) / g(z))",
	},
		func(a *Argument, s *Expr[Set[Complex]], f, g *Arrow[Complex, Complex], given Fact) {
			a.Show(
				"at each point of s, f and g have derivatives and g "+
					"is not zero, and the quotient rule gives one for f/g",
				By(HolomorphicOnDef, DerivativeDiv, given))
		}),
})}

// HolomorphicOnCompose — a function holomorphic on t composed after one
// holomorphic on s that maps s into t is holomorphic on s: at a point z of
// s, g has a derivative at z and f one at g(z) ∈ t, and the chain rule
// gives one for f ∘ g at z.
var HolomorphicOnCompose = holomorphicOnComposeThm{family.Add(registry.ProofEntry{
	Name: "HolomorphicOnCompose",
	Key:  "prop_7cddd1f5924683d5",
	Build: family.Theorem(Statement{
		Binders: "∀s t:set(complex). ∀f g:(complex → complex).",
		Hypotheses: []string{
			"holomorphic_on(s, g)",
			"holomorphic_on(t, f)",
			"∀z:complex. z ∈ s ⇒ g(z) ∈ t",
		},
		Conclusion: "holomorphic_on(s, f ∘ g)",
	},
		func(a *Argument, s, t *Expr[Set[Complex]], f, g *Arrow[Complex, Complex], given Fact) {
			a.Show(
				"at a point z of s, g has a derivative at z and f "+
					"one at g(z) ∈ t, and the chain rule composes them",
				By(HolomorphicOnDef, DerivativeChain, given))
		}),
})}
