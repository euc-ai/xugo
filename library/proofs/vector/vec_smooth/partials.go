// partials.go — the partial derivative as a function: it is the derivative
// where there is one, it is read near the point, it follows the sum, the
// product and the chain rules, and for a function of class C² the order of
// two partial derivatives does not matter.

package vec_smooth

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/real/real_derivative"
	"github.com/euc-ai/xugo/library/proofs/vector/euclidean"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_derivative"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// PartialDerivativeValue — where f has a partial derivative, the function
// ∂ⱼf takes its value.
var PartialDerivativeValue = partialDerivativeValueThm{family.Add(registry.ProofEntry{
	Name: "PartialDerivativeValue",
	Key:  "prop_78ab16861b12683c",
	Build: family.Theorem(Statement{
		Binders: "∀f:((num → real) → real). ∀j:num. ∀c:(num → real). ∀d:real.",
		Hypotheses: []string{
			"partial_derivative_at(f, j, c, d)",
		},
		Conclusion: "partial_derivative(f, j, c) = d",
	},
		func(
			a *Argument,
			f *Arrow[Fun[Nat, Real], Real],
			j *Expr[Nat],
			c *Arrow[Nat, Real],
			d *Expr[Real],
			derivative Fact,
		) {
			value, chosen := a.ObtainChosen(
				"so the definition chooses a partial derivative of f at c along j",
				"∃e:real. partial_derivative_at(f, j, c, e)",
				derivative)
			line := a.TermAs[Fun[Real, Real]]("λt:real. f(c + t • basis_vector(j))")
			a.Show(
				"the chosen value and d are derivatives of f along the coordinate line, which has only one",
				Unfold(PartialDerivativeDef),
				By(
					chosen,
					derivative,
					At(vec_derivative.PartialDerivativeAtDef, f, j, c, value),
					vec_derivative.PartialDerivativeAtDef.At(f, j, c, d),
					At(real_derivative.DerivativeUnique, line, a.TermAs[Real]("&0"), value, d)))
		}),
})}

// PartialDerivativeLocal — two functions that agree near c have the same
// partial derivatives there: e_j is a unit n-vector, so the point c + t·e_j
// is an n-vector at distance |t| from c, and t ↦ f(c + t·e_j) and t ↦ g(c +
// t·e_j) agree for |t| < r; a derivative at 0 reads its function only near
// 0, so the two lines have the same derivatives there.
var PartialDerivativeLocal = partialDerivativeLocalThm{family.Add(registry.ProofEntry{
	Name: "PartialDerivativeLocal",
	Key:  "prop_1dee42a363dabb8d",
	Reading: "vec⟨n⟩(c) and j < n keep the line c + t·e_j among the n-vectors, " +
		"where the agreement is asked; nothing is asked of either function's derivative.",
	Build: family.Theorem(Statement{
		Binders: "∀n:num. ∀f g:((num → real) → real). ∀j:num. ∀c:(num → real). ∀r:real.",
		Hypotheses: []string{
			"vec⟨n⟩(c)",
			"j < n",
			"&0 < r",
			"∀x:(num → real). vec⟨n⟩(x) ∧ ‖x - c‖_n < r ⇒ f(x) = g(x)",
		},
		Conclusion: "(∀d:real. partial_derivative_at(f, j, c, d) ⇔ partial_derivative_at(g, j, c, d)) ∧ " +
			"partial_derivative(f, j, c) = partial_derivative(g, j, c)",
	},
		func(
			a *Argument,
			n *Expr[Nat],
			f, g *Arrow[Fun[Nat, Real], Real],
			j *Expr[Nat],
			c *Vec[Real, DimN],
			r *Expr[Real],
			cIn, below, rPos, agree Fact,
		) {
			zero := a.TermAs[Real]("&0")
			one := a.TermAs[Real]("&1")
			direction := a.VecAs[Real, DimN]("basis_vector(j)")
			directionIn := a.Have(
				"the basis vector e_j is an n-vector, j being below n",
				"vec⟨n⟩(basis_vector(j))",
				By(below, vec_space.VecBasisVector.At(zero, one, n, j)))
			line := a.Conjuncts(
				euclidean.LineThroughPoint.At(proof.Inhabit(c, cIn), proof.Inhabit(direction, directionIn)),
				"the line through c along e_j, its start",
				"and its point at t, an n-vector at distance |t|·‖e_j‖ from c")
			onLine := a.Have(
				"so f and g agree on the line through c along e_j, within r of t = 0",
				"∀t:real. |t - &0| < r ⇒ f(c + t • basis_vector(j)) = g(c + t • basis_vector(j))",
				Derive(func(b *Argument) {
					t := b.FixAs[Real]("t")
					near := b.Assume()
					point := b.VecAs[Real, DimN]("c + t • basis_vector(j)")
					b.Show(
						"c + t·e_j is an n-vector at distance |t| < r from c, where f and g agree",
						ByArith(agree.At(point), line[1].At(t), below, euclidean.NormBasisVector.At(n, j), near))
				}))
			fLine := a.TermAs[Fun[Real, Real]]("λt:real. f(c + t • basis_vector(j))")
			gLine := a.TermAs[Fun[Real, Real]]("λt:real. g(c + t • basis_vector(j))")
			same := a.Have(
				"a derivative at 0 reads its function only near 0, so "+
					"f and g have the same partial derivatives at c along j",
				"∀d:real. partial_derivative_at(f, j, c, d) ⇔ partial_derivative_at(g, j, c, d)",
				Derive(func(b *Argument) {
					d := b.FixAs[Real]("d")
					b.Iff()
					b.Forward(
						"a derivative d of f's line at 0 is one of g's line",
						func(e *Argument, partial Fact) {
							e.Show(
								"t ↦ g(c + t·e_j) has derivative d at 0",
								By(
									partial,
									onLine,
									rPos,
									vec_derivative.PartialDerivativeAtDef,
									real_derivative.DerivativeLocal.At(gLine, fLine, zero, r, d)))
						})
					b.Backward(
						"a derivative d of g's line at 0 is one of f's line",
						func(e *Argument, partial Fact) {
							e.Show(
								"t ↦ f(c + t·e_j) has derivative d at 0",
								By(
									partial,
									onLine,
									rPos,
									vec_derivative.PartialDerivativeAtDef,
									real_derivative.DerivativeLocal.At(fLine, gLine, zero, r, d)))
						})
				}))
			a.Show(
				"the first half is the equivalence just shown, and by it the two "+
					"choices of PartialDerivativeDef choose among the same numbers",
				Simp(Fwd(PartialDerivativeDef), Fwd(same)),
				Refl())
		}),
})}

// PartialDerivativeAdd — the partial derivative of a sum.
var PartialDerivativeAdd = partialDerivativeAddThm{family.Add(registry.ProofEntry{
	Name: "PartialDerivativeAdd",
	Key:  "prop_79189c298adac65b",
	Deps: []registry.EntryLike{vec_derivative.PartialDerivativeAtDef, real_derivative.DerivativeAdd},
	Build: family.Card(Statement{
		Binders: "∀f g:((num → real) → real). ∀j:num. ∀c:(num → real). ∀a b:real.",
		Hypotheses: []string{
			"partial_derivative_at(f, j, c, a)",
			"partial_derivative_at(g, j, c, b)",
		},
		Conclusion: "partial_derivative_at(λx:(num → real). f(x) + g(x), j, c, a + b)",
	},
		"real_derivative.DerivativeAdd at 0 for t ↦ f(c + t·e_j) and t ↦ g(c + t·e_j)"),
})}

// PartialDerivativeMul — the partial derivative of a product, Leibniz's
// rule.
var PartialDerivativeMul = partialDerivativeMulThm{family.Add(registry.ProofEntry{
	Name: "PartialDerivativeMul",
	Key:  "prop_e03fae6909315ae2",
	Deps: []registry.EntryLike{vec_derivative.PartialDerivativeAtDef, real_derivative.DerivativeMul},
	Build: family.Card(Statement{
		Binders: "∀f g:((num → real) → real). ∀j:num. ∀c:(num → real). ∀a b:real.",
		Hypotheses: []string{
			"partial_derivative_at(f, j, c, a)",
			"partial_derivative_at(g, j, c, b)",
		},
		Conclusion: "partial_derivative_at(λx:(num → real). f(x) * g(x), j, c, a * g(c) + f(c) * b)",
	},
		"real_derivative.DerivativeMul at 0 for t ↦ f(c + t·e_j) and t ↦ g(c "+
			"+ t·e_j), whose values at 0 are f(c) and g(c), c + 0·e_j being c"),
})}

// PartialDerivativeChain — the chain rule for partial derivatives: the
// partial derivative of g ∘ f along j is Σᵢ ∂ᵢg(f(x))·∂ⱼfᵢ(x), for f and g
// of class C¹ on open sets.
var PartialDerivativeChain = partialDerivativeChainThm{family.Add(registry.ProofEntry{
	Name: "PartialDerivativeChain",
	Key:  "prop_11580977aff9a15e",
	Reading: "V open in ℝᵐ makes f(y) an m-vector, which is what the " +
		"m-dimensional reading of g at f(y) asks; class C¹ is load-bearing " +
		"on both sides, partial derivatives alone giving no chain rule.",
	Deps: []registry.EntryLike{
		vec_derivative.ContinuousPartialsDerivative,
		vec_derivative.VecDerivativeChain,
		vec_derivative.PartialFromDerivative,
		PartialDerivativeValue,
	},
	Build: family.Card(Statement{
		Binders: "∀n m:num. " +
			"∀U V:((num → real) → bool). " +
			"∀f:((num → real) → num → real). " +
			"∀g:((num → real) → real). " +
			"∀j:num. " +
			"∀x:(num → real).",
		Hypotheses: []string{
			"U ∈ euclidean_topology(n)",
			"V ∈ euclidean_topology(m)",
			"∀y:(num → real). y ∈ U ⇒ f(y) ∈ V",
			"∀i:num. i < m ⇒ vec_continuously_differentiable_on⟨n⟩(U, 1, λy:(num → real). f(y)(i))",
			"vec_continuously_differentiable_on⟨m⟩(V, 1, g)",
			"x ∈ U",
			"j < n",
		},
		Conclusion: "partial_derivative_at(λy:(num → real). g(f(y)), " +
			"    j, " +
			"    x, " +
			"    Σ_{i<m} partial_derivative(g, i, f(x)) * partial_derivative(λy:(num → real). f(y)(i), j, x))",
	},
		"continuous partial derivatives on a ball inside the open set give derivatives "+
			"(vec_derivative.ContinuousPartialsDerivative): f has one at x, and g, read as "+
			"the map y ↦ (g(y), 0, 0, …) into ℝ¹, one at f(x); the chain rule "+
			"(VecDerivativeChain) composes them, and PartialFromDerivative reads the "+
			"composite's derivative at e_j, the sum over i < m of the two Jacobians' entries"),
})}

// PartialDerivativeSymmetric — for a function of class C², two partial
// derivatives commute.
var PartialDerivativeSymmetric = partialDerivativeSymmetricThm{family.Add(registry.ProofEntry{
	Name: "PartialDerivativeSymmetric",
	Key:  "prop_92fb6224cf8f199e",
	Deps: []registry.EntryLike{vec_derivative.MixedPartialsCommute, PartialDerivativeValue},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀U:((num → real) → bool). " +
			"∀g:((num → real) → real). " +
			"∀i j:num. " +
			"∀x:(num → real).",
		Hypotheses: []string{
			"U ∈ euclidean_topology(n)",
			"vec_continuously_differentiable_on⟨n⟩(U, 2, g)",
			"i < n",
			"j < n",
			"x ∈ U",
		},
		Conclusion: "partial_derivative(partial_derivative(g, i), j, x) = " +
			"partial_derivative(partial_derivative(g, j), i, x)",
	},
		"for i = j there is nothing to show; otherwise U holds a square x + s·e_i + t·e_j, |s|, "+
			"|t| < r, on which g, ∂ᵢg, ∂ⱼg, ∂ⱼ∂ᵢg and ∂ᵢ∂ⱼg are what class C² gives, continuous at "+
			"x, and vec_derivative.MixedPartialsCommute equates the two mixed partials at x"),
})}
