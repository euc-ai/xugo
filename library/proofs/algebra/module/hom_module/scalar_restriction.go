// scalar_restriction.go — independence survives the restriction of
// scalars along a one-to-one ring map: a set is independent over R acting
// through f exactly when it is independent over the image of f.

package hom_module

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/linear_independence"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/registry"
)

// ScalarRestrictionIndependent — a set of vectors of a module over T is
// independent over R acting through a one-to-one ring map f exactly when
// it is independent over the image of f: a coefficient a(x) in R acts as
// f(a(x)) in the image, and a coefficient in the image is f of a chosen
// one in R, which f, one-to-one, sends to zero only from zero.
var ScalarRestrictionIndependent = scalarRestrictionIndependentThm{family.Add(registry.ProofEntry{
	Name: "ScalarRestrictionIndependent",
	Key:  "prop_c5e650749b21b2e",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀T:ring_ops(C). ∀f:(A → C). ∀N:module_ops(C, D). ∀S:set(D).",
		Hypotheses: []string{
			"ring_homomorphism(R, T, f)",
			"injective_on(R.carrier, f)",
		},
		Conclusion: "module_independent(R, scalar_restriction(f, N), S) ⇔ " +
			"module_independent(restrict_ring(T, image(f, R.carrier)), N, S)",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			T *Expr[RingOps[C]],
			f *Arrow[A, C],
			N *Expr[ModuleOps[C, D]],
			S *Expr[Set[D]],
			given Fact,
		) {
			parts := a.Conjuncts(
				given,
				"f is a ring map from R to T",
				"f is one-to-one on R")
			ringMap, oneToOne := parts[0], parts[1]
			a.Do(Unfold(linear_independence.ModuleIndependentDef))
			a.Iff()
			a.Forward(
				"a coefficient in the image is f of one in R, so a "+
					"vanishing combination over the image is one over R",
				func(b *Argument, overR Fact) {
					kept := b.Conjuncts(
						overR,
						"S lies in N",
						"over R only zero coefficients give a vanishing combination")
					overImage := b.Have(
						"a vanishing combination with coefficients in the image of f has zero coefficients",
						Statement{
							Binders: "∀U:set(D). ∀c:(D → C).",
							Hypotheses: []string{
								"finite(U)",
								"U ⊆ S",
								"∀x:D. x ∈ U ⇒ c(x) ∈ image(f, R.carrier)",
								"module_sum(N.add, N.zero, U, λx:D. c(x) • x) = N.zero",
							},
							Conclusion: "∀x:D. x ∈ U ⇒ c(x) = T.zero",
						},
						Derive(func(d *Argument) {
							U := d.FixAs[Set[D]]("U")
							d.FixAs[Fun[D, C]]("c")
							vanishing := d.Assume()
							e, chosen := d.Obtain(
								"each coefficient is f of a coefficient in R",
								"∃e:(D → A). ∀x:D. x ∈ U ⇒ e(x) ∈ R.carrier ∧ c(x) = f(e(x))",
								By(vanishing, set_basic.InImage),
								Named("e"))
							zero := d.Have(
								"the combination with coefficients e is the same combination, so e vanishes on U",
								"∀x:D. x ∈ U ⇒ e(x) = R.zero",
								By(
									kept[1].At(U, e),
									chosen,
									vanishing,
									At(
										module.ModuleSumCongruence,
										d.Term("N.add"),
										d.Term("N.zero"),
										U,
										d.Term("λx:D. N.smul(f(e(x)), x)"),
										d.Term("λx:D. N.smul(c(x), x)"))))
							d.Show(
								"so each coefficient is f(R.zero) = T.zero",
								By(ring_homomorphism.MapZero.Read(ringMap), zero, chosen))
						}))
					b.Show(
						"S lies in N and only zero coefficients from the image vanish a combination",
						By(kept[0], overImage))
				})
			a.Backward(
				"a coefficient a(x) of R acts as f(a(x)) in the image, and f is one-to-one",
				func(b *Argument, overImage Fact) {
					kept := b.Conjuncts(
						overImage,
						"S lies in N",
						"over the image only zero coefficients give a vanishing combination")
					overR := b.Have(
						"a vanishing combination over R through f has zero coefficients",
						Statement{
							Binders: "∀U:set(D). ∀e:(D → A).",
							Hypotheses: []string{
								"finite(U)",
								"U ⊆ S",
								"∀x:D. x ∈ U ⇒ e(x) ∈ R.carrier",
								"module_sum(N.add, N.zero, U, λx:D. f(e(x)) • x) = N.zero",
							},
							Conclusion: "∀x:D. x ∈ U ⇒ e(x) = R.zero",
						},
						Derive(func(d *Argument) {
							U := d.FixAs[Set[D]]("U")
							d.FixAs[Fun[D, A]]("e")
							vanishing := d.Assume()
							images := d.Have(
								"the same combination has the coefficients f(e(x)) in the image, which vanish",
								"∀x:D. x ∈ U ⇒ f(e(x)) = T.zero",
								By(kept[1].At(U, d.Term("λx:D. f(e(x))")), vanishing, set_image.FunInImage))
							d.Show(
								"f(e(x)) = T.zero = f(R.zero), and f is one-to-one on R",
								By(
									ring_homomorphism.MapZero.Read(ringMap),
									comm_ring.ZeroIn.Read(ring_homomorphism.Source.Read(ringMap)),
									images,
									vanishing,
									oneToOne,
									functions.InjectiveOnDef))
						}))
					b.Show(
						"S lies in N and only zero coefficients from R vanish a combination through f",
						By(kept[0], overR))
				})
		}),
})}
