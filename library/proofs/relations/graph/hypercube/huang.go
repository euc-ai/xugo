package hypercube

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/registry"
)

// Huang gives a vertex of large induced degree in every strict majority
// of a finite cube. It signs the cube so that the square counts the
// coordinates, chooses a nonzero vector supported on H whose signed image
// vanishes at the omitted vertices, and hands both to SupportedDegreeBound.
var Huang = huangThm{family.Add(registry.ProofEntry{
	Name: "Huang", Key: "prop_ab16562212a7676d",
	Build: family.Theorem(Statement{
		Binders:    "∀S:set(A). ∀H:set(set(A)).",
		Hypotheses: []string{"finite(S)", "H ⊆ «vertices»", "card(«vertices») < 2 * card(H)"},
		Conclusion: "∃X:set(A). X ∈ H ∧ card(S) ≤ «degree»(X) * «degree»(X)",
		Abbrev: Abbrev{
			{Name: "vertices", Text: "{Y:set(A) | Y ⊆ S}"},
			{Name: "degree", Text: "λX:set(A). graph_degree(H,cube_adjacent(S),X)"},
		},
	}, func(a *Argument, S *Expr[Set[A]], H *Expr[Set[Set[A]]], finite, within, majority Fact) {
		V := a.TermAs[Set[Set[A]]]("«vertices»")
		finiteV := a.Have(
			"the cube has finitely many vertices",
			"finite(«vertices»)",
			By(finite, finite_set.FinitePowerset.At(S)))
		M, signed := a.ObtainAs[Fun2[Set[A], Set[A], Real]](
			"choose a signing whose square counts the coordinates",
			"∃M:set(A) → set(A) → real. cube_signing(S,M) ∧ cube_square(S,M,&card(S))",
			By(finite, SignedCube.At(S)))
		v, kernel := a.ObtainAs[Fun[Set[A], Real]](
			"choose a nonzero vector whose image vanishes at the omitted vertices",
			"∃v:set(A) → real. "+
				"    (∃X:set(A). X ∈ H ∧ v(X) ≠ &0) ∧ "+
				"    (∀X:set(A). X ∉ H ⇒ v(X) = &0) ∧ "+
				"    (∀X:set(A). X ∈ «vertices» ∧ X ∉ H ⇒ Σ_{Y∈«vertices»} M(X,Y)*v(Y) = &0)",
			By(finiteV, majority, within, module_dimension.MajorityKernelVector.At(V, H, M)))
		parts := a.Conjuncts(
			kernel,
			"nonzero at a vertex of H",
			"zero off H",
			"the omitted rows vanish")
		nonzero, zeroOff, omittedRows := parts[0], parts[1], parts[2]
		image := a.Have(
			"the signed cube action vanishes on the omitted vertices",
			"∀X:set(A). X ⊆ S ∧ X ∉ H ⇒ cube_action(S, M, v, X) = &0",
			Derive(func(b *Argument) {
				X := b.FixAs[Set[A]]("X")
				outside := b.Assume()
				vertex := b.Have(
					"each subset of S is a cube vertex",
					"X ∈ «vertices»",
					BySets(outside))
				b.Show(
					"the action at X is its row sum",
					By(vertex, outside, omittedRows, cubeActionDef.At(S, M, v, X)))
			}))
		a.Show(
			"two applications of the row bound give a vertex with degree squared at least the dimension",
			By(finite, zeroOff, image, nonzero, within, signed, SupportedDegreeBound.At(S, H, M, v)))
	}),
})}

// HuangDegreeSquare states the induced-degree bound in terms of the
// dimension n and the threshold 2^(n−1).
var HuangDegreeSquare = huangDegreeSquareThm{family.Add(registry.ProofEntry{
	Name: "HuangDegreeSquare", Key: "prop_92a8386f9d004f2e",
	Build: family.Sections(Statement{
		Binders:    "∀S:set(A). ∀H:set(set(A)). ∀n:num.",
		Hypotheses: []string{"finite(S)", "card(S) = n", "H ⊆ «vertices»", "2 ^ (n - 1) < card(H)"},
		Conclusion: "∃X:set(A). X ∈ H ∧ n ≤ «degree»(X) * «degree»(X)",
		Abbrev: Abbrev{
			{Name: "vertices", Text: "{Y:set(A) | Y ⊆ S}"},
			{Name: "degree", Text: "λX:set(A). graph_degree(H,cube_adjacent(S),X)"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		double := ctx.Lemma("∀n:num. 2 ^ n ≤ 2 * 2 ^ (n - 1)", func(a *Argument, n *Expr[Nat]) {
			a.Cases(a.TermAs[Bool]("n = 0"))
			a.When(
				"at n = 0 both powers equal one",
				func(b *Argument, zero Fact) {
					b.Show(
						"one is at most two",
						ByArith(zero))
				})
			a.Otherwise(
				"for positive n the power doubles the one at n − 1",
				func(b *Argument, positive Fact) {
					pred := b.Have(
						"a positive n is the successor of n − 1",
						"suc(n-1) = n",
						ByArith(positive))
					power := b.Have(
						"the two exponents agree",
						"2 ^ suc(n-1) = 2 ^ n",
						By(Normalized, pred))
					b.Show(
						"a successor exponent doubles the power of two",
						ByArith(power, nat_arith.PowTwoSuc.At(b.TermAs[Nat]("n-1"))))
				})
		})
		return ctx.Theorem(headline, func(
			a *Argument,
			S *Expr[Set[A]],
			H *Expr[Set[Set[A]]],
			n *Expr[Nat],
			finite, size, within, threshold Fact,
		) {
			count := a.Have(
				"the cube has two choices in each of its n coordinates",
				"card(«vertices») = 2 ^ n",
				By(finite, size, cardinality.CardPowerset.At(S)))
			majority := a.Have(
				"the retained vertices comprise a strict majority",
				"card(«vertices») < 2*card(H)",
				ByArith(threshold, count, At(double, n)))
			a.Show(
				"apply the strict majority bound in dimension n",
				By(finite, majority, size, within, Huang.At(S, H)))
		})
	}),
})}
