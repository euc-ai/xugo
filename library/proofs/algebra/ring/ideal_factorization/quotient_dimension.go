package ideal_factorization

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_extension"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/fractional_ideal"
	"github.com/euc-ai/xugo/library/registry"
)

// DivisionShrinksColength — dividing an invertible ideal of a subring by an
// invertible ideal above it gives an ideal between it and the ring, so the
// colength does not grow; and it strictly drops unless the divisor is the ring,
// since an ideal equal to its quotient has the divisor cancelled to the ring.
var DivisionShrinksColength = divisionShrinksColengthThm{family.Add(registry.ProofEntry{
	Name: "DivisionShrinksColength",
	Key:  "prop_62ed9fa2b3ff41ac",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k S H Q:set(A).",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"subfield(L, k)",
			"k ⊆ S",
			"ring_ideal(«chart», H)",
			"H ≠ {L.zero}",
			"invertible_fractional(field_ring(L), S, H)",
			"ring_ideal(«chart», Q)",
			"invertible_fractional(field_ring(L), S, Q)",
			"H ⊆ Q",
			"finite_dimensional(«scalars», quotient_module(«vectors»(S), H))",
		},
		Conclusion: "ring_ideal(«chart», «J») ∧ «dim»(«J») ≤ «dim»(H) ∧ (Q ≠ S ⇒ «dim»(«J») < «dim»(H))",
		Abbrev: Abbrev{
			{Name: "chart", Text: "restrict_ring(field_ring(L), S)"},
			{Name: "scalars", Text: "restrict_ring(field_ring(L), k)"},
			{Name: "space", Text: "regular_module(field_ring(L))"},
			{Name: "vectors", Text: "λX:set(A). restrict_module(«space», X)"},
			{Name: "J", Text: "fractional_mul(field_ring(L), S, H, fractional_inverse(field_ring(L), S, Q))"},
			{Name: "dim", Text: "λX:set(A). module_dim(«scalars», quotient_module(«vectors»(S), X))"},
		},
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, S, H, Q *Expr[Set[A]],
			subring, constants, kInS, idealH, nonzero, invertibleH, idealQ, invertibleQ, below, colength Fact,
		) {
			ring := a.TermAs[RingOps[A]]("field_ring(L)")
			chart := a.TermAs[RingOps[A]]("«chart»")
			scalars := a.TermAs[RingOps[A]]("«scalars»")
			space := a.TermAs[module_record.ModuleOps[A, A]]("«space»")
			inverse := a.TermAs[Fun[A, A]]("L.inv")
			J := a.TermAs[Set[A]]("«J»")
			scalarField := a.Have(
				"k is a field of scalars for L",
				"ring_subfield(«scalars», L.inv, «scalars».carrier) ∧ module_on(«scalars», «space»)",
				By(
					constants,
					field.SubfieldRingSubfield.Read(L).At(k, k),
					field_extension.SubfieldScalars.Read(L).At(k),
					module_record.RestrictRingDef.At(ring, k)))
			divided := a.Conjuncts(
				GroupPremises(
					subring, idealH, nonzero, idealQ, below, invertibleQ, DivideByInvertibleIdeal.Read(L).At(S, H, Q)),
				"the quotient is an ideal",
				"nonzero",
				"whose product with Q is H",
				"and which lies above H")
			subspaces := a.Have(
				"an ideal of S is a module over S, and over k a subspace of L inside S",
				Statement{
					Binders:    "∀X:set(A).",
					Hypotheses: []string{"ring_ideal(«chart», X)"},
					Conclusion: "submodule(«chart», «space», X) ∧ submodule(«scalars», «space», X) ∧ X ⊆ S",
				},
				Derive(func(b *Argument) {
					X := b.FixAs[Set[A]]("X")
					ideal := b.Assume()
					b.Show(
						"an ideal is a module over S, and k lies in S",
						By(
							subring,
							ideal,
							kInS,
							fractional_ideal.IntegralIdealFractional.Read(L).At(S, X),
							submodule.SubmoduleRestrictScalars.At(chart, space, X, scalars),
							module_record.RestrictRingDef.At(ring, k),
							module_record.RestrictRingDef.At(ring, S)))
				}))
			wholeRing := a.Have(
				"S is a module over itself, and over k a subspace of L",
				"submodule(«chart», «space», S) ∧ submodule(«scalars», «space», S)",
				By(
					subring,
					kInS,
					fractional_ideal.SubringSubmodule.Read(L).At(S),
					submodule.SubmoduleRestrictScalars.At(chart, space, S, scalars),
					module_record.RestrictRingDef.At(ring, k),
					module_record.RestrictRingDef.At(ring, S)))
			chain := a.Conjuncts(
				a.Have(
					"along S ⊇ J ⊇ H, J/H is finite-dimensional and the dimensions add",
					"finite_dimensional(«scalars», quotient_module(«vectors»(«J»), H)) ∧ "+
						"«dim»(H) = «dim»(«J») + module_dim(«scalars», quotient_module(«vectors»(«J»), H))",
					By(
						scalarField,
						wholeRing,
						divided[0],
						divided[3],
						idealH,
						subspaces.At(J),
						subspaces.At(H),
						colength,
						module_dimension.QuotientChainDim.At(scalars, space, inverse, S, J, H))),
				"J/H is finite-dimensional",
				"and the dimension of S/H is the sum")
			shrinks := a.Have(
				"so the colength does not grow",
				"«dim»(«J») ≤ «dim»(H)",
				ByArith(chain[1]))
			strict := a.Have(
				"and it drops unless Q is S",
				"Q ≠ S ⇒ «dim»(«J») < «dim»(H)",
				Derive(func(b *Argument) {
					proper := b.Assume()
					distinct := b.Have(
						"J is not H, or Q would cancel to S",
						"«J» ≠ H",
						Derive(func(c *Argument) {
							same := c.SupposeNot()
							inField := c.Have(
								"H and Q lie in L",
								"H ⊆ L.carrier ∧ Q ⊆ L.carrier",
								BySets(
									idealH,
									idealQ,
									subspaces.At(H),
									subspaces.At(Q),
									subring,
									comm_ring.SubringSubset.At(ring, S)))
							multiples := c.Have(
								"so H · Q and H · S are both H",
								"fractional_mul(field_ring(L), S, H, Q) = fractional_mul(field_ring(L), S, H, S)",
								By(
									same,
									divided[2],
									inField,
									idealH,
									subring,
									subspaces.At(H),
									comm_ring.SubringSubset.At(ring, S),
									fractional_ideal.FractionalMulComm.Read(L).At(S, H, Q),
									fractional_ideal.FractionalMulComm.Read(L).At(S, H, S),
									fractional_ideal.FractionalMulOne.Read(L).At(S, H)))
							c.Show(
								"cancelling the invertible H, Q is S",
								By(
									Normalized,
									proper,
									multiples,
									invertibleH,
									subring,
									wholeRing,
									idealQ,
									subspaces.At(Q),
									InvertibleMulCancel.Read(L).At(S, H, Q, S)))
						}))
					positive := b.Have(
						"so J/H has positive dimension",
						"module_dim(«scalars», quotient_module(«vectors»(«J»), H)) ≠ 0",
						By(
							distinct,
							chain[0],
							scalarField,
							divided[0],
							idealH,
							subspaces.At(J),
							subspaces.At(H),
							divided[3],
							module_dimension.QuotientDimZeroIff.At(scalars, space, inverse, J, H)))
					b.Show(
						"the two dimensions add up to that of S/H",
						ByArith(chain[1], positive))
				}))
			a.Show(
				"H over Q is an ideal of the chart, of colength at "+
					"most that of H, and strictly less unless Q is the ring",
				By(divided[0], shrinks, strict))
		}),
})}
