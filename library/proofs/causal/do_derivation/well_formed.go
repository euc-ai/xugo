package do_derivation

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

// UnitWellFormed states that the unit, the atom whose three groups are
// empty, is well formed over any observed nodes: empty groups are
// observed and pairwise disjoint.
var UnitWellFormed = unitWellFormedThm{family.Add(registry.ProofEntry{
	Name: "UnitWellFormed",
	Key:  "prop_4e2ae94d1876db2b",
	Build: family.Theorem(
		"∀O:set(I). do_expr_wf(O, do_prob(∅, ∅, ∅))",
		Chain(Simp(Fwd(WellFormedDef)), BySets())),
})}

// DerivableWellFormed establishes well-formedness at both ends of a derivation.
var DerivableWellFormed = derivableWellFormedThm{family.Add(registry.ProofEntry{
	Name: "DerivableWellFormed",
	Key:  "prop_3e2eafa6b14c851c",
	Build: family.Theorem(Statement{
		Binders:    "∀E:(I → I → bool). ∀O:set(I). ∀e₁ e₂:do_expr(I).",
		Hypotheses: []string{"do_derivable(E, O, e₁, e₂)"},
		Conclusion: "do_expr_wf(O, e₁) ∧ do_expr_wf(O, e₂)",
	}, func(
		a *Argument,
		E *Arrow2[I, I, Bool],
		O *Expr[Set[I]],
		e1, e2 *Expr[DoExpr[I]],
		derivation Fact,
	) {
		unit := UnitWellFormed.At(O)

		fromGuard := Chain(StripQuant(), Derive(func(b *Argument) {
			guard := b.Assume()
			b.Do(By(guard))
		}))
		checkNodeSets := Chain(Simp(Fwd(WellFormedDef)), BySets())

		a.Do(ByInduction(DoDerivableInduct, derivation,
			Case(
				"reflexivity uses its well-formedness guard",
				fromGuard),
			Case(
				"symmetry swaps the two well-formed endpoints",
				fromGuard),
			Case(
				"transitivity keeps the two outer endpoints",
				fromGuard),
			Case(
				"sum congruence keeps the observed group and well-formed bodies",
				Simp(Fwd(WellFormedDef)),
				fromGuard),
			Case(
				"product congruence pairs the well-formed operands",
				By(WellFormedDef)),
			Case(
				"quotient congruence pairs the well-formed operands",
				By(WellFormedDef)),
			Case(
				"observation joins disjoint observed conditioning groups",
				checkNodeSets),
			Case(
				"exchange joins the moved group to either interventions or observations",
				checkNodeSets),
			Case(
				"deletion keeps the remaining interventions and observations disjoint",
				checkNodeSets),
			Case(
				"conditioning joins the event and conditioning groups in the numerator",
				checkNodeSets),
			Case(
				"marginalisation sums an observed group joined to the event",
				checkNodeSets),
			Case(
				"the empty event and unit preserve the node-set guards",
				StripQuant(),
				BySets(unit, WellFormedDef)),
			Case(
				"commutativity uses the same two well-formed factors",
				By(WellFormedDef)),
			Case(
				"associativity uses the same three well-formed factors",
				By(WellFormedDef)),
			Case(
				"the unit is a well-formed extra factor",
				StripQuant(),
				By(unit, WellFormedDef)),
			Case(
				"self-division uses a well-formed operand twice and yields the unit",
				StripQuant(),
				By(unit, WellFormedDef)),
			Case(
				"the reciprocal uses the unit and the original denominator",
				StripQuant(),
				By(unit, WellFormedDef)),
			Case(
				"factoring a sum keeps the observed group and both operands",
				By(WellFormedDef)),
			Case(
				"nested sums combine two observed groups",
				checkNodeSets),
			Case(
				"the empty sum binds an observed group",
				BySets(WellFormedDef)),
		))
	}),
})}
