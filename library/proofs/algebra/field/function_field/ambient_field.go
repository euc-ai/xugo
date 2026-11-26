// ambient_field.go — regularity of a function field read in a subfield of the ambient field.

package function_field

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// RegularFunctionFieldInAmbient — a function field regular over k, read
// inside its own carrier K, is regular over k read in any field holding K:
// the restriction keeps the operations, so algebraicity over a set reads the
// same in both fields, and K's subfields are the subfields of M inside K, so
// adjoining to k inside K gives the same field in both.
var RegularFunctionFieldInAmbient = regularFunctionFieldInAmbientThm{family.Add(registry.ProofEntry{
	Name: "RegularFunctionFieldInAmbient",
	Key:  "prop_c0f2eb5e5fe00e6e",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k K:set(A).",
		Hypotheses: []string{
			"subfield(M, K)",
			"regular_function_field(restrict_field(M, K), k, K)",
		},
		Conclusion: "regular_function_field(M, k, K)",
	}, func(a *Argument, M field.FieldFact[on.M], k, K *Expr[Set[A]], subfieldK, regularInK Fact) {
		ops := a.TermAs[FieldOps[A]]("M")
		inRestriction := a.Conjuncts(
			a.Unfolded(regularInK, RegularFunctionFieldDef),
			"k is a subfield of the restriction",
			"K is a subfield of the restriction",
			"k lies in K",
			"the constants are perfect in the restriction",
			"K is finitely generated over k in the restriction",
			"K has a parameter over k in the restriction",
			"k is exactly the constants in the restriction")
		kInK := inRestriction[2]
		algebraicAgrees := a.Have(
			"Algebraicity reads the operations alone, and the restriction keeps them",
			"∀S:set(A). ∀x:A. algebraic_over(restrict_field(M, K), S, x) ⇔ algebraic_over(M, S, x)",
			Unfold(algebraic_element.AlgebraicOverDef))
		adjoinAgrees := a.Have(
			"Adjoining to k inside K gives one field in the restriction and in M",
			"∀E:set(A). E ⊆ K ⇒ field_adjoin(restrict_field(M, K), k, E) = field_adjoin(M, k, E)",
			Derive(func(b *Argument) {
				E := b.FixAs[Set[A]]()
				eInK := b.Assume()
				inM := b.Have(
					"The adjoined field of M holds k and E, which lie in K and so in M",
					"subfield(M, field_adjoin(M, k, E)) ∧ k ⊆ field_adjoin(M, k, E) ∧ E ⊆ field_adjoin(M, k, E)",
					By(
						kInK,
						eInK,
						subfieldK,
						field.SubfieldSubset.At(ops, K),
						set_order.SubsetTrans,
						algebraic_element.AdjoinSubfield.Read(M).At(k, E)))
				restricted := b.Have(
					"The restriction of M to K is a field",
					"field_on(restrict_field(M, K))",
					By(subfieldK, field.SubfieldFieldOn.Read(M).At(K)))
				inRestricted := b.Have(
					"The adjoined field of the restriction holds k and E",
					"subfield(restrict_field(M, K), field_adjoin(restrict_field(M, K), k, E)) ∧ "+
						"k ⊆ field_adjoin(restrict_field(M, K), k, E) ∧ "+
						"E ⊆ field_adjoin(restrict_field(M, K), k, E)",
					By(kInK, eInK, algebraic_element.AdjoinSubfield.Read(restricted).At(k, E)))
				below := b.Have(
					"M's adjoined field is a subfield of the restriction, since K holds k and E",
					"subfield(restrict_field(M, K), field_adjoin(M, k, E))",
					By(
						subfieldK,
						inM,
						kInK,
						eInK,
						algebraic_element.AdjoinLeast.Read(M).At(k, E, K),
						field.SubfieldRestrict.At(ops, K, b.TermAs[Set[A]]("field_adjoin(M, k, E)"))))
				above := b.Have(
					"The restriction's adjoined field is a subfield of M",
					"subfield(M, field_adjoin(restrict_field(M, K), k, E))",
					By(
						subfieldK,
						inRestricted,
						field.SubfieldTrans.At(ops, K, b.TermAs[Set[A]]("field_adjoin(restrict_field(M, K), k, E)"))))
				b.Show(
					"Each adjoined field contains the other, by leastness",
					By(
						below,
						inM,
						above,
						inRestricted,
						set_order.SubsetAntisym,
						algebraic_element.AdjoinLeast.Read(restricted).At(k, E, b.TermAs[Set[A]]("field_adjoin(M, k, E)")),
						algebraic_element.AdjoinLeast.Read(M).At(
							k, E, b.TermAs[Set[A]]("field_adjoin(restrict_field(M, K), k, E)"))))
			}))
		subfieldConstants := a.Have(
			"k is a subfield of M, being one of the subfield K",
			"subfield(M, k)",
			By(subfieldK, inRestriction[0], field.SubfieldTrans.At(ops, K, k)))
		perfect := a.Have(
			"k stays perfect: restricting M to K and then to k is restricting M to k",
			"perfect_field(restrict_field(M, k))",
			Unfold(field.RestrictFieldDef))
		generated := a.Have(
			"The finite set generating K in the restriction generates it in M",
			"∃E:set(A). finite(E) ∧ E ⊆ K ∧ field_adjoin(M, k, E) = K",
			By(inRestriction[4], adjoinAgrees))
		parameter := a.Have(
			"The parameter of the restriction is a parameter in M",
			"∃t:A. "+
				"    t ∈ K ∧ "+
				"    ¬algebraic_over(M, k, t) ∧ "+
				"    (∀x:A. x ∈ K ⇒ algebraic_over(M, field_adjoin(M, k, {t}), x))",
			Derive(func(b *Argument) {
				s, sData := b.UnpackAs[A](inRestriction[5], "s")
				sParts := b.Conjuncts(
					sData,
					"s lies in K",
					"s is transcendental over k in the restriction",
					"K is algebraic over k(s) in the restriction")
				sameField := b.Have(
					"k(s) is one field in the restriction and in M",
					"field_adjoin(restrict_field(M, K), k, {s}) = field_adjoin(M, k, {s})",
					By(sParts[0], set_order.SingSubset.At(K, s), adjoinAgrees.At(b.TermAs[Set[A]]("{s}"))))
				algebraic := b.Have(
					"K is algebraic over k(s) in M",
					"∀x:A. x ∈ K ⇒ algebraic_over(M, field_adjoin(M, k, {s}), x)",
					sameField.RwRev(),
					By(sParts[2], algebraicAgrees))
				b.Take(s)
				b.Show(
					"s keeps its three properties in M",
					By(sParts[0], sParts[1], algebraic, algebraicAgrees))
			}))
		exact := a.Have(
			"The elements of K algebraic over k in M are those of the restriction",
			"∀x:A. x ∈ K ∧ algebraic_over(M, k, x) ⇒ x ∈ k",
			By(inRestriction[6], algebraicAgrees))
		a.Show(
			"The conditions of regularity all stand in M",
			Unfold(RegularFunctionFieldDef),
			By(subfieldConstants, subfieldK, kInK, perfect, generated, parameter, exact))
	}),
})}

// RegularFunctionFieldInRestriction — a function field regular over k in a
// field holding it stays regular over k read inside its own carrier: the
// restriction keeps the operations, so algebraicity reads the same, and
// adjoining to k inside K gives one field in both.
var RegularFunctionFieldInRestriction = regularFunctionFieldInRestrictionThm{family.Add(registry.ProofEntry{
	Name: "RegularFunctionFieldInRestriction",
	Key:  "prop_35b7e9bdcbf97c25",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k K:set(A).",
		Hypotheses: []string{
			"subfield(M, K)",
			"regular_function_field(M, k, K)",
		},
		Conclusion: "regular_function_field(restrict_field(M, K), k, K)",
	}, func(a *Argument, M field.FieldFact[on.M], k, K *Expr[Set[A]], subfieldK, regular Fact) {
		ops := a.TermAs[FieldOps[A]]("M")
		inAmbient := a.Unfolded(regular, RegularFunctionFieldDef)
		kInK := a.Have(
			"k lies in K",
			"k ⊆ K",
			By(inAmbient))
		algebraicAgrees := a.Have(
			"Algebraicity reads the operations alone, and the restriction keeps them",
			"∀S:set(A). ∀x:A. algebraic_over(restrict_field(M, K), S, x) ⇔ algebraic_over(M, S, x)",
			Unfold(algebraic_element.AlgebraicOverDef))
		adjoinAgrees := a.Have(
			"Adjoining to k inside K gives one field in the restriction and in M",
			"∀E:set(A). E ⊆ K ⇒ field_adjoin(restrict_field(M, K), k, E) = field_adjoin(M, k, E)",
			Derive(func(b *Argument) {
				E := b.FixAs[Set[A]]()
				eInK := b.Assume()
				inM := b.Have(
					"The adjoined field of M holds k and E, which lie in K and so in M",
					"subfield(M, field_adjoin(M, k, E)) ∧ k ⊆ field_adjoin(M, k, E) ∧ E ⊆ field_adjoin(M, k, E)",
					By(
						kInK,
						eInK,
						subfieldK,
						field.SubfieldSubset.At(ops, K),
						set_order.SubsetTrans,
						algebraic_element.AdjoinSubfield.Read(M).At(k, E)))
				restricted := b.Have(
					"The restriction of M to K is a field",
					"field_on(restrict_field(M, K))",
					By(subfieldK, field.SubfieldFieldOn.Read(M).At(K)))
				inRestricted := b.Have(
					"The adjoined field of the restriction holds k and E",
					"subfield(restrict_field(M, K), field_adjoin(restrict_field(M, K), k, E)) ∧ "+
						"k ⊆ field_adjoin(restrict_field(M, K), k, E) ∧ "+
						"E ⊆ field_adjoin(restrict_field(M, K), k, E)",
					By(kInK, eInK, algebraic_element.AdjoinSubfield.Read(restricted).At(k, E)))
				below := b.Have(
					"M's adjoined field is a subfield of the restriction, since K holds k and E",
					"subfield(restrict_field(M, K), field_adjoin(M, k, E))",
					By(
						subfieldK,
						inM,
						kInK,
						eInK,
						algebraic_element.AdjoinLeast.Read(M).At(k, E, K),
						field.SubfieldRestrict.At(ops, K, b.TermAs[Set[A]]("field_adjoin(M, k, E)"))))
				above := b.Have(
					"The restriction's adjoined field is a subfield of M",
					"subfield(M, field_adjoin(restrict_field(M, K), k, E))",
					By(
						subfieldK,
						inRestricted,
						field.SubfieldTrans.At(ops, K, b.TermAs[Set[A]]("field_adjoin(restrict_field(M, K), k, E)"))))
				b.Show(
					"Each adjoined field contains the other, by leastness",
					By(
						below,
						inM,
						above,
						inRestricted,
						set_order.SubsetAntisym,
						algebraic_element.AdjoinLeast.Read(restricted).At(k, E, b.TermAs[Set[A]]("field_adjoin(M, k, E)")),
						algebraic_element.AdjoinLeast.Read(M).At(
							k, E, b.TermAs[Set[A]]("field_adjoin(restrict_field(M, K), k, E)"))))
			}))
		constantsSubfield := a.Have(
			"k is a subfield of the restriction, lying in K",
			"subfield(restrict_field(M, K), k)",
			By(inAmbient, kInK, field.SubfieldRestrict.At(ops, K, k)))
		wholeSubfield := a.Have(
			"so is K itself",
			"subfield(restrict_field(M, K), K)",
			By(subfieldK, field.SubfieldRestrict.At(ops, K, K), set_order.SubsetRefl))
		perfect := a.Have(
			"k stays perfect: restricting M to K and then to k is restricting M to k",
			"perfect_field(restrict_field(restrict_field(M, K), k))",
			Unfold(field.RestrictFieldDef))
		generated := a.Have(
			"The finite set generating K in M generates it in the restriction",
			"∃E:set(A). finite(E) ∧ E ⊆ K ∧ field_adjoin(restrict_field(M, K), k, E) = K",
			By(inAmbient, adjoinAgrees))
		parameter := a.Have(
			"A parameter in M is a parameter in the restriction",
			"∃t:A. "+
				"    t ∈ K ∧ "+
				"    ¬algebraic_over(restrict_field(M, K), k, t) ∧ "+
				"    (∀x:A. "+
				"        x ∈ K ⇒ "+
				"        algebraic_over(restrict_field(M, K), field_adjoin(restrict_field(M, K), k, {t}), x))",
			Derive(func(b *Argument) {
				s, sData := b.ObtainAs[A](
					"take a parameter of K over k in M",
					"∃t:A. "+
						"    t ∈ K ∧ "+
						"    ¬algebraic_over(M, k, t) ∧ "+
						"    (∀x:A. x ∈ K ⇒ algebraic_over(M, field_adjoin(M, k, {t}), x))",
					By(inAmbient))
				sameField := b.Have(
					"k(t) is one field in the restriction and in M",
					"field_adjoin(restrict_field(M, K), k, {t}) = field_adjoin(M, k, {t})",
					By(sData, set_order.SingSubset.At(K, s), adjoinAgrees))
				b.Take(s)
				b.Show(
					"t keeps its three properties in the restriction",
					By(sData, algebraicAgrees, sameField))
			}))
		exact := a.Have(
			"The elements of K algebraic over k in the restriction are those of M",
			"∀x:A. x ∈ K ∧ algebraic_over(restrict_field(M, K), k, x) ⇒ x ∈ k",
			By(inAmbient, algebraicAgrees))
		a.Show(
			"The conditions of regularity all stand in the restriction",
			Unfold(RegularFunctionFieldDef),
			By(constantsSubfield, wholeSubfield, kInK, perfect, generated, parameter, exact))
	}),
})}
