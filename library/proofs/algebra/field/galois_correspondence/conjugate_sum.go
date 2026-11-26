// conjugate_sum.go — on a Galois extension C of K the sum of the conjugates
// is a K-linear form into K: the group is finite, each automorphism is
// K-linear, and the sum is fixed by the group, whose fixed field is K.

package galois_correspondence

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_automorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_extension"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/symmetric_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/registry"
)

// GaloisTraceLinear — the sum of the conjugates is a K-linear form on a Galois
// extension C of K: each automorphism is K-linear, and a value fixed by the
// whole group lies in K.
var GaloisTraceLinear = galoisTraceLinearThm{family.Add(registry.ProofEntry{
	Name: "GaloisTraceLinear",
	Key:  "prop_4695bf17b4386fb5",
	Build: family.Theorem(Statement{
		Abbrev: Abbrev{
			{Name: "trace", Text: "λb:A. " +
				"    module_sum(M.add, " +
				"        M.zero, " +
				"        field_automorphisms(M, K, C), " +
				"        λg:permutation(A). permutation_map(g, b))"},
			{Name: "scalars", Text: "restrict_ring(field_ring(M), K)"},
			{Name: "vectors", Text: "restrict_module(regular_module(field_ring(M)), C)"},
		},
		Binders: "∀M:field_on(A). ∀K C:set(A).",
		Hypotheses: []string{
			"subfield(M, K)",
			"subfield(M, C)",
			"K ⊆ C",
			"galois_over(M, K, C)",
		},
		Conclusion: "finite(field_automorphisms(M, K, C)) ∧ " +
			"module_homomorphism(«scalars», «vectors», regular_module(«scalars»), «trace»)",
	},
		func(a *Argument, M field.FieldFact[on.M], K, C *Expr[Set[A]], subK, subC, KInC, galois Fact) {
			m := a.TermAs[FieldOps[A]]("M")
			scalars := a.TermAs[module_record.RingOps[A]]("«scalars»")
			vectors := a.TermAs[module_record.ModuleOps[A, A]]("«vectors»")
			G := a.TermAs[Set[symmetric_group.Permutation[A]]]("field_automorphisms(M, K, C)")
			trace := a.TermAs[Fun[A, A]]("«trace»")
			add := a.TermAs[Op[A]]("M.add")
			zero := a.TermAs[A]("M.zero")
			moduleC := a.Have(
				"C is a module over K",
				"module_on(«scalars», «vectors»)",
				By(M, subK, subC, KInC, field_extension.ExtensionModuleOn.Read(M).At(K, C)))
			baseRing := a.Have(
				"K is a ring under the operations of M",
				"comm_ring_on(«scalars»)",
				By(subK, field.SubfieldCommRing.Read(M).At(K)))
			finiteExtension := a.Conjuncts(
				a.Unfolded(galois, GaloisOverDef),
				"C is finite over K",
				"C is normal over K",
				"C is separable over K")[0]
			finiteG := a.Conjuncts(
				GroupPremises(
					subK, subC, KInC, finiteExtension, field_automorphism.AutomorphismsBound.Read(M).At(K, C)),
				"a finite extension has finitely many automorphisms",
				"at most its degree")[0]
			fixedField := a.Have(
				"K is the field fixed by the group",
				"fixed_field(C, field_automorphisms(M, K, C)) = K",
				By(subK, subC, KInC, finiteExtension, galois, GaloisIffFixed.Read(M).At(K, C)))
			conjugates := a.Have(
				"an automorphism is K-linear and keeps C",
				"∀g:permutation(A). ∀b:A. g ∈ field_automorphisms(M, K, C) ∧ b ∈ C ⇒ permutation_map(g, b) ∈ C",
				Derive(func(c *Argument) {
					g := c.FixAs[symmetric_group.Permutation[A]]("g")
					c.FixAs[A]("b")
					members := c.Assume()
					linear := c.Have(
						"g is linear over K",
						"module_homomorphism(«scalars», «vectors», «vectors», permutation_map(g))",
						By(M, subK, subC, KInC, members, field_automorphism.AutomorphismLinear.At(m, K, C, g)))
					c.Show(
						"g maps C into itself",
						By(members, module_homomorphism.HomIn.Read(linear)))
				}))
			inK := a.Have(
				"the sum of the conjugates of b is fixed by the group, so it lies in K",
				"∀b:A. b ∈ C ⇒ «trace»(b) ∈ K",
				Derive(func(c *Argument) {
					b := c.FixAs[A]("b")
					bIn := c.Assume()
					evaluate := c.TermAs[Fun[symmetric_group.Permutation[A], A]](
						"λg:permutation(A). permutation_map(g, b)")
					sumIn := c.Have(
						"the sum lies in C",
						"«trace»(b) ∈ C",
						By(finiteG, bIn, conjugates, module.ModuleSumIn.Read(moduleC).AsFact().At(G, evaluate)))
					fixed := c.Have(
						"every automorphism fixes the sum",
						"∀h:permutation(A). h ∈ field_automorphisms(M, K, C) ⇒ permutation_map(h, «trace»(b)) = «trace»(b)",
						Derive(func(d *Argument) {
							h := d.FixAs[symmetric_group.Permutation[A]]("h")
							hIn := d.Assume()
							d.Show(
								"the group permutes the conjugates",
								By(M, subK, subC, KInC, finiteG, hIn, bIn, field_automorphism.GaloisTraceFixed.At(m, K, C, h, b)))
						}))
					inFixed := c.Have(
						"the sum lies in the fixed field",
						"«trace»(b) ∈ fixed_field(C, field_automorphisms(M, K, C))",
						BySets(sumIn, fixed, field_automorphism.FixedFieldDef.At(C, G)))
					c.Show(
						"K is the fixed field",
						By(fixedField, inFixed))
				}))
			adds := a.Have(
				"each automorphism adds, so the sum of the conjugates does",
				"∀u v:A. u ∈ C ∧ v ∈ C ⇒ «trace»(u + v) = «trace»(u) + «trace»(v)",
				Derive(func(c *Argument) {
					c.FixAs[A]("u")
					c.FixAs[A]("v")
					members := c.Assume()
					summand := c.TermAs[Fun[symmetric_group.Permutation[A], A]](
						"λg:permutation(A). permutation_map(g, u + v)")
					left := c.TermAs[Fun[symmetric_group.Permutation[A], A]]("λg:permutation(A). permutation_map(g, u)")
					right := c.TermAs[Fun[symmetric_group.Permutation[A], A]](
						"λg:permutation(A). permutation_map(g, v)")
					split := c.TermAs[Fun[symmetric_group.Permutation[A], A]](
						"λg:permutation(A). permutation_map(g, u) + permutation_map(g, v)")
					each := c.Have(
						"each conjugate of u + v is the sum of the conjugates",
						Statement{
							Binders:    "∀g:permutation(A).",
							Hypotheses: []string{"g ∈ field_automorphisms(M, K, C)"},
							Conclusion: "permutation_map(g, u + v) = permutation_map(g, u) + permutation_map(g, v)",
						},
						Derive(func(d *Argument) {
							g := d.FixAs[symmetric_group.Permutation[A]]("g")
							gIn := d.Assume()
							linear := d.Have(
								"g is linear over K",
								"module_homomorphism(«scalars», «vectors», «vectors», permutation_map(g))",
								By(M, subK, subC, KInC, gIn, field_automorphism.AutomorphismLinear.At(m, K, C, g)))
							d.Show(
								"g keeps sums",
								By(members, linear, module_homomorphism.HomAdd.Read(linear)))
						}))
					c.Show(
						"the sum of sums is the sum of the two sums",
						By(
							each,
							finiteG,
							members,
							conjugates,
							module.ModuleSumCongruence.At(add, zero, G, summand, split),
							module.ModuleSumAdd.Read(moduleC).AsFact().At(G, left, right)))
				}))
			scales := a.Have(
				"each automorphism fixes a scalar of K, so the sum of the conjugates takes it out",
				"∀c u:A. c ∈ K ∧ u ∈ C ⇒ «trace»(c * u) = c * «trace»(u)",
				Derive(func(b *Argument) {
					scalar := b.FixAs[A]("c")
					b.FixAs[A]("u")
					members := b.Assume()
					summand := b.TermAs[Fun[symmetric_group.Permutation[A], A]](
						"λg:permutation(A). permutation_map(g, c * u)")
					conjugate := b.TermAs[Fun[symmetric_group.Permutation[A], A]](
						"λg:permutation(A). permutation_map(g, u)")
					scaled := b.TermAs[Fun[symmetric_group.Permutation[A], A]](
						"λg:permutation(A). c * permutation_map(g, u)")
					each := b.Have(
						"each conjugate of c * u is c times the conjugate of u",
						Statement{
							Binders:    "∀g:permutation(A).",
							Hypotheses: []string{"g ∈ field_automorphisms(M, K, C)"},
							Conclusion: "permutation_map(g, c * u) = c * permutation_map(g, u)",
						},
						Derive(func(d *Argument) {
							g := d.FixAs[symmetric_group.Permutation[A]]("g")
							gIn := d.Assume()
							linear := d.Have(
								"g is linear over K",
								"module_homomorphism(«scalars», «vectors», «vectors», permutation_map(g))",
								By(M, subK, subC, KInC, gIn, field_automorphism.AutomorphismLinear.At(m, K, C, g)))
							d.Show(
								"g takes a scalar of K out",
								By(members, linear, module_homomorphism.HomSmul.Read(linear)))
						}))
					b.Show(
						"a scalar comes out of a finite sum",
						By(
							each,
							finiteG,
							members,
							conjugates,
							module.ModuleSumCongruence.At(add, zero, G, summand, scaled),
							module.ModuleSumSmul.Read(moduleC).AsFact().At(G, scalar, conjugate)))
				}))
			a.Show(
				"a finite group, and the sum of the conjugates meets the conditions of a linear form",
				By(
					finiteG,
					moduleC,
					module.RegularModuleOn.Read(baseRing),
					inK,
					adds,
					scales,
					module_homomorphism.ModuleHomomorphismDef.At(
						scalars, vectors, a.TermAs[module_record.ModuleOps[A, A]]("regular_module(«scalars»)"), trace)))
		}),
})}
