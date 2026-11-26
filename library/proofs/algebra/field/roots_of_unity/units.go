// units.go — the multiplicative group of a field, and the cyclicity of its
// finite subgroups.

package roots_of_unity

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/finite_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/abelian_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/cyclic_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/registry"
)

// FieldUnitsAbelianGroupOn — the nonzero elements of a field form an abelian
// group under its product: one is nonzero, a product of nonzero elements is
// nonzero (a field has no zero divisors), the inverse of a nonzero element is
// a nonzero element, and associativity, the identity, the left inverse and
// commutativity are the field's laws.
var FieldUnitsAbelianGroupOn = fieldUnitsAbelianGroupOnThm{family.Add(registry.ProofEntry{
	Name: "FieldUnitsAbelianGroupOn",
	Key:  "prop_37dd3f7d2b0c4108",
	Build: family.Theorem("∀F:field_on(A). abelian_group_on(field_units(F))",
		func(a *Argument, F field.FieldFact[on.F]) {
			ring := field.RingOn.Read(F)
			monoid := comm_ring.MulMonoidOn.Read(ring)
			nonzero := a.Have(
				"a nonzero element is an element of the field other than zero",
				"∀x:A. x ∈ F.carrier ∖ {F.zero} ⇔ x ∈ F.carrier ∧ x ≠ F.zero",
				BySets())
			a.Show(
				"the nonzero elements satisfy each axiom of an abelian group under the field's operations",
				Unfold(abelian_group.AbelianGroupOn),
				Unfold(group.GroupOn),
				SplitConjAll(
					Case(
						"one is not zero",
						By(nonzero.At(a.TermAs[A]("F.one")), comm_ring.OneIn.Read(ring), field.OneNotZeroOn.Read(F))),
					Case(
						"a product of nonzero elements is nonzero, a field having no zero divisors",
						Derive(func(b *Argument) {
							x := b.FixAs[A]("x")
							y := b.FixAs[A]("y")
							both := b.Assume()
							b.Show(
								"x · y lies in the field, and it is zero only when x or y is",
								By(
									nonzero.At(x),
									nonzero.At(y),
									nonzero.At(b.TermAs[A]("x * y")),
									both,
									comm_ring.MulIn.Read(ring).AsFact().At(x, y),
									field.MulEqZeroOn.Read(F).AsFact().At(x, y)))
						})),
					Case(
						"the inverse of a nonzero element is a nonzero element",
						Derive(func(b *Argument) {
							x := b.FixAs[A]("x")
							member := b.Assume()
							b.Show(
								"the inverse lies in the field, and it is zero only when x is",
								By(
									nonzero.At(x),
									nonzero.At(b.TermAs[A]("F.inv(x)")),
									member,
									field.InvIn.Read(F).AsFact().At(x),
									field.InvEqZeroOn.Read(F).AsFact().At(x)))
						})),
					Case(
						"the product associates",
						Derive(func(b *Argument) {
							x := b.FixAs[A]("x")
							y := b.FixAs[A]("y")
							z := b.FixAs[A]("z")
							all := b.Assume()
							b.Show(
								"it does on the whole field",
								By(
									nonzero.At(x),
									nonzero.At(y),
									nonzero.At(z),
									all,
									comm_monoid.AssocOn.Read(monoid).AsFact().At(x, y, z)))
						})),
					Case(
						"one is an identity",
						Derive(func(b *Argument) {
							x := b.FixAs[A]("x")
							member := b.Assume()
							b.Show(
								"it is on the whole field",
								By(nonzero.At(x), member, comm_monoid.LeftIdentityOn.Read(monoid).AsFact().At(x)))
						})),
					Case(
						"the inverse of a nonzero element is its inverse in the group",
						Derive(func(b *Argument) {
							x := b.FixAs[A]("x")
							member := b.Assume()
							b.Show(
								"a nonzero element of the field times its inverse is one",
								By(nonzero.At(x), member, field.MulLeftInverseOn.Read(F).AsFact().At(x)))
						})),
					Case(
						"the product commutes",
						Derive(func(b *Argument) {
							x := b.FixAs[A]("x")
							y := b.FixAs[A]("y")
							both := b.Assume()
							b.Show(
								"it does on the whole field",
								By(nonzero.At(x), nonzero.At(y), both, comm_monoid.CommOn.Read(monoid).AsFact().At(x, y)))
						}))))
		}),
})}

// RestrictFieldUnits — the multiplicative group of a field restricted to a
// set H is the group on H under the field's product, one and inverse: a
// restriction keeps the operations and replaces the carrier.
var RestrictFieldUnits = restrictFieldUnitsThm{family.Add(registry.ProofEntry{
	Name: "RestrictFieldUnits",
	Key:  "prop_c6a634a965abb26a",
	Build: family.Theorem("∀F:field_ops(A). ∀H:set(A). "+
		"    restrict_group(field_units(F), H) = mk_group(F.mul, F.one, F.inv, H)",
		func(a *Argument, F *Expr[FieldOps[A]], H *Expr[Set[A]]) {
			a.Show(
				"the restriction keeps the operations of the nonzero elements, which are the field's",
				Simp(
					Fwd(group.RestrictGroupDef),
					Fwd(FieldUnitsDef),
					Fwd(group.GroupMulDef),
					Fwd(group.GroupOneDef),
					Fwd(group.GroupInvDef)),
				Refl())
		}),
})}

// FiniteSubgroupCyclic — every finite subgroup of the multiplicative group of
// a field is cyclic. H is a group under the field's operations, and for
// d > 0 the solutions of x ^ d = 1 in H are among the field's, which number
// at most d (finite_field.RootsOfUnityBound); so the counting criterion
// (cyclic_group.CyclicCriterion) applies.
var FiniteSubgroupCyclic = finiteSubgroupCyclicThm{family.Add(registry.ProofEntry{
	Name: "FiniteSubgroupCyclic",
	Key:  "prop_707050bca54863c4",
	Build: family.Theorem(Statement{
		Binders: "∀F:field_on(A). ∀H:set(A).",
		Hypotheses: []string{
			"subgroup(field_units(F), H)",
			"finite(H)",
		},
		Conclusion: "cyclic_group(restrict_group(field_units(F), H))",
	}, func(a *Argument, F field.FieldFact[on.F], H *Expr[Set[A]], subgroup, finite Fact) {
		units := abelian_group.GroupOn.Read(FieldUnitsAbelianGroupOn.Read(F))
		record := a.Have(
			"restricted to H, the group of nonzero elements keeps the field's product, one and inverse",
			"restrict_group(field_units(F), H) = mk_group(F.mul, F.one, F.inv, H)",
			Cite(RestrictFieldUnits))
		groupOnH := a.Have(
			"H is a group under the field's operations, being a subgroup of the nonzero elements",
			"group_on(mk_group(F.mul, F.one, F.inv, H))",
			By(record, subgroup, group.SubgroupGroupOn.Read(units)))
		fewRoots := a.Have(
			"for d > 0, x ^ d = 1 has at most d solutions in H",
			"∀d:num. 0 < d ⇒ card({x:A | x ∈ H ∧ monoid_pow(F.mul, F.one, x, d) = F.one}) ≤ d",
			Derive(func(b *Argument) {
				d := b.FixAs[Nat]()
				positive := b.Assume()
				rootsInH := b.TermAs[Set[A]]("{x:A | x ∈ H ∧ monoid_pow(F.mul, F.one, x, d) = F.one}")
				rootsInF := b.TermAs[Set[A]]("{x:A | x ∈ F.carrier ∧ monoid_pow(F.mul, F.one, x, d) = F.one}")
				among := b.Have(
					"H lies among the nonzero elements, so the solutions in H are solutions in the field",
					"{x:A | x ∈ H ∧ monoid_pow(F.mul, F.one, x, d) = F.one} ⊆ "+
						"{x:A | x ∈ F.carrier ∧ monoid_pow(F.mul, F.one, x, d) = F.one}",
					BySets(subgroup, group.SubgroupSubset))
				b.Show(
					"and those number at most d",
					ByArith(
						positive,
						among,
						finite_field.RootsOfUnityBound.Read(F).At(d),
						cardinality.CardSubset.At(rootsInH, rootsInF)))
			}))
		a.Show(
			"so, by the counting criterion, the group on H is cyclic",
			record.Rw(),
			By(finite, groupOnH, fewRoots, cyclic_group.CyclicCriterion))
	}),
})}

// FiniteFieldUnitsCyclic — the multiplicative group of a finite field is
// cyclic: its nonzero elements are a finite subgroup of that group, all of
// it (FiniteSubgroupCyclic).
var FiniteFieldUnitsCyclic = finiteFieldUnitsCyclicThm{family.Add(registry.ProofEntry{
	Name: "FiniteFieldUnitsCyclic",
	Key:  "prop_a280fd1bda20723c",
	Build: family.Theorem(Statement{
		Binders: "∀F:field_on(A).",
		Hypotheses: []string{
			"finite(F.carrier)",
		},
		Conclusion: "cyclic_group(field_units(F))",
	}, func(a *Argument, F field.FieldFact[on.F], finite Fact) {
		nonzero := a.TermAs[Set[A]]("F.carrier ∖ {F.zero}")
		whole := a.Have(
			"restricted to all the nonzero elements, the group is itself",
			"restrict_group(field_units(F), F.carrier ∖ {F.zero}) = field_units(F)",
			Simp(Fwd(RestrictFieldUnits), Rev(FieldUnitsDef)),
			Refl())
		a.Show(
			"the nonzero elements are a finite subgroup of the group they form",
			By(
				finite,
				whole,
				group.CarrierSubgroupOn.Read(abelian_group.GroupOn.Read(FieldUnitsAbelianGroupOn.Read(F))),
				finite_set.FiniteDiff.At(a.TermAs[Set[A]]("F.carrier"), a.TermAs[Set[A]]("{F.zero}")),
				FiniteSubgroupCyclic.Read(F).At(nonzero)))
	}),
})}
