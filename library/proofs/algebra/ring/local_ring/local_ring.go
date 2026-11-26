// local_ring.go — local rings on a set, the rings whose non-units are
// closed under the addition: the non-units are their one maximal ideal,
// and its cosets are the residue field.

package local_ring

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/quotient_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_ideal"
	"github.com/euc-ai/xugo/library/registry"
)

// LocalRingOn — `local_ring_on(R)`: a ring on R.carrier in which one
// is not zero and a sum of two non-units is a non-unit. The non-units
// form its one maximal ideal (NonUnitsMaximal).
var LocalRingOn = localRingOnThm{family.DefineStructure(registry.DefEntry{
	Name:     "LocalRingOn",
	Key:      "prop_ad4c26867a569794",
	Const:    "local_ring_on",
	Subject:  "R",
	Type:     "ring_ops(A) → bool",
	Implicit: []string{},
	Equations: []string{
		"∀R:ring_ops(A). " +
			"    local_ring_on(R) ⇔ " +
			"    comm_ring_on(R) ∧ " +
			"    ¬(R.one = R.zero) ∧ " +
			"    (∀x y:A. " +
			"        x ∈ R.carrier ∧ y ∈ R.carrier ∧ ¬ring_unit(R, x) ∧ ¬ring_unit(R, y) ⇒ " +
			"        ¬ring_unit(R, R.add(x, y)))",
	},
	Symbols: map[string]string{},
})}

// Ring — a local ring is a ring.
var Ring = ringThm{family.Add(registry.ProofEntry{
	Name:  "Ring",
	Key:   "prop_bef2b68f97abc987",
	Build: LocalRingOn.Axiom("comm_ring_on(R)"),
})}

// OneNotZero — in a local ring one is not zero.
var OneNotZero = oneNotZeroThm{family.Add(registry.ProofEntry{
	Name:  "OneNotZero",
	Key:   "prop_3e5b52fdc4a68adb",
	Build: LocalRingOn.Axiom("¬(R.one = R.zero)"),
})}

// NonUnitAdd — a sum of two non-units is a non-unit.
var NonUnitAdd = nonUnitAddThm{family.Add(registry.ProofEntry{
	Name: "NonUnitAdd",
	Key:  "prop_32bdaf7c35c38091",
	Build: LocalRingOn.Axiom(Statement{
		Binders: "∀x y:A.",
		Hypotheses: []string{
			"x ∈ R.carrier",
			"y ∈ R.carrier",
			"¬ring_unit(R, x)",
			"¬ring_unit(R, y)",
		},
		Conclusion: "¬ring_unit(R, x + y)",
	}),
})}

// NonUnitsIdeal — the non-units of a local ring form an ideal: zero is no
// unit since one is not zero, a sum of two non-units is a non-unit by the
// axiom, and a multiple r * x of a non-unit x is a non-unit, since an
// inverse v of r * x would make r * v an inverse of x.
var NonUnitsIdeal = nonUnitsIdealThm{family.Add(registry.ProofEntry{
	Name: "NonUnitsIdeal",
	Key:  "prop_288dd844ce10372b",
	Build: LocalRingOn.Law("ring_ideal(R, «nonUnits»)",
		func(a *Argument, local LocalRingFact[on.R]) {
			ring := Ring.Read(local)
			// The multiplicative monoid on c is read as a value, never made
			// resident: its op would meet the ring's `*`.
			monoid := comm_ring.MulMonoidOn.Read(ring)
			a.Do(Unfold(ring_ideal.RingIdealDef), SplitConjAll(
				Case(
					"every non-unit of c lies in c",
					BySets()),
				Case(
					"zero lies in c and is no unit",
					Derive(func(b *Argument) {
						nonUnit := b.Have(
							"zero * y is zero for every y in c, and one is not zero",
							"¬ring_unit(R, R.zero)",
							Unfold(ring_ideal.RingUnitDef),
							b.ForEach(func(y *Expr[A]) Action {
								return By(Normalized, At(comm_ring.MulLeftZeroOn.Read(ring), y), OneNotZero.Read(local))
							}))
						b.Show(
							"and zero lies in c",
							BySets(comm_ring.ZeroIn.Read(ring), nonUnit))
					})),
				Case(
					"a sum of two non-units is a non-unit, and lies in c",
					BySets(NonUnitAdd.Read(local), comm_ring.AddIn.Read(ring))),
				Case(
					"a multiple of a non-unit by a member of c is a non-unit",
					Derive(func(b *Argument) {
						b.FixAs[A]("r")
						b.FixAs[A]("x")
						hypotheses := b.Assume()
						members := b.Have(
							"r and x lie in c, and x is no unit",
							"r ∈ R.carrier ∧ x ∈ R.carrier ∧ ¬ring_unit(R, x)",
							BySets(hypotheses))
						transfer := b.Have(
							"were r * x a unit, so would x be",
							"ring_unit(R, r * x) ⇒ ring_unit(R, x)",
							Derive(func(d *Argument) {
								unit := d.Assume()
								parts := d.Conjuncts(
									d.Unfolded(unit, ring_ideal.RingUnitDef),
									"r * x lies in c",
									"and has an inverse in c")
								_, inverse := d.Unpack(parts[1], "v")
								inverts := d.Have(
									"so r * v is an inverse of x",
									"x * (r * v) = R.one",
									CalcEq(
										Leg(
											d.TermAs[A]("r * (x * v)"),
											"x and r trade places",
											By(comm_monoid.LeftCommOn.Read(monoid), inverse, members)),
										Leg(
											d.TermAs[A]("r * x * v"),
											"the product regroups",
											By(comm_monoid.AssocOn.Read(monoid), inverse, members)),
										FinalLeg(
											"and v is the inverse of r * x",
											By(inverse)),
									))
								invertible := d.Have(
									"and r * v lies in c, so x has an inverse in c",
									"∃w:A. w ∈ R.carrier ∧ x * w = R.one",
									Witness(d.Term("r * v")),
									By(comm_ring.MulIn.Read(ring), inverts, inverse, members))
								d.Show(
									"so x is a unit",
									By(ring_ideal.RingUnitDef, invertible, members))
							}))
						nonUnit := b.Have(
							"x is no unit, so neither is r * x",
							"¬ring_unit(R, r * x)",
							By(transfer, members))
						b.Show(
							"and r * x lies in c",
							BySets(comm_ring.MulIn.Read(ring), nonUnit, members))
					})),
			))
		}),
})}

// NonUnitsMaximal — the non-units of a local ring form a maximal ideal,
// and every maximal ideal is it: one is a unit, so a proper ideal holds
// no unit and lies among the non-units; an ideal above the non-units
// that misses one is therefore them, and a maximal ideal, lying among
// them, is them by its maximality.
var NonUnitsMaximal = nonUnitsMaximalThm{family.Add(registry.ProofEntry{
	Name: "NonUnitsMaximal",
	Key:  "prop_31ea84558d8bf924",
	Reading: "¬(R.one = R.zero) is what keeps R.zero a non-unit: in the " +
		"zero ring R.zero is a unit and the non-units form ∅, which is no ideal.",
	Build: LocalRingOn.Law("maximal_ideal(R, «nonUnits») ∧ "+
		"(∀m:set(A). maximal_ideal(R, m) ⇒ m = «nonUnits»)",
		func(a *Argument, local LocalRingFact[on.R]) {
			ring := Ring.Read(local)
			ideal := NonUnitsIdeal.Read(local)
			oneOutside := a.Have(
				"one is a unit, so the non-units do not hold it",
				"¬(R.one ∈ «nonUnits»)",
				BySets(ring_ideal.OneUnit.Read(ring)))
			below := a.Have(
				"a proper ideal holds no unit, so lies among the non-units",
				"∀J:set(A). ring_ideal(R, J) ∧ R.one ∉ J ⇒ J ⊆ «nonUnits»",
				BySets(ring_ideal.IdealSubset, ring_ideal.UnitNotInProperIdeal.Read(ring)))
			a.Do(SplitConj(
				Case(
					"the non-units form a maximal ideal",
					Simp(Fwd(ring_ideal.MaximalIdealDef)),
					SplitConjAll(
						Case(
							"they form an ideal",
							By(ideal)),
						Case(
							"which does not hold one",
							By(oneOutside)),
						Case(
							"an ideal above them that misses one lies among them, so is them",
							a.ForEach(func(J *Expr[Set[A]]) Action {
								return BySets(below.At(J))
							})),
					)),
				Case(
					"a maximal ideal is the non-units",
					Derive(func(b *Argument) {
						b.FixAs[Set[A]]("m")
						maximal := b.Assume()
						inside := b.Have(
							"m is a proper ideal, so it lies among the non-units",
							"m ⊆ «nonUnits»",
							By(below, ring_ideal.MaximalIdealIdeal.Read(maximal), ring_ideal.MaximalIdealProper.Read(maximal)))
						either := b.Have(
							"the non-units form an ideal above m, so by maximality they are m or hold one",
							"«nonUnits» = m ∨ R.one ∈ «nonUnits»",
							By(ring_ideal.MaximalIdealMaximal.Read(maximal), ideal, inside))
						b.Show(
							"and they do not hold one",
							By(either, oneOutside))
					})),
			))
		}),
})}

// ---------------------------------------------------------------------------
// The residue field
// ---------------------------------------------------------------------------

// ResidueFieldDef — `residue_field(R)`: the cosets of the non-units of
// R.carrier, the quotient of a local ring by its maximal ideal.
var ResidueFieldDef = residueFieldDefThm{family.Define(registry.DefEntry{
	Name:     "ResidueFieldDef",
	Key:      "prop_5fea0d45bdce53aa",
	Const:    "residue_field",
	Type:     "ring_ops(A) → set(set(A))",
	Implicit: []string{},
	Equations: []string{
		"∀R:ring_ops(A). residue_field(R) = left_cosets(R.add, R.carrier, «nonUnits»)",
	},
})}

// ResidueFieldOn — the residue field of a local ring is a field on its
// set: it is the set of the quotient field by the non-units, so the
// quotient field restricted to it is the quotient field itself; the
// non-units are the maximal ideal, and the cosets of a maximal ideal form
// a field (quotient_ring.QuotientFieldOn).
var ResidueFieldOn = residueFieldOnThm{family.Add(registry.ProofEntry{
	Name: "ResidueFieldOn",
	Key:  "prop_712b10b33a38af63",
	Build: LocalRingOn.Law("field_on( "+
		"    restrict_field(ideal_quotient_field(R, «nonUnits»), residue_field(R)))",
		func(a *Argument, local LocalRingFact[on.R]) {
			itself := a.Have(
				"the residue field is the set of the quotient field, so "+
					"restricting the quotient field to it leaves it as it is",
				"restrict_field(ideal_quotient_field(R, «nonUnits»), residue_field(R)) = "+
					"ideal_quotient_field(R, «nonUnits»)",
				Simp(Fwd(field.RestrictFieldDef), Fwd(quotient_ring.IdealQuotientFieldDef), Fwd(ResidueFieldDef)),
				Refl())
			a.Do(itself.Rw())
			a.Show(
				"the non-units are the maximal ideal of the ring, and the cosets of a maximal ideal form a field",
				By(quotient_ring.QuotientFieldOn.Read(Ring.Read(local)), NonUnitsMaximal.Read(local)))
		}),
})}
