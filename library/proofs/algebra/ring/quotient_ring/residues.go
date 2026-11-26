// residues.go — the proper ideals of a subring containing a field k whose
// residues all lie in k: such an ideal is maximal, meets k only at zero, and
// is the kernel of a ring map to k fixing k, and the kernels of those maps
// are such ideals.

package quotient_ring

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_ideal"
	"github.com/euc-ai/xugo/library/registry"
)

// RationalIdealDef — `rational_ideal(R, k, S, I)`: I is a proper ideal of
// the subring S whose residues all lie in k, each member of S congruent
// modulo I to a member of k. With k a field inside S the residue field
// S/I is k: I is the ideal of a k-rational point.
var RationalIdealDef = rationalIdealDefThm{family.Define(registry.DefEntry{
	Name:  "RationalIdealDef",
	Key:   "prop_c14ee00851189cb4",
	Const: "rational_ideal",
	Type:  "ring_ops(A) → set(A) → set(A) → set(A) → bool",
	Reading: "Neither that S is a subring nor that k is a field inside it is asked: " +
		"the predicate speaks of the ideal and its residues alone, and a statement that " +
		"reads S/I as k states subring(R, S), ring_subfield(R, inv, k) and k ⊆ S beside it.",
	Equations: []string{
		"∀R:ring_ops(A). ∀k S I:set(A). " +
			"    rational_ideal(R, k, S, I) ⇔ " +
			"    ring_ideal(restrict_ring(R, S), I) ∧ R.one ∉ I ∧ (∀x:A. x ∈ S ⇒ ∃y:A. y ∈ k ∧ x + -y ∈ I)",
	},
})}

// FieldResiduesMaximal — the ideal I of a k-rational point of a subring S
// containing the field k is maximal. An ideal J above I that is neither I
// nor holds one has a member x outside I; the residue y of x lies in J and
// is not zero, so y is a unit of S, its inverse lying in k and so in S, and
// an ideal without one holds no unit.
var FieldResiduesMaximal = fieldResiduesMaximalThm{family.Add(registry.ProofEntry{
	Name: "FieldResiduesMaximal",
	Key:  "prop_3c7720d4bc561e00",
	Reading: "k ⊆ S is load-bearing: with S = ℤ inside R = ℚ and k = ℚ, every integer " +
		"is its own residue, so the ideal 4ℤ meets every other hypothesis and is not maximal.",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀k:set(A). ∀inv:(A → A). ∀S I:set(A).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"ring_subfield(R, inv, k)",
			"subring(R, S)",
			"k ⊆ S",
			"rational_ideal(R, k, S, I)",
		},
		Conclusion: "maximal_ideal(restrict_ring(R, S), I)",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			ring comm_ring.CommRingFact[on.R],
			k *Expr[Set[A]],
			inv *Arrow[A, A],
			subfieldK Fact,
			S, I *Expr[Set[A]],
			given Fact,
		) {
			hypotheses := a.Conjuncts(
				given,
				"S is a subring of R",
				"k lies in S",
				"I is the ideal of a k-rational point")
			subringS, kInS := hypotheses[0], hypotheses[1]
			rational := a.Conjuncts(
				a.Unfolded(hypotheses[2], RationalIdealDef),
				"I is an ideal of S",
				"I excludes one",
				"each element of S has a residue in k modulo I")
			ideal, proper, residues := rational[0], rational[1], rational[2]
			fieldK := a.Unfolded(subfieldK, field.RingSubfieldDef)
			RS := a.TermAs[RingOps[A]]("restrict_ring(R, S)")
			ringS := a.Have(
				"S is a ring under the operations of R",
				"comm_ring_on(restrict_ring(R, S))",
				By(subringS, comm_ring.SubringRingOn.Read(ring).At(S)))
			maximal := a.Have(
				"an ideal above I is I itself or contains one",
				"∀J:set(A). ring_ideal(restrict_ring(R, S), J) ∧ I ⊆ J ⇒ J = I ∨ R.one ∈ J",
				Derive(func(b *Argument) {
					J := b.FixAs[Set[A]]()
					above := b.Conjuncts(
						b.Assume(),
						"J is an ideal of S",
						"J contains I")
					idealJ, containsI := above[0], above[1]
					neither := b.SupposeNot()
					x, outside := b.ObtainAs[A](
						"a strictly larger ideal has an element outside I",
						"∃x:A. x ∈ J ∧ x ∉ I",
						BySets(neither, containsI))
					xInS := b.Have(
						"an element of J lies in S",
						"x ∈ S",
						BySets(outside, ring_ideal.IdealSubset.Read(idealJ)))
					y, residue := b.ObtainAs[A](
						"choose the residue of x in k",
						"∃y:A. y ∈ k ∧ x + -y ∈ I",
						By(xInS, residues.At(x)))
					yInS := b.Have(
						"the residue lies in S because k does",
						"y ∈ S",
						BySets(residue, kInS))
					zeroDifference := b.Have(
						"subtracting zero fixes x",
						"x + -R.zero = x",
						ByArith(ringS, xInS))
					nonzero := b.Have(
						"the residue is nonzero, since x lies outside I",
						"y ≠ R.zero",
						By(Normalized, zeroDifference, outside, residue))
					difference := b.TermAs[A]("x + -y")
					differenceInJ := b.Have(
						"the residue difference lies in J through I",
						"x + -y ∈ J",
						BySets(residue, containsI))
					recoveredInJ := b.Have(
						"subtracting the residue difference from x stays in J",
						"x + -(x + -y) ∈ J",
						By(idealJ, outside, differenceInJ, ring_ideal.IdealSub.Read(ringS).At(J, x, difference)))
					recover := b.Have(
						"subtracting the residue difference recovers y",
						"x + -(x + -y) = y",
						ByArith(ringS, xInS, yInS))
					residueInJ := b.Have(
						"therefore J contains the residue",
						"y ∈ J",
						By(Normalized, recoveredInJ, recover))
					inverseInS := b.Have(
						"the inverse of the residue lies in S through k",
						"inv(y) ∈ S",
						BySets(residue, field.InvIn.Read(fieldK).AsFact().At(y), kInS))
					inverse := b.Have(
						"inv(y) lies in S and inverts the nonzero residue",
						"∃w:A. w ∈ S ∧ y * w = R.one",
						Witness(inv.Apply(y)),
						By(inverseInS, residue, nonzero, field.MulRightInverseOn.Read(fieldK).AsFact().At(y)))
					unit := b.Have(
						"so the residue is a unit of S",
						"ring_unit(restrict_ring(R, S), y)",
						By(yInS, inverse, ring_ideal.RingUnitDef.At(RS, y)))
					b.Show(
						"a unit in J contradicts the assumed failure of maximality",
						By(idealJ, neither, unit, residueInJ, ring_ideal.UnitNotInProperIdeal.Read(ringS).At(J, y)))
				}))
			a.Show(
				"I is proper and every ideal above it is I or contains one",
				By(ideal, proper, maximal, ring_ideal.MaximalIdealDef.At(RS, I)))
		}),
})}

// ProperIdealMeetsFieldAtZero — a proper ideal I of S, where S contains
// the field k, meets k only at zero: a nonzero c of k in I has its inverse
// in k, so in S, and I absorbs inv(c) · c, which is one.
var ProperIdealMeetsFieldAtZero = properIdealMeetsFieldAtZeroThm{family.Add(registry.ProofEntry{
	Name: "ProperIdealMeetsFieldAtZero",
	Key:  "prop_3bcf81b57b29c41",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀k:set(A). ∀inv:(A → A). ∀S I:set(A). ∀c:A.",
		Hypotheses: []string{
			"ring_subfield(R, inv, k)",
			"k ⊆ S",
			"ring_ideal(restrict_ring(R, S), I)",
			"R.one ∉ I",
			"c ∈ I",
			"c ∈ k",
		},
		Conclusion: "c = R.zero",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			k *Expr[Set[A]],
			inv *Arrow[A, A],
			subfieldK Fact,
			S, I *Expr[Set[A]],
			c *Expr[A],
			given Fact,
		) {
			hypotheses := a.Conjuncts(
				given,
				"k lies in S",
				"I is an ideal of S",
				"I excludes one",
				"c lies in I",
				"c lies in k")
			kInS, ideal, proper, cInI, cInK :=
				hypotheses[0], hypotheses[1], hypotheses[2], hypotheses[3], hypotheses[4]
			fieldK := a.Unfolded(subfieldK, field.RingSubfieldDef)
			nonzero := a.SupposeNot()
			inverseInS := a.Have(
				"the inverse of c lies in k and so in S",
				"inv(c) ∈ S",
				BySets(cInK, field.InvIn.Read(fieldK).AsFact().At(c), kInS))
			inverseProduct := a.Have(
				"c being nonzero, the inverse times c is one",
				"inv(c) * c = R.one",
				By(cInK, nonzero, field.MulLeftInverseOn.Read(fieldK).AsFact().At(c)))
			inverseProductInIdeal := a.Have(
				"the ideal absorbs that product",
				"inv(c) * c ∈ I",
				By(inverseInS, cInI, ring_ideal.IdealMul.Read(ideal).AsFact().At(a.TermAs[A]("inv(c)"), c)))
			a.Show(
				"so one lies in I, which excludes it",
				By(Normalized, inverseProductInIdeal, inverseProduct, proper))
		}),
})}

// FieldResiduesHomomorphism — the ideal I of a k-rational point of a
// subring S containing the field k is the kernel of a ring map S → k
// fixing k. The residue of a member of S is unique, two residues differing
// by a member of k in I, which is zero (ProperIdealMeetsFieldAtZero); a
// choice of residues is then additive, multiplicative and the identity on
// k by that uniqueness, and its kernel is I.
var FieldResiduesHomomorphism = fieldResiduesHomomorphismThm{family.Add(registry.ProofEntry{
	Name: "FieldResiduesHomomorphism",
	Key:  "prop_c6a435824186a167",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀k:set(A). ∀inv:(A → A). ∀S I:set(A).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"ring_subfield(R, inv, k)",
			"subring(R, S)",
			"k ⊆ S",
			"rational_ideal(R, k, S, I)",
		},
		Conclusion: "∃φ:(A → A). " +
			"    ring_homomorphism(restrict_ring(R, S), restrict_ring(R, k), φ) ∧ " +
			"    (∀c:A. c ∈ k ⇒ φ(c) = c) ∧ " +
			"    I = ring_kernel(R.zero, S, φ)",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			ring comm_ring.CommRingFact[on.R],
			k *Expr[Set[A]],
			inv *Arrow[A, A],
			subfieldK Fact,
			S, I *Expr[Set[A]],
			given Fact,
		) {
			hypotheses := a.Conjuncts(
				given,
				"S is a subring of R",
				"k lies in S",
				"I is the ideal of a k-rational point")
			subringS, kInS := hypotheses[0], hypotheses[1]
			rational := a.Conjuncts(
				a.Unfolded(hypotheses[2], RationalIdealDef),
				"I is an ideal of S",
				"I excludes one",
				"each element of S has a residue in k modulo I")
			ideal, proper, residues := rational[0], rational[1], rational[2]
			ringS := a.Have(
				"the subring inherits the ring operations",
				"comm_ring_on(restrict_ring(R, S))",
				By(subringS, comm_ring.SubringRingOn.Read(ring).At(S)))
			fieldRing := a.Simplified(
				field.RingOn.Read(a.Unfolded(subfieldK, field.RingSubfieldDef)),
				Fwd(field.FieldRingDef))
			ringK := a.Have(
				"k is a commutative ring under R's operations, the ring of its field",
				"comm_ring_on(restrict_ring(R, k))",
				By(fieldRing, module_record.RestrictRingDef.At(R, k)))
			residueUnique := a.Have(
				"two residues in k of one element of S coincide",
				"∀x y z:A. x ∈ S ∧ y ∈ k ∧ z ∈ k ∧ x + -y ∈ I ∧ x + -z ∈ I ⇒ y = z",
				Derive(func(b *Argument) {
					b.FixAs[A]()
					y := b.FixAs[A]()
					z := b.FixAs[A]()
					premises := b.Assume()
					twoResidues := b.Conjuncts(
						premises,
						"x lies in S",
						"y lies in k",
						"z lies in k",
						"y is a residue of x",
						"z is a residue of x")
					residuesInS := b.Have(
						"both proposed residues lie in S",
						"y ∈ S ∧ z ∈ S",
						BySets(twoResidues[1], twoResidues[2], kInS))
					differenceInIdeal := b.Have(
						"subtracting the two differences stays in the ideal",
						"x + -z + -(x + -y) ∈ I",
						By(
							ideal,
							twoResidues[3],
							twoResidues[4],
							ring_ideal.IdealSub.Read(ringS).At(I, b.TermAs[A]("x + -z"), b.TermAs[A]("x + -y"))))
					differenceIdentity := b.Have(
						"the difference of differences is the residue difference",
						"x + -z + -(x + -y) = y + -z",
						ByArith(ringS, twoResidues[0], residuesInS))
					residueDifferenceInIdeal := b.Have(
						"the residue difference therefore lies in the ideal",
						"y + -z ∈ I",
						By(differenceInIdeal, differenceIdentity))
					residueDifferenceInK := b.Have(
						"the field holds the residue difference",
						"y + -z ∈ k",
						By(
							twoResidues[1],
							twoResidues[2],
							comm_ring.NegIn.Read(ringK).AsFact().At(z),
							comm_ring.AddIn.Read(ringK).AsFact().At(y, b.TermAs[A]("-z"))))
					residueDifferenceZero := b.Have(
						"the residue difference is zero by properness",
						"y + -z = R.zero",
						By(
							subfieldK,
							kInS,
							ideal,
							proper,
							residueDifferenceInIdeal,
							residueDifferenceInK,
							ProperIdealMeetsFieldAtZero.At(R, k, inv, S, I, b.TermAs[A]("y + -z"))))
					b.Show(
						"the residue difference vanishes, so the residues coincide",
						ByArith(ringK, twoResidues[1], twoResidues[2], residueDifferenceZero))
				}))
			φ, chosenResidues := a.ObtainAs[Fun[A, A]](
				"choose one residue in k for every element of S",
				"∃φ:(A → A). ∀x:A. x ∈ S ⇒ φ(x) ∈ k ∧ x + -φ(x) ∈ I",
				By(residues))
			chosenIsResidue := a.Have(
				"a residue in k of an element of S is its chosen residue",
				"∀x c:A. x ∈ S ∧ c ∈ k ∧ x + -c ∈ I ⇒ φ(x) = c",
				Derive(func(b *Argument) {
					x := b.FixAs[A]()
					c := b.FixAs[A]()
					candidate := b.Assume()
					chosen := b.Have(
						"x has its chosen residue",
						"φ(x) ∈ k ∧ x + -φ(x) ∈ I",
						By(candidate, chosenResidues.At(x)))
					b.Show(
						"two residues in k of x coincide",
						By(candidate, chosen, residueUnique.At(x, b.TermAs[A]("φ(x)"), c)))
				}))
			preservesAdd := a.Have(
				"the chosen residue map preserves addition",
				"∀x y:A. x ∈ S ∧ y ∈ S ⇒ φ(x + y) = φ(x) + φ(y)",
				Derive(func(b *Argument) {
					x := b.FixAs[A]()
					y := b.FixAs[A]()
					premises := b.Assume()
					summandResidues := b.Have(
						"the chosen residues of both summands have their defining differences",
						"φ(x) ∈ k ∧ x + -φ(x) ∈ I ∧ φ(y) ∈ k ∧ y + -φ(y) ∈ I",
						By(premises, chosenResidues.At(x), chosenResidues.At(y)))
					sumResiduesInS := b.Have(
						"the summand residues lie in S through k",
						"φ(x) ∈ S ∧ φ(y) ∈ S",
						BySets(summandResidues, kInS))
					sumDifferencesInIdeal := b.Have(
						"adding the residue differences stays in the ideal",
						"x + -φ(x) + (y + -φ(y)) ∈ I",
						By(
							summandResidues,
							ring_ideal.IdealAdd.Read(ideal).AsFact().At(b.TermAs[A]("x + -φ(x)"), b.TermAs[A]("y + -φ(y)"))))
					sumDifferenceIdentity := b.Have(
						"the sum of differences is the difference from the sum of residues",
						"x + -φ(x) + (y + -φ(y)) = x + y + -(φ(x) + φ(y))",
						ByArith(ringS, premises, sumResiduesInS))
					sumCandidateDifference := b.Have(
						"the sum of residues is another residue of the sum",
						"x + y + -(φ(x) + φ(y)) ∈ I",
						By(sumDifferencesInIdeal, sumDifferenceIdentity))
					b.Show(
						"so it is the chosen residue of the sum",
						By(
							premises,
							comm_ring.AddIn.Read(ringS).AsFact().At(x, y),
							summandResidues,
							comm_ring.AddIn.Read(ringK).AsFact().At(b.TermAs[A]("φ(x)"), b.TermAs[A]("φ(y)")),
							sumCandidateDifference,
							chosenIsResidue.At(b.TermAs[A]("x + y"), b.TermAs[A]("φ(x) + φ(y)"))))
				}))
			preservesMul := a.Have(
				"the chosen residue map preserves multiplication",
				"∀x y:A. x ∈ S ∧ y ∈ S ⇒ φ(x * y) = φ(x) * φ(y)",
				Derive(func(b *Argument) {
					x := b.FixAs[A]()
					y := b.FixAs[A]()
					premises := b.Assume()
					factorResidues := b.Have(
						"the chosen factor residues have their defining differences",
						"φ(x) ∈ k ∧ x + -φ(x) ∈ I ∧ φ(y) ∈ k ∧ y + -φ(y) ∈ I",
						By(premises, chosenResidues.At(x), chosenResidues.At(y)))
					factorResiduesInS := b.Have(
						"the factor residues lie in S through k",
						"φ(x) ∈ S ∧ φ(y) ∈ S",
						BySets(factorResidues, kInS))
					firstProductDifference := b.Have(
						"multiplying the first residue difference stays in the ideal",
						"x * (y + -φ(y)) ∈ I",
						By(
							premises,
							factorResidues,
							ring_ideal.IdealMul.Read(ideal).AsFact().At(x, b.TermAs[A]("y + -φ(y)"))))
					secondProductDifference := b.Have(
						"multiplying the second residue difference stays in the ideal",
						"φ(y) * (x + -φ(x)) ∈ I",
						By(
							factorResiduesInS,
							factorResidues,
							ring_ideal.IdealMul.Read(ideal).AsFact().At(b.TermAs[A]("φ(y)"), b.TermAs[A]("x + -φ(x)"))))
					productDifferenceInIdeal := b.Have(
						"the sum of those products stays in the ideal",
						"x * (y + -φ(y)) + φ(y) * (x + -φ(x)) ∈ I",
						By(
							firstProductDifference,
							secondProductDifference,
							ring_ideal.IdealAdd.Read(ideal).AsFact().At(
								b.TermAs[A]("x * (y + -φ(y))"), b.TermAs[A]("φ(y) * (x + -φ(x))"))))
					productDifferenceIdentity := b.Have(
						"the product difference expands as those two products",
						"x * (y + -φ(y)) + φ(y) * (x + -φ(x)) = x * y + -(φ(x) * φ(y))",
						ByArith(ringS, premises, factorResiduesInS))
					productCandidateDifference := b.Have(
						"the product of residues is another residue of the product",
						"x * y + -(φ(x) * φ(y)) ∈ I",
						By(productDifferenceInIdeal, productDifferenceIdentity))
					b.Show(
						"so it is the chosen residue of the product",
						By(
							premises,
							comm_ring.MulIn.Read(ringS).AsFact().At(x, y),
							factorResidues,
							comm_ring.MulIn.Read(ringK).AsFact().At(b.TermAs[A]("φ(x)"), b.TermAs[A]("φ(y)")),
							productCandidateDifference,
							chosenIsResidue.At(b.TermAs[A]("x * y"), b.TermAs[A]("φ(x) * φ(y)"))))
				}))
			fixesK := a.Have(
				"the map fixes k",
				"∀c:A. c ∈ k ⇒ φ(c) = c",
				Derive(func(b *Argument) {
					c := b.FixAs[A]()
					premises := b.Assume()
					scalarInS := b.Have(
						"the scalar lies in S through k",
						"c ∈ S",
						BySets(premises, kInS))
					scalarSelfDifference := b.Have(
						"the scalar differs from itself by zero",
						"c + -c = R.zero",
						ByArith(ringK, premises))
					scalarSelfResidue := b.Have(
						"the ideal holds that zero difference",
						"c + -c ∈ I",
						By(Normalized, ring_ideal.IdealZero.Read(ideal), scalarSelfDifference))
					b.Show(
						"so the scalar is its own chosen residue",
						By(scalarInS, premises, scalarSelfResidue, chosenIsResidue.At(c, c)))
				}))
			idealMapsToZero := a.Have(
				"every element of the ideal has residue zero",
				"∀x:A. x ∈ I ⇒ φ(x) = R.zero",
				Derive(func(b *Argument) {
					x := b.FixAs[A]()
					premises := b.Assume()
					idealElementInS := b.Have(
						"an ideal element lies in S",
						"x ∈ S",
						BySets(ring_ideal.IdealSubset.Read(ideal), premises))
					subtractZero := b.Have(
						"subtracting zero fixes the element",
						"x + -R.zero = x",
						ByArith(ringS, idealElementInS))
					zeroIsResidue := b.Have(
						"zero is also a residue of the ideal element",
						"x + -R.zero ∈ I",
						By(Normalized, premises, subtractZero))
					b.Show(
						"so zero is its chosen residue",
						By(
							comm_ring.ZeroIn.Read(ringK),
							idealElementInS,
							zeroIsResidue,
							chosenIsResidue.At(x, b.TermAs[A]("R.zero"))))
				}))
			zeroMapsToIdeal := a.Have(
				"an element with residue zero lies in the ideal",
				"∀x:A. x ∈ S ∧ φ(x) = R.zero ⇒ x ∈ I",
				Derive(func(b *Argument) {
					x := b.FixAs[A]()
					premises := b.Assume()
					kernelResidue := b.Have(
						"the element has its chosen residue difference",
						"φ(x) ∈ k ∧ x + -φ(x) ∈ I",
						By(premises, chosenResidues.At(x)))
					kernelSubtractZero := b.Have(
						"subtracting zero fixes the element",
						"x + -R.zero = x",
						ByArith(ringS, premises))
					b.Show(
						"the zero residue difference is the element itself",
						By(Normalized, premises, kernelResidue, kernelSubtractZero))
				}))
			kernelEqualsIdeal := a.Have(
				"the chosen map has exactly the given ideal as kernel",
				"I = ring_kernel(R.zero, S, φ)",
				Simp(Fwd(ring_homomorphism.RingKernelDef)),
				BySets(ring_ideal.IdealSubset.Read(ideal), idealMapsToZero, zeroMapsToIdeal))
			mapsIntoK := a.Have(
				"the chosen map takes S into k",
				"∀x:A. x ∈ S ⇒ φ(x) ∈ k",
				By(chosenResidues))
			preservesOne := a.Have(
				"fixing k makes the map preserve one",
				"φ(R.one) = R.one",
				By(comm_ring.OneIn.Read(ringK), fixesK.At(a.TermAs[A]("R.one"))))
			RS, RK := a.TermAs[RingOps[A]]("restrict_ring(R, S)"), a.TermAs[RingOps[A]]("restrict_ring(R, k)")
			ringMap := a.Have(
				"the map laws assemble to a ring homomorphism",
				"ring_homomorphism(restrict_ring(R, S), restrict_ring(R, k), φ)",
				By(
					ringS,
					ringK,
					mapsIntoK,
					preservesAdd,
					preservesMul,
					preservesOne,
					ring_homomorphism.RingHomomorphism.At(RS, RK, φ)))
			a.Show(
				"the chosen map is a ring map fixing k with kernel I",
				Witness(φ),
				By(ringMap, fixesK, kernelEqualsIdeal))
		}),
})}

// KernelFieldResidues — the kernel of a ring map f : S → k fixing the field
// k is the ideal of a k-rational point of S: an ideal of S, proper, and
// each member x of S congruent modulo it to its value, f(x) lying in k and
// f(x + -f(x)) = f(x) + -f(f(x)) being zero because f fixes f(x). One is
// outside the kernel, f(one) = one not being zero in k.
var KernelFieldResidues = kernelFieldResiduesThm{family.Add(registry.ProofEntry{
	Name: "KernelFieldResidues",
	Key:  "prop_60c1a122d4ca8284",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀k:set(A). ∀inv:(A → A). ∀S:set(A). ∀f:(A → A).",
		Hypotheses: []string{
			"ring_subfield(R, inv, k)",
			"ring_homomorphism(restrict_ring(R, S), restrict_ring(R, k), f)",
			"k ⊆ S",
			"∀c:A. c ∈ k ⇒ f(c) = c",
		},
		Conclusion: "rational_ideal(R, k, S, ring_kernel(R.zero, S, f))",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			k *Expr[Set[A]],
			inv *Arrow[A, A],
			subfieldK Fact,
			S *Expr[Set[A]],
			f *Arrow[A, A],
			given Fact,
		) {
			mapPremises := a.Conjuncts(
				given,
				"f is a ring map from S to k",
				"k lies in S",
				"f fixes k")
			ringMap, kInS, fixesK := mapPremises[0], mapPremises[1], mapPremises[2]
			fieldK := a.Unfolded(subfieldK, field.RingSubfieldDef)
			sourceRing := a.Have(
				"the homomorphism source is a commutative ring",
				"comm_ring_on(restrict_ring(R, S))",
				By(ring_homomorphism.Source.Read(ringMap)))
			kernelIdeal := a.Have(
				"the homomorphism kernel is an ideal",
				"ring_ideal(restrict_ring(R, S), ring_kernel(R.zero, S, f))",
				By(ring_homomorphism.KernelIdeal.Read(ringMap)))
			kernelProper := a.Have(
				"f keeps one, which is not zero in the target field, so the kernel excludes one",
				"R.one ∉ ring_kernel(R.zero, S, f)",
				Simp(Fwd(ring_homomorphism.RingKernelDef)),
				BySets(field.OneNotZeroOn.Read(fieldK), ring_homomorphism.MapOne.Read(ringMap)))
			kernelResidues := a.Have(
				"the value of each element is its residue modulo the kernel",
				"∀x:A. x ∈ S ⇒ ∃y:A. y ∈ k ∧ x + -y ∈ ring_kernel(R.zero, S, f)",
				Derive(func(b *Argument) {
					x := b.FixAs[A]()
					premises := b.Assume()
					imageInK := b.Have(
						"the image lies in k",
						"f(x) ∈ k",
						By(premises, ring_homomorphism.MapIn.Read(ringMap).AsFact().At(x)))
					imageInS := b.Have(
						"the image lies in S through k",
						"f(x) ∈ S",
						BySets(imageInK, kInS))
					negativeImageInS := b.Have(
						"its negative also lies in S",
						"-f(x) ∈ S",
						By(imageInS, comm_ring.NegIn.Read(sourceRing).AsFact().At(b.TermAs[A]("f(x)"))))
					residueInS := b.Have(
						"the residue difference lies in S",
						"x + -f(x) ∈ S",
						By(
							premises,
							negativeImageInS,
							comm_ring.AddIn.Read(sourceRing).AsFact().At(x, b.TermAs[A]("-f(x)"))))
					mapNegative := b.Have(
						"the map preserves the negative of the image",
						"f(-f(x)) = -f(f(x))",
						By(imageInS, ring_homomorphism.MapNeg.Read(ringMap).AsFact().At(b.TermAs[A]("f(x)"))))
					mapDifference := b.Have(
						"the map preserves the residue difference",
						"f(x + -f(x)) = f(x) + f(-f(x))",
						By(
							premises,
							negativeImageInS,
							ring_homomorphism.MapAdd.Read(ringMap).AsFact().At(x, b.TermAs[A]("-f(x)"))))
					fixesImage := b.Have(
						"the map fixes its own image because it lies in k",
						"f(f(x)) = f(x)",
						By(imageInK, fixesK.At(b.TermAs[A]("f(x)"))))
					imageSelfDifference := b.Have(
						"the image differs from itself by zero",
						"f(x) + -f(x) = R.zero",
						ByArith(ring_homomorphism.Target.Read(ringMap), imageInK))
					differenceMapsToZero := b.Have(
						"the residue difference maps to zero",
						"f(x + -f(x)) = R.zero",
						By(mapDifference, mapNegative, fixesImage, imageSelfDifference))
					differenceInKernel := b.Have(
						"the residue difference lies in the kernel",
						"x + -f(x) ∈ ring_kernel(R.zero, S, f)",
						BySets(
							residueInS,
							differenceMapsToZero,
							ring_homomorphism.RingKernelDef.At(b.TermAs[A]("R.zero"), S, f)))
					b.Show(
						"the map value is a residue modulo its kernel",
						Witness(b.TermAs[A]("f(x)")),
						By(imageInK, differenceInKernel))
				}))
			a.Show(
				"a proper ideal with residues in k is the ideal of a k-rational point",
				Simp(Fwd(RationalIdealDef)),
				By(kernelIdeal, kernelProper, kernelResidues))
		}),
})}
