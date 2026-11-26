// line_pairs.go — the line as a biaffine datum, its overlap the Laurent
// ring read through inv(t), and the pairs O(n) on it: O(0) the structure
// pair (k[t], k[1/t]); their charts read by the
// coefficients of a Laurent polynomial, the functions regular on both
// charts, k[t] ∩ k[1/t] = k, and no nonzero one of negative degree; the
// powers of t that move a vector between the charts of a lattice pair; a
// basis of each cohomology module of O(n) with the dimensions it counts and
// χ(O(n)); and the k-structure of H¹ of every lattice pair on the line.

package projective_line

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/laurent_polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/quotient_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/linear_independence"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/fractional_ideal"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_away"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_embed"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_real_lift"
	"github.com/euc-ai/xugo/library/proofs/scheme/invertible_lattice_pair"
	"github.com/euc-ai/xugo/library/proofs/scheme/lattice_pair"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// ---------------------------------------------------------------------------
// The datum
// ---------------------------------------------------------------------------

// ProjectiveLineBiaffine — k[t] and k[1/t] inside a field, glued along k[t,
// 1/t], form a biaffine datum. The overlap k[t, 1/t] is a ring of L holding k,
// t and inv(t) (laurent_polynomial.LaurentRingSubring), so it holds both
// charts, each the least ring holding k and its generator. Symmetrically
// k[1/t][t] is a ring holding k[1/t] and t, so it holds k[t], and with it every
// r = inv(t)ⁿ · (tⁿ · r) of the overlap: k[t, 1/t] lies in k[1/t][t]. A ring
// S[1/s] computed in the overlap's ring is the part of the S[1/s] computed in L
// that lies in the overlap, which is the whole overlap for k[t] and t, and for
// k[1/t] and inv(t).
var ProjectiveLineBiaffine = projectiveLineBiaffineThm{family.Add(registry.ProofEntry{
	Name: "ProjectiveLineBiaffine",
	Key:  "prop_15701074310bffee",
	Reading: "t ≠ zero is load-bearing: it makes t a unit of the field with " +
		"inverse inv(t). Transcendence is not asked — for t algebraic over k " +
		"the two charts and the overlap are all k(t), still a biaffine datum.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀t:A.",
		Hypotheses: []string{
			"subfield(L, k)",
			"t ∈ L.carrier",
			"t ≠ L.zero",
		},
		Conclusion: "biaffine(«plRing», «plChart0», «plChart1», t, L.inv(t))",
		Abbrev: Abbrev{
			{Name: "projectiveLineBiaffineInverted", Text: "ring_away(field_ring(L), «plChart1», L.inv(t))"},
		},
	},
		func(a *Argument, L field.FieldFact[on.L], k *Expr[Set[A]], t *Expr[A], h Fact) {
			hyp := a.Conjuncts(
				h,
				"k is a subfield of L",
				"t lies in L",
				"t is nonzero")
			subK, tInL, nonzero := hyp[0], hyp[1], hyp[2]
			ring := field.RingOn.Read(L)
			monoid := comm_ring.MulMonoidOn.Read(ring)
			tm := a.MemberOf[on.L](t, tInL)
			invT := field.InvIn.Read(L).At(tm)

			// S[1/s] computed in the ring on a part of L.
			inSubring := a.Have(
				"computed in the ring on a part Q of L, S[1/s] is its part in Q: "+
					"a member of either lies in Q and a power of s brings it into S",
				Statement{
					Binders: "∀Q S:set(A). ∀s:A.",
					Hypotheses: []string{
						"Q ⊆ L.carrier",
					},
					Conclusion: "ring_away(restrict_ring(field_ring(L), Q), S, s) = Q ∩ ring_away(field_ring(L), S, s)",
				},
				Simp(Fwd(set_basic.Extension), Fwd(set_basic.InInter), Fwd(ring_away.RingAwayMember)),
				BySets())

			unit := a.Have(
				"t is a unit of L with inverse inv(t)",
				"t * L.inv(t) = L.one",
				By(field.MulRightInverseOn.Read(L).AsFact().At(t), tInL, nonzero))
			unitLeft := a.Have(
				"and inv(t) a unit with inverse t",
				"L.inv(t) * t = L.one",
				By(field.MulLeftInverseOn.Read(L).AsFact().At(t), tInL, nonzero))

			// The charts k[t] and k[1/t].
			chart0 := a.Conjuncts(
				a.Have(
					"k[t] is a subring of L holding k and t",
					"subring(field_ring(L), «plChart0») ∧ k ⊆ «plChart0» ∧ t ∈ «plChart0»",
					By(subK, algebraic_element.PolynomialImageRing.Read(L).At(k, tm))),
				"k[t] is a subring of L",
				"holding k",
				"and t")
			chart1 := a.Conjuncts(
				a.Have(
					"k[1/t] is a subring of L holding k and inv(t)",
					"subring(field_ring(L), «plChart1») ∧ k ⊆ «plChart1» ∧ L.inv(t) ∈ «plChart1»",
					By(subK, algebraic_element.PolynomialImageRing.Read(L).At(k, invT))),
				"k[1/t] is a subring of L",
				"holding k",
				"and inv(t)")

			// The overlap k[t, 1/t] is a ring of L holding k, t and inv(t), so both charts.
			fieldRing := a.TermAs[module_record.RingOps[A]]("field_ring(L)")
			polynomials := a.TermAs[Set[A]]("«plChart0»")
			inversePolynomials := a.TermAs[Set[A]]("«plChart1»")
			overlap := a.TermAs[Set[A]]("«plOverlap»")
			overlapRing := a.Conjuncts(
				a.Have(
					"the overlap is a subring of L holding k, t and inv(t)",
					"subring(field_ring(L), «plOverlap») ∧ k ⊆ «plOverlap» ∧ t ∈ «plOverlap» ∧ L.inv(t) ∈ «plOverlap»",
					By(subK, tInL, nonzero, laurent_polynomial.LaurentRingSubring.Read(L).At(k, tm))),
				"the overlap is a subring of L",
				"it holds k",
				"it holds t",
				"it holds inv(t)")
			overlapRingOn := a.Have(
				"so it is a ring under L's operations",
				"comm_ring_on(«plRing»)",
				By(overlapRing[0], comm_ring.SubringRingOn.Read(ring).At(overlap)))
			overlapInL := a.Have(
				"lying in L",
				"«plOverlap» ⊆ L.carrier",
				By(comm_ring.SubringSubset.Read(overlapRing[0])))
			chart0InOverlap := a.Have(
				"so k[t], the least ring holding k and t, lies in k[t, 1/t]",
				"«plChart0» ⊆ «plOverlap»",
				By(
					algebraic_element.PolynomialImageLeast.Read(L).At(k, overlap, tm),
					overlapRingOn,
					overlapRing[1],
					overlapRing[2]))
			chart1InOverlap := a.Have(
				"and k[1/t], the least ring holding k and inv(t)",
				"«plChart1» ⊆ «plOverlap»",
				By(
					algebraic_element.PolynomialImageLeast.Read(L).At(k, overlap, invT),
					overlapRingOn,
					overlapRing[1],
					overlapRing[3]))

			// Symmetrically k[1/t][t] holds k[1/t] and t, so k[t].
			inverted := a.TermAs[Set[A]]("«projectiveLineBiaffineInverted»")
			invertedRing := a.Conjuncts(
				a.Have(
					"k[1/t][t] is a subring of L holding k[1/t] and the inverse t of inv(t)",
					"«plChart1» ⊆ «projectiveLineBiaffineInverted» ∧ "+
						"subring(field_ring(L), «projectiveLineBiaffineInverted») ∧ "+
						"t ∈ «projectiveLineBiaffineInverted»",
					By(
						ring_away.RingAwaySubring.At(fieldRing, inversePolynomials, invT),
						ring,
						chart1[0],
						chart1[2],
						unitLeft,
						tm)),
				"k[1/t] lies in k[1/t][t]",
				"which is a subring of L",
				"holding t")
			invertedRingOn := a.Have(
				"so k[1/t][t] is a ring under L's operations",
				"comm_ring_on(restrict_ring(field_ring(L), «projectiveLineBiaffineInverted»))",
				By(invertedRing[1], comm_ring.SubringRingOn.Read(ring).At(inverted)))
			kInInverted := a.Have(
				"k lies in k[1/t][t], through k[1/t]",
				"k ⊆ «projectiveLineBiaffineInverted»",
				BySets(chart1[1], invertedRing[0]))
			chart0InInverted := a.Have(
				"so k[t], the least ring holding k and t, lies in k[1/t][t]",
				"«plChart0» ⊆ «projectiveLineBiaffineInverted»",
				By(
					algebraic_element.PolynomialImageLeast.Read(L).At(k, inverted, t),
					invertedRingOn,
					kInInverted,
					invertedRing[2]))
			invInInverted := a.Have(
				"inv(t) lies in k[1/t][t], through k[1/t]",
				"L.inv(t) ∈ «projectiveLineBiaffineInverted»",
				BySets(invertedRing[0], chart1[2]))

			// k[t, 1/t] lies in k[1/t][t]: r = inv(t)ⁿ · (tⁿ · r) with tⁿ · r ∈ k[t].
			invertedMonoid := comm_ring.MulMonoidOn.Read(invertedRingOn)
			overlapInInverted := a.Have(
				"k[t, 1/t] lies in k[1/t][t]",
				"«plOverlap» ⊆ «projectiveLineBiaffineInverted»",
				Simp(Fwd(set_basic.SubsetDef)),
				Derive(func(b *Argument) {
					r := b.FixAs[A]("r")
					rInOverlap := b.Assume()
					members := b.Conjuncts(
						b.Have(
							"r lies in L, and some power of t brings it into k[t]",
							"r ∈ L.carrier ∧ (∃n:num. monoid_pow(L.mul, L.one, t, n) * r ∈ «plChart0»)",
							By(ring_away.RingAwayMember.At(fieldRing, polynomials, t, r), rInOverlap)),
						"r lies in L",
						"some power of t brings r into k[t]")
					rm := b.MemberOf[on.L](r, members[0])
					n, cleared := b.UnpackAs[Nat](members[1], "n")
					cancel := b.Have(
						"inv(t)ⁿ and tⁿ are inverse, as inv(t) and t are",
						"monoid_pow(L.mul, L.one, L.inv(t), n) * monoid_pow(L.mul, L.one, t, n) = L.one",
						By(unitLeft, comm_monoid.PowInverseOn.Read(monoid).At(invT, tm, n)))
					back := b.Have(
						"so r = inv(t)ⁿ · (tⁿ · r)",
						"monoid_pow(L.mul, L.one, L.inv(t), n) * (monoid_pow(L.mul, L.one, t, n) * r) = r",
						ByArith(
							ring,
							comm_monoid.PowIn.Read(monoid).At(invT, n),
							comm_monoid.PowIn.Read(monoid).At(tm, n),
							rm,
							Scaled(r, cancel)))
					clearedIn := proof.MemberOf(b.TermAs[A]("monoid_pow(L.mul, L.one, t, n) * r"),
						b.Have(
							"tⁿ · r lies in k[1/t][t], as k[t] does",
							"monoid_pow(L.mul, L.one, t, n) * r ∈ «projectiveLineBiaffineInverted»",
							BySets(chart0InInverted, cleared)))
					power := comm_monoid.PowIn.Read(invertedMonoid).At(
						proof.MemberOf(b.TermAs[A]("L.inv(t)"), invInInverted), n)
					b.Show(
						"a product of inv(t)ⁿ and tⁿ · r, both in the ring k[1/t][t]",
						By(back, comm_ring.MulIn.Read(invertedRingOn).At(power, clearedIn)))
				}))

			// Computed in the overlap's own ring, both localizations are the overlap.
			awayFromT := a.Have(
				"computed in its own ring, k[t, 1/t] is k[t] with t inverted",
				"«plOverlap» = ring_away(«plRing», «plChart0», t)",
				BySets(inSubring.At(overlap, polynomials, t), overlapInL))
			invertedInOverlap := a.Have(
				"computed in the overlap's ring, k[1/t] with inv(t) inverted is the part of k[1/t][t] in k[t, 1/t]",
				"ring_away(«plRing», «plChart1», L.inv(t)) = «plOverlap» ∩ «projectiveLineBiaffineInverted»",
				By(inSubring.At(overlap, inversePolynomials, invT), overlapInL))
			awayFromInv := a.Have(
				"which is all of k[t, 1/t], as k[t, 1/t] lies in k[1/t][t]",
				"«plOverlap» = ring_away(«plRing», «plChart1», L.inv(t))",
				invertedInOverlap.Rw(),
				By(set_order.SubsetInterAbsorption.At(overlap, inverted), overlapInInverted))
			// Restricted inside the overlap's ring, each chart is the same ring as restricted inside L.
			chart0Ring := a.Have(
				"k[t] restricted from the overlap's ring is k[t] restricted from L",
				"restrict_ring(«plRing», «plChart0») = restrict_ring(field_ring(L), «plChart0»)",
				Unfold(module_record.RestrictRingDef))
			chart1Ring := a.Have(
				"and likewise k[1/t]",
				"restrict_ring(«plRing», «plChart1») = restrict_ring(field_ring(L), «plChart1»)",
				Unfold(module_record.RestrictRingDef))
			chart0Subring := a.Have(
				"so k[t], a subring of L inside the overlap, is a subring of the overlap's ring",
				"subring(«plRing», «plChart0»)",
				By(
					chart0[0],
					chart0InOverlap,
					chart0Ring,
					comm_ring.SubringRingOn.Read(ring).At(polynomials),
					comm_ring.SubringRingOn.Read(overlapRingOn).At(polynomials)))
			chart1Subring := a.Have(
				"and so is k[1/t]",
				"subring(«plRing», «plChart1»)",
				By(
					chart1[0],
					chart1InOverlap,
					chart1Ring,
					comm_ring.SubringRingOn.Read(ring).At(inversePolynomials),
					comm_ring.SubringRingOn.Read(overlapRingOn).At(inversePolynomials)))
			a.Show(
				"so the overlap's ring, its two charts, t and inv(t) form "+
					"a biaffine datum, every clause of the definition in hand",
				By(
					lattice_pair.BiaffineDef.At(
						a.TermAs[module_record.RingOps[A]]("«plRing»"), polynomials, inversePolynomials, t, invT),
					overlapRingOn,
					chart0Subring,
					chart1Subring,
					chart0[2],
					chart1[2],
					unit,
					awayFromT,
					awayFromInv))
		}),
})}

// LaurentThroughInverse — the Laurent ring k[t, 1/t] read through inv(t):
// the members of L a power of inv(t) brings into k[1/t] are those a power
// of t brings into k[t]. The line's own biaffine datum has k[t, 1/t] =
// k[1/t] with inv(t) inverted inside k[t, 1/t], and inverting inv(t)
// there or in L is one set, k[t, 1/t] holding its inverse t
// (RingAwayInSubring).
var LaurentThroughInverse = laurentThroughInverseThm{family.Add(registry.ProofEntry{
	Name: "LaurentThroughInverse",
	Key:  "prop_af57ad3f91ecf505",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀t:A.",
		Hypotheses: []string{
			"subfield(L, k)",
			"t ∈ L.carrier",
			"t ≠ L.zero",
		},
		Conclusion: "ring_away(field_ring(L), «plChart1», L.inv(t)) = «plOverlap»",
	},
		func(arg *Argument, L field.FieldFact[on.L], k *Expr[Set[A]], t *Expr[A], given Fact) {
			parts := arg.Conjuncts(
				given,
				"k is a subfield of L",
				"t lies in L",
				"t is not zero")
			subK, nonzero := parts[0], parts[2]
			tm := arg.MemberOf[on.L](t, parts[1])
			biaffine := arg.Have(
				"k[t] and k[1/t] glued along k[t, 1/t] are a biaffine datum",
				"biaffine(«plRing», «plChart0», «plChart1», t, L.inv(t))",
				By(subK, nonzero, ProjectiveLineBiaffine.Read(L).At(k, tm)))
			line := arg.Unfolded(biaffine, lattice_pair.BiaffineDef)
			overlap := arg.Have(
				"the overlap is a subring of L",
				"subring(field_ring(L), «plOverlap»)",
				By(subK, nonzero, laurent_polynomial.LaurentRingSubring.Read(L).At(k, tm)))
			chart1In := arg.Have(
				"so k[1/t], a chart of the datum, lies in the overlap",
				"«plChart1» ⊆ «plOverlap»",
				By(
					biaffine,
					comm_ring.SubringSubset.Read(overlap),
					invertible_lattice_pair.ChartRingsInField.Read(L).At(
						arg.TermAs[Set[A]]("«plChart0»"),
						arg.TermAs[Set[A]]("«plChart1»"),
						arg.TermAs[Set[A]]("«plOverlap»"),
						t)))
			arg.Show(
				"k[1/t] with inv(t) inverted in L is k[1/t] with inv(t) "+
					"inverted in k[t, 1/t], which the line's datum says is k[t, 1/t]",
				CalcEq(
					Leg(
						arg.Term("ring_away(«plRing», «plChart1», L.inv(t))"),
						"k[t, 1/t] holding t",
						By(
							subK,
							nonzero,
							line,
							field.MulLeftInverseOn.Read(L).At(tm),
							chart1In,
							laurent_polynomial.LaurentRingSubring.Read(L).At(k, tm),
							field.RingOn.Read(L),
							ring_away.RingAwayInSubring.At(
								arg.TermAs[module_record.RingOps[A]]("field_ring(L)"),
								arg.TermAs[Set[A]]("«plOverlap»"),
								arg.TermAs[Set[A]]("«plChart1»"),
								arg.TermAs[A]("L.inv(t)"),
								t))),
					FinalLeg(
						"as the line's datum says",
						By(line)),
				))
		}),
})}

// LineDatum — for t a nonzero member of the field, the line is a biaffine datum
// inside L: k lies in k[t] and in k[1/t], both rings lying in the ring k[t,
// 1/t], which lies in L; t lies in k[t] and inv(t) in k[1/t] and in the
// overlap; and L is a module over k, over k[t], over k[1/t] and over the
// overlap. Each chart is a ring of L holding k (PolynomialImageRing), the
// overlap a subring holding inv(t) (laurent_polynomial.LaurentRingSubring), and
// a subring of L acts on L by the field's product.
var LineDatum = lineDatumThm{family.Add(registry.ProofEntry{
	Name: "LineDatum",
	Key:  "prop_781c3a42b1024074",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀t:A.",
		Hypotheses: []string{
			"subfield(L, k)",
			"t ∈ L.carrier",
			"t ≠ L.zero",
		},
		Conclusion: "biaffine(«plRing», «plChart0», «plChart1», t, L.inv(t)) ∧ " +
			"k ⊆ «plChart0» ∧ " +
			"k ⊆ «plChart1» ∧ " +
			"«plChart0» ⊆ «plOverlap» ∧ " +
			"«plChart1» ⊆ «plOverlap» ∧ " +
			"subring(field_ring(L), «plChart0») ∧ " +
			"subring(field_ring(L), «plChart1») ∧ " +
			"subring(field_ring(L), «plOverlap») ∧ " +
			"t ∈ «plChart0» ∧ " +
			"L.inv(t) ∈ «plChart1» ∧ " +
			"L.inv(t) ∈ «plOverlap» ∧ " +
			"module_on(«plScalars», «plField») ∧ " +
			"module_on(«plRing0», «plField») ∧ " +
			"module_on(«plRing1», «plField») ∧ " +
			"module_on(«plRing», «plField»)",
	},
		func(a *Argument, L field.FieldFact[on.L], k *Expr[Set[A]], t *Expr[A], h Fact) {
			hyp := a.Conjuncts(
				h,
				"k is a subfield of L",
				"t lies in L",
				"t is not zero")
			subK, tInL, nonzero := hyp[0], hyp[1], hyp[2]
			tm := a.MemberOf[on.L](t, tInL)
			biaffine := a.Have(
				"k[t] and k[1/t], glued along the overlap, form a biaffine datum",
				"biaffine(«plRing», «plChart0», «plChart1», t, L.inv(t))",
				By(subK, nonzero, ProjectiveLineBiaffine.Read(L).At(k, tm)))
			overlap := a.Conjuncts(
				a.Have(
					"the overlap is a subring of L holding k, t and inv(t)",
					"subring(field_ring(L), «plOverlap») ∧ k ⊆ «plOverlap» ∧ t ∈ «plOverlap» ∧ L.inv(t) ∈ «plOverlap»",
					By(subK, tInL, nonzero, laurent_polynomial.LaurentRingSubring.Read(L).At(k, tm))),
				"the overlap is a subring of L",
				"it holds k",
				"it holds t",
				"it holds inv(t)")
			chart0Set, chart1Set, overlapSet :=
				a.TermAs[Set[A]]("«plChart0»"), a.TermAs[Set[A]]("«plChart1»"), a.TermAs[Set[A]]("«plOverlap»")
			chartsIn := a.Have(
				"so both charts of the datum lie in the overlap",
				"«plChart0» ⊆ «plOverlap» ∧ «plChart1» ⊆ «plOverlap»",
				By(
					biaffine,
					comm_ring.SubringSubset.Read(overlap[0]),
					invertible_lattice_pair.ChartRingsInField.Read(L).At(chart0Set, chart1Set, overlapSet, t)))
			chart0 := a.Conjuncts(
				a.Have(
					"k[t] is a ring of L holding k and t",
					"subring(field_ring(L), «plChart0») ∧ "+
						"k ⊆ «plChart0» ∧ "+
						"t ∈ «plChart0» ∧ "+
						"«plChart0» ⊆ field_adjoin(L, k, {t})",
					By(subK, algebraic_element.PolynomialImageRing.Read(L).At(k, tm))),
				"k[t] is a subring of L",
				"k lies in k[t]",
				"t lies in k[t]",
				"k[t] lies in k(t)")
			chart1 := a.Conjuncts(
				a.Have(
					"k[1/t] is a ring of L holding k and inv(t)",
					"subring(field_ring(L), «plChart1») ∧ "+
						"k ⊆ «plChart1» ∧ "+
						"L.inv(t) ∈ «plChart1» ∧ "+
						"«plChart1» ⊆ field_adjoin(L, k, {L.inv(t)})",
					By(subK, algebraic_element.PolynomialImageRing.Read(L).At(k, field.InvIn.Read(L).At(tm)))),
				"k[1/t] is a subring of L",
				"k lies in k[1/t]",
				"inv(t) lies in k[1/t]",
				"k[1/t] lies in k(inv(t))")
			fieldRing := a.TermAs[module_record.RingOps[A]]("field_ring(L)")
			overK := a.Have(
				"L is a vector space over k, a subring of it",
				"module_on(«plScalars», «plField»)",
				By(
					subK,
					field.SubfieldSubring.Read(L).At(k),
					fractional_ideal.FieldModuleOn.Read(L).At(k),
					module_record.RestrictRingDef.At(a.TermAs[module_record.RingOps[A]]("«plRing»"), k),
					module_record.RestrictRingDef.At(fieldRing, k)))
			a.Show(
				"the line's datum, gathered",
				By(
					biaffine,
					chart0[1],
					chart1[1],
					chartsIn,
					chart0[0],
					chart1[0],
					overlap[0],
					chart0[2],
					chart1[2],
					overlap[3],
					overK,
					fractional_ideal.FieldModuleOn.Read(L).At(chart0Set),
					fractional_ideal.FieldModuleOn.Read(L).At(chart1Set),
					fractional_ideal.FieldModuleOn.Read(L).At(overlapSet)))
		}),
})}

// ---------------------------------------------------------------------------
// The pairs O(n)
// ---------------------------------------------------------------------------

// LinePairZero — O(0) is the structure pair (k[t], k[1/t]): chart 1 of
// O(0) is t⁰ · k[1/t], t⁰ is the empty product, one, and one fixes
// every member of k[1/t], a subset of L.
var LinePairZero = linePairZeroThm{family.Add(registry.ProofEntry{
	Name:    "LinePairZero",
	Key:     "prop_95acbd09f8a14271",
	Reading: "Even t = zero passes: only inv(t) ∈ L is used, which holds at zero.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀t:A.",
		Hypotheses: []string{
			"subfield(L, k)",
			"t ∈ L.carrier",
		},
		Conclusion: "projective_line_pair(L, k, t, &0) = («plChart0», «plChart1»)",
	},
		func(a *Argument, L field.FieldFact[on.L], k *Expr[Set[A]], t *Expr[A], h Fact) {
			hyp := a.Conjuncts(
				h,
				"k is a subfield of L",
				"t lies in L")
			subK, tInL := hyp[0], hyp[1]
			tm := a.MemberOf[on.L](t, tInL)
			chart1Subring := a.Have(
				"k[1/t] is a subring of L, inv(t) lying in L",
				"subring(field_ring(L), «plChart1»)",
				By(subK, algebraic_element.PolynomialImageRing.Read(L).At(k, field.InvIn.Read(L).At(tm))))
			a.Show(
				"t⁰ being the empty product, one, which moves no member "+
					"of k[1/t], O(0) = (k[t], t⁰ · k[1/t]) = (k[t], k[1/t])",
				By(
					laurent_polynomial.LaurentMonomialOfNum,
					comm_monoid.MonoidPowDef,
					comm_ring.SubringSubset.Read(chart1Subring),
					fractional_ideal.ScaleOne.Read(L).At(a.TermAs[Set[A]]("«plChart1»")),
					ProjectiveLinePairDef))
		}),
})}

// LineChartCoefficients — the charts by their coefficients: for t
// transcendental over k, a member of k[t] is a Laurent polynomial with no
// negative powers of t, and a member of k[1/t] one with no positive powers.
// Both charts are polynomial images read along the naturals
// (laurent_polynomial.PolynomialImageCoefficients), k[t] along m ↦ m and k[1/t]
// along m ↦ −m; an integer is no natural number exactly when it is negative,
// and no −m exactly when it is positive.
var LineChartCoefficients = lineChartCoefficientsThm{family.Add(registry.ProofEntry{
	Name:    "LineChartCoefficients",
	Key:     "prop_820e9d2825e7f83f",
	Reading: "Both halves need transcendence: for t algebraic, inv(t) is itself a polynomial in t.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀t f:A.",
		Hypotheses: []string{
			"subfield(L, k)",
			"t ∈ L.carrier",
			"¬algebraic_over(L, k, t)",
		},
		Conclusion: "(f ∈ «plChart0» ⇔ " +
			"    f ∈ «plOverlap» ∧ (∀i:int. i < &0 ⇒ laurent_polynomial_coefficient(k, t, f, i) = L.zero)) ∧ " +
			"(f ∈ «plChart1» ⇔ " +
			"    f ∈ «plOverlap» ∧ (∀i:int. &0 < i ⇒ laurent_polynomial_coefficient(k, t, f, i) = L.zero))",
	},
		func(arg *Argument, L field.FieldFact[on.L], k *Expr[Set[A]], t, f *Expr[A], h Fact) {
			hyp := arg.Conjuncts(
				h,
				"k is a subfield of L",
				"t lies in L",
				"t is transcendental over k")
			subK, tInL, transcendental := hyp[0], hyp[1], hyp[2]
			tm := arg.MemberOf[on.L](t, tInL)
			overlap := arg.Conjuncts(
				arg.Have(
					"the overlap is a subring of L holding k, t and inv(t)",
					"subring(field_ring(L), «plOverlap») ∧ k ⊆ «plOverlap» ∧ t ∈ «plOverlap» ∧ L.inv(t) ∈ «plOverlap»",
					By(
						subK,
						tInL,
						h,
						algebraic_element.TranscendentalInverse.Read(L).At(k, tm),
						laurent_polynomial.LaurentRingSubring.Read(L).At(k, tm))),
				"the overlap is a subring of L",
				"it holds k",
				"it holds t",
				"it holds inv(t)")
			tInO, invInO := overlap[2], overlap[3]
			invT := arg.TermAs[A]("L.inv(t)")

			// The two charts read along the naturals: k[t] along m ↦ m, k[1/t] along m ↦ −m.
			upPowers := arg.Have(
				"t at a natural m is the m-th power of t",
				"∀m:num. laurent_monomial(t, &m) = monoid_pow(L.mul, L.one, t, m)",
				By(laurent_polynomial.LaurentMonomialOfNum))
			downPowers := arg.Have(
				"t at −m is the m-th power of inv(t)",
				"∀m:num. laurent_monomial(t, -&m) = monoid_pow(L.mul, L.one, L.inv(t), m)",
				By(laurent_polynomial.LaurentMonomialOfNum))
			negatedBack := arg.Have(
				"m ↦ num_of_int(−m) undoes m ↦ −m",
				"∀m:num. num_of_int(--&m) = m",
				By(Normalized, int_real_lift.NegNeg, int_embed.OfNumRetract))
			up := arg.TermAs[Fun[Nat, Int]]("λm:num. &m")
			down := arg.TermAs[Fun[Nat, Int]]("λm:num. -&m")
			chartZero := arg.Have(
				"k[t] is the Laurent polynomials whose coefficients vanish off the naturals",
				"«plChart0» = "+
					"{g:A | "+
					"    g ∈ «plOverlap» ∧ "+
					"    (∀i:int. (∀m:num. &m ≠ i) ⇒ laurent_polynomial_coefficient(k, t, g, i) = L.zero)}",
				By(
					subK,
					tInL,
					transcendental,
					tInO,
					int_embed.OfNumRetract,
					upPowers,
					laurent_polynomial.PolynomialImageCoefficients.Read(L).At(
						k, tm, t, up, arg.TermAs[Fun[Int, Nat]]("num_of_int"))))
			chartOne := arg.Have(
				"k[1/t] is the Laurent polynomials whose coefficients vanish off the nonpositive integers",
				"«plChart1» = "+
					"{g:A | "+
					"    g ∈ «plOverlap» ∧ "+
					"    (∀i:int. (∀m:num. -&m ≠ i) ⇒ laurent_polynomial_coefficient(k, t, g, i) = L.zero)}",
				By(
					subK,
					tInL,
					transcendental,
					invInO,
					negatedBack,
					downPowers,
					laurent_polynomial.PolynomialImageCoefficients.Read(L).At(
						k, tm, invT, down, arg.TermAs[Fun[Int, Nat]]("λj:int. num_of_int(-j)"))))
			negatives := arg.Have(
				"an integer is no natural number exactly when it is negative",
				"∀i:int.(∀m:num. &m ≠ i) ⇔ i < &0",
				arg.ForEach(func(i *Expr[Int]) Action {
					return Derive(func(b *Argument) {
						b.Iff()
						b.Forward(
							"a nonnegative i would be &num_of_int(i)",
							func(c *Argument, missed Fact) {
								c.Show(
									"so i is negative",
									ByArith(missed.At(c.TermAs[Nat]("num_of_int(i)")), int_embed.NumOfInt.At(i)))
							})
						b.Backward(
							"a natural number is never negative",
							func(c *Argument, negative Fact) {
								c.Show(
									"so no &m is i",
									c.ForEach(func(m *Expr[Nat]) Action { return ByArith(negative) }))
							})
					})
				}))
			positives := arg.Have(
				"an integer is no −m exactly when it is positive",
				"∀i:int.(∀m:num. -&m ≠ i) ⇔ &0 < i",
				arg.ForEach(func(i *Expr[Int]) Action {
					return Derive(func(b *Argument) {
						b.Iff()
						b.Forward(
							"a nonpositive i would be −&num_of_int(−i)",
							func(c *Argument, missed Fact) {
								c.Show(
									"so i is positive",
									ByArith(missed.At(c.TermAs[Nat]("num_of_int(-i)")), int_embed.NumOfInt.At(c.TermAs[Int]("-i"))))
							})
						b.Backward(
							"−m is never positive",
							func(c *Argument, positive Fact) {
								c.Show(
									"so no −&m is i",
									c.ForEach(func(m *Expr[Nat]) Action { return ByArith(positive) }))
							})
					})
				}))
			firstChart := arg.Have(
				"so a member of k[t] is a Laurent polynomial with no negative powers",
				"f ∈ «plChart0» ⇔ "+
					"f ∈ «plOverlap» ∧ (∀i:int. i < &0 ⇒ laurent_polynomial_coefficient(k, t, f, i) = L.zero)",
				Simp(Rev(negatives)),
				BySets(chartZero))
			secondChart := arg.Have(
				"and a member of k[1/t] one with no positive powers",
				"f ∈ «plChart1» ⇔ "+
					"f ∈ «plOverlap» ∧ (∀i:int. &0 < i ⇒ laurent_polynomial_coefficient(k, t, f, i) = L.zero)",
				Simp(Rev(positives)),
				BySets(chartOne))
			arg.Show(
				"the two charts by their coefficients",
				By(firstChart, secondChart))
		}),
})}

// LinePairCoefficients — the charts of O(n) by their coefficients: a member of
// k[t] is a Laurent polynomial with no negative powers (LineChartCoefficients),
// and a member of tⁿ · k[1/t] one with no power above n. Multiplying by tⁿ
// moves every coefficient n places up (laurent_polynomial.LaurentCoeffShift):
// tⁿ times a member of k[1/t], which has no positive power, has none above n;
// and a Laurent polynomial f with none above n is tⁿ times t⁻ⁿ · f, which has
// no positive power, so lies in k[1/t].
var LinePairCoefficients = linePairCoefficientsThm{family.Add(registry.ProofEntry{
	Name: "LinePairCoefficients",
	Key:  "prop_7649613f693915b3",
	Reading: "At n = 0, O(0) being (k[t], k[1/t]) (LinePairZero), this is LineChartCoefficients. " +
		"Both halves need transcendence: for t algebraic, inv(t) is itself a polynomial in t.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀t:A. ∀n:int. ∀f:A.",
		Hypotheses: []string{
			"subfield(L, k)",
			"t ∈ L.carrier",
			"¬algebraic_over(L, k, t)",
		},
		Conclusion: "(f ∈ fst(«plPairN») ⇔ " +
			"    f ∈ «plOverlap» ∧ (∀i:int. i < &0 ⇒ laurent_polynomial_coefficient(k, t, f, i) = L.zero)) ∧ " +
			"(f ∈ snd(«plPairN») ⇔ " +
			"    f ∈ «plOverlap» ∧ (∀i:int. n < i ⇒ laurent_polynomial_coefficient(k, t, f, i) = L.zero))",
	},
		func(
			arg *Argument,
			L field.FieldFact[on.L],
			k *Expr[Set[A]],
			t *Expr[A],
			n *Expr[Int],
			f *Expr[A],
			h Fact,
		) {
			hyp := arg.Conjuncts(
				h,
				"k is a subfield of L",
				"t lies in L",
				"t is transcendental over k")
			subK, tInL, transcendental := hyp[0], hyp[1], hyp[2]
			tm := arg.MemberOf[on.L](t, tInL)
			nonzero := arg.Have(
				"t, transcendental, is not zero",
				"t ≠ L.zero",
				By(h, algebraic_element.TranscendentalInverse.Read(L).At(k, tm)))

			// The overlap k[t, 1/t] is a subring of L holding t and inv(t), so every power of t.
			overlap := arg.Conjuncts(
				GroupPremises(hyp[0], nonzero, laurent_polynomial.LaurentRingSubring.Read(L).At(k, tm)),
				"the overlap is a subring of L",
				"it holds k",
				"it holds t",
				"it holds inv(t)")
			ringO := arg.Have(
				"the overlap is a commutative ring under L's operations",
				"comm_ring_on(restrict_ring(field_ring(L), «plOverlap»))",
				By(
					overlap[0],
					comm_ring.SubringRingOn.Read(field.RingOn.Read(L)).At(arg.TermAs[Set[A]]("«plOverlap»"))))
			powersInO := arg.Have(
				"every power of t lies in the overlap",
				"∀m:int. laurent_monomial(t, m) ∈ «plOverlap»",
				arg.ForEach(func(m *Expr[Int]) Action {
					return By(subK, nonzero, laurent_polynomial.LaurentMonomialInRing.Read(L).At(k, tm, m))
				}))
			firstChart := arg.Have(
				"a member of k[t] is a Laurent polynomial with no negative powers",
				"f ∈ «plChart0» ⇔ "+
					"f ∈ «plOverlap» ∧ (∀i:int. i < &0 ⇒ laurent_polynomial_coefficient(k, t, f, i) = L.zero)",
				By(subK, transcendental, LineChartCoefficients.Read(L).At(k, tm, f)))

			// tⁿ · k[1/t]: multiplying by tⁿ moves every coefficient n places up, and t⁻ⁿ moves it back.
			scale := arg.TermAs[Fun[A, A]]("L.mul(laurent_monomial(t, n))")
			chartOneSet := arg.TermAs[Set[A]]("«plChart1»")
			minusN := arg.TermAs[Int]("-n")
			tn := arg.TermAs[A]("laurent_monomial(t, n)")
			tnInO := arg.Have(
				"tⁿ lies in the overlap",
				"laurent_monomial(t, n) ∈ «plOverlap»",
				By(powersInO.At(n)))
			into := arg.Have(
				"a member of tⁿ · k[1/t] lies in the overlap with no power above n",
				Statement{
					Hypotheses: []string{
						"f ∈ «plChart1N»",
					},
					Conclusion: "f ∈ «plOverlap» ∧ " +
						"(∀i:int. n < i ⇒ laurent_polynomial_coefficient(k, t, f, i) = L.zero)",
				},
				Derive(func(b *Argument) {
					fIn := b.Assume()
					u, written := b.ObtainAs[A](
						"write f as tⁿ · u with u in k[1/t]",
						"∃u:A. f = laurent_monomial(t, n) * u ∧ u ∈ «plChart1»",
						By(fIn, set_basic.InImage.At(scale, chartOneSet, f)))
					parts := b.Conjuncts(
						written,
						"f = tⁿ · u",
						"u lies in k[1/t]")
					uFacts := b.Conjuncts(
						b.Have(
							"so u lies in the overlap with no positive power",
							"u ∈ «plOverlap» ∧ (∀i:int. &0 < i ⇒ laurent_polynomial_coefficient(k, t, u, i) = L.zero)",
							By(parts[1], subK, transcendental, LineChartCoefficients.Read(L).At(k, tm, u))),
						"u lies in the overlap",
						"u has no positive power")
					vanish := b.Have(
						"above n the coefficients of f are those of u above 0",
						"∀i:int. n < i ⇒ laurent_polynomial_coefficient(k, t, f, i) = L.zero",
						Derive(func(c *Argument) {
							i := c.FixAs[Int]("i")
							above := c.Assume()
							positive := c.Have(
								"i − n is positive",
								"&0 < i - n",
								ByArith(above))
							c.Show(
								"tⁿ carries the coefficient of u at i − n to i",
								By(
									parts[0],
									positive,
									uFacts[1].At(c.TermAs[Int]("i - n")),
									subK,
									transcendental,
									uFacts[0],
									laurent_polynomial.LaurentCoeffShift.Read(L).At(k, tm, u, n, i)))
						}))
					b.Show(
						"f lies in the overlap with no power above n",
						By(
							parts[0],
							comm_ring.MulIn.Read(ringO).At(proof.MemberOf(tn, tnInO), proof.MemberOf(u, uFacts[0])),
							vanish))
				}))
			onto := arg.Have(
				"a Laurent polynomial with no power above n lies in tⁿ · k[1/t]",
				Statement{
					Hypotheses: []string{
						"f ∈ «plOverlap»",
						"∀i:int. n < i ⇒ laurent_polynomial_coefficient(k, t, f, i) = L.zero",
					},
					Conclusion: "f ∈ «plChart1N»",
				},
				Derive(func(b *Argument) {
					fFacts := b.Conjuncts(
						b.Assume(),
						"f lies in the overlap",
						"f has no power above n")
					lowered := b.TermAs[A]("laurent_monomial(t, -n) * f")
					loweredInO := b.Have(
						"t⁻ⁿ · f lies in the overlap",
						"laurent_monomial(t, -n) * f ∈ «plOverlap»",
						By(powersInO.At(minusN), fFacts[0], comm_ring.MulIn.Read(ringO)))
					loweredVanish := b.Have(
						"t⁻ⁿ · f has no positive power",
						"∀i:int. &0 < i ⇒ laurent_polynomial_coefficient(k, t, laurent_monomial(t, -n) * f, i) = L.zero",
						Derive(func(c *Argument) {
							i := c.FixAs[Int]("i")
							positive := c.Assume()
							above := c.Have(
								"i + n lies above n",
								"n < i - -n",
								ByArith(positive))
							c.Show(
								"t⁻ⁿ carries the coefficient of f at i + n to i",
								By(
									above,
									fFacts[1].At(c.TermAs[Int]("i - -n")),
									subK,
									transcendental,
									fFacts[0],
									laurent_polynomial.LaurentCoeffShift.Read(L).At(k, tm, f, minusN, i)))
						}))
					loweredIn := b.Have(
						"so t⁻ⁿ · f lies in k[1/t]",
						"laurent_monomial(t, -n) * f ∈ «plChart1»",
						By(
							loweredInO,
							loweredVanish,
							subK,
							transcendental,
							LineChartCoefficients.Read(L).At(k, tm, lowered)))
					unit := b.Have(
						"tⁿ · t⁻ⁿ = one",
						"laurent_monomial(t, n) * laurent_monomial(t, -n) = L.one",
						By(nonzero, laurent_polynomial.LaurentMonomialInverse.Read(L).At(tm, n)))
					recovered := b.Have(
						"tⁿ · (t⁻ⁿ · f) = f",
						"laurent_monomial(t, n) * (laurent_monomial(t, -n) * f) = f",
						ByArith(ringO, powersInO.At(n), powersInO.At(minusN), fFacts[0], Scaled(f, unit)))
					b.Show(
						"f is tⁿ times t⁻ⁿ · f, a member of k[1/t]",
						By(Normalized, recovered, loweredIn, set_image.FunInImage.At(scale, chartOneSet, lowered)))
				}))
			arg.Show(
				"O(n) is the pair of the two charts",
				Unfold(ProjectiveLinePairDef),
				Simp(Fwd(pairs.Fst), Fwd(pairs.Snd)),
				By(firstChart, into, onto))
		}),
})}

// LineChartSumCoefficients — a member of k[t] + tⁿ · k[1/t], the sum of
// the two charts of O(n), has no coefficient strictly between n and 0: it
// is p + r with p in k[t], which has no negative coefficient, and r in
// tⁿ · k[1/t], which has none above n, and the coefficient is additive.
var LineChartSumCoefficients = lineChartSumCoefficientsThm{family.Add(registry.ProofEntry{
	Name: "LineChartSumCoefficients",
	Key:  "prop_a749863823d444e",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀t:A. ∀n i:int. ∀f:A.",
		Hypotheses: []string{
			"subfield(L, k)",
			"t ∈ L.carrier",
			"¬algebraic_over(L, k, t)",
			"n < i",
			"i < &0",
			"f ∈ «plChartSumN»",
		},
		Conclusion: "laurent_polynomial_coefficient(k, t, f, i) = L.zero",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k *Expr[Set[A]],
			t *Expr[A],
			n, i *Expr[Int],
			f *Expr[A],
			h Fact,
		) {
			parts := a.Conjuncts(
				h,
				"k is a subfield of L",
				"t lies in L",
				"t is transcendental over k",
				"i lies above n",
				"i is negative",
				"f lies in k[t] + tⁿ · k[1/t]")
			sub, transcendental := parts[0], parts[2]
			tm := a.MemberOf[on.L](t, parts[1])
			first, second := a.TermAs[Set[A]]("fst(«plPairN»)"), a.TermAs[Set[A]]("snd(«plPairN»)")
			p, r, split := a.Obtain2As[A, A](
				"f is p + r with p in k[t] and r in tⁿ · k[1/t]",
				"∃p r:A. p ∈ fst(«plPairN») ∧ r ∈ snd(«plPairN») ∧ f = p + r",
				By(parts[5], quotient_group.InSetMul.At(a.TermAs[Op[A]]("L.add"), first, second, f)))
			pieces := a.Conjuncts(
				split,
				"p lies in k[t]",
				"r lies in tⁿ · k[1/t]",
				"f is p + r")

			// The charts of O(n) by their coefficients: p has none at a negative
			// power and r none above n, and i is negative and above n.
			pAt := a.Conjuncts(
				a.Have(
					"p lies in the overlap with no coefficient at tⁱ, i being negative",
					"p ∈ «plOverlap» ∧ laurent_polynomial_coefficient(k, t, p, i) = L.zero",
					By(pieces[0], parts[4], sub, transcendental, LinePairCoefficients.Read(L).At(k, tm, n, p))),
				"p lies in the overlap",
				"p has no coefficient at tⁱ")
			rAt := a.Conjuncts(
				a.Have(
					"r lies in the overlap with no coefficient at tⁱ, i being above n",
					"r ∈ «plOverlap» ∧ laurent_polynomial_coefficient(k, t, r, i) = L.zero",
					By(pieces[1], parts[3], sub, transcendental, LinePairCoefficients.Read(L).At(k, tm, n, r))),
				"r lies in the overlap",
				"r has no coefficient at tⁱ")

			// The coefficient at tⁱ is additive on the overlap.
			linear := a.Have(
				"the coefficient at tⁱ is k-linear on the overlap",
				"module_homomorphism(«plRingK», "+
					"    «plOverlapModule», "+
					"    restrict_module(regular_module(field_ring(L)), k), "+
					"    λg:A. laurent_polynomial_coefficient(k, t, g, i))",
				By(sub, transcendental, laurent_polynomial.LaurentCoeffLinear.Read(L).At(k, tm, i)))
			zeroSum := a.Have(
				"zero + zero is zero",
				"L.zero + L.zero = L.zero",
				ByArith(field.RingOn.Read(L)))
			a.Show(
				"so the coefficient of f = p + r at tⁱ is zero + zero",
				By(
					pieces[2],
					zeroSum,
					pAt[1],
					rAt[1],
					module_homomorphism.HomAdd.Read(linear).At(proof.MemberOf(p, pAt[0]), proof.MemberOf(r, rAt[0]))))
		}),
})}

// LinePairChartPowers — for a lattice pair M on the line and i ≤ j,
// raising the power of t keeps a vector in chart 0 and lowering it keeps
// it in chart 1: tⁱ · v ∈ fst(M) gives tʲ · v ∈ fst(M), and tʲ · v ∈
// snd(M) gives tⁱ · v ∈ snd(M). tʲ · v is t^(j−i) · (tⁱ · v) with t^(j−i)
// in k[t], over which fst(M) is a module, and tⁱ · v is t^(i−j) · (tʲ · v)
// with t^(i−j) in k[1/t] (laurent_polynomial.LaurentMonomialInPolynomials).
var LinePairChartPowers = linePairChartPowersThm{family.Add(registry.ProofEntry{
	Name: "LinePairChartPowers",
	Key:  "prop_9ddddcd55d7718e0",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). " +
			"∀k:set(A). " +
			"∀t:A. " +
			"∀V:module_ops(A, B). " +
			"∀M:prod(set(B), set(B)). " +
			"∀v:B. " +
			"∀i j:int.",
		Hypotheses: []string{
			"subfield(L, k)",
			"t ∈ L.carrier",
			"t ≠ L.zero",
			"«plPairOnLine»",
			"v ∈ V.carrier",
			"i ≤ j",
		},
		Conclusion: "(laurent_monomial(t, i) • v ∈ fst(M) ⇒ laurent_monomial(t, j) • v ∈ fst(M)) ∧ " +
			"(laurent_monomial(t, j) • v ∈ snd(M) ⇒ laurent_monomial(t, i) • v ∈ snd(M))",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k *Expr[Set[A]],
			t *Expr[A],
			V *Expr[ModuleOps[A, B]],
			M *Expr[Prod[Set[B], Set[B]]],
			v *Expr[B],
			i, j *Expr[Int],
			h Fact,
		) {
			given := a.Conjuncts(
				h,
				"k is a subfield of L",
				"t lies in L",
				"t is not zero",
				"M is a lattice pair on the line",
				"v is a vector",
				"i is at most j")
			subK, tInL, nonzero, pair, vV, order := given[0], given[1], given[2], given[3], given[4], given[5]
			tm := a.MemberOf[on.L](t, tInL)
			parts := a.Conjuncts(
				a.Unfolded(pair, lattice_pair.LatticePairDef),
				"V is a module over the overlap",
				"fst(M) is a k[t]-submodule of V",
				"snd(M) is a k[1/t]-submodule of V",
				"the two charts span one module over the overlap")
			vectors, sub0, sub1 := parts[0], parts[1], parts[2]
			up, down := a.TermAs[Int]("j - i"), a.TermAs[Int]("i - j")
			gaps := a.Conjuncts(
				a.Have(
					"j − i is not negative and i − j not positive",
					"&0 ≤ j - i ∧ i - j ≤ &0",
					ByArith(order)),
				"j − i is not negative",
				"i − j is not positive")
			charts := laurent_polynomial.LaurentMonomialInPolynomials.Read(L)
			raise := a.Have(
				"so t^(j−i) lies in k[t]",
				"laurent_monomial(t, j - i) ∈ «plChart0»",
				By(subK, gaps[0], charts.At(k, tm, up)))
			lower := a.Have(
				"and t^(i−j) in k[1/t]",
				"laurent_monomial(t, i - j) ∈ «plChart1»",
				By(subK, gaps[1], charts.At(k, tm, down)))

			// tʲ = t^(j−i) · tⁱ and tⁱ = t^(i−j) · tʲ, scalars of the overlap acting on V.
			products := laurent_polynomial.LaurentMonomialProduct.Read(L).At(tm)
			overlap := laurent_polynomial.LaurentMonomialInRing.Read(L)
			sumUp := a.Have(
				"(j − i) + i = j",
				"j - i + i = j",
				ByArith())
			sumDown := a.Have(
				"(i − j) + j = i",
				"i - j + j = i",
				ByArith())
			splitUp := a.Have(
				"tʲ · v = t^(j−i) · (tⁱ · v)",
				"laurent_monomial(t, j) • v = laurent_monomial(t, j - i) • (laurent_monomial(t, i) • v)",
				By(
					nonzero,
					sumUp,
					vV,
					subK,
					products,
					overlap.At(k, tm, up),
					overlap.At(k, tm, i),
					module.SmulMul.Read(vectors).AsFact().At(
						a.TermAs[A]("laurent_monomial(t, j - i)"), a.TermAs[A]("laurent_monomial(t, i)"), v)))
			splitDown := a.Have(
				"tⁱ · v = t^(i−j) · (tʲ · v)",
				"laurent_monomial(t, i) • v = laurent_monomial(t, i - j) • (laurent_monomial(t, j) • v)",
				By(
					nonzero,
					sumDown,
					vV,
					subK,
					products,
					overlap.At(k, tm, down),
					overlap.At(k, tm, j),
					module.SmulMul.Read(vectors).AsFact().At(
						a.TermAs[A]("laurent_monomial(t, i - j)"), a.TermAs[A]("laurent_monomial(t, j)"), v)))
			a.Do(SplitConj(
				Case(
					"fst(M), a k[t]-module, takes tⁱ · v to t^(j−i) · (tⁱ · v)",
					Derive(func(b *Argument) {
						inChart := b.Assume()
						b.Show(
							"a multiple of a member of fst(M) by a member of k[t]",
							splitUp.Rw(),
							By(raise, inChart, submodule.SubmoduleSmul.Read(sub0), module_record.RestrictRingDef))
					})),
				Case(
					"snd(M), a k[1/t]-module, takes tʲ · v to t^(i−j) · (tʲ · v)",
					Derive(func(b *Argument) {
						inChart := b.Assume()
						b.Show(
							"a multiple of a member of snd(M) by a member of k[1/t]",
							splitDown.Rw(),
							By(lower, inChart, submodule.SubmoduleSmul.Read(sub1), module_record.RestrictRingDef))
					})),
			))
		}),
})}

// LinePairInvertible — for t a nonzero member of the field, every O(n) is
// an invertible lattice pair on the line. Chart 0 is the ring k[t],
// invertible as a fractional ideal of itself; chart 1 is tⁿ · k[1/t], a
// nonzero multiple of the ring k[1/t] and so a principal fractional ideal
// of it. Over the overlap both charts span the overlap: k[t] holds one,
// and tⁿ · k[1/t] holds tⁿ, a unit of the overlap with inverse t⁻ⁿ.
var LinePairInvertible = linePairInvertibleThm{family.Add(registry.ProofEntry{
	Name: "LinePairInvertible",
	Key:  "prop_88fe8d30d3c65bc0",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀t:A. ∀n:int.",
		Hypotheses: []string{
			"subfield(L, k)",
			"t ∈ L.carrier",
			"t ≠ L.zero",
		},
		Conclusion: "invertible_lattice_pair(field_ring(L), " +
			"    «plChart0», " +
			"    «plChart1», " +
			"    «plOverlap», " +
			"    «plPairN»)",
	},
		func(a *Argument, L field.FieldFact[on.L], k *Expr[Set[A]], t *Expr[A], n *Expr[Int], given Fact) {
			hyp := a.Conjuncts(
				given,
				"k is a subfield of L",
				"t lies in L",
				"t is not zero")
			tm := a.MemberOf[on.L](t, hyp[1])
			ring := field.RingOn.Read(L)
			overlap, chart0, chart1 :=
				a.TermAs[Set[A]]("«plOverlap»"), a.TermAs[Set[A]]("«plChart0»"), a.TermAs[Set[A]]("«plChart1»")
			scaled := a.TermAs[Set[A]]("«plChart1N»")
			minusN := a.TermAs[Int]("-n")
			tn, tMinusN := a.TermAs[A]("laurent_monomial(t, n)"), a.TermAs[A]("laurent_monomial(t, -n)")

			// The line's datum: the two charts are subrings of L inside the overlap, itself a subring of L.
			datum := a.Simplified(GroupPremises(hyp[0], hyp[2], LineDatum.Read(L).At(k, tm)))
			overlapSubring := a.Have(
				"the overlap is a subring of L",
				"subring(field_ring(L), «plOverlap»)",
				By(datum))
			chart0Subring := a.Have(
				"so is k[t]",
				"subring(field_ring(L), «plChart0»)",
				By(datum))
			chart1Subring := a.Have(
				"and so is k[1/t]",
				"subring(field_ring(L), «plChart1»)",
				By(datum))
			chart1InOverlap := a.Have(
				"k[1/t] lies in the overlap",
				"«plChart1» ⊆ «plOverlap»",
				By(datum))

			// tⁿ and t⁻ⁿ lie in the overlap and are inverse to each other.
			power := a.Have(
				"tⁿ lies in the overlap",
				"laurent_monomial(t, n) ∈ «plOverlap»",
				By(given, laurent_polynomial.LaurentMonomialInRing.Read(L).At(k, tm, n)))
			inversePower := a.Have(
				"and so does t⁻ⁿ",
				"laurent_monomial(t, -n) ∈ «plOverlap»",
				By(given, laurent_polynomial.LaurentMonomialInRing.Read(L).At(k, tm, minusN)))
			powers := a.Conjuncts(
				GroupPremises(hyp[2], laurent_polynomial.LaurentMonomialProduct.Read(L).At(tm)),
				"t⁰ = one",
				"t¹ = t",
				"t⁻¹ = inv(t)",
				"the powers of t are nonzero members of L, multiplying by adding exponents")[3]
			powerInL := a.Have(
				"so tⁿ lies in L",
				"laurent_monomial(t, n) ∈ L.carrier",
				By(powers.At(n, n)))
			pm := a.MemberOf[on.L](tn, powerInL)
			unit := a.Have(
				"tⁿ · t⁻ⁿ = t⁰ = one",
				"laurent_monomial(t, n) * laurent_monomial(t, -n) = L.one",
				By(hyp[2], laurent_polynomial.LaurentMonomialInverse.Read(L).At(tm, n)))

			// The charts of O(n) are invertible fractional ideals of their rings.
			first := a.Have(
				"k[t] is an invertible fractional ideal of itself",
				"invertible_fractional(field_ring(L), «plChart0», «plChart0»)",
				By(chart0Subring, fractional_ideal.SubringInvertible.Read(L).At(chart0)))
			second := a.Have(
				"tⁿ · k[1/t], a nonzero multiple of k[1/t], is an invertible fractional ideal of k[1/t]",
				"invertible_fractional(field_ring(L), «plChart1», «plChart1N»)",
				By(
					chart1Subring,
					comm_ring.SubringSubset.Read(chart1Subring),
					powers.At(n, n),
					fractional_ideal.InvertibleScale.Read(L).At(chart1, chart1, pm)))

			// Over the overlap both charts span the overlap: k[t] holds one, tⁿ · k[1/t] holds the unit tⁿ.
			module := a.Have(
				"L is a module over the overlap",
				"module_on(«plRing», «plField»)",
				By(datum))
			span0 := a.Have(
				"k[t], inside the overlap and holding one, spans the overlap",
				"module_span(«plRing», «plField», «plChart0») = «plOverlap»",
				By(
					overlapSubring,
					datum,
					comm_ring.SubringOne.Read(chart0Subring),
					fractional_ideal.SpanHoldingOne.Read(L).At(overlap, chart0)))
			byPower := a.TermAs[Fun[A, A]]("L.mul(laurent_monomial(t, n))")
			multiples := a.Have(
				"tⁿ · q lies in the overlap for each q in k[1/t]: "+
					"the overlap holds both and is closed under products",
				"∀q:A. q ∈ «plChart1» ⇒ laurent_monomial(t, n) * q ∈ «plOverlap»",
				By(
					power,
					a.Unfolded(chart1InOverlap, set_basic.SubsetDef),
					comm_ring.SubringMul.Read(overlapSubring)))
			powerInScaled := a.Have(
				"tⁿ = tⁿ · one lies in tⁿ · k[1/t]",
				"laurent_monomial(t, n) ∈ «plChart1N»",
				By(
					comm_ring.SubringOne.Read(chart1Subring),
					comm_monoid.RightIdentityOn.Read(comm_ring.MulMonoidOn.Read(ring)).At(pm),
					set_image.FunInImage.At(byPower, chart1, a.TermAs[A]("L.one"))))
			span1 := a.Have(
				"tⁿ · k[1/t], inside the overlap and holding the unit tⁿ, spans the overlap",
				"module_span(«plRing», «plField», «plChart1N») = «plOverlap»",
				By(
					overlapSubring,
					multiples,
					set_image.ImageSubsetIff.At(byPower, chart1, overlap),
					powerInScaled,
					inversePower,
					unit,
					fractional_ideal.SpanHoldingUnit.Read(L).At(overlap, scaled, tn, tMinusN)))

			// So O(n) is a lattice pair over the overlap, each chart a submodule over its own ring.
			chart0Submodule := a.Have(
				"k[t] is a k[t]-submodule of L",
				"submodule(restrict_ring(field_ring(L), «plChart0»), «plField», «plChart0»)",
				By(a.Unfolded(first, fractional_ideal.InvertibleFractionalDef)))
			chart1Submodule := a.Have(
				"tⁿ · k[1/t] is a k[1/t]-submodule of L",
				"submodule(restrict_ring(field_ring(L), «plChart1»), «plField», «plChart1N»)",
				By(a.Unfolded(second, fractional_ideal.InvertibleFractionalDef)))
			lattice := a.Have(
				"O(n) is a lattice pair over the overlap",
				"lattice_pair(«plRing», «plChart0», «plChart1», «plField», «plPairN»)",
				Unfold(lattice_pair.LatticePairDef),
				Unfold(ProjectiveLinePairDef),
				Unfold(module_record.RestrictRingDef),
				By(module, chart0Submodule, chart1Submodule, span0, span1, pairs.Fst, pairs.Snd))
			a.Show(
				"each chart of O(n) is invertible over its ring, and O(n) is a lattice pair",
				Unfold(invertible_lattice_pair.InvertibleLatticePairDef),
				Unfold(ProjectiveLinePairDef),
				By(first, second, lattice, pairs.Fst, pairs.Snd))
		}),
})}

// LinePairIsLattice — for t a nonzero member of the field, every O(n) is
// a lattice pair on the line: it is an invertible one (LinePairInvertible).
var LinePairIsLattice = linePairIsLatticeThm{family.Add(registry.ProofEntry{
	Name: "LinePairIsLattice",
	Key:  "prop_6ecba603d02b236f",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀t:A. ∀n:int.",
		Hypotheses: []string{
			"subfield(L, k)",
			"t ∈ L.carrier",
			"t ≠ L.zero",
		},
		Conclusion: "lattice_pair(«plRing», «plChart0», «plChart1», «plField», «plPairN»)",
	},
		func(a *Argument, L field.FieldFact[on.L], k *Expr[Set[A]], t *Expr[A], n *Expr[Int], h Fact) {
			hyp := a.Conjuncts(
				h,
				"k is a subfield of L",
				"t lies in L",
				"t is not zero")
			tm := a.MemberOf[on.L](t, hyp[1])
			a.Show(
				"an invertible lattice pair is a lattice pair",
				By(
					hyp[0],
					hyp[2],
					LinePairInvertible.Read(L).At(k, tm, n),
					invertible_lattice_pair.InvertibleLatticePairDef))
		}),
})}

// LineGlobalSections — the functions regular on both charts are the
// constants: for t transcendental, k[t] ∩ k[1/t] = k. Both charts hold k,
// and a common member has coefficients only at t⁰, so it is its constant
// coefficient, which lies in k.
var LineGlobalSections = lineGlobalSectionsThm{family.Add(registry.ProofEntry{
	Name: "LineGlobalSections",
	Key:  "prop_8ad421706facca70",
	Reading: "Transcendence is load-bearing: for t algebraic " +
		"over k, k[t] = k[1/t] = k(t), larger than k as soon as t ∉ k.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀t:A.",
		Hypotheses: []string{
			"subfield(L, k)",
			"t ∈ L.carrier",
			"¬algebraic_over(L, k, t)",
		},
		Conclusion: "«plChart0» ∩ «plChart1» = k",
	},
		func(a *Argument, L field.FieldFact[on.L], k *Expr[Set[A]], t *Expr[A], h Fact) {
			given := a.Conjuncts(
				h,
				"k is a subfield of L",
				"t lies in L",
				"t is transcendental over k")
			subK, tInL, transcendental := given[0], given[1], given[2]
			tm := a.MemberOf[on.L](t, tInL)
			ring := field.RingOn.Read(L)
			nonzero := a.Have(
				"t, transcendental over k, is not zero",
				"t ≠ L.zero",
				By(subK, transcendental, algebraic_element.TranscendentalInverse.Read(L).At(k, tm)))
			zeroExponent := a.TermAs[Int]("&0")

			// Both charts hold k.
			kInCharts := a.Have(
				"k lies in k[t] and in k[1/t], the rings it generates with t and with inv(t)",
				"k ⊆ «plChart0» ∧ k ⊆ «plChart1»",
				By(
					subK,
					algebraic_element.PolynomialImageRing.Read(L).At(k, tm),
					algebraic_element.PolynomialImageRing.Read(L).At(k, field.InvIn.Read(L).At(tm))))

			// A common member of the charts has no coefficient at a negative and
			// none at a positive power, so it is its coefficient at t⁰.
			polynomials, inversePolynomials := a.TermAs[Set[A]]("«plChart0»"), a.TermAs[Set[A]]("«plChart1»")
			meet := a.TermAs[Set[A]]("«plChart0» ∩ «plChart1»")
			constants := a.Have(
				"a common member of the charts lies in k",
				"«plChart0» ∩ «plChart1» ⊆ k",
				Simp(Fwd(set_basic.SubsetDef)),
				Derive(func(b *Argument) {
					z := b.FixAs[A]("z")
					inBoth := b.Assume()
					parts := b.Conjuncts(
						b.Have(
							"read off the charts by their coefficients (LineChartCoefficients): "+
								"z lies in k[t, 1/t], with no negative and no positive power",
							"z ∈ «plOverlap» ∧ "+
								"(∀i:int. i < &0 ⇒ laurent_polynomial_coefficient(k, t, z, i) = L.zero) ∧ "+
								"(∀i:int. &0 < i ⇒ laurent_polynomial_coefficient(k, t, z, i) = L.zero)",
							BySets(inBoth, subK, transcendental, LineChartCoefficients.Read(L).At(k, tm, z))),
						"z lies in the overlap",
						"z has no negative power",
						"z has no positive power")
					// The singleton {0} is spelled {int_of_num(0)}: an int set literal is
					// not typed by its ⊆ partner, and {&0} would read as a set of reals.
					support := b.Have(
						"so the support of its coefficients lies in {0}: an index there is neither negative nor positive",
						"fun_support(L.zero, λi:int. laurent_polynomial_coefficient(k, t, z, i)) ⊆ {int_of_num(0)}",
						Simp(Fwd(set_basic.SubsetDef)),
						b.ForEach(func(i *Expr[Int]) Action {
							return BySets(parts[1].At(i), parts[2].At(i), int_real_lift.LessThanTrichotomy.At(i, zeroExponent))
						}))
					inK := b.Have(
						"its coefficients lie in k",
						"∀i:int. laurent_polynomial_coefficient(k, t, z, i) ∈ k",
						By(subK, nonzero, parts[0], laurent_polynomial.LaurentExpansion.Read(L).At(k, tm, z)))
					coefficient := b.TermAs[Fun[Int, A]]("λi:int. laurent_polynomial_coefficient(k, t, z, i)")
					terms := b.Have(
						"its terms lie in L",
						"∀j:int. laurent_polynomial_coefficient(k, t, z, j) * laurent_monomial(t, j) ∈ L.carrier",
						b.ForEach(func(j *Expr[Int]) Action {
							return By(
								subK,
								nonzero,
								inK,
								laurent_polynomial.LaurentTermsInField.Read(L).At(k, tm, coefficient, j))
						}))
					single := b.TermAs[Set[Int]]("{int_of_num(0)}")
					term := b.TermAs[Fun[Int, A]](
						"λi:int. laurent_polynomial_coefficient(k, t, z, i) * laurent_monomial(t, i)")
					inSingle := b.Have(
						"0 lies in {0}",
						"int_of_num(0) ∈ {int_of_num(0)}",
						BySets())
					others := b.Have(
						"and {0} has no other index",
						Statement{
							Binders: "∀y:int.",
							Hypotheses: []string{
								"y ∈ {int_of_num(0)}",
								"y ≠ &0",
							},
							Conclusion: "laurent_polynomial_coefficient(k, t, z, y) * laurent_monomial(t, y) = L.zero",
						},
						BySets())
					c0 := b.MemberOf[on.L](b.TermAs[A]("laurent_polynomial_coefficient(k, t, z, &0)"),
						b.Have(
							"the coefficient at t⁰ lies in L, as k does",
							"laurent_polynomial_coefficient(k, t, z, &0) ∈ L.carrier",
							BySets(inK.At(zeroExponent), field.SubfieldSubset.Read(subK))))
					value := b.Have(
						"z is its coefficient at t⁰",
						"z = laurent_polynomial_coefficient(k, t, z, &0)",
						CalcEq(
							Leg(
								b.TermAs[A](
									"module_sum(L.add, "+
										"    L.zero, "+
										"    {int_of_num(0)}, "+
										"    λi:int. laurent_polynomial_coefficient(k, t, z, i) * laurent_monomial(t, i))"),
								"z is the sum of its terms over {0}, which holds their support",
								By(
									subK,
									nonzero,
									parts[0],
									support,
									finite_set.FiniteSing.At(zeroExponent),
									laurent_polynomial.LaurentExpansionOver.Read(L).At(k, tm, single, z))),
							Leg(
								b.TermAs[A]("laurent_polynomial_coefficient(k, t, z, &0) * laurent_monomial(t, &0)"),
								"a sum over {0} is its one term",
								By(
									terms,
									inSingle,
									others,
									finite_set.FiniteSing.At(zeroExponent),
									module.ModuleSumSingle.Read(module.RegularModuleOn.Read(ring)).At(single, zeroExponent, term))),
							Leg(
								b.TermAs[A]("laurent_polynomial_coefficient(k, t, z, &0) * L.one"),
								"t⁰ is one",
								By(nonzero, laurent_polynomial.LaurentMonomialProduct.Read(L).At(tm))),
							FinalLeg(
								"one is the unit of the product",
								By(comm_monoid.RightIdentityOn.Read(comm_ring.MulMonoidOn.Read(ring)).At(c0))),
						))
					b.Show(
						"so z, its coefficient at t⁰, lies in k",
						By(Normalized, value, inK.At(zeroExponent)))
				}))
			a.Show(
				"k lies in both charts, so in their meet, and the meet lies in k",
				By(
					constants,
					kInCharts,
					set_order.SubsetInter.At(k, polynomials, inversePolynomials),
					set_order.SubsetAntisym.At(meet, k)))
		}),
})}

// LineNegativeSectionsVanish — H⁰(O(−n)) = 0 for n > 0: a member f of k[t] that
// is t^(−n)·g for some g in k[1/t] is zero. Being t^(−n)·g, f lies in k[1/t] as
// well, so in k (LineGlobalSections); and t·f = h with h = t^(1−n)·g, which n
// being positive puts in k[1/t], lies in k[t] and k[1/t] too, so in k. Were f
// not zero, t would be (t·f)·(1/f), a member of k, against its transcendence.
// LineIntersectionBasis gives the same vanishing as the empty basis of
// H⁰(O(n)) for n < 0, but reading it here would first carry f through the
// integer-indexed charts of the pair O(n), longer than this argument.
var LineNegativeSectionsVanish = lineNegativeSectionsVanishThm{family.Add(registry.ProofEntry{
	Name: "LineNegativeSectionsVanish",
	Key:  "prop_2cac83826c583b7e",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀t f g:A. ∀n:num.",
		Hypotheses: []string{
			"subfield(L, k)",
			"t ∈ L.carrier",
			"¬algebraic_over(L, k, t)",
			"0 < n",
			"f ∈ «plChart0»",
			"g ∈ «plChart1»",
			"f = monoid_pow(L.mul, L.one, L.inv(t), n) * g",
		},
		Conclusion: "f = L.zero",
		Abbrev: Abbrev{
			{Name: "h", Text: "monoid_pow(L.mul, L.one, L.inv(t), n - 1) * g"},
		},
	}, func(
		a *Argument,
		L field.FieldFact[on.L],
		k *Expr[Set[A]],
		t, f, g *Expr[A],
		n *Expr[Nat],
		subK, tIn, transcendental, positive, fIn, gIn, scaled Fact,
	) {
		ring := field.RingOn.Read(L)
		tm := a.MemberOf[on.L](t, tIn)
		um := field.InvIn.Read(L).At(tm)
		h := a.TermAs[A]("«h»")
		inverse := a.Conjuncts(
			a.Have(
				"t, transcendental over k, is not zero, and t · 1/t = one",
				"t ≠ L.zero ∧ t * L.inv(t) = L.one",
				By(
					subK,
					tIn,
					transcendental,
					algebraic_element.TranscendentalInverse.Read(L).At(k, tm),
					field.MulRightInverseOn.Read(L))),
			"t is not zero",
			"t · 1/t = one")
		unit := inverse[1]
		lines := a.Have(
			"k[t] and k[1/t] are subrings of L holding t and 1/t",
			"subring(field_ring(L), «plChart0») ∧ "+
				"t ∈ «plChart0» ∧ "+
				"subring(field_ring(L), «plChart1») ∧ "+
				"L.inv(t) ∈ «plChart1»",
			By(
				subK,
				algebraic_element.PolynomialImageRing.Read(L).At(k, tm),
				algebraic_element.PolynomialImageRing.Read(L).At(k, um)))
		ring1 := a.Have(
			"k[1/t] is a ring under L's operations",
			"comm_ring_on(«plRing1»)",
			By(lines, comm_ring.SubringRingOn.Read(ring)))
		powers1 := comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(ring1))
		fIn1 := a.Have(
			"f, being t^(−n)·g, lies in k[1/t] as well",
			"f ∈ «plChart1»",
			By(scaled, lines, gIn, powers1, comm_ring.MulIn.Read(ring1)))
		fInK := a.Have(
			"so f lies in k",
			"f ∈ k",
			BySets(fIn1, fIn, subK, transcendental, LineGlobalSections.Read(L).At(k, tm)))
		hIn := a.Have(
			"h = t^(1−n)·g lies in k[1/t]",
			"«h» ∈ «plChart1»",
			By(lines, gIn, powers1, comm_ring.MulIn.Read(ring1)))
		predecessor := a.Have(
			"n is the successor of n − 1, being positive",
			"suc(n - 1) = n",
			ByArith(positive))
		peel := a.Have(
			"so t^(−n) = t^(−1)·t^(1−n)",
			"monoid_pow(L.mul, L.one, L.inv(t), n) = L.inv(t) * monoid_pow(L.mul, L.one, L.inv(t), n - 1)",
			By(predecessor, comm_monoid.MonoidPowDef))
		inField := a.Have(
			"f and g lie in L",
			"g ∈ L.carrier ∧ f ∈ L.carrier",
			By(lines, gIn, fIn, comm_ring.SubringSubset, set_basic.SubsetDef))
		fm := a.MemberOf[on.L](f, a.Conjuncts(
			inField,
			"g lies in L",
			"f lies in L")[1])
		cleared := a.Have(
			"t·f = h",
			"t * f = «h»",
			ByArith(
				L,
				Scaled(t, scaled),
				Scaled(a.TermAs[A]("t * g"), peel),
				Scaled(h, unit),
				inField,
				tIn,
				um))
		tfInK := a.Have(
			"t·f, being h, lies in k[1/t], and in k[t] as a multiple of f, so in k",
			"t * f ∈ k",
			BySets(
				cleared,
				lines,
				fIn,
				hIn,
				comm_ring.SubringMul,
				subK,
				transcendental,
				LineGlobalSections.Read(L).At(k, tm)))
		nonzero := a.SupposeNot()
		solved := a.Have(
			"were f not zero, t would be (t·f)·(1/f)",
			"t = (t * f) * L.inv(f)",
			ByArith(
				L,
				tIn,
				inField,
				nonzero,
				Scaled(t, field.MulRightInverseOn.Read(L).At(fm)),
				field.InvIn.Read(L).At(fm)))
		a.Show(
			"a member of k, which t, being transcendental, is not",
			By(
				solved,
				tfInK,
				fInK,
				subK,
				transcendental,
				field.SubfieldMul,
				field.SubfieldInv,
				algebraic_element.MemberAlgebraic.Read(L).At(k, t)))
	}),
})}

// LineIntersectionBasis — H⁰(O(n)) = k[t] ∩ tⁿ · k[1/t] has the powers
// t⁰, …, tⁿ as a basis over k: the polynomials of degree at most n. The
// powers lie in both charts and are independent, being powers of a
// transcendental t; a member of both charts has no coefficient below 0
// or above n, so it is the k-combination of t⁰, …, tⁿ its expansion
// gives.
var LineIntersectionBasis = lineIntersectionBasisThm{family.Add(registry.ProofEntry{
	Name: "LineIntersectionBasis",
	Key:  "prop_33758a5f94245c4",
	Reading: "For n < 0 the index set is empty and H⁰(O(n)) is the zero " +
		"module, of which ∅ is a basis. The injectivity turns the basis into " +
		"a count; it needs t not a root of unity, which transcendence gives.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀t:A. ∀n:int.",
		Hypotheses: []string{
			"subfield(L, k)",
			"t ∈ L.carrier",
			"¬algebraic_over(L, k, t)",
		},
		Conclusion: "module_basis(«plScalars», " +
			"    lattice_pair_h0(«plField», «plPairN»), " +
			"    {laurent_monomial(t, i) | i:int | &0 ≤ i ∧ i ≤ n}) ∧ " +
			"injective_on({i:int | &0 ≤ i ∧ i ≤ n}, λi:int. laurent_monomial(t, i))",
		Abbrev: Abbrev{
			{Name: "plChartsMeetN", Text: "«plChart0» ∩ «plChart1N»"},
			{Name: "plSpanUpToN", Text: "module_span(«plRingK», «plField», «plPowersUpToN»)"},
		},
	},
		func(a *Argument, L field.FieldFact[on.L], k *Expr[Set[A]], t *Expr[A], n *Expr[Int], h Fact) {
			given := a.Conjuncts(
				h,
				"k is a subfield of L",
				"t lies in L",
				"t is transcendental over k")
			kSub, tIn := given[0], given[1]
			tm := a.MemberOf[on.L](t, tIn)
			nonzero := a.Have(
				"t, transcendental, is not zero",
				"t ≠ L.zero",
				By(h, algebraic_element.TranscendentalInverse.Read(L).At(k, tm)))
			mul, one, inv := a.TermAs[Op[A]]("L.mul"), a.TermAs[A]("L.one"), a.TermAs[Fun[A, A]]("L.inv")

			// The line's datum: k[t] is a ring inside L holding t, and k[1/t] a
			// ring holding inv(t); so each holds the powers of its generator.
			chart0, chart1 := a.TermAs[Set[A]]("«plChart0»"), a.TermAs[Set[A]]("«plChart1»")
			datum := a.Simplified(GroupPremises(given[0], nonzero, LineDatum.Read(L).At(k, tm)))
			subrings := comm_ring.SubringRingOn.Read(field.RingOn.Read(L))
			subring0 := a.Have(
				"k[t] is a subring of L",
				"subring(field_ring(L), «plChart0»)",
				By(datum))
			ring0 := a.Have(
				"so a ring",
				"comm_ring_on(restrict_ring(field_ring(L), «plChart0»))",
				By(subring0, subrings.At(chart0)))
			ring1 := a.Have(
				"and so is k[1/t]",
				"comm_ring_on(restrict_ring(field_ring(L), «plChart1»))",
				By(datum, subrings.At(chart1)))
			chart0InL := a.Have(
				"k[t] lies in L",
				"«plChart0» ⊆ L.carrier",
				By(comm_ring.SubringSubset.Read(subring0)))
			powers0 := a.Have(
				"every power of t lies in k[t]",
				"∀m:num. monoid_pow(L.mul, L.one, t, m) ∈ «plChart0»",
				a.ForEach(func(m *Expr[Nat]) Action {
					return By(datum, comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(ring0)))
				}))
			powers1 := a.Have(
				"every power of inv(t) lies in k[1/t]",
				"∀m:num. monoid_pow(L.mul, L.one, L.inv(t), m) ∈ «plChart1»",
				a.ForEach(func(m *Expr[Nat]) Action {
					return By(datum, comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(ring1)))
				}))
			power := a.Have(
				"at an exponent i ≥ 0, tⁱ is the i-th power of t",
				"∀i:int. &0 ≤ i ⇒ laurent_monomial(t, i) = monoid_pow(L.mul, L.one, t, num_of_int(i))",
				a.ForEach(func(i *Expr[Int]) Action {
					return By(laurent_polynomial.LaurentMonomialDef.At(mul, one, inv, t, i))
				}))

			// tⁱ for 0 ≤ i ≤ n lies in k[t], and is tⁿ times t^(i − n), a power
			// of inv(t).
			monomials := a.Have(
				"each tⁱ with 0 ≤ i ≤ n lies in k[t] and in tⁿ · k[1/t]",
				Statement{
					Binders: "∀i:int.",
					Hypotheses: []string{
						"&0 ≤ i",
						"i ≤ n",
					},
					Conclusion: "laurent_monomial(t, i) ∈ «plChart0» ∧ laurent_monomial(t, i) ∈ «plChart1N»",
				},
				Derive(func(b *Argument) {
					i := b.FixAs[Int]("i")
					bounds := b.Assume()
					gap := b.Have(
						"n − i is not negative",
						"&0 ≤ n - i",
						ByArith(bounds))
					exponents := b.Have(
						"so n − i is the natural number num_of_int(n − i), and n − (n − i) = i",
						"n + -&(num_of_int(n - i)) = i",
						ByArith(gap, int_embed.NumOfIntSection.At(b.TermAs[Int]("n - i"))))
					m := b.TermAs[Nat]("num_of_int(n - i)")
					product := b.Have(
						"tⁿ · t^(i − n) = tⁱ",
						"laurent_monomial(t, n) * laurent_monomial(t, -&(num_of_int(n - i))) = laurent_monomial(t, i)",
						By(exponents, nonzero, laurent_polynomial.LaurentMonomialProduct.Read(L).At(tm)))
					b.Show(
						"tⁱ is a power of t, and tⁿ times a member of k[1/t]",
						By(
							bounds,
							power.At(i),
							powers0.At(b.TermAs[Nat]("num_of_int(i)")),
							product,
							laurent_polynomial.LaurentMonomialOfNum.At(mul, one, inv, t, m),
							powers1.At(m),
							set_image.FunInImage.At(b.TermAs[Fun[A, A]]("L.mul(laurent_monomial(t, n))"), chart1,
								b.TermAs[A]("laurent_monomial(t, -&(num_of_int(n - i)))"))))
				}))

			// H⁰(O(n)) = k[t] ∩ tⁿ · k[1/t] is a k-subspace of L: O(n) is a
			// lattice pair, and k lies in both chart rings.
			scalars := a.TermAs[module_record.RingOps[A]]("«plRingK»")
			vectors := a.TermAs[ModuleOps[A, A]]("«plField»")
			vectorSpace := a.Have(
				"L is a vector space over k",
				"module_on(«plRingK», «plField»)",
				By(
					datum,
					module_record.RestrictRingDef.At(a.TermAs[module_record.RingOps[A]]("«plRing»"), k),
					module_record.RestrictRingDef.At(a.TermAs[module_record.RingOps[A]]("field_ring(L)"), k)))
			lattice := a.Have(
				"O(n) is a lattice pair on the line",
				"lattice_pair(«plRing», «plChart0», «plChart1», «plField», «plPairN»)",
				By(kSub, tIn, nonzero, LinePairIsLattice.Read(L).At(k, tm, n)))
			kInCharts := a.Have(
				"k lies in k[t] and in k[1/t]",
				"k ⊆ «plChart0» ∧ k ⊆ «plChart1»",
				By(datum))
			section := a.TermAs[Set[A]]("«plChartsMeetN»")
			h0 := a.Have(
				"so H⁰(O(n)) is a k-subspace of L",
				"submodule(«plScalars», «plField», «plSectionsN»)",
				By(
					lattice,
					kInCharts,
					lattice_pair.H0Submodule.At(
						a.TermAs[module_record.RingOps[A]]("«plRing»"),
						chart0,
						chart1,
						k,
						vectors,
						a.TermAs[Prod[Set[A], Set[A]]]("«plPairN»"))))
			// Read at k's own ring and at the charts of O(n) themselves, H⁰(O(n)) is k[t] ∩ tⁿ · k[1/t].
			sectionSub := a.Have(
				"so k[t] ∩ tⁿ · k[1/t] is a k-subspace of L",
				"submodule(«plRingK», «plField», «plChartsMeetN»)",
				By(
					a.Simplified(h0, Fwd(ProjectiveLinePairDef), Fwd(pairs.Fst), Fwd(pairs.Snd)),
					module_record.RestrictRingDef.At(a.TermAs[module_record.RingOps[A]]("«plRing»"), k),
					module_record.RestrictRingDef.At(a.TermAs[module_record.RingOps[A]]("field_ring(L)"), k)))
			sectionInL := a.Have(
				"it lies in L",
				"«plChartsMeetN» ⊆ L.carrier",
				BySets(chart0InL))

			// t⁰, …, tⁿ lie in H⁰ and are independent over k, being distinct
			// powers of the transcendental t.
			basisSet := a.TermAs[Set[A]]("«plPowersUpToN»")
			inSection := a.Have(
				"t⁰, …, tⁿ lie in k[t] ∩ tⁿ · k[1/t]",
				"«plPowersUpToN» ⊆ «plChartsMeetN»",
				Simp(Fwd(set_image.SimpleImageGen), Fwd(set_image.ImageSubsetIff), Fwd(set_basic.InInter)),
				By(monomials))
			inField := a.Have(
				"so they lie in L",
				"«plPowersUpToN» ⊆ L.carrier",
				BySets(inSection, chart0InL))
			ofPowers := a.Have(
				"t⁰, …, tⁿ are powers of t",
				"«plPowersUpToN» ⊆ monoid_powers(L.mul, L.one, t)",
				BySets(power, comm_monoid.MonoidPowersDef))
			transcendental := a.Conjuncts(
				a.Have(
					"the powers of t are distinct and independent over k",
					"(∀i j:num. monoid_pow(L.mul, L.one, t, i) = monoid_pow(L.mul, L.one, t, j) ⇒ i = j) ∧ "+
						"module_independent(«plRingK», «plField», monoid_powers(L.mul, L.one, t))",
					By(h, algebraic_element.TranscendentalPowersIndependent.Read(L).At(k, tm))),
				"distinct exponents give distinct powers of t",
				"the powers of t are independent over k")
			independent := a.Have(
				"so t⁰, …, tⁿ are independent over k",
				"module_independent(«plRingK», «plField», «plPowersUpToN»)",
				By(
					ofPowers,
					transcendental[1],
					linear_independence.IndependentSubset.At(
						scalars, vectors, a.TermAs[Set[A]]("monoid_powers(L.mul, L.one, t)"), basisSet)))

			// Their span is H⁰: it lies in the subspace H⁰, and a member of H⁰ is
			// the combination of t⁰, …, tⁿ its expansion gives.
			exponents := a.TermAs[Set[Int]]("«plExponentsUpToN»")
			powerOf := a.TermAs[Fun[Int, A]]("λi:int. laurent_monomial(t, i)")
			asImage := a.Have(
				"t⁰, …, tⁿ are the image of 0, …, n under i ↦ tⁱ",
				"«plPowersUpToN» = image(λi:int. laurent_monomial(t, i), «plExponentsUpToN»)",
				By(set_image.SimpleImageGen.At(powerOf, a.TermAs[Set[Int]]("λi:int. &0 ≤ i ∧ i ≤ n"))))
			span := a.TermAs[Set[A]]("«plSpanUpToN»")
			spanSub := a.Have(
				"the span of t⁰, …, tⁿ is a k-subspace of L",
				"submodule(«plRingK», «plField», «plSpanUpToN»)",
				By(vectorSpace, inField, submodule.SpanSubmodule.At(scalars, vectors, basisSet)))
			spanSpace := a.Have(
				"so a vector space over k",
				"module_on(«plRingK», restrict_module(«plField», «plSpanUpToN»))",
				By(vectorSpace, spanSub, submodule.SubmoduleModuleOn.At(scalars, vectors, span)))
			spanInSection := a.Have(
				"the span lies in the subspace k[t] ∩ tⁿ · k[1/t], which holds t⁰, …, tⁿ",
				"«plSpanUpToN» ⊆ «plChartsMeetN»",
				By(sectionSub, inSection, submodule.SpanLeast.At(scalars, vectors, basisSet, section)))
			sectionInSpan := a.Have(
				"every member of k[t] ∩ tⁿ · k[1/t] is a k-combination of t⁰, …, tⁿ",
				"«plChartsMeetN» ⊆ «plSpanUpToN»",
				Unfold(set_basic.SubsetDef),
				Derive(func(b *Argument) {
					f := b.FixAs[A]("f")
					fIn := b.Assume()
					charts := b.Simplified(
						GroupPremises(given[0], given[2], LinePairCoefficients.Read(L).At(k, tm, n, f)),
						Fwd(ProjectiveLinePairDef),
						Fwd(pairs.Fst),
						Fwd(pairs.Snd))
					vanish := b.Conjuncts(
						b.Have(
							"f lies in k[t, 1/t] with no coefficient below 0 or above n",
							"f ∈ «plOverlap» ∧ "+
								"(∀i:int. i < &0 ⇒ laurent_polynomial_coefficient(k, t, f, i) = L.zero) ∧ "+
								"(∀i:int. n < i ⇒ laurent_polynomial_coefficient(k, t, f, i) = L.zero)",
							BySets(fIn, charts)),
						"f lies in k[t, 1/t]",
						"no coefficient of f is below 0",
						"no coefficient of f is above n")
					expansion := b.Conjuncts(
						b.Have(
							"f is the finite sum of its terms, its coefficients lying in k",
							"finite(fun_support(L.zero, λi:int. laurent_polynomial_coefficient(k, t, f, i))) ∧ "+
								"(∀i:int. laurent_polynomial_coefficient(k, t, f, i) ∈ k) ∧ "+
								"f = «plOwnExpansion»",
							By(kSub, nonzero, vanish[0], laurent_polynomial.LaurentExpansion.Read(L).At(k, tm, f))),
						"f has finitely many nonzero coefficients",
						"every coefficient of f lies in k",
						"f is the sum of its terms")
					terms := b.Have(
						"each term of f on the support of its coefficients is "+
							"a multiple of one of t⁰, …, tⁿ, so lies in the span",
						Statement{
							Binders: "∀i:int.",
							Hypotheses: []string{
								"i ∈ fun_support(L.zero, λi:int. laurent_polynomial_coefficient(k, t, f, i))",
							},
							Conclusion: "laurent_polynomial_coefficient(k, t, f, i) * laurent_monomial(t, i) ∈ «plSpanUpToN»",
						},
						Derive(func(c *Argument) {
							i := c.FixAs[Int]("i")
							inSupport := c.Assume()
							outside := c.Have(
								"so i is neither below 0 nor above n",
								"¬(i < &0) ∧ ¬(n < i)",
								By(inSupport, vanish[1].At(i), vanish[2].At(i)))
							bounds := c.Have(
								"that is, 0 ≤ i ≤ n",
								"&0 ≤ i ∧ i ≤ n",
								ByArith(outside))
							inBasis := c.Have(
								"so tⁱ is one of t⁰, …, tⁿ",
								"laurent_monomial(t, i) ∈ «plPowersUpToN»",
								asImage.Rw(),
								By(bounds, set_image.FunInImage.At(powerOf, exponents, i)))
							inSpan := c.Have(
								"and lies in their span",
								"laurent_monomial(t, i) ∈ «plSpanUpToN»",
								BySets(inBasis, submodule.SubsetSpan.At(scalars, vectors, basisSet)))
							c.Show(
								"a multiple of it by a member of k stays in the span",
								By(
									inSpan,
									spanSub,
									expansion[1].At(i),
									submodule.SubmoduleSmul.At(scalars, vectors, span,
										c.TermAs[A]("laurent_polynomial_coefficient(k, t, f, i)"), c.TermAs[A]("laurent_monomial(t, i)"))))
						}))
					b.Show(
						"so f, the sum of its terms, lies in the span",
						By(
							terms,
							expansion[0],
							expansion[2],
							module.ModuleSumIn.Read(spanSpace).At(
								b.TermAs[Set[Int]]("fun_support(L.zero, λi:int. laurent_polynomial_coefficient(k, t, f, i))"),
								b.TermAs[Fun[Int, A]](
									"λi:int. laurent_polynomial_coefficient(k, t, f, i) * laurent_monomial(t, i)"))))
				}))
			spanned := a.Have(
				"so t⁰, …, tⁿ span k[t] ∩ tⁿ · k[1/t]",
				"«plSpanUpToN» = «plChartsMeetN»",
				By(spanInSection, sectionInSpan, set_order.SubsetAntisym.At(span, section)))
			basisK := a.Have(
				"t⁰, …, tⁿ are a basis of k[t] ∩ tⁿ · k[1/t] over k",
				"module_basis(«plRingK», restrict_module(«plField», «plChartsMeetN»), «plPowersUpToN»)",
				By(
					independent,
					inSection,
					sectionInL,
					spanned,
					sectionSub,
					vectorSpace,
					linear_independence.IndependentRestrict.At(scalars, vectors, section, basisSet),
					linear_independence.SpanRestrict.At(scalars, vectors, section, basisSet),
					linear_independence.ModuleBasisDef))
			basis := a.Have(
				"so they are a basis of H⁰(O(n)) = k[t] ∩ tⁿ · k[1/t] over k",
				"module_basis(«plScalars», lattice_pair_h0(«plField», «plPairN»), «plPowersUpToN»)",
				Unfold(lattice_pair.LatticePairH0Def),
				Unfold(ProjectiveLinePairDef),
				Simp(Fwd(pairs.Fst), Fwd(pairs.Snd)),
				By(
					basisK,
					module_record.RestrictRingDef.At(a.TermAs[module_record.RingOps[A]]("«plRing»"), k),
					module_record.RestrictRingDef.At(a.TermAs[module_record.RingOps[A]]("field_ring(L)"), k)))

			// Distinct exponents give distinct powers: tⁱ is the num_of_int(i)-th
			// power of t, and distinct powers of t have distinct exponents.
			distinct := a.Have(
				"tⁱ = tʲ for 0 ≤ i, j ≤ n forces i = j",
				Statement{
					Binders: "∀i j:int.",
					Hypotheses: []string{
						"&0 ≤ i ∧ i ≤ n",
						"&0 ≤ j ∧ j ≤ n",
						"laurent_monomial(t, i) = laurent_monomial(t, j)",
					},
					Conclusion: "i = j",
				},
				Derive(func(b *Argument) {
					i, j := b.FixAs[Int]("i"), b.FixAs[Int]("j")
					given := b.Conjuncts(
						b.Assume(),
						"i is not negative",
						"i is at most n",
						"j is not negative",
						"j is at most n",
						"tⁱ = tʲ")
					samePower := b.Have(
						"tⁱ and tʲ are the powers of t at num_of_int(i) and num_of_int(j)",
						"monoid_pow(L.mul, L.one, t, num_of_int(i)) = monoid_pow(L.mul, L.one, t, num_of_int(j))",
						GroupPremises(given[0], power.At(i)).RwRev(),
						GroupPremises(given[2], power.At(j)).RwRev(),
						By(given[4]))
					sameExponent := b.Have(
						"so the exponents agree",
						"num_of_int(i) = num_of_int(j)",
						By(samePower, transcendental[0].At(b.TermAs[Nat]("num_of_int(i)"), b.TermAs[Nat]("num_of_int(j)"))))
					b.Show(
						"and i, j, both nonnegative, are those exponents",
						ByArith(
							sameExponent,
							given[0],
							given[2],
							int_embed.NumOfIntSection.At(i),
							int_embed.NumOfIntSection.At(j)))
				}))
			injective := a.Have(
				"so i ↦ tⁱ is one-to-one on 0, …, n",
				"injective_on({i:int | &0 ≤ i ∧ i ≤ n}, λi:int. laurent_monomial(t, i))",
				Unfold(functions.InjectiveOnDef),
				By(distinct))
			a.Show(
				"t⁰, …, tⁿ are a basis of H⁰(O(n)), indexed injectively by 0, …, n",
				By(basis, injective))
		}),
})}

// LineQuotientBasis — H¹(O(n)) has the classes of tⁱ, n < i < 0, as a
// basis over k. The ambient of O(n) is the overlap, so H¹ is the overlap
// modulo W = k[t] + tⁿ · k[1/t], and the powers T = {tⁱ : n < i < 0}
// complement W in the overlap (module_dimension.QuotientComplementBasis).
// A member of W has no coefficient strictly between n and 0
// (LineChartSumCoefficients), while a k-combination of T has its own
// coefficients there: so such a combination lies in W only when its
// coefficients vanish, which makes T independent and its span meet W in
// zero alone. Every member of the
// overlap is a k-combination of powers of t, and a power outside the
// range lies in k[t] or in tⁿ · k[1/t]: so the overlap is span(T) + W.
var LineQuotientBasis = lineQuotientBasisThm{family.Add(registry.ProofEntry{
	Name: "LineQuotientBasis",
	Key:  "prop_3afb737bc73ee05a",
	Reading: "The class of a Laurent polynomial is read off its coefficients " +
		"strictly between n and 0, the ones every member of k[t] + tⁿ · k[1/t] lacks. " +
		"For n ≥ −1 there are none: the index set is empty and H¹(O(n)) is zero.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀t:A. ∀n:int.",
		Hypotheses: []string{
			"subfield(L, k)",
			"t ∈ L.carrier",
			"¬algebraic_over(L, k, t)",
		},
		Conclusion: "module_basis(«plScalars», " +
			"    lattice_pair_h1(«plRing», «plField», «plPairN»), " +
			"    {left_coset(L.add, laurent_monomial(t, i), «plChartSumN») | i:int | n < i ∧ i < &0}) ∧ " +
			"injective_on({i:int | n < i ∧ i < &0}, " +
			"    λi:int. left_coset(L.add, laurent_monomial(t, i), «plChartSumN»))",
		Abbrev: Abbrev{
			{Name: "plProjectionN", Text: "λu:A. left_coset(L.add, u, «plChartSumN»)"},
			{Name: "plPowersBelowN", Text: "{laurent_monomial(t, i) | i:int | n < i ∧ i < &0}"},
		},
	},
		func(a *Argument, L field.FieldFact[on.L], k *Expr[Set[A]], t *Expr[A], n *Expr[Int], h Fact) {
			parts := a.Conjuncts(
				h,
				"k is a subfield of L",
				"t lies in L",
				"t is transcendental over k")
			sub, tInL, transcendental := parts[0], parts[1], parts[2]
			tm := a.MemberOf[on.L](t, tInL)
			K := a.TermAs[module_record.RingOps[A]]("«plRingK»")
			V := a.TermAs[module_record.ModuleOps[A, A]]("«plField»")
			O := a.TermAs[Set[A]]("«plOverlap»")
			W := a.TermAs[Set[A]]("«plChartSumN»")
			first, second := a.TermAs[Set[A]]("fst(«plPairN»)"), a.TermAs[Set[A]]("snd(«plPairN»)")
			pair := a.TermAs[Prod[Set[A], Set[A]]]("«plPairN»")
			S := a.TermAs[Set[A]]("«plPowersBelowN»")
			spanS := a.TermAs[Set[A]]("module_span(«plRingK», «plField», «plPowersBelowN»)")

			// The line: t is not zero, the datum read at k's own ring, every power
			// of t in the overlap, and the coefficients of a power of t.
			nonzero := a.Have(
				"t, transcendental, is not zero",
				"t ≠ L.zero",
				By(h, algebraic_element.TranscendentalInverse.Read(L).At(k, tm)))
			datum := a.Simplified(GroupPremises(parts[0], nonzero, LineDatum.Read(L).At(k, tm)))
			// The overlap's ring read on k and the field's ring read on k: one ring, both being L's operations on k.
			overlapOnK, fieldOnK :=
				module_record.RestrictRingDef.At(a.TermAs[module_record.RingOps[A]]("«plRing»"), k),
				module_record.RestrictRingDef.At(a.TermAs[module_record.RingOps[A]]("field_ring(L)"), k)
			overK := a.Have(
				"L is a vector space over k",
				"module_on(«plRingK», «plField»)",
				By(datum, overlapOnK, fieldOnK))
			kInCharts := a.Have(
				"k lies in k[t] and in k[1/t]",
				"k ⊆ «plChart0» ∧ k ⊆ «plChart1»",
				By(datum))
			oSubring := a.Have(
				"the overlap is a subring of L",
				"subring(field_ring(L), «plOverlap»)",
				By(datum))
			kInL := a.Unfolded(a.Have(
				"k lies in L",
				"k ⊆ L.carrier",
				By(sub, field.SubfieldSubset)), set_basic.SubsetDef)
			powers := a.Have(
				"every power of t lies in the overlap",
				"∀i:int. laurent_monomial(t, i) ∈ «plOverlap»",
				a.ForEach(func(i *Expr[Int]) Action {
					return By(sub, nonzero, laurent_polynomial.LaurentMonomialInRing.Read(L).At(k, tm, i))
				}))
			coefficient := a.Have(
				"tʲ has coefficient one at tʲ and none at any other power",
				"∀i j:int. "+
					"    laurent_polynomial_coefficient(k, t, laurent_monomial(t, j), i) = COND(i = j, L.one, L.zero)",
				Derive(func(b *Argument) {
					i, j := b.FixAs[Int]("i"), b.FixAs[Int]("j")
					b.Show(
						"the expansion of tʲ is one · tʲ",
						By(h, laurent_polynomial.LaurentMonomialCoefficient.Read(L).At(k, tm, i, j)))
				}))

			// H¹(O(n)) is the overlap modulo W: the ambient of O(n) is the overlap,
			// and the overlap and W are k-subspaces of L, W inside the overlap.
			ambient := a.Have(
				"the ambient of O(n) is the overlap",
				"lattice_pair_ambient(«plRing», «plField», «plPairN») = «plOverlap»",
				By(sub, tInL, nonzero, LinePairAmbient.Read(L).At(k, tm, n)))
			lattice := a.Have(
				"O(n) is a lattice pair on the line",
				"lattice_pair(«plRing», «plChart0», «plChart1», «plField», «plPairN»)",
				By(sub, tInL, nonzero, LinePairIsLattice.Read(L).At(k, tm, n)))
			spaces := a.Conjuncts(
				a.Have(
					"over k the overlap and W are subspaces of L, W inside the overlap",
					"submodule(«plRingK», «plField», «plOverlap») ∧ "+
						"submodule(«plRingK», «plField», «plChartSumN») ∧ "+
						"«plChartSumN» ⊆ «plOverlap»",
					By(
						a.Simplified(
							GroupPremises(parts[0], nonzero, lattice, LineH1Module.Read(L).At(k, tm, V, pair)),
							Fwd(ambient)),
						overlapOnK,
						fieldOnK)),
				"the overlap is a k-subspace of L",
				"so is W",
				"W lies in the overlap")
			subO, subW, wInO := spaces[0], spaces[1], spaces[2]
			charts := a.Conjuncts(
				a.Unfolded(lattice, lattice_pair.LatticePairDef),
				"the field is a module over the overlap",
				"k[t] is a submodule over k[t]",
				"tⁿ · k[1/t] is a submodule over k[1/t]",
				"the two span the same")
			firstOverK := a.Have(
				"k[t] is a k-subspace of the field",
				"submodule(«plRingK», «plField», fst(«plPairN»))",
				By(kInCharts, submodule.SubmoduleRestrictScalars.Read(charts[1]).At(K)))
			secondOverK := a.Have(
				"and so is tⁿ · k[1/t]",
				"submodule(«plRingK», «plField», snd(«plPairN»))",
				By(kInCharts, submodule.SubmoduleRestrictScalars.Read(charts[2]).At(K)))
			h1 := a.Have(
				"so H¹(O(n)) is the overlap modulo W",
				"lattice_pair_h1(«plRing», «plField», «plPairN») = "+
					"quotient_module(restrict_module(«plField», «plOverlap»), «plChartSumN»)",
				Simp(Fwd(lattice_pair.LatticePairH1Def)),
				ambient.Rw(),
				Basic())

			// The coefficient test: a k-combination of T lying in W has zero
			// coefficients, as W has no coefficient strictly between n and 0.
			sInO := a.Have(
				"the powers tⁱ, n < i < 0, lie in the overlap",
				"«plPowersBelowN» ⊆ «plOverlap»",
				Simp(Fwd(set_image.SimpleImageGen), Fwd(set_image.ImageSubsetIff)),
				By(powers))
			sInL := a.Have(
				"and so in L",
				"«plPowersBelowN» ⊆ L.carrier",
				BySets(sInO, comm_ring.SubringSubset.Read(oSubring)))
			vanish := a.Have(
				"a k-combination of the powers tⁱ, n < i < 0, lying in W has zero coefficients",
				"∀T:set(A). ∀c:(A → A). "+
					"    finite(T) ∧ "+
					"    T ⊆ «plPowersBelowN» ∧ "+
					"    (∀x:A. x ∈ T ⇒ c(x) ∈ k) ∧ "+
					"    module_sum(L.add, L.zero, T, λx:A. c(x) * x) ∈ «plChartSumN» ⇒ "+
					"    ∀x:A. x ∈ T ⇒ c(x) = L.zero",
				Derive(func(b *Argument) {
					T, c := b.FixAs[Set[A]](), b.FixAs[Fun[A, A]]()
					hT := b.Conjuncts(
						b.Assume(),
						"T is finite",
						"T lies among the powers",
						"the coefficients lie in k",
						"the combination lies in W")
					x := b.FixAs[A]()
					inT := b.Assume()
					i, power := b.ObtainAs[Int](
						"x is a power tⁱ with n < i < 0",
						"∃i:int.(n < i ∧ i < &0) ∧ x = laurent_monomial(t, i)",
						BySets(inT, hT[1]))
					tInO := b.Have(
						"T lies in the overlap",
						"T ⊆ «plOverlap»",
						BySets(hT[1], sInO))
					linear := b.Have(
						"the coefficient at tⁱ is k-linear",
						"module_homomorphism(«plRingK», "+
							"    «plOverlapModule», "+
							"    restrict_module(regular_module(field_ring(L)), k), "+
							"    λf:A. laurent_polynomial_coefficient(k, t, f, i))",
						By(sub, transcendental, laurent_polynomial.LaurentCoeffLinear.Read(L).At(k, tm, i)))
					atW := b.Have(
						"the combination lies in W, which has no coefficient strictly between n and 0, so none at tⁱ",
						"laurent_polynomial_coefficient(k, t, module_sum(L.add, L.zero, T, λz:A. c(z) * z), i) = L.zero",
						By(
							sub,
							transcendental,
							power,
							hT[3],
							LineChartSumCoefficients.Read(L).At(
								k, tm, n, i, b.TermAs[A]("module_sum(L.add, L.zero, T, λz:A. c(z) * z)"))))
					terms := b.Have(
						"each term c(z) times the coefficient of z at tⁱ lies in k",
						"∀z:A. z ∈ T ⇒ c(z) * laurent_polynomial_coefficient(k, t, z, i) ∈ k",
						Derive(func(d *Argument) {
							z := d.FixAs[A]()
							inT := d.Assume()
							zInO := d.Have(
								"z lies in the overlap",
								"z ∈ «plOverlap»",
								BySets(inT, tInO))
							d.Show(
								"a product of members of k",
								By(
									inT,
									hT[2],
									sub,
									field.SubfieldMul,
									module_homomorphism.HomIn.Read(linear).At(proof.MemberOf(z, zInO))))
						}))
					others := b.Have(
						"every other power in T has no coefficient at tⁱ",
						"∀z:A. z ∈ T ∧ z ≠ x ⇒ c(z) * laurent_polynomial_coefficient(k, t, z, i) = L.zero",
						Derive(func(d *Argument) {
							d.FixAs[A]()
							hz := d.Conjuncts(
								d.Assume(),
								"z lies in T",
								"z is not x")
							j, zPower := d.ObtainAs[Int](
								"z is a power tʲ with n < j < 0",
								"∃j:int.(n < j ∧ j < &0) ∧ z = laurent_monomial(t, j)",
								BySets(hz[0], hT[1]))
							apart := d.Have(
								"j is not i, as z is not x",
								"i ≠ j",
								By(zPower, hz[1], power))
							none := d.Have(
								"so z has no coefficient at tⁱ",
								"laurent_polynomial_coefficient(k, t, z, i) = L.zero",
								By(Normalized, zPower, apart, coefficient.At(i, j)))
							inL := d.Have(
								"c(z) lies in L",
								"c(z) ∈ L.carrier",
								By(hz[0], hT[2], kInL))
							d.Show(
								"and its term vanishes",
								none.Rw(),
								ByArith(field.RingOn.Read(L), inL))
						}))
					single := b.Have(
						"so the combination of the coefficients at tⁱ is its one term at x",
						"module_sum(L.add, L.zero, T, λz:A. c(z) * laurent_polynomial_coefficient(k, t, z, i)) = "+
							"c(x) * laurent_polynomial_coefficient(k, t, x, i)",
						By(
							hT[0],
							inT,
							terms,
							others,
							module.ModuleSumSingle.Read(module_homomorphism.HomTarget.Read(linear)).At(T, x,
								b.TermAs[Fun[A, A]]("λz:A. c(z) * laurent_polynomial_coefficient(k, t, z, i)"))))
					combination := b.Have(
						"the coefficient at tⁱ of the combination is the combination of the coefficients",
						"laurent_polynomial_coefficient(k, t, module_sum(L.add, L.zero, T, λz:A. c(z) * z), i) = "+
							"module_sum(L.add, L.zero, T, λz:A. c(z) * laurent_polynomial_coefficient(k, t, z, i))",
						By(
							hT[0],
							b.Unfolded(tInO, set_basic.SubsetDef),
							hT[2],
							module_homomorphism.HomCombination.Read(linear).At(T, c, b.TermAs[Fun[A, A]]("λz:A. z"))))
					unit := b.Have(
						"x = tⁱ has coefficient one at tⁱ",
						"laurent_polynomial_coefficient(k, t, x, i) = L.one",
						By(Normalized, power, coefficient.At(i, i)))
					cx := b.Have(
						"c(x) lies in L",
						"c(x) ∈ L.carrier",
						By(inT, hT[2], kInL))
					scaled := b.Have(
						"and c(x) · one = c(x)",
						"c(x) * L.one = c(x)",
						ByArith(field.RingOn.Read(L), cx))
					b.Show(
						"so c(x), the coefficient of the combination at tⁱ, is zero",
						By(atW, combination, single, unit, scaled))
				}))

			// So T is independent over k, and its span meets W in zero alone.
			independent := a.Have(
				"the powers tⁱ, n < i < 0, are independent over k",
				"module_independent(«plRingK», «plField», «plPowersBelowN»)",
				Unfold(linear_independence.ModuleIndependentDef),
				SplitConj(
					Case(
						"the powers lie in L",
						By(sInL)),
					Case(
						"a vanishing k-combination of them has zero coefficients",
						Derive(func(b *Argument) {
							T, c := b.FixAs[Set[A]](), b.FixAs[Fun[A, A]]("c")
							hT := b.Conjuncts(
								b.Assume(),
								"T is finite",
								"T lies among the powers",
								"the coefficients lie in k",
								"the combination vanishes")
							inW := b.Have(
								"a vanishing combination lies in W",
								"module_sum(L.add, L.zero, T, λx:A. c(x) * x) ∈ «plChartSumN»",
								hT[3].Rw(),
								By(submodule.SubmoduleZero.Read(subW)))
							b.Show(
								"so its coefficients are zero",
								By(hT[0], hT[1], hT[2], inW, vanish.At(T, c)))
						})),
				))
			meetZero := a.Have(
				"a k-combination of the powers tⁱ, n < i < 0, lying in W is zero",
				"∀y:A. y ∈ module_span(«plRingK», «plField», «plPowersBelowN») ∧ y ∈ «plChartSumN» ⇒ y = L.zero",
				Derive(func(b *Argument) {
					y := b.FixAs[A]()
					hy := b.Conjuncts(
						b.Assume(),
						"y lies in the span of the powers",
						"y lies in W")
					T, c, comb := b.Obtain2As[Set[A], Fun[A, A]](
						"y is a k-combination of finitely many of the powers",
						"∃T:set(A). ∃c:(A → A). "+
							"    finite(T) ∧ "+
							"    T ⊆ «plPowersBelowN» ∧ "+
							"    (∀x:A. x ∈ T ⇒ c(x) ∈ k) ∧ "+
							"    y = module_sum(L.add, L.zero, T, λx:A. c(x) * x)",
						By(hy[0], sInL, linear_independence.SpanMembership.Read(overK).At(S, y)))
					hT := b.Conjuncts(
						comb,
						"T is finite",
						"T lies among the powers",
						"the coefficients lie in k",
						"y is their combination")
					inW := b.Have(
						"the combination lies in W",
						"module_sum(L.add, L.zero, T, λx:A. c(x) * x) ∈ «plChartSumN»",
						hT[3].RwRev(),
						By(hy[1]))
					zeroCoefficients := b.Have(
						"so its coefficients are zero",
						"∀x:A. x ∈ T ⇒ c(x) = L.zero",
						By(hT[0], hT[1], hT[2], inW, vanish.At(T, c)))
					zeroTerms := b.Have(
						"and so are its terms",
						"∀x:A. x ∈ T ⇒ c(x) * x = L.zero",
						Derive(func(d *Argument) {
							x := d.FixAs[A]()
							inT := d.Assume()
							xInL := d.Have(
								"x lies in L",
								"x ∈ L.carrier",
								BySets(inT, hT[1], sInL))
							cx := d.Have(
								"its coefficient is zero",
								"c(x) = L.zero",
								By(inT, zeroCoefficients))
							d.Show(
								"so its term is zero",
								cx.Rw(),
								By(comm_ring.MulLeftZeroOn.Read(field.RingOn.Read(L)).At(a.MemberOf[on.L](x, xInL))))
						}))
					b.Show(
						"so y is zero",
						hT[3].Rw(),
						By(hT[0], zeroTerms, module.ModuleSumZero.Read(overK).At(T, b.TermAs[Fun[A, A]]("λx:A. c(x) * x"))))
				}))
			complement := a.Have(
				"so the span of the powers meets W in zero alone",
				"module_span(«plRingK», «plField», «plPowersBelowN») ∩ «plChartSumN» ⊆ {L.zero}",
				Unfold(set_basic.SubsetDef),
				Simp(Fwd(set_basic.InInter), Fwd(set_basic.InSing)),
				By(meetZero))

			// The overlap is span(T) + W: every member is a k-combination of powers
			// of t, and each power lies in T or in W.
			spanSub := a.Have(
				"the span of the powers is a k-subspace of L",
				"submodule(«plRingK», «plField», module_span(«plRingK», «plField», «plPowersBelowN»))",
				By(sInL, submodule.SpanSubmodule.Read(overK).At(S)))
			sum := a.TermAs[Set[A]](
				"set_mul(L.add, module_span(«plRingK», «plField», «plPowersBelowN»), «plChartSumN»)")
			sumSub := a.Have(
				"so is span(T) + W",
				"submodule(«plRingK», "+
					"    «plField», "+
					"    set_mul(L.add, module_span(«plRingK», «plField», «plPowersBelowN»), «plChartSumN»))",
				By(spanSub, subW, submodule.SubmoduleSum.Read(overK).At(spanS, W)))
			sumSpace := a.Have(
				"and a vector space over k in its own right",
				"module_on(«plRingK», "+
					"    mk_module(L.add, "+
					"        L.zero, "+
					"        L.neg, "+
					"        L.mul, "+
					"        set_mul(L.add, module_span(«plRingK», «plField», «plPowersBelowN»), «plChartSumN»)))",
				By(
					sumSub,
					submodule.SubmoduleModuleOn.Read(overK).At(sum),
					module_record.RestrictModuleDef.At(V, sum)))
			spanInSum := a.Have(
				"span(T) lies in span(T) + W",
				"module_span(«plRingK», «plField», «plPowersBelowN») ⊆ "+
					"set_mul(L.add, module_span(«plRingK», «plField», «plPowersBelowN»), «plChartSumN»)",
				By(spanSub, subW, submodule.SumContainsLeft.Read(overK).At(spanS, W)))
			wInSum := a.Have(
				"and so does W",
				"«plChartSumN» ⊆ "+
					"set_mul(L.add, module_span(«plRingK», «plField», «plPowersBelowN»), «plChartSumN»)",
				By(spanSub, subW, submodule.SumContainsRight.Read(overK).At(spanS, W)))
			firstInW := a.Have(
				"k[t] lies in W",
				"fst(«plPairN») ⊆ «plChartSumN»",
				By(firstOverK, secondOverK, submodule.SumContainsLeft.Read(overK).At(first, second)))
			secondInW := a.Have(
				"and so does tⁿ · k[1/t]",
				"snd(«plPairN») ⊆ «plChartSumN»",
				By(firstOverK, secondOverK, submodule.SumContainsRight.Read(overK).At(first, second)))
			powerOf := a.TermAs[Fun[Int, A]]("λi:int. laurent_monomial(t, i)")
			rangeI := a.TermAs[Set[Int]]("«plExponentsBelowN»")
			sAsImage := a.Have(
				"the powers tⁱ, n < i < 0, are the image of the range under i ↦ tⁱ",
				"«plPowersBelowN» = image(λi:int. laurent_monomial(t, i), «plExponentsBelowN»)",
				By(set_image.SimpleImageGen.At(powerOf, a.TermAs[Set[Int]]("λi:int. n < i ∧ i < &0"))))
			spanned := a.Unfolded(a.Have(
				"the powers lie in their span",
				"«plPowersBelowN» ⊆ module_span(«plRingK», «plField», «plPowersBelowN»)",
				By(submodule.SubsetSpan.At(K, V, S))), set_basic.SubsetDef)
			everyPower := a.Have(
				"every power of t lies in span(T) + W",
				"∀i:int. "+
					"    laurent_monomial(t, i) ∈ "+
					"    set_mul(L.add, module_span(«plRingK», «plField», «plPowersBelowN»), «plChartSumN»)",
				Derive(func(b *Argument) {
					i := b.FixAs[Int]()
					power := b.TermAs[A]("laurent_monomial(t, i)")
					b.Cases(b.Term("n < i ∧ i < &0"))
					b.When(
						"for n < i < 0, tⁱ is one of the powers, so in their span",
						func(c *Argument, inRange Fact) {
							isPower := c.Have(
								"tⁱ is one of the powers",
								"laurent_monomial(t, i) ∈ «plPowersBelowN»",
								sAsImage.Rw(),
								By(inRange, set_image.FunInImage.At(powerOf, rangeI, i)))
							c.Show(
								"which lie in span(T) ⊆ span(T) + W",
								BySets(isPower, spanned, spanInSum))
						})
					b.Otherwise(
						"otherwise tⁱ lies in k[t] or in tⁿ · k[1/t], so in W",
						func(c *Argument, outside Fact) {
							inW := c.Have(
								"tⁱ lies in W",
								"laurent_monomial(t, i) ∈ «plChartSumN»",
								Derive(func(d *Argument) {
									d.Cases(d.Term("&0 ≤ i"))
									d.When(
										"for i ≥ 0, tⁱ lies in k[t]",
										func(e *Argument, nonneg Fact) {
											noNegative := e.Have(
												"tⁱ has no coefficient at a negative power",
												"∀j:int. j < &0 ⇒ laurent_polynomial_coefficient(k, t, laurent_monomial(t, i), j) = L.zero",
												Derive(func(f *Argument) {
													j := f.FixAs[Int]()
													below := f.Assume()
													apart := f.Have(
														"j is not i",
														"j ≠ i",
														ByArith(below, nonneg))
													f.Show(
														"so the coefficient is zero",
														By(apart, coefficient.At(j, i)))
												}))
											inK0 := e.Have(
												"so tⁱ lies in k[t]",
												"laurent_monomial(t, i) ∈ fst(«plPairN»)",
												By(powers, noNegative, sub, transcendental, LinePairCoefficients.Read(L).At(k, tm, n, power)))
											e.Show(
												"which lies in W",
												BySets(inK0, firstInW))
										})
									d.Otherwise(
										"for i < 0, i ≤ n, and tⁱ lies in tⁿ · k[1/t]",
										func(e *Argument, negative Fact) {
											low := e.Have(
												"i is at most n",
												"i ≤ n",
												ByArith(outside, negative))
											noHigh := e.Have(
												"tⁱ has no coefficient above n",
												"∀j:int. n < j ⇒ laurent_polynomial_coefficient(k, t, laurent_monomial(t, i), j) = L.zero",
												Derive(func(f *Argument) {
													j := f.FixAs[Int]()
													above := f.Assume()
													apart := f.Have(
														"j is not i",
														"j ≠ i",
														ByArith(above, low))
													f.Show(
														"so the coefficient is zero",
														By(apart, coefficient.At(j, i)))
												}))
											inK1 := e.Have(
												"so tⁱ lies in tⁿ · k[1/t]",
												"laurent_monomial(t, i) ∈ snd(«plPairN»)",
												By(powers, noHigh, sub, transcendental, LinePairCoefficients.Read(L).At(k, tm, n, power)))
											e.Show(
												"which lies in W",
												BySets(inK1, secondInW))
										})
								}))
							c.Show(
								"and W lies in span(T) + W",
								BySets(inW, wInSum))
						})
				}))
			everyMember := a.Have(
				"every member of the overlap lies in span(T) + W",
				Statement{
					Binders: "∀f:A.",
					Hypotheses: []string{
						"f ∈ «plOverlap»",
					},
					Conclusion: "f ∈ " +
						"set_mul(L.add, module_span(«plRingK», «plField», «plPowersBelowN»), «plChartSumN»)",
				},
				Derive(func(b *Argument) {
					f := b.FixAs[A]()
					inO := b.Assume()
					expansion := b.Conjuncts(
						b.Have(
							"f is the finite sum of its coefficients, in k, times the powers of t",
							"finite(fun_support(L.zero, λi:int. laurent_polynomial_coefficient(k, t, f, i))) ∧ "+
								"(∀i:int. laurent_polynomial_coefficient(k, t, f, i) ∈ k) ∧ "+
								"f = «plOwnExpansion»",
							By(sub, nonzero, inO, laurent_polynomial.LaurentExpansion.Read(L).At(k, tm, f))),
						"finitely many coefficients are nonzero",
						"they lie in k",
						"f is their sum")
					terms := b.Have(
						"each term lies in span(T) + W",
						"∀i:int. "+
							"    laurent_polynomial_coefficient(k, t, f, i) * laurent_monomial(t, i) ∈ "+
							"    set_mul(L.add, module_span(«plRingK», «plField», «plPowersBelowN»), «plChartSumN»)",
						By(expansion[1], everyPower, submodule.SubmoduleSmul.Read(sumSub)))
					total := b.Have(
						"so does their sum",
						"«plOwnExpansion» ∈ "+
							"set_mul(L.add, module_span(«plRingK», «plField», «plPowersBelowN»), «plChartSumN»)",
						By(
							expansion[0],
							terms,
							module.ModuleSumIn.Read(sumSpace).At(
								b.TermAs[Set[Int]]("fun_support(L.zero, λi:int. laurent_polynomial_coefficient(k, t, f, i))"),
								b.TermAs[Fun[Int, A]](
									"λi:int. laurent_polynomial_coefficient(k, t, f, i) * laurent_monomial(t, i)"))))
					b.Show(
						"which is f",
						By(total, expansion[2]))
				}))

			// So the classes of T are a basis of the overlap modulo W, one class per
			// power; and distinct exponents give distinct powers.
			quotient := a.Conjuncts(
				a.Unfolded(a.Have(
					"the classes of the powers are a basis of the overlap modulo W, one class per power",
					"module_basis(«plRingK», "+
						"    quotient_module(restrict_module(«plField», «plOverlap»), «plChartSumN»), "+
						"    image(coset_map(L.add, «plChartSumN»), «plPowersBelowN»)) ∧ "+
						"injective_on(«plPowersBelowN», coset_map(L.add, «plChartSumN»))",
					By(
						subO,
						subW,
						wInO,
						sInO,
						independent,
						everyMember,
						set_basic.SubsetDef,
						complement,
						module_dimension.QuotientComplementBasis.Read(overK).At(O, W, S))), group.CosetMapDef),
				"the classes of the powers are a basis",
				"v ↦ v + W is one-to-one on the powers")
			// SimpleImageGen, ImageCompose and ComposeApply are read at int exponents with A- and set-valued maps,
			// instances Simp's type adaptation does not reach from this leaf.
			classes := a.Have(
				"the classes of the powers are the classes of tⁱ, n < i < 0",
				"image(«plProjectionN», «plPowersBelowN») = «plClassesBelowN»",
				Simp(
					Fwd(set_image.SimpleImageGen.Inst(proof.TypeBinder.BindA[Int](), proof.TypeBinder.BindB[A]())),
					Fwd(set_image.SimpleImageGen.Inst(
						proof.TypeBinder.BindA[Int](), proof.TypeBinder.BindB[Set[A]]()))),
				Simp(Rev(set_image.ImageCompose.Inst(
					proof.TypeBinder.BindB[A](), proof.TypeBinder.BindC[Set[A]](), proof.TypeBinder.BindA[Int]()))),
				Simp(Fwd(functions.ComposeApply.Inst(
					proof.TypeBinder.BindB[A](), proof.TypeBinder.BindC[Set[A]](), proof.TypeBinder.BindA[Int]()))),
				Refl())
			basis := a.Have(
				"so the classes of tⁱ, n < i < 0, are a basis of the overlap modulo W",
				"module_basis(«plRingK», "+
					"    quotient_module(restrict_module(«plField», «plOverlap»), «plChartSumN»), "+
					"    «plClassesBelowN»)",
				classes.RwRev(),
				By(quotient[0]))
			oneToOne := a.Unfolded(quotient[1], functions.InjectiveOnDef)
			distinct := a.Have(
				"distinct exponents in the range give distinct classes",
				"injective_on({i:int | n < i ∧ i < &0}, "+
					"    λi:int. left_coset(L.add, laurent_monomial(t, i), «plChartSumN»))",
				Simp(Fwd(functions.InjectiveOnDef)),
				Derive(func(b *Argument) {
					i, j := b.FixAs[Int]("i"), b.FixAs[Int]("j")
					hij := b.Conjuncts(
						b.Assume(),
						"i lies in the range",
						"j lies in the range",
						"the classes of tⁱ and tʲ agree")
					ti, tj := b.TermAs[A]("laurent_monomial(t, i)"), b.TermAs[A]("laurent_monomial(t, j)")
					among := b.Have(
						"tⁱ and tʲ are among the powers",
						"laurent_monomial(t, i) ∈ «plPowersBelowN» ∧ laurent_monomial(t, j) ∈ «plPowersBelowN»",
						sAsImage.Rw(),
						By(
							hij[0],
							hij[1],
							set_image.FunInImage.At(powerOf, rangeI, i),
							set_image.FunInImage.At(powerOf, rangeI, j)))
					same := b.Have(
						"so tⁱ = tʲ, the map being one-to-one on the powers",
						"laurent_monomial(t, i) = laurent_monomial(t, j)",
						By(among, hij[2], oneToOne.At(ti, tj)))
					b.Show(
						"so i = j: otherwise tⁱ would have coefficient one at tⁱ and tʲ none",
						By(same, coefficient.At(i, i), coefficient.At(i, j), field.OneNotZeroOn.Read(L)))
				}))
			a.Show(
				"so the classes form a basis of H¹(O(n)), indexed one-to-one by the exponents",
				h1.Rw(),
				By(basis, distinct, overlapOnK, fieldOnK))
		}),
})}

// LinePairAmbient — the ambient of O(n), the overlap's span of its first
// chart k[t], is the overlap k[t, 1/t] itself: over the overlap, k[t]
// spans the members of L that a power of t carries into k[t], and that is
// how the overlap is defined.
var LinePairAmbient = linePairAmbientThm{family.Add(registry.ProofEntry{
	Name: "LinePairAmbient",
	Key:  "prop_1426c4af5433a619",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀t:A. ∀n:int.",
		Hypotheses: []string{
			"subfield(L, k)",
			"t ∈ L.carrier",
			"t ≠ L.zero",
		},
		Conclusion: "lattice_pair_ambient(«plRing», «plField», «plPairN») = «plOverlap»",
	},
		func(a *Argument, L field.FieldFact[on.L], k *Expr[Set[A]], t *Expr[A], n *Expr[Int], h Fact) {
			parts := a.Conjuncts(
				h,
				"k is a subfield of L",
				"t lies in L",
				"t is not zero")
			tm := a.MemberOf[on.L](t, parts[1])
			lattice := a.Have(
				"O(n) is a lattice pair on the line",
				"lattice_pair(«plRing», «plChart0», «plChart1», «plField», «plPairN»)",
				By(h, LinePairIsLattice.Read(L).At(k, tm, n)))
			charts := a.Conjuncts(
				a.Unfolded(lattice, lattice_pair.LatticePairDef),
				"the field is a module over the overlap",
				"k[t] is a submodule over k[t]",
				"tⁿ · k[1/t] is a submodule over k[1/t]",
				"the two span the same")
			chart := a.Have(
				"the first chart of O(n) is k[t]",
				"fst(«plPairN») = «plChart0»",
				Simp(Fwd(ProjectiveLinePairDef), Fwd(pairs.Fst)),
				Refl())
			datum := a.Have(
				"k[t] and k[1/t], glued along the overlap, form a biaffine datum",
				"biaffine(«plRing», «plChart0», «plChart1», t, L.inv(t))",
				By(parts[0], parts[2], ProjectiveLineBiaffine.Read(L).At(k, tm)))
			chart0 := a.TermAs[Set[A]]("«plChart0»")
			span := a.Have(
				"over the overlap, k[t] spans the members of L that a power of t carries into k[t]",
				"module_span(«plRing», «plField», «plChart0») = "+
					"{v:A | v ∈ L.carrier ∧ (∃m:num. monoid_pow(L.mul, L.one, t, m) * v ∈ «plChart0»)}",
				By(
					datum,
					charts[0],
					chart,
					charts[1],
					lattice_pair.ChartSpanAway.At(
						a.TermAs[module_record.RingOps[A]]("«plRing»"),
						chart0,
						a.TermAs[Set[A]]("«plChart1»"),
						t,
						a.TermAs[A]("L.inv(t)"),
						a.TermAs[module_record.ModuleOps[A, A]]("«plField»"),
						chart0)))
			a.Show(
				"which is the overlap",
				Simp(Fwd(lattice_pair.LatticePairAmbientDef)),
				chart.Rw(),
				span.Rw(),
				Simp(Fwd(ring_away.RingAwayDef)),
				Refl())
		}),
})}

// LineH0Dim — ℓ(O(n)) = n + 1 for n ≥ −1 and 0 below: the powers t⁰, …,
// tⁿ are a basis of H⁰(O(n)) over k (LineIntersectionBasis), one power per
// exponent, and the exponents 0, …, n number max(n + 1, 0). H⁰(O(n)) is a
// k-subspace of L (lattice_pair.H0Submodule), and over the field k a finite
// basis counts the dimension (module_dimension.FiniteBasisDim).
var LineH0Dim = lineH0DimThm{family.Add(registry.ProofEntry{
	Name: "LineH0Dim",
	Key:  "prop_b0458b334524a7d8",
	Reading: "The finiteness clause is what makes the dimension a " +
		"determined number; the count is the size of {0, …, n}, empty for n < 0.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀t:A. ∀n:int.",
		Hypotheses: []string{
			"subfield(L, k)",
			"t ∈ L.carrier",
			"¬algebraic_over(L, k, t)",
		},
		Conclusion: "finite_dimensional(«plScalars», lattice_pair_h0(«plField», «plPairN»)) ∧ " +
			"int_of_num(lattice_pair_h0_dim(«plRing», k, «plField», «plPairN»)) = int_max(n + &1, &0)",
		Abbrev: Abbrev{
			{Name: "plH0N", Text: "lattice_pair_h0(«plField», «plPairN»)"},
		},
	},
		func(a *Argument, L field.FieldFact[on.L], k *Expr[Set[A]], t *Expr[A], n *Expr[Int], line Fact) {
			parts := a.Conjuncts(
				line,
				"k is a subfield of L",
				"t lies in L",
				"t is transcendental over k")
			subfield, tInL, transcendental := parts[0], parts[1], parts[2]
			tm := a.MemberOf[on.L](t, tInL)
			basis := a.Have(
				"the powers t⁰, …, tⁿ are a basis of H⁰(O(n)) over k, distinct at distinct exponents",
				"module_basis(«plScalars», «plH0N», «plPowersUpToN») ∧ "+
					"injective_on(«plExponentsUpToN», λi:int. laurent_monomial(t, i))",
				By(subfield, transcendental, LineIntersectionBasis.Read(L).At(k, tm, n)))

			// H⁰(O(n)) is a vector space over k.
			nonzero := a.Have(
				"t, transcendental, is not zero",
				"t ≠ L.zero",
				By(line, algebraic_element.TranscendentalInverse.Read(L).At(k, tm)))
			datum := a.Simplified(GroupPremises(parts[0], nonzero, LineDatum.Read(L).At(k, tm)))
			space := a.Have(
				"L is a vector space over k",
				"module_on(«plScalars», «plField»)",
				By(datum))
			kInCharts := a.Have(
				"k lies in k[t] and in k[1/t]",
				"k ⊆ «plChart0» ∧ k ⊆ «plChart1»",
				By(datum))
			pair := a.Have(
				"O(n) is a lattice pair on the line",
				"lattice_pair(«plRing», «plChart0», «plChart1», «plField», «plPairN»)",
				By(subfield, tInL, nonzero, LinePairIsLattice.Read(L).At(k, tm, n)))
			sections := a.Have(
				"so H⁰(O(n)) = k[t] ∩ tⁿ · k[1/t] is a k-subspace of L",
				"submodule(«plScalars», «plField», «plSectionsN»)",
				By(
					pair,
					kInCharts,
					lattice_pair.H0Submodule.At(
						a.TermAs[module_record.RingOps[A]]("«plRing»"),
						a.TermAs[Set[A]]("«plChart0»"),
						a.TermAs[Set[A]]("«plChart1»"),
						k,
						a.TermAs[ModuleOps[A, A]]("«plField»"),
						a.TermAs[Prod[Set[A], Set[A]]]("«plPairN»"))))
			h0Space := a.Have(
				"and a vector space over k in its own right",
				"module_on(«plScalars», «plH0N»)",
				By(
					sections,
					submodule.SubmoduleModuleOn.Read(space).At(a.TermAs[Set[A]]("«plSectionsN»")),
					lattice_pair.LatticePairH0Def))

			// Count the basis.
			exponents := a.TermAs[Set[Int]]("«plExponentsUpToN»")
			power := a.TermAs[Fun[Int, A]]("λi:int. laurent_monomial(t, i)")
			powers := a.TermAs[Set[A]]("«plPowersUpToN»")
			interval := a.Have(
				"the exponents 0, …, n number max(n + 1, 0)",
				"finite(«plExponentsUpToN») ∧ &card(«plExponentsUpToN») = max(n + &1, &0)",
				ByArith(int_embed.IntIntervalSize.At(a.TermAs[Int]("&0"), n)))
			counted := a.Have(
				"the powers are the image of the exponents under i "+
					"↦ tⁱ, one power per exponent, so as many and finite",
				"finite(«plPowersUpToN») ∧ card(«plPowersUpToN») = card(«plExponentsUpToN»)",
				By(
					basis,
					interval,
					set_image.SimpleImageGen.At(power, a.TermAs[Set[Int]]("λi:int. &0 ≤ i ∧ i ≤ n")),
					cardinality.CardImageInj.At(power, exponents),
					finite_set.FiniteImage.At(power, exponents)))
			fieldK := a.Have(
				"k, a subfield of L, is a field under the operations of its scalar ring, with L's inverse",
				"ring_subfield(«plScalars», L.inv, k)",
				By(
					subfield,
					field.SubfieldRingSubfield.Read(L).At(k, a.TermAs[Set[A]]("«plOverlap»")),
					field.RingSubfieldRestrict.At(
						a.TermAs[module_record.RingOps[A]]("«plRing»"), k, a.TermAs[Fun[A, A]]("L.inv"), k)))
			dimension := a.Conjuncts(
				a.Have(
					"over the field k the finite basis makes H⁰(O(n)) "+
						"finite-dimensional, of dimension the number of powers",
					"finite_dimensional(«plScalars», «plH0N») ∧ "+
						"module_dim(«plScalars», «plH0N») = card(«plPowersUpToN»)",
					By(
						basis,
						counted,
						fieldK,
						module_dimension.FiniteBasisDim.Read(h0Space).At(a.TermAs[Fun[A, A]]("L.inv"), powers))),
				"H⁰(O(n)) is finite-dimensional",
				"of dimension the number of powers")
			count := a.Have(
				"h⁰(O(n)) is the number of powers, max(n + 1, 0)",
				"&lattice_pair_h0_dim(«plRing», k, «plField», «plPairN») = max(n + &1, &0)",
				ByArith(dimension[1], counted, interval, lattice_pair.LatticePairH0DimDef))
			a.Show(
				"so H⁰(O(n)) is finite of dimension max(n + 1, 0)",
				By(dimension[0], count))
		}),
})}

// LineH1Dim — dim H¹(O(n)) = −n − 1 for n ≤ −1 and 0 above: the classes
// of tⁱ, n < i < 0, are a basis of H¹(O(n)), one class for each such i,
// and over the field k the dimension is the size of a finite basis.
var LineH1Dim = lineH1DimThm{family.Add(registry.ProofEntry{
	Name:    "LineH1Dim",
	Key:     "prop_77c3ecd29c9a7004",
	Reading: "The count is the size of {i | n < i < 0}, empty for n ≥ −1.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀t:A. ∀n:int.",
		Hypotheses: []string{
			"subfield(L, k)",
			"t ∈ L.carrier",
			"¬algebraic_over(L, k, t)",
		},
		Conclusion: "finite_dimensional(«plScalars», lattice_pair_h1(«plRing», «plField», «plPairN»)) ∧ " +
			"int_of_num(lattice_pair_h1_dim(«plRing», k, «plField», «plPairN»)) = int_max(-n - &1, &0)",
		Abbrev: Abbrev{
			{Name: "plH1N", Text: "lattice_pair_h1(«plRing», «plField», «plPairN»)"},
		},
	},
		func(a *Argument, L field.FieldFact[on.L], k *Expr[Set[A]], t *Expr[A], n *Expr[Int], h Fact) {
			given := a.Conjuncts(
				h,
				"k is a subfield of L",
				"t lies in L",
				"t is transcendental over k")
			subK, tInL, transcendental := given[0], given[1], given[2]
			tm := a.MemberOf[on.L](t, tInL)
			nonzero := a.Have(
				"t, transcendental, is not zero",
				"t ≠ L.zero",
				By(h, algebraic_element.TranscendentalInverse.Read(L).At(k, tm)))
			pair := a.Have(
				"O(n) is a lattice pair on the line",
				"lattice_pair(«plRing», «plChart0», «plChart1», «plField», «plPairN»)",
				By(subK, tInL, nonzero, LinePairIsLattice.Read(L).At(k, tm, n)))
			vectorSpace := a.Have(
				"so H¹(O(n)) is a vector space over k",
				"module_on(«plScalars», «plH1N»)",
				By(
					subK,
					tInL,
					nonzero,
					pair,
					LineH1Module.Read(L).At(
						k,
						tm,
						a.TermAs[module_record.ModuleOps[A, A]]("«plField»"),
						a.TermAs[Prod[Set[A], Set[A]]]("«plPairN»"))))
			basis := a.Conjuncts(
				a.Have(
					"the classes of tⁱ, n < i < 0, form a basis of H¹(O(n)), distinct i giving distinct classes",
					"module_basis(«plScalars», «plH1N», «plClassesBelowN») ∧ "+
						"injective_on(«plExponentsBelowN», "+
						"    λi:int. left_coset(L.add, laurent_monomial(t, i), «plChartSumN»))",
					By(subK, transcendental, LineQuotientBasis.Read(L).At(k, tm, n))),
				"the classes are a basis",
				"i ↦ [tⁱ] is one-to-one on the indices")
			count := a.Conjuncts(
				a.Have(
					"the integers strictly between n and 0 are finitely many, max(0 − n − 1, 0) of them",
					"finite(«plExponentsBelowN») ∧ &card(«plExponentsBelowN») = max(&0 - n - &1, &0)",
					By(int_embed.IntegersBetween.At(n, a.TermAs[Int]("&0")))),
				"the indices are finitely many",
				"and max(0 − n − 1, 0) of them")
			classes := a.TermAs[Fun[Int, Set[A]]](
				"λi:int. left_coset(L.add, laurent_monomial(t, i), «plChartSumN»)")
			indices := a.TermAs[Set[Int]]("«plExponentsBelowN»")
			asImage := a.Have(
				"the basis is the image of the indices under i ↦ [tⁱ]",
				"«plClassesBelowN» = "+
					"image(λi:int. left_coset(L.add, laurent_monomial(t, i), «plChartSumN»), «plExponentsBelowN»)",
				By(set_image.SimpleImageGen.At(classes, a.TermAs[Set[Int]]("λi:int. n < i ∧ i < &0"))))
			size := a.Have(
				"so the basis is finite, with as many classes as there are indices",
				"finite(«plClassesBelowN») ∧ card(«plClassesBelowN») = card(«plExponentsBelowN»)",
				asImage.Rw(),
				By(
					count[0],
					basis[1],
					finite_set.FiniteImage.At(classes, indices),
					cardinality.CardImageInj.At(classes, indices)))
			fieldK := a.Have(
				"k, a subfield of L, is a field under the operations of its scalar ring, with L's inverse",
				"ring_subfield(«plScalars», L.inv, k)",
				By(
					subK,
					field.SubfieldRingSubfield.Read(L).At(k, a.TermAs[Set[A]]("«plOverlap»")),
					field.RingSubfieldRestrict.At(
						a.TermAs[module_record.RingOps[A]]("«plRing»"), k, a.TermAs[Fun[A, A]]("L.inv"), k)))
			dimension := a.Have(
				"over the field k a finite basis makes H¹(O(n)) finite-dimensional, of dimension its size",
				"finite_dimensional(«plScalars», «plH1N») ∧ "+
					"module_dim(«plScalars», «plH1N») = card(«plClassesBelowN»)",
				By(
					size,
					basis[0],
					fieldK,
					module_dimension.FiniteBasisDim.Read(vectorSpace).At(
						a.TermAs[Fun[A, A]]("L.inv"), a.TermAs[Set[Set[A]]]("«plClassesBelowN»"))))
			a.Show(
				"h¹ is that dimension, the number of indices, which is max(−n − 1, 0)",
				ByArith(
					dimension,
					size,
					count[1],
					lattice_pair.LatticePairH1DimDef.At(a.TermAs[module_record.RingOps[A]]("«plRing»"), k,
						a.TermAs[module_record.ModuleOps[A, A]]("«plField»"), a.TermAs[Prod[Set[A], Set[A]]]("«plPairN»"))))
		}),
})}

// LineH1Module — for every lattice pair M on the line, the ambient and
// chart 0 + chart 1 are k-subspaces of V, the sum inside the ambient
// (lattice_pair.ChartSumInAmbient), and H¹(M) is a vector space over k:
// k is a subring of both charts, over which the charts, their sum and the
// ambient are submodules (lattice_pair.PairOverSubring) and H¹(M) is a
// module (lattice_pair.H1OverSubring).
var LineH1Module = lineH1ModuleThm{family.Add(registry.ProofEntry{
	Name: "LineH1Module",
	Key:  "prop_986104cc6e83e7bd",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀t:A. ∀V:module_ops(A, B). ∀M:prod(set(B), set(B)).",
		Hypotheses: []string{
			"subfield(L, k)",
			"t ∈ L.carrier",
			"t ≠ L.zero",
			"lattice_pair(«plRing», «plChart0», «plChart1», V, M)",
		},
		Conclusion: "submodule(«plScalars», V, «plAmbient») ∧ " +
			"submodule(«plScalars», V, set_mul(V.add, fst(M), snd(M))) ∧ " +
			"set_mul(V.add, fst(M), snd(M)) ⊆ «plAmbient» ∧ " +
			"module_on(«plScalars», lattice_pair_h1(«plRing», V, M))",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k *Expr[Set[A]],
			t *Expr[A],
			V *Expr[module_record.ModuleOps[A, B]],
			M *Expr[Prod[Set[B], Set[B]]],
			h Fact,
		) {
			given := a.Conjuncts(
				h,
				"k is a subfield of L",
				"t lies in L",
				"t is not zero",
				"M is a lattice pair on the line")
			subK, tInL, nonzero, pair := given[0], given[1], given[2], given[3]
			tm := a.MemberOf[on.L](t, tInL)
			kSubring := a.Have(
				"k is a subring of the overlap",
				"subring(«plRing», k)",
				By(subK, nonzero, laurent_polynomial.LaurentScalarSubring.Read(L).At(k, tm)))
			datum := a.Conjuncts(
				a.Have(
					"the line is a biaffine datum with k inside both charts",
					"biaffine(«plRing», «plChart0», «plChart1», t, L.inv(t)) ∧ k ⊆ «plChart0» ∧ k ⊆ «plChart1»",
					By(subK, nonzero, LineDatum.Read(L).At(k, tm))),
				"the line is a biaffine datum",
				"k lies in k[t]",
				"k lies in k[1/t]")
			ring, chart0, chart1 :=
				a.TermAs[module_record.RingOps[A]]("«plRing»"),
				a.TermAs[Set[A]]("«plChart0»"),
				a.TermAs[Set[A]]("«plChart1»")
			inv := a.TermAs[A]("L.inv(t)")
			a.Show(
				"over k, a subring of both charts, the ambient and the chart sum "+
					"are subspaces, the one inside the other, and H¹(M) is a vector space",
				By(
					datum[0],
					kSubring,
					datum[1],
					datum[2],
					pair,
					lattice_pair.PairOverSubring.At(ring, chart0, chart1, t, inv, k, V, M),
					lattice_pair.ChartSumInAmbient.At(ring, chart0, chart1, V, M),
					lattice_pair.H1OverSubring.At(ring, chart0, chart1, t, inv, k, V, M)))
		}),
})}

// LineEuler — χ(O(n)) = n + 1: H⁰(O(n)) and H¹(O(n)) are finite over k of
// dimensions max(n + 1, 0) and max(−n − 1, 0) (LineH0Dim, LineH1Dim), so
// O(n) is finite, and the difference of the two maxima is n + 1.
var LineEuler = lineEulerThm{family.Add(registry.ProofEntry{
	Name: "LineEuler",
	Key:  "prop_4eaa308b21b0bedf",
	Reading: "n is any integer: for n ≤ −2, O(n) has no sections and χ(O(n)) " +
		"= n + 1 = −h¹ is negative; at n = −1 both cohomology spaces vanish.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀t:A. ∀n:int.",
		Hypotheses: []string{
			"subfield(L, k)",
			"t ∈ L.carrier",
			"¬algebraic_over(L, k, t)",
		},
		Conclusion: "lattice_pair_finite(«plRing», k, «plField», «plPairN») ∧ " +
			"lattice_pair_euler(«plRing», k, «plField», «plPairN») = n + &1",
	},
		func(a *Argument, L field.FieldFact[on.L], k *Expr[Set[A]], t *Expr[A], n *Expr[Int], line Fact) {
			parts := a.Conjuncts(
				line,
				"k is a subfield of L",
				"t lies in L",
				"t is transcendental over k")
			tm := a.MemberOf[on.L](t, parts[1])
			h0 := a.Conjuncts(
				GroupPremises(parts[0], parts[2], LineH0Dim.Read(L).At(k, tm, n)),
				"H⁰(O(n)) is finite-dimensional over k",
				"of dimension max(n + 1, 0)")
			h1 := a.Conjuncts(
				GroupPremises(parts[0], parts[2], LineH1Dim.Read(L).At(k, tm, n)),
				"H¹(O(n)) is finite-dimensional over k",
				"of dimension max(−n − 1, 0)")
			finite := a.Have(
				"so O(n) is finite, both of its cohomology spaces being finite-dimensional",
				"lattice_pair_finite(«plRing», k, «plField», «plPairN»)",
				By(h0[0], h1[0], lattice_pair.LatticePairFiniteDef))
			euler := a.Have(
				"and χ(O(n)) = h⁰ − h¹ = max(n + 1, 0) − max(−n − "+
					"1, 0), which is n + 1: one of the two maxima is zero",
				"lattice_pair_euler(«plRing», k, «plField», «plPairN») = n + &1",
				ByArith(
					h0[1],
					h1[1],
					lattice_pair.LatticePairEulerDef.At(a.TermAs[module_record.RingOps[A]]("«plRing»"), k,
						a.TermAs[module_record.ModuleOps[A, A]]("«plField»"), a.TermAs[Prod[Set[A], Set[A]]]("«plPairN»"))))
			a.Show(
				"O(n) is finite, with Euler characteristic n + 1",
				By(finite, euler))
		}),
})}
