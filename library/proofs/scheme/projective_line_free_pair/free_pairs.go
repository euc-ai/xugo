// free_pairs.go — the free pairs on the line, the sums of the O(N(e)) · e
// along field elements e independent over k[t]: a free pair is a lattice
// pair; adding e to E splits off e · O(N(e)) as a direct summand; and so
// h⁰ and h¹ of a free pair along a finite E are the sums of those of the
// O(N(e)), which multiplying by e ≠ zero leaves unchanged.

package projective_line_free_pair

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_extension"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/laurent_polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/quotient_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/linear_independence"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_away"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"

	"github.com/euc-ai/xugo/library/proofs/iterate/int/int_sum"
	"github.com/euc-ai/xugo/library/proofs/scheme/invertible_lattice_pair"
	"github.com/euc-ai/xugo/library/proofs/scheme/lattice_pair"
	"github.com/euc-ai/xugo/library/proofs/scheme/lattice_pair_map"
	"github.com/euc-ai/xugo/library/proofs/scheme/projective_line"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// lineDatumConjuncts names the conjuncts of projective_line.LineDatum's
// conclusion, in order, for the members that split the datum.
var lineDatumConjuncts = []string{
	"k[t] and k[1/t] glued along the overlap form a biaffine datum",
	"k lies in k[t]",
	"k lies in k[1/t]",
	"k[t] lies in the overlap",
	"k[1/t] lies in the overlap",
	"k[t] is a subring of L",
	"k[1/t] is a subring of L",
	"the overlap is a subring of L",
	"t lies in k[t]",
	"inv(t) lies in k[1/t]",
	"inv(t) lies in the overlap",
	"L is a vector space over k",
	"L is a module over k[t]",
	"L is a module over k[1/t]",
	"L is a module over the overlap",
}

// FreeLinePairIsLattice — a free pair is a lattice pair on the line. The
// field is a module over the overlap and over each chart, each chart's
// span a submodule over its own ring; over the overlap the k[t]-span of E
// spans what E spans, the k[1/t]-span of the t^N(e) · e what they span,
// and the two agree, each t^N(e) being a unit of the overlap.
var FreeLinePairIsLattice = freeLinePairIsLatticeThm{family.Add(registry.ProofEntry{
	Name: "FreeLinePairIsLattice",
	Key:  "prop_e8328a917d349676",
	Reading: "The two spans generate one module over the overlap because each t^N(e) " +
		"is a unit there; independence of E is not needed here, only for the dimensions.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀t:A. ∀E:set(A). ∀N:(A → int).",
		Hypotheses: []string{
			"subfield(L, k)",
			"t ∈ L.carrier",
			"t ≠ L.zero",
			"E ⊆ L.carrier",
		},
		Conclusion: "lattice_pair(«plRing», «plChart0», «plChart1», «plField», «plFreePair»)",
		Abbrev: Abbrev{
			{Name: "plOverlapSpanGens", Text: "module_span(«plRing», «plField», «plGenerators»)"},
		},
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k *Expr[Set[A]],
			t *Expr[A],
			E *Expr[Set[A]],
			N *Arrow[A, Int],
			h Fact,
		) {
			hyp := a.Conjuncts(
				h,
				"k is a subfield of L",
				"t lies in L",
				"t is not zero",
				"E lies in L")
			subfield, tInL, nonzero, setInL := hyp[0], hyp[1], hyp[2], hyp[3]
			tm := a.MemberOf[on.L](t, tInL)
			fieldRing := field.RingOn.Read(L)
			chart0, chart1 := a.TermAs[Set[A]]("«plChart0»"), a.TermAs[Set[A]]("«plChart1»")
			R, V :=
				a.TermAs[module_record.RingOps[A]]("«plRing»"), a.TermAs[module_record.ModuleOps[A, A]]("«plField»")
			fieldOps := a.TermAs[module_record.RingOps[A]]("field_ring(L)")
			generators, overE, overGenerators :=
				a.TermAs[Set[A]]("«plGenerators»"),
				a.TermAs[Set[A]]("«plOverlapSpanE»"),
				a.TermAs[Set[A]]("«plOverlapSpanGens»")
			line := a.Conjuncts(
				a.Have(
					"the line's datum",
					"biaffine(«plRing», «plChart0», «plChart1», t, L.inv(t)) ∧ "+
						"k ⊆ «plChart0» ∧ "+
						"k ⊆ «plChart1» ∧ "+
						"«plChart0» ⊆ «plOverlap» ∧ "+
						"«plChart1» ⊆ «plOverlap» ∧ "+
						"subring(field_ring(L), «plChart0») ∧ "+
						"subring(field_ring(L), «plChart1») ∧ "+
						"subring(field_ring(L), «plOverlap») ∧ "+
						"t ∈ «plChart0» ∧ "+
						"L.inv(t) ∈ «plChart1» ∧ "+
						"L.inv(t) ∈ «plOverlap» ∧ "+
						"module_on(«plScalars», «plField») ∧ "+
						"module_on(«plRing0», «plField») ∧ "+
						"module_on(«plRing1», «plField») ∧ "+
						"module_on(«plRing», «plField»)",
					By(subfield, tInL, nonzero, projective_line.LineDatum.Read(L).At(k, tm))),
				lineDatumConjuncts...)
			module0, module1, overlapModule := line[12], line[13], line[14]

			// Each chart of the free pair is a span over the chart's ring, so a submodule over it.
			sub0 := a.Have(
				"the k[t]-span of E is a k[t]-submodule of L",
				"submodule(restrict_ring(«plRing», «plChart0»), «plField», «plFreeChart0»)",
				By(
					submodule.SpanSubmodule.Read(module0).At(E),
					setInL,
					module_record.RestrictRingDef.At(R, chart0),
					module_record.RestrictRingDef.At(fieldOps, chart0)))

			// The generators lie in what E spans over the overlap, each a multiple of e by a power of t.
			powers := a.Have(
				"the powers of t lie in L",
				"∀m:int. laurent_monomial(t, m) ∈ L.carrier",
				By(nonzero, laurent_polynomial.LaurentMonomialProduct.Read(L).At(tm)))
			powersInOverlap := a.Have(
				"and in the overlap",
				"∀m:int. laurent_monomial(t, m) ∈ «plOverlap»",
				By(Read(laurent_polynomial.LaurentMonomialInRing, L).At(k, t), subfield, tInL, nonzero))
			closedE := a.Have(
				"what E spans over the overlap is a submodule over it",
				"submodule(«plRing», «plField», «plOverlapSpanE»)",
				By(submodule.SpanSubmodule.Read(overlapModule).At(E), setInL))
			eInSpanE := a.Have(
				"holding each e of E",
				"∀e:A. e ∈ E ⇒ e ∈ «plOverlapSpanE»",
				BySets(submodule.SubsetSpan.At(R, V, E)))
			generatorInSpanE := a.Have(
				"and each t^N(e) · e, a multiple of e by a scalar of the overlap",
				"∀e:A. e ∈ E ⇒ laurent_monomial(t, N(e)) * e ∈ «plOverlapSpanE»",
				By(submodule.SubmoduleSmul.Read(closedE), powersInOverlap, eInSpanE))
			generatorsInSpanE := a.Have(
				"so the generators lie in what E spans",
				"«plGenerators» ⊆ «plOverlapSpanE»",
				BySets(generatorInSpanE))
			generatorsInL := a.Have(
				"and in L",
				"«plGenerators» ⊆ L.carrier",
				By(
					generatorsInSpanE,
					submodule.SubmoduleSubset.Read(closedE),
					set_order.SubsetTrans.At(generators, overE, a.TermAs[Set[A]]("L.carrier"))))
			sub1 := a.Have(
				"the k[1/t]-span of the generators is a k[1/t]-submodule of L",
				"submodule(restrict_ring(«plRing», «plChart1»), «plField», «plFreeChart1»)",
				By(
					submodule.SpanSubmodule.Read(module1).At(generators),
					generatorsInL,
					module_record.RestrictRingDef.At(R, chart1),
					module_record.RestrictRingDef.At(fieldOps, chart1)))

			// E lies in what the generators span: e = t^(−N(e)) · (t^N(e) · e).
			closedGenerators := a.Have(
				"what the generators span over the overlap is a submodule over it",
				"submodule(«plRing», «plField», «plOverlapSpanGens»)",
				By(submodule.SpanSubmodule.Read(overlapModule).At(generators), generatorsInL))
			isGenerator := a.Have(
				"t^N(e) · e is a generator for e in E",
				"∀e:A. e ∈ E ⇒ laurent_monomial(t, N(e)) * e ∈ «plGenerators»",
				BySets())
			generatorsInSpan := a.Have(
				"the generators lie in their span",
				"∀x:A. x ∈ «plGenerators» ⇒ x ∈ «plOverlapSpanGens»",
				BySets(submodule.SubsetSpan.At(R, V, generators)))
			generatorInSpan := a.Have(
				"so t^N(e) · e lies in it for e in E",
				"∀e:A. e ∈ E ⇒ laurent_monomial(t, N(e)) * e ∈ «plOverlapSpanGens»",
				By(isGenerator, generatorsInSpan))
			eInSpanGenerators := a.Have(
				"each e of E lies in what the generators span",
				"∀e:A. e ∈ E ⇒ e ∈ «plOverlapSpanGens»",
				Derive(func(b *Argument) {
					e := b.FixAs[A]("e")
					inE := b.Assume()
					inL := b.Have(
						"e lies in L",
						"e ∈ L.carrier",
						BySets(setInL, inE))
					n, minusN := b.TermAs[Int]("N(e)"), b.TermAs[Int]("-N(e)")
					inverse := b.Have(
						"t^N(e) and t^(−N(e)) are inverse",
						"laurent_monomial(t, N(e)) * laurent_monomial(t, -N(e)) = L.one",
						By(nonzero, laurent_polynomial.LaurentMonomialInverse.Read(L).At(tm, n)))
					undone := b.Have(
						"so t^(−N(e)) undoes t^N(e)",
						"laurent_monomial(t, -N(e)) * (laurent_monomial(t, N(e)) * e) = e",
						ByArith(fieldRing, Scaled(e, inverse), powers.At(n), powers.At(minusN), inL))
					scaled := b.Have(
						"and t^(−N(e)) · (t^N(e) · e) lies in the span, a "+
							"multiple of a generator by a scalar of the overlap",
						"laurent_monomial(t, -N(e)) * (laurent_monomial(t, N(e)) * e) ∈ «plOverlapSpanGens»",
						By(
							submodule.SubmoduleSmul.Read(closedGenerators),
							powersInOverlap.At(minusN),
							generatorInSpan.At(e),
							inE))
					b.Show(
						"so e lies in the span",
						By(scaled, undone))
				}))
			eWithinSpanGenerators := a.Have(
				"so E lies in what the generators span",
				"E ⊆ «plOverlapSpanGens»",
				BySets(eInSpanGenerators))

			// So E and the generators span one module over the overlap, and so do the two charts.
			within := a.Have(
				"what the generators span lies in what E spans",
				"«plOverlapSpanGens» ⊆ «plOverlapSpanE»",
				By(submodule.SpanLeast.At(R, V, generators, overE), closedE, generatorsInSpanE))
			holds := a.Have(
				"and what E spans in what the generators span",
				"«plOverlapSpanE» ⊆ «plOverlapSpanGens»",
				By(submodule.SpanLeast.At(R, V, E, overGenerators), closedGenerators, eWithinSpanGenerators))
			same := a.Have(
				"so the generators and E span one module over the overlap",
				"«plOverlapSpanGens» = «plOverlapSpanE»",
				By(within, holds, set_order.SubsetAntisym))
			agree := a.Have(
				"and over the overlap the two charts span one module, spanning over a chart first changing nothing",
				"module_span(«plRing», «plField», «plFreeChart0») = "+
					"module_span(«plRing», «plField», «plFreeChart1»)",
				CalcEq(
					Leg(
						overE,
						"the k[t]-span of E spans what E spans",
						By(
							Read(submodule.SpanOfSubringSpan, overlapModule).At(
								a.TermAs[module_record.RingOps[A]]("«plRing0»"), E),
							line[3],
							setInL)),
					Leg(
						overGenerators,
						"which the generators span as well",
						By(same)),
					FinalLeg(
						"and that is what the k[1/t]-span of the generators spans",
						By(
							Read(submodule.SpanOfSubringSpan, overlapModule).At(
								a.TermAs[module_record.RingOps[A]]("«plRing1»"), generators),
							line[4],
							generatorsInL)),
				))
			freeChart0, freeChart1 := a.TermAs[Set[A]]("«plFreeChart0»"), a.TermAs[Set[A]]("«plFreeChart1»")
			a.Show(
				"L is a module over the overlap, each chart of the free pair a "+
					"submodule over its ring, and the two span one module over the overlap",
				Simp(Fwd(ProjectiveLineFreePairDef)),
				By(
					lattice_pair.LatticePairDef.At(
						R, chart0, chart1, V, a.TermAs[Prod[Set[A], Set[A]]]("(«plFreeChart0», «plFreeChart1»)")),
					pairs.Fst.At(freeChart0, freeChart1),
					pairs.Snd.At(freeChart0, freeChart1),
					overlapModule,
					sub0,
					sub1,
					agree))
		}),
})}

// FreeLinePairSplit — for e new to E, with insert(e, E) independent over
// k[t], the free pair on insert(e, E) is the direct sum of e · O(N(e)) and
// the free pair on E. Chart by chart, a span over insert(e, E) is the
// multiples of e (of t^N(e) · e on chart 1) plus the span over E
// (SpanInsert), and those multiples are the charts e · k[t] and
// e · t^N(e) · k[1/t] of e · O(N(e)). The two ambients lie in the
// overlap's spans of e and of E, which meet only in zero, insert(e, E)
// staying independent over the overlap (IndependentAway).
var FreeLinePairSplit = freeLinePairSplitThm{family.Add(registry.ProofEntry{
	Name: "FreeLinePairSplit",
	Key:  "prop_719b9f78b585713a",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀t e:A. ∀E:set(A). ∀N:(A → int).",
		Hypotheses: []string{
			"subfield(L, k)",
			"t ∈ L.carrier",
			"t ≠ L.zero",
			"e ∉ E",
			"module_independent(«plRing0», «plField», insert(e, E))",
		},
		Conclusion: "fst(«plFreePairInsert») = " +
			"set_mul(L.add, fst(«plScaledPairAtE»), fst(«plFreePair»)) ∧ " +
			"snd(«plFreePairInsert») = set_mul(L.add, snd(«plScaledPairAtE»), snd(«plFreePair»)) ∧ " +
			"«plAmbientOf»(«plScaledPairAtE») ∩ «plAmbientOf»(«plFreePair») ⊆ {L.zero}",
		Abbrev: Abbrev{
			{Name: "plFreePairInsert", Text: "projective_line_free_pair(L, k, t, insert(e, E), N)"},
			{Name: "plGeneratorsInsert", Text: "{laurent_monomial(t, N(x)) * x | x:A | x ∈ insert(e, E)}"},
			{Name: "plFreeChart0Insert", Text: "module_span(«plRing0», «plField», insert(e, E))"},
			{Name: "plFreeChart1Insert", Text: "module_span(«plRing1», «plField», «plGeneratorsInsert»)"},
			{Name: "plScaledChart0", Text: "image(L.mul(e), «plChart0»)"},
			{Name: "plScaledChart1", Text: "image(L.mul(e), " +
				"    image(L.mul(laurent_monomial(t, N(e))), «plChart1»))"},
		},
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k *Expr[Set[A]],
			t, e *Expr[A],
			E *Expr[Set[A]],
			N *Arrow[A, Int],
			h Fact,
		) {
			given := a.Conjuncts(
				h,
				"k is a subfield of L",
				"t lies in L",
				"t is not zero",
				"e is not in E",
				"insert(e, E) is independent over k[t]")
			subfield, tInL, nonzero, fresh, independent := given[0], given[1], given[2], given[3], given[4]
			tm := a.MemberOf[on.L](t, tInL)
			ringL := field.RingOn.Read(L)
			V := a.TermAs[module_record.ModuleOps[A, A]]("«plField»")
			chart0, chart1 := a.TermAs[Set[A]]("«plChart0»"), a.TermAs[Set[A]]("«plChart1»")
			ring0, overlapRing :=
				a.TermAs[module_record.RingOps[A]]("«plRing0»"), a.TermAs[module_record.RingOps[A]]("«plRing»")
			single, insertE, fieldSet :=
				a.TermAs[Set[A]]("{e}"), a.TermAs[Set[A]]("insert(e, E)"), a.TermAs[Set[A]]("L.carrier")
			line := a.Conjuncts(
				a.Have(
					"the line's datum",
					"biaffine(«plRing», «plChart0», «plChart1», t, L.inv(t)) ∧ "+
						"k ⊆ «plChart0» ∧ "+
						"k ⊆ «plChart1» ∧ "+
						"«plChart0» ⊆ «plOverlap» ∧ "+
						"«plChart1» ⊆ «plOverlap» ∧ "+
						"subring(field_ring(L), «plChart0») ∧ "+
						"subring(field_ring(L), «plChart1») ∧ "+
						"subring(field_ring(L), «plOverlap») ∧ "+
						"t ∈ «plChart0» ∧ "+
						"L.inv(t) ∈ «plChart1» ∧ "+
						"L.inv(t) ∈ «plOverlap» ∧ "+
						"module_on(«plScalars», «plField») ∧ "+
						"module_on(«plRing0», «plField») ∧ "+
						"module_on(«plRing1», «plField») ∧ "+
						"module_on(«plRing», «plField»)",
					By(subfield, tInL, nonzero, projective_line.LineDatum.Read(L).At(k, tm))),
				lineDatumConjuncts...)
			overlapInL := a.Have(
				"the overlap lies in L",
				"«plOverlap» ⊆ L.carrier",
				By(comm_ring.SubringSubset.Read(line[7])))
			module0, module1, moduleOverlap := line[12], line[13], line[14]
			chart0InL := a.Have(
				"k[t] lies in L, inside the overlap",
				"«plChart0» ⊆ L.carrier",
				By(
					line[3],
					overlapInL,
					set_order.SubsetTrans.At(chart0, a.TermAs[Set[A]]("«plOverlap»"), fieldSet)))
			chart1InL := a.Have(
				"and so does k[1/t]",
				"«plChart1» ⊆ L.carrier",
				By(
					line[4],
					overlapInL,
					set_order.SubsetTrans.At(chart1, a.TermAs[Set[A]]("«plOverlap»"), fieldSet)))
			power := a.Have(
				"tᴺ⁽ᵉ⁾ lies in the overlap",
				"laurent_monomial(t, N(e)) ∈ «plOverlap»",
				By(
					subfield,
					tInL,
					nonzero,
					Read(laurent_polynomial.LaurentMonomialInRing, L).At(k, t, a.TermAs[Int]("N(e)"))))
			powerL := a.Have(
				"so in L",
				"laurent_monomial(t, N(e)) ∈ L.carrier",
				BySets(power, overlapInL))

			// insert(e, E): its parts, and its independence over the overlap.
			inParts := a.Conjuncts(
				a.Have(
					"insert(e, E) lies in L, so e and E do",
					"e ∈ L.carrier ∧ E ⊆ L.carrier",
					By(
						linear_independence.IndependentInCarrier.Read(independent),
						set_order.InsertSubset.At(E, fieldSet, e))),
				"e lies in L",
				"E lies in L")
			eL, setL := inParts[0], inParts[1]
			em := a.MemberOf[on.L](e, eL)
			parted := a.Conjuncts(
				a.Have(
					"insert(e, E) is {e} ∪ E, the two parts disjoint",
					"insert(e, E) = {e} ∪ E ∧ {e} ∩ E = ∅",
					BySets(fresh)),
				"insert(e, E) is {e} ∪ E",
				"{e} and E are disjoint")
			freeOverlap := a.Have(
				"{e} ∪ E is independent over the overlap, the ring k[t] with t inverted",
				"module_independent(«plRing», «plField», {e} ∪ E)",
				parted[0].RwRev(),
				By(
					line[5],
					chart0InL,
					line[8],
					nonzero,
					independent,
					Read(ring_away.IndependentAway, L).At(chart0, t, insertE)))
			meetOverlap := a.Have(
				"so the overlap's spans of e and of E meet only in zero",
				"module_span(«plRing», «plField», {e}) ∩ «plOverlapSpanE» ⊆ {L.zero}",
				By(
					freeOverlap,
					parted[1],
					linear_independence.IndependentSpansMeet.Read(moduleOverlap).At(single, E)))

			// The charts along E and along insert(e, E), and those of e · O(N(e)).
			along := a.Conjuncts(
				a.Have(
					"along E, chart 0 is the k[t]-span of E and chart 1 the k[1/t]-span of the tᴺ⁽ʸ⁾ · y",
					"fst(«plFreePair») = «plFreeChart0» ∧ snd(«plFreePair») = «plFreeChart1»",
					Unfold(ProjectiveLineFreePairDef),
					By(pairs.Fst, pairs.Snd)),
				"chart 0 along E",
				"chart 1 along E")
			alongIns := a.Conjuncts(
				a.Have(
					"and likewise along insert(e, E)",
					"fst(«plFreePairInsert») = «plFreeChart0Insert» ∧ snd(«plFreePairInsert») = «plFreeChart1Insert»",
					Unfold(ProjectiveLineFreePairDef),
					By(pairs.Fst, pairs.Snd)),
				"chart 0 along insert(e, E)",
				"chart 1 along insert(e, E)")
			scaled := a.Conjuncts(
				a.Have(
					"the charts of e · O(N(e)) are e · k[t] and e · tᴺ⁽ᵉ⁾ · k[1/t]",
					"fst(«plScaledPairAtE») = «plScaledChart0» ∧ snd(«plScaledPairAtE») = «plScaledChart1»",
					Simp(
						Fwd(invertible_lattice_pair.LatticePairScaleDef),
						Fwd(projective_line.ProjectiveLinePairDef),
						Fwd(pairs.Fst),
						Fwd(pairs.Snd)),
					Basic()),
				"chart 0 of e · O(N(e))",
				"chart 1 of e · O(N(e))")
			gensIns := a.Have(
				"the generators along insert(e, E) are those along E and tᴺ⁽ᵉ⁾ · e",
				"«plGeneratorsInsert» = insert(laurent_monomial(t, N(e)) * e, «plGenerators»)",
				BySets())
			spanOverlapSub := a.Have(
				"the overlap's span of E is a submodule",
				"submodule(«plRing», «plField», «plOverlapSpanE»)",
				By(setL, submodule.SpanSubmodule.Read(moduleOverlap).At(E)))
			gensInSpan := a.Have(
				"each tᴺ⁽ʸ⁾ · y, y in E, lies in the overlap's span of E",
				"«plGenerators» ⊆ «plOverlapSpanE»",
				Unfold(set_basic.SubsetDef),
				Derive(func(b *Argument) {
					b.FixAs[A]("z")
					_, made := b.ObtainAs[A](
						"z is tᴺ⁽ʸ⁾ · y with y in E",
						"∃y:A. z = laurent_monomial(t, N(y)) * y ∧ y ∈ E",
						BySets(b.Assume()))
					parts := b.Conjuncts(
						made,
						"z = tᴺ⁽ʸ⁾ · y",
						"y lies in E")
					scalar := b.Have(
						"tᴺ⁽ʸ⁾ lies in the overlap",
						"laurent_monomial(t, N(y)) ∈ «plOverlap»",
						By(
							subfield,
							tInL,
							nonzero,
							Read(laurent_polynomial.LaurentMonomialInRing, L).At(k, t, b.TermAs[Int]("N(y)"))))
					vector := b.Have(
						"y lies in the overlap's span of E",
						"y ∈ «plOverlapSpanE»",
						BySets(parts[1], submodule.SubsetSpan.At(overlapRing, V, E)))
					b.Show(
						"a scalar of the overlap times a member of the span",
						parts[0].Rw(),
						By(scalar, vector, submodule.SubmoduleSmul.Read(spanOverlapSub)))
				}))
			gensL := a.Have(
				"so the generators lie in L",
				"«plGenerators» ⊆ L.carrier",
				BySets(gensInSpan, submodule.SubmoduleSubset.Read(spanOverlapSub)))
			newGenL := a.Have(
				"tᴺ⁽ᵉ⁾ · e lies in L",
				"laurent_monomial(t, N(e)) * e ∈ L.carrier",
				By(powerL, eL, comm_ring.MulIn.Read(ringL)))

			// Chart by chart, the span over insert(e, E) is the multiples of e plus the span over E.
			expand0 := a.Have(
				"chart 0 along insert(e, E) is k[t] · e plus chart 0 along E",
				"fst(«plFreePairInsert») = {c * e + w | c:A, w:A | c ∈ «plChart0» ∧ w ∈ fst(«plFreePair»)}",
				alongIns[0].Rw(),
				along[0].Rw(),
				By(setL, eL, Read(submodule.SpanInsert, module0).At(E, e)))
			expand1 := a.Have(
				"chart 1 along insert(e, E) is k[1/t] · tᴺ⁽ᵉ⁾e plus chart 1 along E",
				"snd(«plFreePairInsert») = "+
					"{c * (laurent_monomial(t, N(e)) * e) + w | c:A, w:A | c ∈ «plChart1» ∧ w ∈ snd(«plFreePair»)}",
				alongIns[1].Rw(),
				gensIns.Rw(),
				along[1].Rw(),
				By(
					gensL,
					newGenL,
					Read(submodule.SpanInsert, module1).At(
						a.TermAs[Set[A]]("«plGenerators»"), a.TermAs[A]("laurent_monomial(t, N(e)) * e"))))
			commute0 := a.Have(
				"a multiple c · e is e · c",
				"∀c:A. c ∈ «plChart0» ⇒ c * e = e * c",
				Derive(func(b *Argument) {
					c := b.FixAs[A]("c")
					cm := b.MemberOf[on.L](c, b.Have(
						"c lies in L",
						"c ∈ L.carrier",
						BySets(b.Assume(), chart0InL)))
					b.Show(
						"L is commutative",
						ByArith(ringL, cm, em))
				}))
			commute1 := a.Have(
				"and c · (tᴺ⁽ᵉ⁾ · e) is e · (tᴺ⁽ᵉ⁾ · c)",
				"∀c:A. c ∈ «plChart1» ⇒ c * (laurent_monomial(t, N(e)) * e) = e * (laurent_monomial(t, N(e)) * c)",
				Derive(func(b *Argument) {
					c := b.FixAs[A]("c")
					cm := b.MemberOf[on.L](c, b.Have(
						"c lies in L",
						"c ∈ L.carrier",
						BySets(b.Assume(), chart1InL)))
					b.Show(
						"L is commutative",
						ByArith(ringL, cm, em, b.MemberOf[on.L](b.TermAs[A]("laurent_monomial(t, N(e))"), powerL)))
				}))
			multiples0 := a.Have(
				"e · k[t] is the multiples of e",
				"«plScaledChart0» = {c * e | c:A | c ∈ «plChart0»}",
				BySets(commute0))
			multiples1 := a.Have(
				"and e · tᴺ⁽ᵉ⁾ · k[1/t] the multiples of tᴺ⁽ᵉ⁾ · e",
				"«plScaledChart1» = {c * (laurent_monomial(t, N(e)) * e) | c:A | c ∈ «plChart1»}",
				BySets(commute1))
			split0 := a.Have(
				"so chart 0 along insert(e, E) is e · k[t] plus chart 0 along E",
				"fst(«plFreePairInsert») = set_mul(L.add, fst(«plScaledPairAtE»), fst(«plFreePair»))",
				expand0.Rw(),
				scaled[0].Rw(),
				multiples0.Rw(),
				Simp(Fwd(quotient_group.SetMulDef)),
				BySets())
			split1 := a.Have(
				"and chart 1 along insert(e, E) is e · tᴺ⁽ᵉ⁾ · k[1/t] plus chart 1 along E",
				"snd(«plFreePairInsert») = set_mul(L.add, snd(«plScaledPairAtE»), snd(«plFreePair»))",
				expand1.Rw(),
				scaled[1].Rw(),
				multiples1.Rw(),
				Simp(Fwd(quotient_group.SetMulDef)),
				BySets())

			// The ambients lie in the overlap's spans of e and of E, which meet only in zero.
			chart0InOverlap := a.Have(
				"chart 0 along E lies in the overlap's span of E",
				"fst(«plFreePair») ⊆ «plOverlapSpanE»",
				along[0].Rw(),
				By(
					line[3],
					Read(submodule.SubmoduleRestrictScalars, spanOverlapSub).At(ring0),
					submodule.SubsetSpan.At(overlapRing, V, E),
					submodule.SpanLeast.At(ring0, V, E, a.TermAs[Set[A]]("«plOverlapSpanE»"))))
			ambientE := a.Have(
				"so the ambient along E, its span over the overlap, lies there too",
				"«plAmbientOf»(«plFreePair») ⊆ «plOverlapSpanE»",
				Simp(Fwd(lattice_pair.LatticePairAmbientDef)),
				By(
					submodule.SpanLeast.At(
						overlapRing, V, a.TermAs[Set[A]]("fst(«plFreePair»)"), a.TermAs[Set[A]]("«plOverlapSpanE»")),
					spanOverlapSub,
					chart0InOverlap))
			lineSpan := a.TermAs[Set[A]]("module_span(«plRing», «plField», {e})")
			lineSpanSub := a.Have(
				"the overlap's span of e is a submodule",
				"submodule(«plRing», «plField», module_span(«plRing», «plField», {e}))",
				By(
					eL,
					set_order.SingSubset.At(fieldSet, e),
					submodule.SpanSubmodule.Read(moduleOverlap).At(single)))
			eInLine := a.Have(
				"holding e",
				"e ∈ module_span(«plRing», «plField», {e})",
				BySets(submodule.SubsetSpan.At(overlapRing, V, single)))
			multiplesInLine := a.Have(
				"e · k[t] lies in it, k[t] lying in the overlap",
				"«plScaledChart0» ⊆ module_span(«plRing», «plField», {e})",
				Simp(Fwd(set_basic.SubsetDef)),
				Derive(func(b *Argument) {
					x := b.FixAs[A]("x")
					c, made := b.ObtainAs[A](
						"x is e · c with c in k[t]",
						"∃c:A. x = e * c ∧ c ∈ «plChart0»",
						By(b.Assume(), set_basic.InImage.At(b.TermAs[Fun[A, A]]("L.mul(e)"), chart0, x)))
					parts := b.Conjuncts(
						made,
						"x = e · c",
						"c lies in k[t]")
					inOverlap := b.Have(
						"c lies in the overlap",
						"c ∈ «plOverlap»",
						BySets(parts[1], line[3]))
					commuted := b.Have(
						"e · c = c · e",
						"c * e = e * c",
						By(commute0.At(c), parts[1]))
					b.Show(
						"x = c · e, a multiple of e by a scalar of the overlap",
						parts[0].Rw(),
						commuted.RwRev(),
						By(inOverlap, eInLine, submodule.SubmoduleSmul.Read(lineSpanSub).AsFact().At(c, e)))
				}))
			ambientScaled := a.Have(
				"so the ambient of e · O(N(e)), its span over the overlap, lies there",
				"«plAmbientOf»(«plScaledPairAtE») ⊆ module_span(«plRing», «plField», {e})",
				Simp(Fwd(lattice_pair.LatticePairAmbientDef)),
				scaled[0].Rw(),
				By(
					submodule.SpanLeast.At(overlapRing, V, a.TermAs[Set[A]]("«plScaledChart0»"), lineSpan),
					lineSpanSub,
					multiplesInLine))
			apart := a.Have(
				"so the two ambients meet only in zero",
				"«plAmbientOf»(«plScaledPairAtE») ∩ «plAmbientOf»(«plFreePair») ⊆ {L.zero}",
				BySets(ambientScaled, ambientE, meetOverlap))
			a.Show(
				"each chart along insert(e, E) is that of e · O(N(e)) "+
					"plus that along E, and the ambients meet only in zero",
				By(split0, split1, apart))
		}),
})}

// ScaledLineH0Dim — for e ≠ zero in L, H⁰(e · O(n)) is finite over k of
// dimension max(n + 1, 0), as H⁰(O(n)) is: multiplying by e is k-linear
// and one-to-one on L, so it carries H⁰(O(n)) isomorphically onto
// e · H⁰(O(n)), which is the meet e · k[t] ∩ e · tⁿ · k[1/t] of the
// charts of e · O(n).
var ScaledLineH0Dim = scaledLineH0DimThm{family.Add(registry.ProofEntry{
	Name: "ScaledLineH0Dim",
	Key:  "prop_e7274d1c0fd91273",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀t e:A. ∀n:int.",
		Hypotheses: []string{
			"subfield(L, k)",
			"t ∈ L.carrier",
			"¬algebraic_over(L, k, t)",
			"e ∈ L.carrier",
			"e ≠ L.zero",
		},
		Conclusion: "finite_dimensional(«plScalars», lattice_pair_h0(«plField», «plScaledPairN»)) ∧ " +
			"int_of_num(lattice_pair_h0_dim(«plRing», k, «plField», «plScaledPairN»)) = int_max(n + &1, &0)",
		Abbrev: Abbrev{
			{Name: "plScaledH0N", Text: "image(L.mul(e), «plSectionsN»)"},
		},
	},
		func(a *Argument, L field.FieldFact[on.L], k *Expr[Set[A]], t, e *Expr[A], n *Expr[Int], h Fact) {
			given := a.Conjuncts(
				h,
				"k is a subfield of L",
				"t lies in L",
				"t is transcendental over k",
				"e lies in L",
				"e is not zero")
			subfield, tInL, transcendental, eL, eNonzero := given[0], given[1], given[2], given[3], given[4]
			tm, em := a.MemberOf[on.L](t, tInL), a.MemberOf[on.L](e, eL)
			scalars := a.TermAs[module_record.RingOps[A]]("«plScalars»")
			V := a.TermAs[module_record.ModuleOps[A, A]]("«plField»")
			inv := a.TermAs[Fun[A, A]]("L.inv")
			chart0, chart1 := a.TermAs[Set[A]]("«plChart0»"), a.TermAs[Set[A]]("«plChart1»")
			pair := a.TermAs[Prod[Set[A], Set[A]]]("«plPairN»")
			first, second, sections :=
				a.TermAs[Set[A]]("fst(«plPairN»)"),
				a.TermAs[Set[A]]("snd(«plPairN»)"),
				a.TermAs[Set[A]]("«plSectionsN»")
			times := a.TermAs[Fun[A, A]]("L.mul(e)")
			nonzero := a.Have(
				"t, transcendental over k, is not zero",
				"t ≠ L.zero",
				By(h, algebraic_element.TranscendentalInverse.Read(L).At(k, tm)))
			kInCharts := a.Have(
				"k lies in both charts",
				"k ⊆ «plChart0» ∧ k ⊆ «plChart1»",
				By(projective_line.LineDatum.Read(L).At(k, tm), subfield, tInL, nonzero))
			scalarField := a.Have(
				"k, a subfield of L, is a field under the operations of its scalar ring, with L's inverse",
				"ring_subfield(«plScalars», L.inv, k)",
				By(
					subfield,
					field.SubfieldRingSubfield.Read(L).At(k, a.TermAs[Set[A]]("«plOverlap»")),
					field.RingSubfieldRestrict.At(a.TermAs[module_record.RingOps[A]]("«plRing»"), k, inv, k)))

			// H⁰(O(n)): a subspace over k, finite-dimensional of dimension max(n + 1, 0).
			counted := a.Conjuncts(
				a.Have(
					"H⁰(O(n)) is finite-dimensional of dimension max(n + 1, 0)",
					"finite_dimensional(«plScalars», lattice_pair_h0(«plField», «plPairN»)) ∧ "+
						"int_of_num(lattice_pair_h0_dim(«plRing», k, «plField», «plPairN»)) = int_max(n + &1, &0)",
					By(subfield, tInL, transcendental, projective_line.LineH0Dim.Read(L).At(k, tm, n))),
				"H⁰(O(n)) is finite-dimensional",
				"of dimension max(n + 1, 0)")
			finite := a.Have(
				"read as the submodule of its sections",
				"finite_dimensional(«plScalars», restrict_module(«plField», «plSectionsN»))",
				Simp(Rev(lattice_pair.LatticePairH0Def)),
				By(counted[0]))
			dimension := a.Have(
				"whose dimension is ℓ(O(n))",
				"lattice_pair_h0_dim(«plRing», k, «plField», «plPairN») = "+
					"module_dim(«plScalars», restrict_module(«plField», «plSectionsN»))",
				Simp(Fwd(lattice_pair.LatticePairH0DimDef), Fwd(lattice_pair.LatticePairH0Def)),
				Basic())
			lattice := a.Have(
				"O(n) is a lattice pair on the line",
				"lattice_pair(«plRing», «plChart0», «plChart1», «plField», «plPairN»)",
				By(subfield, tInL, nonzero, projective_line.LinePairIsLattice.Read(L).At(k, tm, n)))
			subspace := a.Have(
				"so its sections form a subspace over k",
				"submodule(«plScalars», «plField», «plSectionsN»)",
				By(
					lattice,
					kInCharts,
					lattice_pair.H0Submodule.At(
						a.TermAs[module_record.RingOps[A]]("«plRing»"), chart0, chart1, k, V, pair)))
			latticeParts := a.Conjuncts(
				a.Unfolded(lattice, lattice_pair.LatticePairDef),
				"L is a module over the overlap",
				"k[t] is a k[t]-submodule of L",
				"tⁿ · k[1/t] is a k[1/t]-submodule of L",
				"the two charts span one module over the overlap")
			chartsInL := a.Have(
				"its charts lie in L",
				"fst(«plPairN») ⊆ L.carrier ∧ snd(«plPairN») ⊆ L.carrier",
				By(
					submodule.SubmoduleSubset.Read(latticeParts[1]),
					submodule.SubmoduleSubset.Read(latticeParts[2])))
			inL := a.Have(
				"and so do its sections",
				"«plSectionsN» ⊆ L.carrier",
				BySets(chartsInL))

			// Multiplying by e: k-linear on L, one-to-one there.
			fieldOnK := module_record.RestrictRingDef.At(a.TermAs[module_record.RingOps[A]]("field_ring(L)"), k)
			scale := a.Have(
				"multiplying by e is k-linear on L",
				"module_homomorphism(«plScalars», «plField», «plField», L.mul(e))",
				By(
					subfield,
					field.SubfieldSubring.Read(L).At(k),
					eL,
					Read(field_extension.ScaleLinear, L).At(k, e),
					module_record.RestrictRingDef.At(a.TermAs[module_record.RingOps[A]]("«plRing»"), k),
					fieldOnK))
			restricted := a.Have(
				"and from H⁰(O(n)) into L",
				"module_homomorphism(«plScalars», restrict_module(«plField», «plSectionsN»), «plField», L.mul(e))",
				By(scale, subspace, module_homomorphism.HomRestrictSource.At(scalars, V, V, times, sections)))
			cancel := a.Have(
				"one-to-one on L, e being nonzero",
				"injective_on(L.carrier, L.mul(e))",
				By(eNonzero, field.MulBijective.Read(L).At(em)))
			oneToOne := a.Have(
				"so on H⁰(O(n))",
				"injective_on(«plSectionsN», L.mul(e))",
				By(cancel, inL, functions.InjectiveOnSubset.At(times, sections, a.TermAs[Set[A]]("L.carrier"))))

			// The sections of e · O(n) are e · H⁰(O(n)).
			scaledCharts := a.Conjuncts(
				a.Have(
					"the charts of e · O(n) are e times those of O(n)",
					"fst(«plScaledPairN») = image(L.mul(e), fst(«plPairN»)) ∧ "+
						"snd(«plScaledPairN») = image(L.mul(e), snd(«plPairN»))",
					Simp(Fwd(invertible_lattice_pair.LatticePairScaleDef), Fwd(pairs.Fst), Fwd(pairs.Snd)),
					Basic()),
				"chart 0 of e · O(n)",
				"chart 1 of e · O(n)")
			common := a.Have(
				"a multiple of e from each chart is e times a section, e · u = e · v forcing u = v",
				"image(L.mul(e), fst(«plPairN»)) ∩ image(L.mul(e), snd(«plPairN»)) ⊆ «plScaledH0N»",
				Simp(Fwd(set_basic.SubsetDef)),
				Derive(func(b *Argument) {
					y := b.FixAs[A]("y")
					both := b.Conjuncts(
						b.Have(
							"y is a multiple of e from each chart",
							"y ∈ image(L.mul(e), fst(«plPairN»)) ∧ y ∈ image(L.mul(e), snd(«plPairN»))",
							BySets(b.Assume())),
						"y lies in e · k[t]",
						"y lies in e · tⁿ · k[1/t]")
					u, at0 := b.ObtainAs[A](
						"y = e · u with u on chart 0",
						"∃u:A. y = e * u ∧ u ∈ fst(«plPairN»)",
						By(both[0], set_basic.InImage.At(times, first, y)))
					v, at1 := b.ObtainAs[A](
						"y = e · v with v on chart 1",
						"∃v:A. y = e * v ∧ v ∈ snd(«plPairN»)",
						By(both[1], set_basic.InImage.At(times, second, y)))
					p, q := b.Conjuncts(
						at0,
						"y = e · u",
						"u lies on chart 0"), b.Conjuncts(
						at1,
						"y = e · v",
						"v lies on chart 1")
					members := b.Have(
						"u and v lie in L",
						"u ∈ L.carrier ∧ v ∈ L.carrier",
						BySets(p[1], q[1], chartsInL))
					same := b.Have(
						"so u = v, e · u = e · v",
						"u = v",
						By(Normalized, b.Unfolded(cancel, functions.InjectiveOnDef).At(u, v), members, p[0], q[0]))
					onChart1 := b.Have(
						"so u lies on chart 1 as well",
						"u ∈ snd(«plPairN»)",
						same.Rw(),
						By(q[1]))
					section := b.Have(
						"so u is a section of O(n)",
						"u ∈ «plSectionsN»",
						By(p[1], onChart1, set_basic.InInter.At(first, second, u)))
					b.Show(
						"and y = e · u lies in e · H⁰(O(n))",
						p[0].Rw(),
						By(section, set_image.FunInImage.At(times, sections, u)))
				}))
			sectionsScaled := a.Have(
				"so H⁰(e · O(n)) is e · H⁰(O(n))",
				"fst(«plScaledPairN») ∩ snd(«plScaledPairN») = «plScaledH0N»",
				scaledCharts[0].Rw(),
				scaledCharts[1].Rw(),
				By(common, set_image.ImageInterSubset.At(times, first, second), set_order.SubsetAntisym))

			// So H⁰(e · O(n)) has the dimension of H⁰(O(n)).
			carried := a.Conjuncts(
				a.Have(
					"e · H⁰(O(n)) is finite-dimensional, of the dimension of H⁰(O(n))",
					"finite_dimensional(«plScalars», restrict_module(«plField», «plScaledH0N»)) ∧ "+
						"module_dim(«plScalars», restrict_module(«plField», «plScaledH0N»)) = "+
						"module_dim(«plScalars», restrict_module(«plField», «plSectionsN»))",
					By(
						scalarField,
						restricted,
						oneToOne,
						finite,
						module_dimension.InjectiveImageDim.At(
							scalars,
							inv,
							a.TermAs[module_record.ModuleOps[A, A]]("restrict_module(«plField», «plSectionsN»)"),
							V,
							times))),
				"e · H⁰(O(n)) is finite-dimensional",
				"of the dimension of H⁰(O(n))")
			a.Show(
				"so H⁰(e · O(n)) is finite over k of dimension max(n + 1, 0)",
				Simp(Fwd(lattice_pair.LatticePairH0DimDef), Fwd(lattice_pair.LatticePairH0Def)),
				sectionsScaled.Rw(),
				SplitConj(Case(
					"finite, as e · H⁰(O(n)) is",
					By(carried[0])),
					Case(
						"of the dimension of H⁰(O(n)), max(n + 1, 0)",
						ByArith(carried[1], dimension, counted[1]))))
		}),
})}

// FreeLinePairH0Dim — ℓ of a free pair is the sum of the ℓ(O(N(e))), by
// induction on E: along ∅ the only section is zero, and adding e to D
// splits off e · O(N(e)) as a direct summand (FreeLinePairSplit), H⁰ of a
// direct sum adding (lattice_pair.DirectSumH0), and H⁰(e · O(N(e))) has
// dimension ℓ(O(N(e))) (ScaledLineH0Dim).
var FreeLinePairH0Dim = freeLinePairH0DimThm{family.Add(registry.ProofEntry{
	Name:    "FreeLinePairH0Dim",
	Key:     "prop_beb10d0f104791fe",
	Reading: "E finite is load-bearing: infinitely many e with N(e) ≥ 0 make H⁰ infinite-dimensional.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀t:A. ∀E:set(A). ∀N:(A → int).",
		Hypotheses: []string{
			"subfield(L, k)",
			"t ∈ L.carrier",
			"¬algebraic_over(L, k, t)",
			"finite(E)",
			"module_independent(restrict_ring(field_ring(L), «plChart0»), «plField», E)",
		},
		Conclusion: "finite_dimensional(«plScalars», lattice_pair_h0(«plField», «plFreePair»)) ∧ " +
			"int_of_num(lattice_pair_h0_dim(«plRing», k, «plField», «plFreePair»)) = " +
			"int_sum(E, λe:A. int_max(N(e) + &1, &0))",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k *Expr[Set[A]],
			t *Expr[A],
			E *Expr[Set[A]],
			N *Arrow[A, Int],
			h Fact,
		) {
			given := a.Conjuncts(
				h,
				"k is a subfield of L",
				"t lies in L",
				"t is transcendental over k",
				"E is finite",
				"E is independent over k[t]")
			subfield, tInL, transcendental, finiteE, independent :=
				given[0], given[1], given[2], given[3], given[4]
			tm := a.MemberOf[on.L](t, tInL)
			scalars, ring :=
				a.TermAs[module_record.RingOps[A]]("«plScalars»"), a.TermAs[module_record.RingOps[A]]("«plRing»")
			V := a.TermAs[module_record.ModuleOps[A, A]]("«plField»")
			inv := a.TermAs[Fun[A, A]]("L.inv")
			chart0, chart1, overlap :=
				a.TermAs[Set[A]]("«plChart0»"), a.TermAs[Set[A]]("«plChart1»"), a.TermAs[Set[A]]("«plOverlap»")
			nonzero := a.Have(
				"t, transcendental over k, is not zero",
				"t ≠ L.zero",
				By(h, algebraic_element.TranscendentalInverse.Read(L).At(k, tm)))
			line := a.Conjuncts(
				a.Have(
					"the line's datum",
					"biaffine(«plRing», «plChart0», «plChart1», t, L.inv(t)) ∧ "+
						"k ⊆ «plChart0» ∧ "+
						"k ⊆ «plChart1» ∧ "+
						"«plChart0» ⊆ «plOverlap» ∧ "+
						"«plChart1» ⊆ «plOverlap» ∧ "+
						"subring(field_ring(L), «plChart0») ∧ "+
						"subring(field_ring(L), «plChart1») ∧ "+
						"subring(field_ring(L), «plOverlap») ∧ "+
						"t ∈ «plChart0» ∧ "+
						"L.inv(t) ∈ «plChart1» ∧ "+
						"L.inv(t) ∈ «plOverlap» ∧ "+
						"module_on(«plScalars», «plField») ∧ "+
						"module_on(«plRing0», «plField») ∧ "+
						"module_on(«plRing1», «plField») ∧ "+
						"module_on(«plRing», «plField»)",
					By(subfield, tInL, nonzero, projective_line.LineDatum.Read(L).At(k, tm))),
				lineDatumConjuncts...)
			scalarField := a.Have(
				"k, a subfield of L, is a field under the operations of its scalar ring, with L's inverse",
				"ring_subfield(«plScalars», L.inv, k)",
				By(
					subfield,
					field.SubfieldRingSubfield.Read(L).At(k, overlap),
					field.RingSubfieldRestrict.At(ring, k, inv, k)))

			a.Show(
				"by induction on the finite set E, one member at a time",
				ByInduction(finite_set.FiniteInductFresh, finiteE, Generalizing(independent),
					Case(
						"along ∅ the only section is zero, with the empty basis",
						Derive(func(b *Argument) {
							b.Assume()
							empty := b.TermAs[Set[A]]("∅")
							chart := b.Have(
								"chart 0 along ∅ is the k[t]-span of ∅",
								"fst(«plFreePairEmpty») = module_span(«plRing0», «plField», ∅)",
								Unfold(ProjectiveLineFreePairDef),
								By(pairs.Fst))
							spanZero := b.Have(
								"which is zero alone, {zero} being a submodule",
								"module_span(«plRing0», «plField», ∅) ⊆ {L.zero}",
								By(
									submodule.ZeroSubmodule.Read(line[12]),
									set_order.EmptySubset.At(b.TermAs[Set[A]]("{L.zero}")),
									submodule.SpanLeast.At(
										b.TermAs[module_record.RingOps[A]]("«plRing0»"), V, empty, b.TermAs[Set[A]]("{L.zero}"))))
							pair := b.Have(
								"the free pair along ∅ is a lattice pair",
								"lattice_pair(«plRing», «plChart0», «plChart1», «plField», «plFreePairEmpty»)",
								By(
									subfield,
									tInL,
									nonzero,
									set_order.EmptySubset.At(b.TermAs[Set[A]]("L.carrier")),
									FreeLinePairIsLattice.Read(L).At(k, tm, empty, N)))
							sections := b.Have(
								"its sections form a subspace over k",
								"submodule(«plScalars», «plField», fst(«plFreePairEmpty») ∩ snd(«plFreePairEmpty»))",
								By(
									pair,
									line[1],
									line[2],
									lattice_pair.H0Submodule.At(
										ring, chart0, chart1, k, V, b.TermAs[Prod[Set[A], Set[A]]]("«plFreePairEmpty»"))))
							zeroIn := b.Have(
								"holding zero",
								"L.zero ∈ fst(«plFreePairEmpty») ∩ snd(«plFreePairEmpty»)",
								By(submodule.SubmoduleZero.Read(sections)))
							onlyZero := b.Have(
								"so the sections along ∅ are zero alone",
								"fst(«plFreePairEmpty») ∩ snd(«plFreePairEmpty») = {L.zero}",
								BySets(chart, spanZero, zeroIn))
							zeroDim := b.Have(
								"and the zero subspace has dimension zero",
								"finite_dimensional(«plScalars», restrict_module(«plField», {L.zero})) ∧ "+
									"module_dim(«plScalars», restrict_module(«plField», {L.zero})) = 0",
								By(scalarField, line[11], module_dimension.ZeroSubmoduleDim.At(scalars, inv, V)))
							b.Show(
								"so H⁰ along ∅ is finite-dimensional of dimension zero, the empty sum",
								Simp(Fwd(lattice_pair.LatticePairH0DimDef), Fwd(lattice_pair.LatticePairH0Def)),
								onlyZero.Rw(),
								By(zeroDim, int_sum.IntSumClauses))
						})),
					Case(
						"adding e to D splits off e · O(N(e)), whose H⁰ adds max(N(e) + 1, 0)",
						Derive(func(b *Argument) {
							e, D := b.FixAs[A]("e"), b.FixAs[Set[A]]("D")
							step := b.Conjuncts(
								b.Assume(),
								"H⁰ along D is counted once D is independent",
								"e is not in D",
								"D is finite")
							independentIns := b.Assume()
							insertD := b.TermAs[Set[A]]("insert(e, D)")
							freeD, freeIns :=
								b.TermAs[Prod[Set[A], Set[A]]]("«plFreePairD»"),
								b.TermAs[Prod[Set[A], Set[A]]]("«plFreePairInsertD»")
							scaledE, lineE :=
								b.TermAs[Prod[Set[A], Set[A]]]("«plScaledPairAtE»"), b.TermAs[Prod[Set[A], Set[A]]]("«plPairAtE»")
							twist := b.TermAs[Int]("N(e)")
							independentD := b.Have(
								"D is independent over k[t], lying in insert(e, D)",
								"module_independent(«plRing0», «plField», D)",
								By(
									independentIns,
									b.Have(
										"D lies in insert(e, D)",
										"D ⊆ insert(e, D)",
										BySets()),
									linear_independence.IndependentSubset.At(
										b.TermAs[module_record.RingOps[A]]("«plRing0»"), V, insertD, D)))
							hypothesis := b.Conjuncts(
								b.Have(
									"so H⁰ along D is counted",
									"finite_dimensional(«plScalars», lattice_pair_h0(«plField», «plFreePairD»)) ∧ "+
										"int_of_num(lattice_pair_h0_dim(«plRing», k, «plField», «plFreePairD»)) = "+
										"int_sum(D, λe:A. int_max(N(e) + &1, &0))",
									By(step[0], independentD)),
								"H⁰ along D is finite-dimensional",
								"of dimension Σ_{x∈D} max(N(x) + 1, 0)")
							inL := b.Have(
								"insert(e, D) lies in L",
								"insert(e, D) ⊆ L.carrier",
								By(linear_independence.IndependentInCarrier.Read(independentIns)))
							inParts := b.Conjuncts(
								b.Have(
									"so e and D lie in L",
									"e ∈ L.carrier ∧ D ⊆ L.carrier",
									By(inL, set_order.InsertSubset.At(D, b.TermAs[Set[A]]("L.carrier"), e))),
								"e lies in L",
								"D lies in L")
							em := b.MemberOf[on.L](e, inParts[0])
							eNonzero := b.Have(
								"e is not zero, a member of an independent set",
								"e ≠ L.zero",
								BySets(b.Have(
									"zero is not in insert(e, D)",
									"L.zero ∉ insert(e, D)",
									By(
										independentIns,
										field.OneNotZeroOn.Read(L),
										linear_independence.IndependentZeroNotIn.Read(line[12]).At(insertD)))))

							// The free pair along insert(e, D) is e · O(N(e)) ⊕ the free pair along D, three lattice pairs.
							split := b.Have(
								"the free pair along insert(e, D) is the direct sum of e · O(N(e)) and the free pair along D",
								"fst(«plFreePairInsertD») = set_mul(L.add, fst(«plScaledPairAtE»), fst(«plFreePairD»)) ∧ "+
									"snd(«plFreePairInsertD») = set_mul(L.add, snd(«plScaledPairAtE»), snd(«plFreePairD»)) ∧ "+
									"«plAmbientOf»(«plScaledPairAtE») ∩ «plAmbientOf»(«plFreePairD») ⊆ {L.zero}",
								By(subfield, tInL, nonzero, step[1], independentIns, Read(FreeLinePairSplit, L).At(k, t, e, D, N)))
							pairIns := b.Have(
								"the free pair along insert(e, D) is a lattice pair",
								"lattice_pair(«plRing», «plChart0», «plChart1», «plField», «plFreePairInsertD»)",
								By(subfield, tInL, nonzero, inL, FreeLinePairIsLattice.Read(L).At(k, tm, insertD, N)))
							pairD := b.Have(
								"so is the free pair along D",
								"lattice_pair(«plRing», «plChart0», «plChart1», «plField», «plFreePairD»)",
								By(subfield, tInL, nonzero, inParts[1], FreeLinePairIsLattice.Read(L).At(k, tm, D, N)))
							lineLattice := b.Have(
								"O(N(e)) is a lattice pair",
								"lattice_pair(«plRing», «plChart0», «plChart1», «plField», «plPairAtE»)",
								By(subfield, tInL, nonzero, projective_line.LinePairIsLattice.Read(L).At(k, tm, twist)))
							pairScaled := b.Have(
								"and so is e · O(N(e)), e being nonzero",
								"lattice_pair(«plRing», «plChart0», «plChart1», «plField», «plScaledPairAtE»)",
								By(
									b.Have(
										"the charts of O(N(e)) lie in L",
										"fst(«plPairAtE») ⊆ L.carrier ∧ snd(«plPairAtE») ⊆ L.carrier",
										By(b.Unfolded(lineLattice, lattice_pair.LatticePairDef), submodule.SubmoduleSubset)),
									lineLattice,
									comm_ring.SubringSubset.Read(line[7]),
									line[0],
									eNonzero,
									invertible_lattice_pair.ScaleIsLattice.Read(L).At(chart0, chart1, overlap, t, em, lineE)))

							// So H⁰ adds.
							scaledH0 := b.Conjuncts(
								b.Have(
									"H⁰(e · O(N(e))) is finite of dimension max(N(e) + 1, 0)",
									"finite_dimensional(«plScalars», lattice_pair_h0(«plField», «plScaledPairAtE»)) ∧ "+
										"int_of_num(lattice_pair_h0_dim(«plRing», k, «plField», «plScaledPairAtE»)) = "+
										"int_max(N(e) + &1, &0)",
									By(
										subfield,
										tInL,
										transcendental,
										inParts[0],
										eNonzero,
										Read(ScaledLineH0Dim, L).At(k, t, e, twist))),
								"H⁰(e · O(N(e))) is finite",
								"of dimension max(N(e) + 1, 0)")
							summed := b.Conjuncts(
								b.Have(
									"so H⁰ along insert(e, D) is finite, its dimension that of H⁰(e · O(N(e))) plus that along D",
									"finite_dimensional(«plScalars», lattice_pair_h0(«plField», «plFreePairInsertD»)) ∧ "+
										"lattice_pair_h0_dim(«plRing», k, «plField», «plFreePairInsertD») = "+
										"lattice_pair_h0_dim(«plRing», k, «plField», «plScaledPairAtE») + "+
										"lattice_pair_h0_dim(«plRing», k, «plField», «plFreePairD»)",
									By(
										At(
											lattice_pair.DirectSumH0,
											ring,
											chart0,
											chart1,
											t,
											b.TermAs[A]("L.inv(t)"),
											k,
											inv,
											V,
											freeIns,
											scaledE,
											freeD),
										line[0],
										subfield,
										field.SubfieldRingSubfield.Read(L).At(k, overlap),
										line[1],
										line[2],
										pairIns,
										pairScaled,
										pairD,
										split,
										scaledH0[0],
										hypothesis[0])),
								"H⁰ along insert(e, D) is finite",
								"its dimension adds")
							sumIns := b.Have(
								"the sum over insert(e, D) is the term at e plus the sum over D",
								"int_sum(insert(e, D), λx:A. int_max(N(x) + &1, &0)) = "+
									"int_max(N(e) + &1, &0) + int_sum(D, λx:A. int_max(N(x) + &1, &0))",
								By(step[1], step[2], int_sum.IntSumClauses))
							b.Show(
								"so H⁰ along insert(e, D) is counted",
								SplitConj(Case(
									"finite, as the direct sum is",
									By(summed[0])),
									Case(
										"of dimension max(N(e) + 1, 0) + Σ_{x∈D} max(N(x) + 1, 0)",
										ByArith(summed[1], scaledH0[1], hypothesis[1], sumIns))))
						})),
				))
		}),
})}

// ScaledLinePairH1Dim — for e ≠ zero in the field, H¹(e · O(n)) is finite of
// dimension max(−n − 1, 0), as H¹(O(n)) is: multiplication by e is an
// isomorphism of lattice pairs O(n) → e · O(n)
// (invertible_lattice_pair.ScaleIsomorphism), and isomorphic pairs have the
// same h¹ (lattice_pair_map.IsomorphismSameEuler), O(n) having finite
// cohomology (projective_line.LineEuler).
var ScaledLinePairH1Dim = scaledLinePairH1DimThm{family.Add(registry.ProofEntry{
	Name: "ScaledLinePairH1Dim",
	Key:  "prop_ac4b1a9bc2f73422",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀t e:A. ∀n:int.",
		Hypotheses: []string{
			"subfield(L, k)",
			"t ∈ L.carrier",
			"¬algebraic_over(L, k, t)",
			"e ∈ L.carrier",
			"e ≠ L.zero",
		},
		Conclusion: "finite_dimensional(«plScalars», " +
			"    lattice_pair_h1(«plRing», «plField», «plScaledPairN»)) ∧ " +
			"int_of_num(lattice_pair_h1_dim(«plRing», k, «plField», «plScaledPairN»)) = max(-n - &1, &0)",
	},
		func(a *Argument, L field.FieldFact[on.L], k *Expr[Set[A]], t, e *Expr[A], n *Expr[Int], h Fact) {
			given := a.Conjuncts(
				h,
				"k is a subfield of L",
				"t lies in L",
				"t is transcendental over k",
				"e lies in L",
				"e is not zero")
			subfield, tInL, transcendental, eL, eNonzero := given[0], given[1], given[2], given[3], given[4]
			tm, em := a.MemberOf[on.L](t, tInL), a.MemberOf[on.L](e, eL)
			chart0, chart1, overlap :=
				a.TermAs[Set[A]]("«plChart0»"), a.TermAs[Set[A]]("«plChart1»"), a.TermAs[Set[A]]("«plOverlap»")
			V := a.TermAs[module_record.ModuleOps[A, A]]("«plField»")
			ring := a.TermAs[module_record.RingOps[A]]("«plRing»")
			inv := a.TermAs[Fun[A, A]]("L.inv")
			pair, scaled :=
				a.TermAs[Prod[Set[A], Set[A]]]("«plPairN»"), a.TermAs[Prod[Set[A], Set[A]]]("«plScaledPairN»")
			scaling := a.TermAs[Fun[A, A]]("λx:A. COND(x ∈ «plAmbientOf»(«plPairN»), e * x, L.zero)")
			nonzero := a.Have(
				"t, transcendental over k, is not zero",
				"t ≠ L.zero",
				By(h, algebraic_element.TranscendentalInverse.Read(L).At(k, tm)))
			line := a.Conjuncts(
				a.Have(
					"the line's datum",
					"biaffine(«plRing», «plChart0», «plChart1», t, L.inv(t)) ∧ "+
						"k ⊆ «plChart0» ∧ "+
						"k ⊆ «plChart1» ∧ "+
						"«plChart0» ⊆ «plOverlap» ∧ "+
						"«plChart1» ⊆ «plOverlap» ∧ "+
						"subring(field_ring(L), «plChart0») ∧ "+
						"subring(field_ring(L), «plChart1») ∧ "+
						"subring(field_ring(L), «plOverlap») ∧ "+
						"t ∈ «plChart0» ∧ "+
						"L.inv(t) ∈ «plChart1» ∧ "+
						"L.inv(t) ∈ «plOverlap» ∧ "+
						"module_on(«plScalars», «plField») ∧ "+
						"module_on(«plRing0», «plField») ∧ "+
						"module_on(«plRing1», «plField») ∧ "+
						"module_on(«plRing», «plField»)",
					By(subfield, tInL, nonzero, projective_line.LineDatum.Read(L).At(k, tm))),
				lineDatumConjuncts...)
			lattice := a.Have(
				"O(n) is a lattice pair on the line",
				"lattice_pair(«plRing», «plChart0», «plChart1», «plField», «plPairN»)",
				By(subfield, tInL, nonzero, projective_line.LinePairIsLattice.Read(L).At(k, tm, n)))
			isomorphic := a.Have(
				"multiplication by e carries O(n) isomorphically onto e · O(n)",
				"lattice_pair_isomorphism(«plRing», "+
					"    «plField», "+
					"    «plPairN», "+
					"    «plField», "+
					"    «plScaledPairN», "+
					"    λx:A. COND(x ∈ «plAmbientOf»(«plPairN»), e * x, L.zero))",
				By(
					comm_ring.SubringSubset.Read(line[7]),
					line[0],
					eNonzero,
					lattice,
					invertible_lattice_pair.ScaleIsomorphism.Read(L).At(chart0, chart1, overlap, t, em, pair)))
			finiteO := a.Have(
				"O(n) has finite cohomology",
				"lattice_pair_finite(«plRing», k, «plField», «plPairN»)",
				By(subfield, tInL, transcendental, projective_line.LineEuler.Read(L).At(k, tm, n)))
			same := a.Have(
				"isomorphic pairs have the same cohomology",
				"lattice_pair_finite(«plRing», k, «plField», «plScaledPairN») ∧ "+
					"lattice_pair_h1_dim(«plRing», k, «plField», «plPairN») = "+
					"lattice_pair_h1_dim(«plRing», k, «plField», «plScaledPairN»)",
				By(
					line[0],
					line[1],
					line[2],
					lattice,
					isomorphic,
					finiteO,
					subfield,
					field.SubfieldRingSubfield.Read(L).At(k, overlap),
					lattice_pair_map.IsomorphismSameEuler.At(
						ring, chart0, chart1, t, a.TermAs[A]("L.inv(t)"), k, inv, V, V, pair, scaled, scaling)))
			a.Show(
				"so H¹(e · O(n)) is finite, of the dimension of H¹(O(n))",
				By(
					same,
					lattice_pair.LatticePairFiniteDef,
					subfield,
					tInL,
					transcendental,
					projective_line.LineH1Dim.Read(L).At(k, tm, n)))
		}),
})}

// FreeLinePairH1Dim — dim H¹ of a free pair is the sum of the
// dim H¹(O(N(e))), by induction on E: along ∅ the ambient is zero and H¹
// with it, and adding e to D splits off e · O(N(e)) as a direct summand
// (FreeLinePairSplit), H¹ of a direct sum adding (lattice_pair.DirectSumH1),
// and H¹(e · O(N(e))) has the dimension of H¹(O(N(e))) (ScaledLinePairH1Dim).
var FreeLinePairH1Dim = freeLinePairH1DimThm{family.Add(registry.ProofEntry{
	Name:    "FreeLinePairH1Dim",
	Key:     "prop_7cc3f97429db4f9f",
	Reading: "E finite is load-bearing: infinitely many e with N(e) ≤ −2 make H¹ infinite-dimensional.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀t:A. ∀E:set(A). ∀N:(A → int).",
		Hypotheses: []string{
			"subfield(L, k)",
			"t ∈ L.carrier",
			"¬algebraic_over(L, k, t)",
			"finite(E)",
			"module_independent(restrict_ring(field_ring(L), «plChart0»), «plField», E)",
		},
		Conclusion: "finite_dimensional(«plScalars», " +
			"    lattice_pair_h1(«plRing», «plField», «plFreePair»)) ∧ " +
			"int_of_num(lattice_pair_h1_dim(«plRing», k, «plField», «plFreePair»)) = " +
			"int_sum(E, λe:A. int_max(-N(e) - &1, &0))",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k *Expr[Set[A]],
			t *Expr[A],
			E *Expr[Set[A]],
			N *Arrow[A, Int],
			h Fact,
		) {
			given := a.Conjuncts(
				h,
				"k is a subfield of L",
				"t lies in L",
				"t is transcendental over k",
				"E is finite",
				"E is independent over k[t]")
			subfield, tInL, transcendental, finiteE, independent :=
				given[0], given[1], given[2], given[3], given[4]
			tm := a.MemberOf[on.L](t, tInL)
			scalars, ring, ring0 :=
				a.TermAs[module_record.RingOps[A]]("«plScalars»"),
				a.TermAs[module_record.RingOps[A]]("«plRing»"),
				a.TermAs[module_record.RingOps[A]]("«plRing0»")
			V := a.TermAs[module_record.ModuleOps[A, A]]("«plField»")
			inv := a.TermAs[Fun[A, A]]("L.inv")
			chart0, chart1, overlap :=
				a.TermAs[Set[A]]("«plChart0»"), a.TermAs[Set[A]]("«plChart1»"), a.TermAs[Set[A]]("«plOverlap»")
			nonzero := a.Have(
				"t, transcendental over k, is not zero",
				"t ≠ L.zero",
				By(h, algebraic_element.TranscendentalInverse.Read(L).At(k, tm)))
			line := a.Conjuncts(
				a.Have(
					"the line's datum",
					"biaffine(«plRing», «plChart0», «plChart1», t, L.inv(t)) ∧ "+
						"k ⊆ «plChart0» ∧ "+
						"k ⊆ «plChart1» ∧ "+
						"«plChart0» ⊆ «plOverlap» ∧ "+
						"«plChart1» ⊆ «plOverlap» ∧ "+
						"subring(field_ring(L), «plChart0») ∧ "+
						"subring(field_ring(L), «plChart1») ∧ "+
						"subring(field_ring(L), «plOverlap») ∧ "+
						"t ∈ «plChart0» ∧ "+
						"L.inv(t) ∈ «plChart1» ∧ "+
						"L.inv(t) ∈ «plOverlap» ∧ "+
						"module_on(«plScalars», «plField») ∧ "+
						"module_on(«plRing0», «plField») ∧ "+
						"module_on(«plRing1», «plField») ∧ "+
						"module_on(«plRing», «plField»)",
					By(subfield, tInL, nonzero, projective_line.LineDatum.Read(L).At(k, tm))),
				lineDatumConjuncts...)
			scalarField := a.Have(
				"k, a subfield of L, is a field under the operations of its scalar ring, with L's inverse",
				"ring_subfield(«plScalars», L.inv, k)",
				By(
					subfield,
					field.SubfieldRingSubfield.Read(L).At(k, overlap),
					field.RingSubfieldRestrict.At(ring, k, inv, k)))

			a.Show(
				"by induction on the finite set E, one member at a time",
				ByInduction(finite_set.FiniteInductFresh, finiteE, Generalizing(independent),
					Case(
						"along ∅ the ambient is zero, and so is H¹",
						Derive(func(b *Argument) {
							b.Assume()
							empty, zeroSet := b.TermAs[Set[A]]("∅"), b.TermAs[Set[A]]("{L.zero}")
							emptyPair := b.TermAs[Prod[Set[A], Set[A]]]("«plFreePairEmpty»")
							ambient, charts :=
								b.TermAs[Set[A]]("«plAmbientOf»(«plFreePairEmpty»)"),
								b.TermAs[Set[A]]("set_mul(L.add, fst(«plFreePairEmpty»), snd(«plFreePairEmpty»))")
							emptyInL := b.Have(
								"∅ lies in L",
								"∅ ⊆ L.carrier",
								BySets())
							lattice := b.Have(
								"the free pair along ∅ is a lattice pair",
								"lattice_pair(«plRing», «plChart0», «plChart1», «plField», «plFreePairEmpty»)",
								By(subfield, tInL, nonzero, emptyInL, FreeLinePairIsLattice.Read(L).At(k, tm, empty, N)))
							modules := b.Conjuncts(
								b.Have(
									"its ambient and chart sum are k-subspaces, the one inside the other, and H¹ a vector space over k",
									"submodule(«plScalars», «plField», «plAmbientOf»(«plFreePairEmpty»)) ∧ "+
										"submodule(«plScalars», "+
										"    «plField», "+
										"    set_mul(L.add, fst(«plFreePairEmpty»), snd(«plFreePairEmpty»))) ∧ "+
										"set_mul(L.add, fst(«plFreePairEmpty»), snd(«plFreePairEmpty»)) ⊆ "+
										"«plAmbientOf»(«plFreePairEmpty») ∧ "+
										"module_on(«plScalars», lattice_pair_h1(«plRing», «plField», «plFreePairEmpty»))",
									By(subfield, tInL, nonzero, lattice, Read(projective_line.LineH1Module, L).At(k, t, V, emptyPair))),
								"the ambient is a k-subspace",
								"the chart sum is a k-subspace",
								"the chart sum lies in the ambient",
								"H¹ is a vector space over k")
							emptyInZero := b.Have(
								"∅ lies in {zero}",
								"∅ ⊆ {L.zero}",
								BySets())
							chartEmpty := b.Have(
								"chart 0 along ∅ is zero",
								"fst(«plFreePairEmpty») ⊆ {L.zero}",
								Simp(Fwd(ProjectiveLineFreePairDef), Fwd(pairs.Fst)),
								By(
									emptyInZero,
									submodule.ZeroSubmodule.Read(line[12]),
									submodule.SpanLeast.At(ring0, V, empty, zeroSet)))
							ambientZero := b.Have(
								"so its ambient is zero",
								"«plAmbientOf»(«plFreePairEmpty») ⊆ {L.zero}",
								Simp(Fwd(lattice_pair.LatticePairAmbientDef)),
								By(
									chartEmpty,
									submodule.ZeroSubmodule.Read(line[14]),
									submodule.SpanLeast.At(ring, V, b.TermAs[Set[A]]("fst(«plFreePairEmpty»)"), zeroSet)))
							spanZero := b.Have(
								"the k-span of ∅ is zero",
								"module_span(«plScalars», «plField», ∅) ⊆ {L.zero}",
								By(
									emptyInZero,
									submodule.ZeroSubmodule.Read(line[11]),
									submodule.SpanLeast.At(scalars, V, empty, zeroSet)))
							sumHolds := b.Have(
								"the chart sum lies in the k-span of ∅ plus the chart sum, both k-subspaces",
								"set_mul(L.add, fst(«plFreePairEmpty»), snd(«plFreePairEmpty»)) ⊆ "+
									"set_mul(L.add, "+
									"    module_span(«plScalars», «plField», ∅), "+
									"    set_mul(L.add, fst(«plFreePairEmpty»), snd(«plFreePairEmpty»)))",
								By(
									submodule.SumContainsRight.Read(line[11]).At(
										b.TermAs[Set[A]]("module_span(«plScalars», «plField», ∅)"), charts),
									emptyInL,
									submodule.SpanSubmodule.Read(line[11]).At(empty),
									modules[1]))
							spanned := b.Have(
								"so the ambient, zero, lies there too, the chart sum holding zero",
								"«plAmbientOf»(«plFreePairEmpty») ⊆ "+
									"set_mul(L.add, "+
									"    module_span(«plScalars», «plField», ∅), "+
									"    set_mul(L.add, fst(«plFreePairEmpty»), snd(«plFreePairEmpty»)))",
								BySets(ambientZero, submodule.SubmoduleZero.Read(modules[1]), sumHolds))
							counted := b.Have(
								"the empty complement counts H¹ along ∅: it is zero",
								"finite_dimensional(«plScalars», "+
									"    quotient_module(restrict_module(«plField», «plAmbientOf»(«plFreePairEmpty»)), "+
									"        set_mul(L.add, fst(«plFreePairEmpty»), snd(«plFreePairEmpty»)))) ∧ "+
									"module_dim(«plScalars», "+
									"    quotient_module(restrict_module(«plField», «plAmbientOf»(«plFreePairEmpty»)), "+
									"        set_mul(L.add, fst(«plFreePairEmpty»), snd(«plFreePairEmpty»)))) = "+
									"card⟨A:A⟩(∅)",
								By(
									scalarField,
									line[11],
									modules[0],
									modules[1],
									modules[2],
									finite_set.FiniteRules,
									b.Have(
										"∅ lies in the ambient",
										"∅ ⊆ «plAmbientOf»(«plFreePairEmpty»)",
										BySets()),
									linear_independence.IndependentEmpty.At(scalars, V),
									spanned,
									b.Have(
										"the k-span of ∅ meets the chart sum only in zero",
										"module_span(«plScalars», «plField», ∅) ∩ "+
											"set_mul(L.add, fst(«plFreePairEmpty»), snd(«plFreePairEmpty»)) ⊆ "+
											"{L.zero}",
										BySets(spanZero)),
									module_dimension.QuotientComplementDim.At(scalars, V, inv, ambient, charts, empty)))
							b.Show(
								"an empty sum is zero",
								Simp(Fwd(lattice_pair.LatticePairH1DimDef), Fwd(lattice_pair.LatticePairH1Def)),
								By(counted, cardinality.CardClauses, int_sum.IntSumClauses))
						})),
					Case(
						"adding e to D splits off e · O(N(e)), whose H¹ adds max(−N(e) − 1, 0)",
						Derive(func(b *Argument) {
							e, D := b.FixAs[A]("e"), b.FixAs[Set[A]]("D")
							step := b.Conjuncts(
								b.Assume(),
								"H¹ along D is counted once D is independent",
								"e is not in D",
								"D is finite")
							independentIns := b.Assume()
							insertD := b.TermAs[Set[A]]("insert(e, D)")
							freeD, freeIns :=
								b.TermAs[Prod[Set[A], Set[A]]]("«plFreePairD»"),
								b.TermAs[Prod[Set[A], Set[A]]]("«plFreePairInsertD»")
							scaledE, lineE :=
								b.TermAs[Prod[Set[A], Set[A]]]("«plScaledPairAtE»"), b.TermAs[Prod[Set[A], Set[A]]]("«plPairAtE»")
							twist := b.TermAs[Int]("N(e)")
							independentD := b.Have(
								"D is independent over k[t], lying in insert(e, D)",
								"module_independent(«plRing0», «plField», D)",
								By(
									independentIns,
									b.Have(
										"D lies in insert(e, D)",
										"D ⊆ insert(e, D)",
										BySets()),
									linear_independence.IndependentSubset.At(ring0, V, insertD, D)))
							hypothesis := b.Conjuncts(
								b.Have(
									"so H¹ along D is counted",
									"finite_dimensional(«plScalars», lattice_pair_h1(«plRing», «plField», «plFreePairD»)) ∧ "+
										"int_of_num(lattice_pair_h1_dim(«plRing», k, «plField», «plFreePairD»)) = "+
										"int_sum(D, λe:A. int_max(-N(e) - &1, &0))",
									By(step[0], independentD)),
								"H¹ along D is finite-dimensional",
								"of dimension Σ_{x∈D} max(−N(x) − 1, 0)")
							inL := b.Have(
								"insert(e, D) lies in L",
								"insert(e, D) ⊆ L.carrier",
								By(linear_independence.IndependentInCarrier.Read(independentIns)))
							inParts := b.Conjuncts(
								b.Have(
									"so e and D lie in L",
									"e ∈ L.carrier ∧ D ⊆ L.carrier",
									By(inL, set_order.InsertSubset.At(D, b.TermAs[Set[A]]("L.carrier"), e))),
								"e lies in L",
								"D lies in L")
							em := b.MemberOf[on.L](e, inParts[0])
							eNonzero := b.Have(
								"e is not zero, a member of an independent set",
								"e ≠ L.zero",
								BySets(b.Have(
									"zero is not in insert(e, D)",
									"L.zero ∉ insert(e, D)",
									By(
										independentIns,
										field.OneNotZeroOn.Read(L),
										linear_independence.IndependentZeroNotIn.Read(line[12]).At(insertD)))))

							// The free pair along insert(e, D) is e · O(N(e)) ⊕ the free pair along D, three lattice pairs.
							split := b.Have(
								"the free pair along insert(e, D) is the direct sum of e · O(N(e)) and the free pair along D",
								"fst(«plFreePairInsertD») = set_mul(L.add, fst(«plScaledPairAtE»), fst(«plFreePairD»)) ∧ "+
									"snd(«plFreePairInsertD») = set_mul(L.add, snd(«plScaledPairAtE»), snd(«plFreePairD»)) ∧ "+
									"«plAmbientOf»(«plScaledPairAtE») ∩ «plAmbientOf»(«plFreePairD») ⊆ {L.zero}",
								By(subfield, tInL, nonzero, step[1], independentIns, Read(FreeLinePairSplit, L).At(k, t, e, D, N)))
							pairIns := b.Have(
								"the free pair along insert(e, D) is a lattice pair",
								"lattice_pair(«plRing», «plChart0», «plChart1», «plField», «plFreePairInsertD»)",
								By(subfield, tInL, nonzero, inL, FreeLinePairIsLattice.Read(L).At(k, tm, insertD, N)))
							pairD := b.Have(
								"so is the free pair along D",
								"lattice_pair(«plRing», «plChart0», «plChart1», «plField», «plFreePairD»)",
								By(subfield, tInL, nonzero, inParts[1], FreeLinePairIsLattice.Read(L).At(k, tm, D, N)))
							lineLattice := b.Have(
								"O(N(e)) is a lattice pair",
								"lattice_pair(«plRing», «plChart0», «plChart1», «plField», «plPairAtE»)",
								By(subfield, tInL, nonzero, projective_line.LinePairIsLattice.Read(L).At(k, tm, twist)))
							pairScaled := b.Have(
								"and so is e · O(N(e)), e being nonzero",
								"lattice_pair(«plRing», «plChart0», «plChart1», «plField», «plScaledPairAtE»)",
								By(
									b.Have(
										"the charts of O(N(e)) lie in L",
										"fst(«plPairAtE») ⊆ L.carrier ∧ snd(«plPairAtE») ⊆ L.carrier",
										By(b.Unfolded(lineLattice, lattice_pair.LatticePairDef), submodule.SubmoduleSubset)),
									lineLattice,
									comm_ring.SubringSubset.Read(line[7]),
									line[0],
									eNonzero,
									invertible_lattice_pair.ScaleIsLattice.Read(L).At(chart0, chart1, overlap, t, em, lineE)))

							// So H¹ adds.
							scaledH1 := b.Conjuncts(
								b.Have(
									"H¹(e · O(N(e))) is finite of dimension max(−N(e) − 1, 0)",
									"finite_dimensional(«plScalars», lattice_pair_h1(«plRing», «plField», «plScaledPairAtE»)) ∧ "+
										"int_of_num(lattice_pair_h1_dim(«plRing», k, «plField», «plScaledPairAtE»)) = max(-N(e) - &1, &0)",
									By(
										subfield,
										tInL,
										transcendental,
										inParts[0],
										eNonzero,
										Read(ScaledLinePairH1Dim, L).At(k, t, e, twist))),
								"H¹(e · O(N(e))) is finite",
								"of dimension max(−N(e) − 1, 0)")
							summed := b.Conjuncts(
								b.Have(
									"so H¹ along insert(e, D) is finite, its dimension that of H¹(e · O(N(e))) plus that along D",
									"finite_dimensional(«plScalars», lattice_pair_h1(«plRing», «plField», «plFreePairInsertD»)) ∧ "+
										"lattice_pair_h1_dim(«plRing», k, «plField», «plFreePairInsertD») = "+
										"lattice_pair_h1_dim(«plRing», k, «plField», «plScaledPairAtE») + "+
										"lattice_pair_h1_dim(«plRing», k, «plField», «plFreePairD»)",
									By(
										At(
											lattice_pair.DirectSumH1,
											ring,
											chart0,
											chart1,
											t,
											b.TermAs[A]("L.inv(t)"),
											k,
											inv,
											V,
											freeIns,
											scaledE,
											freeD),
										line[0],
										subfield,
										field.SubfieldRingSubfield.Read(L).At(k, overlap),
										line[1],
										line[2],
										pairIns,
										pairScaled,
										pairD,
										split,
										scaledH1[0],
										hypothesis[0])),
								"H¹ along insert(e, D) is finite",
								"its dimension adds")
							sumIns := b.Have(
								"the sum over insert(e, D) is the term at e plus the sum over D",
								"int_sum(insert(e, D), λx:A. int_max(-N(x) - &1, &0)) = "+
									"int_max(-N(e) - &1, &0) + int_sum(D, λx:A. int_max(-N(x) - &1, &0))",
								By(step[1], step[2], int_sum.IntSumClauses))
							b.Show(
								"so H¹ along insert(e, D) is counted",
								SplitConj(Case(
									"finite, as the direct sum is",
									By(summed[0])),
									Case(
										"of dimension max(−N(e) − 1, 0) + Σ_{x∈D} max(−N(x) − 1, 0)",
										ByArith(summed[1], scaledH1[1], hypothesis[1], sumIns))))
						})),
				))
		}),
})}
