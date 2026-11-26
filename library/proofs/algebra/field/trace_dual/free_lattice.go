package trace_dual

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_extension"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_trace"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/functional_dual"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/linear_independence"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/linear_pairing"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/fractional_ideal"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// TraceDualFreeLattice — for a finite K-basis E of L whose trace pairing is
// nondegenerate, and a subring S of K: E has a trace-dual K-basis d(E), the
// trace dual of the S-span of E is the S-span of d(E), d(E) is an S-basis of
// it, and its trace dual is the S-span of E again. The nondegenerate pairing
// gives the dual basis d; the trace dual of an S-span is the trace dual of
// its generators; an element's d(E)-coefficients are its traces against E
// and its E-coordinates its traces against d(E), so each S-span is the trace
// dual of the other's generators.
var TraceDualFreeLattice = traceDualFreeLatticeThm{family.Add(registry.ProofEntry{
	Name: "TraceDualFreeLattice",
	Key:  "prop_c58cce20502fa109",
	Build: family.Sections(Statement{
		Binders: "∀L:field_on(A). ∀K S E:set(A).",
		Hypotheses: []string{
			"subfield(L, K)",
			"S ⊆ K",
			"subring(field_ring(L), S)",
			"finite(E)",
			"module_basis(«ScalarK», «Regular», E)",
			"∀x:A. x ∈ L.carrier ∧ x ≠ L.zero ⇒ ∃y:A. y ∈ L.carrier ∧ field_trace(L, K, x * y) ≠ L.zero",
		},
		Conclusion: "∃d:(A → A). " +
			"    (∀e:A. e ∈ E ⇒ d(e) ∈ L.carrier) ∧ " +
			"    (∀e f:A. e ∈ E ∧ f ∈ E ⇒ field_trace(L, K, d(e) * f) = COND(e = f, L.one, L.zero)) ∧ " +
			"    module_basis(«ScalarK», «Regular», image(d, E)) ∧ " +
			"    trace_dual(L, K, «latticeE», S) = module_span(«ScalarS», «Regular», image(d, E)) ∧ " +
			"    module_basis(«ScalarS», " +
			"        restrict_module(«Regular», trace_dual(L, K, «latticeE», S)), " +
			"        image(d, E)) ∧ " +
			"    trace_dual(L, K, trace_dual(L, K, «latticeE», S), S) = «latticeE»",
		Abbrev: Abbrev{
			{Name: "latticeE", Text: "module_span(«ScalarS», «Regular», E)"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		// The definition of the trace dual, read at one element.
		membership := ctx.Lemma("∀L:field_on(A). ∀K X S:set(A). ∀x:A. "+
			"    x ∈ trace_dual(L, K, X, S) ⇔ x ∈ L.carrier ∧ (∀y:A. y ∈ X ⇒ field_trace(L, K, x * y) ∈ S)",
			func(a *Argument, L field.FieldFact[on.L], K, X, S *Expr[Set[A]], x *Expr[A]) {
				a.Show(
					"the trace dual collects the elements of L whose traces against X lie in S",
					Simp(Fwd(TraceDualDef)),
					BySets())
			})

		// Field multiplication commutes, so trace duality is symmetric.
		symmetry := ctx.Lemma(Statement{
			Binders: "∀L:field_on(A). ∀K S X Y:set(A).",
			Hypotheses: []string{
				"Y ⊆ L.carrier",
				"X ⊆ trace_dual(L, K, Y, S)",
			},
			Conclusion: "Y ⊆ trace_dual(L, K, X, S)",
		}, func(a *Argument, L field.FieldFact[on.L], K, S, X, Y *Expr[Set[A]], given Fact) {
			parts := a.Conjuncts(
				given,
				"Y lies in L",
				"X lies in the trace dual of Y")
			yInL, xDual := parts[0], parts[1]
			a.Show(
				"every element of Y passes the tests against X",
				Unfold(set_basic.SubsetDef),
				Derive(func(b *Argument) {
					y := b.FixAs[A]("y")
					yIn := b.Assume()
					yMember := b.Have(
						"y lies in L",
						"y ∈ L.carrier",
						BySets(yIn, yInL))
					tests := b.Have(
						"its traces against X lie in S",
						"∀x:A. x ∈ X ⇒ field_trace(L, K, y * x) ∈ S",
						Derive(func(c *Argument) {
							x := c.FixAs[A]("x")
							xIn := c.Assume()
							inDual := c.Have(
								"x lies in the trace dual of Y",
								"x ∈ trace_dual(L, K, Y, S)",
								BySets(xIn, xDual))
							xTests := c.Have(
								"so x lies in L and its trace against y lies in S",
								"x ∈ L.carrier ∧ field_trace(L, K, x * y) ∈ S",
								By(inDual, yIn, Read(membership, L).At(K, Y, S, x)))
							commute := c.Have(
								"y and x commute",
								"y * x = x * y",
								ByArith(L, yMember, xTests))
							c.Show(
								"so the trace of y * x lies in S",
								commute.Rw(),
								By(xTests))
						}))
					b.Show(
						"so y lies in the trace dual of X",
						By(yMember, tests, Read(membership, L).At(K, X, S, y)))
				}))
		})

		spanTests := ctx.Lemma(Statement{
			Binders: "∀L:field_on(A). ∀K S F:set(A).",
			Hypotheses: []string{
				"subfield(L, K)",
				"finite_extension(L, K, L.carrier)",
				"S ⊆ K",
				"subring(field_ring(L), S)",
				"F ⊆ L.carrier",
			},
			Conclusion: "trace_dual(L, K, module_span(«ScalarS», «Regular», F), S) = trace_dual(L, K, F, S)",
		}, func(
			a *Argument,
			L field.FieldFact[on.L],
			K, S, F *Expr[Set[A]],
			subK, finite, sInK, subringS, fInL Fact,
		) {
			scalarsS := a.TermAs[module_record.RingOps[A]]("«ScalarS»")
			regular := a.TermAs[module_record.ModuleOps[A, A]]("«Regular»")
			span := a.TermAs[Set[A]]("module_span(«ScalarS», «Regular», F)")
			moduleS := a.Have(
				"L is a module over the ring on S",
				"module_on(«ScalarS», «Regular»)",
				By(subringS, fractional_ideal.FieldModuleOn.Read(L).At(S)))
			spanSubmodule := a.Have(
				"the span is an S-submodule",
				"submodule(«ScalarS», «Regular», module_span(«ScalarS», «Regular», F))",
				By(fInL, submodule.SpanSubmodule.Read(moduleS).At(F)))
			scalarSubmodule := a.Have(
				"S is an S-submodule of K",
				"submodule(«ScalarS», «VectorsK», S)",
				By(
					sInK,
					subringS,
					fractional_ideal.SubringSubmodule.Read(L).At(S),
					submodule.SubmoduleRestrict.At(scalarsS, regular, K, S)))
			a.Show(
				"the trace dual is the functional dual of the K-linear trace, which generators test",
				Simp(Fwd(TraceDualIsFunctionalDual)),
				By(
					subK,
					finite,
					sInK,
					subringS,
					spanSubmodule,
					scalarSubmodule,
					submodule.SubsetSpan.At(scalarsS, regular, F),
					linear_independence.SpanRestrict.Read(moduleS).At(span, F),
					field_trace.FieldTraceLinear.Read(L).At(K),
					functional_dual.FunctionalDualGenerators.Read(L).At(
						K, a.TermAs[Fun[A, A]]("field_trace(L, K)"), S, span, S, F)))
		})

		// The trace is a nonzero K-linear functional, so E has a trace-dual basis,
		// which expands each x by its traces against E.
		dualBasis := ctx.Lemma(Statement{
			Binders: "∀L:field_on(A). ∀K E:set(A).",
			Hypotheses: []string{
				"subfield(L, K)",
				"finite_extension(L, K, L.carrier)",
				"finite(E)",
				"module_basis(«ScalarK», «Regular», E)",
				"∀x:A. x ∈ L.carrier ∧ x ≠ L.zero ⇒ ∃y:A. y ∈ L.carrier ∧ field_trace(L, K, x * y) ≠ L.zero",
			},
			Conclusion: "∃d:(A → A). " +
				"    (∀e:A. e ∈ E ⇒ d(e) ∈ L.carrier) ∧ " +
				"    (∀e f:A. e ∈ E ∧ f ∈ E ⇒ field_trace(L, K, d(e) * f) = COND(e = f, L.one, L.zero)) ∧ " +
				"    module_basis(«ScalarK», «Regular», image(d, E)) ∧ " +
				"    (∀x:A. " +
				"        x ∈ L.carrier ⇒ x = module_sum(L.add, L.zero, E, λe:A. field_trace(L, K, x * e) * d(e)))",
		}, func(a *Argument, L field.FieldFact[on.L], K, E *Expr[Set[A]], given Fact) {
			parts := a.Conjuncts(
				given,
				"K is a subfield of L",
				"L is a finite extension of K",
				"E is finite",
				"E is a K-basis of L",
				"the trace pairing is nondegenerate")
			subK, finite, finiteE, basisE, nondegenerate := parts[0], parts[1], parts[2], parts[3], parts[4]
			ring := field.RingOn.Read(L)
			y, atOne := a.ObtainAs[A](
				"nondegeneracy at one gives a nonzero trace",
				"∃y:A. y ∈ L.carrier ∧ field_trace(L, K, L.one * y) ≠ L.zero",
				By(
					nondegenerate.At(a.TermAs[A]("L.one")),
					comm_ring.OneIn.Read(ring),
					field.OneNotZeroOn.At(a.TermAs[FieldOps[A]]("L"))))
			witness := a.Conjuncts(
				atOne,
				"y lies in L",
				"the trace at one times y is nonzero")
			oneTimes := a.Have(
				"one times y is y",
				"L.one * y = y",
				ByArith(L, witness[0]))
			nonzeroTrace := a.Have(
				"the trace is not identically zero",
				"∃x:A. x ∈ L.carrier ∧ field_trace(L, K, x) ≠ L.zero",
				Witness(y),
				By(Normalized, witness[0], witness[1], oneTimes))
			a.Show(
				"the trace is a nonzero K-linear functional, so E has a trace-dual K-basis",
				By(
					subK,
					finite,
					finiteE,
					basisE,
					nonzeroTrace,
					field_trace.FieldTraceLinear.Read(L).At(K),
					functional_dual.MultiplicationFunctionalDualBasis.Read(L).At(
						K, a.TermAs[Fun[A, A]]("field_trace(L, K)"), E)))
		})

		// The d(e)-coefficient of x is its trace against e: the S-span of the
		// d(e) is the trace dual of E.
		dualCoefficients := ctx.Lemma(Statement{
			Binders: "∀L:field_on(A). ∀K S E:set(A). ∀d:(A → A).",
			Hypotheses: []string{
				"subfield(L, K)",
				"finite_extension(L, K, L.carrier)",
				"S ⊆ K",
				"comm_ring_on(«ScalarS»)",
				"finite(E)",
				"E ⊆ L.carrier",
				"∀e:A. e ∈ E ⇒ d(e) ∈ L.carrier",
				"∀e f:A. e ∈ E ∧ f ∈ E ⇒ field_trace(L, K, d(e) * f) = COND(e = f, L.one, L.zero)",
				"∀x:A. x ∈ L.carrier ⇒ x = module_sum(L.add, L.zero, E, λe:A. field_trace(L, K, x * e) * d(e))",
			},
			Conclusion: "trace_dual(L, K, E, S) = module_span(«ScalarS», «Regular», image(d, E))",
		}, func(a *Argument, L field.FieldFact[on.L], K, S, E *Expr[Set[A]], d *Arrow[A, A], given Fact) {
			parts := a.Conjuncts(
				given,
				"K is a subfield of L",
				"L is a finite extension of K",
				"S lies in K",
				"S is a commutative ring under the field operations",
				"E is finite",
				"E lies in L",
				"the d(e) lie in L",
				"they are trace-dual to E",
				"they expand each x by its traces against E")
			subK, finite, sInK, ringS, finiteE, eInL, dualIn, delta, expansion :=
				parts[0], parts[1], parts[2], parts[3], parts[4], parts[5], parts[6], parts[7], parts[8]
			scalarsS := a.TermAs[module_record.RingOps[A]]("«ScalarS»")
			regular := a.TermAs[module_record.ModuleOps[A, A]]("«Regular»")
			duals := a.TermAs[Set[A]]("image(d, E)")
			dualSpan := a.TermAs[Set[A]]("module_span(«ScalarS», «Regular», image(d, E))")
			kInL := a.Have(
				"K lies in L",
				"K ⊆ L.carrier",
				By(field.SubfieldSubset.Read(subK)))
			sInL := a.Have(
				"so does S",
				"S ⊆ L.carrier",
				BySets(sInK, kInL))
			subringS := a.Have(
				"so S is a subring of L",
				"subring(field_ring(L), S)",
				By(sInL, ringS, comm_ring.SubringRingOn.Read(field.RingOn.Read(L)).At(S)))
			moduleS := a.Have(
				"L is a module over the ring on S",
				"module_on(«ScalarS», «Regular»)",
				By(subringS, fractional_ideal.FieldModuleOn.Read(L).At(S)))
			dualsInL := a.Have(
				"the d(e) lie in L",
				"image(d, E) ⊆ L.carrier",
				BySets(dualIn))
			subSpan := a.Have(
				"they span an S-submodule of L",
				"submodule(«ScalarS», «Regular», module_span(«ScalarS», «Regular», image(d, E)))",
				By(dualsInL, submodule.SpanSubmodule.Read(moduleS).At(duals)))
			spanInL := a.Have(
				"which lies in L",
				"module_span(«ScalarS», «Regular», image(d, E)) ⊆ L.carrier",
				By(submodule.SubmoduleSubset.Read(subSpan)))
			generators := a.Have(
				"the span contains each d(e)",
				"image(d, E) ⊆ module_span(«ScalarS», «Regular», image(d, E))",
				By(submodule.SubsetSpan.At(scalarsS, regular, duals)))
			constants := a.Have(
				"one and zero lie in S",
				"L.one ∈ S ∧ L.zero ∈ S",
				By(comm_ring.OneIn.Read(ringS), comm_ring.ZeroIn.Read(ringS)))
			deltaInS := a.Have(
				"so the traces of the d(e) against E lie in S",
				"∀e f:A. e ∈ E ∧ f ∈ E ⇒ field_trace(L, K, d(e) * f) ∈ S",
				By(constants, delta))
			dualTests := a.Have(
				"so the d(e) lie in the trace dual of E",
				"image(d, E) ⊆ trace_dual(L, K, E, S)",
				Simp(Fwd(TraceDualDef)),
				BySets(dualIn, deltaInS))
			eTests := a.Have(
				"by symmetry E lies in the trace dual of the d(e)",
				"E ⊆ trace_dual(L, K, image(d, E), S)",
				By(eInL, dualTests, Read(symmetry, L).At(K, S, duals, E)))
			spanDual := a.Have(
				"whose S-span has the same trace dual",
				"trace_dual(L, K, module_span(«ScalarS», «Regular», image(d, E)), S) = "+
					"trace_dual(L, K, image(d, E), S)",
				By(subK, finite, sInK, subringS, dualsInL, Read(spanTests, L).At(K, S, duals)))
			eSpanTests := a.Have(
				"so E lies in the trace dual of the S-span of the d(e)",
				"E ⊆ trace_dual(L, K, module_span(«ScalarS», «Regular», image(d, E)), S)",
				spanDual.Rw(),
				By(eTests))
			spanWithin := a.Have(
				"so by symmetry that S-span lies in the trace dual of E",
				"module_span(«ScalarS», «Regular», image(d, E)) ⊆ trace_dual(L, K, E, S)",
				By(spanInL, eSpanTests, Read(symmetry, L).At(K, S, E, dualSpan)))
			dualWithin := a.Have(
				"an element of the trace dual of E is the S-combination of the d(e) by its traces against E",
				"trace_dual(L, K, E, S) ⊆ module_span(«ScalarS», «Regular», image(d, E))",
				Unfold(set_basic.SubsetDef),
				Derive(func(b *Argument) {
					x := b.FixAs[A]("x")
					inDual := b.Assume()
					tests := b.Have(
						"x lies in L and its traces against E lie in S",
						"x ∈ L.carrier ∧ (∀e:A. e ∈ E ⇒ field_trace(L, K, x * e) ∈ S)",
						By(inDual, Read(membership, L).At(K, E, S, x)))
					terms := b.Have(
						"each term of its expansion lies in the S-span of the d(e)",
						"∀e:A. e ∈ E ⇒ field_trace(L, K, x * e) * d(e) ∈ module_span(«ScalarS», «Regular», image(d, E))",
						Derive(func(c *Argument) {
							e := c.FixAs[A]("e")
							eIn := c.Assume()
							generator := c.Have(
								"d(e) lies in the span",
								"d(e) ∈ module_span(«ScalarS», «Regular», image(d, E))",
								BySets(eIn, generators))
							coefficient := c.Have(
								"its coefficient lies in S",
								"field_trace(L, K, x * e) ∈ S",
								By(eIn, tests))
							c.Show(
								"the span is closed under S-multiples",
								By(
									generator,
									coefficient,
									submodule.SubmoduleSmul.Read(subSpan).AsFact().At(
										c.TermAs[A]("field_trace(L, K, x * e)"), d.Apply(e))))
						}))
					sum := b.Have(
						"so does their finite sum",
						"module_sum(L.add, L.zero, E, λe:A. field_trace(L, K, x * e) * d(e)) ∈ "+
							"module_span(«ScalarS», «Regular», image(d, E))",
						By(
							subSpan,
							finiteE,
							terms,
							submodule.SubmoduleModuleSum.Read(moduleS).At(
								dualSpan, E, b.TermAs[Fun[A, A]]("λe:A. field_trace(L, K, x * e) * d(e)"))))
					expanded := b.Have(
						"and that sum is x",
						"module_sum(L.add, L.zero, E, λe:A. field_trace(L, K, x * e) * d(e)) = x",
						By(tests, expansion.At(x)))
					b.Show(
						"so x lies in the S-span of the d(e)",
						By(Normalized, sum, expanded))
				}))
			a.Show(
				"so the two sets are equal",
				BySets(spanWithin, dualWithin))
		})

		// The e-coordinate of x is its trace against d(e): the S-span of E is
		// the trace dual of the d(e).
		basisCoordinates := ctx.Lemma(Statement{
			Binders: "∀L:field_on(A). ∀K S E:set(A). ∀d:(A → A).",
			Hypotheses: []string{
				"subfield(L, K)",
				"finite_extension(L, K, L.carrier)",
				"S ⊆ K",
				"comm_ring_on(«ScalarS»)",
				"finite(E)",
				"module_basis(«ScalarK», «Regular», E)",
				"∀e:A. e ∈ E ⇒ d(e) ∈ L.carrier",
				"∀e f:A. e ∈ E ∧ f ∈ E ⇒ field_trace(L, K, d(e) * f) = COND(e = f, L.one, L.zero)",
			},
			Conclusion: "trace_dual(L, K, image(d, E), S) = «latticeE»",
		}, func(a *Argument, L field.FieldFact[on.L], K, S, E *Expr[Set[A]], d *Arrow[A, A], given Fact) {
			parts := a.Conjuncts(
				given,
				"K is a subfield of L",
				"L is a finite extension of K",
				"S lies in K",
				"S is a commutative ring under the field operations",
				"E is finite",
				"E is a K-basis of L",
				"the d(e) lie in L",
				"they are trace-dual to E")
			subK, finite, sInK, ringS, finiteE, basisE, dualIn, delta :=
				parts[0], parts[1], parts[2], parts[3], parts[4], parts[5], parts[6], parts[7]
			scalarsK, scalarsS :=
				a.TermAs[module_record.RingOps[A]]("«ScalarK»"), a.TermAs[module_record.RingOps[A]]("«ScalarS»")
			regular := a.TermAs[module_record.ModuleOps[A, A]]("«Regular»")
			values := a.TermAs[module_record.ModuleOps[A, A]]("regular_module(«ScalarK»)")
			trace := a.TermAs[Fun2[A, A, A]]("λu:A. λv:A. field_trace(L, K, u * v)")
			duals := a.TermAs[Set[A]]("image(d, E)")
			lattice := a.TermAs[Set[A]]("«latticeE»")
			scalars := a.Conjuncts(
				a.Have(
					"the subfield K supplies scalars acting on L",
					"subring(field_ring(L), K) ∧ module_on(«ScalarK», «Regular»)",
					By(subK, field_extension.SubfieldScalars.Read(L).At(K))),
				"K is a subring of L",
				"L is a module over the ring on K")
			subringK, moduleK := scalars[0], scalars[1]
			ringK := a.Have(
				"the ring on K is commutative",
				"comm_ring_on(«ScalarK»)",
				By(subringK, comm_ring.SubringRingOn.Read(field.RingOn.Read(L)).At(K)))
			kInL := a.Have(
				"K lies in L",
				"K ⊆ L.carrier",
				By(comm_ring.SubringSubset.Read(subringK)))
			sInL := a.Have(
				"so does S",
				"S ⊆ L.carrier",
				BySets(sInK, kInL))
			subringS := a.Have(
				"so S is a subring of L",
				"subring(field_ring(L), S)",
				By(sInL, ringS, comm_ring.SubringRingOn.Read(field.RingOn.Read(L)).At(S)))
			moduleS := a.Have(
				"L is a module over the ring on S",
				"module_on(«ScalarS», «Regular»)",
				By(subringS, fractional_ideal.FieldModuleOn.Read(L).At(S)))
			valuesK := a.Have(
				"K is a module over its ring",
				"module_on(«ScalarK», regular_module(«ScalarK»))",
				By(module.RegularModuleOn.Read(ringK)))
			eInL := a.Have(
				"E lies in L",
				"E ⊆ L.carrier",
				By(linear_independence.BasisInCarrier.Read(basisE)))
			subLattice := a.Have(
				"E spans an S-submodule of L",
				"submodule(«ScalarS», «Regular», «latticeE»)",
				By(eInL, submodule.SpanSubmodule.Read(moduleS).At(E)))
			latticeInL := a.Have(
				"which lies in L",
				"«latticeE» ⊆ L.carrier",
				By(submodule.SubmoduleSubset.Read(subLattice)))
			generators := a.Have(
				"the span contains E",
				"E ⊆ «latticeE»",
				By(submodule.SubsetSpan.At(scalarsS, regular, E)))
			constants := a.Have(
				"one and zero lie in S",
				"L.one ∈ S ∧ L.zero ∈ S",
				By(comm_ring.OneIn.Read(ringS), comm_ring.ZeroIn.Read(ringS)))
			deltaInS := a.Have(
				"so the traces of the d(e) against E lie in S",
				"∀e f:A. e ∈ E ∧ f ∈ E ⇒ field_trace(L, K, d(e) * f) ∈ S",
				By(constants, delta))
			dualTests := a.Have(
				"so the d(e) lie in the trace dual of E",
				"image(d, E) ⊆ trace_dual(L, K, E, S)",
				Simp(Fwd(TraceDualDef)),
				BySets(dualIn, deltaInS))
			spanDual := a.Have(
				"which is the trace dual of its S-span",
				"trace_dual(L, K, «latticeE», S) = trace_dual(L, K, E, S)",
				By(subK, finite, sInK, subringS, eInL, Read(spanTests, L).At(K, S, E)))
			latticeTests := a.Have(
				"so the d(e) lie in the trace dual of the S-span of E",
				"image(d, E) ⊆ trace_dual(L, K, «latticeE», S)",
				spanDual.Rw(),
				By(dualTests))
			latticeWithin := a.Have(
				"so by symmetry the S-span of E lies in the trace dual of the d(e)",
				"«latticeE» ⊆ trace_dual(L, K, image(d, E), S)",
				By(latticeInL, latticeTests, Read(symmetry, L).At(K, S, duals, lattice)))
			pairing := a.Have(
				"the trace pairing is K-bilinear",
				"bilinear_pairing(«ScalarK», «Regular», λu:A. λv:A. field_trace(L, K, u * v))",
				By(subK, finite, field_trace.TracePairingBilinear.Read(L).At(K)))
			coordinates := a.Have(
				"the trace of d(e) * x is the e-coordinate of x",
				Statement{
					Binders: "∀e x:A.",
					Hypotheses: []string{
						"e ∈ E",
						"x ∈ L.carrier",
					},
					Conclusion: "field_trace(L, K, d(e) * x) = module_basis_coordinates(«ScalarK», «Regular», E, x, e)",
				},
				Derive(func(b *Argument) {
					e, x := b.FixAs[A]("e"), b.FixAs[A]("x")
					both := b.Assume()
					dualInL := b.Have(
						"d(e) lies in L",
						"d(e) ∈ L.carrier",
						By(both, dualIn.At(e)))
					column := b.Have(
						"pairing with d(e) is K-linear",
						"module_homomorphism(«ScalarK», "+
							"    «Regular», "+
							"    regular_module(«ScalarK»), "+
							"    λy:A. field_trace(L, K, d(e) * y))",
						By(pairing, dualInL, linear_pairing.BilinearPairingDef.At(scalarsK, regular, trace)))
					spec := b.Have(
						"the coordinates of x are scalars of K",
						"∀f:A. f ∈ E ⇒ module_basis_coordinates(«ScalarK», «Regular», E, x, f) ∈ K",
						By(finiteE, basisE, both, module_dimension.BasisCoordinatesSpec.Read(moduleK).AsFact().At(E, x)))
					expanded := b.Have(
						"expand pairing with d(e) along E at x",
						"field_trace(L, K, d(e) * x) = "+
							"module_sum(L.add, "+
							"    L.zero, "+
							"    E, "+
							"    λf:A. module_basis_coordinates(«ScalarK», «Regular», E, x, f) * field_trace(L, K, d(e) * f))",
						By(
							finiteE,
							basisE,
							column,
							both,
							module_dimension.HomBasisExpansion.At(
								scalarsK, regular, values, E, b.TermAs[Fun[A, A]]("λy:A. field_trace(L, K, d(e) * y)"), x)))
					terms := b.Have(
						"each term is a scalar of K",
						Statement{
							Binders: "∀f:A.",
							Hypotheses: []string{
								"f ∈ E",
							},
							Conclusion: "module_basis_coordinates(«ScalarK», «Regular», E, x, f) * " +
								"field_trace(L, K, d(e) * f) ∈ " +
								"K",
						},
						Derive(func(c *Argument) {
							f := c.FixAs[A]("f")
							fIn := c.Assume()
							fInL := c.Have(
								"f lies in L",
								"f ∈ L.carrier",
								BySets(fIn, eInL))
							value := c.Have(
								"the trace of d(e) * f is a scalar of K",
								"field_trace(L, K, d(e) * f) ∈ K",
								By(fInL, module_homomorphism.HomIn.Read(column).AsFact().At(f)))
							c.Show(
								"and so is its multiple by the coordinate",
								By(
									fIn,
									spec,
									value,
									module.SmulIn.Read(valuesK).AsFact().At(
										c.TermAs[A]("module_basis_coordinates(«ScalarK», «Regular», E, x, f)"),
										c.TermAs[A]("field_trace(L, K, d(e) * f)"))))
						}))
					off := b.Have(
						"every term but the e-term vanishes",
						Statement{
							Binders: "∀f:A.",
							Hypotheses: []string{
								"f ∈ E",
								"f ≠ e",
							},
							Conclusion: "module_basis_coordinates(«ScalarK», «Regular», E, x, f) * " +
								"field_trace(L, K, d(e) * f) = " +
								"L.zero",
						},
						Derive(func(c *Argument) {
							f := c.FixAs[A]("f")
							offDiagonal := c.Assume()
							zero := c.Have(
								"the trace of d(e) * f is zero",
								"field_trace(L, K, d(e) * f) = L.zero",
								By(both, offDiagonal, delta.At(e, f)))
							coordinateIn := c.Have(
								"the coordinate lies in L",
								"module_basis_coordinates(«ScalarK», «Regular», E, x, f) ∈ L.carrier",
								BySets(offDiagonal, spec, kInL))
							c.Show(
								"so the term is zero",
								zero.Rw(),
								ByArith(L, coordinateIn))
						}))
					single := b.Have(
						"so the sum is its e-term",
						"module_sum(L.add, "+
							"    L.zero, "+
							"    E, "+
							"    λf:A. "+
							"        module_basis_coordinates(«ScalarK», «Regular», E, x, f) * "+
							"        field_trace(L, K, d(e) * f)) = "+
							"module_basis_coordinates(«ScalarK», «Regular», E, x, e) * field_trace(L, K, d(e) * e)",
						By(
							finiteE,
							both,
							terms,
							off,
							module.ModuleSumSingle.Read(valuesK).At(E, e,
								b.TermAs[Fun[A, A]](
									"λf:A. module_basis_coordinates(«ScalarK», «Regular», E, x, f) * field_trace(L, K, d(e) * f)"))))
					one := b.Have(
						"the trace of d(e) * e is one",
						"field_trace(L, K, d(e) * e) = L.one",
						By(both, delta.At(e, e)))
					coordinateIn := b.Have(
						"the e-coordinate lies in L",
						"module_basis_coordinates(«ScalarK», «Regular», E, x, e) ∈ L.carrier",
						BySets(both, spec, kInL))
					b.Show(
						"so the trace of d(e) * x is the e-coordinate",
						CalcEq(
							Leg(
								b.TermAs[A](
									"module_sum(L.add, "+
										"    L.zero, "+
										"    E, "+
										"    λf:A. module_basis_coordinates(«ScalarK», «Regular», E, x, f) * field_trace(L, K, d(e) * f))"),
								"expand along E",
								By(expanded)),
							Leg(
								b.TermAs[A](
									"module_basis_coordinates(«ScalarK», «Regular», E, x, e) * field_trace(L, K, d(e) * e)"),
								"only the e-term survives",
								By(single)),
							FinalLeg(
								"the trace of d(e) * e is one",
								one.Rw(),
								ByArith(L, coordinateIn))))
				}))
			dualWithin := a.Have(
				"an element of the trace dual of the d(e) is the S-combination of E by its coordinates",
				"trace_dual(L, K, image(d, E), S) ⊆ «latticeE»",
				Unfold(set_basic.SubsetDef),
				Derive(func(b *Argument) {
					x := b.FixAs[A]("x")
					inDual := b.Assume()
					tests := b.Have(
						"x lies in L and its traces against the d(e) lie in S",
						"x ∈ L.carrier ∧ (∀y:A. y ∈ image(d, E) ⇒ field_trace(L, K, x * y) ∈ S)",
						By(inDual, Read(membership, L).At(K, duals, S, x)))
					coefficients := b.Have(
						"the coordinates of x lie in S",
						"∀e:A. e ∈ E ⇒ module_basis_coordinates(«ScalarK», «Regular», E, x, e) ∈ S",
						Derive(func(c *Argument) {
							e := c.FixAs[A]("e")
							eIn := c.Assume()
							dualInL := c.Have(
								"d(e) lies in L",
								"d(e) ∈ L.carrier",
								By(eIn, dualIn.At(e)))
							test := c.Have(
								"the trace of x * d(e) lies in S",
								"field_trace(L, K, x * d(e)) ∈ S",
								BySets(eIn, tests))
							commute := c.Have(
								"x and d(e) commute",
								"x * d(e) = d(e) * x",
								ByArith(L, tests, dualInL))
							c.Show(
								"and it is the e-coordinate",
								By(eIn, tests, test, commute, coordinates.At(e, x)))
						}))
					terms := b.Have(
						"each coordinate term lies in the S-span of E",
						"∀e:A. e ∈ E ⇒ module_basis_coordinates(«ScalarK», «Regular», E, x, e) * e ∈ «latticeE»",
						Derive(func(c *Argument) {
							e := c.FixAs[A]("e")
							eIn := c.Assume()
							generator := c.Have(
								"e lies in the span",
								"e ∈ «latticeE»",
								BySets(eIn, generators))
							c.Show(
								"the span is closed under S-multiples",
								By(
									generator,
									coefficients.At(e),
									eIn,
									submodule.SubmoduleSmul.Read(subLattice).AsFact().At(
										c.TermAs[A]("module_basis_coordinates(«ScalarK», «Regular», E, x, e)"), e)))
						}))
					sum := b.Have(
						"so does their finite sum",
						"module_sum(L.add, "+
							"    L.zero, "+
							"    E, "+
							"    λe:A. module_basis_coordinates(«ScalarK», «Regular», E, x, e) * e) ∈ "+
							"«latticeE»",
						By(
							subLattice,
							finiteE,
							terms,
							submodule.SubmoduleModuleSum.Read(moduleS).At(lattice, E,
								b.TermAs[Fun[A, A]]("λe:A. module_basis_coordinates(«ScalarK», «Regular», E, x, e) * e"))))
					reconstruction := b.Have(
						"which is x",
						"module_sum(L.add, "+
							"    L.zero, "+
							"    E, "+
							"    λe:A. module_basis_coordinates(«ScalarK», «Regular», E, x, e) * e) = "+
							"x",
						By(finiteE, basisE, tests, module_dimension.BasisCoordinatesSpec.Read(moduleK).AsFact().At(E, x)))
					b.Show(
						"so x lies in the S-span of E",
						By(Normalized, sum, reconstruction))
				}))
			a.Show(
				"so the two sets are equal",
				BySets(latticeWithin, dualWithin))
		})

		// A coefficient in S is one in K, so K-independence gives S-independence.
		freeOverS := ctx.Lemma(Statement{
			Binders: "∀L:field_on(A). ∀K S D:set(A).",
			Hypotheses: []string{
				"subfield(L, K)",
				"S ⊆ K",
				"comm_ring_on(«ScalarS»)",
				"module_basis(«ScalarK», «Regular», D)",
			},
			Conclusion: "module_basis(«ScalarS», " +
				"    restrict_module(«Regular», module_span(«ScalarS», «Regular», D)), " +
				"    D)",
		}, func(a *Argument, L field.FieldFact[on.L], K, S, D *Expr[Set[A]], given Fact) {
			parts := a.Conjuncts(
				given,
				"K is a subfield of L",
				"S lies in K",
				"S is a commutative ring under the field operations",
				"D is a K-basis of L")
			subK, sInK, ringS, basisD := parts[0], parts[1], parts[2], parts[3]
			scalarsK, scalarsS :=
				a.TermAs[module_record.RingOps[A]]("«ScalarK»"), a.TermAs[module_record.RingOps[A]]("«ScalarS»")
			regular := a.TermAs[module_record.ModuleOps[A, A]]("«Regular»")
			span := a.TermAs[Set[A]]("module_span(«ScalarS», «Regular», D)")
			kInL := a.Have(
				"K lies in L",
				"K ⊆ L.carrier",
				By(field.SubfieldSubset.Read(subK)))
			sInL := a.Have(
				"so does S",
				"S ⊆ L.carrier",
				BySets(sInK, kInL))
			subringS := a.Have(
				"so S is a subring of L",
				"subring(field_ring(L), S)",
				By(sInL, ringS, comm_ring.SubringRingOn.Read(field.RingOn.Read(L)).At(S)))
			moduleS := a.Have(
				"L is a module over the ring on S",
				"module_on(«ScalarS», «Regular»)",
				By(subringS, fractional_ideal.FieldModuleOn.Read(L).At(S)))
			dInL := a.Have(
				"D lies in L",
				"D ⊆ L.carrier",
				By(linear_independence.BasisInCarrier.Read(basisD)))
			subSpan := a.Have(
				"D spans an S-submodule of L",
				"submodule(«ScalarS», «Regular», module_span(«ScalarS», «Regular», D))",
				By(dInL, submodule.SpanSubmodule.Read(moduleS).At(D)))
			independentK := a.Have(
				"D is independent over K",
				"module_independent(«ScalarK», «Regular», D)",
				By(basisD, linear_independence.ModuleBasisDef.At(scalarsK, regular, D)))
			criterionK := a.Have(
				"a vanishing K-combination of D has zero coefficients",
				"∀T:set(A). ∀c:(A → A). "+
					"    finite(T) ∧ "+
					"    T ⊆ D ∧ "+
					"    (∀x:A. x ∈ T ⇒ c(x) ∈ K) ∧ "+
					"    module_sum(L.add, L.zero, T, λx:A. c(x) * x) = L.zero ⇒ "+
					"    ∀x:A. x ∈ T ⇒ c(x) = L.zero",
				By(independentK, linear_independence.ModuleIndependentDef.At(scalarsK, regular, D)))
			criterionS := a.Have(
				"so does a vanishing S-combination",
				"∀T:set(A). ∀c:(A → A). "+
					"    finite(T) ∧ "+
					"    T ⊆ D ∧ "+
					"    (∀x:A. x ∈ T ⇒ c(x) ∈ S) ∧ "+
					"    module_sum(L.add, L.zero, T, λx:A. c(x) * x) = L.zero ⇒ "+
					"    ∀x:A. x ∈ T ⇒ c(x) = L.zero",
				Derive(func(b *Argument) {
					T := b.FixAs[Set[A]]("T")
					c := b.FixAs[Fun[A, A]]("c")
					small := b.Assume()
					inK := b.Have(
						"its coefficients are scalars of K",
						"∀x:A. x ∈ T ⇒ c(x) ∈ K",
						BySets(small, sInK))
					b.Show(
						"so K-independence kills them",
						By(small, inK, criterionK.At(T, c)))
				}))
			independentS := a.Have(
				"so D is independent over S",
				"module_independent(«ScalarS», «Regular», D)",
				By(dInL, criterionS, linear_independence.ModuleIndependentDef.At(scalarsS, regular, D)))
			a.Show(
				"so D is an S-basis of its S-span",
				By(independentS, subSpan, linear_independence.BasisRestrict.Read(moduleS).At(span, D)))
		})

		return ctx.Theorem(headline, func(
			a *Argument,
			L field.FieldFact[on.L],
			K, S, E *Expr[Set[A]],
			given Fact,
		) {
			parts := a.Conjuncts(
				given,
				"K is a subfield of L",
				"S lies in K",
				"S is a subring of L",
				"E is finite",
				"E is a K-basis of L",
				"the trace pairing is nondegenerate")
			subK, sInK, subringS, finiteE, basisE := parts[0], parts[1], parts[2], parts[3], parts[4]
			ringS := a.Have(
				"S is a commutative ring under the field operations",
				"comm_ring_on(«ScalarS»)",
				By(subringS, comm_ring.SubringRingOn.Read(field.RingOn.Read(L)).At(S)))
			scalarsK := a.TermAs[module_record.RingOps[A]]("«ScalarK»")
			regular := a.TermAs[module_record.ModuleOps[A, A]]("«Regular»")
			carrier := a.Have(
				"the vectors of the module L are its elements",
				"«Regular».carrier = L.carrier",
				Simp(Fwd(module_record.RegularModuleDef), Fwd(field.FieldRingDef)),
				Basic())
			finiteDimensional := a.Have(
				"the finite basis E makes L finite-dimensional over K",
				"finite_dimensional(«ScalarK», «Regular»)",
				By(finiteE, basisE, module_dimension.FiniteDimensionalDef.At(scalarsK, regular)))
			finite := a.Have(
				"so L is a finite extension of K",
				"finite_extension(L, K, L.carrier)",
				Simp(
					Fwd(field_extension.FiniteExtensionDef),
					Rev(carrier),
					Fwd(module_record.RestrictModuleCarrier)),
				By(finiteDimensional))
			d, dual := a.UnpackAs[Fun[A, A]](
				GroupPremises(parts[0], finite, parts[3], parts[4], parts[5], Read(dualBasis, L).At(K, E)), "d")
			properties := a.Conjuncts(
				dual,
				"the d(e) lie in L",
				"they are trace-dual to E",
				"they are a K-basis of L",
				"they expand each x by its traces against E")
			dualIn, delta, basisD, expansion := properties[0], properties[1], properties[2], properties[3]
			duals := a.TermAs[Set[A]]("image(d, E)")
			eInL := a.Have(
				"E lies in L",
				"E ⊆ L.carrier",
				By(linear_independence.BasisInCarrier.Read(basisE)))
			dualsInL := a.Have(
				"so do the d(e)",
				"image(d, E) ⊆ L.carrier",
				BySets(dualIn))
			dualOfLattice := a.Have(
				"so the trace dual of the S-span of E is the S-span of the d(e)",
				"trace_dual(L, K, «latticeE», S) = module_span(«ScalarS», «Regular», image(d, E))",
				CalcEq(
					Leg(
						a.TermAs[Set[A]]("trace_dual(L, K, E, S)"),
						"the trace dual of an S-span is the trace dual of its generators",
						By(subK, finite, sInK, subringS, eInL, Read(spanTests, L).At(K, S, E))),
					FinalLeg(
						"which the d(e) span",
						By(
							subK,
							finite,
							sInK,
							ringS,
							finiteE,
							eInL,
							dualIn,
							delta,
							expansion,
							Read(dualCoefficients, L).At(K, S, E, d)))))
			bidual := a.Have(
				"and the trace dual of the S-span of the d(e) is the S-span of E",
				"trace_dual(L, K, module_span(«ScalarS», «Regular», image(d, E)), S) = «latticeE»",
				CalcEq(
					Leg(
						a.TermAs[Set[A]]("trace_dual(L, K, image(d, E), S)"),
						"the trace dual of an S-span is the trace dual of its generators",
						By(subK, finite, sInK, subringS, dualsInL, Read(spanTests, L).At(K, S, duals))),
					FinalLeg(
						"which E spans",
						By(
							subK,
							finite,
							sInK,
							ringS,
							finiteE,
							basisE,
							dualIn,
							delta,
							Read(basisCoordinates, L).At(K, S, E, d)))))
			basisS := a.Have(
				"the d(e) are an S-basis of their S-span",
				"module_basis(«ScalarS», "+
					"    restrict_module(«Regular», module_span(«ScalarS», «Regular», image(d, E))), "+
					"    image(d, E))",
				By(subK, sInK, ringS, basisD, Read(freeOverS, L).At(K, S, duals)))
			a.Take(d.Core())
			a.Show(
				"d(E) is the trace-dual K-basis, its S-span the trace "+
					"dual of the S-span of E, and E's S-span its trace dual",
				dualOfLattice.Rw(),
				By(dualIn, delta, basisD, basisS, bidual))
		})
	}),
})}
