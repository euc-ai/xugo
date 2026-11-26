package trace_dual

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_trace"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/functional_dual"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/principal_ideal_domain"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/fractional_ideal"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_away"
	"github.com/euc-ai/xugo/library/registry"
)

// TraceDualLocalizes — the trace dual commutes with inverting s: over S with
// s inverted each span is the saturation of its S-submodule, so the statement
// is functional_dual.FunctionalDualSaturation at the K-linear field trace. Two
// steps connect them: N saturates alike in K and in L, since s is invertible
// in K, and the trace dual of X is an S-submodule, since the tests are
// S-linear and N is one.
var TraceDualLocalizes = traceDualLocalizesThm{family.Add(registry.ProofEntry{
	Name: "TraceDualLocalizes",
	Key:  "prop_c5cb9e59136cf024",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀K S X N:set(A). ∀s:A.",
		Hypotheses: []string{
			"subfield(L, K)",
			"finite_extension(L, K, L.carrier)",
			"S ⊆ K",
			"subring(field_ring(L), S)",
			"submodule(«ScalarS», «Regular», X)",
			"module_finitely_generated(«ScalarS», restrict_module(«Regular», X))",
			"submodule(«ScalarS», «VectorsK», N)",
			"s ∈ S",
			"s ≠ L.zero",
		},
		Conclusion: "trace_dual(L, " +
			"    K, " +
			"    module_span(«ringAway», «Regular», X), " +
			"    module_span(«ringAway», «Regular», N)) = " +
			"module_span(«ringAway», «Regular», trace_dual(L, K, X, N))",
		Abbrev: Abbrev{
			{Name: "ringAway", Text: "restrict_ring(field_ring(L), ring_away(field_ring(L), S, s))"},
		},
	}, func(
		a *Argument,
		L field.FieldFact[on.L],
		K, S, X, N *Expr[Set[A]],
		s *Expr[A],
		subK, finite, sInK, subS, subX, generated, subN, sInS, nonzero Fact,
	) {
		scalarsL := a.TermAs[module_record.RingOps[A]]("field_ring(L)")
		scalarsK, scalarsS :=
			a.TermAs[module_record.RingOps[A]]("«ScalarK»"), a.TermAs[module_record.RingOps[A]]("«ScalarS»")
		regular := a.TermAs[module_record.ModuleOps[A, A]]("«Regular»")
		trace := a.TermAs[Fun[A, A]]("field_trace(L, K)")
		linearK := a.Have(
			"the field trace is K-linear",
			"module_homomorphism(«ScalarK», «Regular», «VectorsK», field_trace(L, K))",
			By(subK, finite, field_trace.FieldTraceLinear.Read(L).At(K)))
		linearS := a.Have(
			"and so S-linear",
			"module_homomorphism(«ScalarS», «Regular», «VectorsK», field_trace(L, K))",
			By(
				Normalized,
				linearK,
				subS,
				sInK,
				comm_ring.SubringRestrict.At(scalarsL, S, K),
				module_record.RestrictRingTwice.At(scalarsL, K, S),
				module_homomorphism.HomRestrictScalars.Read(linearK).At(S)))
		latticeK := a.Have(
			"K is an S-submodule of L",
			"submodule(«ScalarS», «Regular», K)",
			By(
				subK,
				sInK,
				field.SubfieldSubring.Read(L).At(K),
				fractional_ideal.SubringSubmodule.Read(L).At(K),
				submodule.SubmoduleRestrictScalars.At(scalarsK, regular, K, scalarsS)))
		latticeN := a.Have(
			"so is N, an S-submodule of K",
			"submodule(«ScalarS», «Regular», N)",
			By(latticeK, subN, submodule.SubmoduleTrans.At(scalarsS, regular, K, N)))
		latticeDual := a.Have(
			"the trace dual of X is an S-submodule of L",
			"submodule(«ScalarS», «Regular», trace_dual(L, K, X, N))",
			Simp(Fwd(TraceDualIsFunctionalDual)),
			By(
				subS,
				linearS,
				submodule.SubmoduleSubset.Read(subX),
				subN,
				functional_dual.FunctionalDualOverScalars.Read(L).At(K, trace, S, X, N)))
		spanX := a.Have(
			"over S with s inverted, X spans its saturation",
			"module_span(«ringAway», «Regular», X) = module_saturation(«ScalarS», «Regular», s, X)",
			By(subS, sInS, nonzero, subX, ring_away.SpanOverAwayIsSaturation.Read(L).At(S, X, s)))
		spanN := a.Have(
			"N spans its saturation",
			"module_span(«ringAway», «Regular», N) = module_saturation(«ScalarS», «Regular», s, N)",
			By(subS, sInS, nonzero, latticeN, ring_away.SpanOverAwayIsSaturation.Read(L).At(S, N, s)))
		spanDual := a.Have(
			"and the trace dual of X spans its saturation",
			"module_span(«ringAway», «Regular», trace_dual(L, K, X, N)) = "+
				"module_saturation(«ScalarS», «Regular», s, trace_dual(L, K, X, N))",
			By(
				subS,
				sInS,
				nonzero,
				latticeDual,
				ring_away.SpanOverAwayIsSaturation.Read(L).At(S, a.TermAs[Set[A]]("trace_dual(L, K, X, N)"), s)))
		sameSaturation := a.Have(
			"N saturates alike in L and in K",
			"module_saturation(«ScalarS», «Regular», s, N) = module_saturation(«ScalarS», «VectorsK», s, N)",
			BySets(
				subK,
				sInS,
				sInK,
				nonzero,
				submodule.SubmoduleSubset.Read(subN),
				principal_ideal_domain.SaturationInSubfield.Read(L).At(K, S, N, s)))
		a.Show(
			"each span is a saturation, and the functional dual commutes with saturation",
			spanX.Rw(),
			spanN.Rw(),
			sameSaturation.Rw(),
			spanDual.Rw(),
			Simp(Fwd(TraceDualIsFunctionalDual)),
			By(
				subK,
				linearK,
				sInK,
				subS,
				subX,
				subN,
				generated,
				sInS,
				functional_dual.FunctionalDualSaturation.Read(L).At(K, trace, S, X, N, s)))
	}),
})}
