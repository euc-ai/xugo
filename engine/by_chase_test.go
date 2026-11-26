package engine

import (
	"context"
	"strings"
	"testing"

	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/library/serve"
	"github.com/euc-ai/xugo/prover/solver/chase"
	"github.com/stretchr/testify/require"
)

// diagnostics joins a result's diagnostic messages, the text a failed
// `by` reports.
func diagnostics(res *StepResult) string {
	var parts []string
	for _, d := range res.Diagnostics {
		parts = append(parts, d.Message)
	}
	return strings.Join(parts, "\n")
}

// hyp0 names the leaf's first hypothesis as a by_hyps premise.
func hyp0() []ByHypSpec {
	zero := 0
	return []ByHypSpec{{HypIndex: &zero}}
}

// byChaseEngine is the production engine with the chase closer's laws
// installed from the chapters.
func byChaseEngine(t *testing.T) *Engine {
	t.Helper()
	e := byArithEngine(t)
	serve.InstallChaseBundle()
	t.Cleanup(func() { chase.SetLaws(nil); chase.SetFoundation(nil) })
	return e
}

// chaseLeaf reads record field notation through the session's production
// statement door, then strips the statement to the requested chase leaf.
func chaseLeaf(t *testing.T, e *Engine, stmt string, strips ...string) (sid, gid string) {
	t.Helper()
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, err := e.getSession(info.ID)
	require.NoError(t, err)
	parsed := dsl.ParsePropTextInScope(stmt, s.StatementDoorScope())
	require.Empty(t, parsed.Errors, "add-goal %q", stmt)
	s.mu.Lock()
	gid = s.AddGoal(parsed.Prop)
	s.mu.Unlock()
	for _, typ := range strips {
		res, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{GoalID: gid, Tactic: TacticReq{Type: typ}})
		require.NoError(t, err, "apply %s", typ)
		require.Len(t, res.Produced, 1, typ)
		gid = res.Produced[0].GoalID
	}
	return info.ID, gid
}

// The module vocabulary over one ring, including distinct source and
// target element types, in the chapters' spelling.
const chaseRing = "∀R:ring_ops(A). "

func chaseModule(record string) string { return "module_on(R, " + record + ")" }

func chaseHom(f, src, dst string) string {
	return "module_homomorphism(R, " + src + ", " + dst + ", " + f + ")"
}

// TestByChase_ClosesThroughTheChaptersLaws: `by {chase:{depth:k}}` over
// the named premises closes a homomorphism's linearity (no round) and a
// preimage through an exactness (one round), reading the corpus's own
// module_on, module_homomorphism and exact_at facts.
func TestByChase_ClosesThroughTheChaptersLaws(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus and the production bundles")
	}
	e := byChaseEngine(t)
	rows := []struct {
		name, stmt string
		depth      int
	}{
		{"linearity from the hom alone", chaseRing + "∀M:module_ops(A, B). ∀N:module_ops(A, C). ∀f:(B → C). ∀x y:B. " +
			chaseHom("f", "M", "N") + " ∧ x ∈ M.carrier ∧ y ∈ M.carrier ⇒ " +
			"f(M.add(x, M.neg(y))) = N.add(f(x), N.neg(f(y)))", 0},
		{"preimage through an exactness", chaseRing + "∀M N K:module_ops(A, B). ∀g f:(B → B). ∀b:B. " +
			chaseHom("g", "M", "N") + " ∧ " + chaseHom("f", "N", "K") + " ∧ exact_at(K.zero, M.carrier, N.carrier, g, f) ∧ b ∈ N.carrier ∧ f(b) = K.zero ⇒ " +
			"∃a:B. b = g(a) ∧ a ∈ M.carrier", 1},
		{"module scalar closure", chaseRing + "∀M:module_ops(A, B). ∀c:A. ∀u:B. " +
			chaseModule("M") + " ∧ c ∈ R.carrier ∧ u ∈ M.carrier ⇒ M.smul(c, u) ∈ M.carrier", 0},
	}
	for _, row := range rows {
		t.Run(row.name, func(t *testing.T) {
			sid, gid := chaseLeaf(t, e, row.stmt, "strip_quant", "strip_imp")
			res, err := e.ApplyStep(context.Background(), sid, &ApplyStepRequest{
				GoalID: gid, Tactic: TacticReq{Type: "by", Chase: &ByChaseReq{Depth: row.depth},
					ByHyps: hyp0()},
			})
			require.NoError(t, err)
			require.True(t, res.Success, "diagnostics: %+v", res.Diagnostics)
			require.Equal(t, "close", res.Effect)
		})
	}
}

// TestByChase_DepthShortFailsLoudly: a round short, the close fails and
// the error says after how many rounds the chase stopped and which
// element stayed outside which image — never a silent fall-through to
// the refuter.
func TestByChase_DepthShortFailsLoudly(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus and the production bundles")
	}
	e := byChaseEngine(t)
	stmt := chaseRing + "∀M N K:module_ops(A, B). ∀g f:(B → B). ∀b:B. " +
		chaseHom("g", "M", "N") + " ∧ " + chaseHom("f", "N", "K") + " ∧ exact_at(K.zero, M.carrier, N.carrier, g, f) ∧ b ∈ N.carrier ∧ f(b) = K.zero ⇒ " +
		"∃a:B. b = g(a) ∧ a ∈ M.carrier"
	sid, gid := chaseLeaf(t, e, stmt, "strip_quant", "strip_imp")
	res, err := e.ApplyStep(context.Background(), sid, &ApplyStepRequest{
		GoalID: gid, Tactic: TacticReq{Type: "by", Chase: &ByChaseReq{Depth: 0}, ByHyps: hyp0()},
	})
	require.NoError(t, err)
	require.False(t, res.Success, "a round short, the chase must not close")
	text := diagnostics(res)
	require.Contains(t, text, "did not close the goal after 0 round(s)")
	require.Contains(t, text, "not in the image of g")
}

// TestByChase_WireRefusals: chase is one closer among three, and it
// reads a diagram, so the wire refuses it beside arith or settac and
// with no premise to read.
func TestByChase_WireRefusals(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus and the production bundles")
	}
	e := byChaseEngine(t)
	sid, gid := chaseLeaf(t, e, "∀x y:num. x < y ⇒ x + 1 ≤ y", "strip_quant", "strip_imp")
	for _, row := range []struct {
		name string
		req  TacticReq
		want string
	}{
		{"with arith", TacticReq{Type: "by", Chase: &ByChaseReq{Depth: 1}, Arith: true, ByHyps: hyp0()}, "mutually exclusive"},
		{"with settac", TacticReq{Type: "by", Chase: &ByChaseReq{Depth: 1}, Settac: true, ByHyps: hyp0()}, "mutually exclusive"},
		{"no premises", TacticReq{Type: "by", Chase: &ByChaseReq{Depth: 1}}, "empty premise list"},
		{"negative depth", TacticReq{Type: "by", Chase: &ByChaseReq{Depth: -1}, ByHyps: hyp0()}, "negative"},
	} {
		t.Run(row.name, func(t *testing.T) {
			res, err := e.ApplyStep(context.Background(), sid, &ApplyStepRequest{GoalID: gid, Tactic: row.req})
			require.NoError(t, err)
			require.False(t, res.Success)
			text := diagnostics(res)
			require.True(t, strings.Contains(text, row.want), text)
		})
	}
}

// TestByChase_IndexedComplexThroughTheChaptersLaws: a complex's facts
// over degrees, read at the degrees the leaf spells with the instance's
// `n + 2` bridged to the leaf's `(m + 1) + 1` by the nat ring
// normalizer, and its maps the family members d(m + 1), d(m + 1 + 1):
// a boundary is killed by the next boundary map.
func TestByChase_IndexedComplexThroughTheChaptersLaws(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus and the production bundles")
	}
	e := byChaseEngine(t)
	stmt := chaseRing + "∀P:(num → module_ops(A, B)). ∀d:(num → B → B). ∀m:num. ∀x:B. " +
		"(∀n:num. " + chaseHom("d(n + 1)", "P(n + 1)", "P(n)") + ") ∧ " +
		"(∀n:num. ∀u:B. u ∈ mod_carrier(P(n + 2)) ⇒ d(n + 1)(d(n + 2)(u)) = mod_zero(P(n))) ∧ x ∈ image(d(m + 1 + 1), mod_carrier(P(m + 1 + 1))) ⇒ " +
		"d(m + 1)(x) = mod_zero(P(m))"
	sid, gid := chaseLeaf(t, e, stmt, "strip_quant", "strip_imp")
	res, err := e.ApplyStep(context.Background(), sid, &ApplyStepRequest{
		GoalID: gid, Tactic: TacticReq{Type: "by", Chase: &ByChaseReq{Depth: 0}, ByHyps: hyp0()},
	})
	require.NoError(t, err)
	require.True(t, res.Success, "diagnostics: %s", diagnostics(res))
	require.Equal(t, "close", res.Effect)
}

// A premise in the closer's clause form whose guard the leaf holds only
// up to the nat normal form — `x ∉ image(d((m + 1) + 1), …) ∨ …` beside
// the resident `x ∈ image(d(m + 2), …)` — reads as the guarded law, its
// guard decided at the canonical degree: the shape a full-tuple cite
// installs in where the context does not hold its guard as written.
func TestByChase_ClauseFormPremiseWithADegreeGuard(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus and the production bundles")
	}
	e := byChaseEngine(t)
	stmt := chaseRing + "∀P:(num → module_ops(A, B)). ∀d:(num → B → B). ∀m:num. ∀x:B. " +
		"(∀n:num. " + chaseHom("d(n + 1)", "P(n + 1)", "P(n)") + ") ∧ " +
		"(x ∉ image(d((m + 1) + 1), mod_carrier(P((m + 1) + 1))) ∨ d(m + 1)(x) = mod_zero(P(m))) ∧ " +
		"x ∈ image(d(m + 2), mod_carrier(P(m + 2))) ⇒ d(m + 1)(x) = mod_zero(P(m))"
	sid, gid := chaseLeaf(t, e, stmt, "strip_quant", "strip_imp")
	res, err := e.ApplyStep(context.Background(), sid, &ApplyStepRequest{
		GoalID: gid, Tactic: TacticReq{Type: "by", Chase: &ByChaseReq{Depth: 0}, ByHyps: hyp0()},
	})
	require.NoError(t, err)
	require.True(t, res.Success, "diagnostics: %s", diagnostics(res))
	require.Equal(t, "close", res.Effect)
}

// One degree reads as one degree however it is spelled: the leaf's
// `0 + 1` against a law's `1`, and its `m + 1 + 1` against `m + 2`, each
// put in the nat ring normal form before anything is read. The shared
// degree spelling lets an instance at P(1) reach a member of P(0 + 1).
func TestByChase_OneDegreeUnderTwoSpellings(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus and the production bundles")
	}
	e := byChaseEngine(t)
	chainFacts := "(∀n:num. " + chaseHom("d(n + 1)", "P(n + 1)", "P(n)") + ") ∧ "
	for _, stmt := range []string{
		chaseRing + "∀P:(num → module_ops(A, B)). ∀d:(num → B → B). ∀x:B. " + chainFacts +
			"(∀u:B. u ∈ mod_carrier(P(1)) ⇒ d(1)(u) = mod_zero(P(0))) ∧ x ∈ mod_carrier(P(0 + 1)) ⇒ d(0 + 1)(x) = mod_zero(P(0))",
		chaseRing + "∀P:(num → module_ops(A, B)). ∀d:(num → B → B). ∀m:num. ∀x:B. " + chainFacts +
			"(∀n:num. ∀u:B. u ∈ mod_carrier(P(n + 2)) ⇒ d(n + 1)(d(n + 2)(u)) = mod_zero(P(n))) ∧ x ∈ mod_carrier(P(m + 2)) ⇒ d(m + 1)(d(m + 1 + 1)(x)) = mod_zero(P(m))",
	} {
		sid, gid := chaseLeaf(t, e, stmt, "strip_quant", "strip_imp")
		res, err := e.ApplyStep(context.Background(), sid, &ApplyStepRequest{
			GoalID: gid, Tactic: TacticReq{Type: "by", Chase: &ByChaseReq{Depth: 0}, ByHyps: hyp0()},
		})
		require.NoError(t, err)
		require.True(t, res.Success, "%s\ndiagnostics: %s", stmt, diagnostics(res))
		require.Equal(t, "close", res.Effect)
	}
}

// Packed record endpoints and a submodule of a packed module share the
// same carrier only through the supplied projection equations.
func TestByChase_PackedModuleAndSubmoduleWithRecordHom(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus and the production bundles")
	}
	e := byChaseEngine(t)
	stmt := "∀add:(A → A → A). ∀zero:A. ∀neg:(A → A). ∀mul:(A → A → A). ∀one:A. ∀sub:(A → A → A). " +
		"∀add':(B → B → B). ∀zero':B. ∀neg':(B → B). ∀smul:(A → B → B). ∀R:set(A). ∀M N H:set(B). ∀f:(B → B). ∀x:B. " +
		"module_on(mk_ring(add, zero, neg, mul, one, sub, R), mk_module(add', zero', neg', smul, N)) ∧ " +
		"module_homomorphism(mk_ring(add, zero, neg, mul, one, sub, R), mk_module(add', zero', neg', smul, M), mk_module(add', zero', neg', smul, N), f) ∧ " +
		"submodule(mk_ring(add, zero, neg, mul, one, sub, R), mk_module(add', zero', neg', smul, M), H) ∧ x ∈ H ⇒ f(add'(x, zero')) = f(x)"
	sid, gid := chaseLeaf(t, e, stmt, "strip_quant", "strip_imp")
	res, err := e.ApplyStep(context.Background(), sid, &ApplyStepRequest{GoalID: gid, Tactic: TacticReq{Type: "by", Chase: &ByChaseReq{Depth: 0}, ByHyps: hyp0()}})
	require.NoError(t, err)
	require.True(t, res.Success, "diagnostics: %s", diagnostics(res))
	require.Equal(t, "close", res.Effect)
}

func TestByChase_ComplexModuleDefinitionThroughTheChaptersLaws(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus and the production bundles")
	}
	e := byChaseEngine(t)
	stmt := chaseRing + "∀P:complex_ops(A, B). ∀m:num. ∀x:B. " +
		"(∀n:num. " + chaseHom("P.d(n + 1)", "complex_module(P, n + 1)", "complex_module(P, n)") + ") ∧ " +
		"(∀n:num. ∀u:B. u ∈ P.terms(n + 2) ⇒ P.d(n + 1)(P.d(n + 2)(u)) = P.zero) ∧ " +
		"x ∈ image(P.d(m + 1 + 1), P.terms(m + 1 + 1)) ⇒ P.d(m + 1)(x) = P.zero"
	sid, gid := chaseLeaf(t, e, stmt, "strip_quant", "strip_imp")
	res, err := e.ApplyStep(context.Background(), sid, &ApplyStepRequest{GoalID: gid, Tactic: TacticReq{Type: "by", Chase: &ByChaseReq{Depth: 0}, ByHyps: hyp0()}})
	require.NoError(t, err)
	require.True(t, res.Success, "diagnostics: %s", diagnostics(res))
	require.Equal(t, "close", res.Effect)
}

// A complex packed with its terms and its differentials as lambdas over
// degrees has, at a degree, the term and the differential its lambdas
// give there: the degree module's carrier and a membership that spells
// the term are one module, the complex's differential and the map
// spelled out one map. The packed value is spelled out, or stands
// behind a definition (free_complex, whose terms are
// `λn. finite_supp(R.zero, R.carrier, S(n))`).
func TestByChase_PackedFamilyIsReadAtItsDegree(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus and the production bundles")
	}
	e := byChaseEngine(t)
	packed := chaseRing + "∀add:(B → B → B). ∀zero:B. ∀neg:(B → B). ∀smul:(A → B → B). ∀P:(num → set(B)). ∀dd:(num → B → B). " +
		"∀N:module_ops(A, D). ∀f:(B → D). ∀n:num. ∀x y:B. "
	free := chaseRing + "∀T:(num → set(B)). ∀e:(num → (B → A) → B → A). ∀N:module_ops(A, D). ∀eta:((B → A) → D). ∀u v:(B → A). "
	degreeZero := "complex_module(free_complex(R, T, e), 0)"
	atZero := "u ∈ finite_supp(R.zero, R.carrier, T(0)) ∧ v ∈ finite_supp(R.zero, R.carrier, T(0))"
	chainMap := chaseRing + "∀S:(num → set(B)). ∀d:(num → (B → A) → B → A). ∀T:(num → set(C)). ∀e:(num → (C → A) → C → A). " +
		"∀g g':(num → (B → A) → C → A). ∀n:num. ∀x:(B → A). "
	P, Q := "free_complex(R, S, d)", "free_complex(R, T, e)"
	component := func(g string) string {
		return "(∀k:num. " + chaseHom(g+"(k)", "complex_module("+P+", k)", "complex_module("+Q+", k)") + ")"
	}
	square := func(g string) string {
		return "(∀k:num. ∀u:(B → A). u ∈ " + P + ".terms(k + 1) ⇒ " +
			g + "(k)(" + P + ".d(k + 1)(u)) = " + Q + ".d(k + 1)(" + g + "(k + 1)(u)))"
	}
	boundary := func(complex string) string {
		return "(∀k:num. " + chaseHom(complex+".d(k + 1)", "complex_module("+complex+", k + 1)", "complex_module("+complex+", k)") + ")"
	}
	shifted := "pack_complex(add, zero, neg, smul, (λk:num. P(k + 1)), (λk:num. λv:B. dd(k + 1)(v)))"
	for _, row := range []struct{ name, stmt string }{
		{"a packed complex's degree module", packed +
			chaseHom("f", "complex_module(pack_complex(add, zero, neg, smul, (λk:num. P(k + 1)), dd), n)", "N") +
			" ∧ x ∈ P(n + 1) ∧ y ∈ P(n + 1) ⇒ f(add(x, y)) = N.add(f(x), f(y))"},
		{"a packed complex's differential, its values spelled out", packed +
			boundary(shifted) + " ∧ x ∈ P(n + 2) ∧ y ∈ P(n + 2) ⇒ " +
			shifted + ".d(n + 1)(add(x, y)) = add(dd(n + 2)(x), dd(n + 2)(y))"},
		{"a map out of the free complex's degree zero", free +
			chaseHom("eta", degreeZero, "N") + " ∧ " + atZero + " ∧ eta(u) = eta(v) ⇒ " +
			"eta(fun_add(R.add, u, fun_neg(R.neg, v))) = N.zero"},
		{"the same beside the degree module's equation", free +
			chaseHom("eta", degreeZero, "N") + " ∧ " + degreeZero + " = free_module_record(R, T(0)) ∧ " + atZero +
			" ∧ eta(u) = eta(v) ⇒ eta(fun_add(R.add, u, fun_neg(R.neg, v))) = N.zero"},
		{"a chain map's components and squares between free complexes", chainMap +
			component("g") + " ∧ " + component("g'") + " ∧ " + square("g") + " ∧ " + square("g'") + " ∧ " +
			boundary(P) + " ∧ " + boundary(Q) + " ∧ x ∈ finite_supp(R.zero, R.carrier, S(n + 1)) ⇒ " +
			"fun_add(R.add, g(n)(d(n + 1)(x)), fun_neg(R.neg, g'(n)(d(n + 1)(x)))) = " +
			"e(n + 1)(fun_add(R.add, g(n + 1)(x), fun_neg(R.neg, g'(n + 1)(x))))"},
	} {
		t.Run(row.name, func(t *testing.T) {
			sid, gid := chaseLeaf(t, e, row.stmt, "strip_quant", "strip_imp")
			res, err := e.ApplyStep(context.Background(), sid, &ApplyStepRequest{
				GoalID: gid, Tactic: TacticReq{Type: "by", Chase: &ByChaseReq{Depth: 0}, ByHyps: hyp0()},
			})
			require.NoError(t, err)
			require.True(t, res.Success, "diagnostics: %s", diagnostics(res))
			require.Equal(t, "close", res.Effect)
		})
	}
}

// A homomorphism given by a λ is read by its body whatever its elements
// are: a map out of a module whose elements are numbers closes as the
// same fact at a named map does, and its value at a sum is the sum of
// its values, the leaf spelling each value computed.
func TestByChase_LambdaHomomorphismValuesAreReadByTheBody(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus and the production bundles")
	}
	e := byChaseEngine(t)
	numbers := chaseRing + "∀M:module_ops(A, num). ∀N:module_ops(A, D). ∀g:(num → D). ∀x y:num. "
	composite := chaseRing + "∀M:module_ops(A, B). ∀N:module_ops(A, D). ∀S:(B → C). ∀T:(C → D). ∀x y:B. "
	for _, row := range []struct{ name, stmt string }{
		{"a map out of numbers, at an element", numbers +
			chaseHom("(λk:num. g(k + 1))", "M", "N") + " ∧ x ∈ M.carrier ⇒ g(x + 1) ∈ N.carrier"},
		{"the same map named", numbers +
			chaseHom("g", "M", "N") + " ∧ x ∈ M.carrier ⇒ g(x) ∈ N.carrier"},
		{"a map out of numbers, at a sum", numbers +
			chaseHom("(λk:num. g(k + 1))", "M", "N") + " ∧ x ∈ M.carrier ∧ y ∈ M.carrier ⇒ " +
			"g(M.add(x, y) + 1) = N.add(g(x + 1), g(y + 1))"},
		{"a composite, at a sum", composite +
			chaseHom("(λw:B. T(S(w)))", "M", "N") + " ∧ x ∈ M.carrier ∧ y ∈ M.carrier ⇒ " +
			"T(S(M.add(x, y))) = N.add(T(S(x)), T(S(y)))"},
		{"a composite, at a difference", composite +
			chaseHom("(λw:B. T(S(w)))", "M", "N") + " ∧ x ∈ M.carrier ∧ y ∈ M.carrier ⇒ " +
			"T(S(M.add(x, M.neg(y)))) = N.add(T(S(x)), N.neg(T(S(y))))"},
	} {
		t.Run(row.name, func(t *testing.T) {
			sid, gid := chaseLeaf(t, e, row.stmt, "strip_quant", "strip_imp")
			res, err := e.ApplyStep(context.Background(), sid, &ApplyStepRequest{
				GoalID: gid, Tactic: TacticReq{Type: "by", Chase: &ByChaseReq{Depth: 0}, ByHyps: hyp0()},
			})
			require.NoError(t, err)
			require.True(t, res.Success, "diagnostics: %s", diagnostics(res))
			require.Equal(t, "close", res.Effect)
		})
	}
}

// Cohomology classes inhabit the named carrier and the quotient of the
// restricted degree module; supplied definitions identify those carriers.
func TestByChase_CohomologyModuleDefinitionThroughTheChaptersLaws(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus and the production bundles")
	}
	e := byChaseEngine(t)
	stmt := chaseRing + "∀Q:complex_ops(A, B). ∀n:num. ∀N:module_ops(A, set(B)). ∀f:(set(B) → set(B)). ∀x y:set(B). " +
		chaseHom("f", "cohomology_module(Q, n)", "N") + " ∧ " +
		"x ∈ cohomology(Q, n) ∧ y ∈ cohomology(Q, n) ⇒ " +
		"f(mod_add(cohomology_module(Q, n), x, mod_neg(cohomology_module(Q, n), y))) ∈ N.carrier"
	sid, gid := chaseLeaf(t, e, stmt, "strip_quant", "strip_imp")
	res, err := e.ApplyStep(context.Background(), sid, &ApplyStepRequest{GoalID: gid, Tactic: TacticReq{Type: "by", Chase: &ByChaseReq{Depth: 0}, ByHyps: hyp0()}})
	require.NoError(t, err)
	require.True(t, res.Success, "diagnostics: %s", diagnostics(res))
	require.Equal(t, "close", res.Effect)
}

// Degree modules and record homomorphisms between them must name the same
// module, including when the complexes have different vector types.
func TestByChase_DegreeModulesAndRecordHom(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus and the production bundles")
	}
	e := byChaseEngine(t)
	stmt := chaseRing + "∀P:complex_ops(A, B). ∀Q:complex_ops(A, C). ∀f:(B → C). " +
		chaseModule("complex_module(P, 0)") + " ∧ " + chaseModule("complex_module(Q, 0)") + " ∧ " +
		chaseHom("f", "complex_module(P, 0)", "complex_module(Q, 0)") + " ⇒ " +
		"P.zero ∈ P.terms(0) ∧ f(P.zero) = Q.zero"
	sid, gid := chaseLeaf(t, e, stmt, "strip_quant", "strip_imp")
	res, err := e.ApplyStep(context.Background(), sid, &ApplyStepRequest{GoalID: gid, Tactic: TacticReq{Type: "by", Chase: &ByChaseReq{Depth: 0}, ByHyps: hyp0()}})
	require.NoError(t, err)
	require.True(t, res.Success, "diagnostics: %s", diagnostics(res))
	require.Equal(t, "close", res.Effect)
}

func TestByChase_NormalizedRecordZeroAlias(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus and the production bundles")
	}
	e := byChaseEngine(t)
	stmt := chaseRing + "∀P:complex_ops(A, B). ∀Q:complex_ops(A, C). ∀f:(B → C). ∀b:C. " +
		chaseModule("complex_module(P, 0)") + " ∧ " + chaseModule("complex_module(Q, 0)") + " ∧ " +
		chaseHom("f", "complex_module(P, 0)", "complex_module(Q, 0)") + " ∧ b = Q.zero ⇒ " +
		"P.zero ∈ P.terms(0) ∧ f(P.zero) = b"
	sid, gid := chaseLeaf(t, e, stmt, "strip_quant", "strip_imp")
	res, err := e.ApplyStep(context.Background(), sid, &ApplyStepRequest{GoalID: gid, Tactic: TacticReq{Type: "by", Chase: &ByChaseReq{Depth: 0}, ByHyps: hyp0(), ByShape: &ByShapeReq{Normalized: true}}})
	require.NoError(t, err)
	require.True(t, res.Success, "diagnostics: %s", diagnostics(res))
	require.Equal(t, "close", res.Effect)
}

// Scalar equations use the same production statement, By and kernel doors
// as a chapter. The last two cases require a kernel combination rather than
// merely normalizing a scalar expression already spelled in the goal.
func TestByChase_RScalars(t *testing.T) {
	e := byChaseEngine(t)
	prefix := chaseRing + "∀M:module_ops(A, B). ∀N:module_ops(A, C). ∀K:module_ops(A, D). ∀f h:(B → C). ∀g:(D → B). ∀a b:A. ∀x y:B. ∀z:C. "
	module := chaseModule("M") + " ∧ a ∈ R.carrier ∧ b ∈ R.carrier ∧ x ∈ M.carrier ∧ y ∈ M.carrier"
	hom := chaseHom("f", "M", "N") + " ∧ a ∈ R.carrier ∧ b ∈ R.carrier ∧ x ∈ M.carrier ∧ y ∈ M.carrier ∧ z ∈ N.carrier"
	rows := []struct {
		name, hyps, goal string
		depth            int
		success          bool
	}{
		{"distribute both arguments", module, "M.smul(R.add(a, b), M.add(x, y)) = M.add(M.add(M.smul(a, x), M.smul(b, x)), M.add(M.smul(a, y), M.smul(b, y)))", 0, true},
		{"nested commutative scalars", module, "M.smul(a, M.smul(b, x)) = M.smul(b, M.smul(a, x))", 0, true},
		{"negative scalar and vector", module, "M.smul(R.neg(a), M.neg(x)) = M.smul(a, x)", 0, true},
		{"zero and one", module, "M.smul(R.sub(a, a), x) = M.zero ∧ M.smul(R.one, x) = x", 0, true},
		{"homomorphism action", hom, "f(M.smul(a, M.add(x, M.neg(y)))) = N.add(N.smul(a, f(x)), N.neg(N.smul(a, f(y))))", 0, true},
		{"scale an equation", module + " ∧ x = y", "M.smul(a, x) = M.smul(a, y)", 0, true},
		{"compose scalar relations", module + " ∧ M.smul(a, x) = y", "M.smul(b, y) = M.smul(R.mul(b, a), x)", 0, true},
		{"scalar equality", module + " ∧ R.mul(a, b) = R.one ∧ M.smul(a, x) = M.zero", "x = M.zero", 0, true},
		{"integral gcd combination", module + " ∧ M.smul(R.add(a, a), x) = M.zero ∧ M.smul(R.add(a, R.add(a, a)), x) = M.zero", "M.smul(a, x) = M.zero", 0, true},
		{"scalar equality consequence", module + " ∧ a = b", "R.mul(a, a) = R.mul(b, b)", 0, true},
		{"scalar guarded equation", module + " ∧ a = b ∧ (R.mul(a, a) = R.mul(b, b) ⇒ x = y)", "x = y", 0, true},
		{"linear schema with scaled argument", hom + " ∧ " + chaseHom("h", "M", "N") + " ∧ (∀u:B. u ∈ M.carrier ⇒ f(u) = h(M.smul(a, u)))", "f(M.smul(b, x)) = h(M.smul(R.mul(a, b), x))", 0, true},
		{"zero ring", module + " ∧ R.one = R.zero", "x = M.zero", 0, true},
		{"missing scalar membership refused", chaseHom("f", "M", "N") + " ∧ x ∈ M.carrier", "f(M.smul(a, x)) = N.smul(a, f(x))", 0, false},
		{"image polynomial combination", hom + " ∧ f(x) = z", "∃u:B. u ∈ M.carrier ∧ f(u) = N.smul(R.mul(a, b), z)", 0, true},
		{"injectivity kernel combination", hom + " ∧ injective_on(M.carrier, f) ∧ f(x) = N.smul(a, z) ∧ f(y) = N.smul(b, z)", "M.smul(b, x) = M.smul(a, y)", 1, true},
		{"exactness kernel combination", hom + " ∧ " + chaseHom("g", "K", "M") + " ∧ exact_at(N.zero, K.carrier, M.carrier, g, f) ∧ f(x) = N.smul(a, z) ∧ f(y) = N.smul(b, z)", "∃u:D. u ∈ K.carrier ∧ g(u) = M.add(M.smul(b, x), M.neg(M.smul(a, y)))", 1, true},
		{"characteristic two", module + " ∧ R.add(R.one, R.one) = R.zero", "M.add(x, x) = M.zero", 0, true},
		{"zero divisor kernel", hom + " ∧ " + chaseHom("g", "K", "M") + " ∧ exact_at(N.zero, K.carrier, M.carrier, g, f) ∧ R.mul(a, b) = R.zero ∧ f(x) = N.smul(a, z)", "∃u:D. u ∈ K.carrier ∧ g(u) = M.smul(b, x)", 1, true},
		{"onto scaled target", hom + " ∧ image(f, M.carrier) = N.carrier", "∃u:B. u ∈ M.carrier ∧ f(u) = N.smul(R.mul(a, b), z)", 1, true},
		{"nonunit is not cancelled", module + " ∧ M.smul(a, x) = M.zero", "x = M.zero", 1, false},
		{"torsion survives", module + " ∧ M.add(x, x) = M.zero", "x = M.zero", 1, false},
	}
	for _, row := range rows {
		t.Run(row.name, func(t *testing.T) {
			sid, gid := chaseLeaf(t, e, prefix+row.hyps+" ⇒ "+row.goal, "strip_quant", "strip_imp")
			res, err := e.ApplyStep(context.Background(), sid, &ApplyStepRequest{GoalID: gid, Tactic: TacticReq{Type: "by", Chase: &ByChaseReq{Depth: row.depth}, ByHyps: hyp0()}})
			require.NoError(t, err)
			require.Equal(t, row.success, res.Success, "diagnostics: %+v", res.Diagnostics)
		})
	}
}

// A module's operation packed as a λ is read where the λ is a named
// operation at its own arguments, `λi j. h(i, j)`: in the normal form
// its value is `h(x, y)`, a term applied to the elements. An operation
// that is no such term, `λi j. h(j, i)`, is refused by name: the closer
// writes a sum as one operation applied to its elements.
func TestByChase_OperationPackedAsALambda(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus and the production bundles")
	}
	e := byChaseEngine(t)
	prefix := chaseRing + "∀h:(B → B → B). ∀zero:B. ∀neg:(B → B). ∀smul:(A → B → B). ∀c:set(B). " +
		"∀N:module_ops(A, D). ∀f:(B → D). ∀x y:B. "
	attempt := func(add string) *StepResult {
		stmt := prefix + chaseHom("f", "mk_module("+add+", zero, neg, smul, c)", "N") +
			" ∧ x ∈ c ∧ y ∈ c ⇒ f(h(x, y)) = N.add(f(x), f(y))"
		sid, gid := chaseLeaf(t, e, stmt, "strip_quant", "strip_imp")
		res, err := e.ApplyStep(context.Background(), sid, &ApplyStepRequest{
			GoalID: gid, Tactic: TacticReq{Type: "by", Chase: &ByChaseReq{Depth: 0}, ByHyps: hyp0()},
		})
		require.NoError(t, err)
		return res
	}
	for _, add := range []string{"h", "(λi:B. λj:B. h(i, j))"} {
		res := attempt(add)
		require.True(t, res.Success, "%s: diagnostics: %s", add, diagnostics(res))
	}
	refused := attempt("(λi:B. λj:B. h(j, i))")
	require.False(t, refused.Success)
	require.Contains(t, diagnostics(refused), "gives an operation by a λ")
}
