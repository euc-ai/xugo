package proof

import (
	"strings"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/stretchr/testify/require"
)

// inductiveTestEnv is a fresh const-meta service carrying the set and
// recspace constructors the four charter shapes spell, and a parse scope over it.
func inductiveTestEnv(t *testing.T) (*ProverEnv, *dsl.ParseScope) {
	t.Helper()
	env := &ProverEnv{ProofService: MockConstMetaService(), LibraryThms: map[string]Thm{}}
	A := MakeVarType("A")
	setA := MakeFun(A, TypeBool)
	numARel := MakeFun(NumType, A, TypeBool)
	for _, meta := range []ConstTermMeta{
		MakeConstMeta("empty_set", setA),
		MakeConstMeta("insert", MakeFun(A, setA, setA)),
		MakeConstMeta("encoded_bottom", numARel),
		MakeConstMeta("encoded_node", MakeFun(NumType, A, MakeFun(NumType, numARel), numARel)),
	} {
		env.ProofService.LoadOrStoreConstMeta(meta)
	}
	scope := &dsl.ParseScope{
		ConstResolver: func(name string) ConstTermMeta {
			if meta, ok := env.ProofService.LoadConstMeta(TermName(name)); ok {
				return meta
			}
			return ConstTermMeta{}
		},
	}
	return env, scope
}

// inductiveFixture analyzes and mints one definition from texts.
func inductiveFixture(t *testing.T, env *ProverEnv, scope *dsl.ParseScope, name, typeText string, params []string, rules ...string) (*InductiveDefinition, ConstTerm) {
	t.Helper()
	props := make([]Prop, len(rules))
	var defVar VarTerm
	var paramVars []VarTerm
	for i, text := range rules {
		p, dv, pv, err := ParseInductiveRule(text, name, typeText, params, scope)
		require.NoError(t, err, "rule %d", i)
		props[i], defVar, paramVars = p, dv, pv
	}
	d, err := AnalyzeInductiveDefinition(defVar, paramVars, props)
	require.NoError(t, err)
	c, err := MintInductiveDefinition(env, d)
	require.NoError(t, err)
	return d, c
}

// expectStmt parses an expected statement with the minted constant in
// scope and checks the computed statement and the derived theorem
// against it.
func expectStmt(t *testing.T, scope *dsl.ParseScope, d *InductiveDefinition, c ConstTerm, k InductiveTheoremKind, text string) {
	t.Helper()
	strict := *scope
	strict.StrictResolution = true
	strict.FreshenMetaLetters = true
	res := dsl.ParsePropTextInScope(text, &strict)
	require.Empty(t, res.Errors, "%v expected text %q", k, text)
	stmt := d.Stmt(c, k)
	require.True(t, stmt.AlphaEquals(res.Prop), "%v statement: computed %s, expected %s", k, PrintProp(stmt), text)
	derived := DeriveInductiveTheorem(d, c, k)
	require.Equal(t, 0, derived.NumHyps())
	require.True(t, derived.AlphaEquals(stmt))
	require.True(t, derived.Proved(), "%v derived theorem must carry a certificate", k)
}

func TestInductive_FiniteShape(t *testing.T) {
	env, scope := inductiveTestEnv(t)
	d, c := inductiveFixture(t, env, scope, "zfinite", "(A → bool) → bool", nil,
		"zfinite(empty_set)",
		"∀x:A. ∀s:(A → bool). zfinite(s) ⇒ zfinite(insert(x, s))")
	require.Len(t, d.Rules, 2)
	require.True(t, IsInductiveConstDef(c))
	expectStmt(t, scope, d, c, InductiveRules,
		"zfinite⟨A:A⟩(empty_set⟨A:A⟩) ∧ (∀x:A. ∀s:(A → bool). zfinite(s) ⇒ zfinite(insert(x, s)))")
	expectStmt(t, scope, d, c, InductiveInduct,
		"∀P:((A → bool) → bool). ∀t:(A → bool). P(empty_set⟨A:A⟩) ∧ (∀x:A. ∀s:(A → bool). P(s) ⇒ P(insert(x, s))) ∧ zfinite(t) ⇒ P(t)")
	expectStmt(t, scope, d, c, InductiveCases,
		"∀s:(A → bool). zfinite(s) ⇔ s = empty_set ∨ (∃x:A. ∃t:(A → bool). s = insert(x, t) ∧ zfinite(t))")

	expectStmt(t, scope, d, c, InductiveInductStrong,
		"∀P:((A → bool) → bool). ∀t:(A → bool). P(empty_set⟨A:A⟩) ∧ (∀x:A. ∀s:(A → bool). zfinite(s) ∧ P(s) ⇒ P(insert(x, s))) ∧ zfinite(t) ⇒ P(t)")
	require.Equal(t, InductiveKinds(), d.Kinds(), "a rule with a recursive premise gets the strengthened induction")

	// The record round-trips: the constant, the parameters and the
	// rules recover the definition, and the minted body is its closure.
	recovered, err := RecoverInductiveDefinition(c, d.Params, d.RuleTerms)
	require.NoError(t, err)
	require.True(t, recovered.Body.AlphaEquals(d.Body))

	// The unfold surfaces refuse the closure form by name.
	err = InductiveUnfoldRefusal(c)
	require.Error(t, err)
	require.Contains(t, err.Error(), "not a proof surface")
	require.Contains(t, err.Error(), "zfinite")
}

func TestInductive_InfinitePremise(t *testing.T) {
	env, scope := inductiveTestEnv(t)
	d, c := inductiveFixture(t, env, scope, "zrec", "(num → A → bool) → bool", nil,
		"zrec(encoded_bottom)",
		"∀c:num. ∀i:A. ∀r:(num → num → A → bool). (∀n:num. zrec(r(n))) ⇒ zrec(encoded_node(c, i, r))")
	expectStmt(t, scope, d, c, InductiveRules,
		"zrec⟨A:A⟩(encoded_bottom⟨A:A⟩) ∧ ∀c:num. ∀i:A. ∀r:(num → num → A → bool). (∀n:num. zrec(r(n))) ⇒ zrec(encoded_node(c, i, r))")
	expectStmt(t, scope, d, c, InductiveInduct,
		"∀P:((num → A → bool) → bool). ∀a:(num → A → bool). P(encoded_bottom⟨A:A⟩) ∧ (∀c:num. ∀i:A. ∀r:(num → num → A → bool). (∀n:num. P(r(n))) ⇒ P(encoded_node(c, i, r))) ∧ zrec(a) ⇒ P(a)")
	expectStmt(t, scope, d, c, InductiveCases,
		"∀a:(num → A → bool). zrec(a) ⇔ a = encoded_bottom ∨ (∃c:num. ∃i:A. ∃r:(num → num → A → bool). a = encoded_node(c, i, r) ∧ (∀n:num. zrec(r(n))))")
	// Strengthening reaches under the premise's ∀.
	expectStmt(t, scope, d, c, InductiveInductStrong,
		"∀P:((num → A → bool) → bool). ∀a:(num → A → bool). P(encoded_bottom⟨A:A⟩) ∧ (∀c:num. ∀i:A. ∀r:(num → num → A → bool). (∀n:num. zrec(r(n)) ∧ P(r(n))) ⇒ P(encoded_node(c, i, r))) ∧ zrec(a) ⇒ P(a)")
}

func TestInductive_ParameterAndGuardedPremise(t *testing.T) {
	env, scope := inductiveTestEnv(t)
	d, c := inductiveFixture(t, env, scope, "zacc", "(A → A → bool) → A → bool", []string{"R"},
		"∀x:A. (∀y:A. R(y, x) ⇒ zacc(R, y)) ⇒ zacc(R, x)")
	require.Len(t, d.Params, 1)
	expectStmt(t, scope, d, c, InductiveRules,
		"∀R:(A → A → bool). ∀x:A. (∀y:A. R(y, x) ⇒ zacc(R, y)) ⇒ zacc(R, x)")
	expectStmt(t, scope, d, c, InductiveInduct,
		"∀R:(A → A → bool). ∀P:(A → bool). ∀a:A. (∀x:A. (∀y:A. R(y, x) ⇒ P(y)) ⇒ P(x)) ∧ zacc(R, a) ⇒ P(a)")
	expectStmt(t, scope, d, c, InductiveCases,
		"∀R:(A → A → bool). ∀a:A. zacc(R, a) ⇔ ∀y:A. R(y, a) ⇒ zacc(R, y)")
	// Strengthening reaches under the premise's ∀ AND its guard — the
	// shape the well_founded chapter's accessibility induction wants.
	expectStmt(t, scope, d, c, InductiveInductStrong,
		"∀R:(A → A → bool). ∀P:(A → bool). ∀a:A. (∀x:A. (∀y:A. R(y, x) ⇒ zacc(R, y) ∧ P(y)) ⇒ P(x)) ∧ zacc(R, a) ⇒ P(a)")
}

func TestInductive_BinaryRelationTwoPremises(t *testing.T) {
	env, scope := inductiveTestEnv(t)
	d, c := inductiveFixture(t, env, scope, "ztc", "(A → A → bool) → A → A → bool", []string{"R"},
		"∀x y:A. R(x, y) ⇒ ztc(R, x, y)",
		"∀x y z:A. ztc(R, x, y) ∧ ztc(R, y, z) ⇒ ztc(R, x, z)")
	expectStmt(t, scope, d, c, InductiveRules,
		"∀R:(A → A → bool). (∀x y:A. R(x, y) ⇒ ztc(R, x, y)) ∧ (∀x y z:A. ztc(R, x, y) ∧ ztc(R, y, z) ⇒ ztc(R, x, z))")
	expectStmt(t, scope, d, c, InductiveInduct,
		"∀R:(A → A → bool). ∀P:(A → A → bool). ∀a b:A. (∀x y:A. R(x, y) ⇒ P(x, y)) ∧ (∀x y z:A. P(x, y) ∧ P(y, z) ⇒ P(x, z)) ∧ ztc(R, a, b) ⇒ P(a, b)")
	expectStmt(t, scope, d, c, InductiveCases,
		"∀R:(A → A → bool). ∀a b:A. ztc(R, a, b) ⇔ R(a, b) ∨ (∃y:A. ztc(R, a, y) ∧ ztc(R, y, b))")
	// Two premises, both strengthened; the side condition R(x, y) is not.
	expectStmt(t, scope, d, c, InductiveInductStrong,
		"∀R:(A → A → bool). ∀P:(A → A → bool). ∀a b:A. (∀x y:A. R(x, y) ⇒ P(x, y)) ∧ (∀x y z:A. (ztc(R, x, y) ∧ P(x, y)) ∧ (ztc(R, y, z) ∧ P(y, z)) ⇒ P(x, z)) ∧ ztc(R, a, b) ⇒ P(a, b)")
}

// TestInductive_RepeatedIndex: a rule whose conclusion repeats an index
// term — permutation's `R(nil, nil)`, spelled here over the env's set
// constructors — makes the per-rule step and the Cases ⇐ direction
// conjoin the same reflexive equation twice. The conjunction's
// hypotheses are a set, so the second copy has nothing left to
// discharge; every theorem of the definition must still derive.
func TestInductive_RepeatedIndex(t *testing.T) {
	env, scope := inductiveTestEnv(t)
	d, c := inductiveFixture(t, env, scope, "zperm", "(A → bool) → (A → bool) → bool", nil,
		"zperm(empty_set, empty_set)",
		"∀x:A. ∀s t:(A → bool). zperm(s, t) ⇒ zperm(insert(x, s), insert(x, t))",
		"∀x y:A. ∀s:(A → bool). zperm(insert(x, insert(y, s)), insert(y, insert(x, s)))",
		"∀s t u:(A → bool). zperm(s, t) ∧ zperm(t, u) ⇒ zperm(s, u)")
	for _, k := range d.Kinds() {
		derived := DeriveInductiveTheorem(d, c, k)
		require.Equal(t, 0, derived.NumHyps(), "%v", k)
		require.True(t, derived.AlphaEquals(d.Stmt(c, k)), "%v", k)
		require.True(t, derived.Proved(), "%v derived theorem must carry a certificate", k)
	}
}

// TestInductive_NoPremiseHasNoStrongInduction: with nothing to
// strengthen the strong principle IS the plain one, so the door does
// not offer it — two entries would carry one key.
func TestInductive_NoPremiseHasNoStrongInduction(t *testing.T) {
	env, scope := inductiveTestEnv(t)
	d, c := inductiveFixture(t, env, scope, "zflat", "(A → bool) → bool", nil,
		"zflat(empty_set)",
		"∀x:A. zflat(insert(x, empty_set))")
	require.Equal(t,
		[]InductiveTheoremKind{InductiveRules, InductiveInduct, InductiveCases}, d.Kinds())
	require.True(t, d.Stmt(c, InductiveInductStrong).AlphaEquals(d.Stmt(c, InductiveInduct)),
		"with no premise to strengthen the two statements are one")
}

func TestInductive_Refusals(t *testing.T) {
	_, scope := inductiveTestEnv(t)
	parse := func(name, typeText string, params []string, rule string) error {
		p, dv, pv, err := ParseInductiveRule(rule, name, typeText, params, scope)
		if err != nil {
			return err
		}
		_, err = AnalyzeInductiveDefinition(dv, pv, []Prop{p})
		return err
	}
	// The relation under ∃ is outside the first charter.
	err := parse("zbad1", "(A → bool) → bool", nil, "∀s:(A → bool). (∃x:A. zbad1(insert(x, s))) ⇒ zbad1(s)")
	require.Error(t, err)
	require.Contains(t, err.Error(), "outside it")
	// A guard mentioning the relation is refused by name.
	err = parse("zbad2", "(A → A → bool) → A → bool", []string{"R"}, "∀x:A. (∀y:A. zbad2(R, y) ⇒ R(y, x)) ⇒ zbad2(R, x)")
	require.Error(t, err)
	require.Contains(t, err.Error(), "guard mentions")
	// A parameter must be passed unchanged at every occurrence.
	err = parse("zbad3", "(A → A → bool) → A → A → bool", []string{"R"}, "∀x y:A. zbad3(R, x, y) ⇒ zbad3(λu:A. λv:A. R(v, u), y, x)")
	require.Error(t, err)
	require.True(t, strings.Contains(err.Error(), "not the parameter"), err.Error())
	// The definiendum must not already be a constant.
	err = parse("empty_set", "(A → bool) → bool", nil, "empty_set(empty_set)")
	require.Error(t, err)
	require.Contains(t, err.Error(), "already names a constant")
	// Not a predicate.
	_, _, _, err = ParseInductiveRule("zbad4(x) = x", "zbad4", "A → A", nil, scope)
	require.Error(t, err)
	require.Contains(t, err.Error(), "does not end in bool")
	// A plain definition is not an inductive one.
	require.False(t, IsInductiveConstDef(core.NewConstDef(T, "zplain")))
}
