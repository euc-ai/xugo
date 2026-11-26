package engine

import (
	"context"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/solver/chase"
	"github.com/stretchr/testify/require"
)

// rawScalarChase reaches the closer without By's beta and congruence
// shaping, so certificates must bridge the statement's original terms.
func rawScalarChase(t *testing.T, e *Engine, statement string, depth int) (*prop.PropWrapper, chase.Result) {
	t.Helper()
	info, err := e.CreateSession(context.Background())
	require.NoError(t, err)
	s, err := e.getSession(info.ID)
	require.NoError(t, err)
	parsed := dsl.ParsePropTextInScope(statement, s.StatementDoorScope())
	require.Empty(t, parsed.Errors)
	body := parsed.Prop.Conclusion()
	for {
		a := ext.MatchesFORALL(body)
		if a.IsZero() {
			break
		}
		body = a.Body()
	}
	hyp, goal, ok := ext.MatchesIMPLY(body)
	require.True(t, ok)
	p := core.MakeProp(goal, hyp)
	proof, result, err := chase.Close(p, chase.Options{Depth: depth})
	require.NoError(t, err)
	if proof != nil {
		require.True(t, prop.IsStronger(proof, p))
	}
	return proof, result
}

func TestByChase_RScalarOpaqueSchemaIsBounded(t *testing.T) {
	e := byChaseEngine(t)
	statement := chaseRing + "∀M:module_ops(A, B). ∀F:(B → B). ∀x y:B. module_on(R, M) ∧ x ∈ M.carrier ∧ y ∈ M.carrier ∧ (∀u:B. u ∈ M.carrier ⇒ F(u) = u) ⇒ x = y"
	proof, result := rawScalarChase(t, e, statement, 0)
	require.Nil(t, proof)
	require.Contains(t, result.Report, "schema")
	require.NotContains(t, result.Report, "resource limit")
	statement = chaseRing + "∀M:module_ops(A, B). ∀F:(B → B). ∀x y:B. module_on(R, M) ∧ x ∈ M.carrier ∧ y ∈ M.carrier ∧ (∀u:B. u ∈ M.carrier ⇒ F((λv:B. v)(u)) = u) ⇒ M.add(x, y) = M.add(y, x)"
	proof, result = rawScalarChase(t, e, statement, 0)
	require.NotNil(t, proof, result.Report)
}

func TestByChase_RScalarLambdaImage(t *testing.T) {
	e := byChaseEngine(t)
	prefix := chaseRing + "∀M:module_ops(A, B). ∀N:module_ops(A, C). ∀f:(B → C). ∀a b:A. ∀x:B. "
	scaled := "(λu:B. N.smul(b, f(u)))"
	hyps := chaseHom("f", "M", "N") + " ∧ " + chaseHom(scaled, "M", "N") + " ∧ a ∈ R.carrier ∧ b ∈ R.carrier ∧ x ∈ M.carrier ∧ M.smul(a, x) ∈ M.carrier"
	for _, goal := range []string{
		scaled + "(M.smul(a, x)) = N.smul(R.mul(a, b), f(x))",
		scaled + "(M.neg(x)) = N.neg(N.smul(b, f(x)))",
		scaled + "(M.zero) = N.zero",
	} {
		proof, result := rawScalarChase(t, e, prefix+hyps+" ⇒ "+goal, 0)
		require.NotNil(t, proof, result.Report)
	}
	// The homomorphism declaration supplies linearity even when its
	// beta body is an otherwise opaque function application.
	opaque := "(λu:B. f(u))"
	opaqueHyps := chaseHom(opaque, "M", "N") + " ∧ a ∈ R.carrier ∧ x ∈ M.carrier"
	proof, result := rawScalarChase(t, e, prefix+opaqueHyps+" ⇒ "+opaque+"(M.smul(a, x)) = N.smul(a, "+opaque+"(x))", 0)
	require.NotNil(t, proof, result.Report)
}

func TestByChase_RScalarBetaRelationPropagation(t *testing.T) {
	e := byChaseEngine(t)
	stmt := chaseRing + "∀M:module_ops(A, B). ∀N:module_ops(A, C). ∀f:(B → C). ∀x y:B. " + chaseHom("f", "M", "N") + " ∧ x ∈ M.carrier ∧ y ∈ M.carrier ∧ (λu:B. u)(x) = y ⇒ f(x) = f(y)"
	proof, result := rawScalarChase(t, e, stmt, 0)
	require.NotNil(t, proof, result.Report)
}

func TestByChase_RScalarBetaGeneratorMembership(t *testing.T) {
	e := byChaseEngine(t)
	stmt := chaseRing + "∀M:module_ops(A, B). ∀F:(B → B). ∀x:B. module_on(R, M) ∧ F((λu:B. u)(x)) ∈ M.carrier ⇒ M.add(F((λu:B. u)(x)), M.zero) = F((λu:B. u)(x))"
	proof, result := rawScalarChase(t, e, stmt, 0)
	require.NotNil(t, proof, result.Report)
}

func TestByChase_RScalarBetaExactnessWitness(t *testing.T) {
	e := byChaseEngine(t)
	stmt := chaseRing + "∀K:module_ops(A, B). ∀M:module_ops(A, C). ∀N:module_ops(A, D). ∀g:(B → C). ∀f:(C → D). ∀x:B. " + chaseHom("g", "K", "M") + " ∧ " + chaseHom("f", "M", "N") + " ∧ exact_at(N.zero, K.carrier, M.carrier, g, f) ∧ x ∈ K.carrier ∧ (λu:B. u)(x) ∈ K.carrier ⇒ f(g(x)) = N.zero"
	proof, result := rawScalarChase(t, e, stmt, 0)
	require.NotNil(t, proof, result.Report)
}

func TestByChase_RScalarSchemaOpaqueTarget(t *testing.T) {
	e := byChaseEngine(t)
	stmt := chaseRing + "∀M:module_ops(A, B). ∀N:module_ops(A, C). ∀F f:(B → C). ∀x:B. " + chaseHom("f", "M", "N") + " ∧ x ∈ M.carrier ∧ (∀u:B. u ∈ M.carrier ⇒ F(u) = f(u)) ⇒ F(x) = f(x)"
	proof, result := rawScalarChase(t, e, stmt, 0)
	require.NotNil(t, proof, result.Report)
	for _, hom := range []string{"h", "(λv:B. h(v))"} {
		prefix := chaseRing + "∀M N:module_ops(A, B). ∀F h:(B → B). ∀x y z:B. " + chaseHom(hom, "N", "M") + " ∧ x ∈ M.carrier ∧ y ∈ M.carrier ∧ z ∈ N.carrier ∧ (∀u:B. u ∈ M.carrier ⇒ F(u) = z) ⇒ "
		proof, result = rawScalarChase(t, e, prefix+"x = y", 0)
		require.Nil(t, proof)
		require.NotContains(t, result.Report, "resource limit")
		proof, result = rawScalarChase(t, e, prefix+"M.add(x, y) = M.add(y, x)", 0)
		require.NotNil(t, proof, result.Report)
	}
}
