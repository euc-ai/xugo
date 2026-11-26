package engine

import (
	"context"
	"strings"
	"testing"

	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/stretchr/testify/require"
)

// TestByArith_StructureRing_Complex: ℂ is a field by complex_field.Field,
// an installed instance of the structure ring (omega/structure_ring.go),
// so a ring identity over ℂ closes by one bare `by {arith:true}` — no
// componentwise Simp(Parts, …) first — and so does an integer
// combination of the context's equations, including one whose
// polynomial coefficients were supplied as scaled equations.
func TestByArith_StructureRing_Complex(t *testing.T) {
	e := byArithEngine(t)
	runByArithRows(t, e, []byArithRow{
		{"binomial square over ℂ, with a literal coefficient",
			"∀z w:complex. complex_mul(complex_add(z, w), complex_add(z, w)) = complex_add(complex_add(complex_mul(z, z), complex_mul(complex_of_real(&2), complex_mul(z, w))), complex_mul(w, w))",
			[]string{"strip_quant"}, nil},
		{"difference of squares over ℂ",
			"∀z w:complex. complex_mul(complex_sub(z, w), complex_add(z, w)) = complex_sub(complex_mul(z, z), complex_mul(w, w))",
			[]string{"strip_quant"}, nil},
		{"negation through a product",
			"∀z w:complex. complex_neg(complex_mul(z, w)) = complex_mul(z, complex_neg(w))",
			[]string{"strip_quant"}, nil},
		{"a quotient is a product with the inverse",
			"∀z w:complex. complex_div(complex_add(z, w), w) = complex_add(complex_div(z, w), complex_div(w, w))",
			[]string{"strip_quant"}, nil},
		{"the cube of a sum, coefficient 3",
			"∀z w:complex. complex_mul(complex_add(z, w), complex_mul(complex_add(z, w), complex_add(z, w))) = complex_add(complex_add(complex_add(complex_mul(z, complex_mul(z, z)), complex_mul(complex_of_real(&3), complex_mul(z, complex_mul(z, w)))), complex_mul(complex_of_real(&3), complex_mul(z, complex_mul(w, w)))), complex_mul(w, complex_mul(w, w)))",
			[]string{"strip_quant"}, nil},
		{"a repeated compound factor that is zero",
			"∀c:complex. complex_mul(complex_sub(c, c), complex_sub(c, c)) = complex_of_real(&0)",
			[]string{"strip_quant"}, nil},
		{"the same beside a cofactor",
			"∀c:complex. ∀f:complex→complex. complex_mul(complex_mul(complex_sub(c, c), complex_sub(c, c)), f(c)) = complex_of_real(&0)",
			[]string{"strip_quant"}, nil},
		{"an integer combination of two equations",
			"∀a b c d:complex. a = complex_add(b, c) ⇒ d = c ⇒ complex_sub(a, b) = d",
			[]string{"strip_quant", "strip_imp", "strip_imp"}, []int{0, 1}},
		{"polynomial coefficients supplied as scaled equations",
			"∀a b c d e:complex. complex_mul(e, a) = complex_mul(e, complex_mul(b, c)) ⇒ complex_mul(b, d) = complex_mul(b, complex_mul(c, e)) ⇒ complex_mul(a, e) = complex_mul(b, d)",
			[]string{"strip_quant", "strip_imp", "strip_imp"}, []int{0, 1}},
	})
}

// TestByArith_StructureRing_ComplexUnitFacts: over ℂ a factor and its
// inverse cancel wherever they stand in a monomial, on a resident
// statement that the factor is not zero or, for an embedded real, on ℝ's
// own evidence — the primitive αz + βz²/2 of a linear function
// differentiates back by one bare `by {arith:true}` with no premise at
// all, complex_of_real(&2) being nonzero as &2 is — and with no evidence
// nothing cancels.
func TestByArith_StructureRing_ComplexUnitFacts(t *testing.T) {
	e := byArithEngine(t)
	primitive := "complex_add(complex_mul(α, complex_of_real(&1)), complex_mul(complex_div(β, complex_of_real(&2)), complex_add(complex_mul(complex_of_real(&1), u), complex_mul(u, complex_of_real(&1))))) = complex_add(α, complex_mul(β, u))"
	byRadius := "complex_mul(complex_div(x, complex_of_real(r)), complex_of_real(r)) = x"
	runByArithRows(t, e, []byArithRow{
		{"the primitive of a linear function, differentiated back, the 2 stated nonzero",
			"∀α β u:complex. ¬(complex_of_real(&2) = complex_of_real(&0)) ⇒ " + primitive,
			[]string{"strip_quant", "strip_imp"}, []int{0}},
		{"the primitive of a linear function, differentiated back, no premise",
			"∀α β u:complex. " + primitive,
			[]string{"strip_quant"}, nil},
		{"a quotient by an embedded real of resident sign",
			"∀x:complex. ∀r:real. &0 < r ⇒ " + byRadius,
			[]string{"strip_quant", "strip_imp"}, []int{0}},
		{"a quotient times its divisor",
			"∀x y:complex. ¬(y = complex_of_real(&0)) ⇒ complex_mul(complex_div(x, y), y) = x",
			[]string{"strip_quant", "strip_imp"}, []int{0}},
		{"a difference quotient times its offset, from z ≠ c",
			"∀f p z c:complex. ¬(z = c) ⇒ complex_mul(complex_div(complex_sub(f, p), complex_sub(z, c)), complex_sub(z, c)) = complex_sub(f, p)",
			[]string{"strip_quant", "strip_imp"}, []int{0}},
	})
	ctx := context.Background()
	for _, stmt := range []string{
		"∀x y:complex. complex_mul(complex_div(x, y), y) = x",
		"∀x:complex. ∀r:real. " + byRadius,
		"∀x:complex. complex_mul(complex_div(x, complex_of_real(&0)), complex_of_real(&0)) = x",
	} {
		info, err := e.CreateSession(ctx)
		require.NoError(t, err)
		s, err := e.getSession(info.ID)
		require.NoError(t, err)
		parsed := dsl.ParsePropTextInScope(stmt, &dsl.ParseScope{
			ConstResolver: envConstResolver(s.env), StrictResolution: true, FreshenMetaLetters: true,
		})
		require.Empty(t, parsed.Errors, "add-goal %q", stmt)
		s.mu.Lock()
		gid := s.AddGoal(parsed.Prop)
		s.mu.Unlock()
		res, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{GoalID: gid, Tactic: TacticReq{Type: "strip_quant"}})
		require.NoError(t, err)
		require.Len(t, res.Produced, 1)
		res, err = e.ApplyStep(ctx, info.ID, &ApplyStepRequest{GoalID: res.Produced[0].GoalID,
			Tactic: TacticReq{Type: "by", Arith: true}})
		require.NoError(t, err)
		require.NotEqual(t, "close", res.Effect, "cancelled a factor with no evidence that it is nonzero: %s", stmt)
	}
}

// TestByArith_StructureRing_Abstract: a goal of an abstract chapter — the
// ring is a resident hypothesis `comm_ring(R)` at a record R over a type
// variable — closes by `by {arith:true}` with the fact named, the laws
// read at the record's components.
func TestByArith_StructureRing_Abstract(t *testing.T) {
	e := byArithEngine(t)
	ring := "∀R:ring_ops(A). comm_ring(R) ⇒ "
	runByArithRowsIn(t, e, constSyntax(), []byArithRow{
		{"binomial square at the fact",
			ring + "∀x y:A. R.mul(R.add(x, y), R.add(x, y)) = R.add(R.add(R.mul(x, x), R.mul(R.add(R.one, R.one), R.mul(x, y))), R.mul(y, y))",
			[]string{"strip_quant", "strip_imp", "strip_quant"}, []int{0}},
		{"difference of squares at the fact",
			ring + "∀x y:A. R.mul(R.sub(x, y), R.add(x, y)) = R.sub(R.mul(x, x), R.mul(y, y))",
			[]string{"strip_quant", "strip_imp", "strip_quant"}, []int{0}},
		{"a combination of two equations at the fact",
			ring + "∀x y u v:A. x = y ⇒ u = v ⇒ R.add(x, u) = R.add(y, v)",
			[]string{"strip_quant", "strip_imp", "strip_quant", "strip_imp", "strip_imp"}, []int{0, 1, 2}},
	})
	// A ring on a carrier SET: the fact and the atoms' memberships named.
	ringOn := "∀R:ring_ops(A). comm_ring_on(R) ⇒ "
	runByArithRowsIn(t, e, constSyntax(), []byArithRow{
		{"binomial square at a ring on a carrier set, the memberships one conjunction",
			ringOn + "∀x y:A. x ∈ R.carrier ∧ y ∈ R.carrier ⇒ R.mul(R.add(x, y), R.add(x, y)) = R.add(R.add(R.mul(x, x), R.mul(R.add(R.one, R.one), R.mul(x, y))), R.mul(y, y))",
			[]string{"strip_quant", "strip_imp", "strip_quant", "strip_imp"}, []int{0, 1}},
		{"difference of squares at a ring on a carrier set",
			ringOn + "∀x y:A. x ∈ R.carrier ∧ y ∈ R.carrier ⇒ R.mul(R.sub(x, y), R.add(x, y)) = R.sub(R.mul(x, x), R.mul(y, y))",
			[]string{"strip_quant", "strip_imp", "strip_quant", "strip_imp"}, []int{0, 1}},
		{"a negated square at a ring on a carrier set",
			ringOn + "∀x:A. x ∈ R.carrier ⇒ R.mul(R.neg(x), R.neg(x)) = R.mul(x, x)",
			[]string{"strip_quant", "strip_imp", "strip_quant", "strip_imp"}, []int{0, 1}},
		{"a negated square at a field on a carrier set",
			"∀F:field_ops(A). field_on(F) ⇒ ∀x:A. x ∈ F.carrier ⇒ F.mul(F.neg(x), F.neg(x)) = F.mul(x, x)",
			[]string{"strip_quant", "strip_imp", "strip_quant", "strip_imp"}, []int{0, 1}},
	})
}

// TestByArith_ScaledPremise: a premise with a coefficient (the Go
// Scaled(c, h), the session's `coefficient`) is followed by its
// congruence c·l = c·r, which the equality deciders then combine by
// integers — Lean's linear_combination, over ℂ (the structure ring) and
// over ℝ (the twin's monomial basis) alike. The recorded step renders
// back as Scaled(…). The equations scaled here define no variable — each
// has a sum on its left; one that does is read at the definition and
// needs no coefficient (TestByArith_EquationUnderAProduct).
func TestByArith_ScaledPremise(t *testing.T) {
	e := byArithEngine(t)
	ctx := context.Background()
	idx := func(i int) *int { return &i }
	rows := []struct {
		name, stmt, family string
	}{
		{"over ℂ", "∀p q u v b c e:complex. complex_add(p, q) = complex_mul(b, c) ⇒ complex_add(u, v) = complex_mul(c, e) ⇒ " +
			"complex_mul(complex_add(p, q), e) = complex_mul(b, complex_add(u, v))", "complex/complex_field"},
		{"over ℝ", "∀p q u v b c e:real. p + q = b * c ⇒ u + v = c * e ⇒ (p + q) * e = b * (u + v)", "real/real_field"},
	}
	for _, r := range rows {
		t.Run(r.name, func(t *testing.T) {
			info, err := e.CreateSession(ctx)
			require.NoError(t, err)
			s, err := e.getSession(info.ID)
			require.NoError(t, err)
			parsed := dsl.ParsePropTextInScope(r.stmt, &dsl.ParseScope{
				ConstResolver: envConstResolver(s.env), StrictResolution: true, FreshenMetaLetters: true,
			})
			require.Empty(t, parsed.Errors, "add-goal %q", r.stmt)
			s.mu.Lock()
			gid := s.AddGoal(parsed.Prop)
			s.mu.Unlock()
			for _, typ := range []string{"strip_quant", "strip_imp", "strip_imp"} {
				res, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{GoalID: gid, Tactic: TacticReq{Type: typ}})
				require.NoError(t, err)
				require.Len(t, res.Produced, 1)
				gid = res.Produced[0].GoalID
			}
			// Without the coefficients the equations do not combine by integers.
			bare, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{GoalID: gid,
				Tactic: TacticReq{Type: "by", Arith: true, ByHyps: []ByHypSpec{{HypIndex: idx(0)}, {HypIndex: idx(1)}}}})
			require.True(t, err != nil || bare.Effect != "close", "closed without the polynomial coefficients")
			res, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{GoalID: gid,
				Tactic: TacticReq{Type: "by", Arith: true, ByHyps: []ByHypSpec{
					{HypIndex: idx(0), Coefficient: "e"},
					{HypIndex: idx(1), Coefficient: "b"},
				}}})
			require.NoError(t, err)
			require.Equal(t, "close", res.Effect, "%s did not close with the scaled premises", r.name)
			out, err := e.EmitSection(&EmitSectionRequest{SessionID: info.ID, Section: 0, FuncName: "Build_SCALED", Family: r.family})
			require.NoError(t, err)
			// The coefficients and the premises are the closure's
			// parameters, the opening strips lifted into its signature.
			require.Contains(t, out.Go, "Scaled(e, h)", "the scaled premise renders as Scaled(coefficient, fact)\n--- source: ---\n%s", out.Go)
			require.Contains(t, out.Go, "Scaled(b, h2)", "--- source: ---\n%s", out.Go)
			require.Contains(t, out.Go, ", h, h2 Fact) {", "--- source: ---\n%s", out.Go)
			require.NotContains(t, out.Go, "ctx.Var(", "--- source: ---\n%s", out.Go)
		})
	}
}

// TestByArith_StructureRing_AtomEquation: an equation between two atoms
// of a ring on a carrier set, `p = r`, closes by `by {arith:true}` from a
// premise pinning their difference — the memberships and the equation
// one conjunction, as a card's hypothesis arrives — and from two
// equations through a third atom; an equation premise over an atom whose
// membership the premises lack is not read, and the decline names the
// atom, as it names a missing atom of the goal.
func TestByArith_StructureRing_AtomEquation(t *testing.T) {
	e := byArithEngine(t)
	ringOn := "∀R:ring_ops(A). comm_ring_on(R) ⇒ "
	runByArithRowsIn(t, e, constSyntax(), []byArithRow{
		{"two atoms from their difference, the premise one conjunction",
			ringOn + "∀p r:A. p ∈ R.carrier ∧ r ∈ R.carrier ∧ R.sub(p, r) = R.zero ⇒ p = r",
			[]string{"strip_quant", "strip_imp", "strip_quant", "strip_imp"}, []int{0, 1}},
		{"two atoms through a third",
			ringOn + "∀p r u:A. p ∈ R.carrier ∧ r ∈ R.carrier ∧ u ∈ R.carrier ∧ R.add(p, u) = R.add(r, u) ⇒ p = r",
			[]string{"strip_quant", "strip_imp", "strip_quant", "strip_imp"}, []int{0, 1}},
	})
	// The decline names the atom of the unread equation premise.
	ctx := context.Background()
	idx := func(i int) *int { return &i }
	stmt := ringOn + "∀p r u:A. p ∈ R.carrier ∧ r ∈ R.carrier ∧ R.add(p, u) = R.add(r, u) ⇒ p = r"
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, err := e.getSession(info.ID)
	require.NoError(t, err)
	parsed := dsl.ParsePropTextInScope(stmt, &dsl.ParseScope{
		ConstResolver: envConstResolver(s.env), StrictResolution: true, FreshenMetaLetters: true, Syntax: constSyntax(),
	})
	require.Empty(t, parsed.Errors, "add-goal %q", stmt)
	s.mu.Lock()
	gid := s.AddGoal(parsed.Prop)
	s.mu.Unlock()
	for _, typ := range []string{"strip_quant", "strip_imp", "strip_quant", "strip_imp"} {
		res, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{GoalID: gid, Tactic: TacticReq{Type: typ}})
		require.NoError(t, err, "strip %s", typ)
		require.Len(t, res.Produced, 1, "strip %s", typ)
		gid = res.Produced[0].GoalID
	}
	res, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{GoalID: gid,
		Tactic: TacticReq{Type: "by", Arith: true, ByHyps: []ByHypSpec{{HypIndex: idx(0)}, {HypIndex: idx(1)}}}})
	require.NoError(t, err)
	require.NotEqual(t, "close", res.Effect, "closed without u's membership")
	require.NotEmpty(t, res.Diagnostics)
	require.Contains(t, res.Diagnostics[0].Message, "hold no membership in it for u₀", "the decline names the equation's atom:\n%s", res.Diagnostics[0].Message)
}

// byHypContaining is the index of the first hypothesis of the goal
// whose print contains sub — the kernel keeps hypotheses sorted, so a
// test names one by content, never by the order it was stripped in.
func byHypContaining(t *testing.T, e *Engine, sid, gid, sub string) *int {
	t.Helper()
	s, err := e.getSession(sid)
	require.NoError(t, err)
	s.mu.Lock()
	defer s.mu.Unlock()
	g := s.goalIndex[gid].node.Goal
	for i := 0; i < g.NumHyps(); i++ {
		if strings.Contains(ext.PrintTerm(g.Hyp(i)), sub) {
			return &i
		}
	}
	t.Fatalf("no hypothesis of %s contains %q", gid, sub)
	return nil
}

// TestByArith_ScaledBareReading: a coefficient on a BARE reading — a
// law read at a resident hypothesis with no witness tuple, the Go
// `Scaled(c, Law.Read(fact))` — scales the equation the reading states,
// exactly as a coefficient on a resident premise does: the reading is
// the derived premise, asserted and resident before the scaling phase.
// The law is the Weierstrass equation read at a curve's datum, y² = x³
// + ax + b, and the goal is q times it; the equation's sides are
// compound, so the closer cannot substitute it and needs the scaled row.
func TestByArith_ScaledBareReading(t *testing.T) {
	e := byArithEngine(t)
	ctx := context.Background()
	stmt := "∀L:field_ops(A). ∀k:set(A). ∀x y a b q:A. field_on(L) ⇒ weierstrass(L, k, x, y, a, b) ⇒ " +
		"a ∈ L.carrier ∧ b ∈ L.carrier ∧ q ∈ L.carrier ∧ x ∈ L.carrier ∧ y ∈ L.carrier ⇒ " +
		"L.mul(q, L.mul(y, y)) = L.mul(q, L.add(L.add(L.mul(x, L.mul(x, x)), L.mul(a, x)), b))"
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, err := e.getSession(info.ID)
	require.NoError(t, err)
	parsed := dsl.ParsePropTextInScope(stmt, &dsl.ParseScope{
		ConstResolver: envConstResolver(s.env), StrictResolution: true, FreshenMetaLetters: true,
		Syntax: constSyntax(),
	})
	require.Empty(t, parsed.Errors, "add-goal %q", stmt)
	s.mu.Lock()
	gid := s.AddGoal(parsed.Prop)
	s.mu.Unlock()
	for _, typ := range []string{"strip_quant", "strip_imp", "strip_imp", "strip_imp"} {
		res, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{GoalID: gid, Tactic: TacticReq{Type: typ}})
		require.NoError(t, err, typ)
		require.Len(t, res.Produced, 1, typ)
		gid = res.Produced[0].GoalID
	}
	field := byHypContaining(t, e, info.ID, gid, "field_on(")
	datum := byHypContaining(t, e, info.ID, gid, "weierstrass(")
	members := byHypContaining(t, e, info.ID, gid, "∈")
	reading := LemmaWithSpec{Key: "elliptic_curve.WeierstrassEquation", ReadAt: &ReadAtSpec{HypIndex: datum}}
	// Unscaled, the equation does not combine by integers with the goal.
	bare, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{GoalID: gid, Tactic: TacticReq{Type: "by", Arith: true,
		ByHyps: []ByHypSpec{{HypIndex: field}, {HypIndex: members}}, WithLemmas: []LemmaWithSpec{reading}}})
	require.True(t, err != nil || bare.Effect != "close", "closed without the coefficient on the reading")
	reading.Coefficient = "q₀"
	res, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{GoalID: gid, Tactic: TacticReq{Type: "by", Arith: true,
		ByHyps: []ByHypSpec{{HypIndex: field}, {HypIndex: members}}, WithLemmas: []LemmaWithSpec{reading}}})
	require.NoError(t, err)
	require.Equal(t, "close", res.Effect, "the scaled bare reading did not close: %+v", res.Diagnostics)
	// The recorded step renders as the Go spelling the macro accepts.
	out, err := e.EmitSection(&EmitSectionRequest{SessionID: info.ID, Section: 0, FuncName: "Build_SCALED_READING", Family: "scheme/elliptic_curve"})
	require.NoError(t, err)
	require.Contains(t, out.Go, "Scaled(q, ", "--- source: ---\n%s", out.Go)
	require.Contains(t, out.Go, "WeierstrassEquation.Read(", "--- source: ---\n%s", out.Go)
}
