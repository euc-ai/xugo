package engine

import (
	"context"
	"github.com/euc-ai/xugo/library/registry"
	"testing"
	"time"

	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/library/serve"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/stretchr/testify/require"
)

// byArithEngine is the engine the product-leaf pins run on: the registry's
// constants and the corpus, with all three arithmetic bundles installed.
func byArithEngine(t *testing.T) *Engine {
	t.Helper()
	env := testEnv()
	env.ProofService = &proof.ProofService{
		LoadConstMeta:        registry.GetConstMetaManager().LoadConstMeta,
		LoadOrStoreConstMeta: registry.GetConstMetaManager().LoadOrStoreConstMeta,
		Syntax:               registry.GetConstMetaManager(),
	}
	env.LibraryThms = serve.InductionPrinciples()
	serve.RegisterAll(env)
	serve.InstallProofPolicy()
	installTestNatBundle()
	installTestRealBundle()
	serve.InstallIntBundle()
	serve.InstallStructureRingBundle()
	return newEngine(env)
}

type byArithRow struct {
	name, stmt string
	strips     []string
	hyps       []int
}

// runByArithRows adds each row's statement, strips it, and requires the
// session `by {arith:true}` over the listed hyps to close the residual.
func runByArithRows(t *testing.T, e *Engine, rows []byArithRow) {
	t.Helper()
	runByArithRowsIn(t, e, nil, rows)
}

// runByArithRowsIn is runByArithRows with the statements read under the
// constant syntax given: a record's fields (`R.add`, `R.carrier`) are
// read through it, and nil reads no field.
func runByArithRowsIn(t *testing.T, e *Engine, syntax dsl.SyntaxTable, rows []byArithRow) {
	t.Helper()
	ctx := context.Background()
	idx := func(i int) *int { return &i }
	for _, r := range rows {
		t.Run(r.name, func(t *testing.T) {
			info, err := e.CreateSession(ctx)
			require.NoError(t, err)
			s, err := e.getSession(info.ID)
			require.NoError(t, err)
			parsed := dsl.ParsePropTextInScope(r.stmt, &dsl.ParseScope{
				ConstResolver: envConstResolver(s.env), StrictResolution: true, FreshenMetaLetters: true,
				Syntax: syntax,
			})
			require.Empty(t, parsed.Errors, "add-goal %q", r.stmt)
			s.mu.Lock()
			gid := s.AddGoal(parsed.Prop)
			s.mu.Unlock()
			for _, typ := range r.strips {
				res, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{GoalID: gid, Tactic: TacticReq{Type: typ}})
				require.NoError(t, err, "strip %s", typ)
				require.Len(t, res.Produced, 1, "strip %s", typ)
				gid = res.Produced[0].GoalID
			}
			var hyps []ByHypSpec
			for _, i := range r.hyps {
				hyps = append(hyps, ByHypSpec{HypIndex: idx(i)})
			}
			t0 := time.Now()
			res, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{GoalID: gid,
				Tactic: TacticReq{Type: "by", Arith: true, ByHyps: hyps}})
			require.NoError(t, err)
			require.Equal(t, "close", res.Effect, "%s did not close", r.name)
			t.Logf("%s: closed in %v", r.name, time.Since(t0))
		})
	}
}

// TestByArith_IntLeaves: the ℤ twins of the product leaves below — a
// product of variables is a monomial unknown to the int linear layer too
// (omega Domain.polyMul over intRing).
func TestByArith_IntLeaves(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus and the production bundles")
	}
	runByArithRows(t, byArithEngine(t), []byArithRow{
		{"halving over a product",
			"∀a b d:int. &2 * ((a * b) * d) ≤ &2 * (((a * a) * b) * b) ⇒ (a * b) * d ≤ ((a * a) * b) * b",
			[]string{"strip_quant", "strip_imp"}, []int{0}},
		{"scaling a product hypothesis",
			"∀a b:int. &0 < a * b ⇒ &0 < &2 * (a * b)",
			[]string{"strip_quant", "strip_imp"}, []int{0}},
		{"a square hypothesis spelled x * x",
			"∀x y:int. &0 < y ∧ &0 ≤ x ∧ x * x ≤ y ∧ &2 * x ≤ x * x + &1 ⇒ x ≤ y + &1",
			[]string{"strip_quant", "strip_imp"}, []int{0}},
		// The bare side of a scaling read as the factor times &1.
		{"a product against its bare factor",
			"∀x:int. &0 < x ∧ x ≤ &1 ⇒ x * x ≤ x",
			[]string{"strip_quant", "strip_imp"}, []int{0}},
	})
}

// TestByArith_RealLeaves pins the session `by {arith:true}` on the ℝ
// ordering leaves the vector and real_sqrt chapters met,
// each verbatim: a product of variables is a monomial unknown to the ℝ
// linear layer (omega Domain.polyMul over realRing), a scaled product's sign
// descends to its factors' signs (realProveFactorSign), a numeral guard
// inside a Horn premise folds in the hyp pre-simp (groundComparisonDecide),
// and the arith closer runs its Arith to a fixpoint so a firing spent on a
// hypothesis rewrite is followed by the decision. Real corpus, real bundle.
func TestByArith_RealLeaves(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus and the production bundles")
	}
	e := byArithEngine(t)
	runByArithRows(t, e, []byArithRow{
		// euclidean.CauchySchwarz: halving over a product, and a nonneg
		// difference read as an ordering with identical atoms.
		{"halving over a product",
			"∀a b d:real. &2 * ((a * b) * d) ≤ &2 * (((a * a) * b) * b) ⇒ (a * b) * d ≤ ((a * a) * b) * b",
			[]string{"strip_quant", "strip_imp"}, []int{0}},
		{"a nonneg difference read as an ordering",
			"∀a b d:real. &0 ≤ (b * ((b * (a * a)) - (a * d))) - (a * ((b * d) - (a * (b * b)))) ⇒ &2 * ((a * b) * d) ≤ &2 * ((a * b) * (a * b))",
			[]string{"strip_quant", "strip_imp"}, []int{0}},
		{"scaling a product hypothesis",
			"∀a b:real. &0 < a * b ⇒ &0 < &2 * (a * b)",
			[]string{"strip_quant", "strip_imp"}, []int{0}},
		{"the sign of a scaled product from its factors",
			"∀a b:real. &0 < a ∧ &0 < b ⇒ &0 < &2 * (a * b)",
			[]string{"strip_quant", "strip_imp"}, []int{0}},
		// The bare side of a monotone scaling read as the shared factor
		// times &1 — the function-limits product's `η·η ≤ η` — in all four
		// placements of the factor and the strict form.
		{"a square against its bare factor",
			"∀x:real. &0 < x ∧ x ≤ &1 ⇒ x * x ≤ x",
			[]string{"strip_quant", "strip_imp"}, []int{0}},
		{"a bare factor against a product, the factor on the right",
			"∀x y:real. &0 ≤ x ∧ &1 ≤ y ⇒ x ≤ y * x",
			[]string{"strip_quant", "strip_imp"}, []int{0}},
		{"a strict scaling against the bare factor",
			"∀a x:real. &0 < x ∧ a < &1 ⇒ a * x < x",
			[]string{"strip_quant", "strip_imp"}, []int{0}},
		{"the bare factor below its own scaling, strict",
			"∀x y:real. &0 < x ∧ &1 < y ⇒ x < x * y",
			[]string{"strip_quant", "strip_imp"}, []int{0}},
		// real_sqrt.SquareRootExists: the square spelled x * x, and as the
		// pow atom.
		{"a square hypothesis spelled x * x",
			"∀x y:real. &0 < y ∧ &0 ≤ x ∧ x * x ≤ y ∧ &2 * x ≤ x * x + &1 ⇒ x ≤ y + &1",
			[]string{"strip_quant", "strip_imp"}, []int{0}},
		{"the same with the pow atom",
			"∀x y:real. &0 < y ∧ &0 ≤ x ∧ real_pow(x, 2) ≤ y ∧ &2 * x ≤ real_pow(x, 2) + &1 ⇒ x ≤ y + &1",
			[]string{"strip_quant", "strip_imp"}, []int{0}},
		// real_sqrt.ApproachFromAbove: linear over a cross term.
		{"linear over a cross term",
			"∀w x q y p s:real. &2 * (w * x) ≤ q - y ∧ p = (q - &2 * (w * x)) + s ∧ &0 < s ⇒ y < p",
			[]string{"strip_quant", "strip_imp"}, []int{0}},
		// real_pow.PowMonoExp at (x, 1, 2) with its nat guard, and the
		// PowMonoBase instance with the `2 ≠ 0` guard, as the witnessed
		// premises land: a Horn hypothesis whose antecedent carries the
		// numeral guard.
		{"a numeral guard inside a Horn premise",
			"∀x y:real. &0 < y ∧ &0 ≤ x ∧ real_pow(x, 2) ≤ y ∧ ((&1 ≤ x ∧ 1 ≤ 2) ⇒ real_pow(x, 1) ≤ real_pow(x, 2)) ∧ real_pow(x, 1) = x ⇒ x ≤ y + &1",
			[]string{"strip_quant", "strip_imp"}, []int{0}},
		{"a disequation guard inside a Horn premise",
			"∀x z y:real. &0 ≤ x ∧ real_pow(x, 2) ≤ y ∧ &0 < z ∧ y < real_pow(z, 2) ∧ ((2 ≠ 0 ∧ &0 ≤ z ∧ z < x) ⇒ real_pow(z, 2) < real_pow(x, 2)) ⇒ x ≤ z",
			[]string{"strip_quant", "strip_imp"}, []int{0}},
		// real_derivative's rules: a quotient by a symbolic divisor is read
		// as the monomial u·inv(v) (omega quotient_basis.go), so the
		// difference quotients of a sum and of a product combine with no
		// `real_div` unfolded by hand.
		{"the difference quotient of a sum",
			"∀f g p q x c w:real. &0 < w ⇒ (f + g - (p + q)) / (x - c) = (f - p) / (x - c) + (g - q) / (x - c)",
			[]string{"strip_quant", "strip_imp"}, []int{0}},
		{"the difference quotient of a product",
			"∀f g p q x c w:real. &0 < w ⇒ (f * g - p * q) / (x - c) = f * ((g - q) / (x - c)) + q * ((f - p) / (x - c))",
			[]string{"strip_quant", "strip_imp"}, []int{0}},
		{"linear in quotients a hypothesis names",
			"∀a b v q r:real. q = a / v ∧ r = b / v ⇒ (a + b) / v = q + r",
			[]string{"strip_quant", "strip_imp"}, []int{0}},
		// The field handler goes on meeting the `/` the author wrote.
		{"a positive divisor cleared from the goal",
			"∀a b v:real. &0 < v ∧ a ≤ b * v ⇒ a / v ≤ b",
			[]string{"strip_quant", "strip_imp"}, []int{0}},
		// real_function_limits.LimitAtMul's tolerance: the sign is stated
		// about the quotient, and prices the monomial it divides
		// (omega realMonomialSignByPieces).
		{"a quotient's sign as a piece of a monomial",
			"∀e l m:real. e = (e + l + m + &1) * (e / (e + l + m + &1)) ∧ &0 < e ∧ &0 < e / (e + l + m + &1) ⇒ e / (e + l + m + &1) * (l + m + &1) < e",
			[]string{"strip_quant", "strip_imp"}, []int{0}},
		{"an inverse priced from its argument, in a row",
			"∀a v c:real. &0 < a ∧ &0 < v ∧ a / v ≤ c ⇒ &0 < c",
			[]string{"strip_quant", "strip_imp"}, []int{0}},
		// A resident `v ≠ &0` reaches the field layer in the square form
		// the arith step rewrites it into, and a difference is nonzero on
		// the evidence an ε-δ context holds (omega real_nonzero.go).
		{"the adjacent pair under a disequality",
			"∀v:real. v ≠ &0 ⇒ v * real_inv(v) = &1",
			[]string{"strip_quant", "strip_imp"}, []int{0}},
		{"a divisor cleared under a disequality",
			"∀a b v:real. v ≠ &0 ∧ a = b * v ⇒ a / v = b",
			[]string{"strip_quant", "strip_imp"}, []int{0}},
		{"a difference is nonzero where its terms differ",
			"∀x c:real. x ≠ c ⇒ x - c ≠ &0",
			[]string{"strip_quant", "strip_imp"}, []int{0}},
		{"a difference is nonzero at a positive distance",
			"∀x c:real. &0 < real_abs(x - c) ⇒ x - c ≠ &0",
			[]string{"strip_quant", "strip_imp"}, []int{0}},
		// A factor and its inverse cancel wherever they stand in a monomial
		// (omega real_unit_facts.go).
		{"a quotient times its divisor",
			"∀a v:real. v ≠ &0 ⇒ a / v * v = a",
			[]string{"strip_quant", "strip_imp"}, []int{0}},
		{"a difference quotient times its offset",
			"∀f p x c:real. x ≠ c ⇒ (f - p) / (x - c) * (x - c) = f - p",
			[]string{"strip_quant", "strip_imp"}, []int{0}},
		{"two unit pairs after multiplying out",
			"∀u l:real. u ≠ &0 ∧ l ≠ &0 ⇒ (real_inv(u) - real_inv(l)) * (u * l) = l - u",
			[]string{"strip_quant", "strip_imp"}, []int{0}},
		{"a divisor that is a positive difference",
			"∀f p a b:real. a < b ⇒ (f - p) / (b - a) * (b - a) = f - p",
			[]string{"strip_quant", "strip_imp"}, []int{0}},
		{"a factorization divided by its offset",
			"∀φ x c:real. x ≠ c ⇒ φ = (φ * (x - c)) / (x - c)",
			[]string{"strip_quant", "strip_imp"}, []int{0}},
		{"a sum over a nonzero divisor, from its factorization",
			"∀f p φ v:real. v ≠ &0 ∧ f + p = φ * v ⇒ (f + p) / v = φ",
			[]string{"strip_quant", "strip_imp"}, []int{0}},
		// A refutation spine: by_contra, then the arith closer on both hyps.
		{"by_contra then by arith",
			"∀a b d:real. &2 * ((a * b) * d) ≤ &2 * (((a * a) * b) * b) ⇒ (a * b) * d ≤ ((a * a) * b) * b",
			[]string{"strip_quant", "strip_imp", "by_contra"}, []int{0, 1}},
	})
}
