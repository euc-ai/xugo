package reify

import (
	"math/big"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/stretchr/testify/require"
)

// The constants the tests speak in, with the types the corpus states
// them at. The reifier never imports the corpus; the tests restate the
// chapters' vocabulary and definitions here, so a drift between the two
// is a drift the tests cannot see, and the benchmark comparison below
// is a comparison of shapes, not of theorems. The four benchmarks'
// hand-written formulas (ax_formula, lexicographic_minimum_formula,
// polynomial_brouwer_formula, polynomial_system_formula and the
// definitions under them) live only here: the corpus retired them once
// the elementarity step proved its clients, and they stay the
// reference the reifier's shapes are compared with.
var corpusTypes = map[string]string{
	"fo_atom":         "A → fo_formula(A)",
	"fo_not":          "fo_formula(A) → fo_formula(A)",
	"fo_and":          "fo_formula(A) → fo_formula(A) → fo_formula(A)",
	"fo_or":           "fo_formula(A) → fo_formula(A) → fo_formula(A)",
	"fo_implies":      "fo_formula(A) → fo_formula(A) → fo_formula(A)",
	"fo_iff":          "fo_formula(A) → fo_formula(A) → fo_formula(A)",
	"fo_exists":       "num → fo_formula(A) → fo_formula(A)",
	"fo_forall":       "num → fo_formula(A) → fo_formula(A)",
	"fo_all_range":    "num → num → fo_formula(A) → fo_formula(A)",
	"fo_exists_range": "num → num → fo_formula(A) → fo_formula(A)",
	"fo_conjoin":      "fo_formula(A) → num → (num → fo_formula(A)) → fo_formula(A)",

	"ring_true_formula":                  "fo_formula((num → num) → int)",
	"ring_equality_formula":              "((num → num) → int) → ((num → num) → int) → fo_formula((num → num) → int)",
	"ordered_ring_true_formula":          "fo_formula((num → num) → int)",
	"polynomial_weak_inequality_formula": "((num → num) → int) → ((num → num) → int) → fo_formula((num → num) → int)",
	"ordered_ring_equality_formula":      "((num → num) → int) → ((num → num) → int) → fo_formula((num → num) → int)",

	"polynomial_algebra_var":   "ring_ops(A) → D → (D → num) → A",
	"polynomial_algebra_one":   "ring_ops(A) → (D → num) → A",
	"polynomial_algebra_const": "ring_ops(A) → A → (D → num) → A",
	"polynomial_algebra":       "ring_ops(A) → set(D) → set((D → num) → A)",
	"int_ring":                 "ring_ops(int)",
	"integer_polynomial_ring":  "ring_ops((num → num) → int)",
	"polynomial_code":          "num → num → num → num → (num → num) → int",
	"univariate_code":          "num → num → num → (num → num) → int",
	"coefficient_count":        "num → num → num",

	"ring_add":     "ring_ops(A) → A → A → A",
	"ring_zero":    "ring_ops(A) → A",
	"ring_neg":     "ring_ops(A) → A → A",
	"ring_mul":     "ring_ops(A) → A → A → A",
	"ring_one":     "ring_ops(A) → A",
	"ring_sub":     "ring_ops(A) → A → A → A",
	"ring_carrier": "ring_ops(A) → set(A)",

	"field_add":     "field_ops(A) → A → A → A",
	"field_zero":    "field_ops(A) → A",
	"field_neg":     "field_ops(A) → A → A",
	"field_mul":     "field_ops(A) → A → A → A",
	"field_one":     "field_ops(A) → A",
	"field_sub":     "field_ops(A) → A → A → A",
	"field_carrier": "field_ops(A) → set(A)",
	"field_ring":    "field_ops(A) → ring_ops(A)",

	"integer_map":      "ring_ops(A) → int → A",
	"polynomial_value": "ring_ops(A) → ((num → num) → A) → (num → A) → A",
	"polynomial_eval":  "(A → A → A) → A → (A → A → A) → A → (num → A) → A → A",
	"polynomial_map":   "ring_ops(A) → num → (num → (num → num) → A) → (num → A) → num → A",
	"polynomial_bound": "ring_ops(A) → num → num → ((num → num) → A) → bool",
	"ring_tuple":       "ring_ops(A) → num → (num → A) → bool",
	"ordered_le":       "(A → A → bool) → A → A → bool",
	"field_on":         "field_ops(A) → bool",
	"ordered_field_on": "field_ops(A) → (A → A → bool) → bool",
	"module_sum":       "(B → B → B) → B → set(D) → (D → B) → B",

	// The chapters whose statements the benchmarks reify.
	"ax_property":                    "field_ops(A) → num → num → bool",
	"polynomial_map_injective":       "ring_ops(A) → num → (num → (num → num) → A) → bool",
	"polynomial_map_surjective":      "ring_ops(A) → num → (num → (num → num) → A) → bool",
	"lexicographic_minimum_property": "field_ops(A) → (A → A → bool) → num → num → num → num → bool",
	"polynomial_constraint_set":      "field_ops(A) → (A → A → bool) → num → num → num → (num → (num → num) → A) → (num → (num → num) → A) → set(num → A)",
	"polynomial_box_bound":           "field_ops(A) → (A → A → bool) → num → set(num → A) → A → bool",
	"polynomial_lex_minimizer":       "field_ops(A) → (A → A → bool) → set(num → A) → ((num → num) → A) → ((num → num) → A) → (num → A) → bool",
	"polynomial_brouwer_property":    "field_ops(A) → (A → A → bool) → num → num → bool",
	"carrier_cube":                   "field_ops(A) → (A → A → bool) → num → set(num → A)",
	"polynomial_system_solution":     "ring_ops(A) → num → num → num → (num → (num → num) → A) → (num → (num → num) → A) → (num → A) → bool",

	// The hand-written formula families the benchmarks are compared with.
	"ax_map_equality_formula":            "num → num → num → num → fo_formula((num → num) → int)",
	"ax_point_equality_formula":          "num → num → num → fo_formula((num → num) → int)",
	"ax_map_hits_formula":                "num → num → num → num → fo_formula((num → num) → int)",
	"ax_formula_body":                    "num → num → num → num → fo_formula((num → num) → int)",
	"ax_formula":                         "num → num → fo_formula((num → num) → int)",
	"lexicographic_constraint_formula":   "num → num → num → num → num → fo_formula((num → num) → int)",
	"primary_minimum_formula":            "num → num → num → num → num → num → fo_formula((num → num) → int)",
	"lexicographic_minimum_formula_body": "num → num → num → num → num → num → num → num → fo_formula((num → num) → int)",
	"lexicographic_minimum_formula":      "num → num → num → num → fo_formula((num → num) → int)",
	"polynomial_box_formula":             "num → num → num → fo_formula((num → num) → int)",
	"polynomial_cube_formula":            "num → num → fo_formula((num → num) → int)",
	"polynomial_map_into_cube_formula":   "num → num → num → fo_formula((num → num) → int)",
	"polynomial_fixed_point_formula":     "num → num → num → fo_formula((num → num) → int)",
	"polynomial_brouwer_formula_body":    "num → num → num → fo_formula((num → num) → int)",
	"polynomial_brouwer_formula":         "num → num → fo_formula((num → num) → int)",
	"polynomial_system_formula":          "num → num → num → num → fo_formula((num → num) → int)",

	// Constants the negatives use: a function the formulas cannot speak
	// of, a predicate without a definition, and one whose definition
	// leaves the grammar.
	"exp_map":           "A → A",
	"mystery":           "field_ops(A) → num → bool",
	"exponential_fixed": "field_ops(A) → bool",
}

// The definitions the benchmarks unfold, as the chapters state them.
var corpusEquations = map[string]string{
	"ax_grothendieck.AxPropertyDef":                            "∀F:field_ops(A). ∀n d:num. ax_property(F, n, d) ⇔ ∀P:(num → (num → num) → A). (∀j:num. j < n ⇒ polynomial_bound(field_ring(F), n, d, P(j))) ∧ polynomial_map_injective(field_ring(F), n, P) ⇒ polynomial_map_surjective(field_ring(F), n, P)",
	"polynomial_encoding.PolynomialMapInjectiveDef":            "∀R:ring_ops(A). ∀n:num. ∀P:(num → (num → num) → A). polynomial_map_injective(R, n, P) ⇔ ∀x y:(num → A). ring_tuple(R, n, x) ∧ ring_tuple(R, n, y) ∧ polynomial_map(R, n, P, x) = polynomial_map(R, n, P, y) ⇒ x = y",
	"polynomial_encoding.PolynomialMapSurjectiveDef":           "∀R:ring_ops(A). ∀n:num. ∀P:(num → (num → num) → A). polynomial_map_surjective(R, n, P) ⇔ ∀y:(num → A). ring_tuple(R, n, y) ⇒ ∃x:(num → A). ring_tuple(R, n, x) ∧ polynomial_map(R, n, P, x) = y",
	"semialgebraic_properties.LexPropertyDef":                  "∀F:field_ops(A). ∀lt:(A → A → bool). ∀n s t d:num. lexicographic_minimum_property(F, lt, n, s, t, d) ⇔ ∀f q:((num → num) → A). ∀g h:(num → (num → num) → A). ∀M:A. polynomial_bound(field_ring(F), n, d, f) ∧ polynomial_bound(field_ring(F), n, d, q) ∧ (∀j:num. j < s ⇒ polynomial_bound(field_ring(F), n, d, g(j))) ∧ (∀j:num. j < t ⇒ polynomial_bound(field_ring(F), n, d, h(j))) ∧ polynomial_constraint_set(F, lt, n, s, t, g, h) ≠ ∅ ∧ polynomial_box_bound(F, lt, n, polynomial_constraint_set(F, lt, n, s, t, g, h), M) ⇒ ∃x:(num → A). polynomial_lex_minimizer(F, lt, polynomial_constraint_set(F, lt, n, s, t, g, h), f, q, x)",
	"semialgebraic_properties.ConstraintSetDef":                "∀F:field_ops(A). ∀lt:(A → A → bool). ∀n s t:num. ∀g h:(num → (num → num) → A). polynomial_constraint_set(F, lt, n, s, t, g, h) = {x:(num → A) | ring_tuple(field_ring(F), n, x) ∧ (∀j:num. j < s ⇒ ordered_le(lt, F.zero, polynomial_value(field_ring(F), g(j), x))) ∧ (∀j:num. j < t ⇒ polynomial_value(field_ring(F), h(j), x) = F.zero)}",
	"semialgebraic_properties.BoundedSetDef":                   "∀F:field_ops(A). ∀lt:(A → A → bool). ∀n:num. ∀S:set(num → A). ∀M:A. polynomial_box_bound(F, lt, n, S, M) ⇔ M ∈ F.carrier ∧ lt(F.zero, M) ∧ (∀x:(num → A). x ∈ S ⇒ ∀j:num. j < n ⇒ ordered_le(lt, F.neg(M), x(j)) ∧ ordered_le(lt, x(j), M))",
	"semialgebraic_properties.LexMinimizerDef":                 "∀F:field_ops(A). ∀lt:(A → A → bool). ∀S:set(num → A). ∀f q:((num → num) → A). ∀x:(num → A). polynomial_lex_minimizer(F, lt, S, f, q, x) ⇔ x ∈ S ∧ (∀y:(num → A). y ∈ S ⇒ ordered_le(lt, polynomial_value(field_ring(F), f, x), polynomial_value(field_ring(F), f, y))) ∧ (∀y:(num → A). y ∈ S ∧ (∀z:(num → A). z ∈ S ⇒ ordered_le(lt, polynomial_value(field_ring(F), f, y), polynomial_value(field_ring(F), f, z))) ⇒ ordered_le(lt, polynomial_value(field_ring(F), q, x), polynomial_value(field_ring(F), q, y)))",
	"semialgebraic_properties.BrouwerPropertyDef":              "∀F:field_ops(A). ∀lt:(A → A → bool). ∀n d:num. polynomial_brouwer_property(F, lt, n, d) ⇔ ∀P:(num → (num → num) → A). (∀j:num. j < n ⇒ polynomial_bound(field_ring(F), n, d, P(j))) ∧ (∀x:(num → A). x ∈ carrier_cube(F, lt, n) ⇒ polynomial_map(field_ring(F), n, P, x) ∈ carrier_cube(F, lt, n)) ⇒ ∃x:(num → A). x ∈ carrier_cube(F, lt, n) ∧ polynomial_map(field_ring(F), n, P, x) = x",
	"ordered_ring_formula_combinators.CarrierCubeDef":          "∀F:field_ops(A). ∀lt:(A → A → bool). ∀n:num. carrier_cube(F, lt, n) = {x:(num → A) | ring_tuple(field_ring(F), n, x) ∧ (∀j:num. j < n ⇒ ordered_le(lt, F.zero, x(j)) ∧ ordered_le(lt, x(j), F.one))}",
	"polynomial_system_descent.PolynomialSystemDef":            "∀R:ring_ops(A). ∀n r s:num. ∀P Q:(num → (num → num) → A). ∀x:(num → A). polynomial_system_solution(R, n, r, s, P, Q, x) ⇔ ring_tuple(R, n, x) ∧ (∀j:num. j < r ⇒ polynomial_value(R, P(j), x) = R.zero) ∧ (∀j:num. j < s ⇒ polynomial_value(R, Q(j), x) ≠ R.zero)",
	"ax_grothendieck.MapEqualityFormulaDef":                    "∀n d x y:num. ax_map_equality_formula(n, d, x, y) = fo_conjoin(ring_true_formula, n, λj:num. ring_equality_formula(polynomial_code(n, d, j * coefficient_count(n, d), x), polynomial_code(n, d, j * coefficient_count(n, d), y)))",
	"ax_grothendieck.PointEqualityFormulaDef":                  "∀n x y:num. ax_point_equality_formula(n, x, y) = fo_conjoin(ring_true_formula, n, λj:num. ring_equality_formula(polynomial_algebra_var(int_ring, x + j), polynomial_algebra_var(int_ring, y + j)))",
	"ax_grothendieck.MapHitsFormulaDef":                        "∀n d x y:num. ax_map_hits_formula(n, d, x, y) = fo_conjoin(ring_true_formula, n, λj:num. ring_equality_formula(polynomial_code(n, d, j * coefficient_count(n, d), x), polynomial_algebra_var(int_ring, y + j)))",
	"ax_grothendieck.AxBodyDef":                                "∀n d x y:num. ax_formula_body(n, d, x, y) = fo_implies(fo_all_range(x, n, fo_all_range(y, n, fo_implies(ax_map_equality_formula(n, d, x, y), ax_point_equality_formula(n, x, y)))), fo_all_range(y, n, fo_exists_range(x, n, ax_map_hits_formula(n, d, x, y))))",
	"ax_grothendieck.AxFormulaDef":                             "∀n d:num. ax_formula(n, d) = fo_all_range(0, n * coefficient_count(n, d), ax_formula_body(n, d, n * coefficient_count(n, d), n * coefficient_count(n, d) + n))",
	"polynomial_optimization_formula.ConstraintFormulaDef":     "∀n s t d x:num. lexicographic_constraint_formula(n, s, t, d, x) = fo_and(fo_conjoin(ordered_ring_true_formula, s, λj:num. polynomial_weak_inequality_formula(λm:(num → num). int_of_num(0), polynomial_code(n, d, (2 + j) * coefficient_count(n, d), x))), fo_conjoin(ordered_ring_true_formula, t, λj:num. ordered_ring_equality_formula(polynomial_code(n, d, (2 + s + j) * coefficient_count(n, d), x), λm:(num → num). int_of_num(0))))",
	"polynomial_optimization_formula.PrimaryMinimumFormulaDef": "∀n s t d x y:num. primary_minimum_formula(n, s, t, d, x, y) = fo_all_range(y, n, fo_implies(lexicographic_constraint_formula(n, s, t, d, y), polynomial_weak_inequality_formula(polynomial_code(n, d, 0, x), polynomial_code(n, d, 0, y))))",
	"polynomial_optimization_formula.LexBodyDef":               "∀n s t d b x y z:num. lexicographic_minimum_formula_body(n, s, t, d, b, x, y, z) = fo_implies(fo_and(fo_atom(λm:(num → num). -polynomial_algebra_var(int_ring, b, m)), fo_and(fo_exists_range(x, n, lexicographic_constraint_formula(n, s, t, d, x)), fo_all_range(x, n, fo_implies(lexicographic_constraint_formula(n, s, t, d, x), polynomial_box_formula(n, b, x))))), fo_exists_range(x, n, fo_and(lexicographic_constraint_formula(n, s, t, d, x), fo_and(primary_minimum_formula(n, s, t, d, x, y), fo_all_range(y, n, fo_implies(fo_and(lexicographic_constraint_formula(n, s, t, d, y), primary_minimum_formula(n, s, t, d, y, z)), polynomial_weak_inequality_formula(polynomial_code(n, d, coefficient_count(n, d), x), polynomial_code(n, d, coefficient_count(n, d), y))))))))",
	"polynomial_optimization_formula.LexFormulaDef":            "∀n s t d:num. lexicographic_minimum_formula(n, s, t, d) = fo_all_range(0, (2 + s + t) * coefficient_count(n, d) + 1, lexicographic_minimum_formula_body(n, s, t, d, (2 + s + t) * coefficient_count(n, d), (2 + s + t) * coefficient_count(n, d) + 1, (2 + s + t) * coefficient_count(n, d) + 1 + n, (2 + s + t) * coefficient_count(n, d) + 1 + 2 * n))",
	"ordered_ring_formula_combinators.BoxFormulaDef":           "∀n b x:num. polynomial_box_formula(n, b, x) = fo_conjoin(ordered_ring_true_formula, n, λj:num. fo_and(polynomial_weak_inequality_formula(λm:(num → num). -polynomial_algebra_var(int_ring, b, m), polynomial_algebra_var(int_ring, x + j)), polynomial_weak_inequality_formula(polynomial_algebra_var(int_ring, x + j), polynomial_algebra_var(int_ring, b))))",
	"ordered_ring_formula_combinators.CubeFormulaDef":          "∀n x:num. polynomial_cube_formula(n, x) = fo_conjoin(ordered_ring_true_formula, n, λj:num. fo_and(polynomial_weak_inequality_formula(λm:(num → num). int_of_num(0), polynomial_algebra_var(int_ring, x + j)), polynomial_weak_inequality_formula(polynomial_algebra_var(int_ring, x + j), polynomial_algebra_one(int_ring))))",
	"polynomial_brouwer_formula.MapCubeFormulaDef":             "∀n d x:num. polynomial_map_into_cube_formula(n, d, x) = fo_conjoin(ordered_ring_true_formula, n, λj:num. fo_and(polynomial_weak_inequality_formula(λm:(num → num). int_of_num(0), polynomial_code(n, d, j * coefficient_count(n, d), x)), polynomial_weak_inequality_formula(polynomial_code(n, d, j * coefficient_count(n, d), x), polynomial_algebra_one(int_ring))))",
	"polynomial_brouwer_formula.FixedPointFormulaDef":          "∀n d x:num. polynomial_fixed_point_formula(n, d, x) = fo_conjoin(ordered_ring_true_formula, n, λj:num. ordered_ring_equality_formula(polynomial_code(n, d, j * coefficient_count(n, d), x), polynomial_algebra_var(int_ring, x + j)))",
	"polynomial_brouwer_formula.BrouwerBodyDef":                "∀n d x:num. polynomial_brouwer_formula_body(n, d, x) = fo_implies(fo_all_range(x, n, fo_implies(polynomial_cube_formula(n, x), polynomial_map_into_cube_formula(n, d, x))), fo_exists_range(x, n, fo_and(polynomial_cube_formula(n, x), polynomial_fixed_point_formula(n, d, x))))",
	"polynomial_brouwer_formula.BrouwerFormulaDef":             "∀n d:num. polynomial_brouwer_formula(n, d) = fo_all_range(0, n * coefficient_count(n, d), polynomial_brouwer_formula_body(n, d, n * coefficient_count(n, d)))",
	"polynomial_system_descent.SystemFormulaDef":               "∀n r s d:num. polynomial_system_formula(n, r, s, d) = fo_exists_range((r + s) * coefficient_count(n, d), n, fo_and(fo_conjoin(ring_true_formula, r, λj:num. fo_atom(polynomial_code(n, d, j * coefficient_count(n, d), (r + s) * coefficient_count(n, d)))), fo_conjoin(ring_true_formula, s, λj:num. fo_not(fo_atom(polynomial_code(n, d, (r + j) * coefficient_count(n, d), (r + s) * coefficient_count(n, d)))))))",
	"test.ExponentialFixedDef":                                 "∀F:field_ops(A). exponential_fixed(F) ⇔ ∀a:A. a ∈ F.carrier ⇒ exp_map(a) = a",
}

// _TestSyntax is the syntax table the fixture parses under: the
// constants' metas and the two records' fields, and no notation.
type _TestSyntax struct {
	metas   map[string]core.ConstTermMeta
	structs map[string]*dsl.StructSyntax
}

func (s _TestSyntax) ConstSyntax(string) *dsl.ConstSyntax        { return nil }
func (s _TestSyntax) ConstMeta(name string) core.ConstTermMeta   { return s.metas[name] }
func (s _TestSyntax) OutfixConsts(string, string) []string       { return nil }
func (s _TestSyntax) OperatorConsts(string, int) []string        { return nil }
func (s _TestSyntax) BigOpConst(string, core.HolType) string     { return "" }
func (s _TestSyntax) OverloadConsts(string) []string             { return nil }
func (s _TestSyntax) CoercionConst(core.HolType) string          { return "" }
func (s _TestSyntax) TupleNames() []string                       { return nil }
func (s _TestSyntax) StructSyntax(name string) *dsl.StructSyntax { return s.structs[name] }

// _Fixture is the test's corpus: the parse scope, the vocabulary read
// from it, and the unfolder over the chapters' definitions.
type _Fixture struct {
	t        *testing.T
	metas    map[string]core.ConstTermMeta
	syntax   _TestSyntax
	vocab    *Vocabulary
	unfolder Unfolder
}

func newFixture(t *testing.T) *_Fixture {
	t.Helper()
	metas := map[string]core.ConstTermMeta{
		"+":                  dsl.NatPlusMeta,
		"*":                  dsl.NatStarMeta,
		"suc":                dsl.SUCMeta,
		"<":                  dsl.NatLtMeta,
		"int_of_num":         dsl.IntOfNumMeta,
		"int_sub":            dsl.IntSubMeta,
		"set_member":         dsl.InMeta,
		"set_comprehension":  dsl.SetComprehensionMeta,
		"comprehension_spec": dsl.ComprehensionSpecMeta,
		"empty_set":          dsl.EmptyMeta,
	}
	for name, text := range corpusTypes {
		ty, err := dsl.ParseTypeText(text)
		require.NoError(t, err, name)
		metas[name] = core.MakeConstMeta(name, ty)
	}
	record := func(prefix string, fields ...string) *dsl.StructSyntax {
		s := &dsl.StructSyntax{}
		for _, f := range fields {
			s.Fields = append(s.Fields, dsl.StructField{Name: f, Const: prefix + "_" + f})
		}
		return s
	}
	f := &_Fixture{t: t, metas: metas}
	f.syntax = _TestSyntax{metas: metas, structs: map[string]*dsl.StructSyntax{
		"field_ops": record("field", "add", "zero", "neg", "mul", "one", "sub", "carrier"),
		"ring_ops":  record("ring", "add", "zero", "neg", "mul", "one", "sub", "carrier"),
	}}
	vocab, err := NewVocabulary(f.lookup)
	require.NoError(t, err)
	f.vocab = vocab
	var equations []Equation
	for _, lemma := range sortedKeys(corpusEquations) {
		equations = append(equations, Equation{Lemma: lemma, Statement: f.prop(corpusEquations[lemma], nil)})
	}
	f.unfolder = EquationUnfolder(equations...)
	return f
}

func (f *_Fixture) lookup(name core.TermName) core.ConstTermMeta { return f.metas[string(name)] }

func (f *_Fixture) scope(vars map[string]string) *dsl.ParseScope {
	scope := &dsl.ParseScope{ConstMetas: f.metas, Vars: map[string]core.HolType{}, Syntax: f.syntax, StrictResolution: true, FreshenMetaLetters: true}
	for name, text := range vars {
		ty, err := dsl.ParseTypeText(text)
		require.NoError(f.t, err, name)
		scope.Vars[name] = ty
	}
	return scope
}

// prop parses a proposition with the given free variables declared.
func (f *_Fixture) prop(text string, vars map[string]string) core.Term {
	f.t.Helper()
	res := dsl.ParsePropTextInScope(text, f.scope(vars))
	require.Empty(f.t, res.Errors, "parse %q: %v", text, res.Errors)
	return res.Prop.Conclusion()
}

// term parses a term of any type with the given free variables declared.
func (f *_Fixture) term(text string, vars map[string]string) core.Term {
	f.t.Helper()
	ctx := map[string]core.HolType{}
	for name, ty := range vars {
		parsed, err := dsl.ParseTypeText(ty)
		require.NoError(f.t, err, name)
		ctx[name] = parsed
	}
	res := dsl.ParseTermTextInScope(text, ctx, f.scope(vars), nil)
	require.Empty(f.t, res.Errors, "parse %q: %v", text, res.Errors)
	return res.Term
}

// field is the record F:field_ops(A) and the order lt as variables.
func (f *_Fixture) field(name, carrier string) core.Term {
	ty, err := dsl.ParseTypeText("field_ops(" + carrier + ")")
	require.NoError(f.t, err)
	return core.Var(name, ty)
}

func (f *_Fixture) order(name, carrier string) core.Term {
	ty, err := dsl.ParseTypeText(carrier + " → " + carrier + " → bool")
	require.NoError(f.t, err)
	return core.Var(name, ty)
}

// num is a numeric variable, numeral a numeral.
func num(name string) core.Term { return core.Var(name, ext.NumType) }

func numeral(k int64) core.Term { return ext.MakeNumeral(big.NewInt(k)) }

func sortedKeys(m map[string]string) []string {
	keys := make([]string, 0, len(m))
	for k := range m {
		keys = append(keys, k)
	}
	sortStrings(keys)
	return keys
}
