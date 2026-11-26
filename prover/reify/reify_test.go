package reify

import (
	"slices"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/stretchr/testify/require"
)

// benchmark reifies a proposition and compares its formula's shape with
// the hand-written family's: block structure, quantifier prefix and
// atom count, the names left aside.
func (f *_Fixture) benchmark(in Input, handWritten string, vars map[string]string) *Result {
	f.t.Helper()
	result, err := Reify(in)
	require.NoError(f.t, err)
	expected := skeleton(expandAll(f.term(handWritten, vars), f.unfolder))
	got := skeleton(result.Formula)
	f.t.Logf("shape %s", got)
	require.Equal(f.t, expected, got, "generated:\n%s", ext.FormatTermForParser(result.Formula))
	require.Equal(f.t, atomCount(expected), atomCount(got))
	again, err := Reify(in)
	require.NoError(f.t, err)
	require.True(f.t, result.Formula.AlphaEquals(again.Formula), "two reifications of one input differ")
	require.Equal(f.t, len(result.Names.Blocks), len(again.Names.Blocks))
	return result
}

func requireBlock(t *testing.T, block *Block, owner string, kind BlockKind, start, length core.Term) {
	t.Helper()
	require.Equal(t, owner, block.Owner)
	require.Equal(t, kind, block.Kind)
	require.True(t, block.Start.AlphaEquals(start), "start of %s: %s", owner, ext.FormatTermForParser(block.Start))
	require.True(t, block.Length.AlphaEquals(length), "length of %s: %s", owner, ext.FormatTermForParser(block.Length))
}

// The Ax–Grothendieck property, unfolded: one coefficient block for the
// family, then the tuple blocks of injectivity and surjectivity, both
// tuple equalities coordinatewise.
func TestReify_AxPropertyUnfolded(t *testing.T) {
	f := newFixture(t)
	F := f.field("F", "A")
	vars := map[string]string{"F": "field_ops(A)", "n": "num", "d": "num"}
	Φ := f.prop("∀P:(num → (num → num) → A). (∀j:num. j < n ⇒ polynomial_bound(field_ring(F), n, d, P(j))) ∧ polynomial_map_injective(field_ring(F), n, P) ⇒ polynomial_map_surjective(field_ring(F), n, P)", vars)
	result := f.benchmark(Input{Structure: Structure{Field: F}, Proposition: Φ, Unfold: f.unfolder, Vocabulary: f.vocab}, "ax_formula(n, d)", vars)

	count := f.term("n * coefficient_count(n, d)", vars)
	require.Len(t, result.Names.Blocks, 5)
	requireBlock(t, result.Names.Blocks[0], "P", FamilyBlock, numeral(0), count)
	requireBlock(t, result.Names.Blocks[1], "x", TupleBlock, count, num("n"))
	requireBlock(t, result.Names.Blocks[2], "y", TupleBlock, f.term("n * coefficient_count(n, d) + n", vars), num("n"))
	requireBlock(t, result.Names.Blocks[3], "y", TupleBlock, count, num("n"))
	requireBlock(t, result.Names.Blocks[4], "x", TupleBlock, f.term("n * coefficient_count(n, d) + n", vars), num("n"))
	require.True(t, isNumeral(result.Names.Frontier, 0))

	require.Len(t, result.Obligations, 1)
	require.Equal(t, StructureObligation, result.Obligations[0].Kind)
	require.True(t, result.Obligations[0].Statement.AlphaEquals(f.prop("field_on(F)", vars)))

	require.Equal(t, ForallFamily, result.Plan.Kind)
	require.Equal(t, "P", result.Plan.Block.Owner)
	require.Equal(t, "polynomial_encoding.AllRangeFamilyBridge", result.Plan.Citations[0].Lemma)
	require.Equal(t, Implication, result.Plan.Children[0].Kind)
	injective := result.Plan.Children[0].Children[0]
	require.Equal(t, Unfolding, injective.Kind)
	require.Equal(t, "polynomial_encoding.PolynomialMapInjectiveDef", injective.Citations[0].Lemma)
}

// The lexicographic minimum property, read through its definition and
// those of the constraint set, the box bound and the minimizer: the
// hand-written family's one leading block is the reifier's two
// polynomial blocks, two family blocks and one scalar.
func TestReify_LexicographicMinimumProperty(t *testing.T) {
	f := newFixture(t)
	F, lt := f.field("F", "A"), f.order("lt", "A")
	vars := map[string]string{"F": "field_ops(A)", "lt": "A → A → bool", "n": "num", "s": "num", "t": "num", "d": "num"}
	Φ := f.prop("lexicographic_minimum_property(F, lt, n, s, t, d)", vars)
	result := f.benchmark(Input{Structure: Structure{Field: F, Order: lt}, Proposition: Φ, Unfold: f.unfolder, Vocabulary: f.vocab}, "lexicographic_minimum_formula(n, s, t, d)", vars)

	count := f.term("coefficient_count(n, d)", vars)
	requireBlock(t, result.Names.Blocks[0], "f", PolynomialBlock, numeral(0), count)
	requireBlock(t, result.Names.Blocks[1], "q", PolynomialBlock, count, count)
	requireBlock(t, result.Names.Blocks[2], "g", FamilyBlock, f.term("coefficient_count(n, d) + coefficient_count(n, d)", vars), f.term("s * coefficient_count(n, d)", vars))
	requireBlock(t, result.Names.Blocks[3], "h", FamilyBlock, f.term("coefficient_count(n, d) + coefficient_count(n, d) + s * coefficient_count(n, d)", vars), f.term("t * coefficient_count(n, d)", vars))
	requireBlock(t, result.Names.Blocks[4], "M", ScalarBlock, f.term("coefficient_count(n, d) + coefficient_count(n, d) + s * coefficient_count(n, d) + t * coefficient_count(n, d)", vars), numeral(1))

	require.Len(t, result.Obligations, 2)
	require.True(t, result.Obligations[1].Statement.AlphaEquals(f.prop("ordered_field_on(F, lt)", vars)))
	require.Equal(t, Unfolding, result.Plan.Kind)
	require.Equal(t, "semialgebraic_properties.LexPropertyDef", result.Plan.Citations[0].Lemma)
}

// The polynomial Brouwer property: the image of the cube under the
// polynomial map is a normal tuple, read as the true formula beside
// the cube's comparisons, and the fixed point is a tuple equality.
func TestReify_PolynomialBrouwerProperty(t *testing.T) {
	f := newFixture(t)
	F, lt := f.field("F", "A"), f.order("lt", "A")
	vars := map[string]string{"F": "field_ops(A)", "lt": "A → A → bool", "n": "num", "d": "num"}
	Φ := f.prop("polynomial_brouwer_property(F, lt, n, d)", vars)
	result := f.benchmark(Input{Structure: Structure{Field: F, Order: lt}, Proposition: Φ, Unfold: f.unfolder, Vocabulary: f.vocab}, "polynomial_brouwer_formula(n, d)", vars)
	requireBlock(t, result.Names.Blocks[0], "P", FamilyBlock, numeral(0), f.term("n * coefficient_count(n, d)", vars))
	require.Len(t, result.Names.Blocks, 3)
}

// Solution descent: the system over F with its families named, and
// the same system over G at the families' images, reify to one
// formula, with the parameters' blocks first and the solution's block
// after them; the shape is the hand-written system formula's.
func TestReify_SolutionDescentBothSides(t *testing.T) {
	f := newFixture(t)
	common := map[string]string{"n": "num", "r": "num", "s": "num", "d": "num"}
	varsF := map[string]string{"F": "field_ops(A)", "P": "num → (num → num) → A", "Q": "num → (num → num) → A"}
	varsG := map[string]string{"G": "field_ops(B)", "i": "A → B", "P": "num → (num → num) → A", "Q": "num → (num → num) → A"}
	for k, v := range common {
		varsF[k], varsG[k] = v, v
	}
	n, r, s, d := num("n"), num("r"), num("s"), num("d")
	family := func(name string, term core.Term, count core.Term) Parameter {
		return Parameter{Name: name, Term: term, Kind: FamilyBlock, Dimension: n, Degree: d, Count: count}
	}

	F := f.field("F", "A")
	ΦF := f.prop("∃x:(num → A). polynomial_system_solution(field_ring(F), n, r, s, P, Q, x)", varsF)
	inF := Input{Structure: Structure{Field: F}, Proposition: ΦF, Unfold: f.unfolder, Vocabulary: f.vocab,
		Parameters: []Parameter{family("P", f.term("P", varsF), r), family("Q", f.term("Q", varsF), s)}}
	overF := f.benchmark(inF, "polynomial_system_formula(n, r, s, d)", varsF)

	G := f.field("G", "B")
	imageP := f.term("λj:num. λm:(num → num). i(P(j, m))", varsG)
	imageQ := f.term("λj:num. λm:(num → num). i(Q(j, m))", varsG)
	ΦG := f.prop("∃y:(num → B). polynomial_system_solution(field_ring(G), n, r, s, λj:num. λm:(num → num). i(P(j, m)), λj:num. λm:(num → num). i(Q(j, m)), y)", varsG)
	inG := Input{Structure: Structure{Field: G}, Proposition: ΦG, Unfold: f.unfolder, Vocabulary: f.vocab,
		Parameters: []Parameter{family("P", imageP, r), family("Q", imageQ, s)}}
	overG := f.benchmark(inG, "polynomial_system_formula(n, r, s, d)", varsG)

	require.True(t, overF.Formula.AlphaEquals(overG.Formula), "the two sides of the descent reify to different formulas:\n%s\n%s",
		ext.FormatTermForParser(overF.Formula), ext.FormatTermForParser(overG.Formula))

	for _, result := range []*Result{overF, overG} {
		require.Len(t, result.Names.Blocks, 3)
		requireBlock(t, result.Names.Blocks[0], "P", FamilyBlock, numeral(0), f.term("r * coefficient_count(n, d)", common))
		requireBlock(t, result.Names.Blocks[1], "Q", FamilyBlock, f.term("r * coefficient_count(n, d)", common), f.term("s * coefficient_count(n, d)", common))
		require.True(t, result.Names.Blocks[0].Parameter && result.Names.Blocks[1].Parameter && !result.Names.Blocks[2].Parameter)
		require.Equal(t, TupleBlock, result.Names.Blocks[2].Kind)
		require.True(t, result.Names.Blocks[2].Start.AlphaEquals(result.Names.Frontier))
		require.True(t, result.Names.Frontier.AlphaEquals(f.term("r * coefficient_count(n, d) + s * coefficient_count(n, d)", common)))
	}

	// The F side's obligations: the structure, and each family in the
	// algebra below n with the common degree bound, at every member.
	require.Len(t, overF.Obligations, 5)
	require.True(t, overF.Obligations[1].Statement.AlphaEquals(f.prop("∀j:num. j < r ⇒ P(j) ∈ polynomial_algebra(field_ring(F), {i:num | i < n})", varsF)),
		"got %s", ext.FormatTermForParser(overF.Obligations[1].Statement))
	require.True(t, overF.Obligations[2].Statement.AlphaEquals(f.prop("∀j:num. j < r ⇒ polynomial_bound(field_ring(F), n, d, P(j))", varsF)))
	require.Equal(t, "Q", overF.Obligations[3].Owner)
	require.Equal(t, PolynomialObligation, overF.Obligations[4].Kind)
}

// A tuple equality is a coordinatewise finite conjunction of equality
// atoms over the two blocks.
func TestReify_TupleEqualityIsCoordinatewise(t *testing.T) {
	f := newFixture(t)
	F := f.field("F", "A")
	vars := map[string]string{"F": "field_ops(A)", "n": "num"}
	Φ := f.prop("∀x y:(num → A). ring_tuple(field_ring(F), n, x) ∧ ring_tuple(field_ring(F), n, y) ⇒ x = y", vars)
	result, err := Reify(Input{Structure: Structure{Field: F}, Proposition: Φ, Vocabulary: f.vocab})
	require.NoError(t, err)
	require.Equal(t, "∀[2·n]⋀[n]a", skeleton(result.Formula))
	expected := f.term("fo_all_range(0, n, fo_all_range(n, n, fo_conjoin(ring_true_formula, n, λj:num. ring_equality_formula(polynomial_algebra_var(int_ring, j), polynomial_algebra_var(int_ring, n + j)))))", vars)
	require.True(t, result.Formula.AlphaEquals(expected), "got %s", ext.FormatTermForParser(result.Formula))
	equality := result.Plan.Children[0].Children[0]
	require.Equal(t, TupleEquality, equality.Kind)
	require.Equal(t, "polynomial_encoding.RingTupleEqual", equality.Citations[0].Lemma)
}

// A coordinate at a numeral below the tuple's numeral length reads as
// the variable of that coordinate's name, as a binder-bounded index
// does.
func TestReify_NumeralCoordinate(t *testing.T) {
	f := newFixture(t)
	F := f.field("F", "A")
	vars := map[string]string{"F": "field_ops(A)"}
	Φ := f.prop("∀x:(num → A). ring_tuple(field_ring(F), 1, x) ⇒ x(0) = F.zero", vars)
	result, err := Reify(Input{Structure: Structure{Field: F}, Proposition: Φ, Vocabulary: f.vocab})
	require.NoError(t, err)
	expected := f.term("fo_all_range(0, 1, ring_equality_formula(polynomial_algebra_var(int_ring, 0), λm:(num → num). int_of_num(0)))", vars)
	require.True(t, result.Formula.AlphaEquals(expected), "got %s", ext.FormatTermForParser(result.Formula))
	coordinate := result.Plan.Children[0].Children[0]
	require.Equal(t, Coordinate, coordinate.Kind)
}

// The obligations of the three parameter kinds, as the design states them.
func TestReify_ParameterObligations(t *testing.T) {
	f := newFixture(t)
	F := f.field("F", "A")
	vars := map[string]string{"F": "field_ops(A)", "n": "num", "d": "num", "a": "A", "p": "(num → num) → A", "x": "num → A"}
	Φ := f.prop("polynomial_value(field_ring(F), p, x) = F.add(a, F.one)", vars)
	result, err := Reify(Input{Structure: Structure{Field: F}, Proposition: Φ, Vocabulary: f.vocab, Parameters: []Parameter{
		{Name: "a", Term: f.term("a", vars), Kind: ScalarBlock},
		{Name: "p", Term: f.term("p", vars), Kind: PolynomialBlock, Dimension: num("n"), Degree: num("d")},
		{Name: "x", Term: f.term("x", vars), Kind: TupleBlock, Dimension: num("n")},
	}})
	require.NoError(t, err)
	statements := []string{
		"field_on(F)",
		"a ∈ F.carrier",
		"p ∈ polynomial_algebra(field_ring(F), {i:num | i < n})",
		"polynomial_bound(field_ring(F), n, d, p)",
		"ring_tuple(field_ring(F), n, x)",
	}
	require.Len(t, result.Obligations, len(statements))
	for i, text := range statements {
		require.True(t, result.Obligations[i].Statement.AlphaEquals(f.prop(text, vars)), "obligation %d: %s", i, ext.FormatTermForParser(result.Obligations[i].Statement))
	}
	// a at name 0, p's coefficients from 1, x's coordinates past them.
	expected := f.term("ring_equality_formula(polynomial_code(n, d, 1, 1 + coefficient_count(n, d)), ring_add(integer_polynomial_ring, polynomial_algebra_var(int_ring, 0), polynomial_algebra_one(int_ring)))", vars)
	require.True(t, result.Formula.AlphaEquals(expected), "got %s", ext.FormatTermForParser(result.Formula))
}

// The goals the reifier refuses, each at the subterm it stops at.
func TestReify_Refusals(t *testing.T) {
	f := newFixture(t)
	F, lt := f.field("F", "A"), f.order("lt", "A")
	vars := map[string]string{"F": "field_ops(A)", "lt": "A → A → bool", "n": "num", "m": "num", "d": "num", "a": "A", "f": "(num → num) → A", "g": "(num → num) → A", "P": "num → (num → num) → A", "x": "num → A"}
	cases := []struct {
		name        string
		proposition string
		ordered     bool
		parameters  []Parameter
		reason      Reason
		subterm     string
	}{
		{"a function the formulas cannot speak of", "∀a:A. a ∈ F.carrier ⇒ exp_map(a) = a", false, nil, NotFirstOrder, "exp_map(a)"},
		{"a tuple quantifier guarded on its coordinates alone", "∀x:(num → A). (∀i:num. i < n ⇒ x(i) ∈ F.carrier) ⇒ x = x", false, nil, UnguardedQuantifier, ""},
		{"a free parameter in sentence mode", "∀x:(num → A). ring_tuple(field_ring(F), n, x) ⇒ polynomial_value(field_ring(F), f, x) = F.zero", false, nil, FreeParameterInSentence, "f"},
		{"a free variable no parameter names", "∀x:(num → A). ring_tuple(field_ring(F), n, x) ⇒ polynomial_value(field_ring(F), f, x) = F.zero", false,
			[]Parameter{{Name: "g", Term: core.Var("g", f.term("g", vars).Type()), Kind: PolynomialBlock, Dimension: num("n"), Degree: num("d")}}, UndeclaredParameter, "f"},
		{"a constant without an unfolding", "mystery(F, n)", false, nil, NoUnfolding, "mystery(F, n)"},
		{"a constant whose definition leaves the grammar", "exponential_fixed(F)", false, nil, NotFirstOrder, "exp_map(a)"},
		{"a tuple of another length than the polynomial's dimension", "∀x:(num → A). ring_tuple(field_ring(F), m, x) ⇒ ∀p:((num → num) → A). polynomial_bound(field_ring(F), n, d, p) ⇒ polynomial_value(field_ring(F), p, x) = F.zero", false, nil, DimensionMismatch, ""},
		{"a sum over an index set the grammar does not read", "module_sum(F.add, F.zero, {j:num | j ≤ n}, λj:num. F.one) = F.zero", false, nil, NotFirstOrder, "{j:num | j ≤ n}"},
		{"a sum under another operation than the structure's addition", "module_sum(F.mul, F.one, {j:num | j < n}, λj:num. F.one) = F.zero", false, nil, NotFirstOrder, ""},
		{"a sum of a family that is no abstraction", "∀x:(num → A). ring_tuple(field_ring(F), n, x) ⇒ module_sum(F.add, F.zero, {j:num | j < n}, x) = F.zero", false, nil, NotFirstOrder, "x"},
		{"a computed index without an arithmetic", "∀x:(num → A). ring_tuple(field_ring(F), n, x) ⇒ ∀j:num. j < n ⇒ x(j + 0) = F.zero", false, nil, IndexOutsideBlock, ""},
		{"an index without a bound", "∀j:num. F.zero = F.zero", false, nil, UnguardedQuantifier, ""},
		{"a polynomial evaluated at a polynomial map", "∀P:(num → (num → num) → A). (∀j:num. j < n ⇒ polynomial_bound(field_ring(F), n, d, P(j))) ⇒ ∀p:((num → num) → A). polynomial_bound(field_ring(F), n, d, p) ⇒ ∀x:(num → A). ring_tuple(field_ring(F), n, x) ⇒ polynomial_value(field_ring(F), p, polynomial_map(field_ring(F), n, P, x)) = F.zero", false, nil, NotFirstOrder, ""},
		{"an order atom in the ring theory", "∀a:A. a ∈ F.carrier ⇒ ordered_le(lt, a, F.zero)", false, nil, FreeParameterInSentence, "lt"},
		{"a quantifier over a set", "∀S:set(A). S = S", false, nil, NotFirstOrder, ""},
		{"a coordinate at an index past the tuple", "∀x:(num → A). ring_tuple(field_ring(F), n, x) ⇒ x(m) = F.zero", false, nil, IndexOutsideBlock, ""},
		{"a coordinate at a numeral at the tuple's length", "∀x:(num → A). ring_tuple(field_ring(F), 1, x) ⇒ x(1) = F.zero", false, nil, IndexOutsideBlock, "x(1)"},
		{"a coordinate at an index bounded by another length", "∀x:(num → A). ring_tuple(field_ring(F), n, x) ⇒ ∀j:num. j < m ⇒ x(j) = F.zero", false, nil, IndexOutsideBlock, ""},
		{"a polynomial in one variable evaluated at a compound term", "∀p:(num → A). ring_tuple(field_ring(F), n, p) ⇒ ∀a:A. a ∈ F.carrier ⇒ polynomial_eval(F.add, F.zero, F.mul, F.one, p, F.add(a, a)) = F.zero", false, nil, NotFirstOrder, ""},
		{"a family member at an index past the family", "∀P:(num → (num → num) → A). (∀j:num. j < n ⇒ polynomial_bound(field_ring(F), n, d, P(j))) ⇒ ∀x:(num → A). ring_tuple(field_ring(F), n, x) ⇒ polynomial_value(field_ring(F), P(n), x) = F.zero", false, nil, IndexOutsideBlock, ""},
	}
	for _, c := range cases {
		t.Run(c.name, func(t *testing.T) {
			structure := Structure{Field: F}
			if c.ordered {
				structure.Order = lt
			}
			_, err := Reify(Input{Structure: structure, Proposition: f.prop(c.proposition, vars), Parameters: c.parameters, Unfold: f.unfolder, Vocabulary: f.vocab})
			require.Error(t, err)
			refusal, ok := err.(*Refusal)
			require.True(t, ok, "%v", err)
			require.Equal(t, c.reason, refusal.Reason, "%v", err)
			if c.subterm != "" {
				require.True(t, refusal.Subterm.AlphaEquals(f.term(c.subterm, vars)), "refused at %s", ext.FormatTermForParser(refusal.Subterm))
			}
			require.NotEmpty(t, err.Error())
		})
	}
}

// A disjunction needs fo_or; without it the vocabulary is constructed
// and the proposition refused at the disjunction.
func TestReify_OptionalConnectives(t *testing.T) {
	f := newFixture(t)
	vocab, err := NewVocabulary(func(name core.TermName) core.ConstTermMeta {
		if name == "fo_or" || name == "fo_iff" {
			return core.ConstTermMeta{}
		}
		return f.lookup(name)
	})
	require.NoError(t, err)
	F := f.field("F", "A")
	vars := map[string]string{"F": "field_ops(A)"}
	_, err = Reify(Input{Structure: Structure{Field: F}, Proposition: f.prop("∀a:A. a ∈ F.carrier ⇒ a = F.zero ∨ a = F.one", vars), Vocabulary: vocab})
	require.Error(t, err)
	require.Equal(t, MissingVocabulary, err.(*Refusal).Reason)

	result, err := Reify(Input{Structure: Structure{Field: F}, Proposition: f.prop("∀a:A. a ∈ F.carrier ⇒ a = F.zero ∨ a = F.one", vars), Vocabulary: f.vocab})
	require.NoError(t, err)
	require.Equal(t, "∀[1]∨[a a]", skeleton(result.Formula))
}

// A vocabulary missing a required constant names it.
func TestNewVocabulary_MissingNames(t *testing.T) {
	f := newFixture(t)
	_, err := NewVocabulary(func(name core.TermName) core.ConstTermMeta {
		if name == "fo_atom" || name == "polynomial_code" {
			return core.ConstTermMeta{}
		}
		return f.lookup(name)
	})
	require.Error(t, err)
	require.Contains(t, err.Error(), "fo_atom")
	require.Contains(t, err.Error(), "polynomial_code")
	require.Len(t, VocabularyNames(), len(f.vocab.entries()))
}

// The ordered theory's atoms: a strict comparison is one atom of the
// difference, a weak one the negated reverse, an equality two weak ones.
func TestReify_OrderedAtoms(t *testing.T) {
	f := newFixture(t)
	F, lt := f.field("F", "A"), f.order("lt", "A")
	vars := map[string]string{"F": "field_ops(A)", "lt": "A → A → bool"}
	Φ := f.prop("∀a b:A. a ∈ F.carrier ∧ b ∈ F.carrier ⇒ lt(a, b) ∧ ordered_le(lt, F.neg(a), b) ∧ F.mul(a, b) = F.sub(a, integer_map(field_ring(F), int_of_num(3)))", vars)
	result, err := Reify(Input{Structure: Structure{Field: F, Order: lt}, Proposition: Φ, Vocabulary: f.vocab})
	require.NoError(t, err)
	require.Equal(t, "∀[2]∧[a ¬a ∧[¬a ¬a]]", skeleton(result.Formula))
	expected := f.term("fo_forall(0, fo_forall(1, fo_and(fo_and(fo_atom(λm:(num → num). polynomial_algebra_var(int_ring, 0, m) - polynomial_algebra_var(int_ring, 1, m)), polynomial_weak_inequality_formula(ring_neg(integer_polynomial_ring, polynomial_algebra_var(int_ring, 0)), polynomial_algebra_var(int_ring, 1))), ordered_ring_equality_formula(ring_mul(integer_polynomial_ring, polynomial_algebra_var(int_ring, 0), polynomial_algebra_var(int_ring, 1)), ring_sub(integer_polynomial_ring, polynomial_algebra_var(int_ring, 0), polynomial_algebra_const(int_ring, int_of_num(3)))))))", vars)
	require.True(t, result.Formula.AlphaEquals(expected), "got %s", ext.FormatTermForParser(result.Formula))
}

// A guard predicate at a term the grammar already normalizes is the
// true formula: a bounded polynomial lies in the algebra below its
// dimension, a polynomial map's image is a ring tuple.
func TestReify_NormalizedGuardsAreTrue(t *testing.T) {
	f := newFixture(t)
	F := f.field("F", "A")
	vars := map[string]string{"F": "field_ops(A)", "n": "num", "d": "num"}
	Φ := f.prop("∀p:((num → num) → A). polynomial_bound(field_ring(F), n, d, p) ⇒ p ∈ polynomial_algebra(field_ring(F), {i:num | i < n}) ∧ polynomial_bound(field_ring(F), n, d, p)", vars)
	result, err := Reify(Input{Structure: Structure{Field: F}, Proposition: Φ, Vocabulary: f.vocab})
	require.NoError(t, err)
	require.Equal(t, "∀[coefficient_count(n, d)]⊤", skeleton(result.Formula))

	Ψ := f.prop("∀P:(num → (num → num) → A). (∀j:num. j < n ⇒ polynomial_bound(field_ring(F), n, d, P(j))) ⇒ ∀x:(num → A). ring_tuple(field_ring(F), n, x) ⇒ ring_tuple(field_ring(F), n, polynomial_map(field_ring(F), n, P, x))", vars)
	result, err = Reify(Input{Structure: Structure{Field: F}, Proposition: Ψ, Vocabulary: f.vocab})
	require.NoError(t, err)
	require.Equal(t, "∀[coefficient_count(n, d)·n + n]⊤", skeleton(result.Formula))
	image := result.Plan.Children[0].Children[0]
	require.Equal(t, NormalTuple, image.Kind)
	require.Equal(t, "polynomial_encoding.PolynomialMapRingTuple", image.Citations[1].Lemma)
}

// A polynomial in one variable, quantified as the ring tuple of its
// coefficients, evaluated at a scalar binder: the univariate code of its
// block at the binder's slot.
func TestReify_UnivariateValue(t *testing.T) {
	f := newFixture(t)
	F := f.field("F", "A")
	vars := map[string]string{"F": "field_ops(A)", "n": "num"}
	Φ := f.prop("∀p:(num → A). ring_tuple(field_ring(F), n, p) ⇒ ∃x:A. x ∈ F.carrier ∧ polynomial_eval(F.add, F.zero, F.mul, F.one, p, x) = F.zero", vars)
	result, err := Reify(Input{Structure: Structure{Field: F}, Proposition: Φ, Unfold: f.unfolder, Vocabulary: f.vocab})
	require.NoError(t, err)
	require.Len(t, result.Names.Blocks, 2)
	requireBlock(t, result.Names.Blocks[0], "p", TupleBlock, numeral(0), num("n"))
	require.Contains(t, ext.FormatTermForParser(result.Formula), "univariate_code(n, 0, n)")
}

// _Arithmetic is a test's arithmetic: it answers every question with
// one verdict and records the questions asked.
type _Arithmetic struct {
	verdict   bool
	questions [][]core.Term
}

func (a *_Arithmetic) Below(hypotheses []core.Term, goal core.Term) bool {
	a.questions = append(a.questions, append(slices.Clone(hypotheses), goal))
	return a.verdict
}

// requireQuestions checks the arithmetic was asked the questions, each
// its hypotheses followed by its goal.
func (f *_Fixture) requireQuestions(a *_Arithmetic, vars map[string]string, want ...[]string) {
	f.t.Helper()
	require.Len(f.t, a.questions, len(want))
	for i, question := range want {
		require.Len(f.t, a.questions[i], len(question))
		for k, text := range question {
			require.True(f.t, a.questions[i][k].AlphaEquals(f.prop(text, vars)), "question %d, term %d: %s", i, k, ext.FormatTermForParser(a.questions[i][k]))
		}
	}
}

// containsTerm tells whether sub occurs in t up to α.
func containsTerm(t, sub core.Term) bool {
	if t.AlphaEquals(sub) {
		return true
	}
	switch u := t.(type) {
	case core.AppliedTerm:
		return containsTerm(u.Fun(), sub) || containsTerm(u.Arg(), sub)
	case core.AbsTerm:
		return containsTerm(u.Body(), sub)
	}
	return false
}

// An existential index is the negation of the finite conjunction of its
// body's negations; the normalized point's leading coordinate is read
// at an index bounded by an index binder, which the arithmetic keeps
// below the tuple's length.
func TestReify_ExistentialIndex(t *testing.T) {
	f := newFixture(t)
	F := f.field("F", "A")
	vars := map[string]string{"F": "field_ops(A)", "n": "num"}
	Φ := f.prop("∀x:(num → A). ring_tuple(field_ring(F), n, x) ⇒ ∃j:num. j < n ∧ x(j) = F.one ∧ (∀i:num. i < j ⇒ x(i) = F.zero)", vars)
	_, err := Reify(Input{Structure: Structure{Field: F}, Proposition: Φ, Vocabulary: f.vocab})
	require.Error(t, err)
	require.Equal(t, IndexOutsideBlock, err.(*Refusal).Reason)

	arithmetic := &_Arithmetic{verdict: true}
	result, err := Reify(Input{Structure: Structure{Field: F}, Proposition: Φ, Arithmetic: arithmetic, Vocabulary: f.vocab})
	require.NoError(t, err)
	f.requireQuestions(arithmetic, map[string]string{"n": "num", "i": "num", "j": "num"}, []string{"i < j", "j < n", "i < n"})
	expected := f.term("fo_all_range(0, n, fo_not(fo_conjoin(ring_true_formula, n, λj:num. fo_not(fo_and(ring_equality_formula(polynomial_algebra_var(int_ring, j), polynomial_algebra_one(int_ring)), fo_conjoin(ring_true_formula, j, λi:num. ring_equality_formula(polynomial_algebra_var(int_ring, i), λm:(num → num). int_of_num(0))))))))", vars)
	require.True(t, result.Formula.AlphaEquals(expected), "got %s", ext.FormatTermForParser(result.Formula))
	exists := result.Plan.Children[0]
	require.Equal(t, ExistsIndex, exists.Kind)
	require.Equal(t, "first_order.ConjoinSemantics", exists.Citations[0].Lemma)
}

// A finite sum of scalar terms over the indices below a bound is the
// integer polynomial ring's sum of their polynomials over the same
// indices, under either spelling of the field's addition and zero.
func TestReify_FiniteSum(t *testing.T) {
	f := newFixture(t)
	F := f.field("F", "A")
	vars := map[string]string{"F": "field_ops(A)", "n": "num"}
	expected := f.term("fo_all_range(0, n, ring_equality_formula(module_sum(ring_add(integer_polynomial_ring), ring_zero(integer_polynomial_ring), {i:num | i < n}, λj:num. ring_mul(integer_polynomial_ring, polynomial_algebra_var(int_ring, j), polynomial_algebra_var(int_ring, j))), λm:(num → num). int_of_num(0)))", vars)
	for _, text := range []string{
		"∀x:(num → A). ring_tuple(field_ring(F), n, x) ⇒ module_sum(F.add, F.zero, {j:num | j < n}, λj:num. F.mul(x(j), x(j))) = F.zero",
		"∀x:(num → A). ring_tuple(field_ring(F), n, x) ⇒ module_sum(field_ring(F).add, field_ring(F).zero, {j:num | j < n}, λj:num. F.mul(x(j), x(j))) = F.zero",
	} {
		result, err := Reify(Input{Structure: Structure{Field: F}, Proposition: f.prop(text, vars), Vocabulary: f.vocab})
		require.NoError(t, err)
		require.True(t, result.Formula.AlphaEquals(expected), "got %s", ext.FormatTermForParser(result.Formula))
		sum := result.Plan.Children[0].Children[0]
		require.Equal(t, Sum, sum.Kind)
		require.Equal(t, "ring_homomorphism.MapSum", sum.Citations[1].Lemma)
		require.Equal(t, Operation, sum.Children[0].Kind)
	}
}

// A family member and a coordinate at computed indices: the null-space
// condition of a flattened double-indexed family. The member Q(j·N + c)
// is read at its code past j·N + c blocks of the family, the bound
// j·N + c < r·N asked of the arithmetic under the two index bounds.
func TestReify_ComputedIndex(t *testing.T) {
	f := newFixture(t)
	F := f.field("F", "A")
	vars := map[string]string{"F": "field_ops(A)", "N": "num", "r": "num", "d": "num", "Q": "num → (num → num) → A"}
	Φ := f.prop("∀x a:(num → A). ring_tuple(field_ring(F), N, x) ∧ ring_tuple(field_ring(F), N, a) ⇒ ∀j:num. j < r ⇒ module_sum(F.add, F.zero, {c:num | c < N}, λc:num. F.mul(polynomial_value(field_ring(F), Q(j * N + c), x), a(c))) = F.zero", vars)
	Q := Parameter{Name: "Q", Term: f.term("Q", vars), Kind: FamilyBlock, Dimension: num("N"), Degree: num("d"), Count: f.term("r * N", vars)}
	arithmetic := &_Arithmetic{verdict: true}
	result, err := Reify(Input{Structure: Structure{Field: F}, Proposition: Φ, Parameters: []Parameter{Q}, Arithmetic: arithmetic, Vocabulary: f.vocab})
	require.NoError(t, err)
	indices := map[string]string{"N": "num", "r": "num", "d": "num", "j": "num", "c": "num"}
	f.requireQuestions(arithmetic, indices, []string{"c < N", "j < r", "j * N + c < r * N"})
	code := f.term("polynomial_code(N, d, (j * N + c) * coefficient_count(N, d), r * N * coefficient_count(N, d))", indices)
	require.True(t, containsTerm(result.Formula, code), "got %s", ext.FormatTermForParser(result.Formula))

	arithmetic.verdict = false
	_, err = Reify(Input{Structure: Structure{Field: F}, Proposition: Φ, Parameters: []Parameter{Q}, Arithmetic: arithmetic, Vocabulary: f.vocab})
	require.Error(t, err)
	refusal := err.(*Refusal)
	require.Equal(t, IndexOutsideBlock, refusal.Reason)
	require.True(t, refusal.Subterm.AlphaEquals(f.term("Q(j * N + c)", map[string]string{"Q": "num → (num → num) → A", "j": "num", "N": "num", "c": "num"})), "refused at %s", ext.FormatTermForParser(refusal.Subterm))
}
