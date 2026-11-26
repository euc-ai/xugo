package gates

import (
	"context"
	"slices"
	"sort"
	"sync"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/library/serve/testenv"
	"github.com/euc-ai/xugo/prover/bridge"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/euc-ai/xugo/prover/reify"
	"github.com/euc-ai/xugo/utils"
	"github.com/stretchr/testify/require"
)

// _BridgeLibrary serves the builder the corpus: each library theorem
// as its registered statement, which the replay gate holds to its
// proof, and arithmetic by the arith closer on a goal of its own. It
// records what the builder read.
type _BridgeLibrary struct {
	t     *testing.T
	ctx   context.Context
	mu    sync.Mutex
	certs map[string]core.Prop
	reads map[string]bool
	arith int
	// extra are theorems served under names no corpus entry has: a
	// test's sources; extraConstants the constants a test mints for
	// them.
	extra          map[string]core.Prop
	extraConstants map[core.TermName]core.ConstTermMeta
}

func newBridgeLibrary(t *testing.T) *_BridgeLibrary {
	return &_BridgeLibrary{t: t, ctx: context.Background(), certs: map[string]core.Prop{}, reads: map[string]bool{}}
}

func (l *_BridgeLibrary) Theorem(name string) core.Prop {
	l.mu.Lock()
	defer l.mu.Unlock()
	l.reads[name] = true
	if cert, ok := l.certs[name]; ok {
		return cert
	}
	if cert, ok := l.extra[name]; ok {
		return cert
	}
	e, ok := registry.ByName(name)
	require.True(l.t, ok, "the corpus has no entry %s", name)
	cert := core.NewAxiom(e.Statement().Prop.Conclusion())
	l.certs[name] = cert
	return cert
}

func (l *_BridgeLibrary) Constant(name core.TermName) core.ConstTermMeta {
	if meta, ok := l.extraConstants[name]; ok {
		return meta
	}
	meta, ok := registry.GetConstMetaManager().LoadConstMeta(name)
	if !ok {
		return core.ConstTermMeta{}
	}
	return meta
}

func (l *_BridgeLibrary) Arith(goal core.Prop) core.Prop {
	l.mu.Lock()
	l.arith++
	l.mu.Unlock()
	root := proof.CreateGoalStack(goal)
	proof.ApplyArithSimplify(l.ctx, root)
	if !root.Proved() {
		return nil
	}
	return root.PromisedThm()
}

func (l *_BridgeLibrary) Stating(fact core.Term) core.Prop {
	e, ok := registry.Stating(core.MakeProp(fact))
	if !ok {
		return nil
	}
	return l.Theorem(e.Name)
}

func (l *_BridgeLibrary) read() []string {
	var names []string
	for n := range l.reads {
		names = append(names, n)
	}
	sort.Strings(names)
	return names
}

// bridgeVocabulary is the reifier's vocabulary read off the corpus.
func bridgeVocabulary(t *testing.T) *reify.Vocabulary {
	lib := &_BridgeLibrary{}
	vocab, err := reify.NewVocabulary(lib.Constant)
	require.NoError(t, err)
	return vocab
}

// bridgeProposition parses a closed statement in the corpus and returns
// its body with the bound variables free, in binding order.
func bridgeProposition(t *testing.T, text string) (core.Term, []core.VarTerm) {
	s := proof.NewScript(testenv.MakeT(t))
	p := s.MakePropText(text)
	list, body := ext.DecomposesFORALL(p.Conclusion())
	return body, slices.Collect(list.Iter())
}

// bridgeSentence parses a closed statement and frees its first k bound
// variables, the structure and its numeric data, leaving the rest of
// the proposition as written.
func bridgeSentence(t *testing.T, text string, k int) (core.Term, []core.VarTerm) {
	s := proof.NewScript(testenv.MakeT(t))
	body := s.MakePropText(text).Conclusion()
	var vars []core.VarTerm
	for range k {
		abs := ext.MatchesFORALL(body)
		require.False(t, abs.IsZero())
		vars = append(vars, abs.Var())
		body = abs.Body()
	}
	return body, vars
}

// buildSentence reifies a sentence about F and builds its bridge,
// checking the theorem's shape: Φ ⇔ ring_formula_truth(F, φ) under
// field_on(F).
func buildSentence(t *testing.T, text string, k int) (*_BridgeLibrary, *reify.Result) {
	return buildSentenceIn(t, text, k, false)
}

// buildSentenceIn is buildSentence in the ring or the ordered theory,
// the order the second bound variable.
func buildSentenceIn(t *testing.T, text string, k int, ordered bool) (*_BridgeLibrary, *reify.Result) {
	t.Helper()
	installBundles()
	Φ, vars := bridgeSentence(t, text, k)
	structure := reify.Structure{Field: vars[0]}
	if ordered {
		structure.Order = vars[1]
	}
	lib := newBridgeLibrary(t)
	in := reify.Input{Structure: structure, Proposition: Φ, Unfold: bridge.DefinitionUnfolder(), Arithmetic: bridge.Arithmetic(lib), Vocabulary: bridgeVocabulary(t)}
	res, err := reify.Reify(in)
	require.NoError(t, err)
	cert := core.Force(context.Background(), core.AsThm(bridge.Build(in, res, lib)))
	l, r, ok := core.MatchesEQ(cert.Conclusion())
	require.True(t, ok)
	require.True(t, l.AlphaEquals(Φ), "left side %s", ext.PrintTerm(l))
	_, args := ext.MatchesApply(r)
	require.True(t, args[len(args)-1].AlphaEquals(res.Formula), "right side %s", ext.PrintTerm(r))
	require.Equal(t, 1, cert.NumHyps(), "hypotheses: %s", prop.PrintProp(cert))
	return lib, res
}

// The scalar quantifiers and the connectives: a universal and an
// existential scalar, equalities of variables, a disjunction, a
// negation, a conjunction, an equivalence, and the true and false
// propositions.
func TestElementarityBridge_ScalarsAndConnectives(t *testing.T) {
	lib, _ := buildSentence(t, "∀F:field_ops(A). ∀a:A. a ∈ F.carrier ⇒ ∃b:A. b ∈ F.carrier ∧ (a = b ∨ ¬(a = b)) ∧ (a = a ⇔ b = b) ∧ (⊤ ∨ ⊥)", 1)
	t.Logf("reads %v", lib.read())
}

// A polynomial quantifier and a tuple quantifier: the value of a
// bounded polynomial at a ring tuple lies in the carrier, each
// coordinate below the length equals itself, and the tuple is normal.
func TestElementarityBridge_PolynomialsAndIndices(t *testing.T) {
	lib, _ := buildSentence(t, "∀F:field_ops(A). ∀n d:num. ∀p:((num → num) → A). polynomial_bound(field_ring(F), n, d, p) ⇒ ∀x:(num → A). ring_tuple(field_ring(F), n, x) ⇒ polynomial_value(field_ring(F), p, x) ∈ F.carrier ∧ (∀j:num. j < n ⇒ x(j) = x(j)) ∧ ring_tuple(field_ring(F), n, x)", 3)
	t.Logf("reads %v", lib.read())
}

// The Ax–Grothendieck property at a degree bound: the bridge the
// builder proves from the reifier's plan is a kernel theorem, under the
// one obligation field_on(F), that the property holds exactly when the
// reified sentence is true.
func TestElementarityBridge_AxProperty(t *testing.T) {
	installBundles()
	Φ, vars := bridgeProposition(t, "∀F:field_ops(A). ∀n d:num. ax_property(F, n, d)")
	F := vars[0]
	in := reify.Input{Structure: reify.Structure{Field: F}, Proposition: Φ, Unfold: bridge.DefinitionUnfolder(), Vocabulary: bridgeVocabulary(t)}
	res, err := reify.Reify(in)
	require.NoError(t, err)
	lib := newBridgeLibrary(t)
	thm := bridge.Build(in, res, lib)
	builderReads := lib.read()

	cert := core.Force(context.Background(), core.AsThm(thm))
	require.False(t, cert.IsZero())
	l, r, ok := core.MatchesEQ(cert.Conclusion())
	require.True(t, ok)
	require.True(t, l.AlphaEquals(Φ), "left side %s", ext.PrintTerm(l))
	head, args := ext.MatchesApply(r)
	c, isConst := head.AsConst()
	require.True(t, isConst && c.Name() == "ring_formula_truth", "right side %s", ext.PrintTerm(r))
	require.True(t, args[1].AlphaEquals(res.Formula))
	require.Equal(t, 1, cert.NumHyps(), "hypotheses: %s", prop.PrintProp(cert))
	fieldOn, _ := bridgeProposition(t, "∀F:field_ops(A). field_on(F)")
	require.True(t, cert.Hyp(0).AlphaEquals(fieldOn), "hypothesis %s", ext.PrintTerm(cert.Hyp(0)))
	t.Logf("reads %d lemmas: %v", len(builderReads), builderReads)
	t.Logf("arithmetic goals: %d", lib.arith)

}

// Two builds of one reification prove one theorem from one set of
// reads: nothing in the builder reads a map's order or the clock.
func TestElementarityBridge_Deterministic(t *testing.T) {
	installBundles()
	Φ, vars := bridgeProposition(t, "∀F:field_ops(A). ∀n d:num. ax_property(F, n, d)")
	in := reify.Input{Structure: reify.Structure{Field: vars[0]}, Proposition: Φ, Unfold: bridge.DefinitionUnfolder(), Vocabulary: bridgeVocabulary(t)}
	res, err := reify.Reify(in)
	require.NoError(t, err)
	first, second := newBridgeLibrary(t), newBridgeLibrary(t)
	a := bridge.Build(in, res, first)
	b := bridge.Build(in, res, second)
	require.True(t, a.Conclusion().Equals(b.Conclusion()))
	require.Equal(t, first.read(), second.read())
	require.Equal(t, first.arith, second.arith)
}

// The existential polynomial and family quantifiers: a family whose
// members, read at a bounded index, take carrier values at every ring
// tuple, and a bounded polynomial.
func TestElementarityBridge_ExistentialPolynomials(t *testing.T) {
	lib, _ := buildSentence(t, "∀F:field_ops(A). ∀n d:num. (∃P:(num → (num → num) → A). (∀j:num. j < n ⇒ polynomial_bound(field_ring(F), n, d, P(j))) ∧ (∀j:num. j < n ⇒ ∀x:(num → A). ring_tuple(field_ring(F), n, x) ⇒ polynomial_value(field_ring(F), P(j), x) ∈ F.carrier)) ∧ (∃p:((num → num) → A). polynomial_bound(field_ring(F), n, d, p))", 3)
	t.Logf("reads %v", lib.read())
}

// The Ax–Grothendieck property transferred from a family of models by
// prime: the executor reads the goal and the family's property as one
// sentence, proves both bridges and the sentence's closedness, and
// cites the prime-family transfer. The theorem's hypotheses are the two
// facts the call names.
func TestElementarity_AxFromPrimeFamily(t *testing.T) {
	installBundles()
	Φ, vars := bridgeSentence(t, "∀F:field_ops(A). ∀n d:num. ax_property(F, n, d)", 3)
	F, n, d := vars[0], vars[1], vars[2]
	familyText := "∀F:field_ops(A). ∀n d:num. ∀p:num. nat_prime(p) ⇒ ∃G:field_ops(B). algebraically_closed_field_on(G) ∧ field_characteristic(G, p) ∧ ax_property(G, n, d)"
	family, _ := bridgeSentence(t, familyText, 3)
	closedText := "∀F:field_ops(A). algebraically_closed_field_on(F)"
	closedF, _ := bridgeSentence(t, closedText, 1)
	_ = n
	_ = d
	call := bridge.Call{
		Goal:   Φ,
		Facts:  []core.Prop{core.Assume(closedF)},
		Source: bridge.Source{Family: core.Assume(family)},
	}
	lib := newBridgeLibrary(t)
	outcome, err := bridge.Elementarity(call, bridgeVocabulary(t), lib)
	require.NoError(t, err)
	cert := core.Force(context.Background(), core.AsThm(outcome.Theorem))
	require.True(t, cert.Conclusion().AlphaEquals(Φ), "conclusion %s", ext.PrintTerm(cert.Conclusion()))
	require.Equal(t, 2, cert.NumHyps(), "hypotheses: %s", prop.PrintProp(cert))
	require.True(t, cert.HasHyp(closedF) && cert.HasHyp(family), "hypotheses: %s", prop.PrintProp(cert))
	require.Equal(t, bridge.EquivalenceMode, outcome.Mode)
	require.Equal(t, bridge.AlgebraicallyClosedTheory, outcome.Theory)
	_ = F
	t.Logf("reads %d lemmas: %v", len(lib.read()), lib.read())
	t.Logf("arithmetic goals: %d", lib.arith)
}

// bridgeEnv is a member env whose library serves each corpus entry as
// its registered statement.
func bridgeEnv(t *testing.T) *proof.ProverEnv {
	env := testenv.MakeT(t)
	lib := newBridgeLibrary(t)
	env.LibraryResolver = func(name string) (proof.Thm, bool) {
		if _, ok := registry.ByName(name); !ok {
			return nil, false
		}
		return core.AsThm(lib.Theorem(name)), true
	}
	return env
}

// The composite: ByElementarity as a chapter's Go writes it, on a section
// whose hypotheses are the structure's fact and the family of models,
// and the session's entry on the same leaf. Both close the leaf, and
// the step records the call.
func TestByElementarity_Composite(t *testing.T) {
	installBundles()
	Φ, _ := bridgeSentence(t, "∀F:field_ops(A). ∀n d:num. ax_property(F, n, d)", 3)
	family, _ := bridgeSentence(t, "∀F:field_ops(A). ∀n d:num. ∀p:num. nat_prime(p) ⇒ ∃G:field_ops(B). algebraically_closed_field_on(G) ∧ field_characteristic(G, p) ∧ ax_property(G, n, d)", 3)
	closedF, _ := bridgeSentence(t, "∀F:field_ops(A). algebraically_closed_field_on(F)", 1)
	goal := core.MakeProp(Φ, closedF, family)

	s := proof.NewScript(bridgeEnv(t))
	root := s.Section(goal)
	root.Do(proof.ByElementarity(proof.ResidentHyp(family), proof.ResidentHyp(closedF)))
	require.True(t, root.Proved(), "the Go verb leaves the leaf open")
	require.Contains(t, root.StepDescription(), "ByElementarity")

	session := proof.CreateGoalStack(goal)
	require.NoError(t, proof.ApplyElementarityStep(session, bridgeEnv(t), context.Background(), proof.ElementaritySpec{Family: family, Facts: []core.Term{closedF}}))
	require.True(t, session.Proved(), "the session entry leaves the leaf open")

	refused := proof.CreateGoalStack(goal)
	err := proof.ApplyElementarityStep(refused, bridgeEnv(t), context.Background(), proof.ElementaritySpec{Family: family})
	require.Error(t, err)
	require.Contains(t, err.Error(), "no fact names the goal's structure")
}

// The Ax–Grothendieck property transferred from an entry stating it at
// the complex numbers: the source's binders are the degree data, the
// structure facts and the characteristic agreement are resident.
func TestElementarity_AxFromEntry(t *testing.T) {
	installBundles()
	Φ, _ := bridgeSentence(t, "∀F:field_ops(A). ∀n d:num. ax_property(F, n, d)", 3)
	closedF, _ := bridgeSentence(t, "∀F:field_ops(A). algebraically_closed_field_on(F)", 1)
	closedC, _ := bridgeSentence(t, "algebraically_closed_field_on(complex_field_ops)", 0)
	same, _ := bridgeSentence(t, "∀F:field_ops(A). same_characteristic(F, complex_field_ops)", 1)
	source, _ := bridgeSentence(t, "∀n d:num. ax_property(complex_field_ops, n, d)", 0)
	lib := newBridgeLibrary(t)
	lib.extra = map[string]core.Prop{"test.AxAtComplex": core.NewAxiom(source)}
	call := bridge.Call{
		Goal:   Φ,
		Facts:  []core.Prop{core.Assume(closedF), core.Assume(closedC), core.Assume(same)},
		Source: bridge.Source{Entry: "test.AxAtComplex"},
	}
	outcome, err := bridge.Elementarity(call, bridgeVocabulary(t), lib)
	require.NoError(t, err)
	cert := core.Force(context.Background(), core.AsThm(outcome.Theorem))
	require.True(t, cert.Conclusion().AlphaEquals(Φ), "conclusion %s", ext.PrintTerm(cert.Conclusion()))
	require.Equal(t, 3, cert.NumHyps(), "hypotheses: %s", prop.PrintProp(cert))

	call.Facts = call.Facts[:2]
	_, err = bridge.Elementarity(call, bridgeVocabulary(t), lib)
	require.ErrorContains(t, err, "same_characteristic")
}

// The ordered theory: a scalar's weak and strict comparisons and an
// equality, and a bounded index over a tuple's coordinates.
func TestElementarityBridge_OrderedComparisons(t *testing.T) {
	lib, _ := buildSentenceIn(t, "∀F:field_ops(A). ∀lt:(A → A → bool). ∀n:num. ∀a:A. a ∈ F.carrier ⇒ (ordered_le(lt, a, a) ∧ ¬lt(a, a) ∨ a = a) ∧ (∀x:(num → A). ring_tuple(field_ring(F), n, x) ⇒ ∀j:num. j < n ⇒ ordered_le(lt, x(j), x(j)))", 3, true)
	t.Logf("reads %v", lib.read())
}

// A polynomial in one variable, quantified as the ring tuple of its
// coefficients and evaluated at a scalar binder: the univariate code of
// its block at the binder's slot (polynomial_encoding.
// UnivariateCodeEvaluation), in both theories.
func TestElementarityBridge_UnivariateValue(t *testing.T) {
	lib, res := buildSentenceIn(t, "∀F:field_ops(A). ∀n:num. ∀p:(num → A). ring_tuple(field_ring(F), n, p) ⇒ ∃x:A. x ∈ F.carrier ∧ polynomial_eval(p, x) = F.zero", 2, false)
	require.Contains(t, lib.read(), "polynomial_encoding.UnivariateCodeEvaluation")
	require.Contains(t, ext.PrintTerm(res.Formula), "univariate_code")
	lib, _ = buildSentenceIn(t, "∀F:field_ops(A). ∀lt:(A → A → bool). ∀n:num. ∀a b:A. a ∈ F.carrier ∧ b ∈ F.carrier ⇒ ∀p:(num → A). ring_tuple(field_ring(F), n, p) ⇒ ∃u:A. u ∈ F.carrier ∧ ordered_le(lt, a, u) ∧ ordered_le(lt, u, b) ∧ (∀x:A. x ∈ F.carrier ∧ ordered_le(lt, a, x) ∧ ordered_le(lt, x, b) ⇒ ordered_le(lt, polynomial_eval(p, u), polynomial_eval(p, x)))", 3, true)
	require.Contains(t, lib.read(), "polynomial_encoding.UnivariateCodeEvaluation")
}

// The fixed-parameter form at a polynomial in one variable: the
// property quantifies p as the ring tuple of its coefficients, its
// length the open bound, which .At takes from p's polynomial_over fact
// (polynomial_encoding.TupleOfPolynomial); the source states the
// property over the reals, whose instance the step finds itself.
func TestElementarity_FixedUnivariate(t *testing.T) {
	installBundles()
	const binders = "∀F:field_ops(A). ∀lt:(A → A → bool). ∀n:num. "
	body := "∀p:(num → A). ∀a b:A. ring_tuple(field_ring(F), n, p) ∧ a ∈ F.carrier ∧ b ∈ F.carrier ∧ ordered_le(lt, a, b) ⇒ ∃u:A. u ∈ F.carrier ∧ ordered_le(lt, a, u) ∧ ordered_le(lt, u, b) ∧ (∀x:A. x ∈ F.carrier ∧ ordered_le(lt, a, x) ∧ ordered_le(lt, x, b) ⇒ ordered_le(lt, polynomial_eval(p, u), polynomial_eval(p, x)))"
	property, vars := bridgeSentence(t, binders+body, 3)
	probe := core.NewConstDef(core.Abs(vars[0], core.Abs(vars[1], core.Abs(vars[2], property))), "univariate_minimum_probe")
	lib := newBridgeLibrary(t)
	field := core.MakeConstTerm(lib.Constant("real_field_ops"), lib.Constant("real_field_ops").AbsType())
	order := core.MakeConstTerm(lib.Constant("real_lt"), lib.Constant("real_lt").AbsType())
	var env []core.TypeSubst
	require.True(t, core.MatchTypeInto(vars[0].Type(), field.Type(), utils.FullPredicate, &env))
	m := core.Var("m", ext.NumType)
	source := ext.ForAll(m)(ext.Apply(core.MakeConstTerm(probe.Meta(), probe.Type().Substitute(env...)), field, order, m)).Core()
	lib.extra = map[string]core.Prop{"test.UnivariateMinimumSource": core.NewAxiom(source)}
	lib.extraConstants = map[core.TermName]core.ConstTermMeta{probe.Name(): probe.Meta()}

	const params = binders + "∀p:(num → A). ∀a b:A. "
	sentence := func(text string) core.Term {
		term, _ := bridgeSentence(t, params+text, 6)
		return term
	}
	Φ, pvars := bridgeSentence(t, params+"∃u:A. u ∈ F.carrier ∧ ordered_le(lt, a, u) ∧ ordered_le(lt, u, b) ∧ (∀x:A. x ∈ F.carrier ∧ ordered_le(lt, a, x) ∧ ordered_le(lt, x, b) ⇒ ordered_le(lt, polynomial_eval(p, u), polynomial_eval(p, x)))", 6)
	facts := []core.Prop{
		core.Assume(sentence("real_closed_field(F, lt)")),
		core.Assume(sentence("polynomial_over(F.carrier, p)")),
		core.Assume(sentence("a ∈ F.carrier")),
		core.Assume(sentence("b ∈ F.carrier")),
		core.Assume(sentence("ordered_le(lt, a, b)")),
	}
	call := bridge.Call{Goal: Φ, Facts: facts, Source: bridge.Source{Entry: "test.UnivariateMinimumSource"}, Params: []core.Term{pvars[3], pvars[4], pvars[5]}}
	outcome, err := bridge.Elementarity(call, bridgeVocabulary(t), lib)
	require.NoError(t, err)
	requireOnFacts(t, outcome.Theorem, Φ, facts)
	reads := lib.read()
	for _, lemma := range []string{"polynomial_encoding.TupleOfPolynomial", "polynomial_encoding.UnivariateCodeEvaluation", "polynomial_encoding.UnivariateCodeBelow", "real_closed_instance.RealClosed"} {
		require.Contains(t, reads, lemma)
	}
	call.Facts = []core.Prop{facts[0], facts[2], facts[3], facts[4]}
	_, err = bridge.Elementarity(call, bridgeVocabulary(t), lib)
	require.ErrorContains(t, err, "no fact gives the polynomial in one variable over the carrier")
}

// The ordered entry transfer: the two real-closed showcases, each
// stated at the reals by a corpus entry, carried to a real closed field
// F, lt by real_closed_field_transfer.SentenceTransfer.
func TestElementarity_OrderedFromEntry(t *testing.T) {
	installBundles()
	for _, c := range []struct {
		goal   string
		k      int
		source string
	}{
		{"∀F:field_ops(A). ∀lt:(A → A → bool). ∀n d:num. polynomial_brouwer_property(F, lt, n, d)", 4, "real_polynomial_geometry.BrouwerSource"},
		{"∀F:field_ops(A). ∀lt:(A → A → bool). ∀n s t d:num. lexicographic_minimum_property(F, lt, n, s, t, d)", 6, "real_polynomial_geometry.LexicographicSource"},
	} {
		t.Run(c.source, func(t *testing.T) {
			Φ, _ := bridgeSentence(t, c.goal, c.k)
			closedF, _ := bridgeSentence(t, "∀F:field_ops(A). ∀lt:(A → A → bool). real_closed_field(F, lt)", 2)
			lib := newBridgeLibrary(t)
			call := bridge.Call{
				Goal:   Φ,
				Facts:  []core.Prop{core.Assume(closedF), lib.Theorem("real_closed_instance.RealClosed")},
				Source: bridge.Source{Entry: c.source},
			}
			outcome, err := bridge.Elementarity(call, bridgeVocabulary(t), lib)
			require.NoError(t, err)
			require.Equal(t, bridge.RealClosedTheory, outcome.Theory)
			cert := core.Force(context.Background(), core.AsThm(outcome.Theorem))
			require.True(t, cert.Conclusion().AlphaEquals(Φ), "conclusion %s", ext.PrintTerm(cert.Conclusion()))
			require.Equal(t, 1, cert.NumHyps(), "hypotheses: %s", prop.PrintProp(cert))
			t.Logf("reads %v; arith %d", lib.read(), lib.arith)
		})
	}
}

// The fixed-parameter form .At: PolynomialBrouwer's statement, its one
// family of coordinate polynomials P the parameter, closed by the
// Brouwer property transferred at P's common degree bound.
func TestElementarity_FixedBrouwer(t *testing.T) {
	installBundles()
	const binders = "∀F:field_ops(A). ∀lt:(A → A → bool). ∀n:num. ∀P:(num → (num → num) → A). "
	Φ, vars := bridgeSentence(t, binders+"∃x:(num → A). x ∈ carrier_cube(F, lt, n) ∧ polynomial_map(field_ring(F), n, P, x) = x", 4)
	closedF, _ := bridgeSentence(t, binders+"real_closed_field(F, lt)", 4)
	polynomials, _ := bridgeSentence(t, binders+"∀j:num. j < n ⇒ P(j) ∈ polynomial_algebra(field_ring(F), {i:num | i < n})", 4)
	keepsCube, _ := bridgeSentence(t, binders+"∀x:(num → A). x ∈ carrier_cube(F, lt, n) ⇒ polynomial_map(field_ring(F), n, P, x) ∈ carrier_cube(F, lt, n)", 4)
	lib := newBridgeLibrary(t)
	call := bridge.Call{
		Goal:   Φ,
		Facts:  []core.Prop{core.Assume(closedF), lib.Theorem("real_closed_instance.RealClosed"), core.Assume(polynomials), core.Assume(keepsCube)},
		Source: bridge.Source{Entry: "real_polynomial_geometry.BrouwerSource"},
		Params: []core.Term{vars[3]},
	}
	outcome, err := bridge.Elementarity(call, bridgeVocabulary(t), lib)
	require.NoError(t, err)
	cert := core.Force(context.Background(), core.AsThm(outcome.Theorem))
	require.True(t, cert.Conclusion().AlphaEquals(Φ), "conclusion %s", ext.PrintTerm(cert.Conclusion()))
	require.Equal(t, 3, cert.NumHyps(), "hypotheses: %s", prop.PrintProp(cert))

	// The reals' instance need not be passed: the step reads the entry
	// stating it.
	found := newBridgeLibrary(t)
	call.Facts = []core.Prop{core.Assume(closedF), core.Assume(polynomials), core.Assume(keepsCube)}
	outcome, err = bridge.Elementarity(call, bridgeVocabulary(t), found)
	require.NoError(t, err)
	requireOnFacts(t, outcome.Theorem, Φ, call.Facts)
	require.Contains(t, found.read(), "real_closed_instance.RealClosed")

	call.Facts = []core.Prop{core.Assume(closedF), lib.Theorem("real_closed_instance.RealClosed"), core.Assume(polynomials)}
	_, err = bridge.Elementarity(call, bridgeVocabulary(t), lib)
	require.ErrorContains(t, err, "no fact meets the property's guard")
	call.Facts = []core.Prop{core.Assume(closedF), lib.Theorem("real_closed_instance.RealClosed"), core.Assume(keepsCube)}
	_, err = bridge.Elementarity(call, bridgeVocabulary(t), lib)
	require.ErrorContains(t, err, "membership in the polynomial algebra")
}

// The step's refusals: each names the subterm or the obligation it stops
// at, and no theorem comes back.
func TestElementarity_Refusals(t *testing.T) {
	installBundles()
	const ring = "∀F:field_ops(A). ∀n m d:num. ∀f:((num → num) → A). "
	const ordered = "∀F:field_ops(A). ∀lt:(A → A → bool). ∀n m d:num. ∀f:((num → num) → A). "
	cases := []struct {
		name, goal string
		ordered    bool
		source     string
		params     []int
		want       string
	}{
		{"a function the formulas cannot speak of", ring + "∀a:A. a ∈ F.carrier ⇒ F.inv(a) = a", false, "real_polynomial_geometry.BrouwerSource", nil, "field_inv(F, a)"},
		{"a coordinate past the tuple", ring + "∀x:(num → A). ring_tuple(field_ring(F), n, x) ⇒ x(m) = F.zero", false, "real_polynomial_geometry.BrouwerSource", nil, "index outside the block: a coordinate at an index the arithmetic does not keep below the tuple's length: x(m)"},
		{"a coordinate one past an index below the length", ring + "∀x:(num → A). ring_tuple(field_ring(F), n, x) ⇒ ∀j:num. j < n ⇒ x(j + 1) = F.zero", false, "real_polynomial_geometry.BrouwerSource", nil, "index outside the block: a coordinate at an index the arithmetic does not keep below the tuple's length: x(j + 1)"},
		{"a tuple quantifier guarded on its coordinates alone", ring + "∀x:(num → A). (∀i:num. i < n ⇒ x(i) ∈ F.carrier) ⇒ x = x", false, "real_polynomial_geometry.BrouwerSource", nil, "without a ring_tuple guard"},
		{"a free parameter in sentence mode", ring + "∀x:(num → A). ring_tuple(field_ring(F), n, x) ⇒ polynomial_value(field_ring(F), f, x) = F.zero", false, "real_polynomial_geometry.BrouwerSource", nil, "generalize the statement over a degree bound"},
		{"a source stating another property", ordered + "polynomial_brouwer_property(F, lt, n, d)", true, "real_polynomial_geometry.LexicographicSource", nil, "another property than the goal"},
		{".At with a parameter the property does not quantify", ordered + "∃x:(num → A). x ∈ carrier_cube(F, lt, n) ∧ x = x", true, "real_polynomial_geometry.BrouwerSource", []int{5}, "does not fit the property's binder"},
		{".At with more parameters than the property quantifies", ordered + "∃x:(num → A). x ∈ carrier_cube(F, lt, n) ∧ x = x", true, "real_polynomial_geometry.BrouwerSource", []int{5, 5}, "quantifies 1 binders; .At gives 2"},
	}
	for _, c := range cases {
		t.Run(c.name, func(t *testing.T) {
			k := 5
			structure := "∀F:field_ops(A). algebraically_closed_field_on(F)"
			if c.ordered {
				k = 6
				structure = "∀F:field_ops(A). ∀lt:(A → A → bool). real_closed_field(F, lt)"
			}
			Φ, vars := bridgeSentence(t, c.goal, k)
			closedF, _ := bridgeSentence(t, structure, map[bool]int{false: 1, true: 2}[c.ordered])
			lib := newBridgeLibrary(t)
			call := bridge.Call{
				Goal:   Φ,
				Facts:  []core.Prop{core.Assume(closedF), lib.Theorem("real_closed_instance.RealClosed")},
				Source: bridge.Source{Entry: c.source},
			}
			if c.params != nil {
				call.Params = []core.Term{}
				for _, i := range c.params {
					call.Params = append(call.Params, vars[i])
				}
			}
			outcome, err := bridge.Elementarity(call, bridgeVocabulary(t), lib)
			require.Error(t, err)
			require.Nil(t, outcome.Theorem)
			require.ErrorContains(t, err, c.want)
			t.Logf("%v", err)
		})
	}
}

// A formula with parameters, its bridge at a fresh environment ρ: the
// parameters are binders of the root, each represented in ρ, and the
// bridge holds under those representations and the parameters'
// obligations.
func TestElementarityBridge_Parameters(t *testing.T) {
	installBundles()
	cases := []struct {
		name, text string
		k          int
		params     func(vars []core.VarTerm) []reify.Parameter
		hyps       int
	}{
		{"two families of polynomials, the system of SolutionDescent",
			"∀F:field_ops(A). ∀n r s d:num. ∀P Q:(num → (num → num) → A). ∃x:(num → A). polynomial_system_solution(field_ring(F), n, r, s, P, Q, x)", 7,
			func(v []core.VarTerm) []reify.Parameter {
				return []reify.Parameter{
					{Name: "P", Term: v[5], Kind: reify.FamilyBlock, Dimension: v[1], Degree: v[4], Count: v[2]},
					{Name: "Q", Term: v[6], Kind: reify.FamilyBlock, Dimension: v[1], Degree: v[4], Count: v[3]},
				}
			}, 0},
		{"a scalar and a polynomial",
			"∀F:field_ops(A). ∀n d:num. ∀a:A. ∀p:((num → num) → A). ∀x:(num → A). ring_tuple(field_ring(F), n, x) ⇒ polynomial_value(field_ring(F), p, x) = a", 5,
			func(v []core.VarTerm) []reify.Parameter {
				return []reify.Parameter{
					{Name: "a", Term: v[3], Kind: reify.ScalarBlock},
					{Name: "p", Term: v[4], Kind: reify.PolynomialBlock, Dimension: v[1], Degree: v[2]},
				}
			}, 0},
	}
	for _, c := range cases {
		t.Run(c.name, func(t *testing.T) {
			Φ, vars := bridgeSentence(t, c.text, c.k)
			in := reify.Input{Structure: reify.Structure{Field: vars[0]}, Proposition: Φ, Parameters: c.params(vars), Unfold: bridge.DefinitionUnfolder(), Vocabulary: bridgeVocabulary(t)}
			res, err := reify.Reify(in)
			require.NoError(t, err)
			lib := newBridgeLibrary(t)
			thm, rho := bridge.BuildWithParameters(in, res, lib)
			cert := core.Force(context.Background(), core.AsThm(thm))
			l, r, ok := core.MatchesEQ(cert.Conclusion())
			require.True(t, ok)
			require.True(t, l.AlphaEquals(Φ), "left side %s", ext.PrintTerm(l))
			_, args := ext.MatchesApply(r)
			require.True(t, args[1].AlphaEquals(rho), "right side %s", ext.PrintTerm(r))
			require.True(t, args[2].AlphaEquals(res.Formula), "right side %s", ext.PrintTerm(r))
			for i := range cert.NumHyps() {
				t.Logf("hypothesis %s", ext.PrintTerm(cert.Hyp(i)))
			}
		})
	}
}

// The embedding mode's iff on SolutionDescent's goal: the system over G
// at the images of P and Q, and over F at P and Q, read as one formula,
// joined by EmbeddingElementary at an environment ρ representing P and
// Q, whose image λv. i(ρ(v)) represents theirs.
func TestElementarity_EmbeddingBridge(t *testing.T) {
	installBundles()
	const binders = "∀F:field_ops(A). ∀G:field_ops(B). ∀i:(A → B). ∀n r s d:num. ∀P Q:(num → (num → num) → A). "
	sentence := func(text string) core.Term {
		term, _ := bridgeSentence(t, binders+text, 9)
		return term
	}
	Φ := sentence("(∃y:(num → B). polynomial_system_solution(field_ring(G), n, r, s, λj:num. λm:(num → num). i(P(j, m)), λj:num. λm:(num → num). i(Q(j, m)), y)) ⇔ ∃x:(num → A). polynomial_system_solution(field_ring(F), n, r, s, P, Q, x)")
	facts := []core.Prop{
		core.Assume(sentence("algebraically_closed_field_on(F)")),
		core.Assume(sentence("algebraically_closed_field_on(G)")),
		core.Assume(sentence("ring_homomorphism(field_ring(F), field_ring(G), i)")),
		core.Assume(sentence("∀j:num. j < r ⇒ polynomial_bound(field_ring(F), n, d, P(j))")),
		core.Assume(sentence("∀j:num. j < s ⇒ polynomial_bound(field_ring(F), n, d, Q(j))")),
	}
	lib := newBridgeLibrary(t)
	call := bridge.Call{Goal: Φ, Facts: facts}
	thm, rho, err := bridge.EmbeddingBridge(call, bridgeVocabulary(t), lib)
	require.NoError(t, err)
	cert := core.Force(context.Background(), core.AsThm(thm))
	require.True(t, cert.Conclusion().AlphaEquals(Φ), "conclusion %s", ext.PrintTerm(cert.Conclusion()))
	for i := range cert.NumHyps() {
		h := cert.Hyp(i)
		t.Logf("hypothesis %s", ext.PrintTerm(h))
		if h.HasFree(rho) {
			continue
		}
		known := false
		for _, f := range facts {
			known = known || f.Conclusion().AlphaEquals(h)
		}
		require.True(t, known, "a hypothesis neither a fact nor about ρ: %s", ext.PrintTerm(h))
	}
	t.Logf("reads %v; arith %d", lib.read(), lib.arith)

	outcome, err := bridge.Elementarity(call, bridgeVocabulary(t), lib)
	require.NoError(t, err)
	require.Equal(t, bridge.EmbeddingMode, outcome.Mode)
	closed := core.Force(context.Background(), core.AsThm(outcome.Theorem))
	require.True(t, closed.Conclusion().AlphaEquals(Φ), "conclusion %s", ext.PrintTerm(closed.Conclusion()))
	for i := range closed.NumHyps() {
		known := false
		for _, f := range facts {
			known = known || f.Conclusion().AlphaEquals(closed.Hyp(i))
		}
		require.True(t, known, "a hypothesis that is no fact: %s", ext.PrintTerm(closed.Hyp(i)))
	}
	t.Logf("transfer: %d hypotheses; reads %v", closed.NumHyps(), lib.read())
	call.Facts = []core.Prop{facts[0], facts[1], facts[3], facts[4]}
	_, err = bridge.Elementarity(call, bridgeVocabulary(t), lib)
	require.ErrorContains(t, err, "ring_homomorphism(field_ring(F), field_ring(G), i)")
	call.Facts = []core.Prop{facts[0], facts[1], facts[2], facts[3]}
	_, err = bridge.Elementarity(call, bridgeVocabulary(t), lib)
	require.ErrorContains(t, err, "no fact bounds the parameter Q")
}

// The fixed-parameter form from a family of models by prime: the family
// binds the property's data ahead of the prime, .At settles the
// dimension from the goal and the degree from P's membership facts, and
// the family, instantiated there, transfers the property to F.
func TestElementarity_FixedFromPrimeFamily(t *testing.T) {
	installBundles()
	const binders = "∀F:field_ops(A). ∀n:num. ∀P:(num → (num → num) → A). "
	sentence := func(text string) core.Term {
		term, _ := bridgeSentence(t, binders+text, 3)
		return term
	}
	Φ, vars := bridgeSentence(t, binders+"polynomial_map_surjective(field_ring(F), n, P)", 3)
	models := sentence("∀m d:num. ∀p:num. nat_prime(p) ⇒ ∃G:field_ops(B). algebraically_closed_field_on(G) ∧ field_characteristic(G, p) ∧ ax_property(G, m, d)")
	facts := []core.Prop{
		core.Assume(sentence("algebraically_closed_field_on(F)")),
		core.Assume(sentence("∀j:num. j < n ⇒ P(j) ∈ polynomial_algebra(field_ring(F), {v:num | v < n})")),
		core.Assume(sentence("polynomial_map_injective(field_ring(F), n, P)")),
	}
	lib := newBridgeLibrary(t)
	call := bridge.Call{Goal: Φ, Facts: facts, Source: bridge.Source{Family: core.Assume(models)}, Params: []core.Term{vars[2]}}
	outcome, err := bridge.Elementarity(call, bridgeVocabulary(t), lib)
	require.NoError(t, err)
	require.Equal(t, bridge.EquivalenceMode, outcome.Mode)
	require.Equal(t, bridge.AlgebraicallyClosedTheory, outcome.Theory)
	requireOnFacts(t, outcome.Theorem, Φ, append(facts, core.Assume(models)))
	require.Contains(t, lib.read(), "lefschetz.PrimeFamilyTransfer")
}

// The embedding mode reads a parameter's degree bound off its membership
// in the polynomial algebra, as .At does: CommonDegreeBound gives a
// bound, the call is proved at it, and its ∃ is discharged, so the
// theorem stands on the facts alone.
func TestElementarity_EmbeddingFromMembership(t *testing.T) {
	installBundles()
	const binders = "∀F:field_ops(A). ∀G:field_ops(B). ∀i:(A → B). ∀n r s:num. ∀P Q:(num → (num → num) → A). "
	sentence := func(text string) core.Term {
		term, _ := bridgeSentence(t, binders+text, 8)
		return term
	}
	Φ := sentence("(∃y:(num → B). polynomial_system_solution(field_ring(G), n, r, s, λj:num. λm:(num → num). i(P(j, m)), λj:num. λm:(num → num). i(Q(j, m)), y)) ⇔ ∃x:(num → A). polynomial_system_solution(field_ring(F), n, r, s, P, Q, x)")
	facts := []core.Prop{
		core.Assume(sentence("algebraically_closed_field_on(F)")),
		core.Assume(sentence("algebraically_closed_field_on(G)")),
		core.Assume(sentence("ring_homomorphism(field_ring(F), field_ring(G), i)")),
		core.Assume(sentence("∀j:num. j < r ⇒ P(j) ∈ polynomial_algebra(field_ring(F), {v:num | v < n})")),
		core.Assume(sentence("∀j:num. j < s ⇒ Q(j) ∈ polynomial_algebra(field_ring(F), {v:num | v < n})")),
	}
	lib := newBridgeLibrary(t)
	outcome, err := bridge.Elementarity(bridge.Call{Goal: Φ, Facts: facts}, bridgeVocabulary(t), lib)
	require.NoError(t, err)
	require.Equal(t, bridge.EmbeddingMode, outcome.Mode)
	require.Equal(t, bridge.AlgebraicallyClosedTheory, outcome.Theory)
	requireOnFacts(t, outcome.Theorem, Φ, facts)
	require.Contains(t, lib.read(), "polynomial_encoding.CommonDegreeBound")
}

// The embedding mode in the ordered theory: a homomorphism of real
// closed fields is elementary (real_closed_field_transfer.
// EmbeddingElementary), so a negative value of a polynomial over the
// extension descends, the polynomial's bound read off its membership.
func TestElementarity_OrderedEmbedding(t *testing.T) {
	installBundles()
	const binders = "∀F:field_ops(A). ∀lt:(A → A → bool). ∀G:field_ops(B). ∀ls:(B → B → bool). ∀i:(A → B). ∀n:num. ∀p:((num → num) → A). "
	sentence := func(text string) core.Term {
		term, _ := bridgeSentence(t, binders+text, 7)
		return term
	}
	Φ := sentence("(∃x:(num → A). ring_tuple(field_ring(F), n, x) ∧ lt(polynomial_value(field_ring(F), p, x), F.zero)) ⇔ ∃y:(num → B). ring_tuple(field_ring(G), n, y) ∧ ls(polynomial_value(field_ring(G), λm:(num → num). i(p(m)), y), G.zero)")
	facts := []core.Prop{
		core.Assume(sentence("real_closed_field(F, lt)")),
		core.Assume(sentence("real_closed_field(G, ls)")),
		core.Assume(sentence("ring_homomorphism(field_ring(F), field_ring(G), i)")),
		core.Assume(sentence("p ∈ polynomial_algebra(field_ring(F), {j:num | j < n})")),
	}
	lib := newBridgeLibrary(t)
	call := bridge.Call{Goal: Φ, Facts: facts}
	outcome, err := bridge.Elementarity(call, bridgeVocabulary(t), lib)
	require.NoError(t, err)
	require.Equal(t, bridge.EmbeddingMode, outcome.Mode)
	require.Equal(t, bridge.RealClosedTheory, outcome.Theory)
	requireOnFacts(t, outcome.Theorem, Φ, facts)
	require.Contains(t, lib.read(), "real_closed_field_transfer.EmbeddingElementary")
	// One structure real closed and the other algebraically closed is
	// refused.
	call.Facts = []core.Prop{facts[0], core.Assume(sentence("algebraically_closed_field_on(G)")), facts[2], facts[3]}
	_, err = bridge.Elementarity(call, bridgeVocabulary(t), lib)
	require.ErrorContains(t, err, "the embedding mode reads both in one theory")
}

// requireOnFacts checks thm proves goal from the facts alone.
func requireOnFacts(t *testing.T, thm core.Prop, goal core.Term, facts []core.Prop) {
	t.Helper()
	cert := core.Force(context.Background(), core.AsThm(thm))
	require.True(t, cert.Conclusion().AlphaEquals(goal), "conclusion %s", ext.PrintTerm(cert.Conclusion()))
	for i := range cert.NumHyps() {
		known := false
		for _, f := range facts {
			known = known || f.Conclusion().AlphaEquals(cert.Hyp(i))
		}
		require.True(t, known, "a hypothesis that is no fact: %s", ext.PrintTerm(cert.Hyp(i)))
	}
}

// The fixed-parameter form with several polynomial parameters:
// LexicographicMinimum's statement, the bounds of f, q, g and h pooled
// through PolynomialBoundMono, M the box bound a guard names.
func TestElementarity_FixedLex(t *testing.T) {
	installBundles()
	const binders = "∀F:field_ops(A). ∀lt:(A → A → bool). ∀n s t:num. ∀f q:((num → num) → A). ∀g h:(num → (num → num) → A). ∀M:A. "
	sentence := func(text string) (core.Term, []core.VarTerm) { return bridgeSentence(t, binders+text, 10) }
	Φ, vars := sentence("∃x:(num → A). polynomial_lex_minimizer(F, lt, polynomial_constraint_set(F, lt, n, s, t, g, h), f, q, x)")
	var facts []core.Prop
	for _, h := range []string{
		"real_closed_field(F, lt)",
		"f ∈ polynomial_algebra(field_ring(F), {i:num | i < n})",
		"q ∈ polynomial_algebra(field_ring(F), {i:num | i < n})",
		"∀j:num. j < s ⇒ g(j) ∈ polynomial_algebra(field_ring(F), {i:num | i < n})",
		"∀j:num. j < t ⇒ h(j) ∈ polynomial_algebra(field_ring(F), {i:num | i < n})",
		"polynomial_constraint_set(F, lt, n, s, t, g, h) ≠ ∅",
		"polynomial_box_bound(F, lt, n, polynomial_constraint_set(F, lt, n, s, t, g, h), M)",
	} {
		fact, _ := sentence(h)
		facts = append(facts, core.Assume(fact))
	}
	lib := newBridgeLibrary(t)
	call := bridge.Call{
		Goal:   Φ,
		Facts:  append(facts, lib.Theorem("real_closed_instance.RealClosed")),
		Source: bridge.Source{Entry: "real_polynomial_geometry.LexicographicSource"},
		Params: []core.Term{vars[5], vars[6], vars[7], vars[8], vars[9]},
	}
	outcome, err := bridge.Elementarity(call, bridgeVocabulary(t), lib)
	require.NoError(t, err)
	cert := core.Force(context.Background(), core.AsThm(outcome.Theorem))
	require.True(t, cert.Conclusion().AlphaEquals(Φ), "conclusion %s", ext.PrintTerm(cert.Conclusion()))
	require.Equal(t, len(facts), cert.NumHyps(), "hypotheses: %s", prop.PrintProp(cert))
	require.True(t, slices.Contains(lib.read(), "polynomial_encoding.PolynomialBoundMono"))
}

// A coordinate at a numeral below a numeral length: the univariate
// injective-monotone statement, its points tuples of length 1 compared
// at coordinate 0, builds in the ordered theory.
func TestElementarityBridge_NumeralCoordinate(t *testing.T) {
	buildSentenceIn(t, "∀F:field_ops(A). ∀lt:(A → A → bool). ∀d:num. ∀p:((num → num) → A). polynomial_bound(field_ring(F), 1, d, p) ∧ (∀x:(num → A). ring_tuple(field_ring(F), 1, x) ⇒ ∀y:(num → A). ring_tuple(field_ring(F), 1, y) ⇒ polynomial_value(field_ring(F), p, x) = polynomial_value(field_ring(F), p, y) ⇒ x = y) ⇒ (∀x:(num → A). ring_tuple(field_ring(F), 1, x) ⇒ ∀y:(num → A). ring_tuple(field_ring(F), 1, y) ⇒ lt(x(0), y(0)) ⇒ lt(polynomial_value(field_ring(F), p, x), polynomial_value(field_ring(F), p, y))) ∨ (∀x:(num → A). ring_tuple(field_ring(F), 1, x) ⇒ ∀y:(num → A). ring_tuple(field_ring(F), 1, y) ⇒ lt(x(0), y(0)) ⇒ lt(polynomial_value(field_ring(F), p, y), polynomial_value(field_ring(F), p, x)))", 3, true)
}
