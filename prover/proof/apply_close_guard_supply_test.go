// apply_close_guard_supply_test.go — the apply rung supplies a cited
// law's guard from what the context holds in shapes other than the
// guard as written:
//
//  1. A CONJUNCT OF AN ⇔'S SIDE: `x ∈ F ⇔ P(x) ∧ K(x)` with `a ∈ F`
//     held closes `P(a)` and `K(a)` — the conjuncts a split goal asks —
//     on either side of the ⇔, at any conjunct, through the membership
//     reading of a side too.
//  2. A BINDER PINNED PAST THE FIRST MATCHING GUARD: a binder only the
//     antecedents pin is pinned again where the first hypothesis a
//     guard meets is not the one the other antecedents say, within
//     pinningBound pinnings.
//  3. A GROUNDED LAW IN ITS CLAUSE FORM: a witnessed premise whose
//     stated guards the leaf does not supply by assumption installs its
//     clause form, and its stated form at the tuple is still the rung's
//     head.
//  4. THROUGH AN INCLUSION, with SubsetDef named: `x ∈ S` from `x ∈ t`
//     and `t ⊆ S`, at a set variable or a union alike — one apply, so
//     it counts against the rung's depth like any other.
//
// The By cases run live and then strict from an EMPTY store: keyless,
// or they fail. The declines are read off the rung directly.
package proof

import (
	"strings"
	"sync"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/ext/unify"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

var (
	guardSupplyOnce  sync.Once
	guardSupplyMetas map[string]core.ConstTermMeta
)

// guardSupplyVocabulary is the set-builder vocabulary, `subset` and
// `union` minted with their definitions as set_basic spells them, and
// opaque constants for the laws' own symbols (a law's normalized
// install closes over its free variables, so its symbols are constants).
func guardSupplyVocabulary() map[string]core.ConstTermMeta {
	guardSupplyOnce.Do(func() {
		metas := map[string]core.ConstTermMeta{}
		for name, m := range setBuilderVocabulary() {
			metas[name] = m
		}
		A := core.TypeA()
		set := core.MakeFun(A, core.TypeBool())
		member := ext.WrapTerm(core.MakeConstTerm(metas["set_member"], core.MakeFun(A, set, core.TypeBool())))
		x, s, u := ext.Var("x", A), ext.Var("s", set), ext.Var("t", set)
		subset := core.NewConstDef(s.To(u.To(ext.ForAll(x)(member.Apply(x, s).Imply(member.Apply(x, u))))).Core(), "subset")
		union := core.NewConstDef(s.To(u.To(x.To(member.Apply(x, s).Or(member.Apply(x, u))))).Core(), "union")
		metas["subset"], metas["union"] = subset.Meta(), union.Meta()

		num := ext.NumType
		nset := core.MakeFun(num, core.TypeBool())
		rel := core.MakeFun(num, num, core.TypeBool())
		for name, ty := range map[string]core.HolType{
			"zz_gs_smul":     core.MakeFun(num, num, num),
			"zz_gs_insert":   core.MakeFun(num, nset, nset),
			"zz_gs_sum":      core.MakeFun(nset, core.MakeFun(num, num), num),
			"zz_gs_add":      core.MakeFun(num, num, num),
			"zz_gs_finite":   core.MakeFun(nset, core.TypeBool()),
			"zz_gs_basis":    core.MakeFun(nset, core.TypeBool()),
			"zz_gs_card":     core.MakeFun(nset, num),
			"zz_gs_dim":      num,
			"zz_gs_has_size": core.MakeFun(nset, num, core.TypeBool()),
			"zz_gs_sub":      core.MakeFun(nset, core.TypeBool()),
			"zz_gs_bas":      core.MakeFun(nset, nset, nset, core.TypeBool()),
			"zz_gs_prod":     core.MakeFun(nset, nset, nset),
			"zz_gs_class":    core.MakeFun(rel, num, nset),
			"zz_gs_rel_on":   core.MakeFun(nset, rel, rel),
			"zz_gs_ok":       core.MakeFun(num, core.TypeBool()),
			"zz_gs_good":     core.MakeFun(num, core.TypeBool()),
		} {
			metas[name] = core.MakeConstMeta(core.TermName(name), ty)
		}
		guardSupplyMetas = metas
	})
	return guardSupplyMetas
}

func guardSupplyScope() *dsl.ParseScope {
	num := ext.NumType
	nset := core.MakeFun(num, core.TypeBool())
	family := core.MakeFun(nset, core.TypeBool())
	predicate := core.MakeFun(nset, core.TypeBool())
	return &dsl.ParseScope{
		Vars: map[string]core.HolType{
			"G": family, "F": family, "s": nset, "t": nset, "S": nset, "s1": nset, "s2": nset,
			"C": nset, "k": nset, "P": nset,
			"K0": nset, "M0": nset, "N0": nset, "B0": nset, "C0": nset,
			"Q": predicate, "W": predicate, "V": predicate,
			"phi": core.MakeFun(num, num), "g": core.MakeFun(num, num),
			"Rr": core.MakeFun(num, num, core.TypeBool()),
			"x":  num, "r": num, "a": num, "n": num, "M": num, "N": num,
		},
		ConstMetas: guardSupplyVocabulary(),
	}
}

func parseGuardSupply(t *testing.T, text string) core.Term {
	t.Helper()
	res := dsl.ParsePropTextInScope(text, guardSupplyScope())
	require.Empty(t, res.Errors, "%s: %v", text, res.Errors)
	return res.Prop.Conclusion()
}

// gsPremise is one premise of a case: a resident hypothesis by index,
// or a law by its closed statement, each grounded at the terms in at.
type gsPremise struct {
	hyp int
	law string
	at  []string
}

func residentAt(hyp int, at ...string) gsPremise { return gsPremise{hyp: hyp, at: at} }
func lawAt(law string, at ...string) gsPremise   { return gsPremise{hyp: -1, law: law, at: at} }

// guardSupplyOutcome is what one case did: whether the live By closed,
// the certificates and plans it recorded, and whether the strict replay
// from an empty store closed.
type guardSupplyOutcome struct {
	live, strict  bool
	keys, plans   int
	liveFailure   string
	strictFailure string
}

func runGuardSupply(t *testing.T, hyps []string, goal string, premises ...gsPremise) guardSupplyOutcome {
	t.Helper()
	scope := guardSupplyScope()
	term := func(text string) core.Term {
		t.Helper()
		res := dsl.ParseTermTextInScope(text, nil, scope, nil)
		require.Empty(t, res.Errors, "%s: %v", text, res.Errors)
		return res.Term
	}
	hypTerms := make([]core.Term, len(hyps))
	for i, h := range hyps {
		hypTerms[i] = parseGuardSupply(t, h)
	}
	// MakeProp orders its hypotheses in place: a copy keeps the indices.
	sequent := prop.MakeProp(parseGuardSupply(t, goal), append([]core.Term{}, hypTerms...)...)
	spec := BySpec{}
	for _, p := range premises {
		var ws []core.Term
		for _, w := range p.at {
			ws = append(ws, term(w))
		}
		if p.hyp >= 0 {
			spec.Premises = append(spec.Premises, ByPremiseSpec{Install: prop.MakeProp(hypTerms[p.hyp]), Resident: true,
				Witnesses: ws, Describe: hyps[p.hyp]})
			continue
		}
		spec.Premises = append(spec.Premises, ByPremiseSpec{Install: prop.MakeProp(parseGuardSupply(t, p.law)),
			Witnesses: ws, Describe: p.law})
	}
	run := func(env *ProverEnv) (closed bool, failure string) {
		defer func() {
			if r := recover(); r != nil {
				closed, failure = false, clipRunes(strings.TrimSpace(sprintAny(r)), 600)
			}
		}()
		// A cited law leaves its claim obligation open for the caller.
		return ApplyByStep(CreateGoalStack(sequent), env, t.Context(), spec), ""
	}
	wire := func(env *ProverEnv) {
		for _, m := range guardSupplyVocabulary() {
			env.ProofService.LoadOrStoreConstMeta(m)
		}
	}
	var out guardSupplyOutcome
	live := groundTestEnv(t)
	wire(live)
	st := newGroundByStore()
	st.wire(live, true)
	out.live, out.liveFailure = run(live)
	out.keys, out.plans = len(st.Proofs()), len(st.Plans())

	strict := groundTestEnv(t)
	wire(strict)
	newGroundByStore().wire(strict, true)
	strict.RequireCNFCacheHit = true
	out.strict, out.strictFailure = run(strict)
	return out
}

func requireKeyless(t *testing.T, what string, out guardSupplyOutcome) {
	t.Helper()
	assert.True(t, out.live, "%s: the live By closes: %s", what, out.liveFailure)
	assert.Zero(t, out.keys, "%s: keyless — no refutation", what)
	assert.Zero(t, out.plans, "%s: and no plan row", what)
	assert.True(t, out.strict, "%s: strict replay from an EMPTY store closes: %s", what, out.strictFailure)
}

// rungCloses runs the rung alone on the leaf, the laws its stated heads.
func rungCloses(t *testing.T, goal string, hyps []string, laws ...string) bool {
	t.Helper()
	var hs []core.Term
	for _, h := range hyps {
		hs = append(hs, parseGuardSupply(t, h))
	}
	var heads []applyHead
	for _, l := range laws {
		heads = append(heads, applyHead{stated: prop.MakeProp(parseGuardSupply(t, l)), describe: l})
	}
	var claims []*GoalStackNode
	closed, _ := applyClose(CreateGoalStack(prop.MakeProp(parseGuardSupply(t, goal), hs...)), &claims, heads,
		rungOpts{depth: antecedentApplies})
	return closed
}

const subsetDef = "∀s t:(A → bool). s ⊆ t ⇔ (∀x:A. x ∈ s ⇒ x ∈ t)"

// A member s of a subfamily G of F is a member of F, whose membership
// is an ⇔ fact (order.HausdorffMaximality's chains above c): the goal
// is split into its conjuncts, each one conjunct of the ⇔'s side, and
// `s ∈ F` comes through the inclusion.
//
//	G ⊆ F,  s ∈ G,  ∀d. d ∈ F ⇔ Q(d) ∧ W(d)  ⊢  Q(s) ∧ W(s)
func TestApplyClose_ConjunctOfAnIffSide_Subfamily(t *testing.T) {
	hyps := []string{"G ⊆ F", "s ∈ G", "∀d:set(num). d ∈ F ⇔ Q(d) ∧ W(d)"}
	goal := "Q(s) ∧ W(s)"
	requireKeyless(t, "the ⇔ fact at s, SubsetDef bare",
		runGuardSupply(t, hyps, goal, residentAt(0), residentAt(1), residentAt(2, "s"), lawAt(subsetDef)))
	requireKeyless(t, "the ⇔ fact at s, SubsetDef at (G, F)",
		runGuardSupply(t, hyps, goal, residentAt(0), residentAt(1), residentAt(2, "s"), lawAt(subsetDef, "G", "F")))
	requireKeyless(t, "the ⇔ fact bare",
		runGuardSupply(t, hyps, goal, residentAt(0), residentAt(1), residentAt(2), lawAt(subsetDef)))
}

// Every direction the reading can be asked in: the conjunction on the
// ⇔'s left, a middle conjunct, a side that is a membership in a
// set-builder whose condition is the conjunction, and — the reading
// into the membership, which the rung already made — the membership
// from its conjuncts.
func TestApplyClose_ConjunctOfAnIffSide_EveryDirection(t *testing.T) {
	requireKeyless(t, "the conjunction on the left",
		runGuardSupply(t, []string{"s ∈ F", "∀d:set(num). Q(d) ∧ W(d) ⇔ d ∈ F"}, "W(s)", residentAt(0), residentAt(1)))
	requireKeyless(t, "a middle conjunct",
		runGuardSupply(t, []string{"s ∈ F", "∀d:set(num). d ∈ F ⇔ Q(d) ∧ W(d) ∧ V(d)"}, "W(s)", residentAt(0), residentAt(1)))
	requireKeyless(t, "a set-builder side",
		runGuardSupply(t, []string{"s ∈ F", "∀d:set(num). d ∈ F ⇔ d ∈ {e:set(num) | Q(e) ∧ W(e)}"}, "W(s)",
			residentAt(0), residentAt(1)))
	requireKeyless(t, "a ground ⇔",
		runGuardSupply(t, []string{"s ∈ F", "s ∈ F ⇔ Q(s) ∧ W(s)"}, "Q(s)", residentAt(0), residentAt(1)))
	requireKeyless(t, "into the membership",
		runGuardSupply(t, []string{"Q(s)", "W(s)", "∀d:set(num). d ∈ F ⇔ Q(d) ∧ W(d)"}, "s ∈ F",
			residentAt(0), residentAt(1), residentAt(2)))
	assert.False(t, rungCloses(t, "Q(s)", []string{"∀d:set(num). d ∈ F ⇔ Q(d) ∧ W(d)"}),
		"the other side not held: nothing to read the conjunct off")
}

// A law's antecedent `finite(P) ∧ basis(P)`, the finiteness one
// conjunct of a resident ⇔'s side whose other side is held — a set's
// size read through has_size (field_extension.TowerLaw's finite
// basis) — or of a resident conjunction.
//
//	has_size(P, n) ⇔ finite(P) ∧ card(P) = n,  has_size(P, n),  basis(P)  ⊢  dim = card(P)
func TestApplyClose_ConjunctOfAnIffSide_Antecedent(t *testing.T) {
	dimBasis := "∀S:set(num). zz_gs_finite(S) ∧ zz_gs_basis(S) ⇒ zz_gs_dim = zz_gs_card(S)"
	goal := "zz_gs_dim = zz_gs_card(P)"
	iff := []string{"zz_gs_has_size(P, n) ⇔ zz_gs_finite(P) ∧ zz_gs_card(P) = n", "zz_gs_has_size(P, n)", "zz_gs_basis(P)"}
	requireKeyless(t, "a conjunct of a resident ⇔'s side",
		runGuardSupply(t, iff, goal, residentAt(0), residentAt(1), residentAt(2), lawAt(dimBasis)))
	conj := []string{"zz_gs_finite(P) ∧ zz_gs_card(P) = n", "zz_gs_basis(P)"}
	requireKeyless(t, "a conjunct of a resident conjunction",
		runGuardSupply(t, conj, goal, residentAt(0), residentAt(1), lawAt(dimBasis)))
}

// A law whose middle binder M only its guards pin
// (field_extension.TowerBasis): the first guard that mentions M,
// `sub(M)`, meets every subfield in sight.
//
//	sub(K₀) ∧ sub(M₀) ∧ sub(N₀) ∧ K₀ ⊆ M₀ ∧ M₀ ⊆ N₀,  bas(K₀, M₀, B₀),  bas(M₀, N₀, C₀)  ⊢  bas(K₀, N₀, prod(B₀, C₀))
func TestApplyClose_BinderPinnedPastTheFirstMatchingGuard(t *testing.T) {
	towerBasis := "∀K M N B C:set(num). zz_gs_sub(K) ∧ zz_gs_sub(M) ∧ zz_gs_sub(N) ∧ K ⊆ M ∧ M ⊆ N ∧ " +
		"zz_gs_bas(K, M, B) ∧ zz_gs_bas(M, N, C) ⇒ zz_gs_bas(K, N, zz_gs_prod(B, C))"
	hyps := []string{"zz_gs_sub(K0) ∧ zz_gs_sub(M0) ∧ zz_gs_sub(N0) ∧ K0 ⊆ M0 ∧ M0 ⊆ N0",
		"zz_gs_bas(K0, M0, B0)", "zz_gs_bas(M0, N0, C0)"}
	goal := "zz_gs_bas(K0, N0, zz_gs_prod(B0, C0))"
	requireKeyless(t, "grounded",
		runGuardSupply(t, hyps, goal, residentAt(0), residentAt(1), residentAt(2), lawAt(towerBasis, "K0", "M0", "N0", "B0", "C0")))
	requireKeyless(t, "bare", runGuardSupply(t, hyps, goal, residentAt(0), residentAt(1), residentAt(2), lawAt(towerBasis)))
}

// The pinnings a plan is tried at: pinFrom's own first — every piece
// in stated order at its first consistent hypothesis — then, where a
// piece met more than one, the others, the piece with the fewest
// extensions taken first, pinningBound in all.

// The pinnings a plan is tried at: pinFrom's own first — every piece
// in stated order at its first consistent hypothesis — then, where a
// piece met more than one, the others, the piece with the fewest
// extensions taken first, pinningBound in all.
func TestPinAlternatives_FirstMatchThenTheRestBounded(t *testing.T) {
	law := parseGuardSupply(t, "∀M:set(num). zz_gs_sub(M) ∧ M ⊆ N0 ⇒ zz_gs_bas(K0, N0, M)")
	subfields := []string{"K0", "M0", "B0", "C0", "S", "P"}
	var hyps []core.Term
	for _, f := range subfields {
		hyps = append(hyps, parseGuardSupply(t, "zz_gs_sub("+f+")"))
	}
	hyps = append(hyps, parseGuardSupply(t, "P ⊆ N0"))
	goal := prop.MakeProp(parseGuardSupply(t, "zz_gs_bas(K0, N0, M0)"), hyps...)
	plans, miss := matchHeadAll(readerOf(nil), goal, law, "law", nil)
	require.NotEmpty(t, plans, miss)
	plan := plans[0]
	delete(plan.bindings, plan.binders[0].Name())
	extensionsOf := func(piece core.Term, from unify.MatchBindings) []unify.MatchBindings {
		var out []unify.MatchBindings
		for i := range goal.NumHyps() {
			trial := copyBindings(from)
			if unify.TermMatchApproxWith(piece, goal.Hyp(i), plan.slots, trial) {
				out = append(out, trial)
			}
		}
		return out
	}
	alternatives := plan.pinAlternatives(extensionsOf)
	require.Len(t, alternatives, 2, "pinFrom's pinning, then the one `M ⊆ N₀` says")
	first := extensionsOf(conjuncts(plan.antes[0])[0], plan.bindings)[0]
	assert.True(t, alternatives[0][plan.binders[0].Name()].AlphaEquals(first[plan.binders[0].Name()]),
		"the first pinning is pinFrom's")
	assert.Equal(t, "P", ext.PrintTerm(alternatives[1][plan.binders[0].Name()]))

	// Six subfields and nothing else to say which: the search stops at
	// the bound.
	goal = prop.MakeProp(goal.Conclusion(), hyps[:len(subfields)]...)
	looser := parseGuardSupply(t, "∀M:set(num). zz_gs_sub(M) ⇒ zz_gs_bas(K0, N0, M)")
	plans, miss = matchHeadAll(readerOf(nil), goal, looser, "law", nil)
	require.NotEmpty(t, plans, miss)
	plan = plans[0]
	delete(plan.bindings, plan.binders[0].Name())
	assert.Len(t, plan.pinAlternatives(extensionsOf), pinningBound)
}

// A grounded law's guard read as one conjunct of a resident
// conjunction, at either position (the class of a point of a closed
// set, curve_degree.PairClassEqIff and its two siblings): the
// closure guard's own binder u is pinned past `M ∈ P`, the first
// membership it meets, at N.
//
//	∀u v. u ∈ P ∧ R(u, v) ⇒ v ∈ P,  M ∈ P ∧ N ∈ P  ⊢  class(rel_on(P, R), N) = class(R, N)
func TestApplyClose_GuardFromEitherConjunctOfAResidentConjunction(t *testing.T) {
	classOnClosed := "∀c:set(num). ∀R:(num → num → bool). ∀x:num. x ∈ c ∧ (∀y:num. R(x, y) ⇒ y ∈ c) ⇒ " +
		"zz_gs_class(zz_gs_rel_on(c, R), x) = zz_gs_class(R, x)"
	hyps := []string{"∀u v:num. u ∈ P ∧ Rr(u, v) ⇒ v ∈ P", "M ∈ P ∧ N ∈ P"}
	for _, point := range []string{"M", "N"} {
		goal := "zz_gs_class(zz_gs_rel_on(P, Rr), " + point + ") = zz_gs_class(Rr, " + point + ")"
		requireKeyless(t, "grounded at "+point,
			runGuardSupply(t, hyps, goal, residentAt(0), residentAt(1), lawAt(classOnClosed, "P", "Rr", point)))
		requireKeyless(t, "bare at "+point, runGuardSupply(t, hyps, goal, residentAt(0), residentAt(1), lawAt(classOnClosed)))
	}
}

// A sum law's guard is a ∀-membership over insert(a, t); the context
// holds the map's membership over C and insert(a, t) ⊆ C
// (linear_independence.IndependentInsertIff). Grounded at a tuple
// whose stated guards the leaf does not supply by assumption, the law
// installs its clause form, and its stated form at the tuple is the
// rung's head as the bare law's is.
//
//	∀z. z ∈ C ⇒ g(z) ∈ C,  insert(a, t) ⊆ C,  a ∈ C  ⊢  sum(insert(a, t), g) = add(g(a), sum(t, g))
func TestApplyClose_GroundedLawInItsClauseForm(t *testing.T) {
	insertSum := "∀c:set(num). ∀a:num. ∀t:set(num). ∀f:(num → num). (∀y:num. y ∈ zz_gs_insert(a, t) ⇒ f(y) ∈ c) ∧ a ∈ c ⇒ " +
		"zz_gs_sum(zz_gs_insert(a, t), f) = zz_gs_add(f(a), zz_gs_sum(t, f))"
	hyps := []string{"∀z:num. z ∈ C ⇒ g(z) ∈ C", "zz_gs_insert(a, t) ⊆ C", "a ∈ C"}
	goal := "zz_gs_sum(zz_gs_insert(a, t), g) = zz_gs_add(g(a), zz_gs_sum(t, g))"
	residents := []gsPremise{residentAt(0), residentAt(1), residentAt(2)}
	with := func(law gsPremise) []gsPremise {
		return append(append([]gsPremise{}, residents...), law, lawAt(subsetDef))
	}
	requireKeyless(t, "bare", runGuardSupply(t, hyps, goal, with(lawAt(insertSum))...))
	requireKeyless(t, "at a partial tuple", runGuardSupply(t, hyps, goal, with(lawAt(insertSum, "C"))...))
	requireKeyless(t, "at its full tuple", runGuardSupply(t, hyps, goal, with(lawAt(insertSum, "C", "a", "t", "g"))...))
	requireKeyless(t, "at a λ for the map",
		runGuardSupply(t, hyps, "zz_gs_sum(zz_gs_insert(a, t), λz:num. g(z)) = zz_gs_add(g(a), zz_gs_sum(t, λz:num. g(z)))",
			with(lawAt(insertSum, "C"))...))
}

// A law's guard `phi(x) ∈ C` is the conclusion of a resident
// ∀-membership over S, whose own guard `x ∈ S` the context holds
// through an inclusion (free_module.FreeLiftHom's scalings): at a set
// variable and at a union alike, with SubsetDef named. The rung reads
// no definition: unnamed, the inclusion is an atom. And the hop is an
// apply like any other: past a ∀-membership whose apply spends the
// depth, it is a third, and the rung declines.
//
//	x ∈ s₁ ∪ s₂,  s₁ ∪ s₂ ⊆ S,  ∀y. y ∈ S ⇒ phi(y) ∈ C,  r ∈ k  ⊢  smul(r, phi(x)) ∈ C
func TestApplyClose_GuardThroughAResidentInclusion(t *testing.T) {
	smulIn := "∀c k:set(num). ∀r y:num. r ∈ k ∧ y ∈ c ⇒ zz_gs_smul(r, y) ∈ c"
	goal := "zz_gs_smul(r, phi(x)) ∈ C"
	union := []string{"x ∈ s1 ∪ s2", "s1 ∪ s2 ⊆ S", "∀y:num. y ∈ S ⇒ phi(y) ∈ C", "r ∈ k"}
	variable := []string{"x ∈ t", "t ⊆ S", "∀y:num. y ∈ S ⇒ phi(y) ∈ C", "r ∈ k"}
	premises := []gsPremise{residentAt(0), residentAt(1), residentAt(2), residentAt(3), lawAt(smulIn), lawAt(subsetDef)}
	requireKeyless(t, "a set variable", runGuardSupply(t, variable, goal, premises...))
	requireKeyless(t, "a union", runGuardSupply(t, union, goal, premises...))
	assert.False(t, rungCloses(t, goal, union, smulIn), "SubsetDef unnamed: the inclusion is an atom")

	past := []string{"x ∈ t", "t ⊆ S", "∀y:num. y ∈ S ⇒ zz_gs_ok(y)"}
	assert.False(t, rungCloses(t, "zz_gs_good(x)", past, "∀y:num. zz_gs_ok(y) ⇒ zz_gs_good(y)", subsetDef),
		"law, ∀-membership, inclusion: three applies")
	assert.True(t, rungCloses(t, "zz_gs_ok(x)", past, subsetDef), "the ∀-membership and the inclusion: two")
}
