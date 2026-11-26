// calc_scoped_close_test.go — the chain-fold's premise-scoped close
// (_CalcChainClose, calc.go).
//
// The chained fact of a relation chain is a three-step resolution: the
// two links plus the grounded transitivity instance entail it. Before
// the scoped close the fold refuted it over the WHOLE ambient context,
// and an analysis context — a dozen resident hyps, a ∀∃ coverage fact,
// a set-builder membership — ran that refute to its budget and failed
// (measured twice on iterate/real/real_sum's Covered). These cases pin the
// fixed behaviour against a synthetic POISON the ambient refute fails
// on (measured with the scoped close reverted — see poisonBudget).

package proof

import (
	"fmt"
	"strings"
	"testing"
	"time"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/stretchr/testify/require"
)

// calcScopedEnv: an uninterpreted relation R over ind with its
// transitivity as an axiom, a second relation S with S ⇒ R (CalcOrder's
// defined ≈ and its lift), and the POISON — the resident facts an
// analysis context carries: a coverage-shaped ∀∃ (Skolem function), a
// Q-to-P chain that re-feeds it, Q's transitivity and symmetry, one
// ground seed P(x), and a finite COVER `∀u. P u ⇒ ⋁ᵢ (Q u cᵢ ∧ P cᵢ)`
// of coverCells cells — the Covered-lemma shape, whose CNF is 2ⁿ
// clauses. Every link of every chain is a conjunct of one resident
// `givens` hypothesis, so a leg closes by By(ResidentHyp(givens)) —
// scoped, instant, and never α-equal to the link it proves (AssertStep
// refuses a resident claim).
type calcScopedEnv struct {
	env        *ProverEnv
	ctx        *Script
	R, S, Q    *ext.TermWrapper // ind → ind → bool
	P          *ext.TermWrapper // ind → bool
	x, y, z, w *ext.TermWrapper
	trans      core.ThmCert // ∀a b c. R a b ∧ R b c ⇒ R a c
	sToR       core.ThmCert // ∀a b.   S a b ⇒ R a b
	poison     []Term
}

func makeCalcScopedEnv(t *testing.T, budget time.Duration) *calcScopedEnv {
	t.Helper()
	env := makeStepTestEnv()
	env.CnfRefuterTimeout = budget
	ctx := NewScript(env)
	predTy := MakeFun(TypeInd, TypeBool)
	relTy := MakeFun(TypeInd, predTy)
	for _, c := range []struct {
		name string
		ty   core.HolType
	}{{"calcScopedR", relTy}, {"calcScopedS", relTy}, {"calcScopedQ", relTy}, {"calcScopedP", predTy}} {
		env.ProofService.LoadOrStoreConstMeta(core.MakeConstMeta(c.name, c.ty))
	}
	e := &calcScopedEnv{
		env: env, ctx: ctx,
		R: ctx.Const("calcScopedR", relTy),
		S: ctx.Const("calcScopedS", relTy),
		Q: ctx.Const("calcScopedQ", relTy),
		P: ctx.Const("calcScopedP", predTy),
		x: Var("x", TypeInd), y: Var("y", TypeInd), z: Var("z", TypeInd), w: Var("w", TypeInd),
	}
	a, b, c := Var("a", TypeInd), Var("b", TypeInd), Var("c", TypeInd)
	e.trans = core.NewAxiom(ForAll(a)(ForAll(b)(ForAll(c)(
		e.R.Apply(a, b).And(e.R.Apply(b, c)).Imply(e.R.Apply(a, c))))))
	e.sToR = core.NewAxiom(ForAll(a)(ForAll(b)(e.S.Apply(a, b).Imply(e.R.Apply(a, b)))))

	u, v, k := Var("u", TypeInd), Var("v", TypeInd), Var("k", TypeInd)
	var cover *ext.TermWrapper
	for i := 0; i < coverCells; i++ {
		ci := Var(TermName(fmt.Sprintf("c%d", i)), TypeInd)
		cell := e.Q.Apply(u, ci).And(e.P.Apply(ci))
		if cover == nil {
			cover = cell
		} else {
			cover = cover.Or(cell)
		}
	}
	e.poison = []Term{
		ForAll(u)(e.P.Apply(u).Imply(Exists(v)(e.Q.Apply(u, v)))),                                    // coverage: ∀u. P u ⇒ ∃v. Q u v
		ForAll(u)(ForAll(v)(e.Q.Apply(u, v).Imply(e.P.Apply(v)))),                                    // ∀u v. Q u v ⇒ P v
		ForAll(u)(ForAll(v)(ForAll(k)(e.Q.Apply(u, v).And(e.Q.Apply(v, k)).Imply(e.Q.Apply(u, k))))), // Q transitive
		ForAll(u)(ForAll(v)(e.Q.Apply(u, v).Imply(e.Q.Apply(v, u)))),                                 // Q symmetric
		e.P.Apply(e.x),                       // the seed
		ForAll(u)(e.P.Apply(u).Imply(cover)), // the finite cover
	}
	return e
}

// coverCells is the finite cover's width. The ambient chain-fold refute
// (scoped close reverted) FAILS from 7 cells on — the cover's CNF
// distribution exceeds the clause layer's _CNF_SIZE_THRES (64), the
// hypothesis never normalizes, and the refute returns nil in ~40–150 ms
// at any budget; at 6 cells it still closes, in ~110 ms. Twelve cells
// puts the fixture well past the cliff.
const coverCells = 12

// section opens ⊢ goal with the poison and `givens` resident.
func (e *calcScopedEnv) section(goal Term, givens Term) *GoalStackNode {
	hyps := append([]Term{givens}, e.poison...)
	return e.ctx.Section(MakeProp(goal, hyps...))
}

func (e *calcScopedEnv) kit() CalcRel {
	return CalcRel{
		Rel:   func(a, b Term) Prop { return MakeProp(e.R.Apply(a, b)) },
		Trans: MakeFact(e.trans),
	}
}

func (e *calcScopedEnv) orderKit() CalcOrder {
	return CalcOrder{
		Le:      func(a, b Term) Prop { return MakeProp(e.R.Apply(a, b)) },
		Eq:      func(a, b Term) Prop { return MakeProp(e.S.Apply(a, b)) },
		LeTrans: MakeFact(e.trans),
		EqToLe:  MakeFact(e.sToR),
	}
}

// fromGivens proves a link from the resident givens conjunction —
// scoped, so the poison never reaches the leg's refute.
func fromGivens(givens Term) Action { return By(ResidentHyp(givens)) }

// calcTreeCensus walks a section tree: the recorded ministep count and
// the closers among them. A By composite's private tree is NOT part of
// the section tree, so a clear or refute it runs internally is
// invisible here — exactly the "inside the close" property under test.
type calcTreeCensus struct {
	steps, by, clearHyps, cnfRefute int
	preorder                        []string
}

func censusCalcTree(root *GoalStackNode) (c calcTreeCensus) {
	var walk func(n *GoalStackNode)
	walk = func(n *GoalStackNode) {
		if n.miniStep != nil {
			c.steps++
			c.preorder = append(c.preorder, n.StepDescription())
			switch n.miniStep.(type) {
			case _ByStep:
				c.by++
			case _ClearHypsStep:
				c.clearHyps++
			case _CNFRefute:
				c.cnfRefute++
			}
		}
		for _, ch := range n.children {
			walk(ch)
		}
	}
	walk(root)
	return
}

// poisonBudget is the refuter budget the chains run under. Measured
// with the scoped close reverted (the fork-point calc.go): the fold's
// CnfRefute over the poisoned context FAILS at this budget and at 2 s
// alike — not a cut-off but a refusal, the cover hypothesis's CNF is
// past the clause layer's size threshold, so the ambient refuter never
// gets a clause set (a leaf that is a three-step resolution, failed).
// The wide ∀∃ and ∀-facts alone did NOT defeat the ambient refute
// (closed in ~20–40 ms at every Herbrand-front width tried): the
// refutation lies in the initial all-pairs round, and the clause
// whistle cuts Skolem-term growth. With the scoped close, every chain
// here closes in 30–60 ms — the poison never reaches a refute.
const poisonBudget = 300 * time.Millisecond

// (a) POISON — a two-leg CalcRel chain closes its chained fact under a
// small budget inside a context whose ambient refute fails.
func TestCalcChainClose_ScopedUnderPoison(t *testing.T) {
	e := makeCalcScopedEnv(t, poisonBudget)
	givens := e.R.Apply(e.x, e.y).And(e.R.Apply(e.y, e.z)).Core()
	// Terminal chain: the chained fact R(x,z) IS the goal, so the fold's
	// close runs against the goal leaf — poison and all.
	root := e.section(e.R.Apply(e.x, e.z).Core(), givens)
	started := time.Now()
	e.kit().Calc(e.x,
		Leg(e.y, "x R y — a given", fromGivens(givens)),
		Leg(e.z, "y R z — a given", fromGivens(givens)),
	).applyAction(e.ctx, root)
	elapsed := time.Since(started)
	require.True(t, root.Proved(), "the chain must close the section")
	require.Less(t, elapsed, poisonBudget,
		"the scoped close must not be paying the ambient refute's budget")
}

// (a') the same under CalcOrder.Calc with a lifted ≈ link: the premise
// set is the running fact, the link, the EqToLe instance and the
// LeTrans instance — a four-step resolution, still instant.
func TestCalcChainClose_OrderWithLiftUnderPoison(t *testing.T) {
	e := makeCalcScopedEnv(t, poisonBudget)
	givens := e.R.Apply(e.x, e.y).And(e.S.Apply(e.y, e.z)).Core()
	root := e.section(e.R.Apply(e.x, e.z).Core(), givens)
	e.orderKit().Calc(e.x,
		LeLeg(e.y, "x R y — a given", fromGivens(givens)),
		EqLeg(e.z, "y S z — a given", fromGivens(givens)),
	).applyAction(e.ctx, root)
	require.True(t, root.Proved(), "the mixed chain must close the section")
}

// (d) Leibniz branch — a mixed ≤/= chain: the fold has no instance and
// the scoped close is the running fact and the = link alone, closed by
// paramodulation, in the same poisoned context.
func TestCalcChainClose_LeibnizUnderPoison(t *testing.T) {
	e := makeCalcScopedEnv(t, poisonBudget)
	givens := e.R.Apply(e.x, e.y).And(e.y.Eq(e.z)).Core()
	root := e.section(e.R.Apply(e.x, e.z).Core(), givens)
	CalcOrder{
		Le: func(a, b Term) Prop { return MakeProp(e.R.Apply(a, b)) },
		// no LeTrans: ≤ never composes with ≤ here
	}.CalcLeibniz(e.x,
		LeLeg(e.y, "x R y — a given", fromGivens(givens)),
		EqLeg(e.z, "y = z — a given", fromGivens(givens)),
	).applyAction(e.ctx, root)
	require.True(t, root.Proved(), "the Leibniz chain must close the section")
}

// (c) A certificate that does not compose the two links — the
// mis-tagged-leg class: the grounded instance's antecedents are not the
// link the leg claims. The scoped close fails, and the diagnostic names
// the chained fact and its three premises; it does not send the author
// to record a key.
func TestCalcChainClose_MiscomposedCertificateNamesThePremises(t *testing.T) {
	e := makeCalcScopedEnv(t, poisonBudget)
	a, b, c := Var("a", TypeInd), Var("b", TypeInd), Var("c", TypeInd)
	// ∀a b c. R a b ∧ R c b ⇒ R a c — grounded at (x, y, z) it wants
	// R z y, which is not the link R y z.
	bad := core.NewAxiom(ForAll(a)(ForAll(b)(ForAll(c)(
		e.R.Apply(a, b).And(e.R.Apply(c, b)).Imply(e.R.Apply(a, c))))))
	kit := e.kit()
	kit.Trans = MakeFact(bad)
	givens := e.R.Apply(e.x, e.y).And(e.R.Apply(e.y, e.z)).Core()
	root := e.section(e.R.Apply(e.x, e.z).Core(), givens)

	msg := mustPanic(t, func() {
		kit.Calc(e.x,
			Leg(e.y, "x R y — a given", fromGivens(givens)),
			Leg(e.z, "y R z — a given", fromGivens(givens)),
		).applyAction(e.ctx, root)
	})
	require.Contains(t, msg, "CalcRel.Calc: calc: chain to leg 2 by transitivity")
	require.Contains(t, msg, "could not be closed from its two links and the transitivity instance")
	for _, premise := range []string{
		"chained fact:  " + ext.PrintTerm(e.R.Apply(e.x, e.z).Core()),
		"running fact:  " + ext.PrintTerm(e.R.Apply(e.x, e.y).Core()),
		"link:          " + ext.PrintTerm(e.R.Apply(e.y, e.z).Core()),
		"instance:      " + ext.PrintTerm(e.R.Apply(e.x, e.y).And(e.R.Apply(e.z, e.y)).Imply(e.R.Apply(e.x, e.z)).Core()),
	} {
		require.Contains(t, msg, premise)
	}
	require.Contains(t, msg, "mis-tagged leg")
	require.NotContains(t, msg, "XUGO_RECORD_FAMILY_CNF",
		"a live failure of the scoped close is a chain defect, never a key to record")
	// The fold leg carries its own diagnostic; the author-leg advice
	// ("drop its CnfRefute, or swap CiteSpecialize") must not be appended.
	require.NotContains(t, msg, "drop its CnfRefute")
	require.False(t, root.Proved())
}

// (e) The scoping happens INSIDE the chained leg's close: the section
// tree records ONE `by` composite per fold — per leg Assert + the
// leg's By, per fold Assert + the close — with no ClearHyps step and
// no bare CnfRefute beside it. The absolute total is not pinned (see
// the assertion's comment).
func TestCalcChainClose_RecordsNoExtraSteps(t *testing.T) {
	e := makeCalcScopedEnv(t, poisonBudget)
	givens := e.R.Apply(e.x, e.y).And(e.R.Apply(e.y, e.z)).And(e.R.Apply(e.z, e.w)).Core()
	// Non-terminal: the goal is unrelated, the chain's facts end resident
	// beside it and one leaf remains (Deduce linearity).
	env := e.env
	env.ProofService.LoadOrStoreConstMeta(core.MakeConstMeta("calcScopedG", TypeBool))
	G := e.ctx.Const("calcScopedG", TypeBool)
	root := e.section(G.Core(), givens)
	e.kit().Calc(e.x,
		Leg(e.y, "x R y — a given", fromGivens(givens)),
		Leg(e.z, "y R z — a given", fromGivens(givens)),
		Leg(e.w, "z R w — a given", fromGivens(givens)),
	).applyAction(e.ctx, root)

	leaves := root.UnsolvedLeaves()
	require.Len(t, leaves, 1, "a non-terminal chain leaves exactly one leaf")
	require.True(t, leaves[0].Goal.AnyHyp(e.R.Apply(e.x, e.w).AlphaEquals),
		"the chained fact R(x,w) must end resident")

	c := censusCalcTree(root)
	// Three legs → three link Bys; two folds → two scoped closes.
	require.Equal(t, 5, c.by, "three leg closes + two scoped chain closes:\n  %s", strings.Join(c.preorder, "\n  "))
	require.Equal(t, 0, c.clearHyps, "the clear lives inside the composite, never as a recorded step")
	require.Equal(t, 0, c.cnfRefute, "the bare CnfRefute is replaced 1:1 by the composite")
	// The ABSOLUTE step count is deliberately not pinned: how many steps
	// a leg's own proof records is the leg's business. What the fold
	// must not do is add steps of its own beside its close, and the
	// three counts above pin exactly that: one `by` composite per fold,
	// nothing else.
	require.Equal(t, c.steps, len(c.preorder), "the census and the preorder walk must agree:\n  %s",
		strings.Join(c.preorder, "\n  "))
}

// (f) A RESIDENT certificate — the transitivity of the relation is a
// hypothesis of the section, as the transitivity rule of an inductive
// relation stands once its rules are read out. The fold hands it to its
// close at the computed triple like any other certificate.
func TestCalcChainClose_ResidentCertificate(t *testing.T) {
	e := makeCalcScopedEnv(t, poisonBudget)
	a, b, c := Var("a", TypeInd), Var("b", TypeInd), Var("c", TypeInd)
	rule := ForAll(a)(ForAll(b)(ForAll(c)(
		e.R.Apply(a, b).And(e.R.Apply(b, c)).Imply(e.R.Apply(a, c))))).Core()
	givens := e.R.Apply(e.x, e.y).And(e.R.Apply(e.y, e.z)).And(e.R.Apply(e.z, e.w)).Core()
	hyps := append([]Term{givens, rule}, e.poison...)
	root := e.ctx.Section(MakeProp(e.R.Apply(e.x, e.w).Core(), hyps...))
	CalcRel{
		Rel:   func(a, b Term) Prop { return MakeProp(e.R.Apply(a, b)) },
		Trans: ResidentHyp(rule),
	}.Calc(e.x,
		Leg(e.y, "x R y — a given", fromGivens(givens)),
		Leg(e.z, "y R z — a given", fromGivens(givens)),
		Leg(e.w, "z R w — a given", fromGivens(givens)),
	).applyAction(e.ctx, root)
	require.True(t, root.Proved(), "a chain folded through a resident transitivity rule must close the section")
}

// (g) A certificate already at its relation's PARAMETERS — the relation
// T(p, ·, ·) with its transitivity stated over every p, handed to the
// kit at p. The fold appends the computed triple to the certificate's
// own grounding.
func TestCalcChainClose_CertificateAtItsParameters(t *testing.T) {
	e := makeCalcScopedEnv(t, poisonBudget)
	relTy := MakeFun(TypeInd, MakeFun(TypeInd, MakeFun(TypeInd, TypeBool)))
	e.env.ProofService.LoadOrStoreConstMeta(core.MakeConstMeta("calcScopedT", relTy))
	T := e.ctx.Const("calcScopedT", relTy)
	q, a, b, c := Var("q", TypeInd), Var("a", TypeInd), Var("b", TypeInd), Var("c", TypeInd)
	trans := core.NewAxiom(ForAll(q)(ForAll(a)(ForAll(b)(ForAll(c)(
		T.Apply(q, a, b).And(T.Apply(q, b, c)).Imply(T.Apply(q, a, c)))))))
	p := Var("p", TypeInd)
	givens := T.Apply(p, e.x, e.y).And(T.Apply(p, e.y, e.z)).And(T.Apply(p, e.z, e.w)).Core()
	root := e.section(T.Apply(p, e.x, e.w).Core(), givens)
	CalcRel{
		Rel:   func(a, b Term) Prop { return MakeProp(T.Apply(p, a, b)) },
		Trans: At(MakeFact(trans), p),
	}.Calc(e.x,
		Leg(e.y, "x T y — a given", fromGivens(givens)),
		Leg(e.z, "y T z — a given", fromGivens(givens)),
		Leg(e.w, "z T w — a given", fromGivens(givens)),
	).applyAction(e.ctx, root)
	require.True(t, root.Proved(), "a chain folded through a certificate at its parameters must close the section")
}

// (h) A certificate of a parameterized relation left OFF its parameters
// takes the fold's triple at the wrong binders: the close fails and the
// diagnostic names the instance and says what a mis-shaped certificate
// is.
func TestCalcChainClose_CertificateOffItsParametersNamesTheInstance(t *testing.T) {
	e := makeCalcScopedEnv(t, poisonBudget)
	relTy := MakeFun(TypeInd, MakeFun(TypeInd, MakeFun(TypeInd, TypeBool)))
	e.env.ProofService.LoadOrStoreConstMeta(core.MakeConstMeta("calcScopedT", relTy))
	T := e.ctx.Const("calcScopedT", relTy)
	q, a, b, c := Var("q", TypeInd), Var("a", TypeInd), Var("b", TypeInd), Var("c", TypeInd)
	trans := core.NewAxiom(ForAll(q)(ForAll(a)(ForAll(b)(ForAll(c)(
		T.Apply(q, a, b).And(T.Apply(q, b, c)).Imply(T.Apply(q, a, c)))))))
	p := Var("p", TypeInd)
	givens := T.Apply(p, e.x, e.y).And(T.Apply(p, e.y, e.z)).Core()
	root := e.section(T.Apply(p, e.x, e.z).Core(), givens)
	msg := mustPanic(t, func() {
		CalcRel{
			Rel:   func(a, b Term) Prop { return MakeProp(T.Apply(p, a, b)) },
			Trans: MakeFact(trans),
		}.Calc(e.x,
			Leg(e.y, "x T y — a given", fromGivens(givens)),
			Leg(e.z, "y T z — a given", fromGivens(givens)),
		).applyAction(e.ctx, root)
	})
	require.Contains(t, msg, "CalcRel.Calc: calc: chain to leg 2 by transitivity")
	require.Contains(t, msg, "a certificate of a parameterized relation left off its parameters")
	require.False(t, root.Proved())
}
