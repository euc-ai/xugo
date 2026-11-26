package engine

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/stretchr/testify/require"
)

// Detaching both loose laws would change the intermediate structure's
// type on emitted Go replay. Both frontends refuse that shape before
// applying it; materializing the intermediate structure is explicit.
func TestByRead_NestedLooseIntermediateMustBeMaterialized(t *testing.T) {
	env := testEnv()
	b, c := core.MakeVarType("B"), core.MakeVarType("C")
	funB := core.MakeFun(b, b)
	hm := core.MakeConstMeta("nestedLooseH", core.MakeFun(core.TypeA(), core.TypeBool()))
	km := core.MakeConstMeta("nestedLooseK", core.MakeFun(funB, core.TypeBool()))
	pm := core.MakeConstMeta("nestedLooseP", core.MakeFun(funB, core.MakeFun(c, core.TypeBool())))
	for _, m := range []core.ConstTermMeta{hm, km, pm} {
		env.ProofService.LoadOrStoreConstMeta(m)
	}
	a, x, y := core.Var("a", core.TypeA()), core.Var("x", b), core.Var("y", c)
	f := core.Var("f", funB)
	h := ext.WrapTerm(core.MakeConstTerm(hm, hm.AbsType()))
	k := ext.WrapTerm(core.MakeConstTerm(km, km.AbsType()))
	p := ext.WrapTerm(core.MakeConstTerm(pm, pm.AbsType()))
	inner := core.TestThm(ext.ForAll(a)(h.Apply(a).Imply(k.Apply(core.Abs(x, x)))).Core())
	outer := core.TestThm(ext.ForAll(f)(k.Apply(f).Imply(ext.ForAll(y)(p.Apply(f, y)))).Core())
	if env.LibraryThms == nil {
		env.LibraryThms = map[string]core.Thm{}
	}
	env.LibraryThms["nested.Inner"], env.LibraryThms["nested.Outer"] = inner, outer
	boolFun := core.MakeFun(core.TypeBool(), core.TypeBool())
	z := core.Var("z", core.TypeBool())
	identity := core.Abs(z, z)
	hyp := core.Apply(core.MakeConstTerm(hm, core.MakeFun(TypeInd, core.TypeBool())), core.Var("a0", TypeInd))
	structure := core.Apply(core.MakeConstTerm(km, core.MakeFun(boolFun, core.TypeBool())), identity)
	goalTerm := ext.WrapTerm(core.MakeConstTerm(pm, core.MakeFun(boolFun, core.MakeFun(core.TypeBool(), core.TypeBool())))).Apply(identity, core.Var("target", core.TypeBool())).Core()
	message := "By: a bare nested loose reading has an intermediate structure with unfixed type letters; materialize that structure as a resident fact before reading the outer law"
	for _, materialized := range []bool{false, true} {
		name := "nested"
		goal := core.MakeProp(goalTerm, hyp)
		if materialized {
			name = "materialized"
			goal = core.MakeProp(goalTerm, structure)
		}
		t.Run(name+"/Go", func(t *testing.T) {
			script := proof.NewScript(env)
			section := script.Section(goal)
			read := proof.Read(homologyReadDep("nested.Outer"), proof.Read(homologyReadDep("nested.Inner"), proof.ResidentHyp(hyp)))
			if materialized {
				read = proof.Read(homologyReadDep("nested.Outer"), proof.ResidentHyp(structure))
			}
			apply := func() { section.Do(proof.Derive(func(a *proof.Argument) { a.Show("the outer law", proof.By(read)) })) }
			if !materialized {
				require.PanicsWithValue(t, "Argument.Show(\"the outer law\"): "+message, apply)
				return
			}
			apply()
			require.True(t, section.Proved())
		})
		t.Run(name+"/session", func(t *testing.T) {
			e := newEngine(env)
			info, err := e.CreateSession(t.Context())
			require.NoError(t, err)
			s, err := e.getSession(info.ID)
			require.NoError(t, err)
			installSimpAdaptationCards(s, []core.Prop{inner, outer}, []LemmaWithSpec{{Key: "nested.Inner"}, {Key: "nested.Outer"}})
			gid := s.AddGoal(goal)
			idx := 0
			at := &ReadAtSpec{Key: "nested.Inner", ReadAt: &ReadAtSpec{HypIndex: &idx}}
			if materialized {
				at = &ReadAtSpec{HypIndex: &idx}
			}
			out, err := e.ApplyStep(t.Context(), info.ID, &ApplyStepRequest{GoalID: gid, Tactic: TacticReq{Type: "by", WithLemmas: []LemmaWithSpec{{Key: "nested.Outer", ReadAt: at}}}})
			if !materialized {
				if err != nil {
					require.Contains(t, err.Error(), message)
				} else {
					require.False(t, out.Success)
					require.Contains(t, out.Diagnostics[0].Message, message)
				}
				state, err := e.InspectState(t.Context(), info.ID)
				require.NoError(t, err)
				require.Len(t, state.Goals, 1)
				require.True(t, state.Goals[0].Statement.AlphaEquals(goal))
				return
			}
			require.NoError(t, err)
			require.True(t, out.Success, "%+v", out.Diagnostics)
			require.Zero(t, out.State.NumOpen)
		})
	}
}
