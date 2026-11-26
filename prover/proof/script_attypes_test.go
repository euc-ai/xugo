package proof

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/stretchr/testify/assert"
)

// TestScriptAtTypes_SequentRow exercises the compute-route cross-type
// cite: a sequent-shaped "registry entry" at a machine-named type var is
// normalized to its closed canonical form and type-instantiated to the target
// type, with zero pinned text. Mirrors a card-is-zero cite at ?83488
// that motivated the primitive. (Predicates are consts, not variables —
// Normalize's mini-scoping collapses var-predicate clauses.)
func TestScriptAtTypes_SequentRow(t *testing.T) {
	env := makeStepTestEnv()
	ctx := NewScript(env)

	// Row:  FIN(s) ⊢ CRD(s)   at type var ?83488.
	elem := core.MakeVarType("?83488")
	setT := MakeFun(elem, TypeBool)
	env.ProofService.LoadOrStoreConstMeta(core.MakeConstMeta("FIN", MakeFun(setT, TypeBool)))
	env.ProofService.LoadOrStoreConstMeta(core.MakeConstMeta("CRD", MakeFun(setT, TypeBool)))
	FIN := ctx.Const("FIN", MakeFun(setT, TypeBool))
	CRD := ctx.Const("CRD", MakeFun(setT, TypeBool))
	s := Var("s", setT)
	row := core.TestThm(CRD.Apply(s), FIN.Apply(s))

	inst := ctx.AtTypes(row, TypeInd)

	// The instance is proved, closed (hyps folded by Normalize), and
	// carries no residual type variable.
	assert.True(t, inst.Proved())
	assert.Equal(t, 0, inst.NumHyps())
	assert.False(t, ext.PropHasTypeVars(inst))

	// It is exactly Normalize(row) instantiated at ind.
	norm, _ := Normalize(row)
	want := core.PropTypeInst(norm, core.MakeTypeSubst(elem, TypeInd))
	assert.True(t, inst.AlphaEquals(want))
}

// TestScriptAtTypes_IdentitySubst: passing the row's own type var is a
// no-op substitution — the canonical form itself comes back.
func TestScriptAtTypes_IdentitySubst(t *testing.T) {
	env := makeStepTestEnv()
	ctx := NewScript(env)

	elem := core.MakeVarType("A")
	env.ProofService.LoadOrStoreConstMeta(core.MakeConstMeta("PP", MakeFun(elem, TypeBool)))
	env.ProofService.LoadOrStoreConstMeta(core.MakeConstMeta("QQ", MakeFun(elem, TypeBool)))
	P := ctx.Const("PP", MakeFun(elem, TypeBool))
	Q := ctx.Const("QQ", MakeFun(elem, TypeBool))
	x := Var("x", elem)
	row := core.TestThm(ext.ForAll(x)(P.Apply(x).Or(Q.Apply(x))))

	inst := ctx.AtTypes(row, elem)
	norm, _ := Normalize(row)
	assert.True(t, inst.AlphaEquals(norm))
}

// TestScriptAtTypes_PositionalOrderAndArity: type args match the
// normalized statement's type vars by first occurrence, and a count
// mismatch panics with the vars listed in that order.
func TestScriptAtTypes_PositionalOrderAndArity(t *testing.T) {
	env := makeStepTestEnv()
	ctx := NewScript(env)

	// Two type vars; ?22 occurs first (g : ?22 → ?11 applied to b : ?22).
	tvA := core.MakeVarType("?11")
	tvB := core.MakeVarType("?22")
	env.ProofService.LoadOrStoreConstMeta(core.MakeConstMeta("gg", MakeFun(tvB, tvA)))
	env.ProofService.LoadOrStoreConstMeta(core.MakeConstMeta("qq", MakeFun(tvA, TypeBool)))
	g := ctx.Const("gg", MakeFun(tvB, tvA))
	q := ctx.Const("qq", MakeFun(tvA, TypeBool))
	b := Var("b", tvB)
	row := core.TestThm(q.Apply(g.Apply(b)))

	norm, _ := Normalize(row)
	vars := orderedPropTypeVars(norm)
	if assert.Len(t, vars, 2) {
		assert.Equal(t, "?22", string(vars[0].Name()))
		assert.Equal(t, "?11", string(vars[1].Name()))
	}

	// Correct positional use: ?22 ↦ bool, ?11 ↦ ind.
	inst := ctx.AtTypes(row, TypeBool, TypeInd)
	assert.False(t, ext.PropHasTypeVars(inst))

	// Arity mismatch panics, naming both vars in positional order.
	defer func() {
		r := recover()
		if assert.NotNil(t, r, "expected arity panic") {
			msg, _ := r.(string)
			assert.Contains(t, msg, "?22")
			assert.Contains(t, msg, "?11")
		}
	}()
	_ = ctx.AtTypes(row, TypeBool)
}

// TestScriptAtTypeVars_NamedEqualsPositional: the named spelling and
// the positional one are the SAME instance — install form and stated
// reference alike — whatever order the bindings are written in,
// because both funnel into the one install tail (atTypeInstance).
// This identity is what lets wrapper source migrate off the
// positional convention with zero re-record.
func TestScriptAtTypeVars_NamedEqualsPositional(t *testing.T) {
	env := makeStepTestEnv()
	ctx := NewScript(env)

	// Same shape as the positional-order fixture: ?22 occurs first
	// (g : ?22 → ?11 applied to b : ?22).
	tvA := core.MakeVarType("?11")
	tvB := core.MakeVarType("?22")
	env.ProofService.LoadOrStoreConstMeta(core.MakeConstMeta("ggnv", MakeFun(tvB, tvA)))
	env.ProofService.LoadOrStoreConstMeta(core.MakeConstMeta("qqnv", MakeFun(tvA, TypeBool)))
	g := ctx.Const("ggnv", MakeFun(tvB, tvA))
	q := ctx.Const("qqnv", MakeFun(tvA, TypeBool))
	b := Var("b", tvB)
	row := core.TestThm(q.Apply(g.Apply(b)))

	// Positional: first occurrence runs (?22, ?11).
	pos := ctx.AtTypes(row, TypeBool, TypeInd)

	// Named, written in the OTHER order — the list order carries no
	// meaning. One binding goes through the public TypeVarBinding
	// spelling, one through the raw struct, so both constructors are
	// observed.
	named := ctx.AtTypeVars(row,
		TypeBinding{name: "?11", to: TypeInd},
		typeVarBinding[ext.Bool]("?22"))

	assert.True(t, named.AlphaEquals(pos))
	assert.True(t, named.Reference().AlphaEquals(pos.Reference()))
}

// TestScriptAtTypeVars_NameMismatchPanics: a binding set that does not
// match the statement's type variables exactly panics naming the
// statement's own letters — missing, unknown and doubly-bound alike.
// The loud failure is the point of the named spelling: the positional
// twin's failure mode for a wrong ORDER was a silently permuted
// instance.
func TestScriptAtTypeVars_NameMismatchPanics(t *testing.T) {
	env := makeStepTestEnv()
	ctx := NewScript(env)

	elem := core.MakeVarType("A")
	env.ProofService.LoadOrStoreConstMeta(core.MakeConstMeta("PPnm", MakeFun(elem, TypeBool)))
	P := ctx.Const("PPnm", MakeFun(elem, TypeBool))
	x := Var("x", elem)
	row := core.TestThm(ext.ForAll(x)(P.Apply(x)))

	expectPanic := func(t *testing.T, wants ...string) {
		t.Helper()
		r := recover()
		if !assert.NotNil(t, r, "expected panic") {
			return
		}
		msg, _ := r.(string)
		for _, w := range wants {
			assert.Contains(t, msg, w)
		}
	}

	t.Run("unknown name", func(t *testing.T) {
		defer expectPanic(t, "unknown [B]", "type variables [A]")
		ctx.AtTypeVars(row, TypeBinding{name: "B", to: TypeInd})
	})
	t.Run("missing name", func(t *testing.T) {
		defer expectPanic(t, "missing [A]")
		ctx.AtTypeVars(row)
	})
	t.Run("bound twice", func(t *testing.T) {
		defer expectPanic(t, "bound twice")
		ctx.AtTypeVars(row,
			TypeBinding{name: "A", to: TypeInd},
			TypeBinding{name: "A", to: TypeBool})
	})
}

// TestScriptAtTypes_WitnessOrderFollowsStatedForm: an `At(ctx.AtTypes(dep,
// τ…), w…)` witness tuple is read in the dep's OWN stated binder order —
// the same statement-slot rule every other ground cite follows — because
// the TypedThm return carries the raw stated form as the reference
// (witness_order.go). Historically this cite fell to the POSITIONAL path
// (the reference was the normalized install form itself), so a row whose
// normalized ∀-prefix reorders had to be cited in machine order.
//
// Fixture: stated ∀x:A. ∀s:(A→bool). QQ(s, x) — the matrix mentions s
// first, so the normalized prefix flips to (s, x). The witnesses' types
// differ, so a positional (machine-order) reading of the stated-order
// tuple could not silently succeed.
func TestScriptAtTypes_WitnessOrderFollowsStatedForm(t *testing.T) {
	env := makeStepTestEnv()
	ctx := NewScript(env)

	elem := core.MakeVarType("A")
	setT := MakeFun(elem, TypeBool)
	qTy := MakeFun(setT, MakeFun(elem, TypeBool))
	env.ProofService.LoadOrStoreConstMeta(core.MakeConstMeta("QQwo", qTy))
	Q := ctx.Const("QQwo", qTy)
	x := Var("x", elem)
	sv := Var("s", setT)
	row := core.TestThm(ext.ForAll(x)(ext.ForAll(sv)(Q.Apply(sv).Apply(x))))

	// The fixture is load-bearing only if Normalize actually reorders.
	norm, _ := Normalize(row)
	prefix, distinct := forallPrefixNames(norm.Conclusion())
	assert.True(t, distinct)
	if assert.Equal(t, []string{"s", "x"}, prefix,
		"fixture must normalize to the FLIPPED prefix, else it tests nothing") {

		L := ctx.AtTypes(row, TypeInd)
		// The reference half is the stated form at the instance types.
		refPrefix, _ := forallPrefixNames(L.Reference().Conclusion())
		assert.Equal(t, []string{"x", "s"}, refPrefix)

		// Cite at witnesses in the STATED order (x first, s second).
		indSetT := MakeFun(TypeInd, TypeBool)
		x0 := Var("x0", TypeInd)
		s0 := Var("s0", indSetT)
		R := Var("R", TypeBool)
		S := Var("S", TypeBool)
		sec := ctx.Section(prop.MakeProp(R.Core(), S.Core()))
		sec.Do(Cite(L, x0, s0))
		leaves := sec.UnsolvedLeaves()
		if assert.Len(t, leaves, 1) {
			qInd := ext.WrapTerm(Q.Core().TypeSubstitute(core.MakeTypeSubst(elem, TypeInd)))
			want := qInd.Apply(s0).Apply(x0)
			assert.True(t, leaves[0].Goal.AnyHyp(want.AlphaEquals),
				"the ground instance QQwo(s0, x0) must be resident — the stated-order "+
					"tuple (x0, s0) permuted onto the flipped install prefix")
		}
	}
}

// TestScriptAtTypes_ByPremiseIsExact: a By premise whose target is an
// AtTypes instance records exact=true — the executor installs the
// explicit instantiation verbatim instead of letting the speculative
// goal-side type adaptation override it (the materialize failure of
// cardinality.CardSubsetEq at B). The premise goes in BARE: against this one-premise
// goal the ∀-form's exact install absorbs the goal outright, so a
// witness tuple would never be applied and By refuses it (the
// unapplied-witnesses contract).
func TestScriptAtTypes_ByPremiseIsExact(t *testing.T) {
	env := makeStepTestEnv()
	ctx := NewScript(env)

	elem := core.MakeVarType("A")
	pTy := MakeFun(elem, TypeBool)
	env.ProofService.LoadOrStoreConstMeta(core.MakeConstMeta("PPex", pTy))
	P := ctx.Const("PPex", pTy)
	x := Var("x", elem)
	row := core.TestThm(ext.ForAll(x)(P.Apply(x)))

	// Instantiate at a fresh type VARIABLE — the shape whose install a
	// speculative adaptation would re-adapt against the goal.
	B := core.MakeVarType("B")
	L := ctx.AtTypes(row, B)

	a := Var("a", B)
	pAtB := ext.WrapTerm(P.Core().TypeSubstitute(core.MakeTypeSubst(elem, B)))
	sec := ctx.Section(prop.MakeProp(pAtB.Apply(a).Core()))
	sec.Do(By(L))
	assert.True(t, sec.Proved())

	// The recorded composite carries exact on the premise.
	detailed := sec.DetailedProofProto()
	var byProto *ByProto
	for _, s := range detailed.GetSteps() {
		if bp, ok := s.Step.(*StepProto_By); ok {
			byProto = bp.By
		}
	}
	if assert.NotNil(t, byProto) && assert.Len(t, byProto.GetPremises(), 1) {
		assert.True(t, byProto.GetPremises()[0].GetExact(),
			"an AtTypes premise must record exact=true")
	}
}

// TestScriptAtTypes_InductionObligations: ByInduction reads its case
// obligations off a principle cited THROUGH AtTypes — the raw stated
// form (implication intact) is the reference, where the normalized
// install form has no antecedent to read cases off.
func TestScriptAtTypes_InductionObligations(t *testing.T) {
	env := makeStepTestEnv()
	ctx := NewScript(env)

	elem := core.MakeVarType("A")
	env.ProofService.LoadOrStoreConstMeta(core.MakeConstMeta("zz_ind", elem))
	env.ProofService.LoadOrStoreConstMeta(core.MakeConstMeta("sc_ind", MakeFun(elem, elem)))
	z := ctx.Const("zz_ind", elem)
	sc := ctx.Const("sc_ind", MakeFun(elem, elem))
	Pv := Var("P", MakeFun(elem, TypeBool))
	n := Var("n", elem)
	// ∀P. P(z) ∧ (∀n. P(n) ⇒ P(sc(n))) ⇒ ∀n. P(n)
	principle := core.TestThm(ext.ForAll(Pv)(
		Pv.Apply(z).
			And(ext.ForAll(n)(Pv.Apply(n).Imply(Pv.Apply(sc.Apply(n))))).
			Imply(ext.ForAll(n)(Pv.Apply(n)))))

	L := ctx.AtTypes(principle, TypeInd)

	env.ProofService.LoadOrStoreConstMeta(core.MakeConstMeta("qq_ind", MakeFun(TypeInd, TypeBool)))
	q := ctx.Const("qq_ind", MakeFun(TypeInd, TypeBool))

	obligations := inductionObligations(ctx, At(L, q.Core()), 2, L.Reference())
	if assert.Len(t, obligations, 2) {
		zInd := ext.WrapTerm(z.Core().TypeSubstitute(core.MakeTypeSubst(elem, TypeInd)))
		assert.True(t, obligations[0].Conclusion().AlphaEquals(
			q.Apply(zInd).Core()),
			"base obligation is P at the instantiated zero")
	}
}
