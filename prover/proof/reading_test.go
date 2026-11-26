package proof

import (
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
)

// serveThm registers a theorem under a dep name in the script's env.
func serveThm(ctx *Script, name string, thm core.ThmCert) {
	if ctx.Env.LibraryThms == nil {
		ctx.Env.LibraryThms = map[string]core.Thm{}
	}
	ctx.Env.LibraryThms[name] = thm
}

// sprintAny renders a recovered panic value for an assertion message.
func sprintAny(v any) string {
	if err, ok := v.(error); ok {
		return err.Error()
	}
	if s, ok := v.(string); ok {
		return s
	}
	return ""
}

// depName is a bare dep name as a NamedDep, for the tests' served
// theorems.
type depName string

func (d depName) DepName() string { return string(d) }

// AsFact makes a bare dep name a cite target, as an entry is.
func (d depName) AsFact() Fact { return NamedFact(d) }

// readingTestEnv: a structure `mon : (A → A → A) → A → bool`, its law
// `∀op e. mon(op, e) ⇒ ∀x. op(e, x) = x` at the letter A, an instance
// `mon(plus, zero)` at ind, and a predicate Q : ind → bool to rewrite
// under.
type readingTestEnv struct {
	ctx        *Script
	plus, zero *ext.TermWrapper
	Q          *ext.TermWrapper
	a          *ext.TermWrapper
	// law is the served law's statement, for a dep that states it.
	law Prop
}

// statedDep is a dep that states its statement before the proof runs,
// as a registry entry does.
type statedDep struct {
	name   string
	stated Prop
}

func (d statedDep) DepName() string     { return d.name }
func (d statedDep) StatementProp() Prop { return d.stated }

func makeReadingTestEnv() *readingTestEnv {
	env := makeStepTestEnv()
	ctx := NewScript(env)
	opA := MakeFun(core.TypeA(), MakeFun(core.TypeA(), core.TypeA()))
	monA := MakeFun(opA, MakeFun(core.TypeA(), TypeBool))
	opInd := MakeFun(TypeInd, MakeFun(TypeInd, TypeInd))
	env.ProofService.LoadOrStoreConstMeta(core.MakeConstMeta("readMon", monA))
	env.ProofService.LoadOrStoreConstMeta(core.MakeConstMeta("readPlus", opInd))
	env.ProofService.LoadOrStoreConstMeta(core.MakeConstMeta("readZero", TypeInd))
	env.ProofService.LoadOrStoreConstMeta(core.MakeConstMeta("readQ", MakeFun(TypeInd, TypeBool)))

	// The law, at the letter A.
	op := Var("op", opA)
	e := Var("e", core.TypeA())
	x := Var("x", core.TypeA())
	monAtA := ctx.Const("readMon", monA)
	law := ext.ForAll(op, e)(monAtA.Apply(op, e).Imply(ext.ForAll(x)(ext.WrapTerm(op).Apply(e, x).Eq(x))))
	serveThm(ctx, "zz_read_law", core.TestThm(law.Core()))

	// The instance, at ind.
	monAtInd := ctx.Const("readMon", MakeFun(opInd, MakeFun(TypeInd, TypeBool)))
	plus := ctx.Const("readPlus", opInd)
	zero := ctx.Const("readZero", TypeInd)
	serveThm(ctx, "zz_read_inst", core.TestThm(monAtInd.Apply(plus, zero).Core()))
	// A second fact that does not state the law's structure.
	serveThm(ctx, "zz_read_other", core.TestThm(ctx.Const("readQ", MakeFun(TypeInd, TypeBool)).Apply(zero).Core()))

	return &readingTestEnv{
		ctx: ctx, plus: plus, zero: zero,
		Q:   ctx.Const("readQ", MakeFun(TypeInd, TypeBool)),
		a:   ext.WrapTerm(Var("a", TypeInd)),
		law: prop.MakeProp(law.Core()),
	}
}

// The reading is the law at the instance's components with the
// hypothesis gone, and it serves a Simp as an unconditional rule.
func TestRead_LawAtInstanceIsAnUnconditionalRule(t *testing.T) {
	e := makeReadingTestEnv()
	reading := Read(depName("zz_read_law"), depName("zz_read_inst"))

	sec := e.ctx.Section(prop.MakeProp(e.Q.Apply(e.plus.Apply(e.zero, e.a)).Core()))
	sec.Do(Simp(Fwd(reading)))
	leaves := sec.UnsolvedLeaves()
	require.Len(t, leaves, 1)
	require.True(t, leaves[0].Goal.Conclusion().AlphaEquals(e.Q.Apply(e.a).Core()),
		"plus(zero, a) ↦ a under Q; got %s", ext.PrintTerm(leaves[0].Goal.Conclusion()))

	// The derived statement itself: ∀x:ind. plus(zero, x) = x.
	x := Var("x", TypeInd)
	want := ext.ForAll(x)(e.plus.Apply(e.zero, x).Eq(x)).Core()
	got := resolveLemmaTarget("test", e.ctx, reading)
	require.True(t, got.Conclusion().AlphaEquals(want), "reading reads %s", prop.PrintProp(got))
	require.Zero(t, got.NumHyps())
}

// A By closes on the reading alone: the apply rung reads its
// conclusion, nothing conditional left to discharge.
func TestRead_ByClosesOnTheReading(t *testing.T) {
	e := makeReadingTestEnv()
	sec := e.ctx.Section(prop.MakeProp(e.plus.Apply(e.zero, e.a).Eq(e.a).Core()))
	sec.Do(Derive(func(arg *Argument) {
		arg.Show("the identity law read at the instance", By(Read(depName("zz_read_law"), depName("zz_read_inst"))))
	}))
	require.True(t, sec.Proved())
}

// A fact that does not state the law's hypothesis refuses at
// consumption, naming both statements.
func TestRead_RefusesAnInstanceOfAnotherStructure(t *testing.T) {
	e := makeReadingTestEnv()
	sec := e.ctx.Section(prop.MakeProp(e.Q.Apply(e.plus.Apply(e.zero, e.a)).Core()))
	defer func() {
		r := recover()
		require.NotNil(t, r, "a reading at a fact that is not the law's structure must refuse")
		require.Contains(t, sprintAny(r), "the instance states")
	}()
	sec.Do(Simp(Fwd(Read(depName("zz_read_law"), depName("zz_read_other")))))
	t.Fatal("unreachable")
}

// residentReadingGoal is a section whose goal carries the instance as
// its antecedent — `mon(plus, zero) ⇒ body` — so that, assumed, the
// structure fact is a RESIDENT hypothesis and the law is read under it.
func (e *readingTestEnv) residentReadingGoal(body *ext.TermWrapper) *GoalStackNode {
	monAtInd := e.ctx.Const("readMon", MakeFun(MakeFun(TypeInd, MakeFun(TypeInd, TypeInd)), MakeFun(TypeInd, TypeBool)))
	return e.ctx.Section(prop.MakeProp(monAtInd.Apply(e.plus, e.zero).Imply(body).Core()))
}

// The reading at a resident fact is the law at the fact's components
// UNDER the fact: one hypothesis, the fact's content, and the law's
// body at the components as conclusion.
func TestRead_AtResidentFactIsTheLawUnderIt(t *testing.T) {
	e := makeReadingTestEnv()
	sec := e.residentReadingGoal(e.plus.Apply(e.zero, e.a).Eq(e.a))
	var got Prop
	sec.Do(Derive(func(arg *Argument) {
		inst := arg.Assume()
		got = resolveLemmaTarget("test", e.ctx, Read(depName("zz_read_law"), inst))
		arg.Show("the law read under the resident instance", By(Read(depName("zz_read_law"), inst)))
	}))
	require.True(t, sec.Proved())
	x := Var("x", TypeInd)
	want := ext.ForAll(x)(e.plus.Apply(e.zero, x).Eq(x)).Core()
	require.True(t, got.Conclusion().AlphaEquals(want), "reading reads %s", prop.PrintProp(got))
	require.Equal(t, 1, got.NumHyps(), "the reading is under the resident fact: %s", prop.PrintProp(got))
	monAtInd := e.ctx.Const("readMon", MakeFun(MakeFun(TypeInd, MakeFun(TypeInd, TypeInd)), MakeFun(TypeInd, TypeBool)))
	require.True(t, got.Hyp(0).AlphaEquals(monAtInd.Apply(e.plus, e.zero).Core()))
}

// A By keeps the reading's hypothesis resident beside it without the
// author listing the fact: the ring is not a premise, the reading is,
// and the reading's conclusion joins the context bare — where a
// SECOND law cited beside it finds it as an antecedent. That is the
// one-hop instance resolution the resident form exists for.
func TestRead_AtResidentFactSuppliesAnAntecedent(t *testing.T) {
	e := makeReadingTestEnv()
	// A second law over the same structure: mon(op, e) ⇒ ∀x. op(x, e) = x
	// — stated so that its conclusion is what the goal asks, and whose
	// antecedent the reading's conclusion is NOT; and a law whose
	// antecedent IS the reading's conclusion: (∀x. plus(zero, x) = x) ⇒ Q(zero).
	x := Var("x", TypeInd)
	consequence := ext.ForAll(x)(e.plus.Apply(e.zero, x).Eq(x)).Imply(e.Q.Apply(e.zero))
	serveThm(e.ctx, "zz_read_consequence", core.TestThm(consequence.Core()))

	sec := e.residentReadingGoal(e.Q.Apply(e.zero))
	sec.Do(Derive(func(arg *Argument) {
		inst := arg.Assume()
		arg.Show("the identity law read under the instance discharges the consequence's antecedent",
			By(Read(depName("zz_read_law"), inst), depName("zz_read_consequence")))
	}))
	require.True(t, sec.Proved())
}

// A resident reading serves a Simp as a rule under its hypothesis —
// here the fact is named by content (ResidentHyp, emit's spelling of a
// resident premise), the other resident flavor.
func TestRead_AtResidentFactServesSimp(t *testing.T) {
	e := makeReadingTestEnv()
	sec := e.residentReadingGoal(e.Q.Apply(e.plus.Apply(e.zero, e.a)))
	sec.Do(StripImp())
	monAtInd := e.ctx.Const("readMon", MakeFun(MakeFun(TypeInd, MakeFun(TypeInd, TypeInd)), MakeFun(TypeInd, TypeBool)))
	inst := ResidentHyp(monAtInd.Apply(e.plus, e.zero).Core())
	sec.Do(Simp(Fwd(Read(depName("zz_read_law"), inst))))
	leaves := sec.UnsolvedLeaves()
	require.Len(t, leaves, 1)
	require.True(t, leaves[0].Goal.Conclusion().AlphaEquals(e.Q.Apply(e.a).Core()),
		"plus(zero, a) ↦ a under Q; got %s", ext.PrintTerm(leaves[0].Goal.Conclusion()))
}

// A resident fact that does not state the law's structure refuses at
// consumption, naming both statements — the same refusal as at an
// entry.
func TestRead_AtResidentFactOfAnotherStructureRefuses(t *testing.T) {
	e := makeReadingTestEnv()
	sec := e.ctx.Section(prop.MakeProp(e.Q.Apply(e.zero).Imply(e.plus.Apply(e.zero, e.a).Eq(e.a)).Core()))
	defer func() {
		r := recover()
		require.NotNil(t, r, "a reading under a fact that is not the law's structure must refuse")
		require.Contains(t, sprintAny(r), "the instance states")
	}()
	sec.Do(Derive(func(arg *Argument) {
		other := arg.Assume()
		arg.Show("cannot read the law under Q(zero)", By(Read(depName("zz_read_law"), other)))
	}))
	t.Fatal("unreachable")
}

// The instance is the fact itself: a grounded or pinned fact is
// refused at construction, and so is anything that is neither an
// entry nor a resident fact. A grounded READING is refused with the
// spelling that serves it — the ground fact as a Have.
func TestRead_RefusesAGroundedInstance(t *testing.T) {
	e := makeReadingTestEnv()
	require.PanicsWithValue(t,
		"Read(zz_read_law): the instance is the structure fact itself, not dep \"zz_read_inst\" at (a) — a reading pins nothing of it",
		func() { Read(depName("zz_read_law"), At(depName("zz_read_inst"), e.a)) })
	require.Panics(t, func() { Read(depName("zz_read_law"), "zz_read_inst") })
	defer func() {
		r := recover()
		require.NotNil(t, r, "a reading at a grounded reading must refuse")
		require.Contains(t, sprintAny(r), "is a reading grounded at its witnesses")
		require.Contains(t, sprintAny(r), "state the ground fact as a Have")
	}()
	Read(depName("zz_read_law"), Read(depName("zz_read_law"), depName("zz_read_inst")).At(e.a))
	t.Fatal("unreachable")
}

// A reading under a resident hypothesis is a fact of the context, so
// it is materialized before every install whatever its position in
// the author's list — the Have it replaces was resident before the By
// began, and an install's strategies read the context. (The corpus
// pins the consequence: vec_space.SpanMember's leaf key moves when the
// reading is asserted after ZeroSmul's install.)
func TestRead_AtResidentFactIsMaterializedFirst(t *testing.T) {
	law := byPremise{describe: "law"}
	reading := byPremise{describe: "reading", readingUnder: true}
	kept := byPremise{describe: "kept", resident: true}
	got := withReadingsFirst([]byPremise{law, kept, reading})
	require.Equal(t, []string{"reading", "law", "kept"},
		[]string{got[0].describe, got[1].describe, got[2].describe})
	same := []byPremise{law, kept}
	require.Equal(t, same, withReadingsFirst(same))
}

// A reading at a READING: a projection law `grp(op, e) ⇒ mon(op, e)`
// read at the resident group fact gives the monoid at its components
// under the group; the monoid's law read at THAT is the identity law
// under the group — one value where two rules (the projection's
// reading as side-condition oracle, the law at the carrier's letter)
// stood before.
func TestRead_AtAReadingIsTheLawUnderTheInnerHypothesis(t *testing.T) {
	e := makeReadingTestEnv()
	opA := MakeFun(core.TypeA(), MakeFun(core.TypeA(), core.TypeA()))
	grpA := MakeFun(opA, MakeFun(core.TypeA(), TypeBool))
	e.ctx.Env.ProofService.LoadOrStoreConstMeta(core.MakeConstMeta("readGrp", grpA))
	op := Var("op", opA)
	eV := Var("e", core.TypeA())
	monAtA := e.ctx.Const("readMon", MakeFun(opA, MakeFun(core.TypeA(), TypeBool)))
	grpAtA := e.ctx.Const("readGrp", grpA)
	projection := ext.ForAll(op, eV)(grpAtA.Apply(op, eV).Imply(monAtA.Apply(op, eV)))
	serveThm(e.ctx, "zz_read_proj", core.TestThm(projection.Core()))

	opInd := MakeFun(TypeInd, MakeFun(TypeInd, TypeInd))
	grpAtInd := e.ctx.Const("readGrp", MakeFun(opInd, MakeFun(TypeInd, TypeBool)))
	sec := e.ctx.Section(prop.MakeProp(grpAtInd.Apply(e.plus, e.zero).Imply(e.plus.Apply(e.zero, e.a).Eq(e.a)).Core()))
	var got Prop
	sec.Do(Derive(func(arg *Argument) {
		group := arg.Assume()
		nested := Read(depName("zz_read_law"), Read(depName("zz_read_proj"), group))
		got = resolveLemmaTarget("test", e.ctx, nested)
		arg.Show("the identity law read at the monoid read at the group", By(nested))
	}))
	require.True(t, sec.Proved())
	x := Var("x", TypeInd)
	want := ext.ForAll(x)(e.plus.Apply(e.zero, x).Eq(x)).Core()
	require.True(t, got.Conclusion().AlphaEquals(want), "nested reading reads %s", prop.PrintProp(got))
	require.Equal(t, 1, got.NumHyps(), "under the group alone: %s", prop.PrintProp(got))
	require.True(t, got.Hyp(0).AlphaEquals(grpAtInd.Apply(e.plus, e.zero).Core()))
}

// A bare reading of a law whose statement is known before the proof
// runs states its content — the law at what its instance says: the
// projection's conclusion at the resident group, and the law's body at
// that — so a closure law read at the reading of a projection can name
// the member it concludes (ReadMember), as one read at a typed
// structure fact can. A law named by a bare name states nothing.
func TestRead_ContentOfAReadingOfAProjection(t *testing.T) {
	e := makeReadingTestEnv()
	opA := MakeFun(core.TypeA(), MakeFun(core.TypeA(), core.TypeA()))
	grpA := MakeFun(opA, MakeFun(core.TypeA(), TypeBool))
	e.ctx.Env.ProofService.LoadOrStoreConstMeta(core.MakeConstMeta("readGrp", grpA))
	op := Var("op", opA)
	eV := Var("e", core.TypeA())
	monAtA := e.ctx.Const("readMon", MakeFun(opA, MakeFun(core.TypeA(), TypeBool)))
	grpAtA := e.ctx.Const("readGrp", grpA)
	projection := prop.MakeProp(ext.ForAll(op, eV)(grpAtA.Apply(op, eV).Imply(monAtA.Apply(op, eV))).Core())
	serveThm(e.ctx, "zz_read_proj", core.TestThm(projection.Conclusion()))
	law := statedDep{name: "zz_read_law", stated: e.law}
	proj := statedDep{name: "zz_read_proj", stated: projection}

	opInd := MakeFun(TypeInd, MakeFun(TypeInd, TypeInd))
	grpAtInd := e.ctx.Const("readGrp", MakeFun(opInd, MakeFun(TypeInd, TypeBool)))
	monAtInd := e.ctx.Const("readMon", MakeFun(opInd, MakeFun(TypeInd, TypeBool)))
	x := Var("x", TypeInd)
	identity := ext.ForAll(x)(e.plus.Apply(e.zero, x).Eq(x)).Core()
	sec := e.ctx.Section(prop.MakeProp(grpAtInd.Apply(e.plus, e.zero).Imply(e.plus.Apply(e.zero, e.a).Eq(e.a)).Core()))
	sec.Do(Derive(func(arg *Argument) {
		group := arg.Assume()
		inner := Read(proj, group)
		content, ok := instanceContent(inner)
		require.True(t, ok, "the projection's reading states its conclusion at the group's content")
		require.True(t, content.AlphaEquals(monAtInd.Apply(e.plus, e.zero).Core()), "reads %s", ext.PrintTerm(content))
		outer := Read(law, inner)
		content, ok = instanceContent(outer)
		require.True(t, ok, "the law's reading at the reading states its body at the monoid")
		require.True(t, content.AlphaEquals(identity), "reads %s", ext.PrintTerm(content))
		_, ok = instanceContent(Read(depName("zz_read_proj"), group))
		require.False(t, ok, "a law named by a bare name states nothing before the proof runs")
		arg.Show("the identity law read at the monoid read at the group", By(outer))
	}))
	require.True(t, sec.Proved())
}

// The nested reading serves a Simp as a rule under the group, with no
// second rule beside it.
func TestRead_AtAReadingServesSimp(t *testing.T) {
	e := makeReadingTestEnv()
	opA := MakeFun(core.TypeA(), MakeFun(core.TypeA(), core.TypeA()))
	grpA := MakeFun(opA, MakeFun(core.TypeA(), TypeBool))
	e.ctx.Env.ProofService.LoadOrStoreConstMeta(core.MakeConstMeta("readGrp", grpA))
	op := Var("op", opA)
	eV := Var("e", core.TypeA())
	monAtA := e.ctx.Const("readMon", MakeFun(opA, MakeFun(core.TypeA(), TypeBool)))
	grpAtA := e.ctx.Const("readGrp", grpA)
	serveThm(e.ctx, "zz_read_proj", core.TestThm(ext.ForAll(op, eV)(grpAtA.Apply(op, eV).Imply(monAtA.Apply(op, eV))).Core()))
	opInd := MakeFun(TypeInd, MakeFun(TypeInd, TypeInd))
	grpAtInd := e.ctx.Const("readGrp", MakeFun(opInd, MakeFun(TypeInd, TypeBool)))
	sec := e.ctx.Section(prop.MakeProp(grpAtInd.Apply(e.plus, e.zero).Imply(e.Q.Apply(e.plus.Apply(e.zero, e.a))).Core()))
	sec.Do(StripImp())
	group := ResidentHyp(grpAtInd.Apply(e.plus, e.zero).Core())
	sec.Do(Simp(Fwd(Read(depName("zz_read_law"), Read(depName("zz_read_proj"), group)))))
	leaves := sec.UnsolvedLeaves()
	require.Len(t, leaves, 1)
	require.True(t, leaves[0].Goal.Conclusion().AlphaEquals(e.Q.Apply(e.a).Core()),
		"the rule fired under the group: %s", prop.PrintProp(leaves[0].Goal))
}

// A reading whose conclusion IS the goal closes the leaf by its own
// certificate — the projection read at the resident group proves the
// sub-structure outright — and the hypothesis the engine keeps beside
// the reading is not reported as an unused premise.
func TestRead_ByAReadingThatIsTheGoal(t *testing.T) {
	e := makeReadingTestEnv()
	opA := MakeFun(core.TypeA(), MakeFun(core.TypeA(), core.TypeA()))
	grpA := MakeFun(opA, MakeFun(core.TypeA(), TypeBool))
	e.ctx.Env.ProofService.LoadOrStoreConstMeta(core.MakeConstMeta("readGrp", grpA))
	op := Var("op", opA)
	eV := Var("e", core.TypeA())
	monAtA := e.ctx.Const("readMon", MakeFun(opA, MakeFun(core.TypeA(), TypeBool)))
	grpAtA := e.ctx.Const("readGrp", grpA)
	serveThm(e.ctx, "zz_read_proj", core.TestThm(ext.ForAll(op, eV)(grpAtA.Apply(op, eV).Imply(monAtA.Apply(op, eV))).Core()))
	opInd := MakeFun(TypeInd, MakeFun(TypeInd, TypeInd))
	grpAtInd := e.ctx.Const("readGrp", MakeFun(opInd, MakeFun(TypeInd, TypeBool)))
	monAtInd := e.ctx.Const("readMon", MakeFun(opInd, MakeFun(TypeInd, TypeBool)))
	sec := e.ctx.Section(prop.MakeProp(grpAtInd.Apply(e.plus, e.zero).Imply(monAtInd.Apply(e.plus, e.zero)).Core()))
	sec.Do(Derive(func(arg *Argument) {
		group := arg.Assume()
		arg.Show("the group's monoid", By(Read(depName("zz_read_proj"), group)))
	}))
	require.True(t, sec.Proved())
}

// A law whose statement carries a type letter its structure does not
// bind — the index letter B of `∀f:(B → A). ∀y:B. op(e, f(y)) = f(y)`,
// beside the carrier A the instance fixes — read under a RESIDENT
// instance closes a goal at B := bool, bare (the apply rung pins the
// letter off the goal) and grounded (the tuple's types fix it). The
// reading's own sequent keeps B rigid, so the By reads it as the law
// beside the hypothesis (expandLooseReadings).
func TestRead_AtResidentFactWithALooseLetter(t *testing.T) {
	e := makeReadingTestEnv()
	typeB := core.MakeVarType("B")
	opA := MakeFun(core.TypeA(), MakeFun(core.TypeA(), core.TypeA()))
	monA := MakeFun(opA, MakeFun(core.TypeA(), TypeBool))
	op := Var("op", opA)
	unit := Var("e", core.TypeA())
	f := Var("f", MakeFun(typeB, core.TypeA()))
	y := Var("y", typeB)
	fy := ext.WrapTerm(f).Apply(y)
	law := ext.ForAll(op, unit)(e.ctx.Const("readMon", monA).Apply(op, unit).Imply(
		ext.ForAll(f, y)(ext.WrapTerm(op).Apply(unit, fy).Eq(fy))))
	serveThm(e.ctx, "zz_read_loose", core.TestThm(law.Core()))

	g := ext.WrapTerm(Var("g", MakeFun(TypeBool, TypeInd)))
	c := ext.WrapTerm(Var("c", TypeBool))
	body := e.plus.Apply(e.zero, g.Apply(c)).Eq(g.Apply(c))
	for _, grounded := range []bool{false, true} {
		sec := e.residentReadingGoal(body)
		sec.Do(Derive(func(arg *Argument) {
			inst := arg.Assume()
			reading := Read(depName("zz_read_loose"), inst)
			if grounded {
				reading = reading.At(g, c)
			}
			arg.Show("the identity law read under the instance, at the index type bool", By(reading))
		}))
		require.True(t, sec.Proved(), "grounded=%v", grounded)
	}
}

func TestRead_NestedResidentWitnessTypesKeepHypothesesRigid(t *testing.T) {
	e := makeReadingTestEnv()
	typeB := core.MakeVarType("B")
	opTy := MakeFun(core.TypeA(), MakeFun(core.TypeA(), core.TypeA()))
	op, unit, tag := Var("op", opTy), Var("e", core.TypeA()), Var("tag", typeB)
	mon := e.ctx.Const("readMon", MakeFun(opTy, MakeFun(core.TypeA(), TypeBool)))
	taggedTy := MakeFun(opTy, MakeFun(core.TypeA(), MakeFun(typeB, TypeBool)))
	e.ctx.Env.ProofService.LoadOrStoreConstMeta(core.MakeConstMeta("readTagged", taggedTy))
	tagged := e.ctx.Const("readTagged", taggedTy)
	projection := ext.ForAll(op, unit, tag)(tagged.Apply(op, unit, tag).Imply(mon.Apply(op, unit)))
	serveThm(e.ctx, "zz_read_tagged", core.TestThm(projection.Core()))
	f, y := Var("f", MakeFun(typeB, core.TypeA())), Var("y", typeB)
	fy := ext.WrapTerm(f).Apply(y)
	law := ext.ForAll(op, unit)(mon.Apply(op, unit).Imply(
		ext.ForAll(f, y)(ext.WrapTerm(op).Apply(unit, fy).Eq(fy))))
	serveThm(e.ctx, "zz_read_nested_loose", core.TestThm(law.Core()))
	g, c := ext.WrapTerm(Var("g", f.Type())), ext.WrapTerm(Var("c", typeB))
	hyp := tagged.Apply(op, unit, tag)
	body := ext.WrapTerm(op).Apply(unit, g.Apply(c)).Eq(g.Apply(c))
	sec := e.ctx.Section(prop.MakeProp(hyp.Imply(body).Core()))
	sec.Do(Derive(func(arg *Argument) {
		group := arg.Assume()
		nested := Read(depName("zz_read_nested_loose"), Read(depName("zz_read_tagged"), group))
		resolved := resolveLemmaTarget("test", e.ctx, nested)
		hasLoose := func(v core.VarType) bool { return v.Name() == "♭B" }
		require.True(t, ext.TermAnyTypeVar(resolved.Conclusion(), hasLoose))
		adapted, _, err := ReadingAtWitnessTypes(resolved, []Term{g.Core(), c.Core()})
		require.NoError(t, err)
		require.True(t, adapted.Hyp(0).AlphaEquals(hyp.Core()))
		require.False(t, ext.TermAnyTypeVar(adapted.Conclusion(), hasLoose))
		bad := Var("bad", MakeFun(TypeBool, TypeBool))
		_, _, err = ReadingAtWitnessTypes(resolved, []Term{bad, Var("badY", TypeBool)})
		require.ErrorContains(t, err, "hypothesis types fixed")
		arg.Show("the nested reading at the witness types", By(nested.At(g, c)))
	}))
	require.True(t, sec.Proved())
}

func TestRead_SuccessiveBundlesKeepSharedComponentsAndHypotheses(t *testing.T) {
	e := makeReadingTestEnv()
	opTy := core.MakeFun(core.TypeA(), core.MakeFun(core.TypeA(), core.TypeA()))
	op, next, zero, x := Var("op", opTy), Var("next", opTy), Var("zero", core.TypeA()), Var("x", core.TypeA())
	mon := e.ctx.Const("readMon", core.MakeFun(opTy, core.MakeFun(core.TypeA(), core.TypeBool())))
	law := ext.ForAll(op, zero)(mon.Apply(op, zero).Imply(ext.ForAll(next)(mon.Apply(next, zero).Imply(ext.ForAll(x)(ext.WrapTerm(op).Apply(zero, x).Eq(ext.WrapTerm(next).Apply(zero, x)))))))
	serveThm(e.ctx, "zz_read_two", core.TestThm(law.Core()))
	other := ext.WrapTerm(Var("other", e.plus.Type()))
	mono := e.ctx.Const("readMon", core.MakeFun(e.plus.Type(), core.MakeFun(TypeInd, core.TypeBool())))
	first, second := mono.Apply(e.plus, e.zero), mono.Apply(other, e.zero)
	wanted := e.plus.Apply(e.zero, e.a).Eq(other.Apply(e.zero, e.a))
	sec := e.ctx.Section(prop.MakeProp(first.Imply(second.Imply(wanted)).Core()))
	sec.Do(Derive(func(a *Argument) {
		one, two := a.Assume(), a.Assume()
		read := Read(depName("zz_read_two"), one, two)
		resolved := resolveLemmaTarget("test", e.ctx, read)
		require.Equal(t, 2, resolved.NumHyps())
		a.Show("the law at both bundles", By(read.At(e.a)))
	}))
	require.True(t, sec.Proved())
	// The next bundle may share every component, with no binders left.
	shared := ext.ForAll(op, zero)(mon.Apply(op, zero).Imply(mon.Apply(op, zero).Imply(ext.ForAll(x)(ext.WrapTerm(op).Apply(zero, x).Eq(x)))))
	serveThm(e.ctx, "zz_read_shared", core.TestThm(shared.Core()))
	duplicate := Read(depName("zz_read_shared"), depName("zz_read_inst"), depName("zz_read_inst"))
	sharedResult := resolveLemmaTarget("test", e.ctx, duplicate)
	require.Zero(t, sharedResult.NumHyps())
	require.True(t, sharedResult.Conclusion().AlphaEquals(ext.ForAll(Var("x", TypeInd))(e.plus.Apply(e.zero, Var("x", TypeInd)).Eq(Var("x", TypeInd))).Core()))
	// Closed polymorphic instances also keep shared components fixed.
	serveThm(e.ctx, "zz_read_poly_inst", core.TestThm(mon.Apply(op, zero).Core()))
	polyRead := Read(depName("zz_read_shared"), depName("zz_read_poly_inst"), depName("zz_read_poly_inst"))
	polyResult := resolveLemmaTarget("test", e.ctx, polyRead)
	require.Zero(t, polyResult.NumHyps())
	require.True(t, polyResult.Conclusion().AlphaEquals(ext.ForAll(x)(ext.WrapTerm(op).Apply(zero, x).Eq(x)).Core()))
	// A later instance cannot change a type fixed by a resident hypothesis.
	partial, err := readLawAt(e.ctx.Dep(depName("zz_read_two")), core.Assume(first.Core()), nil)
	require.NoError(t, err)
	boolOp := Var("boolOp", core.MakeFun(core.TypeBool(), core.MakeFun(core.TypeBool(), core.TypeBool())))
	boolZero := Var("boolZero", core.TypeBool())
	boolMon := e.ctx.Const("readMon", core.MakeFun(boolOp.Type(), core.MakeFun(core.TypeBool(), core.TypeBool())))
	_, err = readLawAt(partial, core.Assume(boolMon.Apply(boolOp, boolZero).Core()), nil)
	require.Error(t, err)
}

func TestRead_NestedBareAfterResidentAndClosedBundles(t *testing.T) {
	e := makeReadingTestEnv()
	typeB := core.MakeVarType("B")
	opTy := MakeFun(core.TypeA(), MakeFun(core.TypeA(), core.TypeA()))
	op, unit := Var("op", opTy), Var("e", core.TypeA())
	mon := e.ctx.Const("readMon", MakeFun(opTy, MakeFun(core.TypeA(), TypeBool)))
	structure := mon.Apply(op, unit)
	next := Var("next", opTy)
	projection := ext.ForAll(op, unit)(structure.Imply(ext.ForAll(next)(mon.Apply(next, unit).Imply(structure))))
	serveThm(e.ctx, "zz_read_two_projection", core.TestThm(projection.Core()))
	f, y := Var("f", MakeFun(typeB, core.TypeA())), Var("y", typeB)
	fy := ext.WrapTerm(f).Apply(y)
	law := ext.ForAll(op, unit)(structure.Imply(
		ext.ForAll(f, y)(ext.WrapTerm(op).Apply(unit, fy).Eq(fy))))
	serveThm(e.ctx, "zz_read_nested_two_loose", core.TestThm(law.Core()))
	g := ext.WrapTerm(Var("g", MakeFun(TypeBool, TypeInd)))
	c := ext.WrapTerm(Var("c", TypeBool))
	other := ext.WrapTerm(Var("other", e.plus.Type()))
	mono := e.ctx.Const("readMon", MakeFun(e.plus.Type(), MakeFun(TypeInd, TypeBool)))
	hyp := mono.Apply(other, e.zero)
	body := other.Apply(e.zero, g.Apply(c)).Eq(g.Apply(c))
	sec := e.ctx.Section(prop.MakeProp(hyp.Imply(body).Core()))
	sec.Do(Derive(func(arg *Argument) {
		resident := arg.Assume()
		inner := Read(depName("zz_read_two_projection"), resident, depName("zz_read_inst"))
		resolved := resolveLemmaTarget("test", e.ctx, inner)
		require.Equal(t, 1, resolved.NumHyps())
		require.True(t, resolved.Hyp(0).AlphaEquals(resolved.Conclusion()))
		arg.Show("the loose law after resident and closed bundles", By(Read(depName("zz_read_nested_two_loose"), inner)))
	}))
	require.True(t, sec.Proved())
}

// A closure law read at one point twice in a By — the shape a member's
// evidence takes when two cites carry it: `EvalScalar.At(cInverse, …)`
// and `MulRightZeroOn.At(cInverse)` each list `InvIn.Read(L).At(c)`,
// the reading that establishes cInverse. The second grounding finds
// its consequent resident from the first, and its guard is discharged
// into it all the same.
func TestRead_GuardedLawAtOnePointTwiceInOneBy(t *testing.T) {
	e := makeReadingTestEnv()
	opA := MakeFun(core.TypeA(), MakeFun(core.TypeA(), core.TypeA()))
	monA := MakeFun(opA, MakeFun(core.TypeA(), TypeBool))
	e.ctx.Env.ProofService.LoadOrStoreConstMeta(core.MakeConstMeta("readG", MakeFun(core.TypeA(), TypeBool)))
	op, unit, x := Var("op", opA), Var("e", core.TypeA()), Var("x", core.TypeA())
	gA := e.ctx.Const("readG", MakeFun(core.TypeA(), TypeBool))
	law := ext.ForAll(op, unit)(e.ctx.Const("readMon", monA).Apply(op, unit).Imply(
		ext.ForAll(x)(gA.Apply(x).Imply(gA.Apply(ext.WrapTerm(op).Apply(unit, x))))))
	serveThm(e.ctx, "zz_read_guarded", core.TestThm(law.Core()))

	g := e.ctx.Const("readG", MakeFun(TypeInd, TypeBool))
	f := ext.WrapTerm(Var("f", MakeFun(TypeInd, TypeInd)))
	point := f.Apply(e.a)
	mono := e.ctx.Const("readMon", MakeFun(e.plus.Type(), MakeFun(TypeInd, TypeBool)))
	sec := e.ctx.Section(prop.MakeProp(mono.Apply(e.plus, e.zero).Imply(
		g.Apply(point).Imply(g.Apply(e.plus.Apply(e.zero, point)))).Core()))
	sec.Do(Derive(func(arg *Argument) {
		inst := arg.Assume()
		guard := arg.Assume()
		reading := Read(depName("zz_read_guarded"), inst)
		arg.Show("the law read under the instance, at the point twice", By(guard, reading.At(point), reading.At(point)))
	}))
	require.True(t, sec.Proved())
}

// A coefficient on a BARE reading reaches the scaling phase: the
// reading is the derived premise, asserted and resident, and the
// coefficient scales what it states. The law here states a ∀-fact at
// ind, which no arithmetic carrier owns, so the scaling REFUSES —
// naming the premise and what it read — where a dropped coefficient
// would have run the closer on the unscaled fact without a word.
func TestRead_ScaledBareReadingIsScaled(t *testing.T) {
	e := makeReadingTestEnv()
	sec := e.residentReadingGoal(e.Q.Apply(e.zero))
	defer func() {
		r := recover()
		require.NotNil(t, r, "the coefficient on a bare reading must reach the scaling phase")
		msg := sprintAny(r)
		require.Contains(t, msg, "is scaled by")
		require.Contains(t, msg, "not an equation at a carrier the arithmetic layers own")
	}()
	sec.Do(Derive(func(arg *Argument) {
		inst := arg.Assume()
		arg.Show("a scaled bare reading", ByArith(Scaled(e.a, Read(depName("zz_read_law"), inst))))
	}))
	t.Fatal("unreachable")
}

// The economy audit's probe that drops the hypothesis a reading
// located leaves the reading's certificate standing on a fact the leaf
// no longer holds: the premise fails to materialize, and the probe reads
// the drop as not inert — measured on complete_metric
// CompactImpSequential (`BySets(kM, BallOpen.Read(metric))`), where the
// materialization reached the kernel step and its invariant panicked
// the record.
func TestRead_AuditProbeDroppingTheLocatedFact(t *testing.T) {
	e := makeReadingTestEnv()
	var findings []string
	e.ctx.Env.ByAuditReport = func(f string) { findings = append(findings, f) }
	x := Var("x", TypeInd)
	sec := e.residentReadingGoal(ext.ForAll(x)(e.plus.Apply(e.zero, x).Eq(x)))
	ok := provesInHand(t, func() *GoalStackNode {
		sec.Do(Derive(func(arg *Argument) {
			inst := arg.Assume()
			arg.Show("the law read under the resident instance", BySets(Read(depName("zz_read_law"), inst)))
		}))
		return sec
	})
	require.True(t, ok != nil && sec.Proved())
	for _, f := range findings {
		require.NotContains(t, f, "inert", "the located fact is no inert premise: %s", f)
	}
}
