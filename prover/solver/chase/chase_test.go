package chase

// The closer over a FABRICATED algebra: the structure predicates and
// the set vocabulary are test constants at one element type, every law
// a statement-correct stand-in (core.TestThm, the solver packages'
// fabricator convention). Under test is the chase — the reading of a
// leaf, the lattice decisions, the rounds, and the certificates'
// composition against the kernel — not the laws, which the serve
// binding test checks against the corpus.

import (
	"github.com/euc-ai/xugo/prover/solver/omega"
	"strings"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/stretchr/testify/require"
)

type _FakeWorld struct {
	records                                             *_RecordWorld
	S, T                                                core.HolType // the ring's and the modules' element types
	setT, groupType                                     core.HolType
	mkGroup, groupMul, groupOne, groupInv, groupCarrier core.Term
	exactAt, submodule                                  core.Term
	image, kernel                                       core.Term
	coset, subgroup                                     core.Term
	injectiveOn                                         core.Term
	groupOn, abelianOn                                  core.Term
	subset, member                                      core.Term
	radd, rzero, rneg                                   core.Term // the ring's operations
	rmul, rone, rsub, R                                 core.Term
	add, zero, neg                                      core.Term // the modules' shared operations
	smul                                                core.Term
	laws                                                *Laws
}

// defConst mints a constant of the given argument and result types whose
// body is constantly true (a set-valued result is the set of everything).
func defConst(name string, args []core.HolType, result core.HolType) core.Term {
	vars := make([]core.VarTerm, len(args))
	for i, ty := range args {
		vars[i] = core.Var(core.TermName("a"+string(rune('0'+i))), ty)
	}
	var body core.Term = ext.T
	if flat := ext.MatchesFun(result); len(flat) == 2 {
		body = core.Abs(core.Var("y", flat[0]), ext.T)
	}
	for i := len(vars) - 1; i >= 0; i-- {
		body = core.Abs(vars[i], body)
	}
	return core.NewConstDef(body, core.TermName(name))
}

func newFakeWorld() *_FakeWorld { return newRecordWorld()._FakeWorld }

func newFakeWorldBase() *_FakeWorld {
	S, T := core.MakeVarType("S"), core.MakeVarType("T")
	setS, setT := core.MakeFun(S, core.TypeBool()), core.MakeFun(T, core.TypeBool())
	SS := core.MakeFun(S, S)
	SSS := core.MakeFun(S, SS)
	TT := core.MakeFun(T, T)
	TTT := core.MakeFun(T, TT)
	STT := core.MakeFun(S, TT)
	w := &_FakeWorld{S: S, T: T, setT: setT}
	w.groupType = core.MakeCompositeType(core.MakeMetaType("zz_group_ops_chase", 1), T)
	w.mkGroup = opaqueRecordConst("zz_mk_group_chase", []core.HolType{TTT, T, TT, setT}, w.groupType)
	w.groupMul = opaqueRecordConst("zz_group_mul_chase", []core.HolType{w.groupType}, TTT)
	w.groupOne = opaqueRecordConst("zz_group_one_chase", []core.HolType{w.groupType}, T)
	w.groupInv = opaqueRecordConst("zz_group_inv_chase", []core.HolType{w.groupType}, TT)
	w.groupCarrier = opaqueRecordConst("zz_group_carrier_chase", []core.HolType{w.groupType}, setT)
	w.exactAt = defConst(exactAtName, []core.HolType{T, setT, setT, TT, TT}, core.TypeBool())
	w.image = defConst(imageName, []core.HolType{TT, setT}, setT)
	w.kernel = defConst(kernelName, []core.HolType{T, setT, TT}, setT)
	w.coset = defConst(leftCosetName, []core.HolType{TTT, T, setT}, setT)
	w.subgroup = defConst(subgroupName, []core.HolType{w.groupType, setT}, core.TypeBool())
	w.groupOn = defConst(groupOnName, []core.HolType{w.groupType}, core.TypeBool())
	w.abelianOn = defConst(abelianGroupOnName, []core.HolType{w.groupType}, core.TypeBool())
	w.subset = defConst(subsetName, []core.HolType{setT, setT}, core.TypeBool())
	w.injectiveOn = defConst(injectiveOnName, []core.HolType{setT, TT}, core.TypeBool())
	// `∈` is one polymorphic constant, as the corpus's set_member is: the
	// closer identifies a membership by its meta at every type.
	MA := core.MakeVarType("MA")
	w.member = defConst("zz_member_chase_test", []core.HolType{MA, core.MakeFun(MA, core.TypeBool())}, core.TypeBool())
	v := func(name string, ty core.HolType) core.Term { return core.Var(core.TermName(name), ty) }
	w.radd, w.rzero, w.rneg, w.rmul, w.rone, w.rsub, w.R = v("radd", SSS), v("rzero", S), v("rneg", SS), v("rmul", SSS), v("rone", S), v("rsub", SSS), v("R", setS)
	w.add, w.zero, w.neg, w.smul = v("add", TTT), v("zero", T), v("neg", TT), v("smul", STT)
	w.laws = w.fabricateLaws()
	gmul, gone, ginv, gc := v("gmul", TTT), v("gone", T), v("ginv", TT), v("gc", setT)
	parts := []core.Term{gmul, gone, ginv, gc}
	packed := w.ap(w.mkGroup, parts...)
	var projections []prop.Rewrite
	for i, selector := range []core.Term{w.groupMul, w.groupOne, w.groupInv, w.groupCarrier} {
		projections = append(projections, recordDefinition(thm(all(parts, eq(w.ap(selector, packed), parts[i])))))
	}
	w.laws.NormalizeWith = func(omega.LibraryRead) prop.Rewrite { return prop.DeepRewrite(projections...) }
	return w
}

func (w *_FakeWorld) ap(f core.Term, args ...core.Term) core.Term { return ext.Apply(f, args...) }

// in is `x ∈ s`, the membership constant instantiated at x's type.
func (w *_FakeWorld) in(x, s core.Term) core.Term {
	c, _ := w.member.AsConst()
	member := core.MakeConstTerm(c.Meta(), core.MakeFun(x.Type(), core.MakeFun(s.Type(), core.TypeBool())))
	return w.ap(member, x, s)
}

func wrap(t core.Term) *ext.TermWrapper { return ext.WrapTerm(t) }

func dslNum() core.HolType { return dsl.NumType }

func imp(a, b core.Term) core.Term { return wrap(a).Imply(b).Core() }
func and(a, b core.Term) core.Term { return wrap(a).And(b).Core() }
func eq(a, b core.Term) core.Term  { return core.Eq(a, b) }
func iff(a, b core.Term) core.Term { return core.Eq(a, b) }
func all(vars []core.Term, body core.Term) core.Term {
	return ext.ForAll(vars...)(body).Core()
}
func thm(t core.Term) *prop.PropWrapper { return prop.WrapProp(core.TestThm(t)) }

// fabricateLaws states the group and set laws in the chapters' stated
// shapes; _RecordWorld supplies the module, submodule and homomorphism
// laws, stated over the records.
func (w *_FakeWorld) fabricateLaws() *Laws {
	T, setT := w.T, w.setT
	v := func(name string, ty core.HolType) core.Term { return core.Var(core.TermName(name), ty) }
	TT := core.MakeFun(T, T)
	M, M_ := v("M", setT), v("M'", setT)
	x, y, z, e := v("x", T), v("y", T), v("z", T), v("e", T)
	// The group's operations are projections of its single record subject.
	G := v("G", w.groupType)
	gmul, gone, ginv, gc := w.ap(w.groupMul, G), w.ap(w.groupOne, G), w.ap(w.groupInv, G), w.ap(w.groupCarrier, G)
	groupComps := []core.Term{G}
	group := w.ap(w.groupOn, groupComps...)
	groupLaw := func(body core.Term) *prop.PropWrapper { return thm(all(groupComps, imp(group, body))) }
	inC := func(t core.Term) core.Term { return w.in(t, gc) }
	gm := func(a, b core.Term) core.Term { return w.ap(gmul, a, b) }
	gi := func(a core.Term) core.Term { return w.ap(ginv, a) }
	abelian := w.ap(w.abelianOn, groupComps...)
	abelianLaw := func(body core.Term) *prop.PropWrapper { return thm(all(groupComps, imp(abelian, body))) }
	comm := all([]core.Term{x, y}, imp(and(inC(x), inC(y)), eq(gm(x, y), gm(y, x))))
	f := v("f", TT)
	fa := func(t core.Term) core.Term { return w.ap(f, t) }
	g, s, h := v("g", TT), v("s", setT), v("h", setT)
	return &Laws{
		AbelianGroupOnDef: thm(all(groupComps, iff(abelian, and(group, comm)))),
		NegAdd:            abelianLaw(all([]core.Term{x, y}, imp(and(inC(x), inC(y)), eq(gi(gm(x, y)), gm(gi(x), gi(y)))))),

		OneIn:           groupLaw(inC(gone)),
		MulIn:           groupLaw(all([]core.Term{x, y}, imp(and(inC(x), inC(y)), inC(gm(x, y))))),
		InvIn:           groupLaw(all([]core.Term{x}, imp(inC(x), inC(gi(x))))),
		Assoc:           groupLaw(all([]core.Term{x, y, z}, imp(and(inC(x), and(inC(y), inC(z))), eq(gm(x, gm(y, z)), gm(gm(x, y), z))))),
		LeftIdentity:    groupLaw(all([]core.Term{x}, imp(inC(x), eq(gm(gone, x), x)))),
		RightIdentity:   groupLaw(all([]core.Term{x}, imp(inC(x), eq(gm(x, gone), x)))),
		LeftInverse:     groupLaw(all([]core.Term{x}, imp(inC(x), eq(gm(gi(x), x), gone)))),
		RightInverse:    groupLaw(all([]core.Term{x}, imp(inC(x), eq(gm(x, gi(x)), gone)))),
		InvInv:          groupLaw(all([]core.Term{x}, imp(inC(x), eq(gi(gi(x)), x)))),
		InvOne:          groupLaw(eq(gi(gone), gone)),
		IdempotentIsOne: groupLaw(all([]core.Term{e}, imp(inC(e), imp(eq(gm(e, e), e), eq(e, gone))))),
		InvUnique:       groupLaw(all([]core.Term{x, y}, imp(and(inC(x), inC(y)), iff(eq(gm(x, y), gone), eq(x, gi(y)))))),
		LeftCosetEq: groupLaw(all([]core.Term{x, y, h}, imp(and(inC(x), and(inC(y), w.ap(w.subgroup, G, h))),
			iff(eq(w.ap(w.coset, gmul, x, h), w.ap(w.coset, gmul, y, h)), w.in(gm(gi(x), y), h))))),

		ExactAtDef: thm(all([]core.Term{e, M, M_, f, g}, iff(w.ap(w.exactAt, e, M, M_, f, g), eq(w.ap(w.image, f, M), w.ap(w.kernel, e, M_, g))))),
		InImage: thm(all([]core.Term{f, s, y}, iff(w.in(y, w.ap(w.image, f, s)),
			ext.Exists(x)(and(eq(y, fa(x)), w.in(x, s))).Core()))),
		InKernel:       thm(all([]core.Term{e, s, f, x}, iff(w.in(x, w.ap(w.kernel, e, s, f)), and(w.in(x, s), eq(fa(x), e))))),
		SubgroupSubset: thm(all([]core.Term{G, h}, imp(w.ap(w.subgroup, G, h), w.ap(w.subset, h, gc)))),
		SubsetDef:      thm(all([]core.Term{s, h}, iff(w.ap(w.subset, s, h), all([]core.Term{x}, imp(w.in(x, s), w.in(x, h)))))),
		InjectiveOnDef: thm(all([]core.Term{s, f}, iff(w.ap(w.injectiveOn, s, f),
			all([]core.Term{x, y}, imp(and(w.in(x, s), and(w.in(y, s), eq(fa(x), fa(y)))), eq(x, y)))))),
		Extension: thm(all([]core.Term{s, h}, iff(eq(s, h), all([]core.Term{x}, iff(w.in(x, s), w.in(x, h)))))),
	}
}

func installFake(t *testing.T) *_FakeWorld {
	t.Helper()
	w := newFakeWorld()
	SetLaws(w.laws)
	t.Cleanup(func() { SetLaws(nil) })
	return w
}

// ── a concrete diagram's vocabulary ─────────────────────────────────────────

func (w *_FakeWorld) set(name string) core.Term  { return core.Var(core.TermName(name), w.setT) }
func (w *_FakeWorld) elem(name string) core.Term { return core.Var(core.TermName(name), w.T) }
func (w *_FakeWorld) fn(name string) core.Term {
	return core.Var(core.TermName(name), core.MakeFun(w.T, w.T))
}

// module is module_on(R, M) at the modules' shared operations packed
// over the carrier M.
func (w *_FakeWorld) module(M core.Term) core.Term {
	return w.ap(w.records.moduleOn, w.records.ring, w.records.packed(M))
}
func (w *_FakeWorld) homOf(f, M, N core.Term) core.Term {
	return w.records.homRecord(f, w.records.packed(M), w.records.packed(N))
}
func (w *_FakeWorld) exact(A, B, g, f core.Term) core.Term {
	return w.ap(w.exactAt, w.zero, A, B, g, f)
}
func (w *_FakeWorld) plus(a, b core.Term) core.Term     { return w.ap(w.add, a, b) }
func (w *_FakeWorld) minus(a core.Term) core.Term       { return w.ap(w.neg, a) }
func (w *_FakeWorld) imageOf(f, A core.Term) core.Term  { return w.ap(w.image, f, A) }
func (w *_FakeWorld) kernelOf(B, g core.Term) core.Term { return w.ap(w.kernel, w.zero, B, g) }
func (w *_FakeWorld) cosetOf(x, N core.Term) core.Term  { return w.ap(w.coset, w.add, x, N) }
func (w *_FakeWorld) submoduleOf(M, N core.Term) core.Term {
	return w.ap(w.submodule, w.records.ring, w.records.packed(M), N)
}
func (w *_FakeWorld) onto(f, A, B core.Term) core.Term       { return eq(w.imageOf(f, A), B) }
func (w *_FakeWorld) injectiveOnOf(f, A core.Term) core.Term { return w.ap(w.injectiveOn, A, f) }
func (w *_FakeWorld) oneToOne(f, A core.Term) core.Term {
	u, v := w.elem("u"), w.elem("v")
	return all([]core.Term{u, v}, imp(and(and(w.in(u, A), w.in(v, A)), eq(w.ap(f, u), w.ap(f, v))), eq(u, v)))
}

// law is ∀u. u ∈ A ⇒ l(u) = r(u).
func (w *_FakeWorld) law(A core.Term, l, r func(core.Term) core.Term) core.Term {
	u := w.elem("u")
	return all([]core.Term{u}, imp(w.in(u, A), eq(l(u), r(u))))
}

// preimage is ∃q. t = f(q) ∧ q ∈ A, the bound name one no test's element
// carries.
func preimage(w *_FakeWorld, f, A, t core.Term) core.Term {
	q := w.elem("q")
	return ext.Exists(q)(and(eq(t, w.ap(f, q)), w.in(q, A))).Core()
}

// closes runs the chase and checks the theorem closes the goal.
func closes(t *testing.T, goal core.Prop, depth int) Result {
	t.Helper()
	thm, res, err := Close(goal, Options{Depth: depth})
	require.NoError(t, err)
	require.NotNil(t, thm, "the chase did not close the goal:\n%s", res.Report)
	require.True(t, prop.IsStronger(thm, goal), "the certificate does not close the goal: %s", prop.PrintProp(thm))
	return res
}

func fails(t *testing.T, goal core.Prop, depth int) string {
	t.Helper()
	thm, res, err := Close(goal, Options{Depth: depth})
	require.NoError(t, err)
	require.Nil(t, thm, "the chase closed a goal it must not")
	return res.Report
}

// ── tests ───────────────────────────────────────────────────────────────────

func TestChase_NormalizerCommutesAndCancels(t *testing.T) {
	w := installFake(t)
	M := w.set("M")
	x, y := w.elem("x"), w.elem("y")
	hyps := []core.Term{w.module(M), w.in(x, M), w.in(y, M)}
	closes(t, core.MakeProp(eq(w.plus(x, y), w.plus(y, x)), hyps...), 0)
	closes(t, core.MakeProp(eq(w.plus(w.plus(x, y), w.minus(x)), y), hyps...), 0)
	closes(t, core.MakeProp(eq(w.minus(w.plus(x, w.minus(y))), w.plus(y, w.minus(x))), hyps...), 0)
	closes(t, core.MakeProp(eq(w.plus(x, w.zero), w.plus(w.zero, x)), hyps...), 0)
}

func TestChase_TorsionIsRespected(t *testing.T) {
	w := installFake(t)
	M := w.set("M")
	x := w.elem("x")
	twice := w.plus(x, x)
	hyps := []core.Term{w.module(M), w.in(x, M), eq(twice, w.zero)}
	closes(t, core.MakeProp(eq(w.plus(twice, twice), w.zero), hyps...), 0)
	report := fails(t, core.MakeProp(eq(x, w.zero), hyps...), 2)
	require.Contains(t, report, "not an integer combination")
}

func TestChase_HomomorphismIsLinear(t *testing.T) {
	w := installFake(t)
	M, N := w.set("M"), w.set("N")
	f := w.fn("f")
	x, y := w.elem("x"), w.elem("y")
	hyps := []core.Term{w.module(M), w.module(N), w.homOf(f, M, N), w.in(x, M), w.in(y, M)}
	closes(t, core.MakeProp(eq(w.ap(f, w.plus(x, w.minus(y))), w.plus(w.ap(f, x), w.minus(w.ap(f, y)))), hyps...), 0)
	closes(t, core.MakeProp(eq(w.ap(f, w.zero), w.zero), hyps...), 0)
	closes(t, core.MakeProp(w.in(w.ap(f, w.plus(x, y)), N), hyps...), 0)
}

// A homomorphism spelled as a lambda is read like a named one: the
// certificate spells its applications unreduced, as the homomorphism
// laws do, and reads each image through its beta bridge.
func TestChase_LambdaHomomorphismIsLinear(t *testing.T) {
	w := installFake(t)
	M, N := w.set("M"), w.set("N")
	g := w.fn("g")
	v := w.elem("v").(core.VarTerm)
	lambda := core.Abs(v, w.ap(g, v))
	x, y := w.elem("x"), w.elem("y")
	hyps := []core.Term{w.module(M), w.module(N), w.homOf(lambda, M, N), w.in(x, M), w.in(y, M)}
	closes(t, core.MakeProp(eq(w.ap(lambda, w.plus(x, w.minus(y))), w.plus(w.ap(lambda, x), w.minus(w.ap(lambda, y)))), hyps...), 0)
	closes(t, core.MakeProp(eq(w.ap(lambda, w.zero), w.zero), hyps...), 0)
}

// _Snake is the connecting homomorphism's diagram: the short exact
// sequence A' → B → C at degree n (i, p), B1 → B and C1 → C the
// boundaries down from degree n + 1, A' → A0 and B → B0 the boundaries
// down from degree n, and the squares.
type _Snake struct {
	w                            *_FakeWorld
	A_, B, C, B1, C1, A0, B0     core.Term
	i, p, d, d__, p1, d_, i0, d0 core.Term
	facts                        []core.Term
}

func newSnake(w *_FakeWorld) *_Snake {
	s := &_Snake{w: w,
		A_: w.set("A'"), B: w.set("B"), C: w.set("C"), B1: w.set("B1"), C1: w.set("C1"), A0: w.set("A0"), B0: w.set("B0"),
		i: w.fn("i"), p: w.fn("p"), d: w.fn("d"), d__: w.fn("d''"), p1: w.fn("p1"), d_: w.fn("d'"), i0: w.fn("i0"), d0: w.fn("d0")}
	ap := w.ap
	s.facts = []core.Term{
		w.module(s.A_), w.module(s.B), w.module(s.C), w.module(s.B1), w.module(s.C1), w.module(s.A0), w.module(s.B0),
		w.homOf(s.i, s.A_, s.B), w.homOf(s.p, s.B, s.C), w.homOf(s.d, s.B1, s.B), w.homOf(s.d__, s.C1, s.C), w.homOf(s.p1, s.B1, s.C1),
		w.homOf(s.d_, s.A_, s.A0), w.homOf(s.i0, s.A0, s.B0), w.homOf(s.d0, s.B, s.B0),
		// p ∘ d = d'' ∘ p1 and i0 ∘ d' = d0 ∘ i
		w.law(s.B1, func(u core.Term) core.Term { return ap(s.p, ap(s.d, u)) }, func(u core.Term) core.Term { return ap(s.d__, ap(s.p1, u)) }),
		w.law(s.A_, func(u core.Term) core.Term { return ap(s.i0, ap(s.d_, u)) }, func(u core.Term) core.Term { return ap(s.d0, ap(s.i, u)) }),
		// d0 ∘ d = 0
		w.law(s.B1, func(u core.Term) core.Term { return ap(s.d0, ap(s.d, u)) }, func(core.Term) core.Term { return w.zero }),
		w.exact(s.A_, s.B, s.i, s.p),
		w.oneToOne(s.i0, s.A0),
	}
	return s
}

func TestChase_SnakePullBack(t *testing.T) {
	w := installFake(t)
	s := newSnake(w)
	z, u := w.elem("z"), w.elem("u")
	hyps := append(s.facts, w.in(z, s.C1), eq(w.ap(s.d__, z), w.zero), w.in(u, s.B1), eq(w.ap(s.p1, u), z))
	// d(u) is killed by p, so it is i(w) for some w of A'.
	goal := core.MakeProp(preimage(w, s.i, s.A_, w.ap(s.d, u)), hyps...)
	res := closes(t, goal, 1)
	require.Equal(t, 1, res.Rounds)
	report := fails(t, goal, 0)
	require.Contains(t, report, "not in the image")
	// The same as a membership in the image.
	closes(t, core.MakeProp(w.in(w.ap(s.d, u), w.imageOf(s.i, s.A_)), hyps...), 1)
}

func TestChase_SnakePullBackIsACycle(t *testing.T) {
	w := installFake(t)
	s := newSnake(w)
	u, v := w.elem("u"), w.elem("v")
	hyps := append(s.facts, w.in(u, s.B1), w.in(v, s.A_), eq(w.ap(s.i, v), w.ap(s.d, u)))
	// i0(d'(v)) = d0(i(v)) = d0(d(u)) = 0, and i0 is one-to-one.
	closes(t, core.MakeProp(eq(w.ap(s.d_, v), w.zero), hyps...), 1)
	fails(t, core.MakeProp(eq(w.ap(s.d_, v), w.zero), hyps...), 0)
}

// _FiveLemma is the two rows A4 → A3 → A2 → A1 → A0 and B4 → … → B0 with
// the vertical maps f4 … f0, exact where the four lemmas need it.
type _FiveLemma struct {
	w       *_FakeWorld
	A, B    [5]core.Term
	d, e, f [5]core.Term
	rows    []core.Term
}

func newFiveLemma(w *_FakeWorld) *_FiveLemma {
	fl := &_FiveLemma{w: w}
	names := []string{"0", "1", "2", "3", "4"}
	for k := 0; k < 5; k++ {
		fl.A[k], fl.B[k] = w.set("A"+names[k]), w.set("B"+names[k])
		fl.f[k] = w.fn("f" + names[k])
		if k > 0 {
			fl.d[k], fl.e[k] = w.fn("d"+names[k]), w.fn("e"+names[k])
		}
	}
	for k := 0; k < 5; k++ {
		fl.rows = append(fl.rows, w.module(fl.A[k]), w.module(fl.B[k]), w.homOf(fl.f[k], fl.A[k], fl.B[k]))
		if k > 0 {
			fl.rows = append(fl.rows, w.homOf(fl.d[k], fl.A[k], fl.A[k-1]), w.homOf(fl.e[k], fl.B[k], fl.B[k-1]))
			// the square f(k−1) ∘ d(k) = e(k) ∘ f(k)
			k := k
			fl.rows = append(fl.rows, w.law(fl.A[k],
				func(u core.Term) core.Term { return w.ap(fl.f[k-1], w.ap(fl.d[k], u)) },
				func(u core.Term) core.Term { return w.ap(fl.e[k], w.ap(fl.f[k], u)) }))
		}
		if k > 1 {
			k := k
			fl.rows = append(fl.rows,
				w.law(fl.A[k], func(u core.Term) core.Term { return w.ap(fl.d[k-1], w.ap(fl.d[k], u)) }, func(core.Term) core.Term { return w.zero }),
				w.law(fl.B[k], func(u core.Term) core.Term { return w.ap(fl.e[k-1], w.ap(fl.e[k], u)) }, func(core.Term) core.Term { return w.zero }))
		}
	}
	return fl
}

// exactAt is the row's exactness at degree k: im d(k+1) = ker d(k).
func (fl *_FiveLemma) exactAt(top bool, k int) core.Term {
	if top {
		return fl.w.exact(fl.A[k+1], fl.A[k], fl.d[k+1], fl.d[k])
	}
	return fl.w.exact(fl.B[k+1], fl.B[k], fl.e[k+1], fl.e[k])
}

func TestChase_FourLemmaInjective(t *testing.T) {
	w := installFake(t)
	fl := newFiveLemma(w)
	x, y := w.elem("x"), w.elem("y")
	hyps := append(append([]core.Term{}, fl.rows...),
		fl.exactAt(true, 3), fl.exactAt(true, 2), fl.exactAt(false, 3), fl.exactAt(false, 2),
		w.onto(fl.f[4], fl.A[4], fl.B[4]), w.oneToOne(fl.f[3], fl.A[3]), w.oneToOne(fl.f[1], fl.A[1]),
		w.in(x, fl.A[2]), w.in(y, fl.A[2]), eq(w.ap(fl.f[2], x), w.ap(fl.f[2], y)))
	goal := core.MakeProp(eq(x, y), hyps...)
	res := closes(t, goal, 3)
	require.Equal(t, 3, res.Rounds)
	report := fails(t, goal, 2)
	require.Contains(t, report, "did not close the goal after 2 round(s)")
}

func TestChase_FourLemmaSurjective(t *testing.T) {
	w := installFake(t)
	fl := newFiveLemma(w)
	z := w.elem("z")
	hyps := append(append([]core.Term{}, fl.rows...),
		fl.exactAt(true, 2), fl.exactAt(true, 1), fl.exactAt(false, 2), fl.exactAt(false, 1),
		w.onto(fl.f[3], fl.A[3], fl.B[3]), w.onto(fl.f[1], fl.A[1], fl.B[1]), w.oneToOne(fl.f[0], fl.A[0]),
		w.in(z, fl.B[2]))
	goal := core.MakeProp(preimage(w, fl.f[2], fl.A[2], z), hyps...)
	res := closes(t, goal, 4)
	require.LessOrEqual(t, res.Rounds, 4)
	fails(t, goal, res.Rounds-1)
}

func TestChase_FalseGoalStaysOpen(t *testing.T) {
	w := installFake(t)
	M := w.set("M")
	x, y := w.elem("x"), w.elem("y")
	hyps := []core.Term{w.module(M), w.in(x, M), w.in(y, M)}
	report := fails(t, core.MakeProp(eq(x, y), hyps...), 3)
	require.Contains(t, report, "not an integer combination")
	require.Contains(t, report, "nothing to pull back")
}

func TestChase_CosetEquationReducesToTheImage(t *testing.T) {
	w := installFake(t)
	M, A := w.set("M"), w.set("A")
	f := w.fn("f")
	x, a := w.elem("x"), w.elem("a")
	N := w.imageOf(f, A)
	y := w.plus(x, w.ap(f, a))
	hyps := []core.Term{w.module(M), w.module(A), w.homOf(f, A, M), w.submoduleOf(M, N), w.in(x, M), w.in(a, A)}
	closes(t, core.MakeProp(eq(w.cosetOf(x, N), w.cosetOf(y, N)), hyps...), 0)
	// And read as a hypothesis: two elements in one coset differ by an image.
	y2 := w.elem("y")
	hyps2 := []core.Term{w.module(M), w.module(A), w.homOf(f, A, M), w.submoduleOf(M, N), w.in(x, M), w.in(y2, M), eq(w.cosetOf(x, N), w.cosetOf(y2, N))}
	closes(t, core.MakeProp(preimage(w, f, A, w.plus(y2, w.minus(x))), hyps2...), 0)
}

func TestChase_KernelMembership(t *testing.T) {
	w := installFake(t)
	A, B, C := w.set("A"), w.set("B"), w.set("C")
	g, f := w.fn("g"), w.fn("f")
	a := w.elem("a")
	hyps := []core.Term{w.module(A), w.module(B), w.module(C), w.homOf(g, A, B), w.homOf(f, B, C), w.exact(A, B, g, f), w.in(a, A)}
	closes(t, core.MakeProp(eq(w.ap(f, w.ap(g, a)), w.zero), hyps...), 0)
	closes(t, core.MakeProp(w.in(w.ap(g, a), w.kernelOf(B, f)), hyps...), 0)
}

func TestChase_RefusesWithoutLaws(t *testing.T) {
	w := newFakeWorld()
	M := w.set("M")
	x := w.elem("x")
	_, _, err := Close(core.MakeProp(eq(x, x), w.module(M), w.in(x, M)), Options{Depth: 1})
	require.Error(t, err)
	require.Contains(t, err.Error(), "not installed")
}

func TestChase_RefusesACycle(t *testing.T) {
	w := installFake(t)
	M := w.set("M")
	f := w.fn("f")
	x := w.elem("x")
	_, _, err := Close(core.MakeProp(eq(x, x), w.module(M), w.homOf(f, M, M), w.in(x, M)), Options{Depth: 1})
	require.Error(t, err)
	require.True(t, strings.Contains(err.Error(), "cycle"), err.Error())
}

// The corpus states injectivity on a set as the atom injective_on: read
// as a hypothesis through its definition, and decided as a goal by
// fixing two points, so the four lemma's injective half closes in the
// chapter's own spelling at the depth the formula spelling needs.
func TestChase_FourLemmaInjectiveOnTheAtom(t *testing.T) {
	w := installFake(t)
	fl := newFiveLemma(w)
	hyps := append(append([]core.Term{}, fl.rows...),
		fl.exactAt(true, 3), fl.exactAt(true, 2), fl.exactAt(false, 3), fl.exactAt(false, 2),
		w.onto(fl.f[4], fl.A[4], fl.B[4]), w.injectiveOnOf(fl.f[3], fl.A[3]), w.injectiveOnOf(fl.f[1], fl.A[1]))
	goal := core.MakeProp(w.injectiveOnOf(fl.f[2], fl.A[2]), hyps...)
	res := closes(t, goal, 3)
	require.Equal(t, 3, res.Rounds)
	fails(t, goal, 2)
}

// Onto as a goal: image(f, A) = B is the two inclusions, one by the
// map's image law, the other a chase that lifts every element of B —
// the four lemma's surjective half in the chapter's spelling.
func TestChase_FourLemmaSurjectiveAsASetEquation(t *testing.T) {
	w := installFake(t)
	fl := newFiveLemma(w)
	hyps := append(append([]core.Term{}, fl.rows...),
		fl.exactAt(true, 2), fl.exactAt(true, 1), fl.exactAt(false, 2), fl.exactAt(false, 1),
		w.onto(fl.f[3], fl.A[3], fl.B[3]), w.onto(fl.f[1], fl.A[1], fl.B[1]), w.injectiveOnOf(fl.f[0], fl.A[0]))
	goal := core.MakeProp(w.onto(fl.f[2], fl.A[2], fl.B[2]), hyps...)
	res := closes(t, goal, 4)
	fails(t, goal, res.Rounds-1)
}

// Exactness as a goal: exact_at is its definition's set equation, and
// each inclusion a chase — the image killed by the composite, the
// kernel pulled back through the set equation the premises state.
func TestChase_ExactnessAsAGoal(t *testing.T) {
	w := installFake(t)
	A, B, C := w.set("A"), w.set("B"), w.set("C")
	g, f := w.fn("g"), w.fn("f")
	hyps := []core.Term{w.module(A), w.module(B), w.module(C), w.homOf(g, A, B), w.homOf(f, B, C),
		eq(w.imageOf(g, A), w.kernelOf(B, f))}
	goal := core.MakeProp(w.exact(A, B, g, f), hyps...)
	res := closes(t, goal, 1)
	require.Equal(t, 1, res.Rounds)
	fails(t, goal, 0)
}

// An element given by an equation to an element of a module is an
// element of it: no Have of its membership before the close.
func TestChase_MembershipByEquation(t *testing.T) {
	w := installFake(t)
	M, N := w.set("M"), w.set("N")
	f := w.fn("f")
	x, u := w.elem("x"), w.elem("u")
	hyps := []core.Term{w.module(M), w.module(N), w.homOf(f, M, N), w.in(x, M), eq(u, w.ap(f, x))}
	closes(t, core.MakeProp(w.in(u, N), hyps...), 0)
	closes(t, core.MakeProp(eq(w.plus(u, w.minus(w.ap(f, x))), w.zero), hyps...), 0)
}

// ── indexed families: a complex's modules and maps are families over
// degrees, and a map is the application d(k) of the family — the
// probes of the first fills found the closer reading none of them.
// nxt stands for the successor; the bridging of `m + 2` against
// `(m + 1) + 1` is the nat ring normalizer's, tested at the engine.

func (w *_FakeWorld) family(name string) core.Term {
	return core.Var(core.TermName(name), core.MakeFun(dslNum(), w.setT))
}
func (w *_FakeWorld) mapFamily(name string) core.Term {
	return core.Var(core.TermName(name), core.MakeFun(dslNum(), core.MakeFun(w.T, w.T)))
}
func numVar(name string) core.Term { return core.Var(core.TermName(name), dslNum()) }
func nxtOf() core.Term             { return core.Var("nxt", core.MakeFun(dslNum(), dslNum())) }

// allDegrees is ∀k:num. body(k).
func allDegrees(body func(k core.Term) core.Term) core.Term {
	k := numVar("k")
	return all([]core.Term{k}, body(k))
}

// complexFacts are a chain complex's facts over degrees: every P(k) a
// module, d(k + 1): P(k + 1) → P(k), and two boundaries in a row zero.
func complexFacts(w *_FakeWorld, P, d core.Term) []core.Term {
	nxt := nxtOf()
	s := func(k core.Term) core.Term { return w.ap(nxt, k) }
	u := w.elem("u")
	return []core.Term{
		allDegrees(func(k core.Term) core.Term { return w.module(w.ap(P, k)) }),
		allDegrees(func(k core.Term) core.Term { return w.homOf(w.ap(d, s(k)), w.ap(P, s(k)), w.ap(P, k)) }),
		allDegrees(func(k core.Term) core.Term {
			return all([]core.Term{u}, imp(w.in(u, w.ap(P, s(s(k)))), eq(w.ap(w.ap(d, s(k)), w.ap(w.ap(d, s(s(k))), u)), w.zero)))
		}),
	}
}

// The two leaves the boundaries-are-cycles fill met: a boundary lies in
// the module below, and is killed by the next boundary map.
func TestChase_IndexedComplexBoundaryIsACycle(t *testing.T) {
	w := installFake(t)
	P, d := w.family("P"), w.mapFamily("d")
	nxt := nxtOf()
	s := func(k core.Term) core.Term { return w.ap(nxt, k) }
	n, m, x := numVar("n"), numVar("m"), w.elem("x")
	facts := complexFacts(w, P, d)
	inLower := core.MakeProp(w.in(x, w.ap(P, n)), append(facts, w.in(x, w.imageOf(w.ap(d, s(n)), w.ap(P, s(n)))))...)
	closes(t, inLower, 0)
	killed := core.MakeProp(eq(w.ap(w.ap(d, s(m)), x), w.zero),
		append(facts, w.in(x, w.imageOf(w.ap(d, s(s(m))), w.ap(P, s(s(m))))))...)
	closes(t, killed, 0)
}

// The leaves the cochain-map fill met: a cocycle's image lies in the
// target and is a cocycle there — the square read at n names f(n + 1),
// a map only by the facts read at the degree n + 1 the leaf never
// spells — and a coboundary's image is a coboundary.
func TestChase_IndexedCochainMapKeepsCocycles(t *testing.T) {
	w := installFake(t)
	Q, Q2 := w.family("Q"), w.family("Q2")
	dd, ee, f := w.mapFamily("dd"), w.mapFamily("ee"), w.mapFamily("f")
	nxt := nxtOf()
	s := func(k core.Term) core.Term { return w.ap(nxt, k) }
	u := w.elem("u")
	facts := []core.Term{
		allDegrees(func(k core.Term) core.Term { return w.module(w.ap(Q, k)) }),
		allDegrees(func(k core.Term) core.Term { return w.module(w.ap(Q2, k)) }),
		allDegrees(func(k core.Term) core.Term { return w.homOf(w.ap(dd, k), w.ap(Q, k), w.ap(Q, s(k))) }),
		allDegrees(func(k core.Term) core.Term { return w.homOf(w.ap(ee, k), w.ap(Q2, k), w.ap(Q2, s(k))) }),
		allDegrees(func(k core.Term) core.Term { return w.homOf(w.ap(f, k), w.ap(Q, k), w.ap(Q2, k)) }),
		allDegrees(func(k core.Term) core.Term {
			v := w.elem("v")
			return all([]core.Term{v}, imp(w.in(v, w.ap(Q, k)),
				eq(w.ap(w.ap(f, s(k)), w.ap(w.ap(dd, k), v)), w.ap(w.ap(ee, k), w.ap(w.ap(f, k), v)))))
		}),
	}
	n, m := numVar("n"), numVar("m")
	cocycle := append(append([]core.Term{}, facts...), w.in(u, w.ap(Q, n)), eq(w.ap(w.ap(dd, n), u), w.zero))
	closes(t, core.MakeProp(w.in(w.ap(w.ap(f, n), u), w.ap(Q2, n)), cocycle...), 0)
	closes(t, core.MakeProp(eq(w.ap(w.ap(ee, n), w.ap(w.ap(f, n), u)), w.zero), cocycle...), 0)
	coboundary := append(append([]core.Term{}, facts...), w.in(u, w.imageOf(w.ap(dd, m), w.ap(Q, m))))
	closes(t, core.MakeProp(w.in(w.ap(w.ap(f, s(m)), u), w.imageOf(w.ap(ee, m), w.ap(Q2, m))), coboundary...), 0)
}

// An element a hypothesis equates to the zero is read as the zero at
// every module whose zero it is: its image is zero, and it lies in the
// module — no rewrite of it to the zero before the close.
func TestChase_ElementEqualToTheZero(t *testing.T) {
	w := installFake(t)
	M, N := w.set("M"), w.set("N")
	f := w.fn("f")
	u, x := w.elem("u"), w.elem("x")
	hyps := []core.Term{w.module(M), w.module(N), w.homOf(f, M, N), eq(u, w.zero), w.in(x, M)}
	closes(t, core.MakeProp(eq(w.ap(f, u), w.zero), hyps...), 0)
	closes(t, core.MakeProp(w.in(u, M), hyps...), 0)
	closes(t, core.MakeProp(eq(w.ap(f, w.plus(x, u)), w.ap(f, x)), hyps...), 0)
	// The zero on the left of the equation reads the same.
	flipped := []core.Term{w.module(M), w.module(N), w.homOf(f, M, N), eq(w.zero, u)}
	closes(t, core.MakeProp(eq(w.ap(f, u), w.zero), flipped...), 0)
}

// The images of a map's source are made atoms of its target while its
// matrix is built — a witness introduced in a round is not saturated
// yet — and every row is spelled at the target's final width: two
// source atoms without images once made rows of two widths, and the
// echelon indexed past the narrower (the four lemma's surjective half,
// with both rows exact at both degrees, met it at depth 3).
func TestChase_HomMatrixRowsShareTheTargetsWidth(t *testing.T) {
	w := installFake(t)
	M, N := w.set("M"), w.set("N")
	f := w.fn("f")
	x, y := w.elem("x"), w.elem("y")
	goal := core.MakeProp(w.in(x, M), w.module(M), w.module(N), w.homOf(f, M, N), w.in(x, M), w.in(y, M))
	d := newDiagram(Installed(), goal, false, nil)
	require.NoError(t, d.read())
	require.Len(t, d.nodes[1].atoms, 0, "the target holds no image before the matrix is built")
	rows := d.homMatrix(d.homs[0])
	require.Len(t, rows, 2)
	for _, r := range rows {
		require.Len(t, r, len(d.homs[0].dst.atoms))
	}
	_, ok := d.imageCoefficients(d.homs[0], _Vector{})
	require.True(t, ok)
}

// A grounded law `u ∈ M ⇒ l = r` reads once its antecedent holds: a
// premise stating it, or a membership the diagram decides (here w,
// a sum of two generators of M). An antecedent neither stated nor
// decided leaves the premise unread, and the goal open.
func TestChase_ImplicationReadOnceItsAntecedentHolds(t *testing.T) {
	w := installFake(t)
	M, N := w.set("M"), w.set("N")
	f, g := w.fn("f"), w.fn("g")
	u, x, y, z := w.elem("u"), w.elem("x"), w.elem("y"), w.elem("z")
	base := []core.Term{w.module(M), w.module(N), w.homOf(f, M, N), w.homOf(g, M, N)}
	agree := func(v core.Term) core.Term { return eq(w.ap(f, v), w.ap(g, v)) }
	stated := append(append([]core.Term{}, base...), w.in(u, M), imp(w.in(u, M), agree(u)))
	closes(t, core.MakeProp(agree(w.plus(u, u)), stated...), 0)
	sum := w.plus(x, y)
	decided := append(append([]core.Term{}, base...), w.in(x, M), w.in(y, M), imp(and(w.in(sum, M), w.in(x, M)), agree(sum)))
	closes(t, core.MakeProp(agree(sum), decided...), 0)
	open := append(append([]core.Term{}, base...), w.in(u, M), imp(w.in(z, M), agree(u)))
	report := fails(t, core.MakeProp(agree(u), open...), 0)
	require.Contains(t, report, "neither a premise nor decided by the diagram")
}

// A premise in the closer's clause form — `¬p ∨ q`, the spelling a By
// installs a guarded law in where the context does not supply its guard
// as written — reads as the implication p ⇒ q: ground, with the negated
// disjunct in either position, two guards as two negated disjuncts, and
// under a ∀ as an equation schema. A guard the diagram neither states
// nor decides leaves the clause unread, named as the implication.
func TestChase_ClauseFormReadsAsTheImplication(t *testing.T) {
	w := installFake(t)
	M, N := w.set("M"), w.set("N")
	f, g := w.fn("f"), w.fn("g")
	u, v, z := w.elem("u"), w.elem("v"), w.elem("z")
	base := []core.Term{w.module(M), w.module(N), w.homOf(f, M, N), w.homOf(g, M, N), w.in(u, M)}
	agree := func(x core.Term) core.Term { return eq(w.ap(f, x), w.ap(g, x)) }
	or := func(a, b core.Term) core.Term { return wrap(a).Or(b).Core() }
	not := func(p core.Term) core.Term { return ext.Not(p).Core() }
	with := func(clause core.Term) []core.Term { return append(append([]core.Term{}, base...), clause) }
	goal := agree(w.plus(u, u))
	closes(t, core.MakeProp(goal, with(or(not(w.in(u, M)), agree(u)))...), 0)
	closes(t, core.MakeProp(goal, with(or(agree(u), not(w.in(u, M))))...), 0)
	closes(t, core.MakeProp(goal, with(or(not(w.in(u, M)), or(agree(u), not(w.in(u, M)))))...), 0)
	closes(t, core.MakeProp(goal, with(all([]core.Term{v}, or(not(w.in(v, M)), agree(v))))...), 0)
	report := fails(t, core.MakeProp(agree(u), with(or(not(w.in(z, M)), agree(u)))...), 0)
	require.Contains(t, report, "neither a premise nor decided by the diagram")
}

// A guard can become known only after equations travel through maps.
func TestChase_RetriesGuardAfterSaturation(t *testing.T) {
	w := installFake(t)
	M, N := w.set("M"), w.set("N")
	f, g, h := w.fn("f"), w.fn("g"), w.fn("h")
	x, y, u := w.elem("x"), w.elem("y"), w.elem("u")
	conclusion := eq(w.ap(g, u), w.ap(h, u))
	hyps := []core.Term{w.module(M), w.module(N), w.homOf(f, M, N), w.homOf(g, M, N), w.homOf(h, M, N), w.in(x, M), w.in(y, M), w.in(u, M), imp(eq(w.ap(f, x), w.ap(f, y)), conclusion)}
	fails(t, core.MakeProp(conclusion, hyps...), 0)
	closes(t, core.MakeProp(conclusion, append(hyps, eq(x, y))...), 0)
}
