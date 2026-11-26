package refuter

import (
	"context"
	"sync"
	"testing"
	"time"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/clause"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/utils"

	"github.com/stretchr/testify/assert"
	"go.uber.org/goleak"
)

var (
	MakeFun  = core.MakeFun
	TypeA    = core.TypeA()
	TypeB    = ext.TypeB
	TypeBool = core.TypeBool()
	Var      = ext.Var
	Not      = ext.Not
	ForAll   = ext.ForAll
	Exists   = ext.Exists
	Unique   = ext.Unique
	TestProp = prop.MakeProp
)

var cnfNormalizationCache utils.Map[core.TermKey, Prop]

// _PROVE_BUDGET bounds a capability test's search. The test's claim is
// that the refuter closes these goals; the bound is there so a search that
// never closes fails instead of hanging, and a search that gives up
// reports saturation long before it. It is not a performance
// gate: these tests take up to two thirds of a second on an idle machine
// (TestProve0 alone outran its old half-second budget there), and the
// budget is what `go test ./...` on a saturated machine still clears with
// room (measured at twice the cores: under four seconds) — a slowdown is
// for a benchmark to show, not a red test.
const _PROVE_BUDGET = 10 * time.Second

func TestDivisionRejectsRetiredInitialClause(t *testing.T) {
	u := Var("u", MakeFun(TypeA, TypeBool))
	y := Var("y", TypeA)
	q := Var("q", TypeBool)

	initial := clause.MakeClause(u.Apply(y))
	divisible := clause.MakeClause(ext.Or(u.Apply(y), q))
	division := divisible.Division()

	passive := emptyPassiveSet()
	passive.add(initial)
	passive.markUseless(initial)

	s := newRefuteState(
		&ext.VarList{},
		ClauseMap{initial.Key(): initial},
		make(ClauseMap),
		&_ActiveSet{m: make(ClauseMap)},
		passive,
		emptyDeductRecord(),
		&_AttemptRecords{},
		&_RefuteCache{},
		newClauseWhistle(ClauseMap{initial.Key(): initial}),
		&_FaultSlot{},
	)

	assert.False(t, s.passiveSet.has(initial),
		"cleanup must remove the initial clause from the passive list")
	assert.True(t, s.isOrigInitClause(initial),
		"cleanup must not erase permanent initial-clause identity")
	assert.True(t, s.divisionHasExistingClause(division),
		"division must not reclassify a retired initial clause as an assumption")
}

func TestRetireLeavesBothSets(t *testing.T) {
	u := Var("u", MakeFun(TypeA, TypeBool))
	y := Var("y", TypeA)
	c := clause.MakeClause(u.Apply(y))

	active := &_ActiveSet{m: make(ClauseMap)}
	assert.True(t, active.insert(c))
	passive := emptyPassiveSet()
	passive.add(c)
	s := newRefuteState(
		&ext.VarList{},
		ClauseMap{c.Key(): c},
		make(ClauseMap),
		active,
		passive,
		emptyDeductRecord(),
		&_AttemptRecords{},
		&_RefuteCache{},
		newClauseWhistle(ClauseMap{c.Key(): c}),
		&_FaultSlot{},
	)

	s.retire(c)
	assert.False(t, s.activeSet.has(c), "a retired clause is no resolution partner")
	assert.False(t, s.passiveSet.has(c), "a retired clause is never selected")
	assert.True(t, s.passiveSet.checkUselessness(c))
	// Retiring again finds nothing to remove and changes nothing.
	s.retire(c)
	assert.False(t, s.activeSet.has(c))
	assert.True(t, s.passiveSet.checkUselessness(c))
}

// A search whose producers have all returned and whose selector finds
// nothing is saturated: refute reports fail on its own, with no deadline.
func TestSaturatedSearchReportsFail(t *testing.T) {
	defer goleak.VerifyNone(t)

	x := Var("x", TypeA)
	y := Var("y", TypeA)
	P := Var("P", MakeFun(TypeA, TypeBool))

	// P(x) ⊢ P(y) does not hold: {P(x), ¬P(y)} is satisfiable.
	r := CreateRefuter(t.Context(), TestProp(P.Apply(y), P.Apply(x)), &cnfNormalizationCache)
	s := refuteStateFromCNF(r.CNF())
	assert.Equal(t, fail, s.refute(t.Context()))
	assert.False(t, s.isRefuted())
}

func TestProve0(t *testing.T) {
	defer goleak.VerifyNone(t)

	var goals []Prop

	x := Var("x", TypeA)
	y := Var("y", TypeA)
	P := Var("P", MakeFun(TypeA, TypeBool))
	D := Var("D", MakeFun(TypeA, TypeBool))
	Q := Var("Q", TypeBool)

	// ∃x.P(x) ⊢ ∃x.P(x) ∧ (D(x) ⇒ ∀y.(P(y) ⇒ D(y)))
	g := Exists(x)(P.Apply(x).And(D.Apply(x).Imply(ForAll(y)(P.Apply(y).Imply(D.Apply(y))))))
	goal := TestProp(g, Exists(x)(P.Apply(x)))
	goals = append(goals, goal)

	// ∃x.∀y.(P(y) ⇔ (x = y)) ⇔ ∃x.P(x) ∧ ∀x.∀y.((P(x) ∧ P(y)) ⇒ (x = y))
	g0 := Exists(x)(P.Apply(x)).And(ForAll(x, y)(P.Apply(x).And(P.Apply(y)).Imply(x.Eq(y))))
	g1 := Exists(x)(ForAll(y)(P.Apply(y).Eq(x.Eq(y))))
	goal = TestProp(g0.Eq(g1))
	goals = append(goals, goal)

	// P(x) ⇔ ∀y.((x = y) ⇒ P(y))
	goal = TestProp(P.Apply(x).Eq(ForAll(y)(x.Eq(y).Imply(P.Apply(y)))))
	goals = append(goals, goal)

	// P(x) ⇔ ∃y.((x = y) ∧ P(y))
	goal = TestProp(P.Apply(x).Eq(Exists(y)(x.Eq(y).And(P.Apply(y)))))
	goals = append(goals, goal)

	// ¬Q, ¬(∃x.P(x)), ∃x.P(x) ⊢ Q
	goal = TestProp(Q, Not(Exists(x)(P.Apply(x))), Not(Q), Exists(x)(P.Apply(x)))
	goals = append(goals, goal)

	ctx, cancel := context.WithTimeout(t.Context(), _PROVE_BUDGET)
	defer cancel()
	wg := sync.WaitGroup{}
	for _, goal := range goals {
		wg.Go(func() {
			p := CreateRefuter(t.Context(), goal, &cnfNormalizationCache)
			p.Prove(ctx)
			assert.True(t, p.Refuted())
		})
	}
	wg.Wait()
}

func TestProve1(t *testing.T) {
	defer goleak.VerifyNone(t)

	x := Var("x", TypeA)
	y := Var("y", TypeA)
	z := Var("z", TypeA)
	P := Var("P", MakeFun(TypeA, TypeA, TypeA))
	I := Var("Inv", MakeFun(TypeA, TypeA))
	One := Var("One", TypeA)

	// ∀x.∀y.∀z.(P(x, P(y, z)) = P(P(x, y), z)),
	// ∀x.(P(One, x) = x),
	// ∀x.(P(Inv(x), x) = One)
	// 	⊢ ∀x.(P(x, Inv(x)) = One)
	g0 := ForAll(x, y, z)(P.Apply(x, P.Apply(y, z)).Eq(P.Apply(P.Apply(x, y), z)))
	g1 := ForAll(x)(P.Apply(One, x).Eq(x))
	g2 := ForAll(x)(P.Apply(I.Apply(x), x).Eq(One))
	g := ForAll(x)(P.Apply(x, I.Apply(x)).Eq(One))
	goal := TestProp(g, g0, g1, g2)
	prover := CreateRefuter(t.Context(), goal, &cnfNormalizationCache)
	ctx, cancel := context.WithTimeout(t.Context(), _PROVE_BUDGET)
	defer cancel()
	prover.Prove(ctx)
	assert.True(t, prover.Refuted())
}

func TestProve2(t *testing.T) {
	defer goleak.VerifyNone(t)

	var goals []Prop

	P := Var("P", MakeFun(TypeB, TypeB, TypeBool))
	R := Var("R", MakeFun(TypeB, TypeB, TypeBool))
	Q := Var("Q", MakeFun(TypeB, TypeB, TypeB))
	x := Var("x", TypeB)
	y := Var("y", TypeB)
	z := Var("z", TypeB)

	// ∀x.∀y.(P(x, y) ⇒ P(y, x)),
	// ∀x.∀y.(R(x, y) ⇒ P(x, y))
	// 	⊢ (∀x.∀y.(R(x, y) ∨ R(y, x))) ⇒ (∀x.∀y.P(x, y))
	goal := TestProp(
		ForAll(x, y)(R.Apply(x, y).Or(R.Apply(y, x))).Imply(ForAll(x, y)(P.Apply(x, y))),
		ForAll(x, y)(P.Apply(x, y).Imply(P.Apply(y, x))),
		ForAll(x, y)(R.Apply(x, y).Imply(P.Apply(x, y))))
	goals = append(goals, goal)

	// ∀x.∀y.∀z.((P(x, y) ∧ P(y, z)) ⇒ P(x, z)),
	// ∀x.∀y.∀z.((R(x, y) ∧ R(y, z)) ⇒ R(x, z)),
	// ∀x.∀y.(R(x, y) ⇒ R(y, x)),
	// ∀x.∀y.(P(x, y) ∨ R(x, y))
	// 	⊢ (∀x.∀y.P(x, y)) ∨ (∀x.∀y.R(x, y))
	g0 := ForAll(x, y, z)(P.Apply(x, y).And(P.Apply(y, z)).Imply(P.Apply(x, z)))
	g1 := ForAll(x, y, z)(R.Apply(x, y).And(R.Apply(y, z)).Imply(R.Apply(x, z)))
	g2 := ForAll(x, y)(R.Apply(x, y).Imply(R.Apply(y, x)))
	g3 := ForAll(x, y)(P.Apply(x, y).Or(R.Apply(x, y)))
	g := ForAll(x, y)(P.Apply(x, y)).Or(ForAll(x, y)(R.Apply(x, y)))
	goal = TestProp(g, g0, g1, g2, g3)
	goals = append(goals, goal)

	// ∀x.∀y.∀z.(Q(x, Q(y, z)) = Q(Q(x, y), z)),
	// ∀x.∀y.(Q(x, y) = Q(y, x)),
	// ∀x.∀y.(R(x, y) ⇔ (∃z.(y = Q(z, x))))
	// 	⊢ ∀x.∀y.∀z.(R(x, y) ⇒ R(x, Q(z, y)))
	g0 = ForAll(x, y, z)(Q.Apply(x, Q.Apply(y, z)).Eq(Q.Apply(Q.Apply(x, y), z)))
	g1 = ForAll(x, y)(Q.Apply(x, y).Eq(Q.Apply(y, x)))
	g2 = ForAll(x, y)(R.Apply(x, y).Eq(Exists(z)(y.Eq(Q.Apply(z, x)))))
	g = ForAll(x, y, z)(R.Apply(x, y).Imply(R.Apply(x, Q.Apply(z, y))))
	goal = TestProp(g, g0, g1, g2)
	goals = append(goals, goal)

	ctx, cancel := context.WithTimeout(t.Context(), _PROVE_BUDGET)
	defer cancel()
	wg := sync.WaitGroup{}
	for _, goal := range goals {
		wg.Go(func() {
			p := CreateRefuter(t.Context(), goal, &cnfNormalizationCache)
			p.refute(ctx)
			assert.True(t, p.Refuted())
		})
	}
	wg.Wait()
}

func TestProve3(t *testing.T) {
	defer goleak.VerifyNone(t)

	x := Var("x", TypeA)
	P := Var("P", MakeFun(TypeA, TypeB, TypeBool))
	f := Var("f", MakeFun(TypeA, TypeB))

	a := Var("a", TypeB)
	x0 := Var("x_0", TypeA)
	y0 := Var("y_0", TypeB)

	s0 := Exists(f)(f.Apply(x0).Eq(y0).And(ForAll(x)(P.Apply(x, f.Apply(x)))))
	s1 := ForAll(x)(P.Apply(x, a.SuchThat(x.Eq(x0).Imply(a.Eq(y0)).And(Not(x.Eq(x0)).Imply(a.Eq(f.Apply(x)))))))

	// ∀x.P(x, εa.(((x = x₀) ⇒ (a = y₀)) ∧ ((x ≠ x₀) ⇒ (a = f(x)))))
	// 	⊢ ∃f.((f(x₀) = y₀) ∧ (∀x.P(x, f(x))))
	goal := TestProp(s0, s1)
	prover := CreateRefuter(t.Context(), goal, &cnfNormalizationCache)
	ctx, cancel := context.WithTimeout(t.Context(), _PROVE_BUDGET)
	defer cancel()
	prover.Prove(ctx)
	assert.True(t, prover.Refuted())
}

func TestProve4(t *testing.T) {
	defer goleak.VerifyNone(t)
	var goals []Prop

	f := Var("f", MakeFun(TypeInd, TypeBool))
	g := Var("g", MakeFun(TypeInd, TypeBool))
	i := Var("i", TypeInd)
	j := Var("j", TypeInd)
	a := Var("a", TypeInd)
	b := Var("b", TypeInd)
	alpha0 := Var("α₀", MakeFun(MakeFun(TypeInd, TypeBool), TypeInd, TypeBool))
	Suc := ext.TestConst("Suc", MakeFun(TypeInd, TypeInd))
	_0 := ext.TestConst("0", TypeInd)

	// (a = 0) ∨ (∃i.((a = Suc(i)) ∧ f(i)))
	Sf := a.Eq(_0).Or(Exists(i)(a.Eq(Suc.Apply(i)).And(f.Apply(i))))
	// (a = 0) ∨ (∃i.((a = Suc(i)) ∧ g(i)))
	Sg := a.Eq(_0).Or(Exists(i)(a.Eq(Suc.Apply(i)).And(g.Apply(i))))

	// num = λa.(∀f.((∀a.(((a = 0) ∨ (∃i.((a = Suc(i)) ∧ f(i)))) ⇒ f(a))) ⇒ f(a)))
	num := ext.ConstDef(a.To(ForAll(f)(ForAll(a)(Sf.Imply(f.Apply(a))).Imply(f.Apply(a)))), "num")
	numDef := num.AssertConst().DefThm().Conclusion()

	// (a = 0) ∨ (∃i.((a = Suc(i)) ∧ num(i)))
	Sa := a.Eq(_0).Or(Exists(i)(a.Eq(Suc.Apply(i)).And(num.Apply(i))))
	// (b = 0) ∨ (∃i.((b = Suc(j)) ∧ num(j)))
	Sb := b.Eq(_0).Or(Exists(j)(b.Eq(Suc.Apply(j)).And(num.Apply(j))))

	// ∀a.(((a = 0) ∨ (∃i.((a = Suc(i)) ∧ num(i)))) ⇒ num(a))
	S := ForAll(a)(a.Eq(_0).Or(Exists(i)(a.Eq(Suc.Apply(i)).And(num.Apply(i)))).Imply(num.Apply(a)))

	R := ForAll(a)(Sf.Imply(f.Apply(a)))

	// ∀g.∀f.((∀a.(g(a) ⇒ f(a))) ⇒ (∀a.(((a = 0) ∨ (∃i.((a = Suc(i)) ∧ g(i)))) ⇒ ((a = 0) ∨ (∃i.((a = Suc(i)) ∧ f(i)))))))
	mono := ForAll(g, f)(ForAll(a)(g.Apply(a).Imply(f.Apply(a))).Imply(ForAll(a)(Sg.Imply(Sf))))

	// ∀a.(((a = 0) ∨ (∃i.((a = Suc(i)) ∧ f(i)))) ⇒ f(a)),
	// g = (λa.(∀f.((∀a.(((a = 0) ∨ (∃i.((a = Suc(i)) ∧ f(i)))) ⇒ f(a))) ⇒ f(a))))
	// 	⊢ g(a) ⇒ f(a)
	goal := TestProp(
		g.Apply(a).Imply(f.Apply(a)),
		R,
		g.Eq(a.To(ForAll(f)(R.Imply(f.Apply(a))))),
	)
	goals = append(goals, goal)

	// g = (λa.(∀f.((∀a.(((a = 0) ∨ (∃i.((a = Suc(i)) ∧ f(i)))) ⇒ f(a))) ⇒ f(a)))),
	// a = 0
	// 	⊢ g(a)
	goal = TestProp(
		g.Apply(a),
		a.Eq(_0),
		g.Eq(a.To(ForAll(f)(R.Imply(f.Apply(a))))),
	)
	goals = append(goals, goal)

	// ¬(∀a.(num(a) ⇒ ((a = 0) ∨ (∃i.((a = Suc(i)) ∧ num(i)))))),
	// ∀a.(((a = 0) ∨ (∃i.((a = Suc(i)) ∧ num(i)))) ⇒ num(a))
	// 	⊢ ∀a.(((a = 0) ∨ (∃b.((a = Suc(b)) ∧ ((b = 0) ∨ (∃j.((b = Suc(j)) ∧ num(j))))))) ⇒ ((a = 0) ∨ (∃i.((a = Suc(i)) ∧ num(i)))))
	goal = TestProp(
		ForAll(a)(a.Eq(_0).Or(Exists(b)(a.Eq(Suc.Apply(b)).And(Sb))).Imply(Sa)),
		ForAll(a)(Sa.Imply(num.Apply(a))),
		Not(ForAll(a)(num.Apply(a).Imply(Sa))))
	goals = append(goals, goal)

	// ∀g.∀f.((∀a.(g(a) ⇒ f(a))) ⇒ (∀a.(((a = 0) ∨ (∃i.((a = Suc(i)) ∧ g(i)))) ⇒ ((a = 0) ∨ (∃i.((a = Suc(i)) ∧ f(i))))))),
	// ∀a.(((a = 0) ∨ (∃i.((a = Suc(i)) ∧ num(i)))) ⇒ num(a)),
	// num = (λa.(∀f.((∀a.(((a = 0) ∨ (∃i.((a = Suc(i)) ∧ f(i)))) ⇒ f(a))) ⇒ f(a))))
	// 	⊢ num(0) ∧ (∀i.(num(i) ⇒ num(Suc(i))))
	goal = TestProp(
		num.Apply(_0).And(ForAll(i)(num.Apply(i).Imply(num.Apply(Suc.Apply(i))))),
		numDef,
		S,
		mono)
	goals = append(goals, goal)

	// ∀g.∀f.((∀a.(g(a) ⇒ f(a))) ⇒ (∀a.(((a = 0) ∨ (∃i.((a = Suc(i)) ∧ g(i)))) ⇒ ((a = 0) ∨ (∃i.((a = Suc(i)) ∧ f(i))))))),
	// num = (λa.(∀f.((∀a.(((a = 0) ∨ (∃i.((a = Suc(i)) ∧ f(i)))) ⇒ f(a))) ⇒ f(a))))
	// 	⊢ ∀a.(((a = 0) ∨ (∃i.((a = Suc(i)) ∧ num(i)))) ⇒ num(a))
	goal = TestProp(
		S,
		numDef,
		mono)
	goals = append(goals, goal)

	// ∀g.∀f.((∀a.(g(a) ⇒ f(a))) ⇒ (∀a.(α₀(g, a) ⇒ α₀(f, a)))),
	// α₀ = (λg.λa.((a = 0) ∨ (∃i.((a = Suc(i)) ∧ g(i))))),
	// g = (λa.(∀f.((∀a.(α₀(f, a) ⇒ f(a))) ⇒ f(a))))
	// 	⊢ ∀a.(α₀(g, a) ⇒ g(a))
	goal = TestProp(
		ForAll(a)(alpha0.Apply(g, a).Imply(g.Apply(a))),
		alpha0.Eq(g.To(a.To(Sg))),
		g.Eq(a.To(ForAll(f)(ForAll(a)(alpha0.Apply(f, a).Imply(f.Apply(a))).Imply(f.Apply(a))))),
		ForAll(g, f)(ForAll(a)(g.Apply(a).Imply(f.Apply(a))).Imply(ForAll(a)(alpha0.Apply(g, a).Imply(alpha0.Apply(f, a))))))
	goals = append(goals, goal)

	wg := sync.WaitGroup{}
	for _, goal := range goals {
		wg.Go(func() {
			p := CreateRefuter(t.Context(), goal, &cnfNormalizationCache)
			p.Prove(t.Context())
			assert.True(t, p.Refuted())
		})
	}
	wg.Wait()
}

func TestProveBooleanTheorems(t *testing.T) {
	defer goleak.VerifyNone(t)

	var goal Prop
	var goals []Prop

	x := Var("x", TypeBool)
	u := Var("u", TypeBool)
	v := Var("v", TypeBool)
	w := Var("w", TypeBool)
	f := Var("f", MakeFun(TypeBool, TypeBool))
	R := Var("R", MakeFun(TypeBool, TypeBool))
	S := Var("S", MakeFun(TypeBool, TypeBool, TypeBool))

	// ⊢ ¬∀x.x
	goal = TestProp(Not(ForAll(x)(x)))
	goals = append(goals, goal)

	// x ⇒ u, u ⇒ v, v ⇒ x, (x = ¬u) ∨ (x = ¬v) ⊢ ⊥
	goal = TestProp(ext.F, x.Imply(u), u.Imply(v), v.Imply(x), x.Eq(Not(u)).Or(x.Eq(Not(v))))
	goals = append(goals, goal)

	// ⊢ ¬(∃x.∃S.∀u.(S(x, u) = ¬S(u, u))))
	goal = TestProp(Not(Exists(x, S)(ForAll(u)(S.Apply(x, u).Eq(Not(S.Apply(u, u)))))))
	goals = append(goals, goal)

	// ⊢ ∃u.(S(x, u) = S(u, u))
	goal = TestProp(Exists(u)(S.Apply(x, u).Eq(S.Apply(u, u))))
	goals = append(goals, goal)

	// ⊢ ∀x.R(x) = (R(⊤) ∧ R(⊥))
	goal = TestProp(ForAll(x)(R.Apply(x)).Eq(R.Apply(ext.T).And(R.Apply(ext.F))))
	goals = append(goals, goal)

	// ⊢ ∃x.R(x) = (R(⊤) ∨ R(⊥))
	goal = TestProp(Exists(x)(R.Apply(x)).Eq(R.Apply(ext.T).Or(R.Apply(ext.F))))
	goals = append(goals, goal)

	// ∀v.∀w.(¬R(v) ∨ R(f(w))),
	// ∀u.(R(u) ∨ R(f(u))),
	// ∀x.(¬R(x) ∨ ¬R(f(x)))
	// ⊢ ⊥
	goal = TestProp(
		ext.F,
		ForAll(u)((R.Apply(u)).Or(R.Apply(f.Apply(u)))),
		ForAll(v, w)((Not(R.Apply(v))).Or(R.Apply(f.Apply(w)))),
		ForAll(x)(Not(R.Apply(x)).Or(Not(R.Apply(f.Apply(x))))))
	goals = append(goals, goal)

	ctx, cancel := context.WithTimeout(t.Context(), _PROVE_BUDGET)
	defer cancel()
	wg := sync.WaitGroup{}
	for _, goal := range goals {
		wg.Go(func() {
			p := CreateRefuter(t.Context(), goal, &cnfNormalizationCache)
			p.Prove(ctx)
			assert.True(t, p.Refuted())
		})
	}
	wg.Wait()
}

func TestProveUntrue(t *testing.T) {
	defer goleak.VerifyNone(t)

	var goal Prop
	var goals []Prop

	x := Var("x", TypeA)
	y := Var("y", TypeA)
	z := Var("z", TypeA)
	P := Var("P", MakeFun(TypeA, TypeBool))
	S := Var("S", MakeFun(TypeA, TypeA, TypeBool))

	// ⊢ ∀x.(x = y)
	goal = TestProp(ForAll(x)(x.Eq(y)))
	goals = append(goals, goal)

	// x ≠ z, y ≠ z ⊢ x = y
	goal = TestProp(x.Eq(y), Not(x.Eq(z)), Not(y.Eq(z)))
	goals = append(goals, goal)

	// ⊢ ∃!z.(S(x, z) = S(z, z))
	goal = TestProp(Unique(z)(S.Apply(x, z).Eq(S.Apply(z, z))))
	goals = append(goals, goal)

	// P(x) ⇔ ∃y.((x = y) ⇒ P(y))
	goal = TestProp(P.Apply(x).Eq(Exists(y)(x.Eq(y).Imply(P.Apply(y)))))
	goals = append(goals, goal)

	// P(x) ⇔ ∀y.((x = y) ∧ P(y))
	goal = TestProp(P.Apply(x).Eq(ForAll(y)(x.Eq(y).And(P.Apply(y)))))
	goals = append(goals, goal)

	wg := sync.WaitGroup{}
	for _, goal := range goals {
		wg.Go(func() {
			p := CreateRefuter(t.Context(), goal, &cnfNormalizationCache)
			p.Prove(t.Context())
			assert.False(t, p.Refuted())
		})
	}
	wg.Wait()
}

func TestEpsilonSkolem(t *testing.T) {
	defer goleak.VerifyNone(t)

	x := Var("x", TypeA)
	P := Var("P", MakeFun(TypeA, TypeBool))

	{
		// Given ∃x.P(x), can refute close the same ∃x.P(x)?
		// ∃x.P(x) ⊢ ∃x.P(x)
		goal := TestProp(Exists(x)(P.Apply(x)), Exists(x)(P.Apply(x)))
		p := CreateRefuter(t.Context(), goal, &cnfNormalizationCache)
		ctx, cancel := context.WithTimeout(t.Context(), 500*time.Millisecond)
		defer cancel()
		p.Prove(ctx)
		assert.True(t, p.Refuted(), "Probe A (trivial ∃→∃) failed")
	}
	{
		// Given P(εx.P(x)), can refute close ∃x.P(x)?

		// hyp: P(εx.P(x))
		epsX := x.SuchThat(P.Apply(x))
		hyp := P.Apply(epsX)
		// goal: ∃x.P(x)
		goalConcl := Exists(x)(P.Apply(x))

		goal := TestProp(goalConcl, hyp)
		p := CreateRefuter(t.Context(), goal, &cnfNormalizationCache)
		ctx, cancel := context.WithTimeout(t.Context(), 1000*time.Millisecond)
		defer cancel()
		p.Prove(ctx)
		assert.True(t, p.Refuted(), "Probe B (P(εx.P(x)) ⊢ ∃x.P(x)) failed")
	}
	{
		// ε-encoded existence bridge via curried application.
		// Goal:  ∃r:A→B. ∀x. Q(r(x))
		// Hyp:   ∀x. Q((εr:A→B. ∀x. Q(r(x)))(x))
		// I.e. the body of ε is exactly the goal's matrix, and the hyp instantiates
		// it pointwise.
		r := Var("r", MakeFun(TypeA, TypeB))
		Q := Var("Q", MakeFun(TypeB, TypeBool))

		// body(r) := ∀x. P(r(x))
		body := ForAll(x)(Q.Apply(r.Apply(x)))
		// εr:A→B. body(r)
		epsR := r.SuchThat(body)
		// hyp: ∀x. P((εr. body)(x))
		hyp := ForAll(x)(Q.Apply(epsR.Apply(x)))
		// goal: ∃r. ∀x. P(r(x))
		concl := Exists(r)(ForAll(x)(Q.Apply(r.Apply(x))))

		goal := TestProp(concl, hyp)
		p := CreateRefuter(t.Context(), goal, &cnfNormalizationCache)
		ctx, cancel := context.WithTimeout(t.Context(), 2000*time.Millisecond)
		defer cancel()
		p.Prove(ctx)
		assert.True(t, p.Refuted(), "Probe C (applied-ε ⊢ ∃r-curry) failed")
	}

	{
		// 3-arg tag-indexed: r : Tag → A → A → B
		Tag := core.TypeA() // alias
		Int := TypeInd      // alias for "int-ish"
		tag := Var("tag", Tag)
		m := Var("m", Int)
		n := Var("n", Int)
		r := Var("r", MakeFun(Tag, Int, Int, ext.TypeB))
		P := Var("P", MakeFun(ext.TypeB, TypeBool))

		// body(r) := ∀tag m n. P(r(tag, m, n))
		body := ForAll(tag)(ForAll(m)(ForAll(n)(P.Apply(r.Apply(tag, m, n)))))
		// εr. body
		epsR := r.SuchThat(body)
		// hyp: ∀tag m n. P((εr. body)(tag, m, n))
		hyp := ForAll(tag)(ForAll(m)(ForAll(n)(P.Apply(epsR.Apply(tag, m, n)))))
		// goal: ∃r. ∀tag m n. P(r(tag, m, n))
		concl := Exists(r)(ForAll(tag)(ForAll(m)(ForAll(n)(P.Apply(r.Apply(tag, m, n))))))

		goal := TestProp(concl, hyp)
		p := CreateRefuter(t.Context(), goal, &cnfNormalizationCache)
		ctx, cancel := context.WithTimeout(t.Context(), 5000*time.Millisecond)
		defer cancel()
		p.Prove(ctx)
		assert.True(t, p.Refuted())
	}

	{
		Tag := core.TypeA()
		Int := TypeInd
		tag := Var("tag", Tag)
		m := Var("m", Int)
		n := Var("n", Int)
		r := Var("r", MakeFun(Tag, Int, Int, ext.TypeB))
		P := Var("P", MakeFun(ext.TypeB, TypeBool))
		Q := Var("Q", MakeFun(ext.TypeB, TypeBool))

		body := ForAll(tag)(ForAll(m)(ForAll(n)(
			P.Apply(r.Apply(tag, m, n)).And(Q.Apply(r.Apply(tag, m, n))))))
		epsR := r.SuchThat(body)
		hyp := ForAll(tag)(ForAll(m)(ForAll(n)(
			P.Apply(epsR.Apply(tag, m, n)).And(Q.Apply(epsR.Apply(tag, m, n))))))
		concl := Exists(r)(body)

		_ = m
		_ = n
		goal := TestProp(concl, hyp)
		p := CreateRefuter(t.Context(), goal, &cnfNormalizationCache)
		ctx, cancel := context.WithTimeout(t.Context(), 5000*time.Millisecond)
		defer cancel()
		p.Prove(ctx)
		assert.True(t, p.Refuted())
	}

	{
		Tag := core.TypeA()
		Int := TypeInd
		tag := Var("tag", Tag)
		m := Var("m", Int)
		n := Var("n", Int)
		r := Var("r", MakeFun(Tag, Int, Int, ext.TypeB))
		c := Var("c", MakeFun(Int, TypeBool))
		P := Var("P", MakeFun(ext.TypeB, TypeBool))
		Q := Var("Q", MakeFun(ext.TypeB, TypeBool))

		body := ForAll(tag)(ForAll(m)(ForAll(n)(
			c.Apply(n).Imply(P.Apply(r.Apply(tag, m, n))).
				And(Not(c.Apply(n)).Imply(Q.Apply(r.Apply(tag, m, n)))))))
		epsR := r.SuchThat(body)
		hyp := ForAll(tag)(ForAll(m)(ForAll(n)(
			c.Apply(n).Imply(P.Apply(epsR.Apply(tag, m, n))).
				And(Not(c.Apply(n)).Imply(Q.Apply(epsR.Apply(tag, m, n)))))))
		concl := Exists(r)(body)

		goal := TestProp(concl, hyp)
		p := CreateRefuter(t.Context(), goal, &cnfNormalizationCache)
		ctx, cancel := context.WithTimeout(t.Context(), 5000*time.Millisecond)
		defer cancel()
		p.Prove(ctx)
		assert.True(t, p.Refuted())
	}

}

// TestDivisionRefutesAComponentReadWithABinder: a divided component is a
// clause made from one disjunct, and a disjunct alone can be read with a
// binder the clause it came from is not read with. In
// R(εx.Q(x)) ∨ ¬P(εx.P(x)) the ε-term met first has no Q(εx.Q(x)) beside
// it, so the clause stands as written, while its component ¬P(εx.P(x)) is
// read as ∀x.¬P(x). The sub-state assuming that component refutes it
// against P(a), at x ↦ a.
func TestDivisionRefutesAComponentReadWithABinder(t *testing.T) {
	defer goleak.VerifyNone(t)

	x := Var("x", TypeA)
	a := Var("a", TypeA)
	P := Var("P", MakeFun(TypeA, TypeBool))
	Q := Var("Q", MakeFun(TypeA, TypeBool))
	R := Var("R", MakeFun(TypeA, TypeBool))
	chosenQ := x.SuchThat(Q.Apply(x))
	chosenP := x.SuchThat(P.Apply(x))

	divisible := clause.MakeClause(ext.Or(R.Apply(chosenQ), Not(P.Apply(chosenP))))
	witness := clause.MakeClause(P.Apply(a))
	denied := clause.MakeClause(Not(R.Apply(chosenQ)))

	// The scene: the clause is read as written and divides, and its
	// second component is read as ∀x.¬P(x).
	assert.True(t, divisible.EffectiveTerm().AlphaEquals(divisible.Term()))
	division := divisible.Division()
	if !assert.NotNil(t, division) || !assert.Len(t, division.DividedClauses, 2) {
		return
	}
	assert.True(t, division.DividedClauses[1].EffectiveTerm().AlphaEquals(ForAll(x)(Not(P.Apply(x)))),
		"the component is read as %s", ext.WrapTerm(division.DividedClauses[1].EffectiveTerm()))

	initial := ClauseMap{}
	active := &_ActiveSet{m: make(ClauseMap)}
	groundVars := ext.VarList{}
	for _, c := range []*Clause{divisible, witness, denied} {
		initial[c.Key()] = c
		assert.True(t, active.insert(c))
		for _, v := range c.Term().Frees(nil) {
			groundVars.Add(v)
		}
	}
	s := newRefuteState(
		&groundVars,
		initial,
		make(ClauseMap),
		active,
		emptyPassiveSet(),
		emptyDeductRecord(),
		&_AttemptRecords{},
		&_RefuteCache{},
		newClauseWhistle(initial),
		&_FaultSlot{},
	)

	ctx, cancel := context.WithTimeout(t.Context(), _PROVE_BUDGET)
	defer cancel()
	assert.Equal(t, succeed, s.refute(ctx))
	assert.Nil(t, s.fault.recorded())
	assert.True(t, s.isRefuted())
}
