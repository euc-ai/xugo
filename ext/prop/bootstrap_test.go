package prop

import (
	"testing"

	"github.com/euc-ai/xugo/ext"
	"github.com/stretchr/testify/assert"
)

func TestBasics(t *testing.T) {
	x := Var("x", TypeBool)
	y := Var("y", TypeBool)
	z := Var("z", TypeBool)

	// True / False
	assertPropAlphaEqual(t, DerivesTrue, testThm(T))
	assertPropAlphaEqual(t, FalseDerives(x), testThm(x, F))
	assertPropAlphaEqual(t, ImpliesFalse(x), testThm(x.Imply(F).Eq(Not(x))))
	assertPropAlphaEqual(t, NotTrue, testThm(Not(T).Eq(F)))
	assertPropAlphaEqual(t, NotFalse, testThm(Not(F).Eq(T)))

	// Neg of (AND / OR / IMPLY / IFF)
	assertPropAlphaEqual(t,
		BinaryThms["¬(p ∧ q) ⇔ (¬p ∨ ¬q)"](x, y),
		testThm(Not(x.And(y)).Eq(Not(x).Or(Not(y)))))
	assertPropAlphaEqual(t,
		BinaryThms["¬(p ∨ q) ⇔ (¬p ∧ ¬q)"](x, y),
		testThm(Not(x.Or(y)).Eq(Not(x).And(Not(y)))))
	assertPropAlphaEqual(t,
		BinaryThms["¬(p ⇒ q) ⇔ (p ∧ ¬q)"](x, y),
		testThm(Not(x.Imply(y)).Eq(x.And(Not(y)))))
	assertPropAlphaEqual(t,
		BinaryThms["(p ⊕ q) ⇔ (¬p ⇔ q)"](x, y),
		testThm(x.Xor(y).Eq(Not(x).Eq(y))))

	// IFF to OR
	assertPropAlphaEqual(t,
		BinaryThms["(p ⇔ q) ⇔ ((p ∧ q) ∨ (¬p ∧ ¬q))"](x, y),
		testThm(x.Eq(y).Eq(x.And(y).Or(Not(x).And(Not(y))))))
	// XOR to AND
	assertPropAlphaEqual(t,
		BinaryThms["(p ⊕ q) ⇔ ((p ∨ q) ∧ (¬p ∨ ¬q))"](x, y),
		testThm(x.Xor(y).Eq(x.Or(y).And(Not(x).Or(Not(y))))))

	// IMPLY to OR
	assertPropAlphaEqual(t,
		BinaryThms["(p ⇒ q) ⇔ (¬p ∨ q)"](x, y),
		testThm(x.Imply(y).Eq(Not(x).Or(y))))
	// OR to IMPLY
	assertPropAlphaEqual(t,
		BinaryThms["(p ∨ q) ⇔ (¬p ⇒ q)"](x, y),
		testThm(x.Or(y).Eq(Not(x).Imply(y))))

	// Contraposition
	thm := testThm(z, x, y)
	assertPropAlphaEqual(t,
		WrapProp(thm).Contraposition(x),
		testThm(Not(x), Not(z), y))
	assertPropAlphaEqual(t,
		WrapProp(thm).Contraposition(y),
		testThm(Not(y), Not(z), x))

	// Contradict / Modus Ponens
	assertPropAlphaEqual(t, Contradict(x), testThm(F, Not(x), x))
	assertPropAlphaEqual(t, ModusPonens(x, y), testThm(y, x, x.Imply(y)))

	// Contradict recursive
	assertPropAlphaEqual(t,
		ContradictRecursive(x, y),
		testThm(F, Not(x), Not(y), x.Or(y)))
	assertPropAlphaEqual(t,
		ContradictRecursive(x, y, z, x),
		testThm(F, Not(x), Not(y), Not(z), x.Or(y).Or(z).Or(x)))

	// Excluded middle
	assertPropAlphaEqual(t, ExcludedMiddle(x), testThm(x.Or(Not(x))))

	// Logicals
	assertPropAlphaEqual(t,
		CommuteAND(x, y),
		testThm(x.And(y).Eq(y.And(x))))
	assertPropAlphaEqual(t,
		CommuteOR(x, y),
		testThm(x.Or(y).Eq(y.Or(x))))
	assertPropAlphaEqual(t,
		CommuteEQ(x, y),
		testThm(x.Eq(y).Eq(y.Eq(x))))
	assertPropAlphaEqual(t,
		BinaryThms["p ∧ (p ∨ q) ⇔ p"](x, y),
		testThm(x.And(x.Or(y)).Eq(x)))
	assertPropAlphaEqual(t,
		BinaryThms["p ∨ (p ∧ q) ⇔ p"](x, y),
		testThm(x.Or(x.And(y)).Eq(x)))
	assertPropAlphaEqual(t,
		TernaryThms["((p ∧ q) ∧ r) ⇔ (p ∧ (q ∧ r))"](x, y, z),
		testThm(x.And(y).And(z).Eq(x.And(y.And(z)))))
	assertPropAlphaEqual(t,
		TernaryThms["((p ∨ q) ∨ r) ⇔ (p ∨ (q ∨ r))"](x, y, z),
		testThm(x.Or(y).Or(z).Eq(x.Or(y.Or(z)))))
	assertPropAlphaEqual(t,
		TernaryThms["((p ⇔ q) ⇔ r) ⇔ (p ⇔ (q ⇔ r))"](x, y, z),
		testThm(x.Eq(y).Eq(z).Eq(x.Eq(y.Eq(z)))))
	assertPropAlphaEqual(t,
		TernaryThms["(p ∧ (q ∨ r)) ⇔ ((p ∧ q) ∨ (p ∧ r))"](x, y, z),
		testThm(x.And(y.Or(z)).Eq((x.And(y)).Or(x.And(z)))))
	assertPropAlphaEqual(t,
		TernaryThms["p ⇒ q, p ∧ r ⊢ q ∧ r"](x, y, z),
		testThm(y.And(z), x.Imply(y), x.And(z)))
	assertPropAlphaEqual(t,
		TernaryThms["p ⇒ q, p ∨ r ⊢ q ∨ r"](x, y, z),
		testThm(y.Or(z), x.Imply(y), x.Or(z)))
	assertPropAlphaEqual(t,
		TernaryThms["(p ⇒ r) ∧ (q ⇒ r) ⇔ ((p ∨ q) ⇒ r)"](x, y, z),
		testThm(x.Imply(z).And(y.Imply(z)).Eq(x.Or(y).Imply(z))))

	// cond clause
	a := Var("a", TypeB)
	b := Var("b", TypeB)
	assertPropAlphaEqual(t,
		CondId(x, b),
		testThm(ext.Cond(x, b, b).Eq(b)))
	assertPropAlphaEqual(t,
		CondClauseT(a, b),
		testThm(ext.Cond(T, a, b).Eq(a)))
	assertPropAlphaEqual(t,
		CondClauseF(a, b),
		testThm(ext.Cond(F, a, b).Eq(b)))
}

func TestHyps(t *testing.T) {
	h0 := Var("h0", TypeBool)
	h1 := Var("h1", TypeBool)
	h2 := Var("h2", TypeBool)
	h := And(h0, h1, h2)

	assertPropAlphaEqual(t,
		ConclAND(h0, h1),
		testThm(h0.And(h1), h0, h1))
	assertPropAlphaEqual(t,
		ConclAND(h0, h0),
		testThm(h0.And(h0), h0))

	// h0 ∧ h1 ∧ h2 ⊢ hi
	thms := HypANDRecursive(h0, h1, h2)
	assertPropAlphaEqual(t,
		thms[0], testThm(h0, h))
	assertPropAlphaEqual(t,
		thms[1], testThm(h1, h))
	assertPropAlphaEqual(t,
		thms[2], testThm(h2, h))

	thms = HypANDRecursive(h0, h1, h0)
	assertPropAlphaEqual(t,
		thms[0], testThm(h0, h0.And(h1).And(h0)))
	assertPropAlphaEqual(t,
		thms[1], testThm(h1, h0.And(h1).And(h0)))
	assertPropAlphaEqual(t,
		thms[2], testThm(h0, h0.And(h1).And(h0)))

	assertPropAlphaEqual(t,
		ConclANDRecursive(h0, h1, h2),
		testThm(h, h0, h1, h2))

	assertPropAlphaEqual(t,
		ConclANDRecursive(h0, h1, h0),
		testThm(h0.And(h1).And(h0), h0, h1))

	c := Var("c", TypeBool)
	assertPropAlphaEqual(t,
		ByCasesRecursive(c, h0, h1, h2),
		testThm(c, Or(h0, h1, h2), h0.Imply(c), h1.Imply(c), h2.Imply(c)))
}

func TestQuantifier(t *testing.T) {
	a := Var("a", TypeInd)
	b := Var("b", TypeInd)
	c := Var("c", TypeInd)
	d := Var("d", TypeInd)
	e := Var("e", MakeFun(TypeInd, TypeBool))
	h := Var("h", TypeBool)
	p := Var("p", TypeBool)
	q := Var("q", TypeBool)
	r := Var("r", TypeBool)
	P := Var("P", MakeFun(TypeInd, TypeBool))
	Q := Var("Q", MakeFun(TypeInd, TypeBool))
	R := Var("R", MakeFun(TypeBool, TypeBool))
	S := Var("S", MakeFun(TypeInd, TypeInd))
	W := Var("W", MakeFun(TypeInd, TypeInd, TypeBool))

	/////////////////////////
	// Test ∀
	/////////////////////////

	assertPropAlphaEqual(t,
		InstForAll(ForAll(a)(P.Apply(a)), b),
		testThm(P.Apply(b), ForAll(a)(P.Apply(a))))

	thm := Refl(e.Apply(a)).ConclForAll(a.AssertVar())
	assertPropAlphaEqual(t,
		thm,
		testThm(ForAll(a)(e.Apply(a).Eq(e.Apply(a)))))

	assertPropAlphaEqual(t,
		NegForAll(b.To(Not(Q.Apply(b)))),
		testThm(Not(ForAll(a)(Not(Q.Apply(a)))).Eq(
			Exists(a)(Not(Not(Q.Apply(a)))))))

	assertPropAlphaEqual(t,
		MootForAll(b.AssertVar(), (Q.Apply(a))),
		testThm(ForAll(b)(Q.Apply(a)).Eq(Q.Apply(a))))

	assertPropAlphaEqual(t,
		MootForAll(q.AssertVar(), (R.Apply(p))),
		testThm(ForAll(q)(R.Apply(p)).Eq(R.Apply(p))))

	assertPropAlphaEqual(t,
		BoolInduct(r.To(R.Apply(r))),
		testThm(R.Apply(r), R.Apply(T), R.Apply(F)))

	assertPropAlphaEqual(t,
		BoolForAll(r.To(R.Apply(r))),
		testThm(ForAll(r)(R.Apply(r)).Eq(R.Apply(T).And(R.Apply(F)))))

	assertPropAlphaEqual(t,
		ForAllAND(a.To(Q.Apply(a)), a.To(P.Apply(a))),
		testThm(
			ForAll(a)(Q.Apply(a).And(P.Apply(a))).Eq(
				ForAll(a)(Q.Apply(a)).And(ForAll(a)(P.Apply(a))))))

	assertPropAlphaEqual(t,
		ForAllAND(a.To(b.To(P.Apply(b)).Apply(a)), a.To(P.Apply(a))),
		testThm(
			ForAll(a)(b.To(P.Apply(b)).Apply(a).And(P.Apply(a))).Eq(
				ForAll(a)(b.To(P.Apply(b)).Apply(a)).And(ForAll(a)(P.Apply(a))))))

	assertPropAlphaEqual(t,
		ForAllIMPLY(a.To(Q.Apply(a)), a.To(P.Apply(a))),
		testThm(
			ForAll(a)(P.Apply(a)),
			ForAll(a)(Q.Apply(a).Imply(P.Apply(a))),
			ForAll(a)(Q.Apply(a))))

	assertPropAlphaEqual(t,
		WrapProp(testThm(P.Apply(a), Q.Apply(a), R.Apply(h))).
			HypForAllInst(a.AssertVar(), Q.Apply(a)).
			ConclForAll(a.AssertVar()),
		testThm(
			ForAll(a)(P.Apply(a)),
			ForAll(a)(Q.Apply(a)),
			R.Apply(h)))

	verify := func(t0, t1 *ext.TermWrapper) {
		assertPropAlphaEqual(t,
			ReorderForAll(t0, t1),
			testThm(t0.Eq(t1)))
	}

	verify(ForAll(a, b, c, W)(W.Apply(a, b).Eq(W.Apply(c, d))),
		ForAll(W, c, b, a)(W.Apply(a, b).Eq(W.Apply(c, d))))
	verify(ForAll(a, b, c, W)(W.Apply(a, b).Eq(W.Apply(c, d))),
		ForAll(a, b, W, c)(W.Apply(a, b).Eq(W.Apply(c, d))))
	verify(ForAll(a, b, c, W)(W.Apply(a, b).Eq(W.Apply(c, d))),
		ForAll(b, a, c, W)(W.Apply(a, b).Eq(W.Apply(c, d))))
	verify(ForAll(a, b, c, W)(W.Apply(a, b).Eq(W.Apply(c, d))),
		ForAll(a, c, b, W)(W.Apply(a, b).Eq(W.Apply(c, d))))
	verify(ForAll(a, b, d, W)(W.Apply(a, b).Eq(a.Eq(b))),
		ForAll(W, c, b, d)(W.Apply(b, c).Eq(b.Eq(c))))
	verify(ForAll(a, b, W)(W.Apply(a, b).Eq(a.Eq(b))),
		ForAll(d, W, c)(W.Apply(d, c).Eq(d.Eq(c))))

	thm = WrapProp(testThm(P.Apply(a), ForAll(a)(P.Apply(a))))
	assertPropAlphaEqual(t,
		thm.ConclForAll(a.AssertVar()),
		testThm(ForAll(a)(P.Apply(a)), ForAll(a)(P.Apply(a))))

	thm = WrapProp(testThm(P.Apply(a), ForAll(a)(P.Apply(a)), Q.Apply(a)))
	assert.Panics(t, func() { thm.ConclForAll(a.AssertVar()) })

	/////////////////////////
	// Test ∃
	/////////////////////////

	assertPropAlphaEqual(t,
		InstExists(Exists(a)(P.Apply(a)), b),
		testThm(Exists(a)(P.Apply(a)), P.Apply(b)))

	assertPropAlphaEqual(t,
		MootExists(b.AssertVar(), (Q.Apply(a))),
		testThm(Exists(b)(Q.Apply(a)).Eq(Q.Apply(a))))

	assertPropAlphaEqual(t,
		MootExists(q.AssertVar(), (R.Apply(p))),
		testThm(Exists(q)(R.Apply(p)).Eq(R.Apply(p))))

	assertPropAlphaEqual(t,
		SelectExists(a.To(Q.Apply(a))),
		testThm(Q.Apply(a.SuchThat(Q.Apply(a))), Exists(a)(Q.Apply(a))))

	assertPropAlphaEqual(t,
		NegExists(a.To(Not(Q.Apply(a)))),
		testThm(Not(Exists(b)(Not(Q.Apply(b)))).Eq(
			ForAll(b)(Not(Not(Q.Apply(b)))))))

	assertPropAlphaEqual(t,
		BoolExists(r.To(R.Apply(r))),
		testThm(Exists(r)(R.Apply(r)).Eq(R.Apply(T).Or(R.Apply(F)))))

	assertPropAlphaEqual(t,
		ExistsAND(a.To(Q.Apply(a)), a.To(P.Apply(a))),
		testThm(
			Exists(a)(Q.Apply(a)).And(Exists(a)(P.Apply(a))),
			Exists(a)(Q.Apply(a).And(P.Apply(a)))))

	assertPropAlphaEqual(t,
		ExistsOR(a.To(Q.Apply(a)), a.To(b.To(Q.Apply(b)).Apply(a))),
		testThm(
			Exists(a)(Q.Apply(a).Or(b.To(Q.Apply(b)).Apply(a))).Eq(
				Exists(a)(Q.Apply(a)).Or(Exists(a)(b.To(Q.Apply(b)).Apply(a))))))

	assertPropAlphaEqual(t,
		ExistsIMPLY(a.To(Q.Apply(a)), a.To(P.Apply(a))),
		testThm(
			Exists(a)(P.Apply(a)),
			ForAll(a)(Q.Apply(a).Imply(P.Apply(a))),
			Exists(a)(Q.Apply(a))))

	assertPropAlphaEqual(t,
		WrapProp(testThm(P.Apply(a), Q.Apply(a), R.Apply(h))).
			ConclExistsInst(a.AssertVar()).
			HypExists(a.AssertVar(), Q.Apply(a)),
		testThm(
			Exists(a)(P.Apply(a)),
			Exists(a)(Q.Apply(a)),
			R.Apply(h)))

	assertPropAlphaEqual(t,
		ReorderExists(
			Exists(a, b, c, d)(Not(W.Apply(a, b).Imply(W.Apply(c, d)))),
			Exists(d, c, b, a)(Not(W.Apply(a, b).Imply(W.Apply(c, d))))),
		testThm(Exists(a, b, c, d)(Not(W.Apply(a, b).Imply(W.Apply(c, d)))).
			Eq(Exists(d, c, b, a)(Not(W.Apply(a, b).Imply(W.Apply(c, d)))))))

	assertPropAlphaEqual(t,
		ReorderExists(
			Exists(a, b, c)(Not(W.Apply(a, b).Imply(b.Eq(c)))),
			Exists(d, c, a)(Not(W.Apply(a, d).Imply(d.Eq(c))))),
		testThm(Exists(a, b, c)(Not(W.Apply(a, b).Imply(b.Eq(c)))).
			Eq(Exists(d, c, a)(Not(W.Apply(a, d).Imply(d.Eq(c)))))))

	thm = WrapProp(testThm(ForAll(a)(P.Apply(a)), P.Apply(b)))
	assertPropAlphaEqual(t,
		thm.HypExists(b.AssertVar(), P.Apply(b)),
		testThm(ForAll(a)(P.Apply(a)), Exists(b)(P.Apply(b))))

	thm = WrapProp(testThm(ForAll(a)(P.Apply(a)), P.Apply(b), Q.Apply(b)))
	assert.Panics(t, func() { thm.HypExists(b.AssertVar(), P.Apply(b)) })

	thm = WrapProp(testThm(P.Apply(a), P.Apply(b), Q.Apply(a)))
	assert.Panics(t, func() { thm.HypExists(a.AssertVar(), Q.Apply(a)) })

	/////////////////////////
	// Test ∃!
	/////////////////////////

	assertPropAlphaEqual(t,
		AltUnique(a.To(Q.Apply(a))),
		testThm(
			Unique(a)(Q.Apply(a)).Eq(
				Exists(a)(Q.Apply(a)).And(
					ForAll(a, b)((Q.Apply(a).And(Q.Apply(b)).Imply(a.Eq(b))))))))

	assertPropAlphaEqual(t,
		WitnessUnique(a.To(Q.Apply(a))),
		testThm(
			Unique(a)(Q.Apply(a)).Eq(
				Exists(a)(Q.Apply(a).And(
					ForAll(b)(Q.Apply(b).Imply(b.Eq(a))))))))

	// A predicate with a free variable under the name the inner binder is
	// renamed to: the instantiation renames the binder away from it.
	aNext := WrapTerm(a.AssertVar().Rename())
	assertPropAlphaEqual(t,
		WitnessUnique(a.To(W.Apply(a, aNext))),
		testThm(
			Unique(a)(W.Apply(a, aNext)).Eq(
				Exists(a)(W.Apply(a, aNext).And(
					ForAll(d)(W.Apply(d, aNext).Imply(d.Eq(a))))))))
	assert.False(t, aNext.Equals(d))

	Sprime := WrapTerm(S.AssertVar().Rename())
	assert.Panics(t, func() {
		SkolemUnique(S.AssertVar(),
			a.To(b.To(W.Apply(c.To(Sprime.Apply(c)).Apply(a), b))))
	})

	assertPropAlphaEqual(t,
		SkolemAltUnique(S.AssertVar(), a.To(b.To(W.Apply(a, b)))),
		testThm(
			ForAll(a)(Unique(b)(W.Apply(a, b))).Eq(
				Unique(S)(ForAll(a)(W.Apply(a, S.Apply(a)))))))
}

func TestPrenex(t *testing.T) {
	a := Var("a", TypeInd)
	b := Var("b", TypeInd)
	P := Var("P", MakeFun(TypeInd, TypeBool))
	Q := Var("Q", MakeFun(TypeInd, TypeBool))

	assertPropAlphaEqual(t,
		PrenexThms["(∀x.P(x)) ∧ Q ⇔ ∀x.(P(x) ∧ Q)"](
			a.To(P.Apply(a)), Q.Apply(b)),
		testThm(
			ForAll(a)(P.Apply(a)).And(Q.Apply(b)).Eq(
				ForAll(a)(P.Apply(a).And(Q.Apply(b))))))
	assertPropAlphaEqual(t,
		PrenexThms["(∀x.P(x)) ∧ Q ⇔ ∀x.(P(x) ∧ Q)"](
			a.To(P.Apply(a)), Q.Apply(a)),
		testThm(
			ForAll(b)(P.Apply(b)).And(Q.Apply(a)).Eq(
				ForAll(b)(P.Apply(b).And(Q.Apply(a))))))
	assertPropAlphaEqual(t,
		PrenexThms["Q ∧ ∀x.P(x) ⇔ ∀x.(Q ∧ P(x))"](
			a.To(Q.Apply(a)), P.Apply(b)),
		testThm(
			P.Apply(b).And(ForAll(a)(Q.Apply(a))).Eq(
				ForAll(a)(P.Apply(b).And(Q.Apply(a))))))
	assertPropAlphaEqual(t,
		PrenexThms["Q ∧ ∀x.P(x) ⇔ ∀x.(Q ∧ P(x))"](
			a.To(Q.Apply(a)), P.Apply(a)),
		testThm(
			P.Apply(a).And(ForAll(b)(Q.Apply(b))).Eq(
				ForAll(b)(P.Apply(a).And(Q.Apply(b))))))

	assertPropAlphaEqual(t,
		PrenexThms["(∃x.P(x)) ∧ Q ⇔ ∃x.(P(x) ∧ Q)"](
			a.To(P.Apply(a)), Q.Apply(b)),
		testThm(
			Exists(a)(P.Apply(a)).And(Q.Apply(b)).Eq(
				Exists(a)(P.Apply(a).And(Q.Apply(b))))))

	assertPropAlphaEqual(t,
		PrenexThms["Q ∧ ∃x.P(x) ⇔ ∃x.(Q ∧ P(x))"](
			a.To(Q.Apply(a)), P.Apply(b)),
		testThm(
			P.Apply(b).And(Exists(a)(Q.Apply(a))).Eq(
				Exists(a)(P.Apply(b).And(Q.Apply(a))))))
	assertPropAlphaEqual(t,
		PrenexThms["Q ∧ ∃x.P(x) ⇔ ∃x.(Q ∧ P(x))"](
			a.To(Q.Apply(a)), P.Apply(a)),
		testThm(
			P.Apply(a).And(Exists(b)(Q.Apply(b))).Eq(
				Exists(b)(P.Apply(a).And(Q.Apply(b))))))

	assertPropAlphaEqual(t,
		PrenexThms["(∀x.P(x)) ∨ Q ⇔ ∀x.(P(x) ∨ Q)"](
			a.To(P.Apply(a)), Q.Apply(b)),
		testThm(
			ForAll(a)(P.Apply(a)).Or(Q.Apply(b)).Eq(
				ForAll(a)(P.Apply(a).Or(Q.Apply(b))))))
	assertPropAlphaEqual(t,
		PrenexThms["(∀x.P(x)) ∨ Q ⇔ ∀x.(P(x) ∨ Q)"](
			a.To(P.Apply(a)), Q.Apply(a)),
		testThm(
			ForAll(b)(P.Apply(b)).Or(Q.Apply(a)).Eq(
				ForAll(b)(P.Apply(b).Or(Q.Apply(a))))))
	assertPropAlphaEqual(t,
		PrenexThms["Q ∨ ∀x.P(x) ⇔ ∀x.(Q ∨ P(x))"](
			a.To(Q.Apply(a)), P.Apply(b)),
		testThm(
			P.Apply(b).Or(ForAll(a)(Q.Apply(a))).Eq(
				ForAll(a)(P.Apply(b).Or(Q.Apply(a))))))
	assertPropAlphaEqual(t,
		PrenexThms["Q ∨ ∀x.P(x) ⇔ ∀x.(Q ∨ P(x))"](
			a.To(Q.Apply(a)), P.Apply(a)),
		testThm(
			P.Apply(a).Or(ForAll(b)(Q.Apply(b))).Eq(
				ForAll(b)(P.Apply(a).Or(Q.Apply(b))))))

	assertPropAlphaEqual(t,
		PrenexThms["(∃x.P(x)) ∨ Q ⇔ ∃x.(P(x) ∨ Q)"](
			a.To(P.Apply(a)), Q.Apply(b)),
		testThm(
			Exists(a)(P.Apply(a)).Or(Q.Apply(b)).Eq(
				Exists(a)(P.Apply(a).Or(Q.Apply(b))))))
	assertPropAlphaEqual(t,
		PrenexThms["(∃x.P(x)) ∨ Q ⇔ ∃x.(P(x) ∨ Q)"](
			a.To(P.Apply(a)), Q.Apply(a)),
		testThm(
			Exists(b)(P.Apply(b)).Or(Q.Apply(a)).Eq(
				Exists(b)(P.Apply(b).Or(Q.Apply(a))))))
	assertPropAlphaEqual(t,
		PrenexThms["Q ∨ ∃x.P(x) ⇔ ∃x.(Q ∨ P(x))"](
			a.To(Q.Apply(a)), P.Apply(b)),
		testThm(
			P.Apply(b).Or(Exists(a)(Q.Apply(a))).Eq(
				Exists(a)(P.Apply(b).Or(Q.Apply(a))))))
	assertPropAlphaEqual(t,
		PrenexThms["Q ∨ ∃x.P(x) ⇔ ∃x.(Q ∨ P(x))"](
			a.To(Q.Apply(a)), P.Apply(a)),
		testThm(
			P.Apply(a).Or(Exists(b)(Q.Apply(b))).Eq(
				Exists(b)(P.Apply(a).Or(Q.Apply(b))))))

	assertPropAlphaEqual(t,
		PrenexThms["(∀x.P(x)) ⇒ Q ⇔ ∃x.(P(x) ⇒ Q)"](
			a.To(P.Apply(a)), Q.Apply(b)),
		testThm(
			ForAll(a)(P.Apply(a)).Imply(Q.Apply(b)).Eq(
				Exists(a)(P.Apply(a).Imply(Q.Apply(b))))))
	assertPropAlphaEqual(t,
		PrenexThms["(∀x.P(x)) ⇒ Q ⇔ ∃x.(P(x) ⇒ Q)"](
			a.To(P.Apply(a)), Q.Apply(a)),
		testThm(
			ForAll(b)(P.Apply(b)).Imply(Q.Apply(a)).Eq(
				Exists(b)(P.Apply(b).Imply(Q.Apply(a))))))
	assertPropAlphaEqual(t,
		PrenexThms["Q ⇒ ∀x.P(x) ⇔ ∀x.(Q ⇒ P(x))"](
			a.To(Q.Apply(a)), P.Apply(b)),
		testThm(
			P.Apply(b).Imply(ForAll(a)(Q.Apply(a))).Eq(
				ForAll(a)(P.Apply(b).Imply(Q.Apply(a))))))
	assertPropAlphaEqual(t,
		PrenexThms["Q ⇒ ∀x.P(x) ⇔ ∀x.(Q ⇒ P(x))"](
			a.To(Q.Apply(a)), P.Apply(a)),
		testThm(
			P.Apply(a).Imply(ForAll(b)(Q.Apply(b))).Eq(
				ForAll(b)(P.Apply(a).Imply(Q.Apply(b))))))

	assertPropAlphaEqual(t,
		PrenexThms["(∃x.P(x)) ⇒ Q ⇔ ∀x.(P(x) ⇒ Q)"](
			a.To(P.Apply(a)), Q.Apply(b)),
		testThm(
			Exists(a)(P.Apply(a)).Imply(Q.Apply(b)).Eq(
				ForAll(a)(P.Apply(a).Imply(Q.Apply(b))))))
	assertPropAlphaEqual(t,
		PrenexThms["(∃x.P(x)) ⇒ Q ⇔ ∀x.(P(x) ⇒ Q)"](
			a.To(P.Apply(a)), Q.Apply(a)),
		testThm(
			Exists(b)(P.Apply(b)).Imply(Q.Apply(a)).Eq(
				ForAll(b)(P.Apply(b).Imply(Q.Apply(a))))))

	assertPropAlphaEqual(t,
		PrenexThms["Q ⇒ ∃x.P(x) ⇔ ∃x.(Q ⇒ P(x))"](
			a.To(Q.Apply(a)), P.Apply(b)),
		testThm(
			P.Apply(b).Imply(Exists(a)(Q.Apply(a))).Eq(
				Exists(a)(P.Apply(b).Imply(Q.Apply(a))))))
	assertPropAlphaEqual(t,
		PrenexThms["Q ⇒ ∃x.P(x) ⇔ ∃x.(Q ⇒ P(x))"](
			a.To(Q.Apply(a)), P.Apply(a)),
		testThm(
			P.Apply(a).Imply(Exists(b)(Q.Apply(b))).Eq(
				Exists(b)(P.Apply(a).Imply(Q.Apply(b))))))
}

func TestDenote(t *testing.T) {
	a := Var("a", TypeInd)
	b := Var("b", TypeInd)
	c := Var("c", TypeInd)
	P := Var("P", MakeFun(TypeInd, TypeInd))
	Q := Var("Q", MakeFun(TypeInd, TypeBool))

	assertPropAlphaEqual(t,
		ForAllDenote(a.AssertVar(), P.Apply(b), a.To(Q.Apply(a))),
		testThm(Q.Apply(P.Apply(b)).Eq(ForAll(a)(a.Eq(P.Apply(b)).Imply(Q.Apply(a))))))
	assertPropAlphaEqual(t,
		ForAllDenote(a.AssertVar(), P.Apply(b), a.To(Q.Apply(c))),
		testThm(Q.Apply(c).Eq(ForAll(a)(a.Eq(P.Apply(b)).Imply(Q.Apply(c))))))

	assertPropAlphaEqual(t,
		ExistsDenote(a.AssertVar(), P.Apply(b), a.To(Q.Apply(a))),
		testThm(Q.Apply(P.Apply(b)).Eq(Exists(a)(a.Eq(P.Apply(b)).And(Q.Apply(a))))))
	assertPropAlphaEqual(t,
		ExistsDenote(a.AssertVar(), P.Apply(b), a.To(Q.Apply(c))),
		testThm(Q.Apply(c).Eq(Exists(a)(a.Eq(P.Apply(b)).And(Q.Apply(c))))))
}
