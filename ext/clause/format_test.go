package clause

import (
	"fmt"
	"testing"

	"github.com/stretchr/testify/assert"
)

func checkFormat[T any](t *testing.T, s T, f string) {
	assert.Equal(t, fmt.Sprint(s), f)
}

func TestFormatClause(t *testing.T) {
	a := Var("a", TypeInd)
	b := Var("b", TypeA)
	D := Var("D", MakeFun(TypeInd, TypeBool))
	q := Var("q", TypeBool)
	P := Var("P", MakeFun(TypeA, TypeBool))

	checkFormat(t, MakeClause(P.Apply(b).Or(Not(D.Apply(a)))),
		"¬D(a) | P(b)")
	checkFormat(t, MakeClause(ForAll(a, b)(D.Apply(a).Or(Not(P.Apply(b))).Or(q))),
		"∀a.∀b.\n\t¬P(b) | D(a) | q")
}

func ExampleFormatClauseThm() {
	a := Var("a", TypeInd)
	b := Var("b", TypeA)
	D := Var("D", MakeFun(TypeInd, TypeBool))
	h := Var("h", TypeBool)
	P := Var("P", MakeFun(TypeA, TypeBool))
	R := Var("R", MakeFun(TypeBool, TypeBool))
	fmt.Println(MakeClauseThm(
		testThm(ForAll(b)(P.Apply(b))),
		MakeClause(ForAll(b)(P.Apply(b)))))
	fmt.Println()
	fmt.Println(MakeClauseThm(
		testThm(R.Apply(h), ForAll(b)(P.Apply(b))),
		MakeClause(R.Apply(h)), MakeClause(ForAll(b)(P.Apply(b)))))
	fmt.Println()
	fmt.Println(MakeClauseThm(
		testThm(
			F, R.Apply(h), ForAll(b)(P.Apply(b).Or(h)), ForAll(D)(D.Apply(a)), P.Apply(b)),
		FClause,
		MakeClause(R.Apply(h)),
		MakeClause(ForAll(b)(P.Apply(b).Or(h))),
		MakeClause(ForAll(D)(D.Apply(a))),
		MakeClause(P.Apply(b))))
	fmt.Println()
	fmt.Println(MakeClauseThm(
		testThm(
			ForAll(b)(P.Apply(b).Or(h)), R.Apply(h), ForAll(D)(D.Apply(a)), P.Apply(b)),
		MakeClause(ForAll(b)(P.Apply(b).Or(h))),
		MakeClause(R.Apply(h)),
		MakeClause(ForAll(D)(D.Apply(a))),
		MakeClause(P.Apply(b))))
	// Output:
	// ⊢ ∀b.
	// 	P(b)
	//
	// ∀b.
	// 	P(b)
	// 	⊢ R(h)
	//
	// P(b),
	// R(h),
	// ∀D.
	// 	D(a),
	// ∀b.
	// 	P(b) | h
	// 	⊢ ⊥
	//
	// P(b),
	// R(h),
	// ∀D.
	// 	D(a)
	// 	⊢ ∀b.
	// 		P(b) | h
}

func ExampleFormatConjunctiveClauses() {
	a := Var("a", TypeInd)
	b := Var("b", TypeA)
	D := Var("D", MakeFun(TypeInd, TypeBool))
	h := Var("h_0", TypeBool)
	P := Var("P", MakeFun(TypeA, TypeBool))
	R := Var("R", MakeFun(TypeBool, TypeBool))

	fmt.Println(mustMakeCNF(ForAll(D, a)(Not(D.Apply(a)))))
	fmt.Println()
	fmt.Println(mustMakeCNF(ForAll(D, a, b)(
		Not(D.Apply(a)).Or(P.Apply(b))).And(ForAll(D, a)(
		(R.Apply(h)).Or(D.Apply(a))))))
	fmt.Println()
	fmt.Println(mustMakeCNF(ForAll(D, a, b)(
		Not(D.Apply(a)).Or(P.Apply(b))).And(ForAll(D, a)(
		(R.Apply(h)).Or(D.Apply(a))))))
	fmt.Println()
	fmt.Println(mustMakeCNF(ForAll(D, a, b)(
		Not(D.Apply(a)).Or(P.Apply(b))).And(ForAll(D, a)(
		(R.Apply(h)).Or(D.Apply(a))))))
	// Output:
	// ∀D.∀a.
	// 	¬D(a)
	//
	// P:(var:A → bool), R:(bool → bool), h₀:bool,
	// 	∀D.∀a.
	// 		R(h₀) | D(a)
	// 	∀D.∀a.∀b.
	// 		¬D(a) | P(b)
	//
	// P:(var:A → bool), R:(bool → bool), h₀:bool,
	// 	∀D.∀a.
	// 		R(h₀) | D(a)
	// 	∀D.∀a.∀b.
	// 		¬D(a) | P(b)
	//
	// P:(var:A → bool), R:(bool → bool), h₀:bool,
	// 	∀D.∀a.
	// 		R(h₀) | D(a)
	// 	∀D.∀a.∀b.
	// 		¬D(a) | P(b)
}
