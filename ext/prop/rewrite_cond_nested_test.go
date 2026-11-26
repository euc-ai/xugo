package prop

import (
	"testing"
	"time"

	"github.com/euc-ai/xugo/ext"
	"github.com/stretchr/testify/require"
)

// nestedFaceEquation is the shape `def_expand nerve_face` leaves on the
// simplicial identity d_i d_j = d_{j−1} d_i after funext: a five-guard
// COND tree whose leaves apply a second such tree, on both sides of
// one equation under ∀x. Guards are free predicates over free index
// functions, so no two guards are the same term unless the definition
// makes them so, as in the corpus.
func nestedFaceEquation() *ext.TermWrapper {
	index := TypeInd
	succ := Var("succ", MakeFun(index, index))
	pred := Var("pred", MakeFun(index, index))
	lt := Var("lt", MakeFun(index, index, TypeBool))
	zero := Var("zero", index)
	ident := Var("ident", MakeFun(index, index))
	source := Var("source", MakeFun(index, index))
	comp := Var("comp", MakeFun(index, index, index))
	f := Var("f", MakeFun(index, index))
	n := Var("n", index)
	i := Var("i", index)
	j := Var("j", index)
	x := Var("x", index)

	type chain = func(Term) Term
	// face(m, k, g)(y), nerve_face's defining equation over the free
	// vocabulary above.
	face := func(m, k Term, g chain) chain {
		return func(y Term) Term {
			sy := succ.Apply(y)
			return ext.Cond(WrapTerm(k).Eq(zero), g(sy),
				ext.Cond(WrapTerm(k).Eq(m),
					ext.Cond(lt.Apply(sy, m), g(y), ident.Apply(source.Apply(g(pred.Apply(m))))),
					ext.Cond(lt.Apply(sy, k), g(y),
						ext.Cond(WrapTerm(sy).Eq(k),
							comp.Apply(g(k), g(pred.Apply(k))),
							g(sy)))))
		}
	}
	chainOf := func(g Term) chain { return func(y Term) Term { return WrapTerm(g).Apply(y) } }
	n1, n2 := succ.Apply(n), succ.Apply(succ.Apply(n))
	left := face(n1, i, face(n2, j, chainOf(f)))(x)
	right := face(n1, pred.Apply(j), face(n2, i, chainOf(f)))(x)
	return ForAll(x)(WrapTerm(left).Eq(right))
}

// TestCondElim_NestedTreesFinish pins the cost of eliminating nested
// COND trees. Each elimination copies its atom, so the equation above
// unfolds into the product of its two sides' case trees: about 1300
// eliminations growing the term from 850 to 37k nodes. Both drivers —
// the def tidy (TrivialNormalize) and the cond_rewrite move
// (CondRewriteTactic's rewrite) — finish in about a second, which holds
// only while every COND search walks just the part of the term that
// still carries a COND and the deep walk memoizes once the term it
// grows passes the memo gate; with either walk over the whole term the
// call runs for minutes to hours (the shape is `def_expand nerve_face`'s
// tidy and `inspect`'s cond_rewrite probe on the simplicial identities).
func TestCondElim_NestedTreesFinish(t *testing.T) {
	in := nestedFaceEquation()
	for _, row := range []struct {
		name    string
		rewrite Rewrite
	}{
		{"TrivialNormalize", TrivialNormalize},
		{"cond_rewrite", BasicRewritesWith(CondElimRewrite, CondSwapRewrite)},
	} {
		t.Run(row.name, func(t *testing.T) {
			done := make(chan *PropWrapper, 1)
			go func() { done <- row.rewrite(in) }()
			select {
			case w := <-done:
				require.NotNil(t, w)
				require.Nil(t, ext.FindTopSubTerm(Rhs(w), func(s Term) bool {
					_, _, _, ok := ext.MatchesCond(s)
					return ok
				}), "every COND is eliminated")
			case <-time.After(60 * time.Second):
				t.Fatalf("%s did not finish within 60s on two nested five-guard COND trees", row.name)
			}
		})
	}
}
