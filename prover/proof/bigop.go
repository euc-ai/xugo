// bigop.go — a big-operator term read with its parts: the range and the
// summand of a Σ, the index set and the body of a fold.
//
// The sum laws take their summand as a FUNCTION — `real_sum(s, f) ≤ real_sum(s,
// g)`, `real_sum(s, f) * c = real_sum(s, λx. f(x) * c)` — while a claim writes
// the big operator, `Σ_{i<m} ‖f(eᵢ)‖`. A body citing a law about a sum
// its claim shows therefore spelled the summand twice, once as `λi. …`
// for the law's slot and once under the Σ, and kept the two agreeing
// by hand; nothing checked that the λ handed to the law was the summand
// of the Σ in the claim, and a mismatch surfaced as a close that would
// not fire. A BigOp is one spelling read three ways — the term itself,
// its range, its summand — so the λ is derived from the Σ rather than
// restated beside it.

package proof

import (
	"fmt"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
)

// BigOp is a big-operator application — `real_sum(s, λi. b)` at ℝ, the fold
// `iterated_op(op, s, λi. b)` at vectors, whatever a chapter declared as
// one (registry.DefEntry.BigOp) — adopted at its carrier T with index
// type I and carrying its two parts. Built only by BigOpAs, so holding
// one IS holding a term the scope's syntax table recognizes as a big
// operator.
type BigOp[I, T ext.TypePhantom] struct {
	*ext.Expr[T]
	rng     *ext.Expr[ext.Set[I]]
	summand *ext.Expr[ext.Fun[I, T]]
}

// Range is the index set: the `{i | i < m}` of `Σ_{i<m}`, the `s` of
// `Σ_{i∈s}` — what a law's set slot takes.
func (b *BigOp[I, T]) Range() *ext.Expr[ext.Set[I]] { return b.rng }

// Summand is the body as the function of the index — what a law's
// summand slot takes, `λi. …` derived rather than spelled.
func (b *BigOp[I, T]) Summand() *ext.Expr[ext.Fun[I, T]] { return b.summand }

// BigOpAs parses a term text as a big-operator application and reads
// its range and summand off it. What counts as one is what the text
// layer writes a `Σ_{…}` for (ext/dsl/bigop.go, foldBigOps): a
// constant the scope declares as a big operator — `sum` at ℝ, `nat_sum`
// at ℕ — applied, after its implicit prefix, to the range and the
// summand; or the fold `iterated_op(op, range, summand)`, which is the Σ
// at every carrier that mints no sum of its own (the vectors: the fold
// at `vadd`). Anything else panics naming the head, and so does a sum
// applied beyond its terms — `(Σ_{i∈s} F(i))(j)` is a coordinate, not
// a sum.
//
//	total := a.BigOpAs[Nat, Real]("Σ_{i<m} ‖f(vbasis(i))‖_n")
//	… real_sum.ScalarRight.At(c, total.Summand(), total.Range()) …
func (a *Argument) BigOpAs[I, T ext.TypePhantom](raw string) *BigOp[I, T] {
	a.guardRead("BigOpAs")
	t := a.Term(raw)
	head, args := ext.MatchesApply(t)
	c, ok := head.Core().(core.ConstTerm)
	if !ok {
		panic(fmt.Sprintf("Argument.BigOpAs: %s is not a big-operator application — its head %s is not a constant",
			ext.PrintTerm(t), ext.PrintTerm(head)))
	}
	name := string(c.Name())
	// The position of the range among the arguments: after the implicit
	// prefix for a declared big operator, after the operation for the fold.
	var at int
	switch {
	case name == "iterated_op":
		at = 1
	case a.s.ParseScope.Syntax != nil && a.s.ParseScope.Syntax.ConstSyntax(name) != nil &&
		a.s.ParseScope.Syntax.ConstSyntax(name).BigOp != nil:
		at = len(a.s.ParseScope.Syntax.ConstSyntax(name).Implicit)
	default:
		panic(fmt.Sprintf("Argument.BigOpAs: %s is not a big-operator application — the scope declares no big operator at %s, and it is not the fold",
			ext.PrintTerm(t), name))
	}
	if len(args) != at+2 {
		panic(fmt.Sprintf("Argument.BigOpAs: %s applies %s to %d argument(s), and a big operator takes its range and its summand at positions %d and %d — a sum applied beyond its terms is a coordinate, not a sum",
			ext.PrintTerm(t), name, len(args), at, at+1))
	}
	return &BigOp[I, T]{
		Expr:    ext.As[T](t),
		rng:     ext.As[ext.Set[I]](args[at]),
		summand: ext.As[ext.Fun[I, T]](args[at+1]),
	}
}
