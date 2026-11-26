// sequences.go — identities of the trace sequence s and the Lucas sequence
// u of a and q. Both sequences are read through their pair states, whose
// two components step from (x, y) to (y, a·y − q·x): the Lucas sequence's
// determinant identity, the trace written through the Lucas sequence, and
// the discriminant identity the two combine to.

package zeta_recurrence

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_pow"
	"github.com/euc-ai/xugo/library/registry"
)

var TraceSequenceSign = traceSequenceSignThm{family.Add(registry.ProofEntry{
	Name: "TraceSequenceSign",
	Key:  "prop_8684a05752467829",
	Deps: []registry.EntryLike{traceSequenceDef, int_pow.IntPowDef},
	Build: family.Card(
		"∀a:int. ∀q n:num. "+
			"    elliptic_trace_sequence(-a, q, n) = int_pow(-(1), n) * elliptic_trace_sequence(a, q, n)",
		"Induct through the pair-state recurrence; the two consecutive "+
			"components have their respective alternating signs."),
})}

// LucasDeterminant — the quadratic form of two consecutive Lucas numbers is
// the n-th power of q, the determinant of the recurrence's matrix raised to
// the n-th power: by induction on n, one step of the recurrence multiplying
// the form by q.
var LucasDeterminant = lucasDeterminantThm{family.Add(registry.ProofEntry{
	Name: "LucasDeterminant",
	Key:  "prop_98c4c867db93bede",
	Build: family.Theorem(
		"∀a:int. ∀q n:num. "+
			"    int_pow(elliptic_lucas_sequence(a, q, suc(n)), 2) - "+
			"    a * elliptic_lucas_sequence(a, q, suc(n)) * elliptic_lucas_sequence(a, q, n) + "+
			"    &q * int_pow(elliptic_lucas_sequence(a, q, n), 2) = "+
			"    int_pow(q, n)",
		func(arg *Argument, a *Expr[Int], q *Expr[Nat]) {
			arg.Induct("n")
			arg.Base(
				"u₀ = 0 and u₁ = 1, so the form is 1 = q⁰",
				Simp(
					Fwd(lucasSequenceDef),
					Fwd(traceStateDef),
					Fwd(pairs.Fst),
					Fwd(pairs.Snd),
					Fwd(int_pow.PowClauses)),
				ByArith())
			arg.Step(
				"one step of the recurrence multiplies the form by q",
				func(b *Argument, form Fact) {
					recurrence := b.Have(
						"unfolding one step of the state, u obeys the recurrence that reaches back two steps",
						"elliptic_lucas_sequence(a, q, suc(suc(n))) = "+
							"a * elliptic_lucas_sequence(a, q, suc(n)) - &q * elliptic_lucas_sequence(a, q, n)",
						Simp(Fwd(lucasSequenceDef), Fwd(traceStateDef), Fwd(pairs.Fst), Fwd(pairs.Snd)),
						Refl())
					b.Show(
						"substituted, the form at n + 1 is q times the form at n, and q^(n+1) = q·qⁿ",
						recurrence.Rw(),
						Simp(Fwd(int_pow.PowClauses)),
						ByArith(Scaled(b.TermAs[Int]("&q"), form)))
				})
		}),
})}

// TraceFromLucas — the trace sequence is twice the next Lucas number less
// a times the current one: both sides obey one recurrence, which reaches
// back two steps, so the induction carries the identity at n and at n + 1
// together.
var TraceFromLucas = traceFromLucasThm{family.Add(registry.ProofEntry{
	Name: "TraceFromLucas",
	Key:  "prop_e8104dc16cd5e578",
	Build: family.Sections(
		"∀a:int. ∀q n:num. "+
			"    elliptic_trace_sequence(a, q, n) = "+
			"    2 * elliptic_lucas_sequence(a, q, suc(n)) - a * elliptic_lucas_sequence(a, q, n)",
		func(ctx *Script, headline string) *GoalStackNode {
			pair := ctx.Lemma(
				"∀a:int. ∀q n:num. "+
					"    elliptic_trace_sequence(a, q, n) = "+
					"    2 * elliptic_lucas_sequence(a, q, suc(n)) - a * elliptic_lucas_sequence(a, q, n) ∧ "+
					"    elliptic_trace_sequence(a, q, suc(n)) = "+
					"    2 * elliptic_lucas_sequence(a, q, suc(suc(n))) - a * elliptic_lucas_sequence(a, q, suc(n))",
				func(arg *Argument, a *Expr[Int], q *Expr[Nat]) {
					arg.Induct("n")
					arg.Base(
						"s₀ = 2 = 2·u₁ − a·u₀ and s₁ = a = 2·u₂ − a·u₁",
						Simp(
							Fwd(traceSequenceDef),
							Fwd(lucasSequenceDef),
							Fwd(traceStateDef),
							Fwd(pairs.Fst),
							Fwd(pairs.Snd)),
						ByArith())
					arg.Step(
						"the pair moves up one index: the identity at n + 1 "+
							"is carried over, the one at n + 2 computed from both",
						func(b *Argument, both Fact) {
							identity := b.Conjuncts(
								both,
								"the identity at n",
								"the identity at n + 1")
							b.Show(
								"read in the states' components, a times the identity at "+
									"n + 1 less q times the one at n is the identity at n + 2",
								SimpAll(
									Fwd(traceSequenceDef),
									Fwd(lucasSequenceDef),
									Fwd(traceStateDef),
									Fwd(pairs.Fst),
									Fwd(pairs.Snd)),
								ByArith(Scaled(b.TermAs[Int]("&q"), identity[0]), Scaled(a, identity[1])))
						})
				})
			return ctx.Theorem(headline, func(arg *Argument, a *Expr[Int], q, n *Expr[Nat]) {
				arg.Show(
					"the first of the pair at n",
					By(At(pair, a, q, n)))
			})
		}),
})}

// LucasIdentity — the square of the trace less four times the n-th power
// of q is the discriminant of 1 − aT + qT² times the square of the Lucas
// number: written through the Lucas sequence, the difference of its two
// sides is four times that of the determinant identity's.
var LucasIdentity = lucasIdentityThm{family.Add(registry.ProofEntry{
	Name: "LucasIdentity",
	Key:  "prop_f7aa460f1154a2f2",
	Build: family.Theorem(
		"∀a:int. ∀q n:num. "+
			"    int_pow(elliptic_trace_sequence(a, q, n), 2) - 4 * int_pow(q, n) = "+
			"    (int_pow(a, 2) - 4 * &q) * int_pow(elliptic_lucas_sequence(a, q, n), 2)",
		func(arg *Argument, a *Expr[Int], q, n *Expr[Nat]) {
			arg.Show(
				"with s_n = 2·u_{n+1} − a·u_n the two sides differ by "+
					"4·(u_{n+1}² − a·u_{n+1}·u_n + q·u_n² − qⁿ), which is zero",
				Simp(Fwd(TraceFromLucas)),
				ByArith(LucasDeterminant.At(a, q, n)))
		}),
})}
