package zeta_recurrence

import (
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/finite_field"
	_ "github.com/euc-ai/xugo/library/proofs/int_num/int_construction"
	_ "github.com/euc-ai/xugo/library/proofs/int_num/int_pow"
	_ "github.com/euc-ai/xugo/library/proofs/scheme/algebraic_curve"
	_ "github.com/euc-ai/xugo/library/proofs/scheme/closed_point"
	_ "github.com/euc-ai/xugo/library/proofs/scheme/elliptic_curve"
	_ "github.com/euc-ai/xugo/library/proofs/scheme/lattice_pair"
	_ "github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/registry"
)

var traceStateDef = traceStateDefThm{family.Define(registry.DefEntry{
	Name:  "traceStateDef",
	Key:   "prop_4fdd02f8511c60ae",
	Const: "elliptic_trace_state",
	Type:  "num → int → num → int → int → prod(int, int)",
	Equations: []string{
		"∀a u v:int. ∀q:num. elliptic_trace_state(0, a, q, u, v) = (u, v)",
		"∀n q:num. ∀a u v:int. " +
			"    elliptic_trace_state(suc(n), a, q, u, v) = " +
			"    (snd(elliptic_trace_state(n, a, q, u, v)), " +
			"        a * snd(elliptic_trace_state(n, a, q, u, v)) - " +
			"        q * fst(elliptic_trace_state(n, a, q, u, v)))",
	},
})}

var traceSequenceDef = traceSequenceDefThm{family.Define(registry.DefEntry{
	Name:  "traceSequenceDef",
	Key:   "prop_6b69215a21d23b7",
	Const: "elliptic_trace_sequence",
	Type:  "int → num → num → int",
	Equations: []string{
		"∀a:int. ∀q n:num. elliptic_trace_sequence(a, q, n) = fst(elliptic_trace_state(n, a, q, 2, a))",
	},
	Deps: []registry.EntryLike{traceStateDef},
})}

var lucasSequenceDef = lucasSequenceDefThm{family.Define(registry.DefEntry{
	Name:  "lucasSequenceDef",
	Key:   "prop_633678309f22afa7",
	Const: "elliptic_lucas_sequence",
	Type:  "int → num → num → int",
	Equations: []string{
		"∀a:int. ∀q n:num. elliptic_lucas_sequence(a, q, n) = fst(elliptic_trace_state(n, a, q, 0, 1))",
	},
	Deps: []registry.EntryLike{traceStateDef},
})}
