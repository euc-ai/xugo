// definitions.go — the chapter's definitional layer: the pointwise
// operations, the zero-padded membership, the standard basis vectors,
// what it is for a map of one or two sequence arguments to be linear,
// and what it is for a set of sequences to be a subspace — of which the
// span of a finite family is the one this chapter builds.
//
// A vector is a sequence `num → A`. The operations read a scalar
// operation pointwise and take that operation as their first argument,
// so one constant serves every ring: `vec_add(add, u, v)` is `u + v` at
// whatever addition `add` is. Nothing here mentions a structure; the
// laws that need one state it. The definitions spell every component;
// a law under the ring leaves them implicit — `Implicit` on each entry
// names the binders the parser completes, so `vec_add(u, v)` under
// `R:ring_ops(A)` reads `vec_add(R.add, u, v)` —
// and writes the operation by its notation, declared here with
// `Notation`: `u + v` at a vector type is `vec_add(add, u, v)`, `c • u` is
// `vec_scalar_mul(mul, c, u)`, `-u` is `vec_neg(neg, u)`, `u - v` is
// `vec_sub(sub, u, v)`. The definitions themselves are stated pointwise,
// so each binds the point after the operation's arguments.
//
// Membership is where the dimension lives: `vec⟨n⟩(zero, u)` says u is
// zero from index n on, the active range being 0 .. n-1. The padding is
// the ring's own zero, which is what makes the pointwise operations
// closed without a truncation step: zero plus zero is zero and a
// scalar times zero is zero, so the subspace is closed by the ring's
// laws alone.

package vec_space

import (
	"github.com/euc-ai/xugo/library/registry"
)

// VecZeroDef — the zero vector: the constant sequence at the ring's zero.
var VecZeroDef = vecZeroDefThm{family.Define(registry.DefEntry{
	Name:      "VecZeroDef",
	Key:       "prop_3d12ccb6f79bd61b",
	Const:     "vec_zero",
	Type:      "A → num → A",
	Implicit:  []string{"zero"},
	Equations: []string{"∀zero:A. ∀i:num. vec_zero(zero, i) = zero"},
})}

// VecAddDef — pointwise addition at the given addition, written `u + v`:
// the `+` at a vector type is this constant, at the addition the scope
// binds.
var VecAddDef = vecAddDefThm{family.Define(registry.DefEntry{
	Name:     "VecAddDef",
	Key:      "prop_454c0ef9992a6de0",
	Const:    "vec_add",
	Type:     "(A → A → A) → (num → A) → (num → A) → num → A",
	Implicit: []string{"add"},
	Notation: "u + v",
	Equations: []string{
		"∀add:(A → A → A). ∀u v:(num → A). ∀i:num. vec_add(add, u, v, i) = add(u(i), v(i))",
	},
})}

// VecNegDef — pointwise negation at the given negation, written `-u`.
var VecNegDef = vecNegDefThm{family.Define(registry.DefEntry{
	Name:      "VecNegDef",
	Key:       "prop_f1cc2ddd8746b793",
	Const:     "vec_neg",
	Type:      "(A → A) → (num → A) → num → A",
	Implicit:  []string{"neg"},
	Notation:  "-u",
	Equations: []string{"∀neg:(A → A). ∀u:(num → A). ∀i:num. vec_neg(neg, u, i) = neg(u(i))"},
})}

// VecSubDef — pointwise subtraction at the given subtraction, written
// `u - v`.
var VecSubDef = vecSubDefThm{family.Define(registry.DefEntry{
	Name:     "VecSubDef",
	Key:      "prop_6a51a35e3916ac1a",
	Const:    "vec_sub",
	Type:     "(A → A → A) → (num → A) → (num → A) → num → A",
	Implicit: []string{"sub"},
	Notation: "u - v",
	Equations: []string{
		"∀sub:(A → A → A). ∀u v:(num → A). ∀i:num. vec_sub(sub, u, v, i) = sub(u(i), v(i))",
	},
})}

// VecScalarMulDef — the scalar action, written `c • u`: every entry multiplied
// by the scalar, at the given multiplication.
var VecScalarMulDef = vecScalarMulDefThm{family.Define(registry.DefEntry{
	Name:     "VecScalarMulDef",
	Key:      "prop_10d6f6d7a092d01b",
	Const:    "vec_scalar_mul",
	Type:     "(A → A → A) → A → (num → A) → num → A",
	Implicit: []string{"mul"},
	Notation: "c • u",
	Equations: []string{
		"∀mul:(A → A → A). ∀c:A. ∀u:(num → A). ∀i:num. vec_scalar_mul(mul, c, u, i) = mul(c, u(i))",
	},
})}

// VecDef — membership in dimension n: the sequence is zero from index
// n on. The active range is 0 .. n-1, and the padding is the ring's
// zero, so the predicate is monotone in n and closed under the
// pointwise operations.
var VecDef = vecDefThm{family.Define(registry.DefEntry{
	Name:     "VecDef",
	Key:      "prop_454b28fb1fff43b8",
	Const:    "vec",
	Type:     "A → num → (num → A) → bool",
	Implicit: []string{"zero"},
	Dim:      "n",
	Equations: []string{
		"∀zero:A. ∀n:num. ∀u:(num → A). vec⟨n⟩(zero, u) ⇔ (∀i:num. n ≤ i ⇒ u(i) = zero)",
	},
})}

// BasisVectorDef — the k-th standard basis vector: the ring's one at index
// k, its zero everywhere else. Both ring elements are components, as
// every other constant here takes the scalar operation it reads.
var BasisVectorDef = basisVectorDefThm{family.Define(registry.DefEntry{
	Name:     "BasisVectorDef",
	Key:      "prop_74eaf9205de63d9a",
	Const:    "basis_vector",
	Type:     "A → A → num → num → A",
	Implicit: []string{"zero", "one"},
	Equations: []string{
		"∀zero one:A. ∀k i:num. basis_vector(zero, one, k, i) = COND(i = k, one, zero)",
	},
})}

// VecLinearDef — a module homomorphism: a map on sequences that carries
// the pointwise sum to the pointwise sum and commutes with the scalar
// action. No dimension appears — linearity is a property of the map on
// all of the sequences, and the statements that need a dimension carry
// `vec` themselves.
var VecLinearDef = vecLinearDefThm{family.Define(registry.DefEntry{
	Name:     "VecLinearDef",
	Key:      "prop_23a83b3042093d97",
	Const:    "vec_linear",
	Type:     "(A → A → A) → (A → A → A) → ((num → A) → (num → A)) → bool",
	Implicit: []string{"add", "mul"},
	Equations: []string{"∀add mul:(A → A → A). ∀f:((num → A) → (num → A)). " +
		"    vec_linear(add, mul, f) ⇔ " +
		"    (∀u v:(num → A). f(vec_add(add, u, v)) = vec_add(add, f(u), f(v))) ∧ " +
		"    (∀c:A. ∀u:(num → A). f(vec_scalar_mul(mul, c, u)) = vec_scalar_mul(mul, c, f(u)))"},
	Deps: []registry.EntryLike{VecAddDef, VecScalarMulDef},
})}

// VecBilinearDef — a map of two sequence arguments, linear in each
// separately. Both slots read the same module structure; the
// definition says only that fixing either argument leaves a
// homomorphism, so everything the chapter knows about `vec_linear`
// applies to each slot. No dimension appears: bilinearity, like
// linearity, is a property of the map on all of the sequences.
//
// The map's VALUE is a sequence, so a bilinear FORM — the dot product,
// whose value is a scalar — is not an instance of this predicate,
// though it is bilinear in the ordinary sense; the form's own linearity
// in each argument is stated where the form is (the `dot` chapter).
// The two conjuncts are spelled asymmetrically, `h(u)` against
// `λu. h(u, v)`, because currying makes only the first slot's section a
// partial application; the normalizer η-contracts, so the λ a caller
// writes for that slot IS `h(u)`, and a consumer may spell either.
var VecBilinearDef = vecBilinearDefThm{family.Define(registry.DefEntry{
	Name:     "VecBilinearDef",
	Key:      "prop_5d1962b1fa969de0",
	Const:    "vec_bilinear",
	Type:     "(A → A → A) → (A → A → A) → ((num → A) → (num → A) → (num → A)) → bool",
	Implicit: []string{"add", "mul"},
	Equations: []string{
		"∀add mul:(A → A → A). ∀h:((num → A) → (num → A) → (num → A)). " +
			"    vec_bilinear(add, mul, h) ⇔ " +
			"    (∀u:(num → A). vec_linear(add, mul, h(u))) ∧ " +
			"    (∀v:(num → A). vec_linear(add, mul, λu:(num → A). h(u, v)))",
	},
	Deps: []registry.EntryLike{VecLinearDef},
})}

// VecSubspaceDef — a subspace of the sequences: a set holding the zero
// vector and closed under the pointwise sum and the scalar action.
// Nothing is said about a dimension: a subspace is a property of a set
// of sequences, and the sets that carry one need not be the vectors of
// any one dimension.
var VecSubspaceDef = vecSubspaceDefThm{family.Define(registry.DefEntry{
	Name:     "VecSubspaceDef",
	Key:      "prop_1484020e640bd7e3",
	Const:    "vec_subspace",
	Type:     "(A → A → A) → A → (A → A → A) → set(num → A) → bool",
	Implicit: []string{"add", "zero", "mul"},
	Equations: []string{"∀add:(A → A → A). ∀zero:A. ∀mul:(A → A → A). ∀s:set(num → A). " +
		"    vec_subspace(add, zero, mul, s) ⇔ " +
		"    vec_zero(zero) ∈ s ∧ " +
		"    (∀u v:(num → A). u ∈ s ∧ v ∈ s ⇒ vec_add(add, u, v) ∈ s) ∧ " +
		"    (∀c:A. ∀u:(num → A). u ∈ s ⇒ vec_scalar_mul(mul, c, u) ∈ s)"},
	Deps: []registry.EntryLike{VecZeroDef, VecAddDef, VecScalarMulDef},
})}

// VecSpanDef — the span of the first k members of a family of sequences:
// the values the fold of their scalar multiples takes as the
// coefficient sequence ranges over everything. The equation is stated
// pointwise, at the sequence asked about, so that a theorem writes
// `x ∈ vec_span(k, e)`, and the fold runs over the active range the rest
// of the chapter folds over.
var VecSpanDef = vecSpanDefThm{family.Define(registry.DefEntry{
	Name:     "VecSpanDef",
	Key:      "prop_545277d66e40541b",
	Const:    "vec_span",
	Type:     "(A → A → A) → (A → A → A) → num → (num → num → A) → set(num → A)",
	Implicit: []string{"add", "mul"},
	Equations: []string{"∀add mul:(A → A → A). ∀k:num. ∀e:(num → num → A). ∀x:(num → A). " +
		"    vec_span(add, mul, k, e, x) ⇔ " +
		"    (∃c:(num → A). " +
		"        x = iterated_op(vec_add(add), {i:num | i < k}, λi:num. vec_scalar_mul(mul, c(i), e(i))))"},
	Deps: []registry.EntryLike{VecAddDef, VecScalarMulDef},
})}
