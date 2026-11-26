// A differential form reads a point and a matrix of column vectors.
// Its increasing-coordinate expansion fixes both its degree and its
// normalization, and its coefficients are smooth on the open domain.

package vec_form

import (
	_ "github.com/euc-ai/xugo/library/proofs/algebra/group/symmetric_group"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/function_module"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	_ "github.com/euc-ai/xugo/library/proofs/vector/determinant"
	_ "github.com/euc-ai/xugo/library/proofs/vector/matrix"
	_ "github.com/euc-ai/xugo/library/proofs/vector/vec_smooth"
	"github.com/euc-ai/xugo/library/registry"
)

// FormIndicesDef — increasing lists of k coordinate indices below n,
// represented as sequences whose unused entries are zero.
var FormIndicesDef = formIndicesDefThm{family.Define(registry.DefEntry{
	Name:  "FormIndicesDef",
	Key:   "prop_961bf8888ec1bb6a",
	Const: "vec_form_indices",
	Type:  "num → num → set(num → num)",
	Reading: "The zero tail makes this indexing set finite. At degree zero " +
		"it contains the zero sequence alone; at degree greater than n it is empty.",
	Equations: []string{
		"∀n k:num. " +
			"    vec_form_indices(n, k) = " +
			"    {a:(num → num) | " +
			"        (∀j:num. j < k ⇒ a(j) < n) ∧ " +
			"        (∀i j:num. i < j ∧ j < k ⇒ a(i) < a(j)) ∧ " +
			"        (∀j:num. k ≤ j ⇒ a(j) = 0)}",
	},
})}

// formBasisDef — the n×k frame with coordinate vector e_(a(j)) in
// column j, zero-padded in both matrix indices.
var formBasisDef = formBasisDefThm{family.Define(registry.DefEntry{
	Name:      "formBasisDef",
	Key:       "prop_e14043e3f2461b33",
	Const:     "vec_form_basis",
	Type:      "num → num → (num → num) → num → num → real",
	RowDim:    "n",
	ColumnDim: "k",
	Equations: []string{
		"∀n k:num. ∀a:(num → num). ∀i j:num. " +
			"    vec_form_basis⟨n, k⟩(a, i, j) = COND(i < n ∧ j < k ∧ i = a(j), &1, &0)",
	},
})}

// FormOnDef — the coordinate expansion in increasing exterior basis
// elements, with smooth coefficients and zero values off the open set.
var FormOnDef = formOnDefThm{family.Define(registry.DefEntry{
	Name:  "FormOnDef",
	Key:   "prop_fc4b7ab2320a25d4",
	Const: "vec_form_on",
	Type:  "num → set(num → real) → num → ((num → real) → (num → num → real) → real) → bool",
	Dim:   "n",
	Deps:  []registry.EntryLike{FormIndicesDef, formBasisDef},
	Reading: "The degree k is an ordinary argument. Matrices are read only in their n×k block, " +
		"even when their tails are not zero; the determinant expansion supplies alternation and " +
		"multilinearity. Values off U are zero, so laws between forms are literal function equalities. " +
		"Openness is part of the predicate; a zero form belongs to every degree on an open domain.",
	Equations: []string{
		"∀n k:num. ∀U:set(num → real). ∀ω:((num → real) → (num → num → real) → real). " +
			"    vec_form_on⟨n⟩(U, k, ω) ⇔ " +
			"    U ∈ euclidean_topology(n) ∧ " +
			"    (∀a:(num → num). " +
			"        a ∈ vec_form_indices(n, k) ⇒ " +
			"        vec_smooth_on⟨n⟩(U, λx:(num → real). ω(x, vec_form_basis⟨n, k⟩(a)))) ∧ " +
			"    (∀x:(num → real). ∀P:(num → num → real). " +
			"        ω(x, P) = " +
			"        COND(x ∈ U, " +
			"            module_sum(real_ring.add, " +
			"                &0, " +
			"                vec_form_indices(n, k), " +
			"                λa:(num → num). " +
			"                    ω(x, vec_form_basis⟨n, k⟩(a)) * " +
			"                    determinant(real_ring, " +
			"                        k, " +
			"                        λi:num. λj:num. COND(i < k ∧ j < k, P(a(i), j), &0))), " +
			"            &0))",
	},
})}

// FormModuleDef — the form carrier inside two iterated function modules.
var FormModuleDef = formModuleDefThm{family.Define(registry.DefEntry{
	Name:  "FormModuleDef",
	Key:   "prop_60b7f066461a34f8",
	Const: "vec_form_module",
	Type: "num → " +
		"set(num → real) → " +
		"num → " +
		"module_ops(real, (num → real) → (num → num → real) → real)",
	Dim:  "n",
	Deps: []registry.EntryLike{FormOnDef},
	Equations: []string{
		"∀n k:num. ∀U:set(num → real). " +
			"    vec_form_module⟨n⟩(U, k) = " +
			"    restrict_module(function_module( " +
			"            function_module(regular_module(real_ring), 𝕌⟨A:num → num → real⟩), " +
			"            𝕌⟨A:num → real⟩), " +
			"        {ω:((num → real) → (num → num → real) → real) | vec_form_on⟨n⟩(U, k, ω)})",
	},
})}

// WedgeDef — the signed shuffle sum. Each ordered split of the input
// columns is counted once, with no factorial normalization.
var WedgeDef = wedgeDefThm{family.Define(registry.DefEntry{
	Name:  "WedgeDef",
	Key:   "prop_a0d00d8a33b8cdeb",
	Const: "vec_form_wedge",
	Type: "num → " +
		"set(num → real) → " +
		"num → " +
		"num → " +
		"((num → real) → (num → num → real) → real) → " +
		"((num → real) → (num → num → real) → real) → " +
		"(num → real) → " +
		"(num → num → real) → " +
		"real",
	Dim: "n",
	Equations: []string{
		"∀n p q:num. " +
			"∀U:set(num → real). " +
			"∀α β:((num → real) → (num → num → real) → real). " +
			"∀x:(num → real). " +
			"∀P:(num → num → real). " +
			"    vec_form_wedge⟨n⟩(U, p, q, α, β, x, P) = " +
			"    COND(x ∈ U, " +
			"        module_sum(real_ring.add, " +
			"            &0, " +
			"            {s:permutation(num) | " +
			"                s ∈ symmetric_group({j:num | j < p + q}) ∧ " +
			"                (∀i j:num. i < j ∧ j < p ⇒ permutation_map(s, i) < permutation_map(s, j)) ∧ " +
			"                (∀i j:num. " +
			"                    p ≤ i ∧ i < j ∧ j < p + q ⇒ " +
			"                    permutation_map(s, i) < permutation_map(s, j))}, " +
			"            λs:permutation(num). " +
			"                COND(permutation_even(p + q, s), &1, -&1) * " +
			"                α(x, λi:num. λj:num. COND(i < n ∧ j < p, P(i, permutation_map(s, j)), &0)) * " +
			"                β(x, " +
			"                    λi:num. λj:num. COND(i < n ∧ j < q, P(i, permutation_map(s, p + j)), &0))), " +
			"        &0)",
	},
})}

// ExteriorDerivativeDef — differentiate along each input column and
// omit that column, with the alternating sign of its position.
var ExteriorDerivativeDef = exteriorDerivativeDefThm{family.Define(registry.DefEntry{
	Name:  "ExteriorDerivativeDef",
	Key:   "prop_90913ad5eb27c9ef",
	Const: "vec_exterior_derivative",
	Type: "num → " +
		"set(num → real) → " +
		"num → " +
		"((num → real) → (num → num → real) → real) → " +
		"(num → real) → " +
		"(num → num → real) → " +
		"real",
	Dim: "n",
	Reading: "The argument k is the input degree, so the result has degree k+1; no truncated " +
		"subtraction of degrees occurs. The omitted-column matrix and all output values are normalized. " +
		"Smoothness on the open set makes the chosen partial derivatives meaningful and local.",
	Equations: []string{
		"∀n k:num. " +
			"∀U:set(num → real). " +
			"∀ω:((num → real) → (num → num → real) → real). " +
			"∀x:(num → real). " +
			"∀P:(num → num → real). " +
			"    vec_exterior_derivative⟨n⟩(U, k, ω, x, P) = " +
			"    COND(x ∈ U, " +
			"        Σ_{j<k + 1} (-&1)^j * " +
			"        (Σ_{r<n} P(r, j) * " +
			"            partial_derivative(λy:(num → real). " +
			"                    ω(y, λa:num. λb:num. COND(a < n ∧ b < k, P(a, COND(b < j, b, b + 1)), &0)), " +
			"                r, " +
			"                x)), " +
			"        &0)",
	},
})}

// PullbackDef — evaluate at f(x) after applying its Jacobian to each
// input column, and normalize the result outside the source domain.
var PullbackDef = pullbackDefThm{family.Define(registry.DefEntry{
	Name:  "PullbackDef",
	Key:   "prop_2df8e42786a49f7b",
	Const: "vec_form_pullback",
	Type: "num → " +
		"num → " +
		"set(num → real) → " +
		"num → " +
		"((num → real) → num → real) → " +
		"((num → real) → (num → num → real) → real) → " +
		"(num → real) → " +
		"(num → num → real) → " +
		"real",
	Dim:       "n",
	SourceDim: "n",
	TargetDim: "m",
	Equations: []string{
		"∀n m k:num. " +
			"∀U:set(num → real). " +
			"∀f:((num → real) → num → real). " +
			"∀ω:((num → real) → (num → num → real) → real). " +
			"∀x:(num → real). " +
			"∀P:(num → num → real). " +
			"    vec_form_pullback⟨n, m⟩(U, k, f, ω, x, P) = " +
			"    COND(x ∈ U, " +
			"        ω(f(x), " +
			"            matrix_mul(n, " +
			"                vec_jacobian_matrix⟨n, m⟩(f, x), " +
			"                λi:num. λj:num. COND(i < n ∧ j < k, P(i, j), &0))), " +
			"        &0)",
	},
})}
