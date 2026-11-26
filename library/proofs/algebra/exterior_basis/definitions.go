package exterior_basis

import (
	"github.com/euc-ai/xugo/library/registry"
)

var MaskDef = maskDefThm{family.Define(registry.DefEntry{
	Name:  "MaskDef",
	Key:   "prop_d2ca5e69b067e777",
	Const: "exterior_mask",
	Type:  "num → num → set(num)",
	Equations: []string{
		"∀r a:num. exterior_mask(r, a) = {i:num | i < r ∧ nat_mod(nat_div(a, nat_pow(2, i)), 2) = 1}",
	},
})}

var SlotDef = slotDefThm{family.Define(registry.DefEntry{
	Name:  "SlotDef",
	Key:   "prop_829b03d6302028e5",
	Deps:  []registry.EntryLike{MaskDef},
	Const: "exterior_slot",
	Type:  "num → num → num → num",
	Equations: []string{
		"∀r a k:num. " +
			"    exterior_slot(r, a, k) = " +
			"    εi:num. i ∈ exterior_mask(r, a) ∧ card({j:num | j ∈ exterior_mask(r, a) ∧ j < i}) = k",
	},
})}

var CliffordMatrixDef = cliffordMatrixDefThm{family.Define(registry.DefEntry{
	Name:  "CliffordMatrixDef",
	Key:   "prop_1dad0e2990cb3425",
	Deps:  []registry.EntryLike{MaskDef},
	Const: "koszul_ambient_matrix",
	Type:  "num → (num → complex) → num → num → complex",
	Equations: []string{
		"∀r:num. ∀v:(num → complex). ∀a b:num. " +
			"    koszul_ambient_matrix(r, v, a, b) = " +
			"    COND(a < nat_pow(2, r) ∧ b < nat_pow(2, r), " +
			"        module_sum(complex_add, " +
			"            complex_of_real(&0), " +
			"            {i:num | i < r}, " +
			"            λi:num. " +
			"                COND(i ∉ exterior_mask(r, b) ∧ " +
			"                    exterior_mask(r, a) = insert(i, exterior_mask(r, b)), " +
			"                    COND(nat_mod(card({j:num | j ∈ exterior_mask(r, b) ∧ j < i}), 2) = 0, " +
			"                        v(i), " +
			"                        -v(i)), " +
			"                    COND(i ∉ exterior_mask(r, a) ∧ " +
			"                        exterior_mask(r, b) = insert(i, exterior_mask(r, a)), " +
			"                        COND(nat_mod(card({j:num | j ∈ exterior_mask(r, a) ∧ j < i}), 2) = 0, " +
			"                            complex_conj(v(i)), " +
			"                            -complex_conj(v(i))), " +
			"                        complex_of_real(&0)))), " +
			"        complex_of_real(&0))",
	},
})}

// PowerDef — `exterior_power(R, r, P, a, b)`: the matrix of the exterior
// power of the r × r matrix P in the binary basis, the minor of P on the
// rows of a's digits and the columns of b's, both in increasing order, and
// 0 between basis vectors of different degrees.
var PowerDef = powerDefThm{family.Define(registry.DefEntry{
	Name:  "PowerDef",
	Key:   "prop_7a25b43704752b7f",
	Deps:  []registry.EntryLike{MaskDef, SlotDef},
	Const: "exterior_power",
	Type:  "ring_ops(A) → num → (num → num → A) → num → num → A",
	Equations: []string{
		"∀R:ring_ops(A). ∀r:num. ∀P:(num → num → A). ∀a b:num. " +
			"    exterior_power(R, r, P, a, b) = " +
			"    COND(a < nat_pow(2, r) ∧ " +
			"        b < nat_pow(2, r) ∧ " +
			"        card(exterior_mask(r, a)) = card(exterior_mask(r, b)), " +
			"        determinant(R, " +
			"            card(exterior_mask(r, a)), " +
			"            λi:num. λj:num. P(exterior_slot(r, a, i), exterior_slot(r, b, j))), " +
			"        R.zero)",
	},
	Reading: "Only the entries of P below r are read. At a = b = 0 " +
		"the entry is the determinant of the empty matrix, the ring's one.",
})}
