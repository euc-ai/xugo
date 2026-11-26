package class_number

import (
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/number_field/ring_of_integers"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/characteristic_zero"
	_ "github.com/euc-ai/xugo/library/proofs/int_num/int_construction"
	_ "github.com/euc-ai/xugo/library/proofs/iterate/nat/nat_sum"
	_ "github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/registry"
)

var integralStructureConstantDef = integralStructureConstantDefThm{family.Define(registry.DefEntry{
	Name:  "integralStructureConstantDef",
	Key:   "prop_c75900d8d85a2d11",
	Deps:  []registry.EntryLike{},
	Const: "integral_structure_constant",
	Type:  "ring_ops(A) → num → (num → A) → num → num → num → int",
	Equations: []string{
		"∀R:ring_ops(A). ∀n:num. ∀e:(num → A). ∀i j k:num. " +
			"    integral_structure_constant(R, n, e, i, j, k) = " +
			"    integer_value(R, " +
			"        module_basis_coordinates(restrict_ring(R, integer_image(R)), " +
			"            restrict_module(regular_module(R), ring_of_integers(R)), " +
			"            {e(u) | u:num | u < n}, " +
			"            R.mul(e(i), e(j)), " +
			"            e(k)))",
	},
})}

var structureConstantBoundDef = structureConstantBoundDefThm{family.Define(registry.DefEntry{
	Name:  "structureConstantBoundDef",
	Key:   "prop_a405300ee2512c06",
	Deps:  []registry.EntryLike{integralStructureConstantDef},
	Const: "structure_constant_bound",
	Type:  "ring_ops(A) → num → (num → A) → num",
	Equations: []string{
		"∀R:ring_ops(A). ∀n:num. ∀e:(num → A). " +
			"    structure_constant_bound(R, n, e) = " +
			"    εs:num. " +
			"        s ∈ " +
			"        ({1} ∪ " +
			"            {nat_sum({i:num | i < n}, " +
			"                    λi:num. " +
			"                        num_of_int(int_abs(integral_structure_constant(R, n, e, i, j, k)))) | " +
			"                j:num, " +
			"                k:num | " +
			"                j < n ∧ k < n}) ∧ " +
			"        (∀a:num. " +
			"            a ∈ " +
			"            ({1} ∪ " +
			"                {nat_sum({i:num | i < n}, " +
			"                        λi:num. " +
			"                            num_of_int( " +
			"                                int_abs(integral_structure_constant(R, n, e, i, j, k)))) | " +
			"                    j:num, " +
			"                    k:num | " +
			"                    j < n ∧ k < n}) ⇒ " +
			"            a ≤ s)",
	},
})}

var classNumberBoundDef = classNumberBoundDefThm{family.Define(registry.DefEntry{
	Name:  "classNumberBoundDef",
	Key:   "prop_5b13ed319e826a1c",
	Deps:  []registry.EntryLike{structureConstantBoundDef},
	Const: "class_number_bound",
	Type:  "ring_ops(A) → num → (num → A) → num",
	Equations: []string{
		"∀R:ring_ops(A). ∀n:num. ∀e:(num → A). " +
			"    class_number_bound(R, n, e) = factorial(n) * structure_constant_bound(R, n, e) ^ n",
	},
})}

var integerCoordinateBoxDef = integerCoordinateBoxDefThm{family.Define(registry.DefEntry{
	Name:  "integerCoordinateBoxDef",
	Key:   "prop_64f0354c320f9a9e",
	Deps:  []registry.EntryLike{},
	Const: "integer_coordinate_box",
	Type:  "ring_ops(A) → num → (num → A) → num → set(A)",
	Equations: []string{
		"∀R:ring_ops(A). ∀n H:num. ∀e:(num → A). " +
			"    integer_coordinate_box(R, n, e, H) = " +
			"    {module_sum(R.add, R.zero, {i:num | i < n}, λi:num. R.mul(integer_map(R, a(i)), e(i))) | " +
			"        a:(num → int) | " +
			"        ∀i:num. i < n ⇒ 0 ≤ a(i) ∧ a(i) ≤ H}",
	},
})}

var integerRootFloorDef = integerRootFloorDefThm{family.Define(registry.DefEntry{
	Name:      "integerRootFloorDef",
	Key:       "prop_b5d35e451dba6a0d",
	Deps:      []registry.EntryLike{},
	Const:     "integer_root_floor",
	Type:      "num → num → num",
	Equations: []string{"∀m n:num. integer_root_floor(m, n) = εh:num. h ^ n ≤ m ∧ m < (h + 1) ^ n"},
})}
