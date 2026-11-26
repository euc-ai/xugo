package clifford_spin

import (
	"github.com/euc-ai/xugo/library/registry"
)

var ProductDef = productDefThm{family.Define(registry.DefEntry{
	Name:  "ProductDef",
	Key:   "prop_6cd7f7d9967c81cb",
	Const: "clifford_product",
	Type:  "num → (num → real) → (num → real) → num → real",
	Equations: []string{
		"∀n:num. ∀u v:(num → real). ∀k:num. " +
			"    clifford_product(n, u, v, k) = " +
			"    COND(k < nat_pow(2, n), " +
			"        real_sum({a:num | a < nat_pow(2, n)}, " +
			"            λa:num. " +
			"                real_sum({b:num | b < nat_pow(2, n)}, " +
			"                    λb:num. " +
			"                        COND(exterior_mask(n, k) = " +
			"                            {i:num | " +
			"                                i < n ∧ ¬(i ∈ exterior_mask(n, a) ⇔ i ∈ exterior_mask(n, b))}, " +
			"                            real_pow(-&1, " +
			"                                card({p:prod(num, num) | " +
			"                                        fst(p) ∈ exterior_mask(n, a) ∧ " +
			"                                        snd(p) ∈ exterior_mask(n, b) ∧ " +
			"                                        snd(p) < fst(p)}) + " +
			"                                card(exterior_mask(n, a) ∩ exterior_mask(n, b))) * " +
			"                            u(a) * " +
			"                            v(b), " +
			"                            &0))), " +
			"        &0)",
	},
})}

var VectorDef = vectorDefThm{family.Define(registry.DefEntry{
	Name:  "VectorDef",
	Key:   "prop_641172238b3aa525",
	Const: "clifford_vector",
	Type:  "num → (num → real) → num → real",
	Equations: []string{
		"∀n:num. ∀v:(num → real). ∀a:num. " +
			"    clifford_vector(n, v, a) = " +
			"    COND(a < nat_pow(2, n) ∧ card(exterior_mask(n, a)) = 1, v(exterior_slot(n, a, 0)), &0)",
	},
})}

var ConjugateDef = conjugateDefThm{family.Define(registry.DefEntry{
	Name:  "ConjugateDef",
	Key:   "prop_f9aedb58fb916427",
	Const: "clifford_conjugate",
	Type:  "num → (num → real) → num → real",
	Equations: []string{
		"∀n:num. ∀u:(num → real). ∀a:num. " +
			"    clifford_conjugate(n, u, a) = " +
			"    COND(a < nat_pow(2, n), " +
			"        real_pow(-&1, " +
			"            nat_div(card(exterior_mask(n, a)) * (card(exterior_mask(n, a)) + 1), 2)) * " +
			"        u(a), " +
			"        &0)",
	},
})}

var wordDef = wordDefThm{family.Define(registry.DefEntry{
	Name:  "wordDef",
	Key:   "prop_322f3ac41dd1b41e",
	Deps:  []registry.EntryLike{ProductDef, VectorDef},
	Const: "clifford_word",
	Type:  "num → (num → num → real) → num → num → real",
	Equations: []string{
		"∀n:num. ∀v:(num → num → real). clifford_word(n, v, 0) = (λa:num. COND(a = 0, &1, &0))",
		"∀n k:num. ∀v:(num → num → real). " +
			"    clifford_word(n, v, suc(k)) = " +
			"    clifford_product(n, clifford_word(n, v, k), clifford_vector(n, v(k)))",
	},
})}

var SpinElementDef = spinElementDefThm{family.Define(registry.DefEntry{
	Name:  "SpinElementDef",
	Key:   "prop_52d809e066684abe",
	Deps:  []registry.EntryLike{wordDef},
	Const: "spin_element",
	Type:  "num → (num → real) → bool",
	Equations: []string{
		"∀n:num. ∀a:(num → real). " +
			"    spin_element(n, a) ⇔ " +
			"    ∃k:num. ∃v:(num → num → real). " +
			"        (∀j:num. " +
			"            j < 2 * k ⇒ " +
			"            vec⟨n⟩(&0, v(j)) ∧ real_sum({i:num | i < n}, λi:num. real_pow(v(j, i), 2)) = &1) ∧ " +
			"        a = clifford_word(n, v, 2 * k)",
	},
})}

var SpinGroupDef = spinGroupDefThm{family.Define(registry.DefEntry{
	Name:  "SpinGroupDef",
	Key:   "prop_201de2678b2d3969",
	Deps:  []registry.EntryLike{ProductDef, ConjugateDef, SpinElementDef},
	Const: "spin_group",
	Type:  "num → group_ops(num → real)",
	Equations: []string{
		"∀n:num. " +
			"    spin_group(n) = " +
			"    mk_group(clifford_product(n), " +
			"        (λa:num. COND(a = 0, &1, &0)), " +
			"        clifford_conjugate(n), " +
			"        {a:(num → real) | spin_element(n, a)})",
	},
})}

var ActionDef = actionDefThm{family.Define(registry.DefEntry{
	Name:  "ActionDef",
	Key:   "prop_dbacae6b1d70fe1b",
	Deps:  []registry.EntryLike{ProductDef, VectorDef, ConjugateDef},
	Const: "spin_vector_action",
	Type:  "num → (num → real) → num → num → real",
	Equations: []string{
		"∀n:num. ∀a:(num → real). ∀i j:num. " +
			"    spin_vector_action(n, a, i, j) = " +
			"    COND(i < n ∧ j < n, " +
			"        clifford_product(n, " +
			"            clifford_product(n, a, clifford_vector(n, λl:num. COND(l = j, &1, &0))), " +
			"            clifford_conjugate(n, a), " +
			"            nat_pow(2, i)), " +
			"        &0)",
	},
})}

var GeneratorDef = generatorDefThm{family.Define(registry.DefEntry{
	Name:  "GeneratorDef",
	Key:   "prop_b8d54aec70411c9f",
	Const: "spinor_generator",
	Type:  "num → num → num → num → complex",
	Equations: []string{
		"∀m l a b:num. " +
			"    spinor_generator(m, l, a, b) = " +
			"    COND(l < 2 * m, " +
			"        COND(nat_mod(l, 2) = 1, " +
			"            complex_i * " +
			"            koszul_ambient_matrix(m, " +
			"                (λj:num. COND(j = nat_div(l, 2), complex_of_real(&1), complex_of_real(&0))), " +
			"                a, " +
			"                b), " +
			"            COND(card(exterior_mask(m, a)) = suc(card(exterior_mask(m, b))), " +
			"                koszul_ambient_matrix(m, " +
			"                    (λj:num. " +
			"                        COND(j = nat_div(l, 2), complex_of_real(&1), complex_of_real(&0))), " +
			"                    a, " +
			"                    b), " +
			"                -koszul_ambient_matrix(m, " +
			"                    (λj:num. " +
			"                        COND(j = nat_div(l, 2), complex_of_real(&1), complex_of_real(&0))), " +
			"                    a, " +
			"                    b))), " +
			"        complex_of_real(&0))",
	},
})}

var bladeMatrixDef = bladeMatrixDefThm{family.Define(registry.DefEntry{
	Name:  "bladeMatrixDef",
	Key:   "prop_e96f9e51407b6b63",
	Deps:  []registry.EntryLike{GeneratorDef},
	Const: "spinor_blade",
	Type:  "num → num → num → num → num → complex",
	Equations: []string{
		"∀m a:num. " +
			"    spinor_blade(m, a, 0) = " +
			"    (λi:num. λj:num. COND(i < nat_pow(2, m) ∧ i = j, complex_of_real(&1), complex_of_real(&0)))",
		"∀m a k:num. " +
			"    spinor_blade(m, a, suc(k)) = " +
			"    COND(k ∈ exterior_mask(2 * m, a), " +
			"        matrix_mul(complex_add, " +
			"            complex_mul, " +
			"            nat_pow(2, m), " +
			"            spinor_blade(m, a, k), " +
			"            spinor_generator(m, k)), " +
			"        spinor_blade(m, a, k))",
	},
})}

var RepresentationDef = representationDefThm{family.Define(registry.DefEntry{
	Name:  "RepresentationDef",
	Key:   "prop_d791460f7ee7e9d7",
	Deps:  []registry.EntryLike{bladeMatrixDef},
	Const: "spinor_representation",
	Type:  "num → (num → real) → num → num → complex",
	Equations: []string{
		"∀m:num. ∀a:(num → real). ∀i j:num. " +
			"    spinor_representation(m, a, i, j) = " +
			"    module_sum(complex_add, " +
			"        complex_of_real(&0), " +
			"        {b:num | b < nat_pow(2, 2 * m)}, " +
			"        λb:num. complex_of_real(a(b)) * spinor_blade(m, b, 2 * m, i, j))",
	},
})}
