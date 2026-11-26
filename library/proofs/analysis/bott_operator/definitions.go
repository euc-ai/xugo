package bott_operator

import (
	"github.com/euc-ai/xugo/library/registry"
)

var indicesDef = indicesDefThm{family.Define(registry.DefEntry{
	Name:  "indicesDef",
	Key:   "prop_50f2ba234bfdbb0f",
	Const: "bott_indices",
	Type:  "num → set(prod(num → num, num))",
	Equations: []string{
		"∀n:num. " +
			"    bott_indices(n) = " +
			"    {z:prod(num → num, num) | snd(z) < nat_pow(2, n) ∧ (∀j:num. n ≤ j ⇒ fst(z)(j) = 0)}",
	},
})}

var energyDef = energyDefThm{family.Define(registry.DefEntry{
	Name:  "energyDef",
	Key:   "prop_a21e57739ad457c9",
	Const: "bott_energy",
	Type:  "num → prod(num → num, num) → real",
	Equations: []string{
		"∀n:num. ∀z:prod(num → num, num). " +
			"    bott_energy(n, z) = " +
			"    &2 * real_sum({i:num | i < n}, λi:num. &(fst(z)(i))) + &2 * &(card(exterior_mask(n, snd(z))))",
	},
})}

var shiftDef = shiftDefThm{family.Define(registry.DefEntry{
	Name:  "shiftDef",
	Key:   "prop_271d26c3bae8b8ac",
	Const: "bott_multi_shift",
	Type:  "num → (num → num) → num → bool → num → num",
	Equations: []string{
		"∀n:num. ∀α:(num → num). ∀j:num. ∀up:bool. ∀i:num. " +
			"    bott_multi_shift(n, α, j, up, i) = " +
			"    COND(i < n, COND(i = j, COND(up, suc(α(i)), α(i) - 1), α(i)), 0)",
	},
})}

var signDef = signDefThm{family.Define(registry.DefEntry{
	Name:  "signDef",
	Key:   "prop_9aa8d59a927f341e",
	Const: "bott_exterior_sign",
	Type:  "num → num → num → complex",
	Equations: []string{
		"∀n a i:num. " +
			"    bott_exterior_sign(n, a, i) = " +
			"    COND(nat_mod(card({j:num | j ∈ exterior_mask(n, a) ∧ j < i}), 2) = 0, " +
			"        complex_of_real(&1), " +
			"        -complex_of_real(&1))",
	},
})}

var sequenceOperatorDef = sequenceOperatorDefThm{family.Define(registry.DefEntry{
	Name:  "sequenceOperatorDef",
	Key:   "prop_47a438cc921266ff",
	Deps:  []registry.EntryLike{indicesDef, shiftDef, signDef},
	Const: "bott_sequence_operator",
	Type:  "num → (prod(num → num, num) → complex) → prod(num → num, num) → complex",
	Equations: []string{
		"∀n:num. ∀u:(prod(num → num, num) → complex). ∀z:prod(num → num, num). " +
			"    bott_sequence_operator(n, u, z) = " +
			"    COND(z ∈ bott_indices(n), " +
			"        module_sum(complex_add, " +
			"            complex_of_real(&0), " +
			"            {i:num | i < n}, " +
			"            λi:num. " +
			"                bott_exterior_sign(n, snd(z), i) * " +
			"                COND(i ∈ exterior_mask(n, snd(z)), " +
			"                    complex_of_real(real_sqrt(&2 * &(suc(fst(z)(i))))) * " +
			"                    u((bott_multi_shift(n, fst(z), i, True), snd(z) - nat_pow(2, i))), " +
			"                    COND(0 < fst(z)(i), " +
			"                        complex_of_real(real_sqrt(&2 * &(fst(z)(i)))) * " +
			"                        u((bott_multi_shift(n, fst(z), i, False), snd(z) + nat_pow(2, i))), " +
			"                        complex_of_real(&0)))), " +
			"        complex_of_real(&0))",
	},
})}

var moduleDef = moduleDefThm{family.Define(registry.DefEntry{
	Name:  "moduleDef",
	Key:   "prop_96db608f25178d83",
	Deps:  []registry.EntryLike{indicesDef, energyDef},
	Const: "bott_sequence_module",
	Type:  "num → num → bool → module_ops(complex, prod(num → num, num) → complex)",
	Equations: []string{
		"∀n e:num. ∀graph:bool. " +
			"    bott_sequence_module(n, e, graph) = " +
			"    restrict_module(weighted_sequence_module(bott_indices(n), " +
			"            λz:prod(num → num, num). COND(graph, &1 + bott_energy(n, z), &1)), " +
			"        {u:(prod(num → num, num) → complex) | " +
			"            u ∈ " +
			"            (weighted_sequence_module(bott_indices(n), " +
			"                    λz:prod(num → num, num). " +
			"                        COND(graph, &1 + bott_energy(n, z), &1))).carrier ∧ " +
			"            (∀z:prod(num → num, num). " +
			"                nat_mod(card(exterior_mask(n, snd(z))), 2) ≠ e ⇒ u(z) = complex_of_real(&0))})",
	},
})}

var innerDef = innerDefThm{family.Define(registry.DefEntry{
	Name:  "innerDef",
	Key:   "prop_af005569809c0b84",
	Deps:  []registry.EntryLike{indicesDef, energyDef},
	Const: "bott_sequence_inner",
	Type: "num → " +
		"bool → " +
		"(prod(num → num, num) → complex) → " +
		"(prod(num → num, num) → complex) → " +
		"complex",
	Equations: []string{
		"∀n:num. ∀graph:bool. " +
			"    bott_sequence_inner(n, graph) = " +
			"    weighted_sequence_inner(bott_indices(n), " +
			"        λz:prod(num → num, num). COND(graph, &1 + bott_energy(n, z), &1))",
	},
})}

var groundDef = groundDefThm{family.Define(registry.DefEntry{
	Name:  "groundDef",
	Key:   "prop_30486f9fd0d50b8f",
	Deps:  []registry.EntryLike{indicesDef},
	Const: "bott_ground_sequence",
	Type:  "num → prod(num → num, num) → complex",
	Equations: []string{
		"∀n:num. ∀z:prod(num → num, num). " +
			"    bott_ground_sequence(n, z) = " +
			"    COND(z ∈ bott_indices(n) ∧ snd(z) = 0 ∧ (∀j:num. fst(z)(j) = 0), " +
			"        complex_of_real(&1), " +
			"        complex_of_real(&0))",
	},
})}

var schwartzDef = schwartzDefThm{family.Define(registry.DefEntry{
	Name:  "schwartzDef",
	Key:   "prop_13cfa88287c34c0e",
	Const: "bott_schwartz",
	Type:  "num → ((num → real) → complex) → bool",
	Equations: []string{
		"∀n:num. ∀f:((num → real) → complex). " +
			"    bott_schwartz(n, f) ⇔ " +
			"    (∀x:(num → real). ¬vec⟨n⟩(&0, x) ⇒ f(x) = complex_of_real(&0)) ∧ " +
			"    vec_smooth_on⟨n⟩({x:(num → real) | vec⟨n⟩(&0, x)}, λx:(num → real). re(f(x))) ∧ " +
			"    vec_smooth_on⟨n⟩({x:(num → real) | vec⟨n⟩(&0, x)}, λx:(num → real). im(f(x))) ∧ " +
			"    (∀r p:num. ∀j:(num → num). " +
			"        (∀l:num. l < r ⇒ j(l) < n) ⇒ " +
			"        ∃C:real. " +
			"            &0 ≤ C ∧ " +
			"            ∀x:(num → real). " +
			"                vec⟨n⟩(&0, x) ⇒ " +
			"                real_pow(&1 + real_sum({i:num | i < n}, λi:num. real_pow(x(i), 2)), p) * " +
			"                (real_pow(ps_derivative_word(r, j, λy:(num → real). re(f(y)), x), 2) + " +
			"                    real_pow(ps_derivative_word(r, j, λy:(num → real). im(f(y)), x), 2)) ≤ " +
			"                C)",
	},
})}

var schwartzFormDef = schwartzFormDefThm{family.Define(registry.DefEntry{
	Name:  "schwartzFormDef",
	Key:   "prop_40f332fae74b59b8",
	Deps:  []registry.EntryLike{schwartzDef},
	Const: "bott_schwartz_form",
	Type:  "num → ((num → real) → num → complex) → bool",
	Equations: []string{
		"∀n:num. ∀f:((num → real) → num → complex). " +
			"    bott_schwartz_form(n, f) ⇔ " +
			"    (∀a:num. a < nat_pow(2, n) ⇒ bott_schwartz(n, λx:(num → real). f(x, a))) ∧ " +
			"    (∀x:(num → real). ∀a:num. nat_pow(2, n) ≤ a ⇒ f(x, a) = complex_of_real(&0))",
	},
})}

var hermiteTransformDef = hermiteTransformDefThm{family.Define(registry.DefEntry{
	Name:  "hermiteTransformDef",
	Key:   "prop_e209d47afcd537d0",
	Deps:  []registry.EntryLike{indicesDef},
	Const: "bott_hermite_transform",
	Type:  "num → ((num → real) → num → complex) → prod(num → num, num) → complex",
	Equations: []string{
		"∀n:num. ∀f:((num → real) → num → complex). ∀z:prod(num → num, num). " +
			"    bott_hermite_transform(n, f, z) = " +
			"    COND(z ∈ bott_indices(n), " +
			"        complex_of_real(vec_integral⟨n⟩( " +
			"                λx:(num → real). re(f(x, snd(z))) * hermite_function(n, fst(z), x))) + " +
			"        complex_i * " +
			"        complex_of_real(vec_integral⟨n⟩( " +
			"                λx:(num → real). im(f(x, snd(z))) * hermite_function(n, fst(z), x))), " +
			"        complex_of_real(&0))",
	},
})}

var physicalDef = physicalDefThm{family.Define(registry.DefEntry{
	Name:  "physicalDef",
	Key:   "prop_d7a1050ed820fa65",
	Deps:  []registry.EntryLike{signDef},
	Const: "bott_physical_operator",
	Type:  "num → ((num → real) → num → complex) → (num → real) → num → complex",
	Equations: []string{
		"∀n:num. ∀f:((num → real) → num → complex). ∀x:(num → real). ∀a:num. " +
			"    bott_physical_operator(n, f, x, a) = " +
			"    COND(vec⟨n⟩(&0, x) ∧ a < nat_pow(2, n), " +
			"        module_sum(complex_add, " +
			"            complex_of_real(&0), " +
			"            {i:num | i < n}, " +
			"            λi:num. " +
			"                bott_exterior_sign(n, a, i) * " +
			"                COND(i ∈ exterior_mask(n, a), " +
			"                    complex_of_real(partial_derivative( " +
			"                            λy:(num → real). re(f(y, a - nat_pow(2, i))), i, x)) + " +
			"                    complex_i * " +
			"                    complex_of_real(partial_derivative( " +
			"                            λy:(num → real). im(f(y, a - nat_pow(2, i))), i, x)) + " +
			"                    complex_of_real(x(i)) * f(x, a - nat_pow(2, i)), " +
			"                    -complex_of_real(partial_derivative( " +
			"                            λy:(num → real). re(f(y, a + nat_pow(2, i))), i, x)) - " +
			"                    complex_i * " +
			"                    complex_of_real(partial_derivative( " +
			"                            λy:(num → real). im(f(y, a + nat_pow(2, i))), i, x)) + " +
			"                    complex_of_real(x(i)) * f(x, a + nat_pow(2, i)))), " +
			"        complex_of_real(&0))",
	},
})}

var rapidDef = rapidDefThm{family.Define(registry.DefEntry{
	Name:  "rapidDef",
	Key:   "prop_7b6fd6a4d605882e",
	Deps:  []registry.EntryLike{indicesDef, energyDef},
	Const: "bott_rapid_sequence",
	Type:  "num → (prod(num → num, num) → complex) → bool",
	Equations: []string{
		"∀n:num. ∀u:(prod(num → num, num) → complex). " +
			"    bott_rapid_sequence(n, u) ⇔ " +
			"    (∀z:prod(num → num, num). z ∉ bott_indices(n) ⇒ u(z) = complex_of_real(&0)) ∧ " +
			"    (∀p:num. ∃C:real. " +
			"        &0 ≤ C ∧ " +
			"        ∀z:prod(num → num, num). " +
			"            z ∈ bott_indices(n) ⇒ real_pow(&1 + bott_energy(n, z), p) * real_pow(|u(z)|, 2) ≤ C)",
	},
})}

var orthogonalDef = orthogonalDefThm{family.Define(registry.DefEntry{
	Name:  "orthogonalDef",
	Key:   "prop_e2ff93a855f87450",
	Const: "bott_orthogonal_matrix",
	Type:  "num → (num → num → real) → bool",
	Equations: []string{
		"∀n:num. ∀O:(num → num → real). " +
			"    bott_orthogonal_matrix(n, O) ⇔ " +
			"    (∀i j:num. n ≤ i ∨ n ≤ j ⇒ O(i, j) = &0) ∧ " +
			"    (∀i j:num. " +
			"        i < n ∧ j < n ⇒ " +
			"        real_sum({k:num | k < n}, λk:num. O(k, i) * O(k, j)) = COND(i = j, &1, &0))",
	},
})}

var rotationDef = rotationDefThm{family.Define(registry.DefEntry{
	Name:  "rotationDef",
	Key:   "prop_c551ab22ac83e2b7",
	Const: "bott_rotate_form",
	Type: "num → " +
		"(num → num → real) → " +
		"((num → real) → num → complex) → " +
		"(num → real) → " +
		"num → " +
		"complex",
	Equations: []string{
		"∀n:num. ∀O:(num → num → real). ∀f:((num → real) → num → complex). ∀x:(num → real). ∀a:num. " +
			"    bott_rotate_form(n, O, f, x, a) = " +
			"    COND(vec⟨n⟩(&0, x) ∧ a < nat_pow(2, n), " +
			"        module_sum(complex_add, " +
			"            complex_of_real(&0), " +
			"            {b:num | b < nat_pow(2, n)}, " +
			"            λb:num. " +
			"                complex_of_real(exterior_power(real_ring, n, O, a, b)) * " +
			"                f((λi:num. COND(i < n, real_sum({j:num | j < n}, λj:num. O(j, i) * x(j)), &0)), " +
			"                    b)), " +
			"        complex_of_real(&0))",
	},
})}

var rotationOperatorDef = rotationOperatorDefThm{family.Define(registry.DefEntry{
	Name:  "rotationOperatorDef",
	Key:   "prop_6b59a74570fd87b",
	Deps:  []registry.EntryLike{indicesDef, schwartzFormDef, hermiteTransformDef, rotationDef},
	Const: "bott_rotation_operator",
	Type: "num → " +
		"(num → num → real) → " +
		"(prod(num → num, num) → complex) → " +
		"prod(num → num, num) → " +
		"complex",
	Equations: []string{
		"∀n:num. ∀O:(num → num → real). " +
			"    bott_rotation_operator(n, O) = " +
			"    εU:((prod(num → num, num) → complex) → prod(num → num, num) → complex). " +
			"        U ∈ " +
			"        (operator_module( " +
			"                weighted_sequence_module(bott_indices(n), λz:prod(num → num, num). &1), " +
			"                hilbert_norm( " +
			"                    weighted_sequence_inner(bott_indices(n), λz:prod(num → num, num). &1)), " +
			"                weighted_sequence_module(bott_indices(n), λz:prod(num → num, num). &1), " +
			"                hilbert_norm(weighted_sequence_inner(bott_indices(n), " +
			"                        λz:prod(num → num, num). &1)))).carrier ∧ " +
			"        (∀f:((num → real) → num → complex). " +
			"            bott_schwartz_form(n, f) ⇒ " +
			"            U(bott_hermite_transform(n, f)) = " +
			"            bott_hermite_transform(n, bott_rotate_form(n, O, f)))",
	},
})}
