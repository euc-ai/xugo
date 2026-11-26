package bott_periodicity

import (
	"github.com/euc-ai/xugo/library/registry"
)

var compactInverseDef = compactInverseDefThm{family.Define(registry.DefEntry{
	Name:  "compactInverseDef",
	Key:   "prop_5ab4d0fcec7219bf",
	Const: "k_to_kc",
	Type: "set(set(A)) → " +
		"set(prod(prod(num, A → num → num → complex), prod(num, A → num → num → complex))) → " +
		"set(prod(prod(num, A → num → num → complex), " +
		"        prod(prod(num, A → num → num → complex), A → num → num → complex)))",
	Equations: []string{
		"∀T:set(set(A)). " +
			"∀C:set(prod(prod(num, A → num → num → complex), prod(num, A → num → num → complex))). " +
			"    k_to_kc(T, C) = " +
			"    induced_map(λv:prod(prod(num, A → num → num → complex), " +
			"                prod(num, A → num → num → complex)). " +
			"            kc_class(T, (fst(v), (snd(v), λx:A. λi:num. λj:num. complex_of_real(&0)))), " +
			"        C)",
	},
})}

var bottTripleDef = bottTripleDefThm{family.Define(registry.DefEntry{
	Name:  "bottTripleDef",
	Key:   "prop_254abfd13e80680e",
	Const: "bott_triple",
	Type: "prod(prod(num, complex → num → num → complex), " +
		"    prod(prod(num, complex → num → num → complex), complex → num → num → complex))",
	Equations: []string{
		"bott_triple = " +
			"(projection_trivial(complex_topology, 1), " +
			"    (projection_trivial(complex_topology, 1), " +
			"        λz:complex. λi:num. λj:num. COND(i = 0 ∧ j = 0, z, complex_of_real(&0))))",
	},
})}

var BottClassDef = bottClassDefThm{family.Define(registry.DefEntry{
	Name:  "BottClassDef",
	Key:   "prop_61dfe01fdf3a4691",
	Deps:  []registry.EntryLike{bottTripleDef},
	Const: "bott_class",
	Type: "set(prod(prod(num, complex → num → num → complex), " +
		"        prod(prod(num, complex → num → num → complex), complex → num → num → complex)))",
	Equations: []string{"bott_class = kc_class(complex_topology, bott_triple)"},
})}

var BottMapDef = bottMapDefThm{family.Define(registry.DefEntry{
	Name:  "BottMapDef",
	Key:   "prop_3935598fcb4b37e5",
	Deps:  []registry.EntryLike{compactInverseDef, BottClassDef},
	Const: "bott_map",
	Type: "set(set(A)) → " +
		"set(prod(prod(num, A → num → num → complex), prod(num, A → num → num → complex))) → " +
		"set(prod(prod(num, prod(A, complex) → num → num → complex), " +
		"        prod(prod(num, prod(A, complex) → num → num → complex), " +
		"            prod(A, complex) → num → num → complex)))",
	Equations: []string{
		"∀T:set(set(A)). " +
			"∀a:set(prod(prod(num, A → num → num → complex), prod(num, A → num → num → complex))). " +
			"    bott_map(T, a) = kc_external(T, complex_topology, k_to_kc(T, a), bott_class)",
	},
})}

var circleDef = circleDefThm{family.Define(registry.DefEntry{
	Name:      "circleDef",
	Key:       "prop_834457325832eb84",
	Const:     "bott_circle",
	Type:      "set(complex)",
	Equations: []string{"bott_circle = {z:complex | |z| = &1}"},
})}

var clutchingDef = clutchingDefThm{family.Define(registry.DefEntry{
	Name:  "clutchingDef",
	Key:   "prop_494745d7f091929f",
	Deps:  []registry.EntryLike{circleDef},
	Const: "bott_clutching",
	Type:  "set(set(A)) → num → (A → complex → num → num → complex) → bool",
	Equations: []string{
		"∀T:set(set(A)). ∀r:num. ∀g:(A → complex → num → num → complex). " +
			"    bott_clutching(T, r, g) ⇔ " +
			"    continuous_projection_map(product_topology(T, subtopology(complex_topology, bott_circle)), " +
			"        projection_trivial(product_topology(T, subtopology(complex_topology, bott_circle)), r), " +
			"        projection_trivial(product_topology(T, subtopology(complex_topology, bott_circle)), r), " +
			"        λp:prod(A, complex). g(fst(p), snd(p))) ∧ " +
			"    (∀x:A. ∀z:complex. " +
			"        x ∈ ⋃T ∧ z ∈ bott_circle ⇒ " +
			"        projection_invertible_at(projection_trivial( " +
			"                product_topology(T, subtopology(complex_topology, bott_circle)), r), " +
			"            projection_trivial(product_topology(T, subtopology(complex_topology, bott_circle)), " +
			"                r), " +
			"            λp:prod(A, complex). g(fst(p), snd(p)), " +
			"            (x, z)))",
	},
})}

var clutchingTripleDef = clutchingTripleDefThm{family.Define(registry.DefEntry{
	Name:  "clutchingTripleDef",
	Key:   "prop_15f6001abb259f0",
	Const: "bott_clutching_triple",
	Type: "set(set(A)) → " +
		"num → " +
		"(A → complex → num → num → complex) → " +
		"prod(prod(num, prod(A, complex) → num → num → complex), " +
		"    prod(prod(num, prod(A, complex) → num → num → complex), " +
		"        prod(A, complex) → num → num → complex))",
	Equations: []string{
		"∀T:set(set(A)). ∀r:num. ∀g:(A → complex → num → num → complex). " +
			"    bott_clutching_triple(T, r, g) = " +
			"    (projection_trivial(product_topology(T, complex_topology), r), " +
			"        (projection_trivial(product_topology(T, complex_topology), r), " +
			"            λp:prod(A, complex). λi:num. λj:num. " +
			"                COND(fst(p) ∈ ⋃T ∧ snd(p) ≠ complex_of_real(&0) ∧ i < r ∧ j < r, " +
			"                    complex_of_real(|snd(p)|) * " +
			"                    g(fst(p), snd(p) / complex_of_real(|snd(p)|), i, j), " +
			"                    complex_of_real(&0))))",
	},
})}

var laurentDef = laurentDefThm{family.Define(registry.DefEntry{
	Name:  "laurentDef",
	Key:   "prop_9c3b5b41c9e4b8db",
	Deps:  []registry.EntryLike{circleDef},
	Const: "bott_laurent_matrix",
	Type:  "set(set(A)) → num → (A → complex → num → num → complex) → bool",
	Equations: []string{
		"∀T:set(set(A)). ∀r:num. ∀p:(A → complex → num → num → complex). " +
			"    bott_laurent_matrix(T, r, p) ⇔ " +
			"    ∃N:num. ∃A B:(num → A → num → num → complex). " +
			"        (∀k i j:num. " +
			"            k < N ∧ i < r ∧ j < r ⇒ " +
			"            continuous_map(T, complex_topology, λx:A. A(k, x, i, j)) ∧ " +
			"            continuous_map(T, complex_topology, λx:A. B(k, x, i, j))) ∧ " +
			"        (∀x:A. ∀z:complex. ∀i j:num. " +
			"            p(x, z, i, j) = " +
			"            COND(x ∈ ⋃T ∧ z ∈ bott_circle ∧ i < r ∧ j < r, " +
			"                module_sum(complex_add, " +
			"                    complex_of_real(&0), " +
			"                    {k:num | k < N}, " +
			"                    λk:num. " +
			"                        A(k, x, i, j) * monoid_pow(complex_mul, complex_of_real(&1), z, k) + " +
			"                        B(k, x, i, j) * " +
			"                        monoid_pow(complex_mul, complex_of_real(&1), complex_conj(z), k)), " +
			"                complex_of_real(&0)))",
	},
})}

var polynomialDef = polynomialDefThm{family.Define(registry.DefEntry{
	Name:  "polynomialDef",
	Key:   "prop_244662fef776b568",
	Const: "bott_polynomial",
	Type: "set(set(A)) → " +
		"num → " +
		"num → " +
		"(A → num → num → num → complex) → " +
		"A → " +
		"complex → " +
		"num → " +
		"num → " +
		"complex",
	Equations: []string{
		"∀T:set(set(A)). ∀r d:num. ∀a:(A → num → num → num → complex). ∀x:A. ∀z:complex. ∀i j:num. " +
			"    bott_polynomial(T, r, d, a)(x, z, i, j) = " +
			"    COND(x ∈ ⋃T ∧ i < r ∧ j < r, " +
			"        COND(i = j, monoid_pow(complex_mul, complex_of_real(&1), z, d), complex_of_real(&0)) + " +
			"        module_sum(complex_add, " +
			"            complex_of_real(&0), " +
			"            {k:num | k < d}, " +
			"            λk:num. a(x, k, i, j) * monoid_pow(complex_mul, complex_of_real(&1), z, k)), " +
			"        complex_of_real(&0))",
	},
})}

var polynomialLoopDef = polynomialLoopDefThm{family.Define(registry.DefEntry{
	Name: "polynomialLoopDef",
	Reading: "The full monic polynomial is defined on the plane. This separate circle restriction " +
		"has the zero padding required of clutching matrices outside the base times the circle.",
	Key:   "prop_bac6001bc3c6beb",
	Deps:  []registry.EntryLike{circleDef, polynomialDef},
	Const: "bott_polynomial_loop",
	Type: "set(set(A)) → " +
		"num → " +
		"num → " +
		"(A → num → num → num → complex) → " +
		"A → " +
		"complex → " +
		"num → " +
		"num → " +
		"complex",
	Equations: []string{
		"∀T:set(set(A)). ∀r d:num. ∀a:(A → num → num → num → complex). ∀x:A. ∀z:complex. ∀i j:num. " +
			"    bott_polynomial_loop(T, r, d, a, x, z, i, j) = " +
			"    COND(z ∈ bott_circle, bott_polynomial(T, r, d, a)(x, z, i, j), complex_of_real(&0))",
	},
})}

// linearLoopDef — the loop z·1 − C(x) on the base times the circle,
// padded with zeros as a clutching matrix.
var linearLoopDef = linearLoopDefThm{family.Define(registry.DefEntry{
	Name: "linearLoopDef",
	Key:  "prop_b7059673671f410b",
	Reading: "bott_clutching of this loop says that z·1 − C(x) is invertible " +
		"at every point of the base and every z of the circle: no eigenvalue of " +
		"C(x) has modulus one. The padding is the one bott_polynomial_loop carries.",
	Deps:  []registry.EntryLike{circleDef},
	Const: "bott_linear_loop",
	Type:  "set(set(A)) → num → (A → num → num → complex) → A → complex → num → num → complex",
	Equations: []string{
		"∀T:set(set(A)). ∀r:num. ∀C:(A → num → num → complex). ∀x:A. ∀z:complex. ∀i j:num. " +
			"    bott_linear_loop(T, r, C, x, z, i, j) = " +
			"    COND(x ∈ ⋃T ∧ z ∈ bott_circle ∧ i < r ∧ j < r, " +
			"        COND(i = j, z, complex_of_real(&0)) - C(x, i, j), " +
			"        complex_of_real(&0))",
	},
})}

var polynomialCoefficientsDef = polynomialCoefficientsDefThm{family.Define(registry.DefEntry{
	Name:  "polynomialCoefficientsDef",
	Key:   "prop_f0f5de6607ef55d2",
	Const: "bott_polynomial_coefficients",
	Type:  "set(set(A)) → num → num → (A → num → num → num → complex) → bool",
	Equations: []string{
		"∀T:set(set(A)). ∀r d:num. ∀a:(A → num → num → num → complex). " +
			"    bott_polynomial_coefficients(T, r, d, a) ⇔ " +
			"    (∀k i j:num. " +
			"        k < d ∧ i < r ∧ j < r ⇒ continuous_map(T, complex_topology, λx:A. a(x, k, i, j)))",
	},
})}

var companionDef = companionDefThm{family.Define(registry.DefEntry{
	Name:  "companionDef",
	Key:   "prop_2ee2f5f056e58963",
	Const: "bott_companion",
	Type:  "set(set(A)) → num → num → (A → num → num → num → complex) → A → num → num → complex",
	Equations: []string{
		"∀T:set(set(A)). ∀r d:num. ∀a:(A → num → num → num → complex). ∀x:A. ∀i j:num. " +
			"    bott_companion(T, r, d, a, x, i, j) = " +
			"    COND(x ∈ ⋃T ∧ i < r * d ∧ j < r * d, " +
			"        COND(nat_div(i, r) = suc(nat_div(j, r)) ∧ nat_mod(i, r) = nat_mod(j, r), " +
			"            complex_of_real(&1), " +
			"            complex_of_real(&0)) - " +
			"        COND(nat_div(j, r) + 1 = d, " +
			"            a(x, nat_div(i, r), nat_mod(i, r), nat_mod(j, r)), " +
			"            complex_of_real(&0)), " +
			"        complex_of_real(&0))",
	},
})}

var iterateDef = iterateDefThm{family.Define(registry.DefEntry{
	Name:  "iterateDef",
	Key:   "prop_60510a6fa2a5c87c",
	Const: "bott_matrix_iterate",
	Type:  "num → (A → num → num → complex) → A → num → (num → complex) → num → complex",
	Equations: []string{
		"∀r:num. ∀C:(A → num → num → complex). ∀x:A. ∀v:(num → complex). " +
			"    bott_matrix_iterate(r, C, x, 0, v) = v",
		"∀r:num. ∀C:(A → num → num → complex). ∀x:A. ∀k:num. ∀v:(num → complex). " +
			"    bott_matrix_iterate(r, C, x, suc(k), v) = " +
			"    λi:num. " +
			"        COND(i < r, " +
			"            module_sum(complex_add, " +
			"                complex_of_real(&0), " +
			"                {j:num | j < r}, " +
			"                λj:num. C(x, i, j) * bott_matrix_iterate(r, C, x, k, v, j)), " +
			"            complex_of_real(&0))",
	},
})}

var insideProjectionDef = insideProjectionDefThm{family.Define(registry.DefEntry{
	Name:  "insideProjectionDef",
	Key:   "prop_26d5026e5b7c0c7",
	Deps:  []registry.EntryLike{iterateDef},
	Const: "bott_inside_projection",
	Type:  "set(set(A)) → num → (A → num → num → complex) → prod(num, A → num → num → complex)",
	Equations: []string{
		"∀T:set(set(A)). ∀r:num. ∀C:(A → num → num → complex). " +
			"    bott_inside_projection(T, r, C) = " +
			"    (r, " +
			"        λx:A. " +
			"            COND(x ∈ ⋃T, " +
			"                εQ:(num → num → complex). " +
			"                    (∀i j:num. " +
			"                        Q(i, j) = " +
			"                        COND(i < r ∧ j < r, complex_conj(Q(j, i)), complex_of_real(&0))) ∧ " +
			"                    (∀i j:num. " +
			"                        i < r ∧ j < r ⇒ " +
			"                        module_sum(complex_add, " +
			"                            complex_of_real(&0), " +
			"                            {l:num | l < r}, " +
			"                            λl:num. Q(i, l) * Q(l, j)) = " +
			"                        Q(i, j)) ∧ " +
			"                    (∀v:(num → complex). " +
			"                        (∀i:num. r ≤ i ⇒ v(i) = complex_of_real(&0)) ⇒ " +
			"                        ((∀i:num. " +
			"                                i < r ⇒ " +
			"                                module_sum(complex_add, " +
			"                                    complex_of_real(&0), " +
			"                                    {j:num | j < r}, " +
			"                                    λj:num. Q(i, j) * v(j)) = " +
			"                                v(i)) ⇔ " +
			"                            (∀ε:real. " +
			"                                &0 < ε ⇒ " +
			"                                ∃K:num. ∀k:num. " +
			"                                    K ≤ k ⇒ " +
			"                                    real_sum({i:num | i < r}, " +
			"                                        λi:num. " +
			"                                            real_pow(|bott_matrix_iterate(r, C, x, k, v, i)|, " +
			"                                                2)) < " +
			"                                    ε))), " +
			"                λi:num. λj:num. complex_of_real(&0)))",
	},
})}

var polynomializationDef = polynomializationDefThm{family.Define(registry.DefEntry{
	Name:  "polynomializationDef",
	Key:   "prop_fb37cb3984622172",
	Deps:  []registry.EntryLike{clutchingDef, polynomialLoopDef, polynomialCoefficientsDef},
	Const: "bott_polynomialization",
	Type: "set(set(A)) → " +
		"num → " +
		"(A → complex → num → num → complex) → " +
		"num → " +
		"num → " +
		"real → " +
		"(A → num → num → num → complex) → " +
		"bool",
	Equations: []string{
		"∀T:set(set(A)). " +
			"∀r N d:num. " +
			"∀g:(A → complex → num → num → complex). " +
			"∀c:real. " +
			"∀a:(A → num → num → num → complex). " +
			"    bott_polynomialization(T, r, g, N, d, c, a) ⇔ " +
			"    &0 < c ∧ " +
			"    bott_polynomial_coefficients(T, r, d, a) ∧ " +
			"    (∀t:real. " +
			"        &0 ≤ t ∧ t ≤ &1 ⇒ " +
			"        bott_clutching(T, " +
			"            r, " +
			"            λx:A. λz:complex. λi:num. λj:num. " +
			"                complex_of_real(&1 - t) * " +
			"                monoid_pow(complex_mul, complex_of_real(&1), z, N) * " +
			"                g(x, z, i, j) + " +
			"                complex_of_real(t * c) * bott_polynomial_loop(T, r, d, a)(x, z, i, j)))",
	},
})}

var clutchingIndexDef = clutchingIndexDefThm{family.Define(registry.DefEntry{
	Name:  "clutchingIndexDef",
	Key:   "prop_ec8f1b6827be5328",
	Deps:  []registry.EntryLike{companionDef, insideProjectionDef, polynomializationDef},
	Const: "bott_clutching_index",
	Type: "set(set(A)) → " +
		"num → " +
		"(A → complex → num → num → complex) → " +
		"set(prod(prod(num, A → num → num → complex), prod(num, A → num → num → complex)))",
	Equations: []string{
		"∀T:set(set(A)). ∀r:num. ∀g:(A → complex → num → num → complex). " +
			"    bott_clutching_index(T, r, g) = " +
			"    εv:set(prod(prod(num, A → num → num → complex), prod(num, A → num → num → complex))). " +
			"    ∃N d:num. " +
			"    ∃c:real. " +
			"    ∃a:(A → num → num → num → complex). " +
			"        bott_polynomialization(T, r, g, N, d, c, a) ∧ " +
			"        v = " +
			"        k_class(T, " +
			"            (bott_inside_projection(T, r * d, bott_companion(T, r, d, a)), " +
			"                projection_trivial(T, N * r)))",
	},
})}

var clutchingInverseDef = clutchingInverseDefThm{family.Define(registry.DefEntry{
	Name:  "clutchingInverseDef",
	Key:   "prop_507f1139530e4f9b",
	Deps:  []registry.EntryLike{clutchingDef, clutchingTripleDef, clutchingIndexDef},
	Const: "bott_inverse",
	Type: "set(set(A)) → " +
		"set(prod(prod(num, prod(A, complex) → num → num → complex), " +
		"        prod(prod(num, prod(A, complex) → num → num → complex), " +
		"            prod(A, complex) → num → num → complex))) → " +
		"set(prod(prod(num, A → num → num → complex), prod(num, A → num → num → complex)))",
	Equations: []string{
		"∀T:set(set(A)). " +
			"∀a:set(prod(prod(num, prod(A, complex) → num → num → complex), " +
			"            prod(prod(num, prod(A, complex) → num → num → complex), " +
			"                prod(A, complex) → num → num → complex))). " +
			"    bott_inverse(T, a) = " +
			"    εv:set(prod(prod(num, A → num → num → complex), prod(num, A → num → num → complex))). " +
			"    ∃r:num. " +
			"    ∃g:(A → complex → num → num → complex). " +
			"        bott_clutching(T, r, g) ∧ " +
			"        a = kc_class(product_topology(T, complex_topology), bott_clutching_triple(T, r, g)) ∧ " +
			"        v = bott_clutching_index(T, r, g)",
	},
})}

var compactSupportBottDef = compactSupportBottDefThm{family.Define(registry.DefEntry{
	Name:  "compactSupportBottDef",
	Key:   "prop_c03f75fb2306f269",
	Deps:  []registry.EntryLike{BottClassDef},
	Const: "kc_bott_map",
	Type: "set(set(A)) → " +
		"set(prod(prod(num, A → num → num → complex), " +
		"        prod(prod(num, A → num → num → complex), A → num → num → complex))) → " +
		"set(prod(prod(num, prod(A, complex) → num → num → complex), " +
		"        prod(prod(num, prod(A, complex) → num → num → complex), " +
		"            prod(A, complex) → num → num → complex)))",
	Equations: []string{
		"∀T:set(set(A)). " +
			"∀a:set(prod(prod(num, A → num → num → complex), " +
			"            prod(prod(num, A → num → num → complex), A → num → num → complex))). " +
			"    kc_bott_map(T, a) = kc_external(T, complex_topology, a, bott_class)",
	},
})}
