package thom_form

import (
	"github.com/euc-ai/xugo/library/registry"
)

var puncturedDef = puncturedDefThm{family.Define(registry.DefEntry{
	Name:  "puncturedDef",
	Key:   "prop_d54efeb7f1027a90",
	Const: "tangent_punctured",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"set(prod(A, prod(set(A), A → num → real) → num → real))",
	Dimensions: []string{"n"},
	Equations: []string{
		"∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). " +
			"    tangent_punctured⟨n⟩(T, 𝒜) = " +
			"    {p:prod(A, prod(set(A), A → num → real) → num → real) | " +
			"        p ∈ tangent_bundle⟨n⟩(T, 𝒜) ∧ snd(p) ≠ (λc:prod(set(A), A → num → real). λi:num. &0)}",
	},
})}

var connectionDifferenceDef = connectionDifferenceDefThm{family.Define(registry.DefEntry{
	Name:  "connectionDifferenceDef",
	Key:   "prop_8de4f905f3e0555b",
	Const: "angular_connection_difference",
	Type: "num → " +
		"set(num → real) → " +
		"num → " +
		"(num → num → (num → real) → (num → num → real) → real) → " +
		"(num → (num → real) → real) → " +
		"num → " +
		"num → " +
		"(num → real) → " +
		"(num → num → real) → " +
		"real",
	Dimensions: []string{"d"},
	Reading: "The skew difference is u(Du)^T − (Du)u^T; " +
		"adding it to B makes the unit section parallel.",
	Equations: []string{
		"∀d r:num. " +
			"∀W:set(num → real). " +
			"∀B:(num → num → (num → real) → (num → num → real) → real). " +
			"∀u:(num → (num → real) → real). " +
			"∀i j:num. " +
			"∀x:(num → real). " +
			"∀P:(num → num → real). " +
			"    angular_connection_difference⟨d⟩(W, r, B, u)(i, j, x, P) = " +
			"    COND(x ∈ W ∧ i < r ∧ j < r, " +
			"        u(i, x) * " +
			"        (vec_exterior_derivative⟨d⟩(W, " +
			"                0, " +
			"                (λx:(num → real). λQ:(num → num → real). COND(x ∈ W, u(j, x), &0)))(x, P) + " +
			"            real_sum({l:num | l < r}, λl:num. B(j, l, x, P) * u(l, x))) - " +
			"        (vec_exterior_derivative⟨d⟩(W, " +
			"                0, " +
			"                (λx:(num → real). λQ:(num → num → real). COND(x ∈ W, u(i, x), &0)))(x, P) + " +
			"            real_sum({l:num | l < r}, λl:num. B(i, l, x, P) * u(l, x))) * " +
			"        u(j, x), " +
			"        &0)",
	},
})}

var transgressionDef = transgressionDefThm{family.Define(registry.DefEntry{
	Name:  "transgressionDef",
	Key:   "prop_2250c9cab4136c1b",
	Const: "angular_transgression",
	Type: "num → " +
		"set(num → real) → " +
		"num → " +
		"(num → num → (num → real) → (num → num → real) → real) → " +
		"(num → (num → real) → real) → " +
		"(num → real) → " +
		"(num → num → real) → " +
		"real",
	Dimensions: []string{"d"},
	Deps:       []registry.EntryLike{connectionDifferenceDef},
	Reading: "Time is the final coordinate and the first contracted vector. " +
		"The curvature includes dt, so this is K Pf(Ω/(2π)) for the affine path B + tα.",
	Equations: []string{
		"∀d r:num. " +
			"∀W:set(num → real). " +
			"∀B:(num → num → (num → real) → (num → num → real) → real). " +
			"∀u:(num → (num → real) → real). " +
			"    angular_transgression⟨d⟩(W, r, B, u) = " +
			"    vec_form_homotopy⟨d⟩(W, " +
			"        r - 1, " +
			"        vec_form_pfaffian⟨d + 1⟩({z:(num → real) | " +
			"                vec⟨d + 1⟩(z) ∧ (λz:(num → real). λi:num. COND(i < d, z(i), &0))(z) ∈ W}, " +
			"            r, " +
			"            (λi:num. λj:num. λz:(num → real). λP:(num → num → real). " +
			"                (&1 / (&2 * π)) * " +
			"                vec_form_curvature⟨d + 1⟩({z:(num → real) | " +
			"                        vec⟨d + 1⟩(z) ∧ " +
			"                        (λz:(num → real). λi:num. COND(i < d, z(i), &0))(z) ∈ W}, " +
			"                    r, " +
			"                    (λi:num. λj:num. λz:(num → real). λP:(num → num → real). " +
			"                        vec_form_matrix_pullback⟨d + 1, d⟩({z:(num → real) | " +
			"                                vec⟨d + 1⟩(z) ∧ " +
			"                                (λz:(num → real). λi:num. COND(i < d, z(i), &0))(z) ∈ W}, " +
			"                            1, " +
			"                            r, " +
			"                            r, " +
			"                            (λz:(num → real). λi:num. COND(i < d, z(i), &0)), " +
			"                            B)(i, j, z, P) + " +
			"                        z(d) * " +
			"                        vec_form_matrix_pullback⟨d + 1, d⟩({z:(num → real) | " +
			"                                vec⟨d + 1⟩(z) ∧ " +
			"                                (λz:(num → real). λi:num. COND(i < d, z(i), &0))(z) ∈ W}, " +
			"                            1, " +
			"                            r, " +
			"                            r, " +
			"                            (λz:(num → real). λi:num. COND(i < d, z(i), &0)), " +
			"                            angular_connection_difference⟨d⟩(W, r, B, u))(i, j, z, P)))(i, " +
			"                    j, " +
			"                    z, " +
			"                    P))))",
	},
})}

var frameChartDef = frameChartDefThm{family.Define(registry.DefEntry{
	Name:  "frameChartDef",
	Key:   "prop_cbbc84123e925d5e",
	Const: "thom_frame_chart",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"(prod(set(A), A → num → real) → (num → real) → num → num → real) → " +
		"prod(set(A), A → num → real) → " +
		"((num → real) → num → num → real) → " +
		"prod(set(prod(A, prod(set(A), A → num → real) → num → real)), " +
		"    prod(A, prod(set(A), A → num → real) → num → real) → num → real)",
	Dimensions: []string{"n"},
	Deps:       []registry.EntryLike{puncturedDef},
	Reading: "The fiber coordinates are EᵀGv in a positive orthonormal " +
		"frame. This chart is restricted to the complement of the zero section.",
	Equations: []string{
		"∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀g:(prod(set(A), A → num → real) → (num → real) → num → num → real). " +
			"∀c:prod(set(A), A → num → real). " +
			"∀E:((num → real) → num → num → real). " +
			"    thom_frame_chart⟨n⟩(T, 𝒜, g, c, E) = " +
			"    ({p:prod(A, prod(set(A), A → num → real) → num → real) | " +
			"            p ∈ tangent_punctured⟨n⟩(T, 𝒜) ∧ fst(p) ∈ fst(c)}, " +
			"        (λp:prod(A, prod(set(A), A → num → real) → num → real). λi:num. " +
			"            COND(i < n, " +
			"                snd(c)(fst(p), i), " +
			"                COND(i < 2 * n, " +
			"                    matrix_act⟨n⟩(matrix_product(real_ring, " +
			"                            n, " +
			"                            transpose(E(snd(c)(fst(p)))), " +
			"                            g(c, snd(c)(fst(p)))), " +
			"                        snd(p)(c))(i - n), " +
			"                    &0))))",
	},
})}

var localAngularDef = localAngularDefThm{family.Define(registry.DefEntry{
	Name:  "localAngularDef",
	Key:   "prop_ce7e0a8956bd60be",
	Const: "riemannian_local_angular",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"(prod(set(A), A → num → real) → (num → real) → num → num → real) → " +
		"prod(set(A), A → num → real) → " +
		"((num → real) → num → num → real) → " +
		"(num → real) → " +
		"(num → num → real) → " +
		"real",
	Dimensions: []string{"n"},
	Deps:       []registry.EntryLike{frameChartDef, transgressionDef},
	Equations: []string{
		"∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀g:(prod(set(A), A → num → real) → (num → real) → num → num → real). " +
			"∀c:prod(set(A), A → num → real). " +
			"∀E:((num → real) → num → num → real). " +
			"    riemannian_local_angular⟨n⟩(T, 𝒜, g, c, E) = " +
			"    angular_transgression⟨2 * n⟩(image(snd(thom_frame_chart⟨n⟩(T, 𝒜, g, c, E)), " +
			"            fst(thom_frame_chart⟨n⟩(T, 𝒜, g, c, E))), " +
			"        n, " +
			"        vec_form_matrix_pullback⟨2 * n, n⟩(image(snd(thom_frame_chart⟨n⟩(T, 𝒜, g, c, E)), " +
			"                fst(thom_frame_chart⟨n⟩(T, 𝒜, g, c, E))), " +
			"            1, " +
			"            n, " +
			"            n, " +
			"            «first coordinates», " +
			"            riemannian_connection⟨n⟩(g, c, E)), " +
			"        (λi:num. λz:(num → real). " +
			"            COND(i < n, «fiber coordinates»(z)(i) / ‖«fiber coordinates»(z)‖_n, &0)))",
	},
})}

var angularRepresentativeDef = angularRepresentativeDefThm{family.Define(registry.DefEntry{
	Name:  "angularRepresentativeDef",
	Key:   "prop_c4c56fd87bf34999",
	Const: "riemannian_angular_representative",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"(prod(set(A), A → num → real) → (num → real) → num → num → real) → " +
		"(prod(set(prod(A, prod(set(A), A → num → real) → num → real)), " +
		"        prod(A, prod(set(A), A → num → real) → num → real) → num → real) → " +
		"    (num → real) → " +
		"    (num → num → real) → " +
		"    real) → " +
		"bool",
	Dimensions: []string{"n"},
	Deps:       []registry.EntryLike{localAngularDef, puncturedDef},
	Equations: []string{
		"∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀g:(prod(set(A), A → num → real) → (num → real) → num → num → real). " +
			"∀ψ:(prod(set(prod(A, prod(set(A), A → num → real) → num → real)), " +
			"            prod(A, prod(set(A), A → num → real) → num → real) → num → real) → " +
			"        (num → real) → " +
			"        (num → num → real) → " +
			"        real). " +
			"    riemannian_angular_representative⟨n⟩(T, 𝒜, g, ψ) ⇔ " +
			"    oriented_manifold⟨n⟩(T, 𝒜) ∧ " +
			"    riemannian_metric⟨n⟩(T, 𝒜, g) ∧ " +
			"    manifold_form_on⟨2 * n⟩(«punctured topology», «punctured atlas», n - 1, ψ) ∧ " +
			"    (∀c:prod(set(A), A → num → real). ∀E:((num → real) → num → num → real). " +
			"        positive_manifold_chart⟨n⟩(T, 𝒜, c) ∧ riemannian_positive_frame⟨n⟩(T, 𝒜, g, c, E) ⇒ " +
			"        ψ(thom_frame_chart⟨n⟩(T, 𝒜, g, c, E)) = riemannian_local_angular⟨n⟩(T, 𝒜, g, c, E))",
	},
})}

var angularFormDef = angularFormDefThm{family.Define(registry.DefEntry{
	Name:  "angularFormDef",
	Key:   "prop_2f87acdb2baed1c",
	Const: "riemannian_angular_form",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"(prod(set(A), A → num → real) → (num → real) → num → num → real) → " +
		"prod(set(prod(A, prod(set(A), A → num → real) → num → real)), " +
		"    prod(A, prod(set(A), A → num → real) → num → real) → num → real) → " +
		"(num → real) → " +
		"(num → num → real) → " +
		"real",
	Dimensions: []string{"n"},
	Deps:       []registry.EntryLike{angularRepresentativeDef},
	Reading: "Existence and uniqueness are asserted for positive even rank. " +
		"Outside those hypotheses this Hilbert choice has no geometric specification.",
	Equations: []string{
		"∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀g:(prod(set(A), A → num → real) → (num → real) → num → num → real). " +
			"    riemannian_angular_form⟨n⟩(T, 𝒜, g) = " +
			"    (εψ:(prod(set(prod(A, prod(set(A), A → num → real) → num → real)), " +
			"                prod(A, prod(set(A), A → num → real) → num → real) → num → real) → " +
			"            (num → real) → " +
			"            (num → num → real) → " +
			"            real). " +
			"        riemannian_angular_representative⟨n⟩(T, 𝒜, g, ψ))",
	},
})}

var frameFiberDef = frameFiberDefThm{family.Define(registry.DefEntry{
	Name:  "frameFiberDef",
	Key:   "prop_f52cd1c0148aec6c",
	Const: "thom_frame_fiber",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"prod(set(A), A → num → real) → " +
		"((num → real) → num → num → real) → " +
		"A → " +
		"(num → real) → " +
		"prod(A, prod(set(A), A → num → real) → num → real)",
	Dimensions: []string{"n"},
	Equations: []string{
		"∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀c:prod(set(A), A → num → real). " +
			"∀E:((num → real) → num → num → real). " +
			"∀x:A. " +
			"∀y:(num → real). " +
			"    thom_frame_fiber⟨n⟩(T, 𝒜, c, E, x)(y) = " +
			"    (x, tangent_from_chart⟨n⟩(T, 𝒜, c, x, matrix_act⟨n⟩(E(snd(c)(x)), y)))",
	},
})}

var angularVolumeDef = angularVolumeDefThm{family.Define(registry.DefEntry{
	Name:  "angularVolumeDef",
	Key:   "prop_3fd4c1ec507b00a0",
	Const: "even_angular_volume",
	Type:  "num → (num → real) → (num → num → real) → real",
	Reading: "The ordered columns are the radial vector followed by the 2m + 1 tangent vectors. " +
		"The coefficient is the reciprocal sphere volume times radius to the negative dimension.",
	Equations: []string{
		"∀m:num. ∀y:(num → real). ∀P:(num → num → real). " +
			"    even_angular_volume(m, y, P) = " +
			"    COND(vec⟨2 * m + 2⟩(y) ∧ y ≠ (λi:num. &0), " +
			"        (&factorial(m) / (&2 * π ^ (m + 1) * ⟪y, y⟫_(2 * m + 2) ^ (m + 1))) * " +
			"        determinant(real_ring, " +
			"            2 * m + 2, " +
			"            (λi:num. λj:num. " +
			"                COND(i < 2 * m + 2 ∧ j < 2 * m + 2, COND(j = 0, y(i), P(i, j - 1)), &0))), " +
			"        &0)",
	},
})}

var radialCutoffDef = radialCutoffDefThm{family.Define(registry.DefEntry{
	Name:  "radialCutoffDef",
	Key:   "prop_87c63e5a9c45d0b3",
	Const: "thom_radial_cutoff",
	Type:  "real → real → (real → real) → bool",
	Reading: "Both radii are squared radii. The function is constant " +
		"on a whole interval around zero and outside the outer radius.",
	Equations: []string{
		"∀a b:real. ∀ρ:(real → real). " +
			"    thom_radial_cutoff(a, b, ρ) ⇔ " +
			"    &0 < a ∧ " +
			"    a < b ∧ " +
			"    vec_smooth_on⟨1⟩({t:num → real | vec⟨1⟩(t)}, λt:(num → real). ρ(t(0))) ∧ " +
			"    (∀s:real. s ≤ a ⇒ ρ(s) = -&1) ∧ " +
			"    (∀s:real. b ≤ s ⇒ ρ(s) = &0)",
	},
})}

var thomRepresentativeDef = thomRepresentativeDefThm{family.Define(registry.DefEntry{
	Name:  "thomRepresentativeDef",
	Key:   "prop_65752947702707d1",
	Const: "riemannian_thom_representative",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"(prod(set(A), A → num → real) → (num → real) → num → num → real) → " +
		"real → " +
		"(real → real) → " +
		"(prod(set(prod(A, prod(set(A), A → num → real) → num → real)), " +
		"        prod(A, prod(set(A), A → num → real) → num → real) → num → real) → " +
		"    (num → real) → " +
		"    (num → num → real) → " +
		"    real) → " +
		"bool",
	Dimensions: []string{"n"},
	Deps:       []registry.EntryLike{angularFormDef},
	Reading: "This is the gluing specification: d(ρψ) off the zero " +
		"section, π*e where the squared norm is below a. No closedness, " +
		"support or fiber-integral conclusion is built into this predicate.",
	Equations: []string{
		"∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀g:(prod(set(A), A → num → real) → (num → real) → num → num → real). " +
			"∀a:real. " +
			"∀ρ:(real → real). " +
			"∀U:(prod(set(prod(A, prod(set(A), A → num → real) → num → real)), " +
			"            prod(A, prod(set(A), A → num → real) → num → real) → num → real) → " +
			"        (num → real) → " +
			"        (num → num → real) → " +
			"        real). " +
			"    riemannian_thom_representative⟨n⟩(T, 𝒜, g, a, ρ, U) ⇔ " +
			"    manifold_form_on⟨2 * n⟩(tangent_topology⟨n⟩(T, 𝒜), tangent_atlas⟨n⟩(T, 𝒜), n, U) ∧ " +
			"    manifold_form_restrict⟨2 * n⟩(tangent_topology⟨n⟩(T, 𝒜), " +
			"        tangent_atlas⟨n⟩(T, 𝒜), " +
			"        tangent_punctured⟨n⟩(T, 𝒜), " +
			"        U) = " +
			"    manifold_exterior_derivative⟨2 * n⟩(«punctured topology», " +
			"        «punctured atlas», " +
			"        n - 1, " +
			"        manifold_form_weight⟨2 * n⟩(«punctured topology», " +
			"            «punctured atlas», " +
			"            (λp:prod(A, prod(set(A), A → num → real) → num → real). " +
			"                ρ(riemannian_pairing⟨n⟩(T, 𝒜, g, fst(p), snd(p), snd(p)))), " +
			"            riemannian_angular_form⟨n⟩(T, 𝒜, g))) ∧ " +
			"    manifold_form_restrict⟨2 * n⟩(tangent_topology⟨n⟩(T, 𝒜), " +
			"        tangent_atlas⟨n⟩(T, 𝒜), " +
			"        {p:prod(A, prod(set(A), A → num → real) → num → real) | " +
			"            p ∈ tangent_bundle⟨n⟩(T, 𝒜) ∧ " +
			"            riemannian_pairing⟨n⟩(T, 𝒜, g, fst(p), snd(p), snd(p)) < a}, " +
			"        U) = " +
			"    manifold_form_pullback⟨2 * n, n⟩(subtopology(tangent_topology⟨n⟩(T, 𝒜), " +
			"            {p:prod(A, prod(set(A), A → num → real) → num → real) | " +
			"                p ∈ tangent_bundle⟨n⟩(T, 𝒜) ∧ " +
			"                riemannian_pairing⟨n⟩(T, 𝒜, g, fst(p), snd(p), snd(p)) < a}), " +
			"        open_submanifold_atlas⟨2 * n⟩(tangent_topology⟨n⟩(T, 𝒜), " +
			"            tangent_atlas⟨n⟩(T, 𝒜), " +
			"            {p:prod(A, prod(set(A), A → num → real) → num → real) | " +
			"                p ∈ tangent_bundle⟨n⟩(T, 𝒜) ∧ " +
			"                riemannian_pairing⟨n⟩(T, 𝒜, g, fst(p), snd(p), snd(p)) < a}), " +
			"        T, " +
			"        𝒜, " +
			"        n, " +
			"        (λp:prod(A, prod(set(A), A → num → real) → num → real). fst(p)), " +
			"        riemannian_euler_form⟨n⟩(T, 𝒜, g))",
	},
})}

var ThomFormDef = thomFormDefThm{family.Define(registry.DefEntry{
	Name:  "ThomFormDef",
	Key:   "prop_2e47d1d786fab631",
	Const: "riemannian_thom_form",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"(prod(set(A), A → num → real) → (num → real) → num → num → real) → " +
		"real → " +
		"(real → real) → " +
		"prod(set(prod(A, prod(set(A), A → num → real) → num → real)), " +
		"    prod(A, prod(set(A), A → num → real) → num → real) → num → real) → " +
		"(num → real) → " +
		"(num → num → real) → " +
		"real",
	Dimensions: []string{"n"},
	Deps:       []registry.EntryLike{thomRepresentativeDef},
	Equations: []string{
		"∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀g:(prod(set(A), A → num → real) → (num → real) → num → num → real). " +
			"∀a:real. " +
			"∀ρ:(real → real). " +
			"    riemannian_thom_form⟨n⟩(T, 𝒜, g, a, ρ) = " +
			"    (εU:(prod(set(prod(A, prod(set(A), A → num → real) → num → real)), " +
			"                prod(A, prod(set(A), A → num → real) → num → real) → num → real) → " +
			"            (num → real) → " +
			"            (num → num → real) → " +
			"            real). " +
			"        riemannian_thom_representative⟨n⟩(T, 𝒜, g, a, ρ, U))",
	},
})}
