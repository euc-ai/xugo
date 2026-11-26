package projection_geometry

import (
	"github.com/euc-ai/xugo/library/registry"
)

var FrameDef = frameDefThm{family.Define(registry.DefEntry{
	Name:  "FrameDef",
	Key:   "prop_7c640064bf772954",
	Const: "smooth_projection_frame",
	Type: "num → " +
		"num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"prod(num, A → num → num → complex) → " +
		"set(A) → " +
		"(A → num → num → complex) → " +
		"bool",
	Equations: []string{
		"∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀r:num. " +
			"∀P:prod(num, A → num → num → complex). " +
			"∀U:set(A). " +
			"∀F:(A → num → num → complex). " +
			"    smooth_projection_frame(n, r, T, 𝒜, P, U, F) ⇔ " +
			"    smooth_projection_bundle(n, fst(P), T, 𝒜, snd(P)) ∧ " +
			"    U ∈ T ∧ " +
			"    (∀i j:num. " +
			"        i < fst(P) ∧ j < r ⇒ " +
			"        smooth_manifold_function⟨n⟩(subtopology(T, U), " +
			"            open_submanifold_atlas⟨n⟩(T, 𝒜, U), " +
			"            λx:A. re(F(x, i, j))) ∧ " +
			"        smooth_manifold_function⟨n⟩(subtopology(T, U), " +
			"            open_submanifold_atlas⟨n⟩(T, 𝒜, U), " +
			"            λx:A. im(F(x, i, j)))) ∧ " +
			"    (∀x:A. ∀i j:num. " +
			"        x ∈ U ⇒ " +
			"        (F(x, i, j) = COND(i < fst(P) ∧ j < r, F(x, i, j), complex_of_real(&0))) ∧ " +
			"        (i < r ∧ j < r ⇒ " +
			"            module_sum(complex_add, " +
			"                complex_of_real(&0), " +
			"                {l:num | l < fst(P)}, " +
			"                λl:num. complex_conj(F(x, l, i)) * F(x, l, j)) = " +
			"            COND(i = j, complex_of_real(&1), complex_of_real(&0))) ∧ " +
			"        (i < fst(P) ∧ j < fst(P) ⇒ " +
			"            module_sum(complex_add, " +
			"                complex_of_real(&0), " +
			"                {l:num | l < r}, " +
			"                λl:num. F(x, i, l) * complex_conj(F(x, j, l))) = " +
			"            snd(P)(x, i, j)))",
	},
})}

var chartDef = chartDefThm{family.Define(registry.DefEntry{
	Name:  "chartDef",
	Key:   "prop_110a9eff9b7e6bb2",
	Const: "projection_total_chart",
	Type: "num → " +
		"num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"prod(num, A → num → num → complex) → " +
		"prod(set(A), A → num → real) → " +
		"(A → num → num → complex) → " +
		"prod(set(prod(A, num → complex)), prod(A, num → complex) → num → real)",
	Equations: []string{
		"∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀r:num. " +
			"∀P:prod(num, A → num → num → complex). " +
			"∀c:prod(set(A), A → num → real). " +
			"∀F:(A → num → num → complex). " +
			"    projection_total_chart(n, r, T, 𝒜, P, c, F) = " +
			"    ({p:prod(A, num → complex) | p ∈ projection_total_space(T, P) ∧ fst(p) ∈ fst(c)}, " +
			"        λp:prod(A, num → complex). λi:num. " +
			"            COND(i < n, " +
			"                snd(c)(fst(p), i), " +
			"                COND(i < n + 2 * r, " +
			"                    COND(nat_mod(i - n, 2) = 0, " +
			"                        re(module_sum(complex_add, " +
			"                                complex_of_real(&0), " +
			"                                {j:num | j < fst(P)}, " +
			"                                λj:num. " +
			"                                    complex_conj(F(fst(p), j, nat_div(i - n, 2))) * " +
			"                                    snd(p)(j))), " +
			"                        im(module_sum(complex_add, " +
			"                                complex_of_real(&0), " +
			"                                {j:num | j < fst(P)}, " +
			"                                λj:num. " +
			"                                    complex_conj(F(fst(p), j, nat_div(i - n, 2))) * " +
			"                                    snd(p)(j)))), " +
			"                    &0)))",
	},
})}

var AtlasDef = atlasDefThm{family.Define(registry.DefEntry{
	Name:  "AtlasDef",
	Key:   "prop_fc7c7f0a3c0d5ddb",
	Deps:  []registry.EntryLike{FrameDef, chartDef},
	Const: "projection_total_atlas",
	Type: "num → " +
		"num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"prod(num, A → num → num → complex) → " +
		"set(prod(set(prod(A, num → complex)), prod(A, num → complex) → num → real))",
	Equations: []string{
		"∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀r:num. " +
			"∀P:prod(num, A → num → num → complex). " +
			"    projection_total_atlas(n, r, T, 𝒜, P) = " +
			"    {e:prod(set(prod(A, num → complex)), prod(A, num → complex) → num → real) | " +
			"        ∃c:prod(set(A), A → num → real). ∃F:(A → num → num → complex). " +
			"            compatible_chart⟨n⟩(T, 𝒜, c) ∧ " +
			"            smooth_projection_frame(n, r, T, 𝒜, P, fst(c), F) ∧ " +
			"            e = projection_total_chart(n, r, T, 𝒜, P, c, F)}",
	},
})}

var orientedAtlasDef = orientedAtlasDefThm{family.Define(registry.DefEntry{
	Name:  "orientedAtlasDef",
	Key:   "prop_113f4d643fd4c6b",
	Deps:  []registry.EntryLike{FrameDef, chartDef},
	Const: "projection_oriented_atlas",
	Type: "num → " +
		"num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"prod(num, A → num → num → complex) → " +
		"set(prod(set(prod(A, num → complex)), prod(A, num → complex) → num → real))",
	Equations: []string{
		"∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀r:num. " +
			"∀P:prod(num, A → num → num → complex). " +
			"    projection_oriented_atlas(n, r, T, 𝒜, P) = " +
			"    {e:prod(set(prod(A, num → complex)), prod(A, num → complex) → num → real) | " +
			"        ∃c:prod(set(A), A → num → real). ∃F:(A → num → num → complex). " +
			"            positive_manifold_chart⟨n⟩(T, 𝒜, c) ∧ " +
			"            smooth_projection_frame(n, r, T, 𝒜, P, fst(c), F) ∧ " +
			"            e = projection_total_chart(n, r, T, 𝒜, P, c, F)}",
	},
})}

var FiberProperSupportDef = fiberProperSupportDefThm{family.Define(registry.DefEntry{
	Name:  "FiberProperSupportDef",
	Key:   "prop_8ffc2631c224e8cf",
	Deps:  []registry.EntryLike{AtlasDef},
	Const: "projection_fiber_proper",
	Type: "num → " +
		"num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"prod(num, A → num → num → complex) → " +
		"(prod(set(prod(A, num → complex)), prod(A, num → complex) → num → real) → " +
		"    (num → real) → " +
		"    (num → num → real) → " +
		"    real) → " +
		"bool",
	Equations: []string{
		"∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀r:num. " +
			"∀P:prod(num, A → num → num → complex). " +
			"∀ω:(prod(set(prod(A, num → complex)), prod(A, num → complex) → num → real) → " +
			"        (num → real) → " +
			"        (num → num → real) → " +
			"        real). " +
			"    projection_fiber_proper(n, r, T, 𝒜, P, ω) ⇔ " +
			"    ∀K:set(A). " +
			"        compact_in(T, K) ⇒ " +
			"        compact_in(projection_total_topology(T, P), " +
			"            manifold_form_support⟨n + 2 * r⟩(projection_total_topology(T, P), " +
			"                projection_total_atlas(n, r, T, 𝒜, P), " +
			"                ω) ∩ " +
			"            {p:prod(A, num → complex) | fst(p) ∈ K})",
	},
})}

var hasFiberIntegralDef = hasFiberIntegralDefThm{family.Define(registry.DefEntry{
	Name:  "hasFiberIntegralDef",
	Key:   "prop_9a8175baab34ff48",
	Deps:  []registry.EntryLike{FrameDef, chartDef},
	Const: "projection_has_fiber_integral",
	Type: "num → " +
		"num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"prod(num, A → num → num → complex) → " +
		"num → " +
		"(prod(set(prod(A, num → complex)), prod(A, num → complex) → num → real) → " +
		"    (num → real) → " +
		"    (num → num → real) → " +
		"    real) → " +
		"(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real) → " +
		"bool",
	Equations: []string{
		"∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀r:num. " +
			"∀P:prod(num, A → num → num → complex). " +
			"∀k:num. " +
			"∀ω:(prod(set(prod(A, num → complex)), prod(A, num → complex) → num → real) → " +
			"        (num → real) → " +
			"        (num → num → real) → " +
			"        real). " +
			"∀β:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real). " +
			"    projection_has_fiber_integral(n, r, T, 𝒜, P, k, ω, β) ⇔ " +
			"    manifold_form_on⟨n⟩(T, 𝒜, k, β) ∧ " +
			"    (∀c:prod(set(A), A → num → real). " +
			"    ∀F:(A → num → num → complex). " +
			"    ∀y:(num → real). " +
			"    ∀V:(num → num → real). " +
			"        compatible_chart⟨n⟩(T, 𝒜, c) ∧ " +
			"        smooth_projection_frame(n, r, T, 𝒜, P, fst(c), F) ∧ " +
			"        y ∈ image(snd(c), fst(c)) ⇒ " +
			"        β(c, y, V) = " +
			"        vec_integral⟨2 * r⟩(λz:(num → real). " +
			"                ω(projection_total_chart(n, r, T, 𝒜, P, c, F), " +
			"                    (λi:num. COND(i < n, y(i), COND(i < n + 2 * r, z(i - n), &0))), " +
			"                    (λi:num. λj:num. " +
			"                        COND(i < n ∧ j < k, " +
			"                            V(i, j), " +
			"                            COND(n ≤ i ∧ i < n + 2 * r ∧ k ≤ j ∧ j < k + 2 * r ∧ i - n = j - k, " +
			"                                &1, " +
			"                                &0))))))",
	},
})}

var FiberIntegralDef = fiberIntegralDefThm{family.Define(registry.DefEntry{
	Name:  "FiberIntegralDef",
	Key:   "prop_7b8446983eba3462",
	Deps:  []registry.EntryLike{hasFiberIntegralDef},
	Const: "projection_fiber_integral",
	Type: "num → " +
		"num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"prod(num, A → num → num → complex) → " +
		"num → " +
		"(prod(set(prod(A, num → complex)), prod(A, num → complex) → num → real) → " +
		"    (num → real) → " +
		"    (num → num → real) → " +
		"    real) → " +
		"prod(set(A), A → num → real) → " +
		"(num → real) → " +
		"(num → num → real) → " +
		"real",
	Equations: []string{
		"∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀r:num. " +
			"∀P:prod(num, A → num → num → complex). " +
			"∀k:num. " +
			"∀ω:(prod(set(prod(A, num → complex)), prod(A, num → complex) → num → real) → " +
			"        (num → real) → " +
			"        (num → num → real) → " +
			"        real). " +
			"    projection_fiber_integral(n, r, T, 𝒜, P, k, ω) = " +
			"    εβ:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real). " +
			"        projection_has_fiber_integral(n, r, T, 𝒜, P, k, ω, β)",
	},
})}
