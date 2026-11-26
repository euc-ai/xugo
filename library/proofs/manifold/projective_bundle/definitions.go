package projective_bundle

import (
	"github.com/euc-ai/xugo/library/registry"
)

var SpaceDef = spaceDefThm{family.Define(registry.DefEntry{
	Name:  "SpaceDef",
	Key:   "prop_4126c4947a5d7e34",
	Const: "projective_space",
	Type:  "set(set(A)) → prod(num, A → num → num → complex) → set(prod(A, num → num → complex))",
	Equations: []string{
		"∀T:set(set(A)). ∀P:prod(num, A → num → num → complex). " +
			"    projective_space(T, P) = " +
			"    {p:prod(A, num → num → complex) | " +
			"        fst(p) ∈ ⋃T ∧ " +
			"        (∀i j:num. " +
			"            snd(p)(i, j) = " +
			"            COND(i < fst(P) ∧ j < fst(P), complex_conj(snd(p)(j, i)), complex_of_real(&0))) ∧ " +
			"        (∀i j:num. " +
			"            i < fst(P) ∧ j < fst(P) ⇒ " +
			"            module_sum(complex_add, " +
			"                complex_of_real(&0), " +
			"                {l:num | l < fst(P)}, " +
			"                λl:num. snd(p)(i, l) * snd(p)(l, j)) = " +
			"            snd(p)(i, j) ∧ " +
			"            module_sum(complex_add, " +
			"                complex_of_real(&0), " +
			"                {l:num | l < fst(P)}, " +
			"                λl:num. snd(P)(fst(p), i, l) * snd(p)(l, j)) = " +
			"            snd(p)(i, j)) ∧ " +
			"        module_sum(complex_add, " +
			"            complex_of_real(&0), " +
			"            {l:num | l < fst(P)}, " +
			"            λl:num. snd(p)(l, l)) = " +
			"        complex_of_real(&1)}",
	},
})}

var topologyDef = topologyDefThm{family.Define(registry.DefEntry{
	Name:  "topologyDef",
	Key:   "prop_177a35d80220f69e",
	Deps:  []registry.EntryLike{SpaceDef},
	Const: "projective_topology",
	Type: "set(set(A)) → " +
		"prod(num, A → num → num → complex) → " +
		"set(set(prod(A, num → num → complex)))",
	Equations: []string{
		"∀T:set(set(A)). ∀P:prod(num, A → num → num → complex). " +
			"    projective_topology(T, P) = " +
			"    subtopology(product_topology(T, " +
			"            indexed_product_topology({i:num | i < fst(P)}, " +
			"                λi:num. (λj:num. complex_of_real(&0)), " +
			"                λi:num. complex_coordinate_topology(fst(P)))), " +
			"        projective_space(T, P))",
	},
})}

var frameEntryDef = frameEntryDefThm{family.Define(registry.DefEntry{
	Name:  "frameEntryDef",
	Key:   "prop_9ffca2cfa7ff5f2",
	Const: "projective_frame_entry",
	Type:  "(A → num → num → complex) → prod(A, num → num → complex) → num → num → num → complex",
	Equations: []string{
		"∀F:(A → num → num → complex). ∀p:prod(A, num → num → complex). ∀N i j:num. " +
			"    projective_frame_entry(F, p, N, i, j) = " +
			"    module_sum(complex_add, " +
			"        complex_of_real(&0), " +
			"        {a:num | a < N}, " +
			"        λa:num. " +
			"            module_sum(complex_add, " +
			"                complex_of_real(&0), " +
			"                {b:num | b < N}, " +
			"                λb:num. complex_conj(F(fst(p), a, i)) * snd(p)(a, b) * F(fst(p), b, j)))",
	},
})}

var chartDef = chartDefThm{family.Define(registry.DefEntry{
	Name:  "chartDef",
	Key:   "prop_64637a0a31804e4a",
	Deps:  []registry.EntryLike{SpaceDef, frameEntryDef},
	Const: "projective_chart",
	Type: "num → " +
		"num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"prod(num, A → num → num → complex) → " +
		"prod(set(A), A → num → real) → " +
		"(A → num → num → complex) → " +
		"num → " +
		"prod(set(prod(A, num → num → complex)), prod(A, num → num → complex) → num → real)",
	Equations: []string{
		"∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀r:num. " +
			"∀P:prod(num, A → num → num → complex). " +
			"∀c:prod(set(A), A → num → real). " +
			"∀F:(A → num → num → complex). " +
			"∀l:num. " +
			"    projective_chart(n, r, T, 𝒜, P, c, F, l) = " +
			"    ({p:prod(A, num → num → complex) | " +
			"            p ∈ projective_space(T, P) ∧ " +
			"            fst(p) ∈ fst(c) ∧ " +
			"            &0 < re(projective_frame_entry(F, p, fst(P), l, l))}, " +
			"        λp:prod(A, num → num → complex). λi:num. " +
			"            COND(i < n, " +
			"                snd(c)(fst(p), i), " +
			"                COND(i < n + 2 * (r - 1), " +
			"                    COND(nat_mod(i - n, 2) = 0, " +
			"                        re(projective_frame_entry(F, " +
			"                                p, " +
			"                                fst(P), " +
			"                                COND(nat_div(i - n, 2) < l, " +
			"                                    nat_div(i - n, 2), " +
			"                                    suc(nat_div(i - n, 2))), " +
			"                                l) / " +
			"                            projective_frame_entry(F, p, fst(P), l, l)), " +
			"                        im(projective_frame_entry(F, " +
			"                                p, " +
			"                                fst(P), " +
			"                                COND(nat_div(i - n, 2) < l, " +
			"                                    nat_div(i - n, 2), " +
			"                                    suc(nat_div(i - n, 2))), " +
			"                                l) / " +
			"                            projective_frame_entry(F, p, fst(P), l, l))), " +
			"                    &0)))",
	},
})}

var atlasDef = atlasDefThm{family.Define(registry.DefEntry{
	Name:  "atlasDef",
	Key:   "prop_bc73406c86fcf93c",
	Deps:  []registry.EntryLike{chartDef},
	Const: "projective_atlas",
	Type: "num → " +
		"num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"prod(num, A → num → num → complex) → " +
		"set(prod(set(prod(A, num → num → complex)), prod(A, num → num → complex) → num → real))",
	Equations: []string{
		"∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀r:num. " +
			"∀P:prod(num, A → num → num → complex). " +
			"    projective_atlas(n, r, T, 𝒜, P) = " +
			"    {e:prod(set(prod(A, num → num → complex)), prod(A, num → num → complex) → num → real) | " +
			"        ∃c:prod(set(A), A → num → real). ∃F:(A → num → num → complex). ∃l:num. " +
			"            compatible_chart⟨n⟩(T, 𝒜, c) ∧ " +
			"            smooth_projection_frame(n, r, T, 𝒜, P, fst(c), F) ∧ " +
			"            l < r ∧ " +
			"            e = projective_chart(n, r, T, 𝒜, P, c, F, l)}",
	},
})}

var TautologicalDef = tautologicalDefThm{family.Define(registry.DefEntry{
	Name:  "TautologicalDef",
	Key:   "prop_ff936ca91cbb01b4",
	Deps:  []registry.EntryLike{SpaceDef},
	Const: "projective_tautological",
	Type: "set(set(A)) → " +
		"prod(num, A → num → num → complex) → " +
		"prod(num, prod(A, num → num → complex) → num → num → complex)",
	Equations: []string{
		"∀T:set(set(A)). ∀P:prod(num, A → num → num → complex). " +
			"    projective_tautological(T, P) = " +
			"    (fst(P), " +
			"        λp:prod(A, num → num → complex). λi:num. λj:num. " +
			"            COND(p ∈ projective_space(T, P), snd(p)(i, j), complex_of_real(&0)))",
	},
})}

var complementDef = complementDefThm{family.Define(registry.DefEntry{
	Name:  "complementDef",
	Key:   "prop_155f383c40320f9",
	Deps:  []registry.EntryLike{SpaceDef},
	Const: "projective_complement",
	Type: "set(set(A)) → " +
		"prod(num, A → num → num → complex) → " +
		"prod(num, prod(A, num → num → complex) → num → num → complex)",
	Equations: []string{
		"∀T:set(set(A)). ∀P:prod(num, A → num → num → complex). " +
			"    projective_complement(T, P) = " +
			"    (fst(P), " +
			"        λp:prod(A, num → num → complex). λi:num. λj:num. " +
			"            COND(p ∈ projective_space(T, P), " +
			"                snd(P)(fst(p), i, j) - snd(p)(i, j), " +
			"                complex_of_real(&0)))",
	},
})}

var modelTopologyDef = modelTopologyDefThm{family.Define(registry.DefEntry{
	Name:  "modelTopologyDef",
	Key:   "prop_8a8d5d1937096145",
	Deps:  []registry.EntryLike{topologyDef},
	Const: "projective_model_topology",
	Type:  "num → set(set(prod(bool, num → num → complex)))",
	Equations: []string{
		"∀r:num. " +
			"    projective_model_topology(r) = " +
			"    projective_topology({U:set(bool) | U ⊆ {⊤}}, projection_trivial({U:set(bool) | U ⊆ {⊤}}, r))",
	},
})}

var modelAtlasDef = modelAtlasDefThm{family.Define(registry.DefEntry{
	Name:  "modelAtlasDef",
	Key:   "prop_2ceb80d166833656",
	Deps:  []registry.EntryLike{atlasDef},
	Const: "projective_model_atlas",
	Type: "num → " +
		"set(prod(set(prod(bool, num → num → complex)), prod(bool, num → num → complex) → num → real))",
	Equations: []string{
		"∀r:num. " +
			"    projective_model_atlas(r) = " +
			"    projective_atlas(0, " +
			"        r, " +
			"        {U:set(bool) | U ⊆ {⊤}}, " +
			"        {({⊤}, λb:bool. λi:num. &0)}, " +
			"        projection_trivial({U:set(bool) | U ⊆ {⊤}}, r))",
	},
})}

var trivializationDef = trivializationDefThm{family.Define(registry.DefEntry{
	Name:  "trivializationDef",
	Key:   "prop_c5d9783c7227c2b1",
	Const: "projective_frame_map",
	Type: "num → " +
		"(A → num → num → complex) → " +
		"prod(A, prod(bool, num → num → complex)) → " +
		"prod(A, num → num → complex)",
	Equations: []string{
		"∀r:num. ∀F:(A → num → num → complex). ∀p:prod(A, prod(bool, num → num → complex)). " +
			"    projective_frame_map(r, F, p) = " +
			"    (fst(p), " +
			"        λi:num. λj:num. " +
			"            module_sum(complex_add, " +
			"                complex_of_real(&0), " +
			"                {a:num | a < r}, " +
			"                λa:num. " +
			"                    module_sum(complex_add, " +
			"                        complex_of_real(&0), " +
			"                        {b:num | b < r}, " +
			"                        λb:num. " +
			"                            F(fst(p), i, a) * " +
			"                            snd(snd(p))(a, b) * " +
			"                            complex_conj(F(fst(p), j, b)))))",
	},
})}

var fiberIntegralDef = fiberIntegralDefThm{family.Define(registry.DefEntry{
	Name: "fiberIntegralDef",
	Key:  "prop_ec0494f4ada4c710",
	Deps: []registry.EntryLike{
		topologyDef,
		atlasDef,
		modelTopologyDef,
		modelAtlasDef,
		trivializationDef,
	},
	Const: "projective_fiber_integral",
	Type: "num → " +
		"num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"prod(num, A → num → num → complex) → " +
		"num → " +
		"(prod(set(prod(A, num → num → complex)), prod(A, num → num → complex) → num → real) → " +
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
			"∀ω:(prod(set(prod(A, num → num → complex)), prod(A, num → num → complex) → num → real) → " +
			"        (num → real) → " +
			"        (num → num → real) → " +
			"        real). " +
			"    projective_fiber_integral(n, r, T, 𝒜, P, k, ω) = " +
			"    εβ:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real). " +
			"        manifold_form_on⟨n⟩(T, 𝒜, k, β) ∧ " +
			"        (∀U:set(A). ∀F:(A → num → num → complex). " +
			"            smooth_projection_frame(n, r, T, 𝒜, P, U, F) ⇒ " +
			"            manifold_form_restrict⟨n⟩(T, 𝒜, U, β) = " +
			"            manifold_fiber_integral⟨n, 2 * (r - 1)⟩(subtopology(T, U), " +
			"                open_submanifold_atlas⟨n⟩(T, 𝒜, U), " +
			"                projective_model_topology(r), " +
			"                projective_model_atlas(r), " +
			"                k, " +
			"                manifold_form_pullback⟨n + 2 * (r - 1), n + 2 * (r - 1)⟩( " +
			"                    product_topology(subtopology(T, U), projective_model_topology(r)), " +
			"                    smooth_product_atlas⟨n, 2 * (r - 1)⟩(open_submanifold_atlas⟨n⟩(T, 𝒜, U), " +
			"                        projective_model_atlas(r)), " +
			"                    projective_topology(T, P), " +
			"                    projective_atlas(n, r, T, 𝒜, P), " +
			"                    k + 2 * (r - 1), " +
			"                    projective_frame_map(r, F), " +
			"                    ω)))",
	},
})}

var fiberClassDef = fiberClassDefThm{family.Define(registry.DefEntry{
	Name:  "fiberClassDef",
	Key:   "prop_45683c5e0caca6bb",
	Deps:  []registry.EntryLike{fiberIntegralDef},
	Const: "projective_fiber_class",
	Type: "num → " +
		"num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"prod(num, A → num → num → complex) → " +
		"num → " +
		"set(prod(set(prod(A, num → num → complex)), prod(A, num → num → complex) → num → real) → " +
		"    (num → real) → " +
		"    (num → num → real) → " +
		"    real) → " +
		"set(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real)",
	Equations: []string{
		"∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀r:num. " +
			"∀P:prod(num, A → num → num → complex). " +
			"∀k:num. " +
			"∀a:set(prod(set(prod(A, num → num → complex)), prod(A, num → num → complex) → num → real) → " +
			"        (num → real) → " +
			"        (num → num → real) → " +
			"        real). " +
			"    projective_fiber_class(n, r, T, 𝒜, P, k, a) = " +
			"    induced_map(λω:(prod(set(prod(A, num → num → complex)), " +
			"                    prod(A, num → num → complex) → num → real) → " +
			"                (num → real) → " +
			"                (num → num → real) → " +
			"                real). " +
			"            de_rham_class⟨n⟩(T, 𝒜, k, projective_fiber_integral(n, r, T, 𝒜, P, k, ω)), " +
			"        a)",
	},
})}

var hyperplanePowerDef = hyperplanePowerDefThm{family.Define(registry.DefEntry{
	Name:  "hyperplanePowerDef",
	Key:   "prop_d49a377bad7f3248",
	Deps:  []registry.EntryLike{topologyDef, atlasDef, TautologicalDef},
	Const: "projective_hyperplane_power",
	Type: "num → " +
		"num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"prod(num, A → num → num → complex) → " +
		"num → " +
		"prod(set(prod(A, num → num → complex)), prod(A, num → num → complex) → num → real) → " +
		"(num → real) → " +
		"(num → num → real) → " +
		"real",
	Equations: []string{
		"∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀r:num. " +
			"∀P:prod(num, A → num → num → complex). " +
			"    projective_hyperplane_power(n, r, T, 𝒜, P, 0) = " +
			"    manifold_form_unit⟨n + 2 * (r - 1)⟩(projective_topology(T, P), " +
			"        projective_atlas(n, r, T, 𝒜, P))",
		"∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀r:num. " +
			"∀P:prod(num, A → num → num → complex). " +
			"∀k:num. " +
			"    projective_hyperplane_power(n, r, T, 𝒜, P, suc(k)) = " +
			"    manifold_form_wedge⟨n + 2 * (r - 1)⟩(projective_topology(T, P), " +
			"        projective_atlas(n, r, T, 𝒜, P), " +
			"        2 * k, " +
			"        2, " +
			"        projective_hyperplane_power(n, r, T, 𝒜, P, k), " +
			"        (λc:prod(set(prod(A, num → num → complex)), prod(A, num → num → complex) → num → real). " +
			"        λy:(num → real). " +
			"        λV:(num → num → real). " +
			"            -chern_form(n + 2 * (r - 1), " +
			"                projective_topology(T, P), " +
			"                projective_atlas(n, r, T, 𝒜, P), " +
			"                projective_tautological(T, P), " +
			"                (λi:num. " +
			"                λj:num. " +
			"                λc:prod(set(prod(A, num → num → complex)), " +
			"                        prod(A, num → num → complex) → num → real). " +
			"                λy:(num → real). " +
			"                λV:(num → num → real). " +
			"                    complex_of_real(&0)), " +
			"                1, " +
			"                c, " +
			"                y, " +
			"                V)))",
	},
})}

var compactFiberClassDef = compactFiberClassDefThm{family.Define(registry.DefEntry{
	Name:  "compactFiberClassDef",
	Key:   "prop_c9ac7f1883844d8e",
	Deps:  []registry.EntryLike{fiberIntegralDef},
	Const: "projective_compact_fiber_class",
	Type: "num → " +
		"num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"prod(num, A → num → num → complex) → " +
		"num → " +
		"set(prod(set(prod(A, num → num → complex)), prod(A, num → num → complex) → num → real) → " +
		"    (num → real) → " +
		"    (num → num → real) → " +
		"    real) → " +
		"set(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real)",
	Equations: []string{
		"∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀r:num. " +
			"∀P:prod(num, A → num → num → complex). " +
			"∀k:num. " +
			"∀a:set(prod(set(prod(A, num → num → complex)), prod(A, num → num → complex) → num → real) → " +
			"        (num → real) → " +
			"        (num → num → real) → " +
			"        real). " +
			"    projective_compact_fiber_class(n, r, T, 𝒜, P, k, a) = " +
			"    induced_map(λω:(prod(set(prod(A, num → num → complex)), " +
			"                    prod(A, num → num → complex) → num → real) → " +
			"                (num → real) → " +
			"                (num → num → real) → " +
			"                real). " +
			"            compact_de_rham_class(n, T, 𝒜, k, projective_fiber_integral(n, r, T, 𝒜, P, k, ω)), " +
			"        a)",
	},
})}
