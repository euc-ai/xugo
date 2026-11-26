package sobolev_section

import "github.com/euc-ai/xugo/library/registry"

var sectionClassDef = sectionClassDefThm{family.Define(registry.DefEntry{
	Name:  "sectionClassDef",
	Key:   "prop_ff20396cdf08f32b",
	Const: "projected_section_class",
	Type: "num → " +
		"num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"(A → num → num → complex) → " +
		"num → " +
		"(A → num → complex) → " +
		"bool",
	Equations: []string{
		"∀n r:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀P:(A → num → num → complex). " +
			"∀k:num. " +
			"∀f:(A → num → complex). " +
			"    projected_section_class(n, r, T, 𝒜, P, k, f) ⇔ " +
			"    smooth_manifold⟨n⟩(T, 𝒜) ∧ " +
			"    (∀x:A. ∀j:num. x ∉ ⋃T ∨ r ≤ j ⇒ f(x, j) = complex_of_real(&0)) ∧ " +
			"    (∀x:A. ∀j:num. " +
			"        x ∈ ⋃T ∧ j < r ⇒ " +
			"        module_sum(complex_add, " +
			"            complex_of_real(&0), " +
			"            {l:num | l < r}, " +
			"            λl:num. P(x, j, l) * f(x, l)) = " +
			"        f(x, j)) ∧ " +
			"    (∀c:prod(set(A), A → num → real). ∀j:num. " +
			"        compatible_chart⟨n⟩(T, 𝒜, c) ∧ j < r ⇒ " +
			"        vec_continuously_differentiable_on⟨n⟩(image(snd(c), fst(c)), " +
			"            k, " +
			"            λy:(num → real). re(f(inverse_on(fst(c), snd(c), y), j))) ∧ " +
			"        vec_continuously_differentiable_on⟨n⟩(image(snd(c), fst(c)), " +
			"            k, " +
			"            λy:(num → real). im(f(inverse_on(fst(c), snd(c), y), j))))",
	},
})}

var SmoothSectionDef = smoothSectionDefThm{family.Define(registry.DefEntry{
	Name:  "SmoothSectionDef",
	Key:   "prop_97c741d8ed56223d",
	Const: "smooth_projected_section",
	Type: "num → " +
		"num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"(A → num → num → complex) → " +
		"(A → num → complex) → " +
		"bool",
	Deps: []registry.EntryLike{sectionClassDef},
	Equations: []string{
		"∀n r:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀P:(A → num → num → complex). " +
			"∀f:(A → num → complex). " +
			"    smooth_projected_section(n, r, T, 𝒜, P, f) ⇔ " +
			"    ∀k:num. projected_section_class(n, r, T, 𝒜, P, k, f)",
	},
})}

var LocalizationDataDef = localizationDataDefThm{family.Define(registry.DefEntry{
	Name:  "LocalizationDataDef",
	Key:   "prop_adb0a725b48b80a",
	Const: "sobolev_localization_on",
	Type:  "num → set(set(A)) → set(prod(set(A), A → num → real)) → sobolev_localization(A) → bool",
	Deps: []registry.EntryLike{
		SobolevLocalizationData.Fields[0],
		SobolevLocalizationData.Fields[1],
		SobolevLocalizationData.Fields[2],
	},
	Equations: []string{
		"∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). ∀D:sobolev_localization(A). " +
			"    sobolev_localization_on(n, T, 𝒜, D) ⇔ " +
			"    smooth_manifold⟨n⟩(T, 𝒜) ∧ " +
			"    compact_in(T, ⋃T) ∧ " +
			"    (∀i:num. " +
			"        i < D.count ⇒ " +
			"        compatible_chart⟨n⟩(T, 𝒜, D.charts(i)) ∧ " +
			"        image(snd(D.charts(i)), fst(D.charts(i))) ⊆ torus_small_box(n) ∧ " +
			"        smooth_manifold_function⟨n⟩(T, 𝒜, D.partition(i)) ∧ " +
			"        (∀x:A. &0 ≤ D.partition(i, x)) ∧ " +
			"        compact_in(T, function_support(T, &0, D.partition(i))) ∧ " +
			"        function_support(T, &0, D.partition(i)) ⊆ fst(D.charts(i))) ∧ " +
			"    (∀i:num. D.count ≤ i ⇒ D.partition(i) = (λx:A. &0)) ∧ " +
			"    (∀x:A. x ∈ ⋃T ⇒ real_sum({i:num | i < D.count}, λi:num. D.partition(i, x)) = &1)",
	},
})}

var localizationIndicesDef = localizationIndicesDefThm{family.Define(registry.DefEntry{
	Name:  "localizationIndicesDef",
	Key:   "prop_392816b027e8cc32",
	Const: "localization_indices",
	Type:  "num → num → num → set(prod(num, prod(num, num → int)))",
	Equations: []string{
		"∀n r N:num. " +
			"    localization_indices(n, r, N) = " +
			"    {z:prod(num, prod(num, num → int)) | " +
			"        fst(z) < N ∧ fst(snd(z)) < r ∧ snd(snd(z)) ∈ fourier_lattice(n)}",
	},
})}

var localizationModuleDef = localizationModuleDefThm{family.Define(registry.DefEntry{
	Name:  "localizationModuleDef",
	Key:   "prop_45e88cc7f2494cea",
	Const: "localization_sequence_module",
	Type:  "num → num → num → int → module_ops(complex, prod(num, prod(num, num → int)) → complex)",
	Deps:  []registry.EntryLike{localizationIndicesDef},
	Equations: []string{
		"∀n r N:num. ∀s:int. " +
			"    localization_sequence_module(n, r, N, s) = " +
			"    weighted_sequence_module(localization_indices(n, r, N), " +
			"        λz:prod(num, prod(num, num → int)). sobolev_weight(n, s, snd(snd(z))))",
	},
})}

var LocalizationInnerDef = localizationInnerDefThm{family.Define(registry.DefEntry{
	Name:  "LocalizationInnerDef",
	Key:   "prop_f7baea455152f2e5",
	Const: "localization_sequence_inner",
	Type: "num → " +
		"num → " +
		"num → " +
		"int → " +
		"(prod(num, prod(num, num → int)) → complex) → " +
		"(prod(num, prod(num, num → int)) → complex) → " +
		"complex",
	Deps: []registry.EntryLike{localizationIndicesDef},
	Equations: []string{
		"∀n r N:num. ∀s:int. " +
			"    localization_sequence_inner(n, r, N, s) = " +
			"    weighted_sequence_inner(localization_indices(n, r, N), " +
			"        λz:prod(num, prod(num, num → int)). sobolev_weight(n, s, snd(snd(z))))",
	},
})}

var LocalizationNormDef = localizationNormDefThm{family.Define(registry.DefEntry{
	Name:  "LocalizationNormDef",
	Key:   "prop_ccfad230d4d1ad70",
	Const: "localization_sequence_norm",
	Type:  "num → num → num → int → (prod(num, prod(num, num → int)) → complex) → real",
	Deps:  []registry.EntryLike{LocalizationInnerDef},
	Equations: []string{
		"∀n r N:num. ∀s:int. " +
			"    localization_sequence_norm(n, r, N, s) = " +
			"    hilbert_norm(localization_sequence_inner(n, r, N, s))",
	},
})}

var LocalizeSectionDef = localizeSectionDefThm{family.Define(registry.DefEntry{
	Name:  "LocalizeSectionDef",
	Key:   "prop_6328f74b34dc7ae4",
	Const: "localize_section",
	Type: "num → " +
		"num → " +
		"sobolev_localization(A) → " +
		"(A → num → complex) → " +
		"prod(num, prod(num, num → int)) → " +
		"complex",
	Deps: []registry.EntryLike{
		SobolevLocalizationData.Fields[0],
		SobolevLocalizationData.Fields[1],
		SobolevLocalizationData.Fields[2],
	},
	Equations: []string{
		"∀n r:num. " +
			"∀D:sobolev_localization(A). " +
			"∀f:(A → num → complex). " +
			"∀z:prod(num, prod(num, num → int)). " +
			"    localize_section(n, r, D, f, z) = " +
			"    COND(fst(z) < D.count ∧ fst(snd(z)) < r, " +
			"        torus_coefficients(n, " +
			"            torus_periodize(n, " +
			"                λy:(num → real). " +
			"                    COND(y ∈ image(snd(D.charts(fst(z))), fst(D.charts(fst(z)))), " +
			"                        complex_of_real(D.partition(fst(z), " +
			"                                inverse_on(fst(D.charts(fst(z))), snd(D.charts(fst(z))), y))) * " +
			"                        f(inverse_on(fst(D.charts(fst(z))), snd(D.charts(fst(z))), y), " +
			"                            fst(snd(z))), " +
			"                        complex_of_real(&0))), " +
			"            snd(snd(z))), " +
			"        complex_of_real(&0))",
	},
})}

var SectionSobolevModuleDef = sectionSobolevModuleDefThm{family.Define(registry.DefEntry{
	Name:  "SectionSobolevModuleDef",
	Key:   "prop_c4db78b2d4741e5a",
	Const: "section_sobolev_module",
	Type: "num → " +
		"num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"(A → num → num → complex) → " +
		"sobolev_localization(A) → " +
		"int → " +
		"module_ops(complex, prod(num, prod(num, num → int)) → complex)",
	Deps: []registry.EntryLike{
		localizationModuleDef,
		LocalizationNormDef,
		LocalizeSectionDef,
		SmoothSectionDef,
		SobolevLocalizationData.Fields[0],
		SobolevLocalizationData.Fields[1],
		SobolevLocalizationData.Fields[2],
	},
	Equations: []string{
		"∀n r:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀P:(A → num → num → complex). " +
			"∀D:sobolev_localization(A). " +
			"∀s:int. " +
			"    section_sobolev_module(n, r, T, 𝒜, P, D, s) = " +
			"    restrict_module(localization_sequence_module(n, r, D.count, s), " +
			"        closure(norm_topology(localization_sequence_module(n, r, D.count, s), " +
			"                localization_sequence_norm(n, r, D.count, s)), " +
			"            image(localize_section(n, r, D), " +
			"                {f:(A → num → complex) | smooth_projected_section(n, r, T, 𝒜, P, f)})))",
	},
})}

var sectionChangeDef = sectionChangeDefThm{family.Define(registry.DefEntry{
	Name:  "sectionChangeDef",
	Key:   "prop_cdcd7faa79201136",
	Const: "section_coordinate_change",
	Type: "num → " +
		"num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"(A → num → num → complex) → " +
		"sobolev_localization(A) → " +
		"sobolev_localization(A) → " +
		"int → " +
		"(prod(num, prod(num, num → int)) → complex) → " +
		"(prod(num, prod(num, num → int)) → complex)",
	Deps: []registry.EntryLike{
		SectionSobolevModuleDef,
		LocalizeSectionDef,
		SmoothSectionDef,
		LocalizationNormDef,
		SobolevLocalizationData.Fields[0],
		SobolevLocalizationData.Fields[1],
		SobolevLocalizationData.Fields[2],
	},
	Equations: []string{
		"∀n r:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀P:(A → num → num → complex). " +
			"∀D:sobolev_localization(A). " +
			"∀s:int. " +
			"∀E:sobolev_localization(A). " +
			"    section_coordinate_change(n, r, T, 𝒜, P, D, E, s) = " +
			"    εL:((prod(num, prod(num, num → int)) → complex) → " +
			"            prod(num, prod(num, num → int)) → " +
			"            complex). " +
			"        L ∈ " +
			"        (operator_module(section_sobolev_module(n, r, T, 𝒜, P, D, s), " +
			"                localization_sequence_norm(n, r, D.count, s), " +
			"                section_sobolev_module(n, r, T, 𝒜, P, E, s), " +
			"                localization_sequence_norm(n, r, E.count, s))).carrier ∧ " +
			"        ∀f:(A → num → complex). " +
			"            smooth_projected_section(n, r, T, 𝒜, P, f) ⇒ " +
			"            L(localize_section(n, r, D, f)) = localize_section(n, r, E, f)",
	},
})}

var sectionMultiplyDef = sectionMultiplyDefThm{family.Define(registry.DefEntry{
	Name:  "sectionMultiplyDef",
	Key:   "prop_89acd002a6503351",
	Const: "section_sobolev_multiply",
	Type: "num → " +
		"num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"(A → num → num → complex) → " +
		"sobolev_localization(A) → " +
		"int → " +
		"(A → complex) → " +
		"(prod(num, prod(num, num → int)) → complex) → " +
		"(prod(num, prod(num, num → int)) → complex)",
	Deps: []registry.EntryLike{
		SectionSobolevModuleDef,
		LocalizationNormDef,
		SmoothSectionDef,
		LocalizeSectionDef,
		SobolevLocalizationData.Fields[0],
		SobolevLocalizationData.Fields[1],
		SobolevLocalizationData.Fields[2],
	},
	Equations: []string{
		"∀n r:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀P:(A → num → num → complex). " +
			"∀D:sobolev_localization(A). " +
			"∀s:int. " +
			"∀a:(A → complex). " +
			"    section_sobolev_multiply(n, r, T, 𝒜, P, D, s, a) = " +
			"    εL:((prod(num, prod(num, num → int)) → complex) → " +
			"            prod(num, prod(num, num → int)) → " +
			"            complex). " +
			"        L ∈ " +
			"        (operator_module(section_sobolev_module(n, r, T, 𝒜, P, D, s), " +
			"                localization_sequence_norm(n, r, D.count, s), " +
			"                section_sobolev_module(n, r, T, 𝒜, P, D, s), " +
			"                localization_sequence_norm(n, r, D.count, s))).carrier ∧ " +
			"        ∀f:(A → num → complex). " +
			"            smooth_projected_section(n, r, T, 𝒜, P, f) ⇒ " +
			"            L(localize_section(n, r, D, f)) = " +
			"            localize_section(n, r, D, λx:A. λj:num. a(x) * f(x, j))",
	},
})}

var sectionMatrixActionDef = sectionMatrixActionDefThm{family.Define(registry.DefEntry{
	Name:  "sectionMatrixActionDef",
	Key:   "prop_a1485b9b741e7c36",
	Const: "section_matrix_action",
	Type:  "num → num → (A → num → num → complex) → (A → num → complex) → A → num → complex",
	Equations: []string{
		"∀r t:num. ∀B:(A → num → num → complex). ∀f:(A → num → complex). ∀x:A. ∀i:num. " +
			"    section_matrix_action(r, t, B, f, x, i) = " +
			"    COND(i < t, " +
			"        module_sum(complex_add, " +
			"            complex_of_real(&0), " +
			"            {j:num | j < r}, " +
			"            λj:num. B(x, i, j) * f(x, j)), " +
			"        complex_of_real(&0))",
	},
})}

var componentSmoothDef = componentSmoothDefThm{family.Define(registry.DefEntry{
	Name:  "componentSmoothDef",
	Key:   "prop_9121a9a1bee5b246",
	Const: "torus_component_smooth",
	Type:  "num → num → ((num → real) → num → complex) → bool",
	Equations: []string{
		"∀n r:num. ∀f:((num → real) → num → complex). " +
			"    torus_component_smooth(n, r, f) ⇔ " +
			"    (∀j:num. j < r ⇒ torus_smooth(n, λx:(num → real). f(x, j))) ∧ " +
			"    (∀j:num. r ≤ j ⇒ ∀x:(num → real). f(x, j) = complex_of_real(&0))",
	},
})}

var componentCodeDef = componentCodeDefThm{family.Define(registry.DefEntry{
	Name:  "componentCodeDef",
	Key:   "prop_6c85cc3b29a91b04",
	Const: "torus_component_code",
	Type:  "num → num → ((num → real) → num → complex) → prod(num, prod(num, num → int)) → complex",
	Equations: []string{
		"∀n r:num. ∀f:((num → real) → num → complex). ∀z:prod(num, prod(num, num → int)). " +
			"    torus_component_code(n, r, f, z) = " +
			"    COND(fst(z) = 0 ∧ fst(snd(z)) < r, " +
			"        torus_coefficients(n, λx:(num → real). f(x, fst(snd(z))), snd(snd(z))), " +
			"        complex_of_real(&0))",
	},
})}

var chartExtensionSeedDef = chartExtensionSeedDefThm{family.Define(registry.DefEntry{
	Name:  "chartExtensionSeedDef",
	Key:   "prop_6f363adddf2cd413",
	Const: "chart_extension_seed",
	Type: "num → " +
		"(A → num → num → complex) → " +
		"prod(set(A), A → num → real) → " +
		"(A → real) → " +
		"((num → real) → num → complex) → " +
		"A → " +
		"num → " +
		"complex",
	Equations: []string{
		"∀r:num. " +
			"∀P:(A → num → num → complex). " +
			"∀c:prod(set(A), A → num → real). " +
			"∀χ:(A → real). " +
			"∀f:((num → real) → num → complex). " +
			"∀x:A. " +
			"∀j:num. " +
			"    chart_extension_seed(r, P, c, χ, f, x, j) = " +
			"    COND(x ∈ fst(c) ∧ j < r, " +
			"        complex_of_real(χ(x)) * " +
			"        module_sum(complex_add, " +
			"            complex_of_real(&0), " +
			"            {l:num | l < r}, " +
			"            λl:num. P(x, j, l) * f(snd(c)(x), l)), " +
			"        complex_of_real(&0))",
	},
})}

var chartExtensionDef = chartExtensionDefThm{family.Define(registry.DefEntry{
	Name:  "chartExtensionDef",
	Key:   "prop_10e4b6f8009a0d2e",
	Const: "section_chart_extension",
	Type: "num → " +
		"num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"(A → num → num → complex) → " +
		"sobolev_localization(A) → " +
		"int → " +
		"prod(set(A), A → num → real) → " +
		"(A → real) → " +
		"(prod(num, prod(num, num → int)) → complex) → " +
		"(prod(num, prod(num, num → int)) → complex)",
	Deps: []registry.EntryLike{
		componentSmoothDef,
		componentCodeDef,
		chartExtensionSeedDef,
		SectionSobolevModuleDef,
		LocalizationNormDef,
		LocalizeSectionDef,
		SobolevLocalizationData.Fields[0],
		SobolevLocalizationData.Fields[1],
		SobolevLocalizationData.Fields[2],
	},
	Equations: []string{
		"∀n r:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀P:(A → num → num → complex). " +
			"∀D:sobolev_localization(A). " +
			"∀s:int. " +
			"∀c:prod(set(A), A → num → real). " +
			"∀χ:(A → real). " +
			"    section_chart_extension(n, r, T, 𝒜, P, D, s, c, χ) = " +
			"    εL:((prod(num, prod(num, num → int)) → complex) → " +
			"            prod(num, prod(num, num → int)) → " +
			"            complex). " +
			"        L ∈ " +
			"        (operator_module(localization_sequence_module(n, r, 1, s), " +
			"                localization_sequence_norm(n, r, 1, s), " +
			"                section_sobolev_module(n, r, T, 𝒜, P, D, s), " +
			"                localization_sequence_norm(n, r, D.count, s))).carrier ∧ " +
			"        ∀f:((num → real) → num → complex). " +
			"            torus_component_smooth(n, r, f) ⇒ " +
			"            L(torus_component_code(n, r, f)) = " +
			"            localize_section(n, r, D, chart_extension_seed(r, P, c, χ, f))",
	},
})}

var chartRestrictionDef = chartRestrictionDefThm{family.Define(registry.DefEntry{
	Name:  "chartRestrictionDef",
	Key:   "prop_359e1e3bbce817b2",
	Const: "section_chart_restriction",
	Type: "num → " +
		"num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"(A → num → num → complex) → " +
		"sobolev_localization(A) → " +
		"int → " +
		"prod(set(A), A → num → real) → " +
		"(A → real) → " +
		"(prod(num, prod(num, num → int)) → complex) → " +
		"(prod(num, prod(num, num → int)) → complex)",
	Deps: []registry.EntryLike{
		SectionSobolevModuleDef,
		LocalizationNormDef,
		LocalizeSectionDef,
		SmoothSectionDef,
		SobolevLocalizationData.Fields[0],
		SobolevLocalizationData.Fields[1],
		SobolevLocalizationData.Fields[2],
	},
	Equations: []string{
		"∀n r:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀P:(A → num → num → complex). " +
			"∀D:sobolev_localization(A). " +
			"∀s:int. " +
			"∀c:prod(set(A), A → num → real). " +
			"∀χ:(A → real). " +
			"    section_chart_restriction(n, r, T, 𝒜, P, D, s, c, χ) = " +
			"    εL:((prod(num, prod(num, num → int)) → complex) → " +
			"            prod(num, prod(num, num → int)) → " +
			"            complex). " +
			"        L ∈ " +
			"        (operator_module(section_sobolev_module(n, r, T, 𝒜, P, D, s), " +
			"                localization_sequence_norm(n, r, D.count, s), " +
			"                localization_sequence_module(n, r, 1, s), " +
			"                localization_sequence_norm(n, r, 1, s))).carrier ∧ " +
			"        ∀f:(A → num → complex). " +
			"            smooth_projected_section(n, r, T, 𝒜, P, f) ⇒ " +
			"            L(localize_section(n, r, D, f)) = " +
			"            localize_section(n, r, sobolev_localization_data(1, λi:num. c, λi:num. χ), f)",
	},
})}
