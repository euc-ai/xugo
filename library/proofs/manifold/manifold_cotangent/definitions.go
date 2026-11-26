package manifold_cotangent

import (
	"github.com/euc-ai/xugo/library/registry"
)

var CovectorDef = covectorDefThm{family.Define(registry.DefEntry{
	Name:  "CovectorDef",
	Key:   "prop_8e5c3c5f33a4d88b",
	Const: "cotangent_covector",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"A → " +
		"(prod(set(A), A → num → real) → num → real) → " +
		"bool",
	Equations: []string{
		"∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀x:A. " +
			"∀ξ:(prod(set(A), A → num → real) → num → real). " +
			"    cotangent_covector(n, T, 𝒜, x, ξ) ⇔ " +
			"    smooth_manifold⟨n⟩(T, 𝒜) ∧ " +
			"    x ∈ ⋃T ∧ " +
			"    (∀c:prod(set(A), A → num → real). vec⟨n⟩(&0, ξ(c))) ∧ " +
			"    (∀c:prod(set(A), A → num → real). " +
			"        ¬(compatible_chart⟨n⟩(T, 𝒜, c) ∧ x ∈ fst(c)) ⇒ ξ(c) = (λi:num. &0)) ∧ " +
			"    (∀c d:prod(set(A), A → num → real). ∀v:(prod(set(A), A → num → real) → num → real). " +
			"        compatible_chart⟨n⟩(T, 𝒜, c) ∧ " +
			"        x ∈ fst(c) ∧ " +
			"        compatible_chart⟨n⟩(T, 𝒜, d) ∧ " +
			"        x ∈ fst(d) ∧ " +
			"        tangent_vector_on⟨n⟩(T, 𝒜, x, v) ⇒ " +
			"        real_sum({i:num | i < n}, λi:num. ξ(c, i) * v(c, i)) = " +
			"        real_sum({i:num | i < n}, λi:num. ξ(d, i) * v(d, i)))",
	},
})}

var BundleDef = bundleDefThm{family.Define(registry.DefEntry{
	Name:  "BundleDef",
	Key:   "prop_66df62205fc1f9db",
	Deps:  []registry.EntryLike{CovectorDef},
	Const: "cotangent_bundle",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"set(prod(A, prod(set(A), A → num → real) → num → real))",
	Equations: []string{
		"∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). " +
			"    cotangent_bundle(n, T, 𝒜) = " +
			"    {p:prod(A, prod(set(A), A → num → real) → num → real) | " +
			"        cotangent_covector(n, T, 𝒜, fst(p), snd(p))}",
	},
})}

var FromChartDef = fromChartDefThm{family.Define(registry.DefEntry{
	Name:  "FromChartDef",
	Key:   "prop_68d0fa5aea26cd34",
	Const: "cotangent_from_chart",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"prod(set(A), A → num → real) → " +
		"A → " +
		"(num → real) → " +
		"prod(set(A), A → num → real) → " +
		"num → " +
		"real",
	Equations: []string{
		"∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀c:prod(set(A), A → num → real). " +
			"∀x:A. " +
			"∀u:(num → real). " +
			"∀d:prod(set(A), A → num → real). " +
			"∀i:num. " +
			"    cotangent_from_chart(n, T, 𝒜, c, x, u, d, i) = " +
			"    COND(compatible_chart⟨n⟩(T, 𝒜, c) ∧ " +
			"        x ∈ fst(c) ∧ " +
			"        compatible_chart⟨n⟩(T, 𝒜, d) ∧ " +
			"        x ∈ fst(d) ∧ " +
			"        vec⟨n⟩(&0, u) ∧ " +
			"        i < n, " +
			"        real_sum({j:num | j < n}, " +
			"            λj:num. " +
			"                vec_jacobian_matrix⟨n, n⟩(snd(c) ∘ inverse_on(fst(d), snd(d)), " +
			"                    snd(d)(x), " +
			"                    j, " +
			"                    i) * " +
			"                u(j)), " +
			"        &0)",
	},
})}

var chartDef = chartDefThm{family.Define(registry.DefEntry{
	Name:  "chartDef",
	Key:   "prop_d1cb7d7683f0377a",
	Deps:  []registry.EntryLike{BundleDef},
	Const: "cotangent_chart",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"prod(set(A), A → num → real) → " +
		"prod(set(prod(A, prod(set(A), A → num → real) → num → real)), " +
		"    prod(A, prod(set(A), A → num → real) → num → real) → num → real)",
	Equations: []string{
		"∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). ∀c:prod(set(A), A → num → real). " +
			"    cotangent_chart(n, T, 𝒜, c) = " +
			"    ({p:prod(A, prod(set(A), A → num → real) → num → real) | " +
			"            p ∈ cotangent_bundle(n, T, 𝒜) ∧ fst(p) ∈ fst(c)}, " +
			"        λp:prod(A, prod(set(A), A → num → real) → num → real). λi:num. " +
			"            COND(i < n, snd(c)(fst(p), i), COND(i < 2 * n, snd(p)(c, i - n), &0)))",
	},
})}

var AtlasDef = atlasDefThm{family.Define(registry.DefEntry{
	Name:  "AtlasDef",
	Key:   "prop_932781b4005fd3ae",
	Deps:  []registry.EntryLike{chartDef},
	Const: "cotangent_atlas",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"set(prod(set(prod(A, prod(set(A), A → num → real) → num → real)), " +
		"        prod(A, prod(set(A), A → num → real) → num → real) → num → real))",
	Equations: []string{
		"∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). " +
			"    cotangent_atlas(n, T, 𝒜) = " +
			"    image(cotangent_chart(n, T, 𝒜), " +
			"        {c:prod(set(A), A → num → real) | compatible_chart⟨n⟩(T, 𝒜, c)})",
	},
})}

var TopologyDef = topologyDefThm{family.Define(registry.DefEntry{
	Name:  "TopologyDef",
	Key:   "prop_95b8e4b39c690724",
	Deps:  []registry.EntryLike{BundleDef, chartDef},
	Const: "cotangent_topology",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"set(set(prod(A, prod(set(A), A → num → real) → num → real)))",
	Equations: []string{
		"∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). " +
			"    cotangent_topology(n, T, 𝒜) = " +
			"    {W:set(prod(A, prod(set(A), A → num → real) → num → real)) | " +
			"        W ⊆ cotangent_bundle(n, T, 𝒜) ∧ " +
			"        (∀c:prod(set(A), A → num → real). " +
			"            compatible_chart⟨n⟩(T, 𝒜, c) ⇒ " +
			"            image(snd(cotangent_chart(n, T, 𝒜, c)), W ∩ fst(cotangent_chart(n, T, 𝒜, c))) ∈ " +
			"            euclidean_topology(2 * n))}",
	},
})}

var MetricFlatDef = metricFlatDefThm{family.Define(registry.DefEntry{
	Name:  "MetricFlatDef",
	Key:   "prop_2f61ff77edf71681",
	Const: "cotangent_metric_flat",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"(prod(set(A), A → num → real) → (num → real) → num → num → real) → " +
		"prod(A, prod(set(A), A → num → real) → num → real) → " +
		"prod(A, prod(set(A), A → num → real) → num → real)",
	Equations: []string{
		"∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀g:(prod(set(A), A → num → real) → (num → real) → num → num → real). " +
			"∀p:prod(A, prod(set(A), A → num → real) → num → real). " +
			"    cotangent_metric_flat(n, T, 𝒜, g, p) = " +
			"    (fst(p), " +
			"        λc:prod(set(A), A → num → real). λi:num. " +
			"            COND(p ∈ tangent_bundle⟨n⟩(T, 𝒜) ∧ " +
			"                compatible_chart⟨n⟩(T, 𝒜, c) ∧ " +
			"                fst(p) ∈ fst(c) ∧ " +
			"                i < n, " +
			"                real_sum({j:num | j < n}, λj:num. g(c, snd(c)(fst(p)), i, j) * snd(p)(c, j)), " +
			"                &0))",
	},
})}

var ScaleDef = scaleDefThm{family.Define(registry.DefEntry{
	Name:  "ScaleDef",
	Key:   "prop_adc53b6f542c665a",
	Const: "cotangent_scale",
	Type: "real → " +
		"prod(A, prod(set(A), A → num → real) → num → real) → " +
		"prod(A, prod(set(A), A → num → real) → num → real)",
	Equations: []string{
		"∀t:real. ∀p:prod(A, prod(set(A), A → num → real) → num → real). " +
			"    cotangent_scale(t, p) = (fst(p), λc:prod(set(A), A → num → real). λi:num. t * snd(p)(c, i))",
	},
})}
