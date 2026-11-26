package torus_manifold

import (
	"github.com/euc-ai/xugo/library/registry"
)

var CarrierDef = carrierDefThm{family.Define(registry.DefEntry{
	Name:  "CarrierDef",
	Key:   "prop_35be7c1552b38855",
	Const: "smooth_torus_carrier",
	Type:  "num → set(num → complex)",
	Equations: []string{
		"∀n:num. " +
			"    smooth_torus_carrier(n) = " +
			"    {z:(num → complex) | " +
			"        (∀j:num. j < n ⇒ |z(j)| = &1) ∧ (∀j:num. n ≤ j ⇒ z(j) = complex_of_real(&0))}",
	},
})}

var TopologyDef = topologyDefThm{family.Define(registry.DefEntry{
	Name:  "TopologyDef",
	Key:   "prop_3529b0d591188afb",
	Deps:  []registry.EntryLike{CarrierDef},
	Const: "smooth_torus_topology",
	Type:  "num → set(set(num → complex))",
	Equations: []string{
		"∀n:num. " +
			"    smooth_torus_topology(n) = " +
			"    subtopology(complex_coordinate_topology(n), smooth_torus_carrier(n))",
	},
})}

var chartDef = chartDefThm{family.Define(registry.DefEntry{
	Name:  "chartDef",
	Key:   "prop_57311ea59ca64a9",
	Deps:  []registry.EntryLike{CarrierDef},
	Const: "smooth_torus_chart",
	Type:  "num → (num → complex) → prod(set(num → complex), (num → complex) → num → real)",
	Equations: []string{
		"∀n:num. ∀c:(num → complex). " +
			"    smooth_torus_chart(n, c) = " +
			"    ({z:(num → complex) | z ∈ smooth_torus_carrier(n) ∧ (∀j:num. j < n ⇒ z(j) ≠ -c(j))}, " +
			"        λz:(num → complex). λj:num. " +
			"            COND(z ∈ smooth_torus_carrier(n) ∧ (∀i:num. i < n ⇒ z(i) ≠ -c(i)) ∧ j < n, " +
			"                im(complex_conj(c(j)) * z(j)) / (&1 + re(complex_conj(c(j)) * z(j))), " +
			"                &0))",
	},
})}

var AtlasDef = atlasDefThm{family.Define(registry.DefEntry{
	Name:  "AtlasDef",
	Key:   "prop_1b42a78e12120aae",
	Deps:  []registry.EntryLike{CarrierDef, chartDef},
	Const: "smooth_torus_atlas",
	Type:  "num → set(prod(set(num → complex), (num → complex) → num → real))",
	Equations: []string{
		"∀n:num. smooth_torus_atlas(n) = image(smooth_torus_chart(n), smooth_torus_carrier(n))",
	},
})}

var cubeMapDef = cubeMapDefThm{family.Define(registry.DefEntry{
	Name:  "cubeMapDef",
	Key:   "prop_68ba2565bb4c8f2c",
	Const: "torus_cube_map",
	Type:  "num → (num → real) → num → real",
	Equations: []string{
		"∀n:num. ∀x:(num → real). ∀j:num. " +
			"    torus_cube_map(n, x, j) = " +
			"    COND(j < n, (pi / &2) * x(j) / real_sqrt(&1 + real_pow(x(j), 2)), &0)",
	},
})}

var EuclideanMapDef = euclideanMapDefThm{family.Define(registry.DefEntry{
	Name:  "EuclideanMapDef",
	Key:   "prop_a72559c27ae92470",
	Deps:  []registry.EntryLike{cubeMapDef},
	Const: "torus_euclidean_map",
	Type:  "num → (num → real) → num → complex",
	Equations: []string{
		"∀n:num. ∀x:(num → real). ∀j:num. " +
			"    torus_euclidean_map(n, x, j) = " +
			"    COND(j < n, " +
			"        complex_exp(complex_i * complex_of_real(torus_cube_map(n, x, j))), " +
			"        complex_of_real(&0))",
	},
})}
