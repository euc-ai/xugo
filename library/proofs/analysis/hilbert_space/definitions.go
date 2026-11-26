package hilbert_space

import "github.com/euc-ai/xugo/library/registry"

var NormedSpace = normedSpaceThm{family.DefineStructure(registry.DefEntry{
	Name: "NormedSpace",
	Reading: "The norm laws constrain only the module carrier. The " +
		"carrier is nonempty because it contains the module zero; the zero " +
		"vector space is allowed, and off-carrier norm values are unrestricted.",
	Key:   "prop_bd19829ed4476589",
	Const: "complex_normed_space",
	Type:  "module_ops(complex, A) → (A → real) → bool",
	Equations: []string{
		"∀M:module_ops(complex, A). ∀v:(A → real). " +
			"    complex_normed_space(M, v) ⇔ " +
			"    module_on(complex_ring, M) ∧ " +
			"    (∀x:A. x ∈ M.carrier ⇒ &0 ≤ v(x) ∧ (v(x) = &0 ⇔ x = M.zero)) ∧ " +
			"    (∀x y:A. x ∈ M.carrier ∧ y ∈ M.carrier ⇒ v(M.add(x, y)) ≤ v(x) + v(y)) ∧ " +
			"    (∀c:complex. ∀x:A. x ∈ M.carrier ⇒ v(M.smul(c, x)) = |c| * v(x))",
	},
})}

var NormDistanceDef = normDistanceDefThm{family.Define(registry.DefEntry{
	Name:  "NormDistanceDef",
	Key:   "prop_7cefb1633df7bd9c",
	Const: "norm_distance",
	Type:  "module_ops(complex, A) → (A → real) → A → A → real",
	Equations: []string{
		"∀M:module_ops(complex, A). ∀v:(A → real). ∀x y:A. " +
			"    norm_distance(M, v, x, y) = v(M.add(x, M.neg(y)))",
	},
})}

var NormTopologyDef = normTopologyDefThm{family.Define(registry.DefEntry{
	Name:  "NormTopologyDef",
	Key:   "prop_e6d3b615cdaeda36",
	Const: "norm_topology",
	Type:  "module_ops(complex, A) → (A → real) → set(set(A))",
	Deps:  []registry.EntryLike{NormDistanceDef},
	Equations: []string{
		"∀M:module_ops(complex, A). ∀v:(A → real). " +
			"    norm_topology(M, v) = metric_topology(M.carrier, norm_distance(M, v))",
	},
})}

var BanachSpace = banachSpaceThm{family.DefineStructure(registry.DefEntry{
	Name:  "BanachSpace",
	Key:   "prop_b226143602eecf7e",
	Const: "complex_banach_space",
	Type:  "module_ops(complex, A) → (A → real) → bool",
	Deps:  []registry.EntryLike{NormedSpace, NormDistanceDef},
	Equations: []string{
		"∀M:module_ops(complex, A). ∀v:(A → real). " +
			"    complex_banach_space(M, v) ⇔ " +
			"    complex_normed_space(M, v) ∧ metric_complete(M.carrier, norm_distance(M, v))",
	},
})}

var InnerProductSpace = innerProductSpaceThm{family.DefineStructure(registry.DefEntry{
	Name:  "InnerProductSpace",
	Key:   "prop_3928da36f0b2414e",
	Const: "complex_inner_space",
	Type:  "module_ops(complex, A) → (A → A → complex) → bool",
	Equations: []string{
		"∀M:module_ops(complex, A). ∀p:(A → A → complex). " +
			"    complex_inner_space(M, p) ⇔ " +
			"    module_on(complex_ring, M) ∧ " +
			"    (∀x y:A. x ∈ M.carrier ∧ y ∈ M.carrier ⇒ p(x, y) = complex_conj(p(y, x))) ∧ " +
			"    (∀x y z:A. " +
			"        x ∈ M.carrier ∧ y ∈ M.carrier ∧ z ∈ M.carrier ⇒ " +
			"        p(M.add(x, y), z) = p(x, z) + p(y, z)) ∧ " +
			"    (∀c:complex. ∀x y:A. x ∈ M.carrier ∧ y ∈ M.carrier ⇒ p(M.smul(c, x), y) = c * p(x, y)) ∧ " +
			"    (∀x:A. x ∈ M.carrier ⇒ &0 ≤ re(p(x, x)) ∧ (p(x, x) = complex_of_real(&0) ⇔ x = M.zero))",
	},
})}

var HilbertNormDef = hilbertNormDefThm{family.Define(registry.DefEntry{
	Name:      "HilbertNormDef",
	Key:       "prop_39d26dee7ab0361",
	Const:     "hilbert_norm",
	Type:      "(A → A → complex) → A → real",
	Equations: []string{"∀p:(A → A → complex). ∀x:A. hilbert_norm(p, x) = real_sqrt(re(p(x, x)))"},
})}

var HilbertSpace = hilbertSpaceThm{family.DefineStructure(registry.DefEntry{
	Name:  "HilbertSpace",
	Key:   "prop_3bf1f1ca7e8dedc7",
	Const: "complex_hilbert_space",
	Type:  "module_ops(complex, A) → (A → A → complex) → bool",
	Deps:  []registry.EntryLike{InnerProductSpace, NormDistanceDef, HilbertNormDef},
	Equations: []string{
		"∀M:module_ops(complex, A). ∀p:(A → A → complex). " +
			"    complex_hilbert_space(M, p) ⇔ " +
			"    complex_inner_space(M, p) ∧ metric_complete(M.carrier, norm_distance(M, hilbert_norm(p)))",
	},
})}

var OrthogonalComplementDef = orthogonalComplementDefThm{family.Define(registry.DefEntry{
	Name:  "OrthogonalComplementDef",
	Key:   "prop_30044320b4279e6",
	Const: "hilbert_complement",
	Type:  "module_ops(complex, A) → (A → A → complex) → set(A) → set(A)",
	Equations: []string{
		"∀M:module_ops(complex, A). ∀p:(A → A → complex). ∀S:set(A). " +
			"    hilbert_complement(M, p, S) = " +
			"    {x:A | x ∈ M.carrier ∧ ∀y:A. y ∈ S ⇒ p(x, y) = complex_of_real(&0)}",
	},
})}

var OrthogonalProjectionDef = orthogonalProjectionDefThm{family.Define(registry.DefEntry{
	Name:  "OrthogonalProjectionDef",
	Key:   "prop_5f1a8013c37e5c81",
	Const: "hilbert_projection",
	Type:  "module_ops(complex, A) → (A → A → complex) → set(A) → A → A",
	Deps:  []registry.EntryLike{OrthogonalComplementDef},
	Equations: []string{
		"∀M:module_ops(complex, A). ∀p:(A → A → complex). ∀S:set(A). ∀x:A. " +
			"    hilbert_projection(M, p, S, x) = " +
			"    COND(x ∈ M.carrier, εy:A. y ∈ S ∧ M.add(x, M.neg(y)) ∈ hilbert_complement(M, p, S), M.zero)",
	},
})}

var ProductInnerDef = productInnerDefThm{family.Define(registry.DefEntry{
	Name:  "ProductInnerDef",
	Key:   "prop_feeec43f398f2efc",
	Const: "direct_sum_inner",
	Type:  "(A → A → complex) → (B → B → complex) → prod(A, B) → prod(A, B) → complex",
	Equations: []string{
		"∀p:(A → A → complex). ∀q:(B → B → complex). ∀x y:prod(A, B). " +
			"    direct_sum_inner(p, q, x, y) = p(fst(x), fst(y)) + q(snd(x), snd(y))",
	},
})}
