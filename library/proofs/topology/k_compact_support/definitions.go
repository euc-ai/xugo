package k_compact_support

import (
	"github.com/euc-ai/xugo/library/registry"
)

var InvertibleAtDef = invertibleAtDefThm{family.Define(registry.DefEntry{
	Name:  "InvertibleAtDef",
	Key:   "prop_d67c898055d29136",
	Const: "projection_invertible_at",
	Type: "prod(num, A → num → num → complex) → " +
		"prod(num, A → num → num → complex) → " +
		"(A → num → num → complex) → " +
		"A → " +
		"bool",
	Equations: []string{
		"∀P Q:prod(num, A → num → num → complex). ∀U:(A → num → num → complex). ∀x:A. " +
			"    projection_invertible_at(P, Q, U, x) ⇔ " +
			"    ∃V:(A → num → num → complex). projection_inverse_on({x}, P, Q, U, V)",
	},
})}

var TripleDef = tripleDefThm{family.Define(registry.DefEntry{
	Name:  "TripleDef",
	Key:   "prop_d9db34ae8b14580c",
	Deps:  []registry.EntryLike{InvertibleAtDef},
	Const: "kc_triple",
	Type: "set(set(A)) → " +
		"prod(prod(num, A → num → num → complex), " +
		"    prod(prod(num, A → num → num → complex), A → num → num → complex)) → " +
		"bool",
	Equations: []string{
		"∀T:set(set(A)). " +
			"∀a:prod(prod(num, A → num → num → complex), " +
			"        prod(prod(num, A → num → num → complex), A → num → num → complex)). " +
			"    kc_triple(T, a) ⇔ " +
			"    continuous_projection_map(T, fst(a), fst(snd(a)), snd(snd(a))) ∧ " +
			"    ∃K:set(A). " +
			"        compact_in(T, K) ∧ " +
			"        (∀x:A. x ∈ ⋃T ∧ x ∉ K ⇒ projection_invertible_at(fst(a), fst(snd(a)), snd(snd(a)), x))",
	},
})}

var degenerateDef = degenerateDefThm{family.Define(registry.DefEntry{
	Name:  "degenerateDef",
	Key:   "prop_f307170e91d84d59",
	Deps:  []registry.EntryLike{InvertibleAtDef},
	Const: "kc_degenerate",
	Type: "set(set(A)) → " +
		"prod(prod(num, A → num → num → complex), " +
		"    prod(prod(num, A → num → num → complex), A → num → num → complex)) → " +
		"bool",
	Equations: []string{
		"∀T:set(set(A)). " +
			"∀a:prod(prod(num, A → num → num → complex), " +
			"        prod(prod(num, A → num → num → complex), A → num → num → complex)). " +
			"    kc_degenerate(T, a) ⇔ " +
			"    continuous_projection_map(T, fst(a), fst(snd(a)), snd(snd(a))) ∧ " +
			"    (∀x:A. x ∈ ⋃T ⇒ projection_invertible_at(fst(a), fst(snd(a)), snd(snd(a)), x))",
	},
})}

var zeroDef = zeroDefThm{family.Define(registry.DefEntry{
	Name:  "zeroDef",
	Key:   "prop_c6fabf282bcd0965",
	Const: "kc_zero_triple",
	Type: "set(set(A)) → " +
		"prod(prod(num, A → num → num → complex), " +
		"    prod(prod(num, A → num → num → complex), A → num → num → complex))",
	Equations: []string{
		"∀T:set(set(A)). " +
			"    kc_zero_triple(T) = " +
			"    (projection_trivial(T, 0), " +
			"        (projection_trivial(T, 0), λx:A. λi:num. λj:num. complex_of_real(&0)))",
	},
})}

var sumDef = sumDefThm{family.Define(registry.DefEntry{
	Name:  "sumDef",
	Key:   "prop_480467c45f58b35",
	Const: "kc_triple_sum",
	Type: "prod(prod(num, A → num → num → complex), " +
		"    prod(prod(num, A → num → num → complex), A → num → num → complex)) → " +
		"prod(prod(num, A → num → num → complex), " +
		"    prod(prod(num, A → num → num → complex), A → num → num → complex)) → " +
		"prod(prod(num, A → num → num → complex), " +
		"    prod(prod(num, A → num → num → complex), A → num → num → complex))",
	Equations: []string{
		"∀a b:prod(prod(num, A → num → num → complex), " +
			"        prod(prod(num, A → num → num → complex), A → num → num → complex)). " +
			"    kc_triple_sum(a, b) = " +
			"    (projection_sum(fst(a), fst(b)), " +
			"        (projection_sum(fst(snd(a)), fst(snd(b))), " +
			"            λx:A. λi:num. λj:num. " +
			"                COND(i < fst(fst(snd(a))) ∧ j < fst(fst(a)), " +
			"                    snd(snd(a))(x, i, j), " +
			"                    COND(fst(fst(snd(a))) ≤ i ∧ " +
			"                        fst(fst(a)) ≤ j ∧ " +
			"                        i < fst(fst(snd(a))) + fst(fst(snd(b))) ∧ " +
			"                        j < fst(fst(a)) + fst(fst(b)), " +
			"                        snd(snd(b))(x, i - fst(fst(snd(a))), j - fst(fst(a))), " +
			"                        complex_of_real(&0)))))",
	},
})}

var PullbackTripleDef = pullbackTripleDefThm{family.Define(registry.DefEntry{
	Name:  "PullbackTripleDef",
	Key:   "prop_93337b5a9740b012",
	Const: "kc_triple_pullback",
	Type: "set(set(A)) → " +
		"(A → B) → " +
		"prod(prod(num, B → num → num → complex), " +
		"    prod(prod(num, B → num → num → complex), B → num → num → complex)) → " +
		"prod(prod(num, A → num → num → complex), " +
		"    prod(prod(num, A → num → num → complex), A → num → num → complex))",
	Equations: []string{
		"∀T:set(set(A)). " +
			"∀f:(A → B). " +
			"∀a:prod(prod(num, B → num → num → complex), " +
			"        prod(prod(num, B → num → num → complex), B → num → num → complex)). " +
			"    kc_triple_pullback(T, f, a) = " +
			"    (projection_pullback(T, f, fst(a)), " +
			"        (projection_pullback(T, f, fst(snd(a))), " +
			"            λx:A. λi:num. λj:num. COND(x ∈ ⋃T, snd(snd(a))(f(x), i, j), complex_of_real(&0))))",
	},
})}

var HomotopyDef = homotopyDefThm{family.Define(registry.DefEntry{
	Name:  "HomotopyDef",
	Key:   "prop_cae7dc8b4b6a7977",
	Deps:  []registry.EntryLike{TripleDef, PullbackTripleDef},
	Const: "kc_triple_homotopic",
	Type: "set(set(A)) → " +
		"prod(prod(num, A → num → num → complex), " +
		"    prod(prod(num, A → num → num → complex), A → num → num → complex)) → " +
		"prod(prod(num, A → num → num → complex), " +
		"    prod(prod(num, A → num → num → complex), A → num → num → complex)) → " +
		"bool",
	Equations: []string{
		"∀T:set(set(A)). " +
			"∀a b:prod(prod(num, A → num → num → complex), " +
			"        prod(prod(num, A → num → num → complex), A → num → num → complex)). " +
			"    kc_triple_homotopic(T, a, b) ⇔ " +
			"    ∃h:prod(prod(num, prod(A, real) → num → num → complex), " +
			"            prod(prod(num, prod(A, real) → num → num → complex), " +
			"                prod(A, real) → num → num → complex)). " +
			"        kc_triple(product_topology(T, subtopology(real_topology, ⟦&0, &1⟧)), h) ∧ " +
			"        kc_triple_pullback(T, λx:A. (x, &0), h) = a ∧ " +
			"        kc_triple_pullback(T, λx:A. (x, &1), h) = b",
	},
})}

var RelationDef = relationDefThm{family.Define(registry.DefEntry{
	Name: "RelationDef",
	Key:  "prop_83e6465fd97a6fd9",
	Reading: "The universal quantifier takes the intersection of every equivalence congruence " +
		"containing the three generating relations; it assumes no index or cohomology invariant.",
	Deps:  []registry.EntryLike{TripleDef, degenerateDef, zeroDef, sumDef, HomotopyDef},
	Const: "kc_equivalent",
	Type: "set(set(A)) → " +
		"prod(prod(num, A → num → num → complex), " +
		"    prod(prod(num, A → num → num → complex), A → num → num → complex)) → " +
		"prod(prod(num, A → num → num → complex), " +
		"    prod(prod(num, A → num → num → complex), A → num → num → complex)) → " +
		"bool",
	Equations: []string{
		"∀T:set(set(A)). " +
			"∀a b:prod(prod(num, A → num → num → complex), " +
			"        prod(prod(num, A → num → num → complex), A → num → num → complex)). " +
			"    kc_equivalent(T, a, b) ⇔ " +
			"    kc_triple(T, a) ∧ " +
			"    kc_triple(T, b) ∧ " +
			"    ∀R:(prod(prod(num, A → num → num → complex), " +
			"                prod(prod(num, A → num → num → complex), A → num → num → complex)) → " +
			"            prod(prod(num, A → num → num → complex), " +
			"                prod(prod(num, A → num → num → complex), A → num → num → complex)) → " +
			"            bool). " +
			"        equivalence_on({u:prod(prod(num, A → num → num → complex), " +
			"                    prod(prod(num, A → num → num → complex), A → num → num → complex)) | " +
			"                kc_triple(T, u)}, " +
			"            R) ∧ " +
			"        (∀u:prod(prod(num, A → num → num → complex), " +
			"                prod(prod(num, A → num → num → complex), A → num → num → complex)). " +
			"            kc_degenerate(T, u) ⇒ R(u, kc_zero_triple(T))) ∧ " +
			"        (∀u v:prod(prod(num, A → num → num → complex), " +
			"                prod(prod(num, A → num → num → complex), A → num → num → complex)). " +
			"            kc_triple_homotopic(T, u, v) ⇒ R(u, v)) ∧ " +
			"        (∀u v w:prod(prod(num, A → num → num → complex), " +
			"                prod(prod(num, A → num → num → complex), A → num → num → complex)). " +
			"            R(u, v) ∧ kc_triple(T, u) ∧ kc_triple(T, v) ∧ kc_triple(T, w) ⇒ " +
			"            R(kc_triple_sum(u, w), kc_triple_sum(v, w)) ∧ " +
			"            R(kc_triple_sum(w, u), kc_triple_sum(w, v))) ⇒ " +
			"        R(a, b)",
	},
})}

var ClassDef = classDefThm{family.Define(registry.DefEntry{
	Name:  "ClassDef",
	Key:   "prop_371e7866e213e7c1",
	Deps:  []registry.EntryLike{RelationDef},
	Const: "kc_class",
	Type: "set(set(A)) → " +
		"prod(prod(num, A → num → num → complex), " +
		"    prod(prod(num, A → num → num → complex), A → num → num → complex)) → " +
		"set(prod(prod(num, A → num → num → complex), " +
		"        prod(prod(num, A → num → num → complex), A → num → num → complex)))",
	Equations: []string{
		"∀T:set(set(A)). " +
			"∀a:prod(prod(num, A → num → num → complex), " +
			"        prod(prod(num, A → num → num → complex), A → num → num → complex)). " +
			"    kc_class(T, a) = " +
			"    {b:prod(prod(num, A → num → num → complex), " +
			"            prod(prod(num, A → num → num → complex), A → num → num → complex)) | " +
			"        kc_equivalent(T, a, b)}",
	},
})}

var AddDef = addDefThm{family.Define(registry.DefEntry{
	Name:  "AddDef",
	Key:   "prop_2f06353382c64015",
	Deps:  []registry.EntryLike{sumDef, ClassDef},
	Const: "kc_add",
	Type: "set(set(A)) → " +
		"set(prod(prod(num, A → num → num → complex), " +
		"        prod(prod(num, A → num → num → complex), A → num → num → complex))) → " +
		"set(prod(prod(num, A → num → num → complex), " +
		"        prod(prod(num, A → num → num → complex), A → num → num → complex))) → " +
		"set(prod(prod(num, A → num → num → complex), " +
		"        prod(prod(num, A → num → num → complex), A → num → num → complex)))",
	Equations: []string{
		"∀T:set(set(A)). " +
			"∀C D:set(prod(prod(num, A → num → num → complex), " +
			"            prod(prod(num, A → num → num → complex), A → num → num → complex))). " +
			"    kc_add(T, C, D) = " +
			"    induced_map(λa:prod(prod(num, A → num → num → complex), " +
			"                prod(prod(num, A → num → num → complex), A → num → num → complex)). " +
			"            induced_map(λb:prod(prod(num, A → num → num → complex), " +
			"                        prod(prod(num, A → num → num → complex), A → num → num → complex)). " +
			"                    kc_class(T, kc_triple_sum(a, b)), " +
			"                D), " +
			"        C)",
	},
})}

var inverseTripleDef = inverseTripleDefThm{family.Define(registry.DefEntry{
	Name:  "inverseTripleDef",
	Key:   "prop_91612aa224b85151",
	Const: "kc_inverse_triple",
	Type: "prod(prod(num, A → num → num → complex), " +
		"    prod(prod(num, A → num → num → complex), A → num → num → complex)) → " +
		"prod(prod(num, A → num → num → complex), " +
		"    prod(prod(num, A → num → num → complex), A → num → num → complex))",
	Equations: []string{
		"∀a:prod(prod(num, A → num → num → complex), " +
			"        prod(prod(num, A → num → num → complex), A → num → num → complex)). " +
			"    kc_inverse_triple(a) = " +
			"    (fst(snd(a)), (fst(a), λx:A. λi:num. λj:num. complex_conj(snd(snd(a))(x, j, i))))",
	},
})}

var NegateDef = negateDefThm{family.Define(registry.DefEntry{
	Name:  "NegateDef",
	Key:   "prop_a2194f8b7ca7347b",
	Deps:  []registry.EntryLike{ClassDef, inverseTripleDef},
	Const: "kc_negate",
	Type: "set(set(A)) → " +
		"set(prod(prod(num, A → num → num → complex), " +
		"        prod(prod(num, A → num → num → complex), A → num → num → complex))) → " +
		"set(prod(prod(num, A → num → num → complex), " +
		"        prod(prod(num, A → num → num → complex), A → num → num → complex)))",
	Equations: []string{
		"∀T:set(set(A)). " +
			"∀C:set(prod(prod(num, A → num → num → complex), " +
			"            prod(prod(num, A → num → num → complex), A → num → num → complex))). " +
			"    kc_negate(T, C) = " +
			"    induced_map(λa:prod(prod(num, A → num → num → complex), " +
			"                prod(prod(num, A → num → num → complex), A → num → num → complex)). " +
			"            kc_class(T, kc_inverse_triple(a)), " +
			"        C)",
	},
})}

var GroupDef = groupDefThm{family.Define(registry.DefEntry{
	Name:  "GroupDef",
	Key:   "prop_72504660becbbb9a",
	Deps:  []registry.EntryLike{TripleDef, zeroDef, RelationDef, ClassDef, AddDef, NegateDef},
	Const: "kc_group",
	Type: "set(set(A)) → " +
		"group_ops(set(prod(prod(num, A → num → num → complex), " +
		"            prod(prod(num, A → num → num → complex), A → num → num → complex))))",
	Equations: []string{
		"∀T:set(set(A)). " +
			"    kc_group(T) = " +
			"    mk_group(kc_add(T), " +
			"        kc_class(T, kc_zero_triple(T)), " +
			"        kc_negate(T), " +
			"        quotient_on({a:prod(prod(num, A → num → num → complex), " +
			"                    prod(prod(num, A → num → num → complex), A → num → num → complex)) | " +
			"                kc_triple(T, a)}, " +
			"            kc_equivalent(T)))",
	},
})}

var PullbackDef = pullbackDefThm{family.Define(registry.DefEntry{
	Name:  "PullbackDef",
	Key:   "prop_1b926c2f422db201",
	Deps:  []registry.EntryLike{PullbackTripleDef, ClassDef},
	Const: "kc_pullback",
	Type: "set(set(A)) → " +
		"(A → B) → " +
		"set(prod(prod(num, B → num → num → complex), " +
		"        prod(prod(num, B → num → num → complex), B → num → num → complex))) → " +
		"set(prod(prod(num, A → num → num → complex), " +
		"        prod(prod(num, A → num → num → complex), A → num → num → complex)))",
	Equations: []string{
		"∀T:set(set(A)). " +
			"∀f:(A → B). " +
			"∀C:set(prod(prod(num, B → num → num → complex), " +
			"            prod(prod(num, B → num → num → complex), B → num → num → complex))). " +
			"    kc_pullback(T, f, C) = " +
			"    induced_map(λa:prod(prod(num, B → num → num → complex), " +
			"                prod(prod(num, B → num → num → complex), B → num → num → complex)). " +
			"            kc_class(T, kc_triple_pullback(T, f, a)), " +
			"        C)",
	},
})}

var ProperDef = properDefThm{family.Define(registry.DefEntry{
	Name:  "ProperDef",
	Key:   "prop_c7689d2073cfac20",
	Const: "kc_proper_map",
	Type:  "set(set(A)) → set(set(B)) → (A → B) → bool",
	Equations: []string{
		"∀T:set(set(A)). ∀S:set(set(B)). ∀f:(A → B). " +
			"    kc_proper_map(T, S, f) ⇔ " +
			"    continuous_map(T, S, f) ∧ " +
			"    (∀K:set(B). compact_in(S, K) ⇒ compact_in(T, {x:A | x ∈ ⋃T ∧ f(x) ∈ K}))",
	},
})}

var CompactComparisonDef = compactComparisonDefThm{family.Define(registry.DefEntry{
	Name:  "CompactComparisonDef",
	Key:   "prop_fe3394df1f42cae0",
	Const: "kc_to_k",
	Type: "set(set(A)) → " +
		"set(prod(prod(num, A → num → num → complex), " +
		"        prod(prod(num, A → num → num → complex), A → num → num → complex))) → " +
		"set(prod(prod(num, A → num → num → complex), prod(num, A → num → num → complex)))",
	Equations: []string{
		"∀T:set(set(A)). " +
			"∀C:set(prod(prod(num, A → num → num → complex), " +
			"            prod(prod(num, A → num → num → complex), A → num → num → complex))). " +
			"    kc_to_k(T, C) = " +
			"    induced_map(λa:prod(prod(num, A → num → num → complex), " +
			"                prod(prod(num, A → num → num → complex), A → num → num → complex)). " +
			"            k_class(T, (fst(a), fst(snd(a)))), " +
			"        C)",
	},
})}

var SupportedDef = supportedDefThm{family.Define(registry.DefEntry{
	Name:  "SupportedDef",
	Key:   "prop_a5e5d729e3a060e",
	Deps:  []registry.EntryLike{InvertibleAtDef, TripleDef},
	Const: "kc_supported_in",
	Type: "set(set(A)) → " +
		"set(A) → " +
		"prod(prod(num, A → num → num → complex), " +
		"    prod(prod(num, A → num → num → complex), A → num → num → complex)) → " +
		"bool",
	Equations: []string{
		"∀T:set(set(A)). " +
			"∀K:set(A). " +
			"∀a:prod(prod(num, A → num → num → complex), " +
			"        prod(prod(num, A → num → num → complex), A → num → num → complex)). " +
			"    kc_supported_in(T, K, a) ⇔ " +
			"    kc_triple(T, a) ∧ " +
			"    compact_in(T, K) ∧ " +
			"    (∀x:A. x ∈ ⋃T ∧ x ∉ K ⇒ projection_invertible_at(fst(a), fst(snd(a)), snd(snd(a)), x))",
	},
})}

var ExtensionDef = extensionDefThm{family.Define(registry.DefEntry{
	Name: "ExtensionDef",
	Key:  "prop_d3b4b6172148bdf2",
	Reading: "The choice asks for a global relative triple supported in the open subspace " +
		"and whose restricted compact-support class is the prescribed one. Excision proves " +
		"existence and uniqueness of the global class; the definition itself asserts neither.",
	Deps:  []registry.EntryLike{PullbackTripleDef, ClassDef, SupportedDef},
	Const: "kc_open_extension",
	Type: "set(set(A)) → " +
		"set(A) → " +
		"set(prod(prod(num, A → num → num → complex), " +
		"        prod(prod(num, A → num → num → complex), A → num → num → complex))) → " +
		"set(prod(prod(num, A → num → num → complex), " +
		"        prod(prod(num, A → num → num → complex), A → num → num → complex)))",
	Equations: []string{
		"∀T:set(set(A)). " +
			"∀U:set(A). " +
			"∀a:set(prod(prod(num, A → num → num → complex), " +
			"            prod(prod(num, A → num → num → complex), A → num → num → complex))). " +
			"    kc_open_extension(T, U, a) = " +
			"    εC:set(prod(prod(num, A → num → num → complex), " +
			"                prod(prod(num, A → num → num → complex), A → num → num → complex))). " +
			"    ∃b:prod(prod(num, A → num → num → complex), " +
			"            prod(prod(num, A → num → num → complex), A → num → num → complex)). " +
			"    ∃K:set(A). " +
			"        K ⊆ U ∧ " +
			"        kc_supported_in(T, K, b) ∧ " +
			"        C = kc_class(T, b) ∧ " +
			"        kc_class(subtopology(T, U), kc_triple_pullback(subtopology(T, U), λx:A. x, b)) = a",
	},
})}

var tensorMapDef = tensorMapDefThm{family.Define(registry.DefEntry{
	Name:  "tensorMapDef",
	Key:   "prop_1cf69adcadb88095",
	Const: "kc_tensor_matrix",
	Type: "num → " +
		"num → " +
		"num → " +
		"num → " +
		"(A → num → num → complex) → " +
		"(A → num → num → complex) → " +
		"A → " +
		"num → " +
		"num → " +
		"complex",
	Equations: []string{
		"∀p q r s:num. ∀U V:(A → num → num → complex). ∀x:A. ∀i j:num. " +
			"    kc_tensor_matrix(p, q, r, s, U, V, x, i, j) = " +
			"    COND(i < p * r ∧ j < q * s, " +
			"        U(x, nat_div(i, r), nat_div(j, s)) * V(x, nat_mod(i, r), nat_mod(j, s)), " +
			"        complex_of_real(&0))",
	},
})}

var blockMapDef = blockMapDefThm{family.Define(registry.DefEntry{
	Name:  "blockMapDef",
	Key:   "prop_8ee03a2c35c275da",
	Const: "kc_block_matrix",
	Type: "num → " +
		"num → " +
		"num → " +
		"num → " +
		"(A → num → num → complex) → " +
		"(A → num → num → complex) → " +
		"(A → num → num → complex) → " +
		"(A → num → num → complex) → " +
		"A → " +
		"num → " +
		"num → " +
		"complex",
	Equations: []string{
		"∀p q r s:num. ∀A B C D:(A → num → num → complex). ∀x:A. ∀i j:num. " +
			"    kc_block_matrix(p, q, r, s, A, B, C, D, x, i, j) = " +
			"    COND(i < p ∧ j < r, " +
			"        A(x, i, j), " +
			"        COND(i < p ∧ r ≤ j ∧ j < r + s, " +
			"            B(x, i, j - r), " +
			"            COND(p ≤ i ∧ i < p + q ∧ j < r, " +
			"                C(x, i - p, j), " +
			"                COND(p ≤ i ∧ i < p + q ∧ r ≤ j ∧ j < r + s, " +
			"                    D(x, i - p, j - r), " +
			"                    complex_of_real(&0)))))",
	},
})}

var ProductTripleDef = productTripleDefThm{family.Define(registry.DefEntry{
	Name:  "ProductTripleDef",
	Key:   "prop_38bcccf16eac9021",
	Deps:  []registry.EntryLike{tensorMapDef, blockMapDef},
	Const: "kc_triple_product",
	Type: "prod(prod(num, A → num → num → complex), " +
		"    prod(prod(num, A → num → num → complex), A → num → num → complex)) → " +
		"prod(prod(num, A → num → num → complex), " +
		"    prod(prod(num, A → num → num → complex), A → num → num → complex)) → " +
		"prod(prod(num, A → num → num → complex), " +
		"    prod(prod(num, A → num → num → complex), A → num → num → complex))",
	Equations: []string{
		"∀a b:prod(prod(num, A → num → num → complex), " +
			"        prod(prod(num, A → num → num → complex), A → num → num → complex)). " +
			"    kc_triple_product(a, b) = " +
			"    (projection_sum(projection_tensor(fst(a), fst(b)), " +
			"            projection_tensor(fst(snd(a)), fst(snd(b)))), " +
			"        (projection_sum(projection_tensor(fst(snd(a)), fst(b)), " +
			"                projection_tensor(fst(a), fst(snd(b)))), " +
			"            kc_block_matrix(fst(fst(snd(a))) * fst(fst(b)), " +
			"                fst(fst(a)) * fst(fst(snd(b))), " +
			"                fst(fst(a)) * fst(fst(b)), " +
			"                fst(fst(snd(a))) * fst(fst(snd(b))), " +
			"                kc_tensor_matrix(fst(fst(snd(a))), " +
			"                    fst(fst(a)), " +
			"                    fst(fst(b)), " +
			"                    fst(fst(b)), " +
			"                    snd(snd(a)), " +
			"                    snd(fst(b))), " +
			"                kc_tensor_matrix(fst(fst(snd(a))), " +
			"                    fst(fst(snd(a))), " +
			"                    fst(fst(b)), " +
			"                    fst(fst(snd(b))), " +
			"                    snd(fst(snd(a))), " +
			"                    λx:A. λi:num. λj:num. -complex_conj(snd(snd(b))(x, j, i))), " +
			"                kc_tensor_matrix(fst(fst(a)), " +
			"                    fst(fst(a)), " +
			"                    fst(fst(snd(b))), " +
			"                    fst(fst(b)), " +
			"                    snd(fst(a)), " +
			"                    snd(snd(b))), " +
			"                kc_tensor_matrix(fst(fst(a)), " +
			"                    fst(fst(snd(a))), " +
			"                    fst(fst(snd(b))), " +
			"                    fst(fst(snd(b))), " +
			"                    λx:A. λi:num. λj:num. complex_conj(snd(snd(a))(x, j, i)), " +
			"                    snd(fst(snd(b)))))))",
	},
})}

var externalTripleDef = externalTripleDefThm{family.Define(registry.DefEntry{
	Name:  "externalTripleDef",
	Key:   "prop_ff66e13e6eef3766",
	Deps:  []registry.EntryLike{PullbackTripleDef, ProductTripleDef},
	Const: "kc_triple_external",
	Type: "set(set(A)) → " +
		"set(set(B)) → " +
		"prod(prod(num, A → num → num → complex), " +
		"    prod(prod(num, A → num → num → complex), A → num → num → complex)) → " +
		"prod(prod(num, B → num → num → complex), " +
		"    prod(prod(num, B → num → num → complex), B → num → num → complex)) → " +
		"prod(prod(num, prod(A, B) → num → num → complex), " +
		"    prod(prod(num, prod(A, B) → num → num → complex), prod(A, B) → num → num → complex))",
	Equations: []string{
		"∀T:set(set(A)). " +
			"∀S:set(set(B)). " +
			"∀a:prod(prod(num, A → num → num → complex), " +
			"        prod(prod(num, A → num → num → complex), A → num → num → complex)). " +
			"∀b:prod(prod(num, B → num → num → complex), " +
			"        prod(prod(num, B → num → num → complex), B → num → num → complex)). " +
			"    kc_triple_external(T, S, a, b) = " +
			"    kc_triple_product(kc_triple_pullback(product_topology(T, S), λz:prod(A, B). fst(z), a), " +
			"        kc_triple_pullback(product_topology(T, S), λz:prod(A, B). snd(z), b))",
	},
})}

var ExternalDef = externalDefThm{family.Define(registry.DefEntry{
	Name:  "ExternalDef",
	Key:   "prop_be79466569837cec",
	Deps:  []registry.EntryLike{ClassDef, externalTripleDef},
	Const: "kc_external",
	Type: "set(set(A)) → " +
		"set(set(B)) → " +
		"set(prod(prod(num, A → num → num → complex), " +
		"        prod(prod(num, A → num → num → complex), A → num → num → complex))) → " +
		"set(prod(prod(num, B → num → num → complex), " +
		"        prod(prod(num, B → num → num → complex), B → num → num → complex))) → " +
		"set(prod(prod(num, prod(A, B) → num → num → complex), " +
		"        prod(prod(num, prod(A, B) → num → num → complex), prod(A, B) → num → num → complex)))",
	Equations: []string{
		"∀T:set(set(A)). " +
			"∀S:set(set(B)). " +
			"∀C:set(prod(prod(num, A → num → num → complex), " +
			"            prod(prod(num, A → num → num → complex), A → num → num → complex))). " +
			"∀D:set(prod(prod(num, B → num → num → complex), " +
			"            prod(prod(num, B → num → num → complex), B → num → num → complex))). " +
			"    kc_external(T, S, C, D) = " +
			"    induced_map(λa:prod(prod(num, A → num → num → complex), " +
			"                prod(prod(num, A → num → num → complex), A → num → num → complex)). " +
			"            induced_map(λb:prod(prod(num, B → num → num → complex), " +
			"                        prod(prod(num, B → num → num → complex), B → num → num → complex)). " +
			"                    kc_class(product_topology(T, S), kc_triple_external(T, S, a, b)), " +
			"                D), " +
			"        C)",
	},
})}
