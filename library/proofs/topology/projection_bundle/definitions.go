package projection_bundle

import (
	"github.com/euc-ai/xugo/library/registry"
)

var ProjectionDef = projectionDefThm{family.Define(registry.DefEntry{
	Name: "ProjectionDef",
	Key:  "prop_50623ed95f7abea4",
	Reading: "The bound is the first component of P, shared by " +
		"every point. Dimension zero and the empty base are allowed.",
	Const: "continuous_projection_bundle",
	Type:  "set(set(A)) → prod(num, A → num → num → complex) → bool",
	Equations: []string{
		"∀T:set(set(A)). ∀P:prod(num, A → num → num → complex). " +
			"    continuous_projection_bundle(T, P) ⇔ " +
			"    is_topology(T) ∧ " +
			"    (∀i j:num. " +
			"        i < fst(P) ∧ j < fst(P) ⇒ continuous_map(T, complex_topology, λx:A. snd(P)(x, i, j))) ∧ " +
			"    (∀x:A. ∀i j:num. " +
			"        x ∉ ⋃T ∨ fst(P) ≤ i ∨ fst(P) ≤ j ⇒ snd(P)(x, i, j) = complex_of_real(&0)) ∧ " +
			"    (∀x:A. ∀i j:num. " +
			"        x ∈ ⋃T ∧ i < fst(P) ∧ j < fst(P) ⇒ " +
			"        snd(P)(x, i, j) = complex_conj(snd(P)(x, j, i)) ∧ " +
			"        module_sum(complex_add, " +
			"            complex_of_real(&0), " +
			"            {k:num | k < fst(P)}, " +
			"            λk:num. snd(P)(x, i, k) * snd(P)(x, k, j)) = " +
			"        snd(P)(x, i, j))",
	},
})}

var TrivialDef = trivialDefThm{family.Define(registry.DefEntry{
	Name:  "TrivialDef",
	Key:   "prop_c50b82262af4f8a6",
	Const: "projection_trivial",
	Type:  "set(set(A)) → num → prod(num, A → num → num → complex)",
	Equations: []string{
		"∀T:set(set(A)). ∀r:num. " +
			"    projection_trivial(T, r) = " +
			"    (r, " +
			"        λx:A. λi:num. λj:num. " +
			"            COND(x ∈ ⋃T ∧ i < r ∧ i = j, complex_of_real(&1), complex_of_real(&0)))",
	},
})}

var MapDef = mapDefThm{family.Define(registry.DefEntry{
	Name:  "MapDef",
	Key:   "prop_9f552e1aebcfb3d6",
	Deps:  []registry.EntryLike{ProjectionDef},
	Const: "continuous_projection_map",
	Type: "set(set(A)) → " +
		"prod(num, A → num → num → complex) → " +
		"prod(num, A → num → num → complex) → " +
		"(A → num → num → complex) → " +
		"bool",
	Equations: []string{
		"∀T:set(set(A)). ∀P Q:prod(num, A → num → num → complex). ∀U:(A → num → num → complex). " +
			"    continuous_projection_map(T, P, Q, U) ⇔ " +
			"    continuous_projection_bundle(T, P) ∧ " +
			"    continuous_projection_bundle(T, Q) ∧ " +
			"    (∀i j:num. " +
			"        i < fst(Q) ∧ j < fst(P) ⇒ continuous_map(T, complex_topology, λx:A. U(x, i, j))) ∧ " +
			"    (∀x:A. ∀i j:num. x ∉ ⋃T ∨ fst(Q) ≤ i ∨ fst(P) ≤ j ⇒ U(x, i, j) = complex_of_real(&0)) ∧ " +
			"    (∀x:A. ∀i j:num. " +
			"        x ∈ ⋃T ∧ i < fst(Q) ∧ j < fst(P) ⇒ " +
			"        module_sum(complex_add, " +
			"            complex_of_real(&0), " +
			"            {k:num | k < fst(Q)}, " +
			"            λk:num. snd(Q)(x, i, k) * U(x, k, j)) = " +
			"        U(x, i, j) ∧ " +
			"        module_sum(complex_add, " +
			"            complex_of_real(&0), " +
			"            {k:num | k < fst(P)}, " +
			"            λk:num. U(x, i, k) * snd(P)(x, k, j)) = " +
			"        U(x, i, j))",
	},
})}

var InverseDef = inverseDefThm{family.Define(registry.DefEntry{
	Name:  "InverseDef",
	Key:   "prop_3861ce82e6e4fc4f",
	Const: "projection_inverse_on",
	Type: "set(A) → " +
		"prod(num, A → num → num → complex) → " +
		"prod(num, A → num → num → complex) → " +
		"(A → num → num → complex) → " +
		"(A → num → num → complex) → " +
		"bool",
	Equations: []string{
		"∀K:set(A). ∀P Q:prod(num, A → num → num → complex). ∀U V:(A → num → num → complex). " +
			"    projection_inverse_on(K, P, Q, U, V) ⇔ " +
			"    (∀x:A. ∀i j:num. " +
			"        x ∈ K ∧ i < fst(P) ∧ j < fst(P) ⇒ " +
			"        module_sum(complex_add, " +
			"            complex_of_real(&0), " +
			"            {k:num | k < fst(Q)}, " +
			"            λk:num. V(x, i, k) * U(x, k, j)) = " +
			"        snd(P)(x, i, j)) ∧ " +
			"    (∀x:A. ∀i j:num. " +
			"        x ∈ K ∧ i < fst(Q) ∧ j < fst(Q) ⇒ " +
			"        module_sum(complex_add, " +
			"            complex_of_real(&0), " +
			"            {k:num | k < fst(P)}, " +
			"            λk:num. U(x, i, k) * V(x, k, j)) = " +
			"        snd(Q)(x, i, j))",
	},
})}

var IsomorphicDef = isomorphicDefThm{family.Define(registry.DefEntry{
	Name:  "IsomorphicDef",
	Key:   "prop_64d1e7f1f387235",
	Deps:  []registry.EntryLike{MapDef, InverseDef},
	Const: "projection_isomorphic",
	Type: "set(set(A)) → " +
		"prod(num, A → num → num → complex) → " +
		"prod(num, A → num → num → complex) → " +
		"bool",
	Equations: []string{
		"∀T:set(set(A)). ∀P Q:prod(num, A → num → num → complex). " +
			"    projection_isomorphic(T, P, Q) ⇔ " +
			"    ∃U V:(A → num → num → complex). " +
			"        continuous_projection_map(T, P, Q, U) ∧ " +
			"        continuous_projection_map(T, Q, P, V) ∧ " +
			"        projection_inverse_on(⋃T, P, Q, U, V)",
	},
})}

var SumDef = sumDefThm{family.Define(registry.DefEntry{
	Name:  "SumDef",
	Key:   "prop_5f0d8969a32ee5f2",
	Const: "projection_sum",
	Type: "prod(num, A → num → num → complex) → " +
		"prod(num, A → num → num → complex) → " +
		"prod(num, A → num → num → complex)",
	Equations: []string{
		"∀P Q:prod(num, A → num → num → complex). " +
			"    projection_sum(P, Q) = " +
			"    (fst(P) + fst(Q), " +
			"        λx:A. λi:num. λj:num. " +
			"            COND(i < fst(P) ∧ j < fst(P), " +
			"                snd(P)(x, i, j), " +
			"                COND(fst(P) ≤ i ∧ fst(P) ≤ j ∧ i < fst(P) + fst(Q) ∧ j < fst(P) + fst(Q), " +
			"                    snd(Q)(x, i - fst(P), j - fst(P)), " +
			"                    complex_of_real(&0))))",
	},
})}

var TensorDef = tensorDefThm{family.Define(registry.DefEntry{
	Name:  "TensorDef",
	Key:   "prop_1a102f104c3b9e46",
	Const: "projection_tensor",
	Type: "prod(num, A → num → num → complex) → " +
		"prod(num, A → num → num → complex) → " +
		"prod(num, A → num → num → complex)",
	Equations: []string{
		"∀P Q:prod(num, A → num → num → complex). " +
			"    projection_tensor(P, Q) = " +
			"    (fst(P) * fst(Q), " +
			"        λx:A. λi:num. λj:num. " +
			"            COND(i < fst(P) * fst(Q) ∧ j < fst(P) * fst(Q), " +
			"                snd(P)(x, nat_div(i, fst(Q)), nat_div(j, fst(Q))) * " +
			"                snd(Q)(x, nat_mod(i, fst(Q)), nat_mod(j, fst(Q))), " +
			"                complex_of_real(&0)))",
	},
})}

var PullbackDef = pullbackDefThm{family.Define(registry.DefEntry{
	Name:  "PullbackDef",
	Key:   "prop_69e29ab2bbe229b0",
	Const: "projection_pullback",
	Type: "set(set(A)) → " +
		"(A → B) → " +
		"prod(num, B → num → num → complex) → " +
		"prod(num, A → num → num → complex)",
	Equations: []string{
		"∀T:set(set(A)). ∀f:(A → B). ∀P:prod(num, B → num → num → complex). " +
			"    projection_pullback(T, f, P) = " +
			"    (fst(P), λx:A. λi:num. λj:num. COND(x ∈ ⋃T, snd(P)(f(x), i, j), complex_of_real(&0)))",
	},
})}

var RankDef = rankDefThm{family.Define(registry.DefEntry{
	Name:  "RankDef",
	Key:   "prop_859a14cac038a087",
	Const: "projection_rank",
	Type:  "prod(num, A → num → num → complex) → A → num",
	Equations: []string{
		"∀P:prod(num, A → num → num → complex). ∀x:A. " +
			"    projection_rank(P, x) = " +
			"    εr:num. real_sum({i:num | i < fst(P)}, λi:num. re(snd(P)(x, i, i))) = &r",
	},
})}

var TotalSpaceDef = totalSpaceDefThm{family.Define(registry.DefEntry{
	Name:  "TotalSpaceDef",
	Key:   "prop_97b5258da827bac3",
	Const: "projection_total_space",
	Type:  "set(set(A)) → prod(num, A → num → num → complex) → set(prod(A, num → complex))",
	Equations: []string{
		"∀T:set(set(A)). ∀P:prod(num, A → num → num → complex). " +
			"    projection_total_space(T, P) = " +
			"    {p:prod(A, num → complex) | " +
			"        fst(p) ∈ ⋃T ∧ " +
			"        (∀i:num. fst(P) ≤ i ⇒ snd(p)(i) = complex_of_real(&0)) ∧ " +
			"        (∀i:num. " +
			"            i < fst(P) ⇒ " +
			"            module_sum(complex_add, " +
			"                complex_of_real(&0), " +
			"                {k:num | k < fst(P)}, " +
			"                λk:num. snd(P)(fst(p), i, k) * snd(p)(k)) = " +
			"            snd(p)(i))}",
	},
})}

var TotalTopologyDef = totalTopologyDefThm{family.Define(registry.DefEntry{
	Name:  "TotalTopologyDef",
	Key:   "prop_c5d1b7ed6332eef3",
	Deps:  []registry.EntryLike{TotalSpaceDef},
	Const: "projection_total_topology",
	Type:  "set(set(A)) → prod(num, A → num → num → complex) → set(set(prod(A, num → complex)))",
	Equations: []string{
		"∀T:set(set(A)). ∀P:prod(num, A → num → num → complex). " +
			"    projection_total_topology(T, P) = " +
			"    subtopology(product_topology(T, complex_coordinate_topology(fst(P))), " +
			"        projection_total_space(T, P))",
	},
})}
