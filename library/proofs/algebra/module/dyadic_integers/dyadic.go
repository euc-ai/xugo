package dyadic_integers

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/borel_subgroup"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/polish_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/derived_limit"
	_ "github.com/euc-ai/xugo/library/proofs/int_num/int_div_rem"
	_ "github.com/euc-ai/xugo/library/proofs/int_num/int_pow"
	_ "github.com/euc-ai/xugo/library/proofs/int_num/int_real_lift"
	_ "github.com/euc-ai/xugo/library/proofs/iterate/int/int_sum"
	_ "github.com/euc-ai/xugo/library/proofs/topology/compact"
	"github.com/euc-ai/xugo/library/registry"
)

var DyadicIntegerGroupDef = dyadicIntegerGroupDefThm{family.Define(registry.DefEntry{
	Name:  "DyadicIntegerGroupDef",
	Key:   "prop_b8e9d37e08406ec",
	Const: "dyadic_integer_group",
	Type:  "group_ops(num → int)",
	Equations: []string{
		"dyadic_integer_group = " +
			"mk_group(λa:(num → int). λb:(num → int). λk:num. int_rem(a(k) + b(k), int_pow(2, k)), " +
			"    λk:num. 0, " +
			"    λa:(num → int). λk:num. int_rem(-a(k), int_pow(2, k)), " +
			"    {a:(num → int) | " +
			"        ∀k:num. 0 ≤ a(k) ∧ a(k) < int_pow(2, k) ∧ int_rem(a(k + 1), int_pow(2, k)) = a(k)})",
	},
	Deps: []registry.EntryLike{},
	Reading: "Compatible residues modulo 2^k, with residuewise " +
		"addition: an independent model of the additive 2-adic integers."})}

var DyadicIntegerTopologyDef = dyadicIntegerTopologyDefThm{family.Define(registry.DefEntry{
	Name:  "DyadicIntegerTopologyDef",
	Key:   "prop_2f55e8153ca96203",
	Const: "dyadic_integer_topology",
	Type:  "set(set(num → int))",
	Equations: []string{
		"dyadic_integer_topology = " +
			"subtopology(indexed_discrete_topology(𝕌, λk:num. int_of_num(0), λk:num. 𝕌), " +
			"    dyadic_integer_group.carrier)",
	},
	Deps:    []registry.EntryLike{DyadicIntegerGroupDef},
	Reading: "The closed inverse-limit topology of the residue groups."})}

var dyadicIntegerEmbeddingDef = dyadicIntegerEmbeddingDefThm{family.Define(registry.DefEntry{
	Name:      "dyadicIntegerEmbeddingDef",
	Key:       "prop_beae9922d8b0ec2a",
	Const:     "dyadic_integer_embedding",
	Type:      "int → num → int",
	Equations: []string{"∀a:int. ∀k:num. dyadic_integer_embedding(a, k) = int_rem(a, int_pow(2, k))"},
	Deps:      []registry.EntryLike{},
	Reading:   "An integer read modulo each power of two."})}

var dyadicSeriesDef = dyadicSeriesDefThm{family.Define(registry.DefEntry{
	Name:  "dyadicSeriesDef",
	Key:   "prop_da7eaaad58866649",
	Const: "dyadic_series",
	Type:  "(num → int) → num → int",
	Equations: []string{
		"∀a:(num → int). ∀k:num. " +
			"    dyadic_series(a, k) = " +
			"    int_rem(int_sum({i:num | i < k}, λi:num. int_pow(2, i) * a(i)), int_pow(2, k))",
	},
	Deps: []registry.EntryLike{},
	Reading: "The compatible residues of the convergent 2-adic series " +
		"sum 2^i a_i; each output uses only finitely many coordinates."})}

var DyadicIntegerPolishCover = dyadicIntegerPolishCoverThm{family.Add(registry.ProofEntry{
	Name: "DyadicIntegerPolishCover",
	Key:  "prop_e9b31993a04c72c4",
	Build: family.Card(
		Statement{
			Binders:    "",
			Hypotheses: []string{},
			Conclusion: "polish_cover_on(dyadic_integer_group, " +
				"    dyadic_integer_topology, " +
				"    image(dyadic_integer_embedding, 𝕌)) ∧ " +
				"compact_in(dyadic_integer_topology, dyadic_integer_group.carrier) ∧ " +
				"closure(dyadic_integer_topology, image(dyadic_integer_embedding, 𝕌)) = " +
				"dyadic_integer_group.carrier ∧ " +
				"¬closed_in(dyadic_integer_topology, image(dyadic_integer_embedding, 𝕌))",
		},
		"The compatible residues are a closed subgroup of the product of finite cyclic groups. "+
			"Integers meet every finite residue cylinder, while binary digits inject the Cantor "+
			"space into the inverse limit, which is uncountable; their countable image is therefore "+
			"dense proper and not closed. Its discrete integer parametrization makes it Polishable."),
	Deps: []registry.EntryLike{
		DyadicIntegerGroupDef,
		DyadicIntegerTopologyDef,
		dyadicIntegerEmbeddingDef,
		polish_group.ContinuousHomImagePolishable,
	},
	Reading: "The compatible residues are a closed subgroup of the product of finite cyclic " +
		"groups. Integers meet every finite residue cylinder, while binary digits inject the Cantor " +
		"space into the inverse limit, which is uncountable; their countable image is therefore " +
		"dense proper and not closed. Its discrete integer parametrization makes it Polishable.",
})}

var DyadicDerivedLimit = dyadicDerivedLimitThm{family.Add(registry.ProofEntry{
	Name: "DyadicDerivedLimit",
	Key:  "prop_4ad2cde4a68b4bcc",
	Build: family.Card(
		Statement{
			Binders:    "",
			Hypotheses: []string{},
			Conclusion: "borel_cover_iso( " +
				"    cocycle_group(tower_complex(λk:num. regular_module(int_ring), λk:num. λa:int. 2 * a), 1), " +
				"    cocycle_topology(tower_complex(λk:num. regular_module(int_ring), λk:num. λa:int. 2 * a), " +
				"        tower_topologies(λk:num. regular_module(int_ring)), " +
				"        1), " +
				"    coboundaries(tower_complex(λk:num. regular_module(int_ring), λk:num. λa:int. 2 * a), 1), " +
				"    dyadic_integer_group, " +
				"    dyadic_integer_topology, " +
				"    image(dyadic_integer_embedding, 𝕌), " +
				"    induced_map(λa:(num → int). " +
				"            left_coset(dyadic_integer_group.mul, " +
				"                dyadic_series(a), " +
				"                image(dyadic_integer_embedding, 𝕌)))) ∧ " +
				"card_le(𝕌⟨A:set(num)⟩, derived_limit(λk:num. regular_module(int_ring), λk:num. λa:int. 2 * a))",
		},
		"The series map is continuous and onto by binary digits. It sends a_k-2a_(k+1) to "+
			"the integer a_0. Conversely if the series is the integer m, the primitives (m minus "+
			"the k-term sum)/2^k are integers and solve the shift equation. This identifies the "+
			"two quotient covers and transfers the nonclosed-boundary continuum conclusion."),
	Deps: []registry.EntryLike{
		dyadicSeriesDef,
		DyadicIntegerPolishCover,
		derived_limit.CountableTowerPolishModel,
		polish_group.ContinuousLiftBijectiveIso,
		borel_subgroup.NonclosedBorelSubgroupContinuumIndex,
	},
	Reading: "The series map is continuous and onto by binary digits. It sends a_k-2a_(k+1) " +
		"to the integer a_0. Conversely if the series is the integer m, the primitives (m minus " +
		"the k-term sum)/2^k are integers and solve the shift equation. This identifies the two " +
		"quotient covers and transfers the nonclosed-boundary continuum conclusion.",
})}
