// definitions.go — a structural causal model as one record: a background
// probability space, a DAG, a state carrier and σ-algebra for each node
// with the values off the nodes fixed, a noise σ-algebra for each node
// and a mechanism for each node. The structural equation of a node reads
// its parents through the restriction of the configuration to them, so
// locality is written into the equation and is not a condition to
// check. The solution is chosen from the equations; that it exists and
// is unique is a theorem of the chapter, not an input to the definition.

package structural_model

import (
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/datatypes/datatype_universe"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// recordRows are the recursive-type universe's rows a record's
// derivations read, and the pair rows its multi-part payload needs.
var recordRows = []registry.EntryLike{
	datatype_universe.Recursion,
	datatype_universe.FamilyCons,
	datatype_universe.NodeInjective,
	pairs.PairEq,
	pairs.Fst,
	pairs.Snd,
}

// ScmData — the record `scm_model(A, B, I)`: samples of type A, nodes of type
// I, states in the host type B. `mk_scm(Ω, Σ, P, V, E, D, T, z, N, g)`
// packs the background space (Ω, Σ, P), the nodes V and edges E, the
// state carrier D(i) and σ-algebra T(i) of each node, the value z(i)
// every configuration takes off V, the noise σ-algebra N(i) of each node
// and the mechanism g(i), which maps a configuration of the parents and
// a sample to a state. Which nodes are observed is not model data.
var ScmData = family.DefineData(registry.DataEntry{
	Name:   "Scm",
	Type:   "scm_model",
	Params: []string{"A", "B", "I"},
	Constructors: []proof.DataConstructorSpec{
		{
			Name: "mk_scm",
			Args: []string{
				"set(A)", "set(set(A))", "set(A) → extended_nonneg_real",
				"set(I)", "I → I → bool",
				"I → set(B)", "I → set(set(B))", "I → B",
				"I → set(set(A))", "I → (I → B) → A → B",
			},
		},
	},
	Fields: []registry.DataField{
		{Name: "ScmSampleDef", Const: "scm_sample", Field: "sample"},
		{Name: "ScmEventsDef", Const: "scm_events", Field: "events"},
		{Name: "ScmProbDef", Const: "scm_prob", Field: "prob"},
		{Name: "ScmNodesDef", Const: "scm_nodes", Field: "nodes"},
		{Name: "ScmEdgesDef", Const: "scm_edges", Field: "edges"},
		{Name: "ScmStatesDef", Const: "scm_states", Field: "states"},
		{Name: "ScmStateSigmaDef", Const: "scm_state_sigma", Field: "state_sigma"},
		{Name: "ScmDefaultDef", Const: "scm_default", Field: "default"},
		{Name: "ScmNoiseDef", Const: "scm_noise", Field: "noise"},
		{Name: "ScmMechDef", Const: "scm_mech", Field: "mech"},
	},
	Principles: registry.DataPrinciples{
		Induction:      "ScmInduction",
		Recursion:      "ScmRecursion",
		Injective:      "MkScmInjective",
		Extensionality: "ScmEq",
	},
	Deps: recordRows,
})

// ScmOn — `scm_on(M)`, the model is legal: its graph is a DAG, the
// background is a probability space, each node's states carry a
// σ-algebra, each node's noise is a sub-σ-algebra of the events, and
// each mechanism maps a parent configuration and a sample into the
// node's states measurably for the product of the parent
// configurations' product σ-algebra with the node's noise. Nonemptiness
// of the state carriers is a consequence, not a condition.
var ScmOn = scmOnThm{family.DefineStructure(registry.DefEntry{
	Name:  "ScmOn",
	Key:   "prop_30cf3b05d4e5a45a",
	Const: "scm_on",
	Type:  "scm_model(A, B, I) → bool",
	Equations: []string{
		"∀M:scm_model(A, B, I). " +
			"    scm_on(M) ⇔ " +
			"    dag_on(M.nodes, M.edges) ∧ " +
			"    probability_on(M.sample, M.events, M.prob) ∧ " +
			"    (∀i:I. i ∈ M.nodes ⇒ sigma_algebra_on(M.states(i), M.state_sigma(i))) ∧ " +
			"    (∀i:I. i ∈ M.nodes ⇒ sigma_algebra_on(M.sample, M.noise(i)) ∧ M.noise(i) ⊆ M.events) ∧ " +
			"    (∀i:I. " +
			"        i ∈ M.nodes ⇒ " +
			"        measurable_map(set_cross( " +
			"                indexed_functions(dag_parents(M.edges, i), M.default, M.states), M.sample), " +
			"            product_sigma(indexed_functions(dag_parents(M.edges, i), M.default, M.states), " +
			"                indexed_product_sigma(dag_parents(M.edges, i), " +
			"                    M.default, " +
			"                    M.states, " +
			"                    M.state_sigma), " +
			"                M.sample, " +
			"                M.noise(i)), " +
			"            M.states(i), " +
			"            M.state_sigma(i), " +
			"            λq:prod(I → B, A). M.mech(i, fst(q), snd(q))))",
	},
	Deps: []registry.EntryLike{ScmSampleDef, ScmEventsDef, ScmProbDef, ScmNodesDef, ScmEdgesDef,
		ScmStatesDef, ScmStateSigmaDef, ScmDefaultDef, ScmNoiseDef, ScmMechDef,
	},
})}

// NoiseIndependentDef — the noise σ-algebras of the nodes form an
// independent family: the class of models whose graph carries their
// semantics. A common cause of two nodes is a node of the model; no
// dependence between noises is left in the background.
var NoiseIndependentDef = noiseIndependentDefThm{family.Define(registry.DefEntry{
	Name:  "NoiseIndependentDef",
	Key:   "prop_90e12cdee54af61f",
	Const: "scm_noise_independent",
	Type:  "scm_model(A, B, I) → bool",
	Equations: []string{
		"∀M:scm_model(A, B, I). " +
			"    scm_noise_independent(M) ⇔ " +
			"    independent_sigma_family(M.sample, M.events, M.prob, M.nodes, M.noise)",
	},
	Deps: []registry.EntryLike{ScmSampleDef, ScmEventsDef, ScmProbDef, ScmNodesDef, ScmNoiseDef},
})}

// EquationsDef — v solves the structural equations at the sample u: at
// each node, v is the mechanism applied to v restricted to the parents
// and to u; off the nodes, v is the fixed value.
var EquationsDef = equationsDefThm{family.Define(registry.DefEntry{
	Name:  "EquationsDef",
	Key:   "prop_ba18a505d509a49d",
	Const: "scm_equations",
	Type:  "scm_model(A, B, I) → A → (I → B) → bool",
	Equations: []string{
		"∀M:scm_model(A, B, I). ∀u:A. ∀v:(I → B). " +
			"    scm_equations(M, u, v) ⇔ " +
			"    (∀i:I. " +
			"        i ∈ M.nodes ⇒ " +
			"        v(i) = M.mech(i, override_on(dag_parents(M.edges, i), v, M.default), u)) ∧ " +
			"    (∀i:I. i ∉ M.nodes ⇒ v(i) = M.default(i))",
	},
	Deps: []registry.EntryLike{ScmNodesDef, ScmEdgesDef, ScmDefaultDef, ScmMechDef},
})}

// SolveDef — the solution at u is a configuration chosen to solve the
// structural equations there.
var SolveDef = solveDefThm{family.Define(registry.DefEntry{
	Name:  "SolveDef",
	Key:   "prop_6b7c42dac2038ca1",
	Const: "scm_solve",
	Type:  "scm_model(A, B, I) → A → I → B",
	Equations: []string{
		"∀M:scm_model(A, B, I). ∀u:A. scm_solve(M, u) = εv:(I → B). scm_equations(M, u, v)",
	},
	Deps: []registry.EntryLike{EquationsDef},
})}

// DistributionDef — the distribution of the model is the background
// probability pushed forward along the solution map, a measure on
// configurations.
var DistributionDef = distributionDefThm{family.Define(registry.DefEntry{
	Name:  "DistributionDef",
	Key:   "prop_431251f5bad45adf",
	Const: "scm_distribution",
	Type:  "scm_model(A, B, I) → set(I → B) → extended_nonneg_real",
	Equations: []string{
		"∀M:scm_model(A, B, I). scm_distribution(M) = pushforward_measure(M.sample, M.prob, scm_solve(M))",
	},
	Deps: []registry.EntryLike{SolveDef, ScmSampleDef, ScmProbDef},
})}

// SigmaDef — `scm_sigma(M, K)` is the σ-algebra on the samples that the
// solution's coordinates in K generate: the information in the variables
// V_K.
var SigmaDef = sigmaDefThm{family.Define(registry.DefEntry{
	Name:  "SigmaDef",
	Key:   "prop_9d9679cb6c5869c7",
	Const: "scm_sigma",
	Type:  "scm_model(A, B, I) → set(I) → set(set(A))",
	Equations: []string{
		"∀M:scm_model(A, B, I). ∀K:set(I). " +
			"    scm_sigma(M, K) = coordinate_sigma(M.sample, scm_solve(M), M.state_sigma, K)",
	},
	Deps: []registry.EntryLike{SolveDef, ScmSampleDef, ScmStateSigmaDef},
})}

// ScmInduction — a property of every packed record holds of every model.
var ScmInduction = scmInductionThm{ScmData.Induct}

// ScmRecursion — a function on models is fixed by its value at the packed
// record.
var ScmRecursion = scmRecursionThm{ScmData.Recursion}

// MkScmInjective — the packed record determines its ten parts.
var MkScmInjective = mkScmInjectiveThm{ScmData.Inj}

// ScmEq — two models are equal when their ten fields are.
var ScmEq = scmEqThm{ScmData.Ext}
