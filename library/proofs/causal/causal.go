// Package causal holds structural causal models on general measurable
// carriers: models and their solutions, interventions, the Markov bridge
// from graph separation to conditional independence, the three rules of
// the do-calculus as point formulas and in kernel form, adjustment
// formulas, identifiability, the expression language in which
// identification formulas are derived, the lines of the ID algorithm,
// and the hedge criterion with the completeness of the do-calculus.
package causal

import (
	// Structural causal models: the model record, its legality, the
	// solution of the structural equations and its distribution.
	_ "github.com/euc-ai/xugo/library/proofs/causal/structural_model"
	// Interventions: replacing mechanisms by constants, composition,
	// consistency, and the regime family comparing two distributions.
	_ "github.com/euc-ai/xugo/library/proofs/causal/intervention"
	// Structural σ-algebra families on a DAG and their global Markov
	// property, with models and regime families as instances.
	_ "github.com/euc-ai/xugo/library/proofs/causal/graphical_markov"
	// The three rules of the do-calculus.
	_ "github.com/euc-ai/xugo/library/proofs/causal/do_calculus"
	// The back-door and front-door adjustment formulas.
	_ "github.com/euc-ai/xugo/library/proofs/causal/adjustment"
	// The three rules in kernel form, through the randomized regime, and
	// the back-door adjustment for continuous variables.
	_ "github.com/euc-ai/xugo/library/proofs/causal/kernel_do_calculus"
	// Identifiability over a model class, and a pair of models that
	// agree on observations and differ under intervention.
	_ "github.com/euc-ai/xugo/library/proofs/causal/identifiability"
	// Causal expressions and the derivation relation of the do-calculus.
	_ "github.com/euc-ai/xugo/library/proofs/causal/do_derivation"
	// The meaning of causal expressions in a model and the soundness of
	// derivation.
	_ "github.com/euc-ai/xugo/library/proofs/causal/do_semantics"
	// The lines of the ID and IDC algorithms as derivations, with the
	// transfer of a subproblem's derivation and Tian's factorization.
	_ "github.com/euc-ai/xugo/library/proofs/causal/id_derivation"
	// The hedge criterion and the completeness of the do-calculus.
	_ "github.com/euc-ai/xugo/library/proofs/causal/hedge_criterion"
)
