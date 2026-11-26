package euclidean_domain

import (
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_domain"
	"github.com/euc-ai/xugo/library/registry"
)

// EuclideanDomain — R is an integral domain with a division algorithm
// measured by δ: any a divided by a nonzero b leaves a remainder that is
// zero or smaller than b under δ.
var EuclideanDomain = euclideanDomainThm{family.DefineStructure(registry.DefEntry{
	Name:    "EuclideanDomain",
	Key:     "prop_577db4d75886d15b",
	Const:   "euclidean_domain",
	Subject: "R",
	Type:    "ring_ops(A) → (A → num) → bool",
	Equations: []string{
		"∀R:ring_ops(A). ∀δ:(A → num). " +
			"    euclidean_domain(R, δ) ⇔ " +
			"    integral_domain_on(R) ∧ " +
			"    (∀a b:A. " +
			"        a ∈ R.carrier ∧ b ∈ R.carrier ∧ b ≠ R.zero ⇒ " +
			"        (∃q r:A. " +
			"            q ∈ R.carrier ∧ " +
			"            r ∈ R.carrier ∧ " +
			"            a = R.add(R.mul(q, b), r) ∧ " +
			"            (r = R.zero ∨ δ(r) < δ(b))))",
	},
})}
