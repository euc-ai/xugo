// definitions.go — a Dirichlet series, its sum, and the Dirichlet
// convolution of two coefficient sequences.

package dirichlet_series

import (
	"github.com/euc-ai/xugo/library/registry"
)

// DirichletSumsDef — `dirichlet_sums(a, s, v)`: the Dirichlet series
// Σ_{n ≥ 1} a(n)·n^(−s) sums to v.
var DirichletSumsDef = dirichletSumsDefThm{family.Define(registry.DefEntry{
	Name:  "DirichletSumsDef",
	Key:   "prop_b53cd626b38c69ce",
	Const: "dirichlet_sums",
	Type:  "(num → complex) → complex → complex → bool",
	Equations: []string{
		"∀a:(num → complex). ∀s v:complex. " +
			"    dirichlet_sums(a, s, v) ⇔ complex_sums(λn:num. a(n + 1) * complex_cpow(&(&(n + 1)), -s), v)",
	},
	Reading: "The series is indexed from 1: its term of index n is a(n + 1)·(n + " +
		"1)^(−s), so the value a(0) is never read and two coefficient sequences that " +
		"agree on the positive numbers have the same sums. Convergence is that of the " +
		"partial sums in the order of n, so a conditionally convergent series has a sum.",
})}

// DirichletSeriesDef — `dirichlet_series(a, s)`: the sum of the Dirichlet
// series of a at s.
var DirichletSeriesDef = dirichletSeriesDefThm{family.Define(registry.DefEntry{
	Name:  "DirichletSeriesDef",
	Key:   "prop_37a88ac0fda219e",
	Const: "dirichlet_series",
	Type:  "(num → complex) → complex → complex",
	Equations: []string{
		"∀a:(num → complex). ∀s:complex. dirichlet_series(a, s) = εv:complex. dirichlet_sums(a, s, v)",
	},
	Deps: []registry.EntryLike{DirichletSumsDef},
	Reading: "Where the series has no sum nothing satisfies the ε and the " +
		"value is unspecified, not 0: a statement about dirichlet_series(a, s) " +
		"holds its convergence at s, as a hypothesis or through dirichlet_sums.",
})}

// DirichletConvolutionDef — `dirichlet_convolution(a, b)`: the sequence
// whose value at n is the sum of a(d)·b(n/d) over the divisors d of n.
var DirichletConvolutionDef = dirichletConvolutionDefThm{family.Define(registry.DefEntry{
	Name:  "DirichletConvolutionDef",
	Key:   "prop_d7e07c773df0c44c",
	Const: "dirichlet_convolution",
	Type:  "(num → complex) → (num → complex) → num → complex",
	Equations: []string{
		"∀a b:(num → complex). ∀n:num. " +
			"    dirichlet_convolution(a, b, n) = Σ_{d∈{d:num | d ∣ n}} a(d) * b(div(n, d))",
	},
	Reading: "At n = 0 every number divides n and div(0, d) = 0, so the sum is that of " +
		"a(d)·b(0) over all d: the finite sum when a has finite support, and 0 by the fold's " +
		"convention when infinitely many terms are not 0. It is not 0 in general. The " +
		"convolution is the usual one at every n > 0, which is all a Dirichlet series reads.",
})}
