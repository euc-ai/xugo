// definitions.go — a Dirichlet character modulo q.

package dirichlet_character

import (
	"github.com/euc-ai/xugo/library/registry"
)

// DirichletCharacterDef — `dirichlet_character(q, χ)`: χ is completely
// multiplicative, has period q, and vanishes exactly at the numbers not
// coprime to q.
var DirichletCharacterDef = dirichletCharacterDefThm{family.Define(registry.DefEntry{
	Name:  "DirichletCharacterDef",
	Key:   "prop_6c08fb6e57ae2083",
	Const: "dirichlet_character",
	Type:  "num → (num → complex) → bool",
	Equations: []string{
		"∀q:num. ∀χ:(num → complex). " +
			"    dirichlet_character(q, χ) ⇔ " +
			"    (∀m n:num. χ(m * n) = χ(m) * χ(n)) ∧ " +
			"    (∀n:num. χ(n + q) = χ(n)) ∧ " +
			"    (∀n:num. χ(n) = &0 ⇔ ¬nat_coprime(n, q))",
	},
	Reading: "At q = 1 every number is coprime to q and the only character is the constant 1. At " +
		"q = 0 only 1 is coprime to q, the period says nothing, and the one character is 1 at 1 and 0 " +
		"elsewhere. χ(1) = 1 at every q, 1 being coprime to every number, and χ(0) = 0 unless q = 1. " +
		"The value at 1, powers, products, conjugates and the principal character need nothing of q; " +
		"the theorems that read a congruence modulo q, Euler's among them, take 0 < q. The principal " +
		"character is the one that is 1 at every number coprime to q; it has no constant of its own.",
})}
