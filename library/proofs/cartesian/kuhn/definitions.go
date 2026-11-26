// definitions.go — the grid {0, …, p}ⁿ, Kuhn's order on it, and the
// simplices that order cuts the grid into.
//
// A grid point is a tuple of naturals in the carrier's sense: its entries
// past the dimension are the junk element, so the grid is a finite set of
// functions `num → num` and a simplex is a finite set of grid points.

package kuhn

import (
	_ "github.com/euc-ai/xugo/library/proofs/cartesian/carrier"
	_ "github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/registry"
)

// KuhnGridDef — `kuhn_grid(p, n)`: the n-tuples of naturals whose
// entries are at most p.
var KuhnGridDef = kuhnGridDefThm{family.Define(registry.DefEntry{
	Name:  "KuhnGridDef",
	Key:   "prop_3e5e8a89b476c865",
	Const: "kuhn_grid",
	Type:  "num → num → set(num → num)",
	Equations: []string{
		"∀p n:num. kuhn_grid(p, n) = {x:(num → num) | tuple(n, x) ∧ ∀i:num. i < n ⇒ x(i) ≤ p}",
	},
})}

// KuhnLeDef — `kuhn_le(n, x, y)`: y is x with some of its first n
// entries raised by one and the others kept. The relation is reflexive
// (KuhnLeRefl).
var KuhnLeDef = kuhnLeDefThm{family.Define(registry.DefEntry{
	Name:  "KuhnLeDef",
	Key:   "prop_51b6a6ef4ba7eaf1",
	Const: "kuhn_le",
	Type:  "num → (num → num) → (num → num) → bool",
	Equations: []string{
		"∀n:num. ∀x y:(num → num). " +
			"    kuhn_le(n, x, y) ⇔ ∀i:num. (i < n ⇒ x(i) ≤ y(i) ∧ y(i) ≤ x(i) + 1) ∧ (n ≤ i ⇒ y(i) = x(i))",
	},
})}

// KuhnSimplexDef — `kuhn_simplex(p, n, s)`: s is n + 1 points of the grid,
// any two comparable under kuhn_le. Ordered, they run from a point a to
// a + (1, …, 1), raising one coordinate at each step; the simplices of
// all base points and all orders of the coordinates triangulate the
// grid's cube.
var KuhnSimplexDef = kuhnSimplexDefThm{family.Define(registry.DefEntry{
	Name:  "KuhnSimplexDef",
	Key:   "prop_6f5398f6fb46d4db",
	Const: "kuhn_simplex",
	Type:  "num → num → set(num → num) → bool",
	Equations: []string{
		"∀p n:num. ∀s:set(num → num). " +
			"    kuhn_simplex(p, n, s) ⇔ " +
			"    s ⊆ kuhn_grid(p, n) ∧ " +
			"    has_size(s, n + 1) ∧ " +
			"    ∀x y:(num → num). x ∈ s ∧ y ∈ s ⇒ kuhn_le(n, x, y) ∨ kuhn_le(n, y, x)",
	},
	Deps: []registry.EntryLike{KuhnGridDef, KuhnLeDef},
})}
