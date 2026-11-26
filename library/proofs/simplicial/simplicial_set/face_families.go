// face_families.go — families of n-simplices indexed by a set S of the
// faces of an (n+1)-simplex: compatible when they meet as the faces of
// one (n+1)-simplex do, a face family of X when they are moreover
// n-simplices of X, and filled by an (n+1)-simplex whose faces at S
// they are. A horn missing the face k is the case
// S = {i | i ≤ n + 1 ∧ i ≠ k}, and the boundary of a cone under an
// r-simplex is a family on S = 0 .. r.

package simplicial_set

import (
	"github.com/euc-ai/xugo/library/registry"
)

// FacesCompatibleDef — `faces_compatible(d, n, S, y)`: the n-simplices
// y(i), read at the indices i ∈ S, have pairwise matching faces,
// d_i y(j) = d_{j−1} y(i) for i < j — the relation the faces of an
// (n+1)-simplex satisfy. Under the structure the text writes
// `faces_compatible(n, S, y)`.
var FacesCompatibleDef = facesCompatibleDefThm{family.Define(registry.DefEntry{
	Name:     "FacesCompatibleDef",
	Key:      "prop_fb35345e4c47a231",
	Const:    "faces_compatible",
	Type:     "(num → num → A → A) → num → set(num) → (num → A) → bool",
	Implicit: []string{"d"},
	Equations: []string{
		"∀d:(num → num → A → A). ∀n:num. ∀S:set(num). ∀y:(num → A). " +
			"    faces_compatible(d, n, S, y) ⇔ " +
			"    (∀i j:num. i ∈ S ∧ j ∈ S ∧ i < j ⇒ d(n, i, y(j)) = d(n, j - 1, y(i)))",
	},
	Reading: "The family is read only on S, and nothing bounds S: an index past n + 1 is read " +
		"like any other, so a statement about the faces of an (n+1)-simplex carries its own bound on S.",
})}

// FaceFamilyDef — `face_family(X, d, n, S, y)`: y is a family of
// n-simplices of X on the faces S, compatible as the faces of an
// (n+1)-simplex — a map to X from the union of those faces. Under the
// structure the text writes `face_family(n, S, y)`.
var FaceFamilyDef = faceFamilyDefThm{family.Define(registry.DefEntry{
	Name:     "FaceFamilyDef",
	Key:      "prop_a4b2652709e653b0",
	Const:    "face_family",
	Type:     "simplicial_ops(A) → num → set(num) → (num → A) → bool",
	Implicit: []string{"X"},
	Equations: []string{
		"∀X:simplicial_ops(A). ∀n:num. ∀S:set(num). ∀y:(num → A). " +
			"    face_family(X, n, S, y) ⇔ " +
			"    (∀i:num. i ∈ S ⇒ y(i) ∈ X.simplices(n)) ∧ faces_compatible(X.d, n, S, y)",
	},
	Deps: append([]registry.EntryLike{FacesCompatibleDef}, recordFields...),
})}

// FacesFillerDef — `faces_filler(d, n, S, y, x)`: the (n+1)-simplex x
// has the family y for its faces at S. Under the structure the text
// writes `faces_filler(n, S, y, x)`.
var FacesFillerDef = facesFillerDefThm{family.Define(registry.DefEntry{
	Name:     "FacesFillerDef",
	Key:      "prop_50fa715736581e3",
	Const:    "faces_filler",
	Type:     "(num → num → A → A) → num → set(num) → (num → A) → A → bool",
	Implicit: []string{"d"},
	Equations: []string{
		"∀d:(num → num → A → A). ∀n:num. ∀S:set(num). ∀y:(num → A). ∀x:A. " +
			"    faces_filler(d, n, S, y, x) ⇔ (∀i:num. i ∈ S ⇒ d(n + 1, i, x) = y(i))",
	},
})}
