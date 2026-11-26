// triangle.go — the three double complexes of the transitivity triangle
// of a tower R → S → T, with coefficients in a module N over T, and their
// totals. At (p, q) the middle term is the finitely supported functions
// with values in N on the variables of the relative standard resolution
// Q(p, q), P's names of degree p under the first tag and the relative
// names under the second; column p with the Jacobians of Q's vertical
// faces is the differential complex of the resolution Q(p, •) of T, and
// the horizontal boundary is the alternating sum of the Jacobians of the
// maps Q's columns receive from P's faces. The left term is the functions
// on P's names, a sub-double complex under the same boundaries, its
// columns constant and augmented onto the cotangent complex of S over R
// by untagging; the right term is the functions on the relative names,
// the quotient — the projection reads a function at the second tags, the
// section puts it back — whose rows are the chains with values in N on
// the simplicial sets of relative names and whose vertical boundary is
// the middle one through the section and the projection. The inclusion,
// the projection and the section are short exact and split at every
// (p, q), so on the totals they are short exact; the left total maps
// quasi-isomorphically onto the cotangent complex of S over R.

package transitivity

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/cotangent_complex"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/simplicial_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/standard_resolution"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/chain_complex"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/function_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/tor_ext"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/partial_derivative"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/simplicial/simplicial_chain"
	"github.com/euc-ai/xugo/library/proofs/simplicial/simplicial_module"
	"github.com/euc-ai/xugo/library/registry"

	// set_basic mints the image of a set; the import initializes that mint
	// before the definitions here are parsed.
	_ "github.com/euc-ai/xugo/library/proofs/sets/set_basic"
)

// The binders of a construction over the tower: the three rings, the two
// structure maps and the module of coefficients over T.
const towerBinders = "∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A " +
	"→ B). ∀T:ring_ops(C). ∀g:(B → C). ∀N:module_ops(C, D). "

const towerType = "ring_ops(A) → ring_ops(B) → (A " +
	"→ B) → ring_ops(C) → (B → C) → module_ops(C, D) → "

// The three cotangent complexes of the tower with coefficients in N, all
// complexes over T: of S over R, of T over R and of T over S.
const (
	cotangentSR = "cotangent_complex(R, S, f, T, g, N)"
	cotangentTR = "cotangent_complex(R, T, λa:A. g(f(a)), T, λc:C. c, N)"
	cotangentTS = "cotangent_complex(S, T, g, T, λc:C. c, N)"
)

const (
	leftTotal   = "triangle_left_total(R, S, f, T, g, N)"
	middleTotal = "triangle_middle_total(R, S, f, T, g, N)"
	rightTotal  = "triangle_right_total⟨U:U⟩(R, S, f, T, g, N)"
)

// ---------------------------------------------------------------------------
// The variables and the three terms
// ---------------------------------------------------------------------------

// TriangleColumnNamesDef — `triangle_column_names(R, S, T, p, q)`: the
// variables of the (p, q)-simplices of the relative standard resolution,
// P's names of degree p under the first tag and the relative names of
// (p, q) under the second.
var TriangleColumnNamesDef = triangleColumnNamesDefThm{family.Define(registry.DefEntry{
	Name:  "TriangleColumnNamesDef",
	Key:   "prop_4cf701a8a5ce325",
	Const: "triangle_column_names",
	Type:  "ring_ops(A) → ring_ops(B) → ring_ops(C) → num → num → set(U)",
	Equations: []string{
		"∀R:ring_ops(A). ∀S:ring_ops(B). ∀T:ring_ops(C). ∀p q:num. " +
			"    triangle_column_names(R, S, T, p, q) = " +
			"    image(universe_tag(0), standard_names(R, S, p)) ∪ " +
			"    image(universe_tag(1), relative_names(R, S, T, p, q))",
	},
	Reading: "relative_terms(R, S, T, p, q) is the free algebra over R on these " +
		"names, so triangle_column_names(R, S, T, p) is the name sets of column p as " +
		"a polynomial simplicial algebra. The two parts are disjoint when the two " +
		"tags have disjoint images, which cotangent_universe(R, 𝕌⟨A:U⟩) provides.",
})}

// triangleLeftDef — `triangle_left(R, S, N, p, q)`: the left term at
// (p, q), the finitely supported functions with values in N on P's names
// of degree p under the first tag, the same in every vertical degree q.
var triangleLeftDef = triangleLeftDefThm{family.Define(registry.DefEntry{
	Name:  "triangleLeftDef",
	Key:   "prop_b088deb13415bea4",
	Const: "triangle_left",
	Type:  "ring_ops(A) → ring_ops(B) → module_ops(C, D) → num → num → set(U → D)",
	Equations: []string{
		"∀R:ring_ops(A). ∀S:ring_ops(B). ∀N:module_ops(C, D). ∀p q:num. " +
			"    triangle_left(R, S, N, p, q) = " +
			"    finite_supp(N.zero, N.carrier, image(universe_tag(0), standard_names(R, S, p)))",
	},
	Reading: "Untagged it is the term of degree p of the cotangent complex of S over R with " +
		"coefficients in N, repeated in every vertical degree: the vertical faces of Q fix P's " +
		"variables, so each acts on it as the identity. N is a module over T and the coefficients reach " +
		"it through the augmentation of Q onto T, which on P's variables is g after P's augmentation.",
})}

// triangleMiddleDef — `triangle_middle(R, S, T, N, p, q)`: the middle term
// at (p, q), the finitely supported functions with values in N on all
// the variables of Q(p, q).
var triangleMiddleDef = triangleMiddleDefThm{family.Define(registry.DefEntry{
	Name:  "triangleMiddleDef",
	Key:   "prop_b8f1c0ead2eb4a80",
	Const: "triangle_middle",
	Type:  "ring_ops(A) → ring_ops(B) → ring_ops(C) → module_ops(C, D) → num → num → set(U → D)",
	Equations: []string{
		"∀R:ring_ops(A). ∀S:ring_ops(B). ∀T:ring_ops(C). ∀N:module_ops(C, D). ∀p q:num. " +
			"    triangle_middle(R, S, T, N, p, q) = " +
			"    finite_supp(N.zero, N.carrier, triangle_column_names(R, S, T, p, q))",
	},
	Reading: "It is differential_terms(triangle_column_names(R, S, T, " +
		"p), N, q): Q(p, q) is free over R on these variables, so this is " +
		"the module of differentials of Q(p, q) over R with coefficients in N.",
	Deps: []registry.EntryLike{TriangleColumnNamesDef},
})}

// triangleRightDef — `triangle_right(R, S, T, N, p, q)`: the right term at
// (p, q), the finitely supported functions with values in N on the
// relative names of (p, q), untagged.
var triangleRightDef = triangleRightDefThm{family.Define(registry.DefEntry{
	Name:  "triangleRightDef",
	Key:   "prop_33872401af62e084",
	Const: "triangle_right",
	Type:  "ring_ops(A) → ring_ops(B) → ring_ops(C) → module_ops(C, D) → num → num → set(U → D)",
	Equations: []string{
		"∀R:ring_ops(A). ∀S:ring_ops(B). ∀T:ring_ops(C). ∀N:module_ops(C, D). ∀p q:num. " +
			"    triangle_right(R, S, T, N, p, q) = " +
			"    finite_supp(N.zero, N.carrier, relative_names(R, S, T, p, q))",
	},
	Reading: "Q(p, q) is free over P's p-simplices on the relative names, so this is " +
		"the module of differentials of Q(p, q) over P's p-simplices with coefficients in N. " +
		"Its row q is the module of chains with values in N on the simplicial set of relative " +
		"names of row q; in row 0 the names are standard_names(S, T, 0) in every column.",
})}

// ---------------------------------------------------------------------------
// The boundaries of the middle and the left term
// ---------------------------------------------------------------------------

// triangleHorizontalDef — `triangle_horizontal(R, S, f, T, g, N, p, q,
// u)`: the horizontal boundary out of (p, q) of the middle and of the left
// term, the alternating sum over i ≤ p of the Jacobians of the maps of
// row q induced by P's faces of degree p, read on the differentials of
// column p into column p − 1.
var triangleHorizontalDef = triangleHorizontalDefThm{family.Define(registry.DefEntry{
	Name:  "triangleHorizontalDef",
	Key:   "prop_cbd65052f059a977",
	Const: "triangle_horizontal",
	Type:  towerType + "num → num → (U → D) → U → D",
	Equations: []string{
		towerBinders + "∀p q:num. ∀u:(U → D). triangle_horizontal(R, S, f, T, g, N, p, q, u) = " +
			"face_boundary(T, finite_supp_module(N, 𝕌⟨A:U⟩), λn:num. λi:num. differential_map(R, triangle_column_names(R, S, T, n), triangle_column_names(R, S, T, n - 1), " +
			"relative_vertical_face(R, S, f, T, g, n - 1), relative_vertical_eps(R, S, f, T, g, n - 1), λm:num. relative_horizontal_map(R, standard_face(R, S, f, n, i), m), N, q), p, u)",
	},
	Reading: "Each face is differential_map at the map of columns induced by P's face i, the " +
		"coefficients read through the augmentation of column p − 1 onto T in degree q; the signs " +
		"are T's. The face carries P's variables into the algebra on P's names under the first " +
		"tag, so the left term is carried into itself and these are its boundaries too; a relative " +
		"name goes to a relative name, so on the relative names the Jacobian is the map of names. " +
		"Out of p = 0 it is the face of a vertex, which no axiom of a double complex reads.",
	Deps: []registry.EntryLike{TriangleColumnNamesDef},
})}

// TriangleVerticalDef — `triangle_vertical(R, S, f, T, g, N, p, q, u)`:
// the vertical boundary out of (p, q) of the middle and of the left term,
// the boundary of the differential complex of column p.
var TriangleVerticalDef = triangleVerticalDefThm{family.Define(registry.DefEntry{
	Name:  "TriangleVerticalDef",
	Key:   "prop_a2efb6cf584b3c4f",
	Const: "triangle_vertical",
	Type:  towerType + "num → num → (U → D) → U → D",
	Equations: []string{
		towerBinders + "∀p q:num. ∀u:(U → D). triangle_vertical(R, S, f, T, g, N, p, q, u) = " +
			"differential_boundary(R, triangle_column_names(R, S, T, p), relative_vertical_face(R, S, f, T, g, p), T, relative_vertical_eps(R, S, f, T, g, p), N, q, u)",
	},
	Reading: "Column p of the middle term with this boundary is differential_complex(R, " +
		"triangle_column_names(R, S, T, p), relative_vertical_face(R, S, f, T, g, p), T, " +
		"relative_vertical_eps(R, S, f, T, g, p), N), the cotangent complex of T over R " +
		"computed on the resolution Q(p, •). The vertical faces fix P's variables, so on the " +
		"left term every face is the identity and the boundary is zero out of odd degrees and " +
		"the identity out of even ones. Out of q = 0 it is not read.",
	Deps: []registry.EntryLike{TriangleColumnNamesDef},
})}

// ---------------------------------------------------------------------------
// The maps of the triangle
// ---------------------------------------------------------------------------

// TriangleInclusionDef — `triangle_inclusion(p, q, u)`: the map of the
// left term into the middle term at (p, q), the identity.
var TriangleInclusionDef = triangleInclusionDefThm{family.Define(registry.DefEntry{
	Name:  "TriangleInclusionDef",
	Key:   "prop_3e9a0ac4eb8750e4",
	Const: "triangle_inclusion",
	Type:  "num → num → (U → D) → U → D",
	Equations: []string{
		"∀p q:num. ∀u:(U → D). triangle_inclusion(p, q, u) = u",
	},
	Reading: "A function on P's names under the first tag is a function on all the " +
		"variables of Q(p, q) as it stands, so the inclusion moves nothing; it is named " +
		"so that the two maps of the triangle read side by side, " +
		"double_total_map(triangle_inclusion) beside double_total_map(triangle_projection).",
})}

// TriangleProjectionDef — `triangle_projection(p, q, u)`: the map of the
// middle term onto the right term at (p, q), u read at the second tags.
var TriangleProjectionDef = triangleProjectionDefThm{family.Define(registry.DefEntry{
	Name:  "TriangleProjectionDef",
	Key:   "prop_7273f68545aa8df",
	Const: "triangle_projection",
	Type:  "num → num → (U → D) → U → D",
	Equations: []string{
		"∀p q:num. ∀u:(U → D). triangle_projection(p, q, u) = (λt:U. u(universe_tag(1, t)))",
	},
	Reading: "On the middle term its values are finitely supported on the relative names " +
		"when the second tag is injective, and its kernel there is the left term exactly when " +
		"no name under the first tag is one under the second: both are cotangent_universe(R, " +
		"𝕌⟨A:U⟩) (TagInjective, TagsDisjoint), which every statement reading the triangle's " +
		"exactness carries. It reads no ring and no column: one function serves every (p, q).",
})}

// TriangleSectionDef — `triangle_section(N, u)`: the splitting of the
// projection, the function on the relative names u carried under the
// second tag, N's zero off the second tags.
var TriangleSectionDef = triangleSectionDefThm{family.Define(registry.DefEntry{
	Name:  "TriangleSectionDef",
	Key:   "prop_89cd6ad58c1121d9",
	Const: "triangle_section",
	Type:  "module_ops(C, D) → (U → D) → U → D",
	Equations: []string{
		"∀N:module_ops(C, D). ∀u:(U → D). " +
			"    triangle_section(N, u) = " +
			"    (λt:U. " +
			"        COND(t ∈ image(universe_tag(1), 𝕌⟨A:U⟩), " +
			"            u(inverse_on(𝕌⟨A:U⟩, universe_tag(1), t)), " +
			"            N.zero))",
	},
	Reading: "The projection after the section is the identity once the second tag is " +
		"injective, the untagged member being the preimage chosen under it. The section is linear " +
		"and splits the projection, but it is no map of double complexes: d_0 evaluates a second-tag " +
		"name of degree q + 1 to a member of Q(p, q), which in general involves first-tag variables.",
})}

// triangleRightHorizontalDef — `triangle_right_horizontal(R, S, f, T, N,
// p, q, u)`: the horizontal boundary out of (p, q) of the right term, the
// boundary of the chains with values in N on the simplicial set of
// relative names of row q, whose faces are the maps of names induced by
// P's faces.
var triangleRightHorizontalDef = triangleRightHorizontalDefThm{family.Define(registry.DefEntry{
	Name:  "triangleRightHorizontalDef",
	Key:   "prop_a77adc922952d2c2",
	Const: "triangle_right_horizontal",
	Type: "ring_ops(A) → " +
		"ring_ops(B) → " +
		"(A → B) → " +
		"ring_ops(C) → " +
		"module_ops(C, D) → " +
		"num → " +
		"num → " +
		"(U → D) → " +
		"U → " +
		"D",
	Equations: []string{
		"∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀T:ring_ops(C). " +
			"∀N:module_ops(C, D). " +
			"∀p q:num. " +
			"∀u:(U → D). " +
			"    triangle_right_horizontal(R, S, f, T, N, p, q, u) = " +
			"    tensor_boundary(T, " +
			"        N, " +
			"        λn:num. " +
			"            simplicial_boundary(T.add, " +
			"                T.zero, " +
			"                T.one, " +
			"                T.neg, " +
			"                T.mul, " +
			"                λm:num. λi:num. triangle_row_name(R, standard_face(R, S, f, m, i), q), " +
			"                n), " +
			"        p, " +
			"        u)",
	},
	Reading: "Row q of the right term is literally tensor_complex(T, λp:num. " +
		"relative_names(R, S, T, p, q), λn:num. simplicial_boundary(…, n), N), the chains " +
		"with values in N on the relative names of row q. It agrees with the projection of " +
		"the middle term's horizontal boundary: a horizontal face carries the variable of a " +
		"relative name to the variable of a relative name, whose Jacobian is the map of " +
		"names, and P's names go into the algebra on P's names, which the projection discards.",
	Deps: []registry.EntryLike{triangleRowNameDef},
})}

// TriangleRightVerticalDef — `triangle_right_vertical(R, S, f, T, g, N, p,
// q, u)`: the vertical boundary out of (p, q) of the right term, the
// middle term's boundary at u carried under the second tag, read at the
// second tags.
var TriangleRightVerticalDef = triangleRightVerticalDefThm{family.Define(registry.DefEntry{
	Name:  "TriangleRightVerticalDef",
	Key:   "prop_370c722556b0d275",
	Const: "triangle_right_vertical",
	Type:  towerType + "num → num → (U → D) → U → D",
	Equations: []string{
		towerBinders + "∀p q:num. ∀u:(U → D). triangle_right_vertical(R, S, f, T, g, N, p, q, u) = " +
			"triangle_projection(p, q - 1, triangle_vertical(R, S, f, T, g, N, p, q, triangle_section(N, u)))",
	},
	Reading: "The vertical faces fix P's variables, so the projection discards only the " +
		"derivatives in P's names of the faces of relative names; column p is the cotangent " +
		"complex of the resolution Q(p, •) of T over P's p-simplices. Out of q = 0 it is not read.",
	Deps: []registry.EntryLike{TriangleProjectionDef, TriangleVerticalDef, TriangleSectionDef},
})}

// TriangleLeftEpsDef — `triangle_left_eps(p, u)`: the augmentation of
// column p of the left term, a function on P's names under the first tag
// read at the untagged names, a term of degree p of the cotangent complex
// of S over R.
var TriangleLeftEpsDef = triangleLeftEpsDefThm{family.Define(registry.DefEntry{
	Name:  "TriangleLeftEpsDef",
	Key:   "prop_ffec5e62464eff93",
	Const: "triangle_left_eps",
	Type:  "num → (U → D) → U → D",
	Equations: []string{
		"∀p:num. ∀u:(U → D). triangle_left_eps(p, u) = (λx:U. u(universe_tag(0, x)))",
	},
	Reading: "On the left term at (p, 0) it is a bijection onto the functions on standard_names(R, " +
		"S, p) when the first tag is injective, so each column, constant with boundaries alternately " +
		"zero and the identity, is a resolution of that term. The edge map of the left total is " +
		"double_edge(triangle_left_eps), the coordinate p of a diagonal of degree p untagged.",
})}

// ---------------------------------------------------------------------------
// The three double complexes, each named once, and their totals
// ---------------------------------------------------------------------------

// TriangleLeftDoubleData — `triangle_left_double(R, S, f, T, g, N)`: the
// module, terms and boundaries of the left double complex, named once
// among the arguments of double_complex, double_total and
// double_complex_map: the finitely supported functions on the whole host
// as the module, the left terms, and the middle term's two boundaries.
var TriangleLeftDoubleData = family.Tuple(
	"triangle_left_double",
	[]string{"R", "S", "f", "T", "g", "N"},
	"finite_supp_module(N, 𝕌⟨A:U⟩)",
	"triangle_left(R, S, N)",
	"triangle_horizontal(R, S, f, T, g, N)",
	"triangle_vertical(R, S, f, T, g, N)")

// TriangleMiddleDoubleData — `triangle_middle_double(R, S, f, T, g, N)`:
// the module, terms and boundaries of the middle double complex.
var TriangleMiddleDoubleData = family.Tuple(
	"triangle_middle_double",
	[]string{"R", "S", "f", "T", "g", "N"},
	"finite_supp_module(N, 𝕌⟨A:U⟩)",
	"triangle_middle(R, S, T, N)",
	"triangle_horizontal(R, S, f, T, g, N)",
	"triangle_vertical(R, S, f, T, g, N)")

// TriangleRightDoubleData — `triangle_right_double(R, S, f, T, g, N)`: the
// module, terms and boundaries of the right double complex.
var TriangleRightDoubleData = family.Tuple(
	"triangle_right_double",
	[]string{"R", "S", "f", "T", "g", "N"},
	"finite_supp_module(N, 𝕌⟨A:U⟩)",
	"triangle_right(R, S, T, N)",
	"triangle_right_horizontal(R, S, f, T, N)",
	"triangle_right_vertical(R, S, f, T, g, N)")

// TriangleLeftTotalDef — `triangle_left_total(R, S, f, T, g, N)`: the
// total complex of the left double complex, the alternating signs of T.
var TriangleLeftTotalDef = triangleLeftTotalDefThm{family.Define(registry.DefEntry{
	Name:  "TriangleLeftTotalDef",
	Key:   "prop_99fed17adf5aa2ca",
	Const: "triangle_left_total",
	Type:  towerType + "complex_ops(C, num → U → D)",
	Equations: []string{
		towerBinders + "triangle_left_total(R, S, f, T, g, N) = double_total(finite_supp_module(N, 𝕌⟨A:U⟩), triangle_left(R, S, N), " +
			"triangle_horizontal(R, S, f, T, g, N), triangle_vertical(R, S, f, T, g, N), alternating_sign(T.one, T.neg))",
	},
	Reading: "A complex over T whose homology is that of the cotangent complex of S over R " +
		"with coefficients in N: the edge map double_edge(triangle_left_eps) is a quasi-isomorphism.",
	Deps: []registry.EntryLike{triangleLeftDef, triangleHorizontalDef, TriangleVerticalDef},
})}

// TriangleMiddleTotalDef — `triangle_middle_total(R, S, f, T, g, N)`: the
// total complex of the middle double complex.
var TriangleMiddleTotalDef = triangleMiddleTotalDefThm{family.Define(registry.DefEntry{
	Name:  "TriangleMiddleTotalDef",
	Key:   "prop_492a496fdcc10eec",
	Const: "triangle_middle_total",
	Type:  towerType + "complex_ops(C, num → U → D)",
	Equations: []string{
		towerBinders + "triangle_middle_total(R, S, f, T, g, N) = double_total(finite_supp_module(N, 𝕌⟨A:U⟩), triangle_middle(R, S, T, N), " +
			"triangle_horizontal(R, S, f, T, g, N), triangle_vertical(R, S, f, T, g, N), alternating_sign(T.one, T.neg))",
	},
	Reading: "Its homology is that of the cotangent complex of T over R, through the double " +
		"complex with constant rows: no map runs between the two directly, the comparison is a zigzag.",
	Deps: []registry.EntryLike{triangleMiddleDef, triangleHorizontalDef, TriangleVerticalDef},
})}

// TriangleRightTotalDef — `triangle_right_total(R, S, f, T, g, N)`: the
// total complex of the right double complex.
var TriangleRightTotalDef = triangleRightTotalDefThm{family.Define(registry.DefEntry{
	Name:  "TriangleRightTotalDef",
	Key:   "prop_f501287db7113a3d",
	Const: "triangle_right_total",
	Type:  towerType + "complex_ops(C, num → U → D)",
	Equations: []string{
		towerBinders + "triangle_right_total(R, S, f, T, g, N) = double_total(finite_supp_module(N, 𝕌⟨A:U⟩), triangle_right(R, S, T, N), " +
			"triangle_right_horizontal(R, S, f, T, N), triangle_right_vertical(R, S, f, T, g, N), alternating_sign(T.one, T.neg))",
	},
	Reading: "Its homology is that of the cotangent complex of T over S: the edge " +
		"map reading the coordinate 0 through the rows' augmentation is a quasi-isomorphism.",
	Deps: []registry.EntryLike{
		triangleRightDef,
		triangleRightHorizontalDef,
		TriangleRightVerticalDef,
	},
})}

// ---------------------------------------------------------------------------
// The three double complexes and the short exact sequence
// ---------------------------------------------------------------------------

// TriangleMiddleDouble — in a universe for the tower, the middle term with
// the Jacobians of Q's faces is a double complex over T.
var TriangleMiddleDouble = triangleMiddleDoubleThm{family.Add(registry.ProofEntry{
	Name: "TriangleMiddleDouble",
	Key:  "prop_eb8a073df82154b7",
	Reading: "Column p is the differential complex of the polynomial resolution " +
		"Q(p, •) of T over R and each horizontal face the Jacobian of a map of such " +
		"columns covering the identity of T: the double complex is assembled from those " +
		"two facts of the differential complexes, nothing particular to the triangle.",
	Deps: []registry.EntryLike{
		triangleMiddleDef,
		triangleHorizontalDef,
		TriangleVerticalDef,
		TriangleColumnNamesDef,
		chain_complex.DoubleComplex,
		function_module.FiniteSuppModuleOn,
		function_module.FiniteSuppModuleDef,
		cotangent_complex.DifferentialComplexChain,
		cotangent_complex.DifferentialComplexDef,
		cotangent_complex.DifferentialMapChainMap,
		cotangent_complex.DifferentialMapCompose,
		cotangent_complex.DifferentialMapDef,
		standard_resolution.RelativeColumnAugmented,
		standard_resolution.RelativeHorizontalHom,
		standard_resolution.RelativeDirectionsCommute,
		standard_resolution.RelativeHorizontalSimplicial,
		standard_resolution.RelativeAugmentationC,
		partial_derivative.JacobianCongruence,
		simplicial_module.FaceBoundaryDef,
		comm_ring.AlternatingSignDef,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀T:ring_ops(C). " +
			"∀g:(B → C). " +
			"∀N:module_ops(C, D).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"cotangent_universe(T, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"ring_homomorphism(S, T, g)",
			"module_on(T, N)",
		},
		Conclusion: "double_complex(T, triangle_middle_double(R, S, f, T, g, N))",
	},
		"each term is finite_supp(N, triangle_column_names(R, S, T, p, q)), a submodule of "+
			"finite_supp_module(N, 𝕌) (FiniteSuppModuleOn). Column p with the vertical boundary is the "+
			"differential complex of the augmented column (TriangleVerticalDef, RelativeColumnAugmented), "+
			"so the vertical boundaries are linear with square zero (DifferentialComplexChain). Each "+
			"horizontal face is differential_map at the map of columns induced by P's face, a simplicial "+
			"algebra map (RelativeHorizontalHom, RelativeDirectionsCommute) covering the identity of T "+
			"(RelativeAugmentationC), so a chain map of the columns (DifferentialMapChainMap): the "+
			"alternating sums commute with the vertical boundary. The horizontal square to zero is the "+
			"alternating double sum of composites of faces, each the Jacobian of a composite "+
			"(DifferentialMapCompose), cancelling in pairs by P's face identities on the variables "+
			"(RelativeHorizontalSimplicial, JacobianCongruence)"),
})}

// LeftColumnsConstant — on the left term every vertical face is the
// identity, so the vertical boundary is zero out of odd degrees and the
// identity out of even ones.
var LeftColumnsConstant = leftColumnsConstantThm{family.Add(registry.ProofEntry{
	Name: "LeftColumnsConstant",
	Key:  "prop_b2ae6c23cdeecbf7",
	Reading: "The left term is the same in every vertical degree and its columns are M ← M " +
		"← M ← … with boundaries 0, id, 0, id, …: exact above degree 0, and in degree 0 every " +
		"function is a cycle and only zero a boundary. The first conjunct is read at j ≤ q + 1, " +
		"the faces out of degree q + 1. A first-tag variable is fixed by the evaluating face " +
		"d_0, a first-tag name not being in tag₁'s image, and by the renaming faces; untagging, " +
		"injective with zero boundary into degree 0, makes each augmented column exact.",
	Deps: []registry.EntryLike{
		triangleLeftDef,
		TriangleVerticalDef,
		TriangleColumnNamesDef,
		cotangent_complex.DifferentialFaceDef,
		cotangent_complex.DifferentialBoundaryDef,
		standard_resolution.RelativeVerticalFixesBase,
		standard_resolution.RelativeColumnAugmented,
		simplicial_ring.AugmentationAtHom,
		partial_derivative.PartialVar,
		partial_derivative.JacobianDelta,
		simplicial_module.FaceBoundaryDef,
		comm_ring.AlternatingSignDef,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀T:ring_ops(C). " +
			"∀g:(B → C). " +
			"∀N:module_ops(C, D).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"cotangent_universe(T, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"ring_homomorphism(S, T, g)",
			"module_on(T, N)",
		},
		Conclusion: "(∀p q j:num. ∀u:(U → D). " +
			"    j ≤ q + 1 ∧ u ∈ triangle_left(R, S, N, p, q + 1) ⇒ " +
			"    differential_face(R, " +
			"        triangle_column_names(R, S, T, p), " +
			"        relative_vertical_face(R, S, f, T, g, p), " +
			"        relative_vertical_eps(R, S, f, T, g, p), " +
			"        N, " +
			"        q + 1, " +
			"        j, " +
			"        u) = " +
			"    u) ∧ " +
			"(∀p q:num. ∀u:(U → D). " +
			"    u ∈ triangle_left(R, S, N, p, 2 * q + 1) ⇒ " +
			"    triangle_vertical(R, S, f, T, g, N, p, 2 * q + 1, u) = fun_zero(N.zero)) ∧ " +
			"(∀p q:num. ∀u:(U → D). " +
			"    u ∈ triangle_left(R, S, N, p, 2 * q + 2) ⇒ " +
			"    triangle_vertical(R, S, f, T, g, N, p, 2 * q + 2, u) = u)",
	},
		"the vertical faces fix the variables of P's names under the first tag "+
			"(RelativeVerticalFixesBase), so at a first-tag name s the face is var(s), whose partial at t "+
			"is [t = s] (PartialVar), and the augmentation in degree q sends one to T.one "+
			"(AugmentationAtHom at RelativeColumnAugmented); the Jacobian therefore sends u to Σ_s [t = s] "+
			"• u(s) = u(t) at every name t of the target, zero at the second-tag names (JacobianDelta). "+
			"The boundary is then Σ_{j ≤ n} (−1)^j u (TriangleVerticalDef, DifferentialBoundaryDef, "+
			"FaceBoundaryDef), zero for odd n and u for even n (AlternatingSignDef)"),
})}

// TriangleLeftDouble — in a universe for the tower, the left term is a
// double complex under the middle term's boundaries.
var TriangleLeftDouble = triangleLeftDoubleThm{family.Add(registry.ProofEntry{
	Name: "TriangleLeftDouble",
	Key:  "prop_74eec24929087fd1",
	Reading: "The left term is a sub-double complex of the middle one: the same module " +
		"and the same boundaries, read on the functions on P's names. A horizontal face sends " +
		"a first-tag variable to map_tag₀ of P's face, a polynomial in first-tag names only, " +
		"so the horizontal boundary keeps the left term in every row q: augmentation_at(·, q) " +
		"acts on first-tag variables as g ∘ standard_to_base(p), whatever q is.",
	Deps: []registry.EntryLike{
		TriangleMiddleDouble,
		LeftColumnsConstant,
		triangleLeftDef,
		triangleHorizontalDef,
		chain_complex.DoubleComplex,
		function_module.FiniteSuppModuleOn,
		standard_resolution.RelativeBaseInclusionNatural,
		partial_derivative.JacobianBlockTriangular,
		partial_derivative.PartialSupportFinite,
		simplicial_ring.TagsDisjoint,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀T:ring_ops(C). " +
			"∀g:(B → C). " +
			"∀N:module_ops(C, D).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"cotangent_universe(T, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"ring_homomorphism(S, T, g)",
			"module_on(T, N)",
		},
		Conclusion: "double_complex(T, triangle_left_double(R, S, f, T, g, N))",
	},
		"each left term is a submodule of the middle one at the same (p, q). A horizontal face "+
			"carries the variable of a name of P under the first tag into the algebra on P's names "+
			"under the first tag (RelativeBaseInclusionNatural), whose derivatives in the second-tag "+
			"names vanish (PartialSupportFinite, TagsDisjoint), so the horizontal boundary carries "+
			"the left term into itself (JacobianBlockTriangular); the vertical boundary is zero or "+
			"the identity on it (LeftColumnsConstant). The linearity, the squares to zero and the "+
			"commuting square are the middle term's (TriangleMiddleDouble) restricted"),
})}

// TriangleDegreewiseShortExact — at every (p, q) the left term includes
// into the middle one, the projection maps the middle term onto the right
// one with the left term as its kernel, and the section splits it.
var TriangleDegreewiseShortExact = triangleDegreewiseShortExactThm{family.Add(registry.ProofEntry{
	Name: "TriangleDegreewiseShortExact",
	Key:  "prop_b380facc8376b65d",
	Reading: "The disjointness of the two tags (TagsDisjoint) is load-bearing for the kernel of the " +
		"projection being the left term: without it a name of P could also be a relative name under the " +
		"second tag, and the projection would not vanish on the left term. TagInjective is load-bearing " +
		"for the projection's values being finitely supported and zero off relative_names(p, q), for " +
		"the section landing back in the middle term, and for projection ∘ section = id; both come from " +
		"the third conjunct of any one of the three universes, card_le(prod(num, U), U). The section is " +
		"linear and splits the projection but is no map of double complexes. At q = 0 the right term is " +
		"finite_supp(N, image(carrier_tag(T.carrier), T.carrier)) in every column.",
	Deps: []registry.EntryLike{
		triangleLeftDef,
		triangleMiddleDef,
		triangleRightDef,
		TriangleColumnNamesDef,
		TriangleInclusionDef,
		TriangleProjectionDef,
		TriangleSectionDef,
		simplicial_ring.TagInjective,
		simplicial_ring.TagsDisjoint,
		functions.InverseOnLeft,
		function_module.FiniteSuppDef,
		function_module.FiniteSuppModuleDef,
		module_homomorphism.ExactAtDef,
		module_homomorphism.ModuleHomomorphismDef,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀T:ring_ops(C). " +
			"∀g:(B → C). " +
			"∀N:module_ops(C, D). " +
			"∀p q:num.",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"cotangent_universe(T, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"ring_homomorphism(S, T, g)",
			"module_on(T, N)",
		},
		Conclusion: "injective_on(triangle_left⟨U:U⟩(R, S, N, p, q), triangle_inclusion(p, q)) ∧ " +
			"exact_at(fun_zero(N.zero), " +
			"    triangle_left⟨U:U⟩(R, S, N, p, q), " +
			"    triangle_middle(R, S, T, N, p, q), " +
			"    triangle_inclusion(p, q), " +
			"    triangle_projection(p, q)) ∧ " +
			"image(triangle_projection⟨U:U⟩(p, q), triangle_middle(R, S, T, N, p, q)) = " +
			"triangle_right(R, S, T, N, p, q) ∧ " +
			"module_homomorphism(T, " +
			"    restrict_module(finite_supp_module(N, 𝕌⟨A:U⟩), triangle_right(R, S, T, N, p, q)), " +
			"    restrict_module(finite_supp_module(N, 𝕌⟨A:U⟩), triangle_middle(R, S, T, N, p, q)), " +
			"    triangle_section(N)) ∧ " +
			"(∀u:(U → D). " +
			"    u ∈ triangle_right(R, S, T, N, p, q) ⇒ triangle_projection(p, q, triangle_section(N, u)) = u)",
	},
		"the inclusion is the identity. A function on the variables of Q(p, q) read at the second "+
			"tags is zero exactly when it vanishes on the second-tag names, that is when it is supported "+
			"on P's names: no first-tag name is a second-tag one (TagsDisjoint). It is finitely "+
			"supported on the relative names of (p, q) since the second tag is injective (TagInjective, "+
			"FiniteSuppDef), and every such function is read off its section, the untagged member being "+
			"the chosen preimage (InverseOnLeft); the section is pointwise, so linear"),
})}

// TriangleInclusionDoubleMap — the inclusion is a map of double complexes
// from the left term to the middle term.
var TriangleInclusionDoubleMap = triangleInclusionDoubleMapThm{family.Add(registry.ProofEntry{
	Name: "TriangleInclusionDoubleMap",
	Key:  "prop_b2a61e99eb661103",
	Deps: []registry.EntryLike{
		TriangleLeftDouble,
		TriangleMiddleDouble,
		TriangleInclusionDef,
		chain_complex.DoubleComplexMapDef,
		module_homomorphism.ModuleHomomorphismDef,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀T:ring_ops(C). " +
			"∀g:(B → C). " +
			"∀N:module_ops(C, D).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"cotangent_universe(T, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"ring_homomorphism(S, T, g)",
			"module_on(T, N)",
		},
		Conclusion: "double_complex_map(T, " +
			"    triangle_left_double(R, S, f, T, g, N), " +
			"    triangle_middle_double(R, S, f, T, g, N), " +
			"    triangle_inclusion)",
	},
		"the identity is linear from each left term into the middle term at the "+
			"same (p, q), both cut out of finite_supp_module(N, 𝕌), and it commutes "+
			"with the boundaries, which are the same functions (TriangleLeftDouble)"),
})}

// TriangleProjectionDoubleMap — the projection is a map of double
// complexes from the middle term to the right term.
var TriangleProjectionDoubleMap = triangleProjectionDoubleMapThm{family.Add(registry.ProofEntry{
	Name: "TriangleProjectionDoubleMap",
	Key:  "prop_a152f01f23deb3c4",
	Reading: "The horizontal square is the content: the Jacobian of a horizontal face " +
		"at a second-tag variable is the map of names triangle_row_name(standard_face(p, " +
		"i), q), with coefficient T.one or T.zero, so read at the second tags the boundary " +
		"is the chains' boundary, and P's variables go to polynomials in P's names, which " +
		"the projection discards. The vertical square holds because x − section(projection " +
		"x) is supported on first-tag names, which the vertical boundary keeps there.",
	Deps: []registry.EntryLike{
		TriangleMiddleDouble,
		TriangleDegreewiseShortExact,
		LeftColumnsConstant,
		TriangleProjectionDef,
		triangleRightHorizontalDef,
		TriangleRightVerticalDef,
		triangleRowNameDef,
		chain_complex.DoubleComplexMapDef,
		standard_resolution.RelativeHorizontalMapDef,
		standard_resolution.RelativeBaseInclusionNatural,
		partial_derivative.JacobianDelta,
		partial_derivative.PartialVar,
		partial_derivative.PartialSupportFinite,
		tor_ext.TensorBoundaryDef,
		simplicial_chain.SimplicialBoundaryDef,
		simplicial_ring.TagsDisjoint,
		simplicial_ring.TagInjective,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀T:ring_ops(C). " +
			"∀g:(B → C). " +
			"∀N:module_ops(C, D).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"cotangent_universe(T, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"ring_homomorphism(S, T, g)",
			"module_on(T, N)",
		},
		Conclusion: "double_complex_map(T, " +
			"    triangle_middle_double(R, S, f, T, g, N), " +
			"    triangle_right_double(R, S, f, T, g, N), " +
			"    triangle_projection)",
	},
		"the projection is linear and onto each right term (TriangleDegreewiseShortExact). "+
			"Horizontally: a horizontal face carries the variable of the second tag of a relative name z "+
			"to the variable of the second tag of triangle_row_name(R, h, q, z) (RelativeHorizontalMapDef, "+
			"triangleRowNameDef), whose Jacobian is the generator there (JacobianDelta, PartialVar), and "+
			"the variable of a name of P under the first tag into the algebra on P's names "+
			"(RelativeBaseInclusionNatural), whose second-tag derivatives vanish (PartialSupportFinite, "+
			"TagsDisjoint); so the projection of the boundary is the chains' boundary of the projection "+
			"(TensorBoundaryDef, SimplicialBoundaryDef, TagInjective). Vertically: x and the section of "+
			"its projection differ by a function on P's names, which the vertical boundary keeps there "+
			"(LeftColumnsConstant) and the projection kills, so the projection of the boundary of x is the "+
			"right term's boundary of its projection (TriangleRightVerticalDef)"),
})}

// TriangleRightDouble — in a universe for the tower, the right term is a
// double complex over T.
var TriangleRightDouble = triangleRightDoubleThm{family.Add(registry.ProofEntry{
	Name: "TriangleRightDouble",
	Key:  "prop_b04d428f98b11781",
	Reading: "It is the quotient of the middle double complex by the left one: " +
		"the projection is onto in every bidegree and carries the middle boundaries " +
		"to the right ones, so every identity of the right term is read through it. " +
		"Its rows are the chains with values in N on simplicial sets of names.",
	Deps: []registry.EntryLike{
		TriangleMiddleDouble,
		TriangleLeftDouble,
		TriangleDegreewiseShortExact,
		TriangleProjectionDoubleMap,
		triangleRightDef,
		triangleRightHorizontalDef,
		TriangleRightVerticalDef,
		chain_complex.DoubleComplex,
		function_module.FiniteSuppModuleOn,
		tor_ext.TensorComplex,
		simplicial_module.SimplicialChainsFreeComplex,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀T:ring_ops(C). " +
			"∀g:(B → C). " +
			"∀N:module_ops(C, D).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"cotangent_universe(T, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"ring_homomorphism(S, T, g)",
			"module_on(T, N)",
		},
		Conclusion: "double_complex(T, triangle_right_double(R, S, f, T, g, N))",
	},
		"each right term is a submodule of finite_supp_module(N, 𝕌) (FiniteSuppModuleOn). Every "+
			"right function is the projection of its section (TriangleDegreewiseShortExact) and the "+
			"projection carries the middle boundaries to the right ones (TriangleProjectionDoubleMap), "+
			"so linearity, the two squares to zero and the commuting square are the middle term's "+
			"(TriangleMiddleDouble) read through the projection; the horizontal square to zero is also "+
			"that of the chains on a simplicial set (TensorComplex at SimplicialChainsFreeComplex)"),
})}

// TriangleTotalShortExact — the totals of the three double complexes form
// a short exact sequence of complexes over T under the inclusion and the
// projection.
var TriangleTotalShortExact = triangleTotalShortExactThm{family.Add(registry.ProofEntry{
	Name: "TriangleTotalShortExact",
	Key:  "prop_dc2e4c98ccd8d78f",
	Deps: []registry.EntryLike{
		TriangleLeftDouble,
		TriangleMiddleDouble,
		TriangleRightDouble,
		TriangleInclusionDoubleMap,
		TriangleProjectionDoubleMap,
		TriangleDegreewiseShortExact,
		TriangleLeftTotalDef,
		TriangleMiddleTotalDef,
		TriangleRightTotalDef,
		chain_complex.DoubleShortExactTotal,
		comm_ring.AlternatingSignDef,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀T:ring_ops(C). " +
			"∀g:(B → C). " +
			"∀N:module_ops(C, D).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"cotangent_universe(T, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"ring_homomorphism(S, T, g)",
			"module_on(T, N)",
		},
		Conclusion: "short_exact_complexes(T, " +
			"    triangle_left_total(R, S, f, T, g, N), " +
			"    triangle_middle_total(R, S, f, T, g, N), " +
			"    triangle_right_total⟨U:U⟩(R, S, f, T, g, N), " +
			"    double_total_map(triangle_inclusion), " +
			"    double_total_map(triangle_projection))",
	},
		"DoubleShortExactTotal at the three double complexes and the two maps "+
			"(TriangleLeftDouble, TriangleMiddleDouble, TriangleRightDouble, "+
			"TriangleInclusionDoubleMap, TriangleProjectionDoubleMap), short exact at "+
			"every (p, q) (TriangleDegreewiseShortExact), the totals unfolded by their "+
			"definitions to double_total at T's alternating sign (AlternatingSignDef)"),
})}

// ---------------------------------------------------------------------------
// The left total computes the cotangent complex of S over R
// ---------------------------------------------------------------------------

// LeftTotalAugmented — the hypotheses of the augmented assembly along the
// columns hold for the left double complex, augmented by untagging onto
// the cotangent complex of S over R.
var LeftTotalAugmented = leftTotalAugmentedThm{family.Add(registry.ProofEntry{
	Name: "LeftTotalAugmented",
	Key:  "prop_bd80c3a732caabf5",
	Reading: "The five conjuncts are AugmentedAssembly's, read at the left double complex, " +
		"the cotangent complex of S over R with coefficients in N as E and triangle_left_eps as " +
		"the augmentation. The last one is the content: on P's names the horizontal face of Q " +
		"is P's face carried by the first tag and Q's augmentation is g after P's, so untagging " +
		"carries the left term's boundary in vertical degree 0 to the cotangent complex's. " +
		"Exactness at (p, 0) is the injectivity of untagging (TagInjective), the vertical " +
		"boundary out of degree 1 being d_0 − d_1 = 0 on the left term. The square in the fifth " +
		"conjunct holds because relative_vertical_eps(p) ∘ map_tag₀ = g ∘ standard_to_base(p).",
	Deps: []registry.EntryLike{
		LeftColumnsConstant,
		TriangleLeftEpsDef,
		triangleLeftDef,
		triangleHorizontalDef,
		cotangent_complex.CotangentComplexDef,
		cotangent_complex.DifferentialComplexDef,
		cotangent_complex.DifferentialBoundaryDef,
		cotangent_complex.DifferentialMapDef,
		cotangent_complex.DifferentialFaceDef,
		standard_resolution.RelativeBaseInclusionNatural,
		standard_resolution.RelativeVerticalEpsHom,
		partial_derivative.JacobianCompose,
		partial_derivative.JacobianCongruence,
		simplicial_ring.TagInjective,
		simplicial_ring.AugmentationAtFaceIndependent,
		function_module.FiniteSuppDef,
		module_homomorphism.ExactAtDef,
		module_homomorphism.ModuleHomomorphismDef,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀T:ring_ops(C). " +
			"∀g:(B → C). " +
			"∀N:module_ops(C, D).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"cotangent_universe(T, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"ring_homomorphism(S, T, g)",
			"module_on(T, N)",
		},
		Conclusion: "(∀p:num. " +
			"    module_homomorphism(T, " +
			"        restrict_module(finite_supp_module(N, 𝕌⟨A:U⟩), triangle_left(R, S, N, p, 0)), " +
			"        complex_module(cotangent_complex(R, S, f, T, g, N), p), " +
			"        triangle_left_eps(p))) ∧ " +
			"(∀p:num. " +
			"    image(triangle_left_eps⟨U:U⟩(p), triangle_left(R, S, N, p, 0)) = " +
			"    cotangent_complex(R, S, f, T, g, N).terms(p)) ∧ " +
			"(∀p:num. " +
			"    exact_at(cotangent_complex(R, S, f, T, g, N).zero, " +
			"        triangle_left⟨U:U⟩(R, S, N, p, 1), " +
			"        triangle_left(R, S, N, p, 0), " +
			"        triangle_vertical(R, S, f, T, g, N, p, 1), " +
			"        triangle_left_eps(p))) ∧ " +
			"(∀p q:num. " +
			"    exact_at(finite_supp_module(N, 𝕌⟨A:U⟩).zero, " +
			"        triangle_left(R, S, N, p, q + 2), " +
			"        triangle_left(R, S, N, p, q + 1), " +
			"        triangle_vertical(R, S, f, T, g, N, p, q + 2), " +
			"        triangle_vertical(R, S, f, T, g, N, p, q + 1))) ∧ " +
			"(∀p:num. ∀x:(U → D). " +
			"    x ∈ triangle_left(R, S, N, p + 1, 0) ⇒ " +
			"    cotangent_complex(R, S, f, T, g, N).d(p + 1, triangle_left_eps(p + 1, x)) = " +
			"    triangle_left_eps(p, triangle_horizontal(R, S, f, T, g, N, p + 1, 0, x)))",
	},
		"untagging is a linear bijection from the functions on P's names under the first tag onto those "+
			"on standard_names(R, S, p), the first tag injective (TagInjective, FiniteSuppDef), and those "+
			"are the cotangent complex's terms (CotangentComplexDef, DifferentialComplexDef). The columns "+
			"are exact by LeftColumnsConstant: out of degree 1 the boundary is zero, matching the injective "+
			"augmentation, and above it zero and the identity alternate. For the square: on P's variables "+
			"the horizontal face is P's face carried by the first tag (RelativeBaseInclusionNatural) and "+
			"the augmentation of column p in degree 0 is g after P's augmentation in degree p "+
			"(RelativeVerticalEpsHom), so untagged each Jacobian is the cotangent complex's face, the "+
			"coefficients λu. g(standard_eps(R, S, f, u)) read in degree p (DifferentialBoundaryDef, "+
			"DifferentialFaceDef, AugmentationAtFaceIndependent, JacobianCompose, JacobianCongruence)"),
})}

// LeftTotalQuasiIsomorphism — the left total maps quasi-isomorphically
// onto the cotangent complex of S over R with coefficients in N, by
// untagging the coordinate on the edge.
var LeftTotalQuasiIsomorphism = leftTotalQuasiIsomorphismThm{family.Add(registry.ProofEntry{
	Name:    "LeftTotalQuasiIsomorphism",
	Key:     "prop_af6293f46acadaf4",
	Reading: "The edge map reads the corner (n, 0) of a diagonal of degree n and untags it.",
	Deps: []registry.EntryLike{
		LeftTotalAugmented,
		TriangleLeftDouble,
		TriangleLeftTotalDef,
		chain_complex.AugmentedAssembly,
		chain_complex.QuasiIsomorphismDef,
		chain_complex.DoubleEdgeDef,
		cotangent_complex.CotangentChainComplex,
		comm_ring.AlternatingSignDef,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀T:ring_ops(C). " +
			"∀g:(B → C). " +
			"∀N:module_ops(C, D).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"cotangent_universe(T, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"ring_homomorphism(S, T, g)",
			"module_on(T, N)",
		},
		Conclusion: "quasi_isomorphism(T, " +
			"    triangle_left_total(R, S, f, T, g, N), " +
			"    cotangent_complex(R, S, f, T, g, N), " +
			"    double_edge(triangle_left_eps⟨U:U⟩))",
	},
		"AugmentedAssembly at TriangleLeftDouble over T, the left total being double_total at T's "+
			"alternating sign (TriangleLeftTotalDef, AlternatingSignDef), E the cotangent complex of S over "+
			"R, a chain complex over T (CotangentChainComplex), and its hypotheses LeftTotalAugmented; its "+
			"conclusion, a chain map inducing isomorphisms of the homology modules, is QuasiIsomorphismDef"),
})}
