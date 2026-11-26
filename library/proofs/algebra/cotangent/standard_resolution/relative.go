// relative.go — the relative standard resolution of an algebra T over the
// standard resolution P of S over R, T an algebra over S through g: a
// bisimplicial algebra Q whose column p is the standard resolution of T
// over P's p-simplices, written without changing the coefficient ring —
// the names of P in degree p enter the names of Q under the first tag,
// and the relative names of the vertical resolution, the tags of T's
// elements in vertical degree 0 and the members of the column's algebra
// below in vertical degree q + 1, enter under the second tag. The
// relative names themselves carry no tag, so in vertical degree 0 they
// are the names of degree 0 of the standard resolution of T over S. The
// vertical faces and degeneracies are the standard resolution's, acting
// through the second tag and fixing the first; the horizontal ones are
// induced by P's faces and degeneracies on the first tag and act on the
// second recursively in the vertical degree. Each column is augmented
// over T, the row of P's 0-simplices over the standard resolution of T
// over S, and the standard resolution of T over R maps into every
// column. In a universe for R, S and T the two directions are simplicial
// algebras that commute, a bisimplicial set; every column is a
// polynomial resolution of T, made acyclic by its extra degeneracy; the
// vertical structure fixes P's variables, the horizontal one extends P's
// maps along the inclusion of P under the first tag; and the row
// augmentation is an algebra map over f coequalizing the two faces of an
// edge and commuting with the vertical structure. The diagonal, the
// (n, n)-simplices with the faces and degeneracies of the two directions
// taken together, is a polynomial resolution of T over R, contracted by
// the diagonal of the columns' contractions, and both P under the first
// tag and the standard resolution of T over R map into it as simplicial
// algebras.

package standard_resolution

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/simplicial_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/free_algebra"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/simplicial/simplicial_homotopy"
	"github.com/euc-ai/xugo/library/proofs/simplicial/simplicial_module"
	"github.com/euc-ai/xugo/library/proofs/simplicial/simplicial_set"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// Names and simplices
// ---------------------------------------------------------------------------

// RelativeNamesDef — `relative_names(R, S, T, p, q)`: the relative names
// of vertical degree q in column p of the relative standard resolution,
// the names that are not P's, untagged — in degree 0 the tags of T's
// elements, the names of degree 0 of the standard resolution of T over
// S, in degree q + 1 the members of the column's algebra of degree q.
// They enter the column's names under the second tag.
var RelativeNamesDef = relativeNamesDefThm{family.Define(registry.DefEntry{
	Name:  "RelativeNamesDef",
	Key:   "prop_cf56b44a9e96970d",
	Const: "relative_names",
	Type:  "ring_ops(A) → ring_ops(B) → ring_ops(C) → num → num → set(U)",
	Equations: []string{
		"∀R:ring_ops(A). ∀S:ring_ops(B). ∀T:ring_ops(C). ∀p:num. " +
			"    relative_names(R, S, T, p, 0) = image(carrier_tag(T.carrier), T.carrier)",
		"∀R:ring_ops(A). ∀S:ring_ops(B). ∀T:ring_ops(C). ∀p:num. ∀q:num. " +
			"    relative_names(R, S, T, p, suc(q)) = " +
			"    universe_algebra(R, " +
			"        image(universe_tag(0), standard_names(R, S, p)) ∪ " +
			"        image(universe_tag(1), relative_names(R, S, T, p, q)))",
	},
	Reading: "In vertical degree 0 the names do not depend on the column p and are " +
		"those of the standard resolution of T over S, standard_names(S, T, 0); from degree " +
		"1 on they depend on the column through P's names. relative_names(R, S, T, p, q + " +
		"1) and relative_terms(R, S, T, p, q) are one set, unfolded from two definitions. A " +
		"relative name carries no tag: it enters the column's names under the second tag " +
		"and P's names under the first, so the two kinds are told apart once the tags are " +
		"injective with disjoint images, which cotangent_universe(R, 𝕌⟨A:U⟩) provides.",
	Deps: []registry.EntryLike{StandardNamesDef},
})}

// RelativeTermsDef — `relative_terms(R, S, T, p, q)`: the (p, q)-simplices
// of the relative standard resolution, the free algebra over R in the
// universe on P's names of degree p under the first tag and the relative
// names of (p, q) under the second.
var RelativeTermsDef = relativeTermsDefThm{family.Define(registry.DefEntry{
	Name:  "RelativeTermsDef",
	Key:   "prop_3b0dfbb3555aea32",
	Const: "relative_terms",
	Type:  "ring_ops(A) → ring_ops(B) → ring_ops(C) → num → num → set(U)",
	Equations: []string{
		"∀R:ring_ops(A). ∀S:ring_ops(B). ∀T:ring_ops(C). ∀p q:num. " +
			"    relative_terms(R, S, T, p, q) = " +
			"    universe_algebra(R, " +
			"        image(universe_tag(0), standard_names(R, S, p)) ∪ " +
			"        image(universe_tag(1), relative_names(R, S, T, p, q)))",
	},
	Reading: "The coefficient ring stays R: P's names of degree p enter under the first tag " +
		"and the relative names under the second, so the algebra is a copy of P's p-simplices " +
		"with the relative names adjoined as variables, read as one free algebra over R. The " +
		"structure maps f and g are not read; the faces and the augmentations read them.",
	Deps: []registry.EntryLike{RelativeNamesDef, StandardNamesDef},
})}

// ---------------------------------------------------------------------------
// The vertical structure: the standard resolution of T over each column
// ---------------------------------------------------------------------------

// relativeNameMapDef — `relative_name_map(h, z)`: the map of a column's
// names induced by a map h of the relative names — the second tag of w
// goes to the second tag of h(w), and every other name, P's under the
// first tag among them, is fixed.
var relativeNameMapDef = relativeNameMapDefThm{family.Define(registry.DefEntry{
	Name:  "relativeNameMapDef",
	Key:   "prop_6cdb8d068b11afcd",
	Const: "relative_name_map",
	Type:  "(U → U) → U → U",
	Equations: []string{
		"∀h:(U → U). ∀z:U. " +
			"    relative_name_map(h, z) = " +
			"    COND(z ∈ image(universe_tag(1), 𝕌⟨A:U⟩), " +
			"        universe_tag(1, h(inverse_on(𝕌⟨A:U⟩, universe_tag(1), z))), " +
			"        z)",
	},
	Reading: "The relative name w is read back as the preimage chosen under the second tag, so " +
		"relative_name_map(h, universe_tag(1, w)) = universe_tag(1, h(w)) asks the second tag to be " +
		"injective; the names of P, under the first tag, are fixed when the two tags have disjoint images.",
})}

// RelativeVerticalEpsDef — `relative_vertical_eps(R, S, f, T, g, p, u)`:
// the augmentation of column p over T, u in vertical degree 0 evaluated
// in T — each coefficient carried by g ∘ f, each name of P under the
// first tag read through P's augmentation in degree p and then g, and
// the second tag of each relative name of degree 0, the tag of an
// element of T, read back as that element.
var RelativeVerticalEpsDef = relativeVerticalEpsDefThm{family.Define(registry.DefEntry{
	Name:  "RelativeVerticalEpsDef",
	Key:   "prop_8c29415a8a733ba",
	Const: "relative_vertical_eps",
	Type:  "ring_ops(A) → ring_ops(B) → (A → B) → ring_ops(C) → (B → C) → num → U → C",
	Equations: []string{
		"∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B). ∀T:ring_ops(C). ∀g:(B → C). ∀p:num. ∀u:U. " +
			"    relative_vertical_eps(R, S, f, T, g, p, u) = " +
			"    universe_algebra_eval(R, " +
			"        T, " +
			"        λa:A. g(f(a)), " +
			"        λz:U. " +
			"            COND(z ∈ image(universe_tag(1), 𝕌⟨A:U⟩), " +
			"                inverse_on(T.carrier, " +
			"                    carrier_tag(T.carrier), " +
			"                    inverse_on(𝕌⟨A:U⟩, universe_tag(1), z)), " +
			"                g(standard_to_base(R, " +
			"                        S, " +
			"                        f, " +
			"                        p, " +
			"                        universe_algebra_var(R, inverse_on(𝕌⟨A:U⟩, universe_tag(0), z))))), " +
			"        u)",
	},
	Reading: "On P's names it is g after P's augmentation in degree p, so its restriction " +
		"to P's p-simplices, carried under the first tag, is the composite of P's augmentation " +
		"with g: T is an algebra over P's p-simplices through it. The tags are read back " +
		"through the preimages chosen under them, which needs the tags and the tag of T's " +
		"elements injective (cotangent_universe of R and of T) and the two tags' images disjoint.",
	Deps: []registry.EntryLike{StandardToBaseDef},
})}

// RelativeVerticalFaceDef — `relative_vertical_face(R, S, f, T, g, p, q,
// j, u)`: the vertical face j of column p on vertical degree q, a function
// of the whole host. In degree q + 1 the 0-th face evaluates the second
// tag of each relative name, a member of the algebra below, to that
// member, and keeps each other name as its variable; the face j + 1 is
// the map induced on the names by relative_name_map of the face j of
// degree q, acting on the relative names. In degree 0 it is the column's
// augmentation followed by the tag of T's elements, carrying the algebra
// of degree 0 onto the relative names of degree 0 — the map of relative
// names the last face of every degree is built on.
var RelativeVerticalFaceDef = relativeVerticalFaceDefThm{family.Define(registry.DefEntry{
	Name:  "RelativeVerticalFaceDef",
	Key:   "prop_1181265acaadf6ca",
	Const: "relative_vertical_face",
	Type:  "ring_ops(A) → ring_ops(B) → (A → B) → ring_ops(C) → (B → C) → num → num → num → U → U",
	Equations: []string{
		"∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B). ∀T:ring_ops(C). ∀g:(B → C). ∀p:num. " +
			"    relative_vertical_face(R, S, f, T, g, p, 0) = " +
			"    (λj:num. λu:U. carrier_tag(T.carrier, relative_vertical_eps(R, S, f, T, g, p, u)))",
		"∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B). ∀T:ring_ops(C). ∀g:(B → C). ∀p:num. ∀q:num. " +
			"    relative_vertical_face(R, S, f, T, g, p, suc(q)) = " +
			"    (λj:num. λu:U. " +
			"        COND(j = 0, " +
			"            universe_algebra_eval(R, " +
			"                universe_algebra_ring(R, 𝕌⟨A:U⟩), " +
			"                universe_algebra_const(R), " +
			"                λz:U. " +
			"                    COND(z ∈ image(universe_tag(1), 𝕌⟨A:U⟩), " +
			"                        inverse_on(𝕌⟨A:U⟩, universe_tag(1), z), " +
			"                        universe_algebra_var(R, z)), " +
			"                u), " +
			"            universe_algebra_map(R, " +
			"                R, " +
			"                λa:A. a, " +
			"                relative_name_map(relative_vertical_face(R, S, f, T, g, p, q, j - 1)), " +
			"                u)))",
	},
	Reading: "The faces fix every variable of P's names, so each is an algebra map " +
		"over P's p-simplices, and the column is the standard resolution of T over them " +
		"with P's names as variables. The values at vertical degree 0 are not a face of " +
		"simplices; they make the last face of degree 1 the column's augmentation on the " +
		"variables. Past the top index the values are those of a lower face and are not read.",
	Deps: []registry.EntryLike{RelativeVerticalEpsDef, relativeNameMapDef},
})}

// RelativeVerticalDegeneracyDef — `relative_vertical_degeneracy(R, q, j,
// u)`: the vertical degeneracy j on vertical degree q, the same in every
// column — the 0-th the map induced by relative_name_map of carrying a
// relative name w to the variable of its second tag, a relative name
// one degree up, the degeneracy j + 1 of degree q + 1 the map induced by
// relative_name_map of the degeneracy j of degree q; P's names are
// fixed.
var RelativeVerticalDegeneracyDef = relativeVerticalDegeneracyDefThm{family.Define(registry.DefEntry{
	Name:  "RelativeVerticalDegeneracyDef",
	Key:   "prop_f6e6b3f10050c6f0",
	Const: "relative_vertical_degeneracy",
	Type:  "ring_ops(A) → num → num → U → U",
	Equations: []string{
		"∀R:ring_ops(A). " +
			"    relative_vertical_degeneracy(R, 0) = " +
			"    (λj:num. λu:U. " +
			"        universe_algebra_map(R, " +
			"            R, " +
			"            λa:A. a, " +
			"            relative_name_map(λw:U. universe_algebra_var(R, universe_tag(1, w))), " +
			"            u))",
		"∀R:ring_ops(A). ∀q:num. " +
			"    relative_vertical_degeneracy(R, suc(q)) = " +
			"    (λj:num. λu:U. " +
			"        COND(j = 0, " +
			"            universe_algebra_map(R, " +
			"                R, " +
			"                λa:A. a, " +
			"                relative_name_map(λw:U. universe_algebra_var(R, universe_tag(1, w))), " +
			"                u), " +
			"            universe_algebra_map(R, " +
			"                R, " +
			"                λa:A. a, " +
			"                relative_name_map(relative_vertical_degeneracy(R, q, j - 1)), " +
			"                u)))",
	},
	Reading: "The variable of the second tag of a relative name w is a member of the " +
		"column's algebra, so a relative name one degree up, and the 0-th degeneracy carries " +
		"the name universe_tag(1, w) to universe_tag(1, the variable of universe_tag(1, w)). " +
		"It reads neither the column nor S, T or the structure maps; a statement passes " +
		"λp:num. relative_vertical_degeneracy(R) for the bisimplicial degeneracies.",
	Deps: []registry.EntryLike{relativeNameMapDef},
})}

// relativeExtraDef — `relative_extra(R, u)`: the vertical extra
// degeneracy, the variable of the second tag of u less the variable of
// the second tag of zero — u a member of the column's algebra of degree
// q, which is a relative name of degree q + 1; the same function of the
// host in every column and degree.
var relativeExtraDef = relativeExtraDefThm{family.Define(registry.DefEntry{
	Name:  "relativeExtraDef",
	Key:   "prop_53bdc150707c6c91",
	Const: "relative_extra",
	Type:  "ring_ops(A) → U → U",
	Equations: []string{
		"∀R:ring_ops(A). ∀u:U. " +
			"    relative_extra(R, u) = " +
			"    universe_algebra_ring(R, 𝕌⟨A:U⟩).sub(universe_algebra_var(R, universe_tag(1, u)), " +
			"        universe_algebra_var(R, universe_tag(1, universe_algebra_ring(R, 𝕌⟨A:U⟩).zero)))",
	},
	Reading: "It keeps zero and is not additive, as the absolute extra degeneracy; the 0-th " +
		"vertical face reads it back as u through the second tag, and P's names are untouched, so it " +
		"is an extra degeneracy of each column over T. A statement passes λq:num. relative_extra(R).",
})}

// relativeExtraBottomDef — `relative_extra_bottom(R, T, t)`: the bottom of
// the vertical extra degeneracy, from T to vertical degree 0 — the
// variable of the second tag of the tag of t, a relative name of degree
// 0, less the same at T's zero.
var relativeExtraBottomDef = relativeExtraBottomDefThm{family.Define(registry.DefEntry{
	Name:  "relativeExtraBottomDef",
	Key:   "prop_f6dfd83be3c3626c",
	Const: "relative_extra_bottom",
	Type:  "ring_ops(A) → ring_ops(C) → C → U",
	Equations: []string{
		"∀R:ring_ops(A). ∀T:ring_ops(C). ∀t:C. " +
			"    relative_extra_bottom(R, T, t) = " +
			"    universe_algebra_ring(R, 𝕌⟨A:U⟩).sub( " +
			"        universe_algebra_var(R, universe_tag(1, carrier_tag(T.carrier, t))), " +
			"        universe_algebra_var(R, universe_tag(1, carrier_tag(T.carrier, T.zero))))",
	},
	Reading: "It lands in the algebra of vertical degree 0 of every " +
		"column, keeps zero, and the column's augmentation reads it back as t.",
})}

// ---------------------------------------------------------------------------
// The horizontal structure
// ---------------------------------------------------------------------------

// RelativeHorizontalMapDef — `relative_horizontal_map(R, h, q, u)`: the
// map of the row of vertical degree q induced by a map h of P's
// simplices, a function of the whole host: each name of P under the
// first tag goes to h at its variable, carried under the first tag, and
// the second tag of a relative name w is kept in degree 0 and in degree
// q + 1 goes to the variable of the second tag of the map of degree q at
// w.
var RelativeHorizontalMapDef = relativeHorizontalMapDefThm{family.Define(registry.DefEntry{
	Name:  "RelativeHorizontalMapDef",
	Key:   "prop_4673748c2228f9c3",
	Const: "relative_horizontal_map",
	Type:  "ring_ops(A) → (U → U) → num → U → U",
	Equations: []string{
		"∀R:ring_ops(A). ∀h:(U → U). " +
			"    relative_horizontal_map(R, h, 0) = " +
			"    (λu:U. " +
			"        universe_algebra_eval(R, " +
			"            universe_algebra_ring(R, 𝕌⟨A:U⟩), " +
			"            universe_algebra_const(R), " +
			"            λz:U. " +
			"                COND(z ∈ image(universe_tag(1), 𝕌⟨A:U⟩), " +
			"                    universe_algebra_var(R, z), " +
			"                    universe_algebra_map(R, " +
			"                        R, " +
			"                        λa:A. a, " +
			"                        universe_tag(0), " +
			"                        h(universe_algebra_var(R, inverse_on(𝕌⟨A:U⟩, universe_tag(0), z))))), " +
			"            u))",
		"∀R:ring_ops(A). ∀h:(U → U). ∀q:num. " +
			"    relative_horizontal_map(R, h, suc(q)) = " +
			"    (λu:U. " +
			"        universe_algebra_eval(R, " +
			"            universe_algebra_ring(R, 𝕌⟨A:U⟩), " +
			"            universe_algebra_const(R), " +
			"            λz:U. " +
			"                COND(z ∈ image(universe_tag(1), 𝕌⟨A:U⟩), " +
			"                    universe_algebra_var(R, " +
			"                        universe_tag(1, " +
			"                            relative_horizontal_map(R, " +
			"                                h, " +
			"                                q, " +
			"                                inverse_on(𝕌⟨A:U⟩, universe_tag(1), z)))), " +
			"                    universe_algebra_map(R, " +
			"                        R, " +
			"                        λa:A. a, " +
			"                        universe_tag(0), " +
			"                        h(universe_algebra_var(R, inverse_on(𝕌⟨A:U⟩, universe_tag(0), z))))), " +
			"            u))",
	},
	Reading: "The horizontal faces and degeneracies are the maps induced by P's: " +
		"relative_horizontal_map(R, standard_face(R, S, f, p + 1, i), q) from (p + 1, q) to (p, q) " +
		"and relative_horizontal_map(R, standard_degeneracy(R, p, i), q) from (p, q) to (p + 1, q). h " +
		"is read at the variables of P's names only, so it may be any algebra map of P's simplices; " +
		"for algebra maps the induced maps compose as the maps of P's simplices do. In vertical " +
		"degree 0 the relative names are those of every column and their second tags are kept.",
})}

// RelativeHorizontalEpsDef — `relative_horizontal_eps(R, S, f, q, u)`:
// the augmentation of the row of vertical degree q, from the column of
// P's 0-simplices to the standard resolution of T over S in degree q —
// each coefficient carried to the constant of its image under f, each
// name of P under the first tag to the constant of its value under P's
// augmentation, and the second tag of a relative name w to the variable
// over S of w itself in degree 0 and of the augmentation of degree q at
// w in degree q + 1.
var RelativeHorizontalEpsDef = relativeHorizontalEpsDefThm{family.Define(registry.DefEntry{
	Name:  "RelativeHorizontalEpsDef",
	Key:   "prop_d195f586104e3c00",
	Const: "relative_horizontal_eps",
	Type:  "ring_ops(A) → ring_ops(B) → (A → B) → num → U → U",
	Equations: []string{
		"∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B). " +
			"    relative_horizontal_eps(R, S, f, 0) = " +
			"    (λu:U. " +
			"        universe_algebra_eval(R, " +
			"            universe_algebra_ring(S, 𝕌⟨A:U⟩), " +
			"            λa:A. universe_algebra_const(S, f(a)), " +
			"            λz:U. " +
			"                COND(z ∈ image(universe_tag(1), 𝕌⟨A:U⟩), " +
			"                    universe_algebra_var(S, inverse_on(𝕌⟨A:U⟩, universe_tag(1), z)), " +
			"                    universe_algebra_const(S, " +
			"                        standard_eps(R, " +
			"                            S, " +
			"                            f, " +
			"                            universe_algebra_var(R, inverse_on(𝕌⟨A:U⟩, universe_tag(0), z))))), " +
			"            u))",
		"∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B). ∀q:num. " +
			"    relative_horizontal_eps(R, S, f, suc(q)) = " +
			"    (λu:U. " +
			"        universe_algebra_eval(R, " +
			"            universe_algebra_ring(S, 𝕌⟨A:U⟩), " +
			"            λa:A. universe_algebra_const(S, f(a)), " +
			"            λz:U. " +
			"                COND(z ∈ image(universe_tag(1), 𝕌⟨A:U⟩), " +
			"                    universe_algebra_var(S, " +
			"                        relative_horizontal_eps(R, " +
			"                            S, " +
			"                            f, " +
			"                            q, " +
			"                            inverse_on(𝕌⟨A:U⟩, universe_tag(1), z))), " +
			"                    universe_algebra_const(S, " +
			"                        standard_eps(R, " +
			"                            S, " +
			"                            f, " +
			"                            universe_algebra_var(R, inverse_on(𝕌⟨A:U⟩, universe_tag(0), z))))), " +
			"            u))",
	},
	Reading: "The target is standard_terms(S, T, q), over S's coefficients, read through " +
		"universe_embedding(S) in the same host: the coefficient ring changes from R to S " +
		"along f and P's names become constants. It reads neither T nor g: on the relative " +
		"names it is the identity in degree 0, where they are the names of degree 0 of the " +
		"standard resolution of T over S, the same tags of T's elements, and the augmentation " +
		"one degree down above, so the names of its target are standard_names(S, T, q). Read " +
		"on the column of P's 0-simplices; over the zero ring S the target is one point.",
	Deps: []registry.EntryLike{StandardEpsDef},
})}

// ---------------------------------------------------------------------------
// The standard resolution over R inside every column
// ---------------------------------------------------------------------------

// RelativeFromAbsoluteDef — `relative_from_absolute(R, q, u)`: the map
// from the standard resolution of T over R to every column of the
// relative standard resolution, in vertical degree q — in degree 0 the
// map induced by the second tag, carrying the tag of an element of T, a
// name of degree 0 of both, to its second tag; in degree q + 1 the map
// induced on the names by the map of degree q, whose values are relative
// names of degree q + 1, followed by the second tag.
var RelativeFromAbsoluteDef = relativeFromAbsoluteDefThm{family.Define(registry.DefEntry{
	Name:  "RelativeFromAbsoluteDef",
	Key:   "prop_94d26ae8bfd81ba",
	Const: "relative_from_absolute",
	Type:  "ring_ops(A) → num → U → U",
	Equations: []string{
		"∀R:ring_ops(A). " +
			"    relative_from_absolute(R, 0) = " +
			"    (λu:U. universe_algebra_map(R, R, λa:A. a, universe_tag(1), u))",
		"∀R:ring_ops(A). ∀q:num. " +
			"    relative_from_absolute(R, suc(q)) = " +
			"    (λu:U. " +
			"        universe_algebra_map(R, " +
			"            R, " +
			"            λa:A. a, " +
			"            λw:U. universe_tag(1, relative_from_absolute(R, q, w)), " +
			"            u))",
	},
	Reading: "It reads neither the column nor S, T or the structure maps: the standard " +
		"resolution of T over R, standard_names(R, T), maps into column p for every p by the " +
		"one function of the host, so its naturality in p is that the horizontal maps fix " +
		"every value it takes. It is a map over T when the structure map of T over R is g ∘ f.",
})}

// ---------------------------------------------------------------------------
// The relative names of vertical degree 0
// ---------------------------------------------------------------------------

// RelativeNamesZero — the relative names of vertical degree 0 are, in
// every column, the names of degree 0 of the standard resolution of T
// over S.
var RelativeNamesZero = relativeNamesZeroThm{family.Add(registry.ProofEntry{
	Name: "RelativeNamesZero",
	Key:  "prop_7a8301fe1e205485",
	Reading: "No hypothesis is read: both sides are literally the names of T's elements, " +
		"image(carrier_tag(T.carrier), T.carrier), one naming of one carrier, whatever R, S and p " +
		"are, and no universe is needed: it holds even where carrier_tag(T.carrier) is the choice " +
		"of an unsatisfiable property. So row 0 of the relative names is constant in p and is the " +
		"bottom of the standard resolution of T over S: the row augmentation carries the variable " +
		"of the second tag of each such name to the variable over S of that same name.",
	Deps: []registry.EntryLike{RelativeNamesDef, StandardNamesDef},
	Build: family.Card(
		"∀R:ring_ops(A). ∀S:ring_ops(B). ∀T:ring_ops(C). ∀p:num. "+
			"    relative_names⟨U:U⟩(R, S, T, p, 0) = standard_names(S, T, 0)",
		"unfold RelativeNamesDef and StandardNamesDef at degree "+
			"0: both are image(carrier_tag(T.carrier), T.carrier)"),
})}

// ---------------------------------------------------------------------------
// The vertical structure
// ---------------------------------------------------------------------------

// RelativeVerticalEpsHom — in a universe for R, S and T, the augmentation
// of column p is a ring map from its vertical degree 0 into T over g ∘ f,
// and on P's p-simplices carried under the first tag it is g after P's
// augmentation in degree p.
var RelativeVerticalEpsHom = relativeVerticalEpsHomThm{family.Add(registry.ProofEntry{
	Name: "RelativeVerticalEpsHom",
	Key:  "prop_3d62cdf41ee00b84",
	Reading: "The third conjunct makes T an algebra over P's p-simplices through the " +
		"column's augmentation, the algebra the column resolves; it reads P's augmentation " +
		"in degree p, standard_to_base, so a column further out is augmented through more of " +
		"P's 0-th faces. The constant conjunct needs nothing. The ring-map conjunct needs no " +
		"injectivity of T's naming, the preimage chosen in T's carrier lying there, but " +
		"reads the two tags' injectivity and disjointness, so that a name under the second " +
		"tag is read back as a name of T's carrier and one under the first as a name of P; " +
		"the third reads them too. The universe for T is not read here: it matters where the " +
		"column's augmentation reads the variable of the second tag of the tag of t back as t.",
	Deps: []registry.EntryLike{
		RelativeVerticalEpsDef,
		RelativeTermsDef,
		RelativeNamesDef,
		RelativeBaseInclusionHom,
		StandardToBaseHom,
		simplicial_ring.UniverseEmbeddingHost,
		simplicial_ring.TagInjective,
		simplicial_ring.TagsDisjoint,
		simplicial_ring.CarrierTagInjective,
		simplicial_ring.UniverseAlgebraEvalDef,
		free_algebra.FreeAlgebraEvalHom,
		free_algebra.FreeAlgebraEvalConst,
		free_algebra.FreeAlgebraEvalVar,
		free_algebra.FreeAlgebraEvalMap,
		free_algebra.FreeAlgebraEvalUnique,
		functions.InverseOnLeft,
		functions.InverseOnIn,
		ring_homomorphism.MapIn,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀T:ring_ops(C). ∀f:(A → B). ∀g:(B → C). ∀p:num.",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"cotangent_universe(T, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"ring_homomorphism(S, T, g)",
		},
		Conclusion: "ring_homomorphism(restrict_ring(universe_algebra_ring(R, " +
			"            image(universe_tag(0), standard_names(R, S, p)) ∪ " +
			"            image(universe_tag(1), relative_names(R, S, T, p, 0))), " +
			"        relative_terms(R, S, T, p, 0)), " +
			"    T, " +
			"    «columnEps»(p)) ∧ " +
			"(∀a:A. " +
			"    a ∈ R.carrier ⇒ " +
			"    relative_vertical_eps(R, S, f, T, g, p, universe_algebra_const⟨U:U⟩(R, a)) = g(f(a))) ∧ " +
			"(∀u:U. " +
			"    u ∈ standard_terms(R, S, p) ⇒ " +
			"    relative_vertical_eps(R, S, f, T, g, p, «baseInclusion»(u)) = " +
			"    g(standard_to_base(R, S, f, p, u)))",
	},
		"an evaluation into T at the universe embedding (UniverseEmbeddingHost) with g ∘ f a "+
			"ring map; its values at the names of (p, 0) lie in T's carrier: at a second tag the "+
			"preimage chosen in T's carrier (InverseOnIn), at P's names g after P's augmentation "+
			"(StandardToBaseHom, MapIn); FreeAlgebraEvalHom and FreeAlgebraEvalConst. For the third "+
			"conjunct both sides are ring maps from P's p-simplices (RelativeBaseInclusionHom; "+
			"StandardToBaseHom then g) agreeing on the constants and on the variable of x, the first "+
			"tag of x untagged back to x and off the second tag's image (TagInjective, TagsDisjoint, "+
			"InverseOnLeft, FreeAlgebraEvalMap, FreeAlgebraEvalVar); FreeAlgebraEvalUnique"),
})}

// RelativeVerticalFaceIn — in a universe for R, S and T, each vertical
// face of column p carries vertical degree q + 1 into vertical degree q.
var RelativeVerticalFaceIn = relativeVerticalFaceInThm{family.Add(registry.ProofEntry{
	Name: "RelativeVerticalFaceIn",
	Key:  "prop_df5ad5925d52692f",
	Deps: []registry.EntryLike{
		RelativeVerticalFaceDef,
		relativeNameMapDef,
		RelativeTermsDef,
		RelativeNamesDef,
		RelativeVerticalEpsHom,
		simplicial_ring.UniverseEmbeddingHost,
		simplicial_ring.TagInjective,
		simplicial_ring.TagsDisjoint,
		free_algebra.FreeAlgebraEvalHom,
		free_algebra.FreeAlgebraVarIn,
		free_algebra.FreeAlgebraSubset,
		free_algebra.FreeAlgebraMapHom,
		functions.InverseOnLeft,
		ring_homomorphism.MapIn,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀T:ring_ops(C). " +
			"∀f:(A → B). " +
			"∀g:(B → C). " +
			"∀p q j:num. " +
			"∀u:U.",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"cotangent_universe(T, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"ring_homomorphism(S, T, g)",
			"j ≤ q + 1",
			"u ∈ relative_terms(R, S, T, p, q + 1)",
		},
		Conclusion: "«verticalFace»(p, q + 1, j, u) ∈ relative_terms(R, S, T, p, q)",
	},
		"induct on q. The relative names of (p, q + 1) are the members of relative_terms(R, S, T, p, "+
			"q) (RelativeNamesDef). The face 0 evaluates the second tag of such a w to w and every other "+
			"name to its variable, so its values at the names of (p, q + 1) lie in relative_terms(R, S, T, "+
			"p, q) (TagInjective, TagsDisjoint, InverseOnLeft, FreeAlgebraVarIn, FreeAlgebraSubset); "+
			"FreeAlgebraEvalHom. The face j + 1 is the map induced by relative_name_map of the face j of "+
			"degree q, which fixes P's names (TagsDisjoint) and carries the second tag of w to the second "+
			"tag of its face: a member of relative_terms(R, S, T, p, q − 1), a relative name of (p, q), by "+
			"the induction, and at q = 0 the tag of the column's augmentation at w, a relative name of (p, "+
			"0) as the augmentation lands in T's carrier (RelativeVerticalEpsHom, MapIn); FreeAlgebraMapHom"),
})}

// RelativeGeneratorsClosed — in a universe for R, S and T, every vertical
// degeneracy carries the variable of the second tag of a relative name
// of (p, q) to the variable of the second tag of a relative name of
// (p, q + 1) and fixes the variables of P's names.
var RelativeGeneratorsClosed = relativeGeneratorsClosedThm{family.Add(registry.ProofEntry{
	Name: "RelativeGeneratorsClosed",
	Key:  "prop_fb08efd040b34b5c",
	Reading: "Stated on the variables, as polynomial_simplicial_algebra's own " +
		"condition is. The two kinds of names are kept apart: the relative names, " +
		"under the second tag, go to relative names one degree up, P's names stay P's.",
	Deps: []registry.EntryLike{
		RelativeVerticalDegeneracyDef,
		relativeNameMapDef,
		RelativeNamesDef,
		RelativeTermsDef,
		simplicial_ring.UniverseEmbeddingHost,
		simplicial_ring.TagInjective,
		simplicial_ring.TagsDisjoint,
		free_algebra.FreeAlgebraMapVar,
		free_algebra.FreeAlgebraMapHom,
		free_algebra.FreeAlgebraVarIn,
		functions.InverseOnLeft,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀T:ring_ops(C). ∀f:(A → B). ∀g:(B → C). ∀p q j:num.",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"cotangent_universe(T, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"ring_homomorphism(S, T, g)",
			"j ≤ q",
		},
		Conclusion: "image(relative_vertical_degeneracy⟨U:U⟩(R, q, j), " +
			"    image(universe_algebra_var(R), image(universe_tag(1), relative_names(R, S, T, p, q)))) ⊆ " +
			"image(universe_algebra_var(R), image(universe_tag(1), relative_names(R, S, T, p, q + 1))) ∧ " +
			"(∀x:U. " +
			"    x ∈ standard_names(R, S, p) ⇒ " +
			"    relative_vertical_degeneracy(R, q, j, universe_algebra_var(R, universe_tag(0, x))) = " +
			"    universe_algebra_var(R, universe_tag(0, x)))",
	},
		"induct on q, together with the closure of the degeneracies, relative_terms(R, S, T, "+
			"p, q) into relative_terms(R, S, T, p, q + 1) (FreeAlgebraMapHom). Every vertical "+
			"degeneracy is the map induced by relative_name_map(h), h the variable after the "+
			"second tag (j = 0) or a degeneracy one degree down, so it carries the variable of z "+
			"to the variable of relative_name_map(h)(z) (FreeAlgebraMapVar): P's names are fixed "+
			"(TagsDisjoint), and the second tag of w goes to the second tag of h(w) (TagInjective, "+
			"InverseOnLeft), a member of relative_terms(R, S, T, p, q), which is a relative name "+
			"of (p, q + 1) (RelativeNamesDef; FreeAlgebraVarIn, or the closure one degree down)"),
})}

// RelativeVerticalHom — in a universe for R, S and T, every vertical face
// and degeneracy of column p is an algebra map over R between the free
// algebras on the names of adjacent vertical degrees.
var RelativeVerticalHom = relativeVerticalHomThm{family.Add(registry.ProofEntry{
	Name: "RelativeVerticalHom",
	Key:  "prop_ddb6571896f71633",
	Deps: []registry.EntryLike{
		RelativeVerticalFaceDef,
		RelativeVerticalDegeneracyDef,
		RelativeVerticalFaceIn,
		RelativeGeneratorsClosed,
		RelativeTermsDef,
		simplicial_ring.UniverseEmbeddingHost,
		simplicial_ring.UniverseAlgebraHomomorphismDef,
		free_algebra.FreeAlgebraEvalHom,
		free_algebra.FreeAlgebraEvalConst,
		free_algebra.FreeAlgebraMapHom,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀T:ring_ops(C). ∀f:(A → B). ∀g:(B → C).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"cotangent_universe(T, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"ring_homomorphism(S, T, g)",
		},
		Conclusion: "(∀p q j:num. " +
			"    j ≤ q + 1 ⇒ " +
			"    universe_algebra_homomorphism(R, " +
			"        image(universe_tag(0), standard_names(R, S, p)) ∪ " +
			"        image(universe_tag(1), relative_names(R, S, T, p, q + 1)), " +
			"        image(universe_tag(0), standard_names(R, S, p)) ∪ " +
			"        image(universe_tag(1), relative_names(R, S, T, p, q)), " +
			"        relative_vertical_face⟨U:U⟩(R, S, f, T, g, p, q + 1, j))) ∧ " +
			"(∀p q j:num. " +
			"    j ≤ q ⇒ " +
			"    universe_algebra_homomorphism(R, " +
			"        image(universe_tag(0), standard_names(R, S, p)) ∪ " +
			"        image(universe_tag(1), relative_names(R, S, T, p, q)), " +
			"        image(universe_tag(0), standard_names(R, S, p)) ∪ " +
			"        image(universe_tag(1), relative_names(R, S, T, p, q + 1)), " +
			"        relative_vertical_degeneracy⟨U:U⟩(R, q, j)))",
	},
		"the face 0 is an evaluation into the host ring fixing the constants "+
			"(FreeAlgebraEvalHom, FreeAlgebraEvalConst) with values in the algebra on the "+
			"names of (p, q) (RelativeVerticalFaceIn); the faces j + 1 and the degeneracies "+
			"are maps induced on the variables (FreeAlgebraMapHom) by maps of names "+
			"carrying the names of (p, q + 1) into those of (p, q) (RelativeVerticalFaceIn) "+
			"or the names of (p, q) into those of (p, q + 1) (RelativeGeneratorsClosed)"),
})}

// RelativeVerticalFixesBase — in a universe for R, S and T, every vertical
// face and degeneracy of column p is the identity on P's p-simplices
// carried under the first tag.
var RelativeVerticalFixesBase = relativeVerticalFixesBaseThm{family.Add(registry.ProofEntry{
	Name: "RelativeVerticalFixesBase",
	Key:  "prop_579214518b622040",
	Reading: "This is what makes each column a simplicial algebra over P's p-simplices: the " +
		"vertical structure is linear over them, P's names being variables that every vertical map keeps.",
	Deps: []registry.EntryLike{
		RelativeVerticalHom,
		RelativeBaseInclusionHom,
		RelativeVerticalFaceDef,
		RelativeVerticalDegeneracyDef,
		relativeNameMapDef,
		simplicial_ring.TagsDisjoint,
		free_algebra.FreeAlgebraEvalVar,
		free_algebra.FreeAlgebraMapVar,
		free_algebra.FreeAlgebraEvalUnique,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀T:ring_ops(C). " +
			"∀f:(A → B). " +
			"∀g:(B → C). " +
			"∀p q j:num. " +
			"∀u:U.",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"cotangent_universe(T, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"ring_homomorphism(S, T, g)",
			"u ∈ standard_terms(R, S, p)",
		},
		Conclusion: "(j ≤ q + 1 ⇒ " +
			"    «verticalFace»(p, q + 1, j, «baseInclusion»(u)) = «baseInclusion»(u)) ∧ " +
			"(j ≤ q ⇒ relative_vertical_degeneracy(R, q, j, «baseInclusion»(u)) = «baseInclusion»(u))",
	},
		"both sides are algebra maps from P's p-simplices (RelativeBaseInclusionHom, "+
			"RelativeVerticalHom) agreeing on the constants and on the variable of x: the "+
			"first tag of x is evaluated to its own variable by the face 0 and kept by the "+
			"maps induced by relative_name_map, which fix every name off the second tag's "+
			"image (TagsDisjoint, FreeAlgebraEvalVar, FreeAlgebraMapVar); FreeAlgebraEvalUnique"),
})}

// RelativeVerticalSimplicial — in a universe for R, S and T, every column
// of the relative standard resolution is a simplicial set under the
// vertical faces and degeneracies.
var RelativeVerticalSimplicial = relativeVerticalSimplicialThm{family.Add(registry.ProofEntry{
	Name: "RelativeVerticalSimplicial",
	Key:  "prop_f1e5ec49590d1fef",
	Reading: "In vertical degree 2 the identity d_1 d_2 = d_1 d_1 reduces to the tag of the " +
		"column's augmentation after d_1 being the tag of it after d_0 on the (p, 1)-simplices, " +
		"which needs the tag injective on T's carrier, the universe for T; d_1 s_0 = id in " +
		"degree 0 needs only that the tag of the preimage chosen for a tag is that tag.",
	Deps: []registry.EntryLike{
		RelativeVerticalFaceIn,
		RelativeVerticalHom,
		RelativeVerticalFixesBase,
		RelativeVerticalEpsHom,
		RelativeVerticalFaceDef,
		RelativeVerticalDegeneracyDef,
		relativeNameMapDef,
		simplicial_ring.TagInjective,
		simplicial_ring.TagsDisjoint,
		simplicial_ring.CarrierTagInjective,
		simplicial_set.SimplicialSet,
		free_algebra.FreeAlgebraEvalMult,
		free_algebra.FreeAlgebraEvalMap,
		free_algebra.FreeAlgebraEvalUnique,
		free_algebra.FreeAlgebraMapCompose,
		free_algebra.FreeAlgebraMapCongruence,
		functions.InverseOnLeft,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀T:ring_ops(C). ∀f:(A → B). ∀g:(B → C). ∀p:num.",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"cotangent_universe(T, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"ring_homomorphism(S, T, g)",
		},
		Conclusion: "simplicial_set(mk_simplicial(λq:num. relative_terms(R, S, T, p, q), " +
			"        «verticalFace»(p), " +
			"        relative_vertical_degeneracy⟨U:U⟩(R)))",
	},
		"the column is the standard resolution of T over P's p-simplices with P's names as variables, "+
			"and the proof is StandardSimplicialSet's: the closures are RelativeVerticalFaceIn and "+
			"RelativeVerticalHom, and the identities are checked on the variables, both sides being "+
			"algebra maps fixing P's variables (RelativeVerticalHom, RelativeVerticalFixesBase; "+
			"FreeAlgebraEvalUnique). On the second tag of w the face 0 untags and the faces j + 1 and the "+
			"degeneracies act through relative_name_map (TagInjective, TagsDisjoint, InverseOnLeft), so "+
			"each identity reduces to one degree down (FreeAlgebraMapCompose, FreeAlgebraMapCongruence, "+
			"FreeAlgebraEvalMap, FreeAlgebraEvalMult); at vertical degree 0 the base identities are the "+
			"column's augmentation coequalizing the two faces of an edge and reading the second tag of "+
			"the tag of t back as t (RelativeVerticalEpsHom, CarrierTagInjective)"),
})}

// ---------------------------------------------------------------------------
// The horizontal structure and the bisimplicial set
// ---------------------------------------------------------------------------

// RelativeBaseInclusionHom — in a universe for R, the inclusion of P's
// p-simplices under the first tag is an algebra map over R into every
// row's (p, q)-simplices.
var RelativeBaseInclusionHom = relativeBaseInclusionHomThm{family.Add(registry.ProofEntry{
	Name: "RelativeBaseInclusionHom",
	Key:  "prop_87792324d9d88d42",
	Deps: []registry.EntryLike{
		RelativeTermsDef,
		RelativeNamesDef,
		StandardNamesDef,
		simplicial_ring.UniverseEmbeddingHost,
		simplicial_ring.UniverseAlgebraHomomorphismDef,
		simplicial_ring.UniverseAlgebraMapDef,
		free_algebra.FreeAlgebraMapHom,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀T:ring_ops(C). ∀f:(A → B). ∀g:(B → C). ∀p q:num.",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"cotangent_universe(T, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"ring_homomorphism(S, T, g)",
		},
		Conclusion: "universe_algebra_homomorphism(R, " +
			"    standard_names⟨U:U⟩(R, S, p), " +
			"    image(universe_tag(0), standard_names(R, S, p)) ∪ " +
			"    image(universe_tag(1), relative_names(R, S, T, p, q)), " +
			"    universe_algebra_map(R, R, λa:A. a, universe_tag(0)))",
	},
		"the map induced by the first tag, which carries P's names of degree p into the "+
			"names of (p, q); FreeAlgebraMapHom at the universe embedding (UniverseEmbeddingHost)"),
})}

// RelativeBaseInclusionNatural — in a universe for R, S and T, the map of
// a row induced by an algebra map h of P's simplices extends h along the
// inclusion of P under the first tag.
var RelativeBaseInclusionNatural = relativeBaseInclusionNaturalThm{family.Add(registry.ProofEntry{
	Name: "RelativeBaseInclusionNatural",
	Key:  "prop_f2c5af4209729f9d",
	Reading: "h is any algebra map of P's simplices, a face or a degeneracy " +
		"among them, and the row q does not matter: the first tag is read the same " +
		"way in every row. So the horizontal faces and degeneracies are maps over P's.",
	Deps: []registry.EntryLike{
		RelativeHorizontalMapDef,
		RelativeBaseInclusionHom,
		simplicial_ring.UniverseEmbeddingHost,
		simplicial_ring.TagInjective,
		simplicial_ring.TagsDisjoint,
		free_algebra.FreeAlgebraEvalHom,
		free_algebra.FreeAlgebraEvalVar,
		free_algebra.FreeAlgebraEvalConst,
		free_algebra.FreeAlgebraEvalUnique,
		functions.InverseOnLeft,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀T:ring_ops(C). " +
			"∀f:(A → B). " +
			"∀g:(B → C). " +
			"∀p p' q:num. " +
			"∀h:(U → U). " +
			"∀u:U.",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"cotangent_universe(T, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"ring_homomorphism(S, T, g)",
			"universe_algebra_homomorphism(R, standard_names(R, S, p), standard_names(R, S, p'), h)",
			"u ∈ standard_terms(R, S, p)",
		},
		Conclusion: "relative_horizontal_map(R, h, q, «baseInclusion»(u)) = «baseInclusion»(h(u))",
	},
		"both sides are algebra maps from P's p-simplices (RelativeBaseInclusionHom, the "+
			"horizontal map an evaluation into the host ring fixing the constants, FreeAlgebraEvalHom; "+
			"h then the inclusion) agreeing on the constants and on the variable of x: the horizontal "+
			"map carries the variable of the first tag of x to the first tag of h at the variable of x "+
			"(FreeAlgebraEvalVar, TagInjective, TagsDisjoint, InverseOnLeft); FreeAlgebraEvalUnique"),
})}

// RelativeHorizontalFaceIn — in a universe for R, S and T, each
// horizontal face carries the (p + 1, q)-simplices into the (p,
// q)-simplices.
var RelativeHorizontalFaceIn = relativeHorizontalFaceInThm{family.Add(registry.ProofEntry{
	Name: "RelativeHorizontalFaceIn",
	Key:  "prop_3047a82371f6454d",
	Deps: []registry.EntryLike{
		RelativeHorizontalMapDef,
		RelativeTermsDef,
		RelativeNamesDef,
		StandardFaceIn,
		RelativeBaseInclusionHom,
		simplicial_ring.UniverseEmbeddingHost,
		simplicial_ring.TagInjective,
		simplicial_ring.TagsDisjoint,
		free_algebra.FreeAlgebraEvalHom,
		free_algebra.FreeAlgebraVarIn,
		free_algebra.FreeAlgebraSubset,
		functions.InverseOnLeft,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀T:ring_ops(C). " +
			"∀f:(A → B). " +
			"∀g:(B → C). " +
			"∀p q i:num. " +
			"∀u:U.",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"cotangent_universe(T, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"ring_homomorphism(S, T, g)",
			"i ≤ p + 1",
			"u ∈ relative_terms(R, S, T, p + 1, q)",
		},
		Conclusion: "relative_horizontal_map(R, standard_face(R, S, f, p + 1, i), q, u) ∈ " +
			"relative_terms(R, S, T, p, q)",
	},
		"induct on q. The map is an evaluation into the host ring (FreeAlgebraEvalHom): the "+
			"variable of the first tag of x ∈ standard_names(R, S, p + 1) goes to the first tag "+
			"of the face of P at the variable of x, a p-simplex of P (StandardFaceIn) carried "+
			"under the first tag (RelativeBaseInclusionHom); the relative names of (p + 1, 0) are "+
			"those of (p, 0) and their second tags are kept; in degree q + 1 the second tag of a "+
			"relative name w ∈ relative_terms(R, S, T, p + 1, q) goes to the variable of the "+
			"second tag of its image under the map of degree q, a member of relative_terms(R, S, "+
			"T, p, q), so a relative name of (p, q + 1), by the induction (RelativeNamesDef; "+
			"TagInjective, TagsDisjoint, InverseOnLeft, FreeAlgebraVarIn, FreeAlgebraSubset)"),
})}

// RelativeHorizontalHom — in a universe for R, S and T, every horizontal
// face and degeneracy is an algebra map over R between the free algebras
// on the names of adjacent columns.
var RelativeHorizontalHom = relativeHorizontalHomThm{family.Add(registry.ProofEntry{
	Name: "RelativeHorizontalHom",
	Key:  "prop_b5764bf0eacef46a",
	Deps: []registry.EntryLike{
		RelativeHorizontalMapDef,
		RelativeHorizontalFaceIn,
		RelativeBaseInclusionHom,
		StandardDegeneracyIn,
		RelativeTermsDef,
		simplicial_ring.UniverseEmbeddingHost,
		simplicial_ring.UniverseAlgebraHomomorphismDef,
		free_algebra.FreeAlgebraEvalHom,
		free_algebra.FreeAlgebraEvalConst,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀T:ring_ops(C). ∀f:(A → B). ∀g:(B → C).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"cotangent_universe(T, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"ring_homomorphism(S, T, g)",
		},
		Conclusion: "(∀p q i:num. " +
			"    i ≤ p + 1 ⇒ " +
			"    universe_algebra_homomorphism(R, " +
			"        image(universe_tag(0), standard_names(R, S, p + 1)) ∪ " +
			"        image(universe_tag(1), relative_names(R, S, T, p + 1, q)), " +
			"        image(universe_tag(0), standard_names(R, S, p)) ∪ " +
			"        image(universe_tag(1), relative_names(R, S, T, p, q)), " +
			"        relative_horizontal_map⟨U:U⟩(R, standard_face(R, S, f, p + 1, i), q))) ∧ " +
			"(∀p q i:num. " +
			"    i ≤ p ⇒ " +
			"    universe_algebra_homomorphism(R, " +
			"        image(universe_tag(0), standard_names(R, S, p)) ∪ " +
			"        image(universe_tag(1), relative_names(R, S, T, p, q)), " +
			"        image(universe_tag(0), standard_names(R, S, p + 1)) ∪ " +
			"        image(universe_tag(1), relative_names(R, S, T, p + 1, q)), " +
			"        relative_horizontal_map⟨U:U⟩(R, standard_degeneracy(R, p, i), q)))",
	},
		"each is an evaluation into the host ring fixing the constants (FreeAlgebraEvalHom, "+
			"FreeAlgebraEvalConst) whose values at the source's names lie in the algebra on the "+
			"target's names: RelativeHorizontalFaceIn for the faces, and for the degeneracies the "+
			"same induction with P's degeneracies (StandardDegeneracyIn, RelativeBaseInclusionHom)"),
})}

// RelativeHorizontalSimplicial — in a universe for R, S and T, every row
// of the relative standard resolution is a simplicial set under the maps
// induced by P's faces and degeneracies.
var RelativeHorizontalSimplicial = relativeHorizontalSimplicialThm{family.Add(registry.ProofEntry{
	Name: "RelativeHorizontalSimplicial",
	Key:  "prop_706239fe60f552f8",
	Deps: []registry.EntryLike{
		RelativeHorizontalFaceIn,
		RelativeHorizontalHom,
		RelativeBaseInclusionNatural,
		RelativeHorizontalMapDef,
		StandardSimplicialSet,
		StandardFacesHom,
		StandardDegeneraciesHom,
		simplicial_ring.TagInjective,
		simplicial_ring.TagsDisjoint,
		simplicial_set.SimplicialSet,
		free_algebra.FreeAlgebraEvalUnique,
		free_algebra.FreeAlgebraEvalVar,
		functions.InverseOnLeft,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀T:ring_ops(C). ∀f:(A → B). ∀g:(B → C). ∀q:num.",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"cotangent_universe(T, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"ring_homomorphism(S, T, g)",
		},
		Conclusion: "simplicial_set(mk_simplicial(λp:num. relative_terms(R, S, T, p, q), " +
			"        λp:num. λi:num. relative_horizontal_map⟨U:U⟩(R, standard_face(R, S, f, p, i), q), " +
			"        λp:num. λi:num. relative_horizontal_map(R, standard_degeneracy(R, p, i), q)))",
	},
		"the maps a row inherits compose as P's do: for algebra maps h' and h of P's simplices, the "+
			"map induced by h after the one induced by h' is the one induced by h ∘ h' on the row, by "+
			"induction on q on the variables — P's through the inclusion (RelativeBaseInclusionNatural), "+
			"the relative names kept in degree 0 and mapped by the induction above (TagInjective, "+
			"TagsDisjoint, InverseOnLeft, FreeAlgebraEvalVar, FreeAlgebraEvalUnique). The identities are "+
			"then P's (StandardSimplicialSet, with StandardFacesHom and StandardDegeneraciesHom), the "+
			"closures RelativeHorizontalFaceIn and RelativeHorizontalHom"),
})}

// RelativeDirectionsCommute — in a universe for R, S and T, the
// horizontal and the vertical faces and degeneracies of the relative
// standard resolution commute.
var RelativeDirectionsCommute = relativeDirectionsCommuteThm{family.Add(registry.ProofEntry{
	Name: "RelativeDirectionsCommute",
	Key:  "prop_5e5fd600c5336e30",
	Reading: "The four identities are the commutation conjuncts of bisimplicial_set at " +
		"the horizontal maps induced by P's faces and degeneracies and the vertical faces " +
		"and degeneracies. The vertical degeneracies are the same in every column; the " +
		"vertical faces read the column through its augmentation in vertical degree 0. Every " +
		"identity reduces on the variables to one degree down, and the only base content is " +
		"that the augmentation of column p after a horizontal face is that of column p + 1, " +
		"and the augmentation of column p + 1 after a horizontal degeneracy that of column p " +
		"(d_0 s_i = id in P); the tags of T's elements are kept by every horizontal map.",
	Deps: []registry.EntryLike{
		RelativeVerticalHom,
		RelativeHorizontalHom,
		RelativeVerticalFixesBase,
		RelativeBaseInclusionNatural,
		RelativeVerticalEpsHom,
		RelativeHorizontalFaceIn,
		StandardToBaseFaceIndependent,
		StandardFaceDegeneracyEqual,
		StandardFacesHom,
		StandardDegeneraciesHom,
		RelativeVerticalFaceDef,
		RelativeVerticalDegeneracyDef,
		RelativeHorizontalMapDef,
		simplicial_ring.TagInjective,
		simplicial_ring.TagsDisjoint,
		simplicial_ring.CarrierTagInjective,
		free_algebra.FreeAlgebraEvalUnique,
		functions.InverseOnLeft,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀T:ring_ops(C). ∀f:(A → B). ∀g:(B → C).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"cotangent_universe(T, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"ring_homomorphism(S, T, g)",
		},
		Conclusion: "(∀p q i j:num. ∀u:U. " +
			"    u ∈ relative_terms(R, S, T, p + 1, q + 1) ∧ i ≤ p + 1 ∧ j ≤ q + 1 ⇒ " +
			"    relative_horizontal_map(R, " +
			"        standard_face(R, S, f, p + 1, i), " +
			"        q, " +
			"        «verticalFace»(p + 1, q + 1, j, u)) = " +
			"    «verticalFace»(p, " +
			"        q + 1, " +
			"        j, " +
			"        relative_horizontal_map(R, standard_face(R, S, f, p + 1, i), q + 1, u))) ∧ " +
			"(∀p q i j:num. ∀u:U. " +
			"    u ∈ relative_terms(R, S, T, p + 1, q) ∧ i ≤ p + 1 ∧ j ≤ q ⇒ " +
			"    relative_horizontal_map(R, " +
			"        standard_face(R, S, f, p + 1, i), " +
			"        q + 1, " +
			"        relative_vertical_degeneracy(R, q, j, u)) = " +
			"    relative_vertical_degeneracy(R, " +
			"        q, " +
			"        j, " +
			"        relative_horizontal_map(R, standard_face(R, S, f, p + 1, i), q, u))) ∧ " +
			"(∀p q i j:num. ∀u:U. " +
			"    u ∈ relative_terms(R, S, T, p, q + 1) ∧ i ≤ p ∧ j ≤ q + 1 ⇒ " +
			"    relative_horizontal_map(R, " +
			"        standard_degeneracy(R, p, i), " +
			"        q, " +
			"        «verticalFace»(p, q + 1, j, u)) = " +
			"    «verticalFace»(p + 1, " +
			"        q + 1, " +
			"        j, " +
			"        relative_horizontal_map(R, standard_degeneracy(R, p, i), q + 1, u))) ∧ " +
			"(∀p q i j:num. ∀u:U. " +
			"    u ∈ relative_terms(R, S, T, p, q) ∧ i ≤ p ∧ j ≤ q ⇒ " +
			"    relative_horizontal_map(R, " +
			"        standard_degeneracy(R, p, i), " +
			"        q + 1, " +
			"        relative_vertical_degeneracy(R, q, j, u)) = " +
			"    relative_vertical_degeneracy(R, " +
			"        q, " +
			"        j, " +
			"        relative_horizontal_map(R, standard_degeneracy(R, p, i), q, u)))",
	},
		"check on the variables, both sides being algebra maps (RelativeVerticalHom, "+
			"RelativeHorizontalHom; FreeAlgebraEvalUnique). P's variables are fixed by the vertical maps "+
			"(RelativeVerticalFixesBase) and moved by the horizontal ones through the inclusion "+
			"(RelativeBaseInclusionNatural), so both sides agree there. On the second tag of w, induct on "+
			"q: the vertical face 0 untags and the horizontal map tags its image, the vertical faces j + 1 "+
			"and the degeneracies act through relative_name_map, and each identity reduces to one degree "+
			"down (TagInjective, TagsDisjoint, InverseOnLeft). At vertical degree 0 what remains is that "+
			"the column augmentations commute with the horizontal maps: relative_vertical_eps of column p "+
			"after the map induced by a face out of column p + 1 is relative_vertical_eps of column p + 1, "+
			"and after the map induced by a degeneracy of column p, the one of column p — P's augmentation "+
			"in degree p after a face is the one in degree p + 1 (StandardToBaseFaceIndependent) and after "+
			"a degeneracy the one in degree p (with StandardFaceDegeneracyEqual) — read through "+
			"RelativeVerticalEpsHom, the tags of T's elements kept (CarrierTagInjective)"),
})}

// RelativeBisimplicialSet — in a universe for R, S and T, the relative
// standard resolution is a bisimplicial set: the maps induced by P's
// faces and degeneracies horizontally, the vertical faces and
// degeneracies vertically.
var RelativeBisimplicialSet = relativeBisimplicialSetThm{family.Add(registry.ProofEntry{
	Name: "RelativeBisimplicialSet",
	Key:  "prop_eca772c6e9aa86dd",
	Deps: []registry.EntryLike{
		RelativeHorizontalSimplicial,
		RelativeVerticalSimplicial,
		RelativeDirectionsCommute,
		simplicial_homotopy.BisimplicialSet,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀T:ring_ops(C). ∀f:(A → B). ∀g:(B → C).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"cotangent_universe(T, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"ring_homomorphism(S, T, g)",
		},
		Conclusion: "bisimplicial_set(mk_bisimplicial(λp:num. λq:num. relative_terms(R, S, T, p, q), " +
			"        λp:num. λq:num. λi:num. " +
			"            relative_horizontal_map⟨U:U⟩(R, standard_face(R, S, f, p, i), q), " +
			"        λp:num. λq:num. λi:num. relative_horizontal_map(R, standard_degeneracy(R, p, i), q), " +
			"        relative_vertical_face(R, S, f, T, g), " +
			"        λp:num. relative_vertical_degeneracy(R)))",
	},
		"unfold BisimplicialSet: the rows are RelativeHorizontalSimplicial, the columns "+
			"RelativeVerticalSimplicial, the four commutations RelativeDirectionsCommute"),
})}

// ---------------------------------------------------------------------------
// Every column a resolution of T
// ---------------------------------------------------------------------------

// RelativeColumnAugmented — in a universe for R, S and T, every column of
// the relative standard resolution is a polynomial simplicial algebra over
// R augmented over T through g ∘ f.
var RelativeColumnAugmented = relativeColumnAugmentedThm{family.Add(registry.ProofEntry{
	Name: "RelativeColumnAugmented",
	Key:  "prop_f843cc63d1528cad",
	Deps: []registry.EntryLike{
		simplicial_ring.AugmentedPolynomialAlgebra,
		simplicial_ring.PolynomialSimplicialAlgebra,
		RelativeVerticalSimplicial,
		RelativeTermsDef,
		RelativeVerticalHom,
		RelativeGeneratorsClosed,
		RelativeVerticalEpsHom,
		RelativeVerticalFixesBase,
		RelativeVerticalFaceDef,
		relativeNameMapDef,
		simplicial_ring.TagInjective,
		simplicial_ring.CarrierTagInjective,
		free_algebra.FreeAlgebraEvalVar,
		free_algebra.FreeAlgebraMapVar,
		free_algebra.FreeAlgebraEvalUnique,
		functions.InverseOnLeft,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀T:ring_ops(C). ∀f:(A → B). ∀g:(B → C). ∀p:num.",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"cotangent_universe(T, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"ring_homomorphism(S, T, g)",
		},
		Conclusion: "augmented_polynomial_algebra(R, " +
			"    λq:num. " +
			"        image(universe_tag(0), standard_names(R, S, p)) ∪ " +
			"        image(universe_tag(1), relative_names(R, S, T, p, q)), " +
			"    «verticalFace»(p), " +
			"    relative_vertical_degeneracy(R), " +
			"    T, " +
			"    λa:A. g(f(a)), " +
			"    «columnEps»(p))",
	},
		"unfold AugmentedPolynomialAlgebra and PolynomialSimplicialAlgebra: R is a commutative ring and "+
			"g ∘ f a ring map (the hypotheses composed); the simplicial set is RelativeVerticalSimplicial, "+
			"the free algebra on the names of (p, q) being relative_terms(R, S, T, p, q) "+
			"(RelativeTermsDef); the faces and degeneracies are algebra maps (RelativeVerticalHom) keeping "+
			"the variables (RelativeGeneratorsClosed); the augmentation is RelativeVerticalEpsHom, and ε "+
			"d_0 = ε d_1 on relative_terms(R, S, T, p, 1): both are ring maps agreeing on P's variables, "+
			"which both faces fix (RelativeVerticalFixesBase), and at the variable of the second tag of w, "+
			"where the left side is ε(w) and the right side ε at the variable of the second tag of the tag "+
			"of ε(w), which is ε(w) (TagInjective, CarrierTagInjective, InverseOnLeft, FreeAlgebraMapVar, "+
			"FreeAlgebraEvalVar); FreeAlgebraEvalUnique"),
})}

// RelativeColumnExtra — in a universe for R, S and T, every column of the
// relative standard resolution has the extra degeneracy u ↦ [tag₁ u] −
// [tag₁ 0] over T, which with its bottom keeps zero.
var RelativeColumnExtra = relativeColumnExtraThm{family.Add(registry.ProofEntry{
	Name: "RelativeColumnExtra",
	Key:  "prop_4ae624b960e7743d",
	Reading: "The extra degeneracy fixes no variable of P: it is a map of sets on the " +
		"column, not an algebra map over P's p-simplices, and like the absolute one it is " +
		"not additive. It is the same function of the host in every column and degree, " +
		"and a map of sets keeping zero is all the acyclicity of an extra degeneracy reads.",
	Deps: []registry.EntryLike{
		relativeExtraDef,
		relativeExtraBottomDef,
		RelativeVerticalSimplicial,
		RelativeVerticalHom,
		RelativeVerticalFaceIn,
		RelativeVerticalEpsHom,
		RelativeVerticalFaceDef,
		RelativeVerticalDegeneracyDef,
		relativeNameMapDef,
		RelativeNamesDef,
		RelativeTermsDef,
		simplicial_homotopy.ExtraDegeneracy,
		simplicial_ring.UniverseEmbeddingHost,
		simplicial_ring.TagInjective,
		simplicial_ring.TagsDisjoint,
		simplicial_ring.CarrierTagInjective,
		free_algebra.FreeAlgebraEvalVar,
		free_algebra.FreeAlgebraMapVar,
		free_algebra.FreeAlgebraVarIn,
		free_algebra.FreeAlgebraCommRingOn,
		functions.InverseOnLeft,
		ring_homomorphism.AdditiveHomomorphism,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀T:ring_ops(C). ∀f:(A → B). ∀g:(B → C).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"cotangent_universe(T, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"ring_homomorphism(S, T, g)",
		},
		Conclusion: "(∀p:num. " +
			"    extra_degeneracy(mk_simplicial(λq:num. relative_terms(R, S, T, p, q), " +
			"            «verticalFace»(p), " +
			"            relative_vertical_degeneracy(R)), " +
			"        T.carrier, " +
			"        «columnEps»(p), " +
			"        λq:num. relative_extra(R), " +
			"        relative_extra_bottom(R, T))) ∧ " +
			"relative_extra(R, «hostZero») = «hostZero» ∧ " +
			"relative_extra_bottom(R, T, T.zero) = «hostZero»",
	},
		"the identities are StandardExtraFace's, StandardExtraDegeneracy's and StandardExtraBottom's "+
			"through the second tag: σ(u) is the difference of the variables of the second tags of u and "+
			"of zero, so the face 0 untags it to u − 0 = u, the faces j + 1 and the degeneracies j + 1 "+
			"act on it through relative_name_map, ring maps keeping zero (RelativeVerticalHom, "+
			"AdditiveHomomorphism), and in vertical degree 0 the face 1 takes it to the difference of "+
			"the variables of the second tags of the tags of ε(u) and of ε(0) = T.zero, the bottom of "+
			"ε(u) (RelativeVerticalEpsHom, TagInjective, InverseOnLeft, FreeAlgebraMapVar); the "+
			"augmentation reads the bottom of t back as t − T.zero = t (CarrierTagInjective, "+
			"TagsDisjoint, FreeAlgebraEvalVar). The closures: a member of relative_terms(R, S, T, p, q) "+
			"is a relative name of (p, q + 1), so the variable of its second tag lies in "+
			"relative_terms(R, S, T, p, q + 1) (RelativeNamesDef, FreeAlgebraVarIn), and the tag of t ∈ "+
			"T.carrier is a relative name of (p, 0). σ and the bottom keep zero, x − x being zero in the "+
			"host ring (FreeAlgebraCommRingOn); the simplicial set is RelativeVerticalSimplicial"),
})}

// RelativeColumnResolution — in a universe for R, S and T, every column of
// the relative standard resolution is a polynomial resolution of T over R
// through g ∘ f.
var RelativeColumnResolution = relativeColumnResolutionThm{family.Add(registry.ProofEntry{
	Name: "RelativeColumnResolution",
	Key:  "prop_e2d47a6d8e169324",
	Reading: "Each column resolves T over P's p-simplices, P's names being " +
		"variables every vertical map fixes, yet the coefficient ring stays R: the " +
		"resolution is one over R, whose underlying simplicial module is over R.",
	Deps: []registry.EntryLike{
		RelativeColumnAugmented,
		RelativeColumnExtra,
		RelativeVerticalEpsHom,
		simplicial_ring.PolynomialResolution,
		simplicial_ring.PolynomialAlgebraSimplicialModule,
		simplicial_module.ExtraDegeneracyAcyclic,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀T:ring_ops(C). ∀f:(A → B). ∀g:(B → C). ∀p:num.",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"cotangent_universe(T, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"ring_homomorphism(S, T, g)",
		},
		Conclusion: "polynomial_resolution(R, " +
			"    λq:num. " +
			"        image(universe_tag(0), standard_names(R, S, p)) ∪ " +
			"        image(universe_tag(1), relative_names(R, S, T, p, q)), " +
			"    «verticalFace»(p), " +
			"    relative_vertical_degeneracy(R), " +
			"    T, " +
			"    λa:A. g(f(a)), " +
			"    «columnEps»(p))",
	},
		"RelativeColumnAugmented; acyclicity is ExtraDegeneracyAcyclic at the simplicial module of the "+
			"column (PolynomialAlgebraSimplicialModule), with N the module T over R through g ∘ f, "+
			"scalar_restriction(λa:A. g(f(a)), regular_module(T)), the augmentation linear on vertical "+
			"degree 0 (RelativeVerticalEpsHom), and the extra degeneracy of RelativeColumnExtra, keeping zero"),
})}

// ---------------------------------------------------------------------------
// The row augmentation and the augmentation onto T
// ---------------------------------------------------------------------------

// RelativeHorizontalEpsHom — in a universe for R, S and T, the
// augmentation of row q is an algebra map over f from the (0,
// q)-simplices to the standard resolution of T over S in degree q.
var RelativeHorizontalEpsHom = relativeHorizontalEpsHomThm{family.Add(registry.ProofEntry{
	Name: "RelativeHorizontalEpsHom",
	Key:  "prop_b64420001c9feacd",
	Reading: "The map changes the coefficient ring from R to S along f: an algebra map over f " +
		"between two free algebras in the one host, read through the universe embeddings of R and " +
		"of S, so it is stated with free_algebra_homomorphism and not with the one-ring " +
		"universe_algebra_homomorphism. The universe for S is load-bearing, its embedding being the " +
		"target's; over a zero ring S, which forces T to be the zero ring, the target is one point.",
	Deps: []registry.EntryLike{
		RelativeHorizontalEpsDef,
		RelativeTermsDef,
		RelativeNamesDef,
		RelativeNamesZero,
		StandardNamesDef,
		StandardEpsHom,
		simplicial_ring.UniverseEmbeddingHost,
		simplicial_ring.TagInjective,
		simplicial_ring.TagsDisjoint,
		simplicial_ring.UniverseAlgebraEvalDef,
		free_algebra.FreeAlgebraEvalHom,
		free_algebra.FreeAlgebraEvalConst,
		free_algebra.FreeAlgebraCommRingOn,
		free_algebra.FreeAlgebraConstHom,
		free_algebra.FreeAlgebraVarIn,
		free_algebra.FreeAlgebraHomomorphismDef,
		functions.InverseOnLeft,
		ring_homomorphism.MapIn,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀T:ring_ops(C). ∀f:(A → B). ∀g:(B → C). ∀q:num.",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"cotangent_universe(T, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"ring_homomorphism(S, T, g)",
		},
		Conclusion: "free_algebra_homomorphism(universe_embedding⟨U:U⟩(R), " +
			"    universe_embedding(S), " +
			"    R, " +
			"    S, " +
			"    f, " +
			"    image(universe_tag(0), standard_names(R, S, 0)) ∪ " +
			"    image(universe_tag(1), relative_names(R, S, T, 0, q)), " +
			"    standard_names(S, T, q), " +
			"    relative_horizontal_eps(R, S, f, q))",
	},
		"f carries R's carrier into S's (MapIn); the map is an evaluation into the free algebra over "+
			"S on all of U, a commutative ring at the universe embedding of S (FreeAlgebraCommRingOn, "+
			"UniverseEmbeddingHost for S), with the constants after f as coefficient map, a ring map "+
			"(FreeAlgebraConstHom); its values at the names of (0, q) lie in the algebra on "+
			"standard_names(S, T, q): P's names of degree 0 go to constants of the augmentation's values "+
			"(StandardEpsHom), and the second tag of a relative name w to the variable over S of w itself "+
			"at q = 0, where the relative names are standard_names(S, T, 0) (RelativeNamesZero), and of "+
			"the augmentation of degree q − 1 at w ∈ relative_terms(R, S, T, 0, q − 1) above, a member of "+
			"standard_terms(S, T, q − 1) = standard_names(S, T, q) by induction on q (TagInjective, "+
			"TagsDisjoint, InverseOnLeft, FreeAlgebraVarIn); FreeAlgebraEvalHom and FreeAlgebraEvalConst"),
})}

// RelativeHorizontalEpsVertical — in a universe for R, S and T, the
// augmentation of the rows is a simplicial map from the column of P's
// 0-simplices to the standard resolution of T over S, over T.
var RelativeHorizontalEpsVertical = relativeHorizontalEpsVerticalThm{family.Add(registry.ProofEntry{
	Name: "RelativeHorizontalEpsVertical",
	Key:  "prop_d53dd845f549a497",
	Deps: []registry.EntryLike{
		RelativeHorizontalEpsHom,
		RelativeVerticalHom,
		RelativeVerticalFixesBase,
		RelativeVerticalEpsHom,
		RelativeHorizontalEpsDef,
		RelativeVerticalFaceDef,
		RelativeVerticalDegeneracyDef,
		relativeNameMapDef,
		StandardFacesHom,
		StandardDegeneraciesHom,
		StandardEpsHom,
		StandardFaceDef,
		StandardDegeneracyDef,
		simplicial_ring.TagInjective,
		simplicial_ring.TagsDisjoint,
		simplicial_ring.CarrierTagInjective,
		free_algebra.FreeAlgebraEvalVar,
		free_algebra.FreeAlgebraMapVar,
		free_algebra.FreeAlgebraEvalUnique,
		functions.InverseOnLeft,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀T:ring_ops(C). ∀f:(A → B). ∀g:(B → C).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"cotangent_universe(T, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"ring_homomorphism(S, T, g)",
		},
		Conclusion: "(∀q j:num. ∀u:U. " +
			"    u ∈ relative_terms(R, S, T, 0, q + 1) ∧ j ≤ q + 1 ⇒ " +
			"    relative_horizontal_eps(R, S, f, q, «verticalFace»(0, q + 1, j, u)) = " +
			"    standard_face(S, T, g, q + 1, j, relative_horizontal_eps(R, S, f, q + 1, u))) ∧ " +
			"(∀q j:num. ∀u:U. " +
			"    u ∈ relative_terms(R, S, T, 0, q) ∧ j ≤ q ⇒ " +
			"    relative_horizontal_eps(R, S, f, q + 1, relative_vertical_degeneracy(R, q, j, u)) = " +
			"    standard_degeneracy(S, q, j, relative_horizontal_eps(R, S, f, q, u))) ∧ " +
			"(∀u:U. " +
			"    u ∈ relative_terms(R, S, T, 0, 0) ⇒ " +
			"    standard_eps(S, T, g, relative_horizontal_eps(R, S, f, 0, u)) = " +
			"    relative_vertical_eps(R, S, f, T, g, 0, u))",
	},
		"on the variables, every side being a ring map over f (RelativeHorizontalEpsHom, "+
			"RelativeVerticalHom; StandardFacesHom, StandardDegeneraciesHom and StandardEpsHom for T "+
			"over S; FreeAlgebraEvalUnique). P's variables are fixed by the vertical maps "+
			"(RelativeVerticalFixesBase) and go to constants, which the faces and degeneracies over S "+
			"fix. The second tag of w goes to the variable over S of the augmentation at w: the face 0 "+
			"untags on both sides, the faces j + 1 and the degeneracies act through the second tag on "+
			"one side and on the variables on the other, and commute by the identity one degree down "+
			"(TagInjective, TagsDisjoint, InverseOnLeft, FreeAlgebraMapVar); in vertical degree 0 that "+
			"base is the third conjunct, both sides ring maps over g ∘ f agreeing on P's variables, "+
			"P's augmentation then g, and reading the second tags of the tags of T's elements back as "+
			"the elements (RelativeVerticalEpsHom, CarrierTagInjective, FreeAlgebraEvalVar)"),
})}

// RelativeAugmentationC — in a universe for R, S and T, the augmentation
// of a (p, q)-simplex onto T, through the vertical 0-th faces and the
// column's augmentation, is the same through any vertical face and in
// the column it is read in.
var RelativeAugmentationC = relativeAugmentationCThm{family.Add(registry.ProofEntry{
	Name: "RelativeAugmentationC",
	Key:  "prop_c79593c43f758495",
	Reading: "With the first conjunct any vertical face gives the augmentation; with the " +
		"second it does not depend on the column, so the simplices of every bidegree map onto T " +
		"compatibly with both directions. At q = 0 the second conjunct is the column augmentations " +
		"commuting with the horizontal faces. Through the row augmentation the same map is the " +
		"standard resolution of T over S augmented onto T (RelativeHorizontalEpsVertical).",
	Deps: []registry.EntryLike{
		RelativeColumnAugmented,
		simplicial_ring.AugmentationAtFaceIndependent,
		simplicial_ring.AugmentationAtDef,
		RelativeDirectionsCommute,
		RelativeVerticalFaceIn,
		RelativeVerticalEpsHom,
		RelativeBaseInclusionNatural,
		StandardToBaseFaceIndependent,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀T:ring_ops(C). ∀f:(A → B). ∀g:(B → C).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"cotangent_universe(T, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"ring_homomorphism(S, T, g)",
		},
		Conclusion: "(∀p q j:num. ∀u:U. " +
			"    u ∈ relative_terms(R, S, T, p, q + 1) ∧ j ≤ q + 1 ⇒ " +
			"    augmentation_at(«verticalFace»(p), «columnEps»(p), q, «verticalFace»(p, q + 1, j, u)) = " +
			"    augmentation_at(«verticalFace»(p), «columnEps»(p), q + 1, u)) ∧ " +
			"(∀p q i:num. ∀u:U. " +
			"    u ∈ relative_terms(R, S, T, p + 1, q) ∧ i ≤ p + 1 ⇒ " +
			"    augmentation_at(«verticalFace»(p), " +
			"        «columnEps»(p), " +
			"        q, " +
			"        relative_horizontal_map(R, standard_face(R, S, f, p + 1, i), q, u)) = " +
			"    augmentation_at(«verticalFace»(p + 1), «columnEps»(p + 1), q, u))",
	},
		"the first conjunct is AugmentationAtFaceIndependent at RelativeColumnAugmented. The "+
			"second inducts on q with AugmentationAtDef: at q = 0 it is the column augmentations "+
			"commuting with the horizontal faces, P's augmentation in degree p after a face being "+
			"the one in degree p + 1 (StandardToBaseFaceIndependent, RelativeVerticalEpsHom, "+
			"RelativeBaseInclusionNatural); at q + 1 the horizontal face commutes with the vertical "+
			"face 0 (RelativeDirectionsCommute), and the vertical face 0 carries u into "+
			"relative_terms(R, S, T, p + 1, q) (RelativeVerticalFaceIn), where the induction applies"),
})}

// ---------------------------------------------------------------------------
// The standard resolution over R inside every column
// ---------------------------------------------------------------------------

// RelativeFromAbsoluteMap — in a universe for R, S and T, the standard
// resolution of T over R through g ∘ f maps into every column of the
// relative standard resolution by an algebra map over T.
var RelativeFromAbsoluteMap = relativeFromAbsoluteMapThm{family.Add(registry.ProofEntry{
	Name: "RelativeFromAbsoluteMap",
	Key:  "prop_ce17d5a2f806d556",
	Reading: "The map does not depend on the column: one function of the host maps the standard " +
		"resolution of T over R into every column, over T when T is an algebra over R through g ∘ f. " +
		"The second conjunct holds in every column because the map lands in degree 0 in the algebra " +
		"on the second tags of T's names, where the column's augmentation reads only those names.",
	Deps: []registry.EntryLike{
		RelativeFromAbsoluteDef,
		StandardPolynomialAlgebra,
		RelativeColumnAugmented,
		RelativeVerticalEpsHom,
		RelativeVerticalFaceDef,
		RelativeVerticalDegeneracyDef,
		relativeNameMapDef,
		RelativeNamesDef,
		RelativeTermsDef,
		StandardNamesDef,
		StandardFaceDef,
		StandardDegeneracyDef,
		StandardEpsDef,
		simplicial_ring.SimplicialAlgebraMap,
		simplicial_ring.TagInjective,
		simplicial_ring.TagsDisjoint,
		simplicial_ring.CarrierTagInjective,
		free_algebra.FreeAlgebraMapHom,
		free_algebra.FreeAlgebraMapVar,
		free_algebra.FreeAlgebraEvalMap,
		free_algebra.FreeAlgebraEvalVar,
		free_algebra.FreeAlgebraMultVar,
		free_algebra.FreeAlgebraMapCompose,
		free_algebra.FreeAlgebraMapCongruence,
		free_algebra.FreeAlgebraEvalUnique,
		functions.InverseOnLeft,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀T:ring_ops(C). ∀f:(A → B). ∀g:(B → C). ∀p:num.",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"cotangent_universe(T, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"ring_homomorphism(S, T, g)",
		},
		Conclusion: "simplicial_algebra_map(R, " +
			"    standard_names⟨U:U⟩(R, T), " +
			"    standard_face(R, T, λa:A. g(f(a))), " +
			"    standard_degeneracy(R), " +
			"    λq:num. " +
			"        image(universe_tag(0), standard_names(R, S, p)) ∪ " +
			"        image(universe_tag(1), relative_names(R, S, T, p, q)), " +
			"    «verticalFace»(p), " +
			"    relative_vertical_degeneracy(R), " +
			"    relative_from_absolute(R)) ∧ " +
			"(∀u:U. " +
			"    u ∈ standard_terms(R, T, 0) ⇒ " +
			"    relative_vertical_eps(R, S, f, T, g, p, relative_from_absolute(R, 0, u)) = " +
			"    standard_eps(R, T, λa:A. g(f(a)), u))",
	},
		"the source is a polynomial simplicial algebra by StandardPolynomialAlgebra at T over R through "+
			"g ∘ f, the target by RelativeColumnAugmented. relative_from_absolute(R, q) is induced on the "+
			"variables (FreeAlgebraMapHom), carrying each name of degree q of the standard resolution of T "+
			"over R to the second tag of a relative name of (p, q): in degree 0 the name itself, the tag of "+
			"an element of T (StandardNamesDef, RelativeNamesDef), and above its image one degree down, a "+
			"member of relative_terms(R, S, T, p, q − 1) (RelativeTermsDef). It commutes with the vertical "+
			"face 0, the untagging after the tagging (TagInjective, InverseOnLeft, FreeAlgebraEvalMap, "+
			"FreeAlgebraMultVar), and with the faces j + 1 and the degeneracies through relative_name_map "+
			"by the identities one degree down (FreeAlgebraMapCompose, FreeAlgebraMapCongruence), whose "+
			"base in degree 0 is the second conjunct: both sides ring maps over g ∘ f reading the variable "+
			"of the tag of t as t (CarrierTagInjective, TagInjective, TagsDisjoint, InverseOnLeft, "+
			"FreeAlgebraEvalVar, FreeAlgebraEvalUnique)"),
})}

// RelativeFromAbsoluteNatural — in a universe for R, every map of a row
// of the relative standard resolution induced by a map of P's simplices
// fixes the image of the standard resolution of T over R.
var RelativeFromAbsoluteNatural = relativeFromAbsoluteNaturalThm{family.Add(registry.ProofEntry{
	Name: "RelativeFromAbsoluteNatural",
	Key:  "prop_5813abd0bc67e204",
	Reading: "h is never read: the map from the standard resolution over R lands in the " +
		"algebra on the second tags of relative names alone, where every horizontal map, a face " +
		"or degeneracy of P's or any other, is the identity. This is the naturality in the column " +
		"of RelativeFromAbsoluteMap. Only R's universe is load-bearing, the second tag being " +
		"injective from degree 1 up; degree 0 needs no injectivity, and T need not be a ring.",
	Deps: []registry.EntryLike{
		RelativeFromAbsoluteDef,
		RelativeHorizontalMapDef,
		simplicial_ring.UniverseEmbeddingHost,
		simplicial_ring.TagInjective,
		simplicial_ring.TagsDisjoint,
		free_algebra.FreeAlgebraMapHom,
		free_algebra.FreeAlgebraMapDef,
		free_algebra.FreeAlgebraEvalMap,
		free_algebra.FreeAlgebraEvalCongruence,
		free_algebra.FreeAlgebraEvalUnique,
		functions.InverseOnLeft,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀T:ring_ops(C). ∀h:(U → U). ∀q:num. ∀u:U.",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"comm_ring_on(R)",
			"u ∈ standard_terms(R, T, q)",
		},
		Conclusion: "relative_horizontal_map(R, h, q, relative_from_absolute(R, q, u)) = " +
			"relative_from_absolute(R, q, u)",
	},
		"induct on q. The value of relative_from_absolute lies in the algebra on second tags "+
			"only (FreeAlgebraMapHom), where the horizontal map, an evaluation, reads its values "+
			"at second tags alone (FreeAlgebraEvalCongruence): in degree 0 it keeps the variable "+
			"of each, so it is the identity there (FreeAlgebraEvalMap, FreeAlgebraMapDef, "+
			"FreeAlgebraEvalUnique); in degree q + 1 it carries the variable of the second tag "+
			"of relative_from_absolute(R, q, w) to the variable of the second tag of its image, "+
			"which is itself by the induction (TagInjective, TagsDisjoint, InverseOnLeft)"),
})}

// ---------------------------------------------------------------------------
// The diagonal
// ---------------------------------------------------------------------------

// RelativeHorizontalGeneratorsClosed — in a universe for R, S and T, the
// map of row q induced by a degeneracy of P carries the variable of every
// name of (p, q) to the variable of a name of (p + 1, q).
var RelativeHorizontalGeneratorsClosed = relativeHorizontalGeneratorsClosedThm{family.Add(registry.ProofEntry{
	Name: "RelativeHorizontalGeneratorsClosed",
	Key:  "prop_b057cbd6e836b678",
	Reading: "Stated on the variables, as polynomial_simplicial_algebra's own condition is. " +
		"P's names go to P's names by P's own closure, and the second tags of relative names to " +
		"second tags of relative names: in row 0 they are simply kept, relative_names(p, 0) " +
		"being the same set in every column; above it a relative name of (p, q + 1) is a member " +
		"of the algebra of (p, q), which the map of row q carries into relative_terms(p + 1, q) " +
		"(RelativeHorizontalHom), that is relative_names(p + 1, q + 1). The maps induced by P's " +
		"faces keep no such closure, P's 0-th face not keeping its variables.",
	Deps: []registry.EntryLike{
		RelativeHorizontalMapDef,
		RelativeHorizontalHom,
		RelativeNamesDef,
		RelativeTermsDef,
		StandardGeneratorsClosed,
		simplicial_ring.UniverseEmbeddingHost,
		simplicial_ring.TagInjective,
		simplicial_ring.TagsDisjoint,
		free_algebra.FreeAlgebraEvalVar,
		free_algebra.FreeAlgebraMapVar,
		functions.InverseOnLeft,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀T:ring_ops(C). ∀f:(A → B). ∀g:(B → C). ∀p q i:num.",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"cotangent_universe(T, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"ring_homomorphism(S, T, g)",
			"i ≤ p",
		},
		Conclusion: "image(relative_horizontal_map⟨U:U⟩(R, standard_degeneracy(R, p, i), q), " +
			"    image(universe_algebra_var(R), " +
			"        image(universe_tag(0), standard_names(R, S, p)) ∪ " +
			"        image(universe_tag(1), relative_names(R, S, T, p, q)))) ⊆ " +
			"image(universe_algebra_var(R), " +
			"    image(universe_tag(0), standard_names(R, S, p + 1)) ∪ " +
			"    image(universe_tag(1), relative_names(R, S, T, p + 1, q)))",
	},
		"the map is an evaluation (RelativeHorizontalMapDef) and takes the variable of a name to its "+
			"value there (FreeAlgebraEvalVar), the two tags told apart (TagInjective, TagsDisjoint, "+
			"InverseOnLeft). The first tag of x ∈ standard_names(R, S, p) goes to the map induced by the "+
			"first tag at P's degeneracy of the variable of x, which is the variable of a name of degree p + "+
			"1 (StandardGeneratorsClosed), so to the variable of its first tag (FreeAlgebraMapVar). The "+
			"second tag of a relative name w is kept in row 0, where the relative names of (p, 0) and (p + "+
			"1, 0) are one set (RelativeNamesDef); in row q + 1 it goes to the variable of the second tag of "+
			"the map of row q at w, a member of relative_terms(R, S, T, p + 1, q) (RelativeHorizontalHom), "+
			"which is a relative name of (p + 1, q + 1) (RelativeNamesDef, RelativeTermsDef)"),
})}

// RelativeDiagonalResolution — in a universe for R, S and T, the diagonal
// of the relative standard resolution, the (n, n)-simplices with the
// faces and degeneracies of the two directions taken together, is a
// polynomial resolution of T over R through g ∘ f, augmented by column
// 0's augmentation.
var RelativeDiagonalResolution = relativeDiagonalResolutionThm{family.Add(registry.ProofEntry{
	Name: "RelativeDiagonalResolution",
	Key:  "prop_4766d2b248d72c82",
	Reading: "The diagonal's 0-simplices are the (0, 0)-simplices and its augmentation is column " +
		"0's; read in degree n through the diagonal's 0-th faces it is column n's augmentation in " +
		"vertical degree n (RelativeAugmentationC). The diagonal has no extra degeneracy of its own: " +
		"its acyclicity comes from the columns' contractions, natural in p, whose diagonal is a " +
		"contraction keeping zero but not additive, all that PointedHomotopyAcyclic reads. G = ι^v ∘ " +
		"ε^v is a bisimplicial map only because ε_{p+1} ∘ s^h_i = ε_p on row 0 (RelativeAugmentationC " +
		"with d^h_i s^h_i = id) and every row-0 horizontal map fixes relative_extra_bottom(c); " +
		"relative_extra commutes with the horizontal maps through inverse_on(𝕌, tag₁, tag₁ u) = u " +
		"(TagInjective). DiagonalHomotopy's end matches PointedHomotopyAcyclic's ι(n, ε_0(last " +
		"vertex)) only on the simplices, through ε_0 ∘ (d^h_0)ⁿ = ε_n on row 0.",
	Deps: []registry.EntryLike{
		simplicial_ring.TagInjective,
		simplicial_ring.PolynomialResolution,
		simplicial_ring.AugmentedPolynomialAlgebra,
		simplicial_ring.PolynomialSimplicialAlgebra,
		simplicial_ring.PolynomialAlgebraSimplicialModule,
		simplicial_ring.AugmentationAtDef,
		RelativeBisimplicialSet,
		RelativeVerticalHom,
		RelativeHorizontalHom,
		RelativeGeneratorsClosed,
		RelativeHorizontalGeneratorsClosed,
		RelativeVerticalEpsHom,
		RelativeColumnAugmented,
		RelativeColumnExtra,
		RelativeAugmentationC,
		RelativeDirectionsCommute,
		RelativeHorizontalMapDef,
		relativeExtraDef,
		relativeExtraBottomDef,
		RelativeTermsDef,
		simplicial_homotopy.DiagonalSimplicialSet,
		simplicial_homotopy.BisimplicialDiagonalSimplicesDef,
		simplicial_homotopy.BisimplicialDiagonalFaceDef,
		simplicial_homotopy.BisimplicialDiagonalDegeneracyDef,
		simplicial_homotopy.ExtraDegeneracyHomotopy,
		simplicial_homotopy.BisimplicialVerticalHomotopy,
		simplicial_homotopy.BisimplicialMap,
		simplicial_homotopy.DiagonalHomotopy,
		simplicial_module.PointedHomotopyAcyclic,
		simplicial_set.BaseSimplexDef,
		ring_homomorphism.AdditiveHomomorphism,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀T:ring_ops(C). ∀f:(A → B). ∀g:(B → C).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"cotangent_universe(T, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"ring_homomorphism(S, T, g)",
		},
		Conclusion: "polynomial_resolution⟨U:U⟩(R, " +
			"    «diagonalNames», " +
			"    «diagonalFaces», " +
			"    «diagonalDegeneracies», " +
			"    T, " +
			"    λa:A. g(f(a)), " +
			"    «columnEps»(0))",
	},
		"the augmented polynomial algebra: the diagonal of RelativeBisimplicialSet is a simplicial "+
			"set (DiagonalSimplicialSet), the free algebra on the names of (n, n) being "+
			"relative_terms(R, S, T, n, n) (RelativeTermsDef); its faces and degeneracies are composites "+
			"of algebra maps (RelativeVerticalHom, RelativeHorizontalHom), the degeneracies keeping the "+
			"variables (RelativeGeneratorsClosed, then RelativeHorizontalGeneratorsClosed); column 0's "+
			"augmentation is a ring map over g ∘ f (RelativeVerticalEpsHom) and coequalizes the two "+
			"faces of a (1, 1)-simplex, the horizontal faces carrying column 1's augmentation to column "+
			"0's (RelativeAugmentationC) and column 1 coequalizing its vertical faces "+
			"(RelativeColumnAugmented). Acyclicity: in column p the contraction (s^v_0)^j ∘ "+
			"relative_extra ∘ (d^v_0)^j runs from the identity to the vertically degenerate section of "+
			"the column's augmentation (ExtraDegeneracyHomotopy at RelativeColumnExtra); relative_extra "+
			"and its bottom commute with the horizontal maps, ring maps acting on second tags through "+
			"the second tag (RelativeHorizontalMapDef, RelativeHorizontalHom, AdditiveHomomorphism), the "+
			"two directions commute (RelativeDirectionsCommute) and the column augmentations agree along "+
			"the horizontal faces (RelativeAugmentationC), so the contractions form a vertical homotopy "+
			"natural in p between two bisimplicial maps (BisimplicialVerticalHomotopy, BisimplicialMap). "+
			"DiagonalHomotopy makes h_j = s^h_j ∘ h^v_j a homotopy on the diagonal from the identity to "+
			"ι(n, c) = (s^v_0)^n(relative_extra_bottom(R, T, c)) after column 0's augmentation of the "+
			"last vertex (AugmentationAtDef, RelativeAugmentationC, BaseSimplexDef). h keeps zero, "+
			"relative_extra keeping zero and every other map being a ring map, and ι(0, ·) is a section "+
			"of column 0's augmentation (RelativeColumnExtra); PointedHomotopyAcyclic at the diagonal's "+
			"simplicial module (PolynomialAlgebraSimplicialModule), with N the module T over R through g "+
			"∘ f, scalar_restriction(λa:A. g(f(a)), regular_module(T)), as in RelativeColumnResolution"),
})}

// RelativeDiagonalBaseInclusion — in a universe for R, S and T, the
// inclusion of P under the first tag is a simplicial algebra map from P to
// the diagonal of the relative standard resolution, and column 0's
// augmentation reads it as g after P's augmentation.
var RelativeDiagonalBaseInclusion = relativeDiagonalBaseInclusionThm{family.Add(registry.ProofEntry{
	Name: "RelativeDiagonalBaseInclusion",
	Key:  "prop_9745d22fc72926b",
	Reading: "On the diagonal the vertical face i fixes P's variables and the horizontal " +
		"face i acts on them as P's face i, so the first tag commutes with the diagonal's faces " +
		"and degeneracies; the second conjunct is RelativeVerticalEpsHom's at column 0, where " +
		"P's augmentation is standard_eps. With RelativeDiagonalFromAbsolute it gives two maps " +
		"from P into one resolution of T covering g, the input of the comparison theorem. It " +
		"covers g, not the identity of T: compared with RelativeDiagonalFromAbsolute, the " +
		"latter needs standard_map(g) in front of it (StandardMapAugmentation).",
	Deps: []registry.EntryLike{
		simplicial_ring.SimplicialAlgebraMap,
		StandardPolynomialAlgebra,
		StandardFacesHom,
		StandardDegeneraciesHom,
		RelativeDiagonalResolution,
		RelativeBaseInclusionHom,
		RelativeBaseInclusionNatural,
		RelativeVerticalFixesBase,
		RelativeVerticalEpsHom,
		StandardToBaseDef,
		simplicial_ring.AugmentationAtDef,
		simplicial_homotopy.BisimplicialDiagonalFaceDef,
		simplicial_homotopy.BisimplicialDiagonalDegeneracyDef,
		simplicial_set.SimplicialMap,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀T:ring_ops(C). ∀f:(A → B). ∀g:(B → C).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"cotangent_universe(T, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"ring_homomorphism(S, T, g)",
		},
		Conclusion: "simplicial_algebra_map⟨U:U⟩(R, " +
			"    standard_names(R, S), " +
			"    standard_face(R, S, f), " +
			"    standard_degeneracy(R), " +
			"    «diagonalNames», " +
			"    «diagonalFaces», " +
			"    «diagonalDegeneracies», " +
			"    λn:num. universe_algebra_map(R, R, λa:A. a, universe_tag(0))) ∧ " +
			"(∀u:U. " +
			"    u ∈ standard_terms(R, S, 0) ⇒ " +
			"    relative_vertical_eps(R, S, f, T, g, 0, «baseInclusion»(u)) = g(standard_eps(R, S, f, u)))",
	},
		"the two ends are polynomial simplicial algebras (StandardPolynomialAlgebra, "+
			"RelativeDiagonalResolution) and the inclusion is an algebra map in every degree "+
			"(RelativeBaseInclusionHom at q = n). At the diagonal face i, the vertical face fixes the "+
			"first tag of P's n-simplices (RelativeVerticalFixesBase) and the map induced by P's face i "+
			"then extends P's face along the inclusion (RelativeBaseInclusionNatural, P's faces algebra "+
			"maps by StandardFacesHom); the degeneracies likewise (RelativeVerticalFixesBase for j ≤ q, "+
			"StandardDegeneraciesHom). The second conjunct is the third of RelativeVerticalEpsHom at p "+
			"= 0, standard_to_base in degree 0 being standard_eps (StandardToBaseDef, AugmentationAtDef)"),
})}

// RelativeDiagonalFromAbsolute — in a universe for R, S and T, the map
// from the standard resolution of T over R through g ∘ f into the columns
// of the relative standard resolution is a simplicial algebra map into
// its diagonal, over T.
var RelativeDiagonalFromAbsolute = relativeDiagonalFromAbsoluteThm{family.Add(registry.ProofEntry{
	Name: "RelativeDiagonalFromAbsolute",
	Key:  "prop_d95774d22fee7f94",
	Reading: "The map is one function of the host for every column, and every horizontal " +
		"map fixes its values (RelativeFromAbsoluteNatural): on the diagonal the horizontal " +
		"half of each face and degeneracy does nothing to its image, and the vertical half is " +
		"the column's, with which it commutes. The second conjunct is RelativeFromAbsoluteMap's " +
		"at column 0. It covers the identity of T in every degree: the diagonal's augmentation " +
		"after relative_from_absolute is standard_eps of T over R in degree 0, and the " +
		"simplicial identities carry this to augmentation_at in each degree.",
	Deps: []registry.EntryLike{
		simplicial_ring.SimplicialAlgebraMap,
		StandardPolynomialAlgebra,
		RelativeDiagonalResolution,
		RelativeFromAbsoluteMap,
		RelativeFromAbsoluteNatural,
		simplicial_homotopy.BisimplicialDiagonalFaceDef,
		simplicial_homotopy.BisimplicialDiagonalDegeneracyDef,
		simplicial_set.SimplicialMap,
		simplicial_set.MapFace,
		simplicial_set.MapDegeneracy,
		simplicial_set.MapIn,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀T:ring_ops(C). ∀f:(A → B). ∀g:(B → C).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"cotangent_universe(T, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"ring_homomorphism(S, T, g)",
		},
		Conclusion: "simplicial_algebra_map⟨U:U⟩(R, " +
			"    standard_names(R, T), " +
			"    standard_face(R, T, λa:A. g(f(a))), " +
			"    standard_degeneracy(R), " +
			"    «diagonalNames», " +
			"    «diagonalFaces», " +
			"    «diagonalDegeneracies», " +
			"    relative_from_absolute(R)) ∧ " +
			"(∀u:U. " +
			"    u ∈ standard_terms(R, T, 0) ⇒ " +
			"    relative_vertical_eps(R, S, f, T, g, 0, relative_from_absolute(R, 0, u)) = " +
			"    standard_eps(R, T, λa:A. g(f(a)), u))",
	},
		"the source is a polynomial simplicial algebra by StandardPolynomialAlgebra at T over R "+
			"through g ∘ f, the target by RelativeDiagonalResolution. In degree n the map is "+
			"RelativeFromAbsoluteMap's into column n, an algebra map carrying the n-simplices into the (n, "+
			"n)-simplices (MapIn); at the diagonal face i the vertical face of column n commutes with it "+
			"(MapFace) and the horizontal map then fixes the image (RelativeFromAbsoluteNatural), likewise "+
			"at the degeneracies (MapDegeneracy); the second conjunct is RelativeFromAbsoluteMap's at p = 0"),
})}
