// right_rows.go — the simplicial sets of names under the rows of the
// right term and the induction that contracts them. The horizontal maps
// of the relative standard resolution carry the variable of a relative
// name to the variable of a relative name, so the relative names of row
// q are a simplicial set, augmented in every column onto the names of
// degree q of the standard resolution of T over S; row q of the right
// term is the chains with values in N on it, augmented by the map of
// chains along the augmentation in column 0. The names of row q + 1 are
// the free algebras on P's names and the names of row q, the diagonal of
// a bisimplicial set in which P's names move in one direction and the
// names of row q in the other; renaming the names of row q by a map of
// simplicial sets acts on it column by column. Replacing the names of row
// q by a fixed set of names W gives free algebras over P's simplices on
// W, which an extra degeneracy acting on the coefficients contracts onto
// the free algebra over S on W.

package transitivity

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/cotangent_complex"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/simplicial_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/standard_resolution"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/chain_complex"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/free_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/tor_ext"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/partial_derivative"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/free_algebra"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/simplicial/simplicial_homotopy"
	"github.com/euc-ai/xugo/library/proofs/simplicial/simplicial_module"
	"github.com/euc-ai/xugo/library/proofs/simplicial/simplicial_set"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The rows as simplicial sets of names
// ---------------------------------------------------------------------------

// triangleRowNameDef — `triangle_row_name(R, h, q, z)`: the relative name
// of row q that the map of the row induced by h carries the relative name
// z to — z itself in row 0, and in row q + 1, where the names are the
// (p, q)-simplices, the map of row q at z.
var triangleRowNameDef = triangleRowNameDefThm{family.Define(registry.DefEntry{
	Name:  "triangleRowNameDef",
	Key:   "prop_13644bb17ce2ec2a",
	Const: "triangle_row_name",
	Type:  "ring_ops(A) → (U → U) → num → U → U",
	Equations: []string{
		"∀R:ring_ops(A). ∀h:(U → U). triangle_row_name(R, h, 0) = (λz:U. z)",
		"∀R:ring_ops(A). ∀h:(U → U). ∀q:num. " +
			"    triangle_row_name(R, h, suc(q)) = relative_horizontal_map(R, h, q)",
	},
	Reading: "relative_horizontal_map(R, h, q) carries the variable of the second tag of a " +
		"relative name z of row q to the variable of the second tag of triangle_row_name(R, h, q, z), so " +
		"the faces and degeneracies of row q's simplicial set of names are triangle_row_name(R, " +
		"standard_face(R, S, f, p, i), q) and triangle_row_name(R, standard_degeneracy(R, p, i), q). In " +
		"row 0 the names are the tags of T's elements in every column and every map keeps them. At q = 1 " +
		"the map moves P's names and keeps every name under the second tag, whatever set they come from.",
})}

// TriangleRowAugmentationDef — `triangle_row_augmentation(R, S, f, p, q,
// z)`: the name of degree q of the standard resolution of T over S that
// the relative name z of row q in column p goes to — z itself in row 0,
// and in row q + 1 the (p, q)-simplex z evaluated over S: each
// coefficient carried by f, each of P's names to the constant of its
// value under P's augmentation in degree p, and each relative name of row
// q to the variable of its augmentation.
var TriangleRowAugmentationDef = triangleRowAugmentationDefThm{family.Define(registry.DefEntry{
	Name:  "TriangleRowAugmentationDef",
	Key:   "prop_1023dfb4a4ebcbb7",
	Const: "triangle_row_augmentation",
	Type:  "ring_ops(A) → ring_ops(B) → (A → B) → num → num → U → U",
	Equations: []string{
		"∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B). ∀p:num. " +
			"    triangle_row_augmentation(R, S, f, p, 0) = (λz:U. z)",
		"∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B). ∀p q:num. " +
			"    triangle_row_augmentation(R, S, f, p, suc(q)) = " +
			"    (λz:U. " +
			"        universe_algebra_eval(R, " +
			"            universe_algebra_ring(S, 𝕌⟨A:U⟩), " +
			"            λa:A. universe_algebra_const(S, f(a)), " +
			"            λy:U. " +
			"                COND(y ∈ image(universe_tag(1), 𝕌⟨A:U⟩), " +
			"                    universe_algebra_var(S, " +
			"                        triangle_row_augmentation(R, " +
			"                            S, " +
			"                            f, " +
			"                            p, " +
			"                            q, " +
			"                            inverse_on(𝕌⟨A:U⟩, universe_tag(1), y))), " +
			"                    universe_algebra_const(S, " +
			"                        standard_to_base(R, " +
			"                            S, " +
			"                            f, " +
			"                            p, " +
			"                            universe_algebra_var(R, inverse_on(𝕌⟨A:U⟩, universe_tag(0), y))))), " +
			"            z))",
	},
	Reading: "It is the augmentation of row q's simplicial set of names onto the constant " +
		"simplicial set standard_names(S, T, q): a simplicial map because P's augmentation reads any " +
		"face (StandardToBaseFaceIndependent). In column 0 the evaluation in row q + 1 is " +
		"relative_horizontal_eps(R, S, f, q), P's augmentation in degree 0 being standard_eps; in row " +
		"0 the relative names are standard_names(S, T, 0) (RelativeNamesZero) and the augmentation is " +
		"the identity. It reads neither T nor g. The same formula in row 1 augments the free algebras " +
		"on P's names and the second tags of any set of names W onto universe_algebra(S, W).",
})}

// TriangleRightEpsDef — `triangle_right_eps(R, S, f, T, N, q, u)`: the
// augmentation of row q of the right term, from column 0 to the term of
// degree q of the cotangent complex of T over S — the chains with values
// in N on the relative names of (0, q) carried along the row's
// augmentation in column 0.
var TriangleRightEpsDef = triangleRightEpsDefThm{family.Define(registry.DefEntry{
	Name:  "TriangleRightEpsDef",
	Key:   "prop_860d4cfeb857d02e",
	Const: "triangle_right_eps",
	Type: "ring_ops(A) → " +
		"ring_ops(B) → " +
		"(A → B) → " +
		"ring_ops(C) → " +
		"module_ops(C, D) → " +
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
			"∀q:num. " +
			"∀u:(U → D). " +
			"    triangle_right_eps(R, S, f, T, N, q, u) = " +
			"    finite_supp_map(T, N, free_pushforward(T, triangle_row_augmentation(R, S, f, 0, q)), u)",
	},
	Reading: "The augmented row q is the chains with values in N on the augmented simplicial set " +
		"of relative names of row q. It is also the Jacobian of relative_horizontal_eps(R, S, f, q) " +
		"read at the second tags, the coefficients through the augmentation of the standard resolution " +
		"of T over S: that map carries the variable of the second tag of a relative name to the " +
		"variable over S of its augmentation, whose derivative is one, and P's names to constants.",
	Deps: []registry.EntryLike{TriangleRowAugmentationDef},
})}

// ---------------------------------------------------------------------------
// The bisimplicial set of the induction and the fixed names
// ---------------------------------------------------------------------------

// triangleFixedNamesDef — `triangle_fixed_names(R, S, W, p)`: the free
// algebra over R on P's names of degree p under the first tag and the
// names W, which do not move with p, under the second.
var triangleFixedNamesDef = triangleFixedNamesDefThm{family.Define(registry.DefEntry{
	Name:  "triangleFixedNamesDef",
	Key:   "prop_8a6743760f0d1ae6",
	Const: "triangle_fixed_names",
	Type:  "ring_ops(A) → ring_ops(B) → set(U) → num → set(U)",
	Equations: []string{
		"∀R:ring_ops(A). ∀S:ring_ops(B). ∀W:set(U). ∀p:num. " +
			"    triangle_fixed_names(R, S, W, p) = " +
			"    universe_algebra(R, " +
			"        image(universe_tag(0), standard_names(R, S, p)) ∪ image(universe_tag(1), W))",
	},
	Reading: "W is a set of untagged names. Its faces and degeneracies are " +
		"triangle_row_name(R, ·, 1) at P's, which move P's names and keep W, and its augmentation is " +
		"triangle_row_augmentation(R, S, f, p, 1), onto the free algebra over S on W; at W = " +
		"standard_names(S, T, q) that is standard_names(S, T, q + 1). The relative names of row 1 " +
		"are the case W = standard_names(S, T, 0), the relative names of row 0. Its extra degeneracy " +
		"acts on the coefficients along W by P's, keeps zero and does not satisfy s_0 σ = σ σ.",
})}

// triangleAuxiliaryDef — `triangle_auxiliary(R, S, T, q, p, p')`: the
// bisimplicial set whose diagonal is the relative names of row q + 1 —
// the free algebra over R on P's names of degree p under the first tag
// and the relative names of row q in column p' under the second.
var triangleAuxiliaryDef = triangleAuxiliaryDefThm{family.Define(registry.DefEntry{
	Name:  "triangleAuxiliaryDef",
	Key:   "prop_c52a6736560e1133",
	Const: "triangle_auxiliary",
	Type:  "ring_ops(A) → ring_ops(B) → ring_ops(C) → num → num → num → set(U)",
	Equations: []string{
		"∀R:ring_ops(A). ∀S:ring_ops(B). ∀T:ring_ops(C). ∀q p p':num. " +
			"    triangle_auxiliary(R, S, T, q, p, p') = " +
			"    triangle_fixed_names(R, S, relative_names(R, S, T, p', q), p)",
	},
	Reading: "It is built from row q and serves the step to row q + 1: at p' = p it is " +
		"relative_terms(R, S, T, p, q), which is relative_names(R, S, T, p, q + 1). Its maps in the " +
		"direction of p are triangle_row_name(R, ·, 1) at P's faces and degeneracies, moving P's " +
		"names, and in the direction of p' they are triangle_rename(R, triangle_row_name(R, ·, q)) at " +
		"P's, moving the names of row q; the diagonal composite of the two is triangle_row_name(R, ·, " +
		"q + 1). At q = 0 the relative names of row 0 do not depend on p', so triangle_auxiliary(R, " +
		"S, T, 0) is triangle_fixed_names(R, S, standard_names(S, T, 0)) in every p'.",
	Deps: []registry.EntryLike{triangleFixedNamesDef},
})}

// triangleRenameDef — `triangle_rename(R, F, w)`: the map of the free
// algebra over R that renames each variable under the second tag by F,
// the second tag of z going to the second tag of F(z), and keeps every
// other variable.
var triangleRenameDef = triangleRenameDefThm{family.Define(registry.DefEntry{
	Name:  "triangleRenameDef",
	Key:   "prop_f0dfffa5346886e4",
	Const: "triangle_rename",
	Type:  "ring_ops(A) → (U → U) → U → U",
	Equations: []string{
		"∀R:ring_ops(A). ∀F:(U → U). ∀w:U. " +
			"    triangle_rename(R, F, w) = " +
			"    universe_algebra_map(R, " +
			"        R, " +
			"        λa:A. a, " +
			"        λy:U. " +
			"            COND(y ∈ image(universe_tag(1), 𝕌⟨A:U⟩), " +
			"                universe_tag(1, F(inverse_on(𝕌⟨A:U⟩, universe_tag(1), y))), " +
			"                y), " +
			"        w)",
	},
	Reading: "It is the free algebra over P's simplices applied to a map of the second-tag " +
		"names: P's names, under the first tag, are kept when the two tags have disjoint images. The " +
		"maps of triangle_auxiliary in the direction of p' are triangle_rename(R, triangle_row_name(R, " +
		"h, q)), and a simplicial map or homotopy of row q's names renames, column by column and " +
		"naturally in p, into one of the bisimplicial sets triangle_fixed_names(R, S, Z(p'), p).",
})}

// ---------------------------------------------------------------------------
// The bisimplicial set of the induction
// ---------------------------------------------------------------------------

// AuxiliaryBisimplicial — in a universe for the tower, triangle_auxiliary
// at row q is a bisimplicial set whose diagonal is the simplicial set of
// relative names of row q + 1.
var AuxiliaryBisimplicial = auxiliaryBisimplicialThm{family.Add(registry.ProofEntry{
	Name: "AuxiliaryBisimplicial",
	Key:  "prop_49eb900e17707988",
	Reading: "The diagonal is literal: at p' = p the set is relative_terms(R, S, T, p, q), the " +
		"names of row q + 1, and the composite of the two directions' maps is the row's map. The two " +
		"directions move disjoint sets of variables — P's names under the first tag, row q's names " +
		"under the second — which is why they commute, under TagInjective and TagsDisjoint. At q = 0 " +
		"the vertical maps are rename(id), the identity, and the auxiliary is constant in p'. The " +
		"diagonal face and degeneracy equal the row's only on members of relative_names — both sides " +
		"are evaluations, unrelated off the free algebra — so the membership hypotheses are load-bearing.",
	Deps: []registry.EntryLike{
		triangleAuxiliaryDef,
		triangleFixedNamesDef,
		triangleRenameDef,
		triangleRowNameDef,
		standard_resolution.RelativeNamesDef,
		standard_resolution.RelativeTermsDef,
		standard_resolution.RelativeHorizontalMapDef,
		standard_resolution.RelativeHorizontalSimplicial,
		standard_resolution.RelativeHorizontalHom,
		standard_resolution.RelativeBaseInclusionNatural,
		standard_resolution.StandardSimplicialSet,
		simplicial_homotopy.BisimplicialSet,
		simplicial_homotopy.BisimplicialDiagonalFaceDef,
		simplicial_homotopy.BisimplicialDiagonalDegeneracyDef,
		free_algebra.FreeAlgebraEvalUnique,
		free_algebra.FreeAlgebraMapDef,
		simplicial_ring.TagInjective,
		simplicial_ring.TagsDisjoint,
		simplicial_ring.UniverseEmbeddingHost,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀T:ring_ops(C). " +
			"∀g:(B → C). " +
			"∀N:module_ops(C, D). " +
			"∀q:num.",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"cotangent_universe(T, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"ring_homomorphism(S, T, g)",
			"module_on(T, N)",
		},
		Conclusion: "bisimplicial_set(mk_bisimplicial(triangle_auxiliary⟨U:U⟩(R, S, T, q), " +
			"        λp:num. λp':num. λi:num. triangle_row_name(R, standard_face(R, S, f, p, i), 1), " +
			"        λp:num. λp':num. λi:num. triangle_row_name(R, standard_degeneracy(R, p, i), 1), " +
			"        λp:num. λp':num. λi:num. " +
			"            triangle_rename(R, triangle_row_name(R, standard_face(R, S, f, p', i), q)), " +
			"        λp:num. λp':num. λi:num. " +
			"            triangle_rename(R, triangle_row_name(R, standard_degeneracy(R, p', i), q)))) ∧ " +
			"(∀p:num. triangle_auxiliary⟨U:U⟩(R, S, T, q, p, p) = relative_names(R, S, T, p, q + 1)) ∧ " +
			"(∀p i:num. ∀z:U. " +
			"    i ≤ p + 1 ∧ z ∈ relative_names(R, S, T, p + 1, q + 1) ⇒ " +
			"    bisimplicial_diagonal_face( " +
			"        λp:num. λp':num. λi:num. triangle_row_name(R, standard_face(R, S, f, p, i), 1), " +
			"        λp:num. λp':num. λi:num. " +
			"            triangle_rename(R, triangle_row_name(R, standard_face(R, S, f, p', i), q)), " +
			"        p + 1, " +
			"        i, " +
			"        z) = " +
			"    triangle_row_name(R, standard_face(R, S, f, p + 1, i), q + 1, z)) ∧ " +
			"(∀p i:num. ∀z:U. " +
			"    i ≤ p ∧ z ∈ relative_names(R, S, T, p, q + 1) ⇒ " +
			"    bisimplicial_diagonal_degeneracy( " +
			"        λp:num. λp':num. λi:num. triangle_row_name(R, standard_degeneracy(R, p, i), 1), " +
			"        λp:num. λp':num. λi:num. " +
			"            triangle_rename(R, triangle_row_name(R, standard_degeneracy(R, p', i), q)), " +
			"        p, " +
			"        i, " +
			"        z) = " +
			"    triangle_row_name(R, standard_degeneracy(R, p, i), q + 1, z))",
	},
		"every map is an algebra map over R of free algebras in the universe "+
			"(UniverseEmbeddingHost, RelativeHorizontalHom at row 0, FreeAlgebraMapDef) fixed by its "+
			"values at the variables (FreeAlgebraEvalUnique). In the direction of p a map moves the "+
			"variables of P's names by P's face or degeneracy carried by the first tag "+
			"(RelativeBaseInclusionNatural) and keeps each second-tag variable; in the direction of p' "+
			"it keeps P's variables and renames the second-tag ones by row q's map (triangleRenameDef, "+
			"TagInjective, TagsDisjoint). So the identities of each direction are P's "+
			"(StandardSimplicialSet) or those of row q's names (RelativeHorizontalSimplicial read at "+
			"the variables, and the identities at row 0), and the two directions commute. At p' = p "+
			"the set is relative_terms(R, S, T, p, q) (triangleAuxiliaryDef, triangleFixedNamesDef, "+
			"RelativeTermsDef), which is relative_names(R, S, T, p, q + 1) (RelativeNamesDef); the "+
			"composite of the two maps moves P's names by P's map and the second-tag names by row q's, "+
			"which is relative_horizontal_map(R, h, q) (RelativeHorizontalMapDef, triangleRowNameDef)"),
})}

// AuxiliaryColumnHomotopyNatural — a simplicial homotopy of maps out of
// row q's names renames, column by column, into a vertical homotopy of
// triangle_auxiliary at row q, natural in the direction of P's names.
var AuxiliaryColumnHomotopyNatural = auxiliaryColumnHomotopyNaturalThm{family.Add(registry.ProofEntry{
	Name: "AuxiliaryColumnHomotopyNatural",
	Key:  "prop_3a280c96afe2c261",
	Reading: "This is where the induction on rows needs a homotopy of simplicial sets rather than " +
		"of chains: renaming is a functor on sets of names, and by any map of names, additive or not, " +
		"it is a ring map of the free algebra over P's simplices, so it carries every identity of H, F, " +
		"G, dz and sz on the names to the same identity of the renamed maps, checked on generators. The " +
		"target is the bisimplicial set of free algebras on P's names and Z, constant in p' when Z is.",
	Deps: []registry.EntryLike{
		AuxiliaryBisimplicial,
		triangleRenameDef,
		triangleFixedNamesDef,
		triangleAuxiliaryDef,
		simplicial_homotopy.SimplicialHomotopy,
		simplicial_homotopy.BisimplicialVerticalHomotopy,
		simplicial_homotopy.BisimplicialMap,
		simplicial_homotopy.BisimplicialSet,
		standard_resolution.RelativeBaseInclusionNatural,
		free_algebra.FreeAlgebraEvalUnique,
		free_algebra.FreeAlgebraMapDef,
		simplicial_ring.TagInjective,
		simplicial_ring.TagsDisjoint,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀T:ring_ops(C). " +
			"∀g:(B → C). " +
			"∀N:module_ops(C, D). " +
			"∀q:num. " +
			"∀Z:simplicial_ops(U). " +
			"∀F G:(num → U → U). " +
			"∀H:(num → num → U → U).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"cotangent_universe(T, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"ring_homomorphism(S, T, g)",
			"module_on(T, N)",
			"simplicial_homotopy(mk_simplicial(λp:num. relative_names(R, S, T, p, q), " +
				"        λp:num. λi:num. triangle_row_name(R, standard_face(R, S, f, p, i), q), " +
				"        λp:num. λi:num. triangle_row_name(R, standard_degeneracy(R, p, i), q)), " +
				"    Z, " +
				"    F, " +
				"    G, " +
				"    H)",
		},
		Conclusion: "bisimplicial_vertical_homotopy(mk_bisimplicial(triangle_auxiliary(R, S, T, q), " +
			"        λp:num. λp':num. λi:num. triangle_row_name(R, standard_face(R, S, f, p, i), 1), " +
			"        λp:num. λp':num. λi:num. triangle_row_name(R, standard_degeneracy(R, p, i), 1), " +
			"        λp:num. λp':num. λi:num. " +
			"            triangle_rename(R, triangle_row_name(R, standard_face(R, S, f, p', i), q)), " +
			"        λp:num. λp':num. λi:num. " +
			"            triangle_rename(R, triangle_row_name(R, standard_degeneracy(R, p', i), q))), " +
			"    mk_bisimplicial(λp:num. λp':num. triangle_fixed_names(R, S, Z.simplices(p'), p), " +
			"        λp:num. λp':num. λi:num. triangle_row_name(R, standard_face(R, S, f, p, i), 1), " +
			"        λp:num. λp':num. λi:num. triangle_row_name(R, standard_degeneracy(R, p, i), 1), " +
			"        λp:num. λp':num. λi:num. triangle_rename(R, Z.d(p', i)), " +
			"        λp:num. λp':num. λi:num. triangle_rename(R, Z.s(p', i))), " +
			"    λp:num. λp':num. triangle_rename(R, F(p')), " +
			"    λp:num. λp':num. triangle_rename(R, G(p')), " +
			"    λp:num. λp':num. λj:num. triangle_rename(R, H(p', j)))",
	},
		"renaming by a map of names carries the free algebra on P's names and Y(p') into the one on "+
			"P's names and Z.simplices(p') (triangleRenameDef, FreeAlgebraMapDef, TagInjective, "+
			"TagsDisjoint); each identity of H, F, G, dz and sz between maps of names is the same "+
			"identity between their renamings, which are algebra maps fixed by the variables "+
			"(FreeAlgebraEvalUnique); the maps in the direction of p move P's names only "+
			"(RelativeBaseInclusionNatural), so they commute with every renaming; the source is a "+
			"bisimplicial set by AuxiliaryBisimplicial and the target likewise, Z being a simplicial set"),
})}

// AuxiliaryToFixedNames — a contraction of row q's names onto the
// standard resolution of T over S renames into a contraction of the names
// of row q + 1 onto the free algebras on P's names and the names of
// degree q of that resolution.
var AuxiliaryToFixedNames = auxiliaryToFixedNamesThm{family.Add(registry.ProofEntry{
	Name: "AuxiliaryToFixedNames",
	Key:  "prop_62ebc380c465988d",
	Reading: "The hypothesis is the induction's for row q, with its section and its " +
		"homotopy explicit; the conclusion keeps them explicit for the diagonal, where " +
		"DiagonalHomotopy gives one homotopy, h_j = sh_j ∘ rename(H_q(n, j)), a ring map in " +
		"x. At q = 0 the hypothesis holds by the identities and triangle_auxiliary is " +
		"constant in p': the row-1 step is this card with nothing renamed, its conclusion the " +
		"identity data on triangle_fixed_names(standard_names(S, T, 0)) = relative_names(·, 1).",
	Deps: []registry.EntryLike{
		AuxiliaryColumnHomotopyNatural,
		AuxiliaryBisimplicial,
		triangleRenameDef,
		TriangleRowAugmentationDef,
		triangleFixedNamesDef,
		simplicial_homotopy.DiagonalHomotopy,
		simplicial_homotopy.DiagonalMap,
		simplicial_homotopy.HomotopyTrivial,
		simplicial_homotopy.BisimplicialMap,
		free_algebra.FreeAlgebraEvalUnique,
		standard_resolution.StandardNamesDef,
		standard_resolution.RelativeBaseInclusionNatural,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀T:ring_ops(C). " +
			"∀g:(B → C). " +
			"∀N:module_ops(C, D). " +
			"∀q:num.",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"cotangent_universe(T, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"ring_homomorphism(S, T, g)",
			"module_on(T, N)",
			"∃ι:(num → U → U). ∃H:(num → num → U → U). " +
				"    simplicial_map(mk_simplicial(λp:num. relative_names(R, S, T, p, q), " +
				"            λp:num. λi:num. triangle_row_name(R, standard_face(R, S, f, p, i), q), " +
				"            λp:num. λi:num. triangle_row_name(R, standard_degeneracy(R, p, i), q)), " +
				"        mk_simplicial(λn:num. standard_names(S, T, q), " +
				"            λn:num. λi:num. λz:U. z, " +
				"            λn:num. λi:num. λz:U. z), " +
				"        λp:num. triangle_row_augmentation(R, S, f, p, q)) ∧ " +
				"    simplicial_map(mk_simplicial(λn:num. standard_names(S, T, q), " +
				"            λn:num. λi:num. λz:U. z, " +
				"            λn:num. λi:num. λz:U. z), " +
				"        mk_simplicial(λp:num. relative_names(R, S, T, p, q), " +
				"            λp:num. λi:num. triangle_row_name(R, standard_face(R, S, f, p, i), q), " +
				"            λp:num. λi:num. triangle_row_name(R, standard_degeneracy(R, p, i), q)), " +
				"        ι) ∧ " +
				"    (∀n:num. ∀z:U. " +
				"        z ∈ standard_names(S, T, q) ⇒ triangle_row_augmentation(R, S, f, n, q, ι(n, z)) = z) ∧ " +
				"    simplicial_homotopy(mk_simplicial(λp:num. relative_names(R, S, T, p, q), " +
				"            λp:num. λi:num. triangle_row_name(R, standard_face(R, S, f, p, i), q), " +
				"            λp:num. λi:num. triangle_row_name(R, standard_degeneracy(R, p, i), q)), " +
				"        mk_simplicial(λp:num. relative_names(R, S, T, p, q), " +
				"            λp:num. λi:num. triangle_row_name(R, standard_face(R, S, f, p, i), q), " +
				"            λp:num. λi:num. triangle_row_name(R, standard_degeneracy(R, p, i), q)), " +
				"        λn:num. λx:U. x, " +
				"        λn:num. λx:U. ι(n, triangle_row_augmentation(R, S, f, n, q, x)), " +
				"        H)",
		},
		Conclusion: "∃ι:(num → U → U). ∃H:(num → num → U → U). " +
			"    simplicial_map(mk_simplicial(λp:num. relative_names(R, S, T, p, q + 1), " +
			"            λp:num. λi:num. triangle_row_name(R, standard_face(R, S, f, p, i), q + 1), " +
			"            λp:num. λi:num. triangle_row_name(R, standard_degeneracy(R, p, i), q + 1)), " +
			"        mk_simplicial(λp:num. triangle_fixed_names(R, S, standard_names(S, T, q), p), " +
			"            λp:num. λi:num. triangle_row_name(R, standard_face(R, S, f, p, i), 1), " +
			"            λp:num. λi:num. triangle_row_name(R, standard_degeneracy(R, p, i), 1)), " +
			"        λp:num. triangle_rename⟨U:U⟩(R, triangle_row_augmentation(R, S, f, p, q))) ∧ " +
			"    simplicial_map(mk_simplicial( " +
			"            λp:num. triangle_fixed_names(R, S, standard_names(S, T, q), p), " +
			"            λp:num. λi:num. triangle_row_name(R, standard_face(R, S, f, p, i), 1), " +
			"            λp:num. λi:num. triangle_row_name(R, standard_degeneracy(R, p, i), 1)), " +
			"        mk_simplicial(λp:num. relative_names(R, S, T, p, q + 1), " +
			"            λp:num. λi:num. triangle_row_name(R, standard_face(R, S, f, p, i), q + 1), " +
			"            λp:num. λi:num. triangle_row_name(R, standard_degeneracy(R, p, i), q + 1)), " +
			"        ι) ∧ " +
			"    (∀n:num. ∀z:U. " +
			"        z ∈ triangle_fixed_names(R, S, standard_names(S, T, q), n) ⇒ " +
			"        triangle_rename(R, triangle_row_augmentation(R, S, f, n, q), ι(n, z)) = z) ∧ " +
			"    simplicial_homotopy(mk_simplicial(λp:num. relative_names(R, S, T, p, q + 1), " +
			"            λp:num. λi:num. triangle_row_name(R, standard_face(R, S, f, p, i), q + 1), " +
			"            λp:num. λi:num. triangle_row_name(R, standard_degeneracy(R, p, i), q + 1)), " +
			"        mk_simplicial(λp:num. relative_names(R, S, T, p, q + 1), " +
			"            λp:num. λi:num. triangle_row_name(R, standard_face(R, S, f, p, i), q + 1), " +
			"            λp:num. λi:num. triangle_row_name(R, standard_degeneracy(R, p, i), q + 1)), " +
			"        λn:num. λx:U. x, " +
			"        λn:num. λx:U. ι(n, triangle_rename(R, triangle_row_augmentation(R, S, f, n, q), x)), " +
			"        H)",
	},
		"rename the data of the hypothesis column by column: the augmentation, a map out of row q's "+
			"names, renames into a bisimplicial map (AuxiliaryColumnHomotopyNatural at its trivial homotopy, "+
			"HomotopyTrivial); the section, a map out of the constant simplicial set standard_names(S, T, q) "+
			"that AuxiliaryColumnHomotopyNatural does not cover, renames into a bisimplicial map "+
			"triangle_fixed_names(R, S, standard_names(S, T, q), ·) → triangle_auxiliary(q) directly from "+
			"BisimplicialMap's definition, checked on variables — a renaming is a ring map of the free "+
			"algebra fixed by its values on the variables (FreeAlgebraEvalUnique), each simplicial identity "+
			"of the section becomes the same identity of its renaming, and the maps in the direction of p "+
			"move P's names only (RelativeBaseInclusionNatural); the section after the augmentation renames "+
			"to the identity of the constant side, and the homotopy from the identity to the section after "+
			"the augmentation renames into a vertical homotopy (AuxiliaryColumnHomotopyNatural). On the "+
			"diagonal (AuxiliaryBisimplicial) the renamed maps are simplicial maps (DiagonalMap) and the "+
			"renamed homotopy a simplicial homotopy (DiagonalHomotopy); the renamed augmentation is "+
			"triangle_rename(R, triangle_row_augmentation(R, S, f, p, q)) on relative_names(R, S, T, p, q + "+
			"1), into triangle_fixed_names(R, S, standard_names(S, T, q), p), constant in p' "+
			"(triangleFixedNamesDef)"),
})}

// ---------------------------------------------------------------------------
// The fixed names contract
// ---------------------------------------------------------------------------

// FixedNamesExtra — the free algebras on P's names and a fixed set of
// names W, augmented onto the free algebra over S on W, have an extra
// degeneracy that keeps zero.
var FixedNamesExtra = fixedNamesExtraThm{family.Add(registry.ProofEntry{
	Name: "FixedNamesExtra",
	Key:  "prop_39f2bcc9f29c5207",
	Reading: "The extra degeneracy is P's acting on the coefficients along W: write a member " +
		"as Σ_m c_m · m over the monomials m of W's variables with coefficients c_m in the algebra " +
		"on P's names, and send it to Σ_m σ(c_m) · m. σ(0) = 0 and b(0) = 0 are load-bearing: a " +
		"face may kill a coefficient, and only zero-keeping makes the coefficientwise σ commute " +
		"with it. It satisfies the three families of identities and the bottom one, not s_0 σ = σ " +
		"σ: s_0 σ(u) = var var u − var var 0 while σ σ(u) = var(var u − var 0) − var 0. W is any " +
		"set of untagged names, entering under the second tag; cotangent_universe(S) is " +
		"load-bearing for ε ∘ b = id (carrier_tag(S.carrier) injective on S's carrier). With W = ∅ " +
		"it is P's extra degeneracy moved under tag₀; with S the zero ring the target is one point.",
	Deps: []registry.EntryLike{
		triangleFixedNamesDef,
		triangleRowNameDef,
		TriangleRowAugmentationDef,
		simplicial_homotopy.ExtraDegeneracy,
		standard_resolution.StandardExtraFace,
		standard_resolution.StandardExtraDegeneracy,
		standard_resolution.StandardExtraBottom,
		standard_resolution.StandardExtraPointed,
		standard_resolution.RelativeBaseInclusionNatural,
		standard_resolution.StandardToBaseDef,
		free_algebra.FreeAlgebraDisjointCoefficients,
		free_algebra.FreeAlgebraBaseMapCoefficientwise,
		simplicial_ring.TagsDisjoint,
		simplicial_ring.TagInjective,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B). ∀W:set(U).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
		},
		Conclusion: "∃σ:(num → U → U). ∃b:(U → U). " +
			"    extra_degeneracy(mk_simplicial(λp:num. triangle_fixed_names(R, S, W, p), " +
			"            λp:num. λi:num. triangle_row_name(R, standard_face(R, S, f, p, i), 1), " +
			"            λp:num. λi:num. triangle_row_name(R, standard_degeneracy(R, p, i), 1)), " +
			"        universe_algebra(S, W), " +
			"        triangle_row_augmentation(R, S, f, 0, 1), " +
			"        σ, " +
			"        b) ∧ " +
			"    (∀n:num. " +
			"        σ(n, universe_algebra_ring(R, 𝕌⟨A:U⟩).zero) = universe_algebra_ring(R, 𝕌⟨A:U⟩).zero) ∧ " +
			"    b(universe_algebra_ring(S, 𝕌⟨A:U⟩).zero) = universe_algebra_ring(R, 𝕌⟨A:U⟩).zero",
	},
		"expand a member along the second-tag variables, its coefficients in the algebra on P's "+
			"names under the first tag (FreeAlgebraDisjointCoefficients, TagsDisjoint), and let σ act "+
			"on each coefficient by P's extra degeneracy carried by the first tag, b by P's bottom on "+
			"each coefficient over S. The faces and degeneracies move P's names only and act "+
			"coefficientwise (FreeAlgebraBaseMapCoefficientwise, RelativeBaseInclusionNatural), so "+
			"each identity is P's on every coefficient (StandardExtraFace, StandardExtraDegeneracy, "+
			"StandardExtraBottom), the sums agreeing because σ and b keep zero (StandardExtraPointed); "+
			"the augmentation evaluates P's names through P's augmentation and keeps W's variables "+
			"(TriangleRowAugmentationDef, StandardToBaseDef), coefficientwise as well"),
})}

// FixedNamesContractible — the augmentation contracts the free algebras on
// P's names and the fixed names W onto the free algebra over S on W.
var FixedNamesContractible = fixedNamesContractibleThm{family.Add(registry.ProofEntry{
	Name: "FixedNamesContractible",
	Key:  "prop_87cc4bf2286245b6",
	Reading: "The section is the degenerate section s₀ⁿ ∘ b, never σⁿ⁺¹ ∘ b, and the " +
		"homotopy is h_j = s₀ʲ ∘ σ ∘ d₀ʲ of the extra degeneracy; neither needs s_0 σ = σ σ. " +
		"At W = standard_names(S, T, q) the target universe_algebra(S, W) is standard_names(S, " +
		"T, q + 1). The second end is s_0ⁿ b ε d_0ⁿ, and triangle_row_augmentation(n, 1) = " +
		"triangle_row_augmentation(0, 1) ∘ d_0ⁿ by StandardToBaseFaceIndependent.",
	Deps: []registry.EntryLike{
		FixedNamesExtra,
		TriangleRowAugmentationDef,
		simplicial_homotopy.ExtraDegeneracySection,
		simplicial_homotopy.ExtraDegeneracyHomotopy,
		simplicial_homotopy.ExtraDegeneracyCoequalizes,
		standard_resolution.StandardToBaseDef,
		standard_resolution.StandardToBaseFaceIndependent,
		free_algebra.FreeAlgebraEvalUnique,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B). ∀W:set(U).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
		},
		Conclusion: "∃ι:(num → U → U). ∃H:(num → num → U → U). " +
			"    simplicial_map(mk_simplicial(λp:num. triangle_fixed_names(R, S, W, p), " +
			"            λp:num. λi:num. triangle_row_name(R, standard_face(R, S, f, p, i), 1), " +
			"            λp:num. λi:num. triangle_row_name(R, standard_degeneracy(R, p, i), 1)), " +
			"        mk_simplicial(λn:num. universe_algebra(S, W), " +
			"            λn:num. λi:num. λz:U. z, " +
			"            λn:num. λi:num. λz:U. z), " +
			"        λp:num. triangle_row_augmentation(R, S, f, p, 1)) ∧ " +
			"    simplicial_map(mk_simplicial(λn:num. universe_algebra(S, W), " +
			"            λn:num. λi:num. λz:U. z, " +
			"            λn:num. λi:num. λz:U. z), " +
			"        mk_simplicial(λp:num. triangle_fixed_names(R, S, W, p), " +
			"            λp:num. λi:num. triangle_row_name(R, standard_face(R, S, f, p, i), 1), " +
			"            λp:num. λi:num. triangle_row_name(R, standard_degeneracy(R, p, i), 1)), " +
			"        ι) ∧ " +
			"    (∀n:num. ∀z:U. " +
			"        z ∈ universe_algebra(S, W) ⇒ triangle_row_augmentation(R, S, f, n, 1, ι(n, z)) = z) ∧ " +
			"    simplicial_homotopy(mk_simplicial(λp:num. triangle_fixed_names(R, S, W, p), " +
			"            λp:num. λi:num. triangle_row_name(R, standard_face(R, S, f, p, i), 1), " +
			"            λp:num. λi:num. triangle_row_name(R, standard_degeneracy(R, p, i), 1)), " +
			"        mk_simplicial(λp:num. triangle_fixed_names(R, S, W, p), " +
			"            λp:num. λi:num. triangle_row_name(R, standard_face(R, S, f, p, i), 1), " +
			"            λp:num. λi:num. triangle_row_name(R, standard_degeneracy(R, p, i), 1)), " +
			"        λn:num. λx:U. x, " +
			"        λn:num. λx:U. ι(n, triangle_row_augmentation(R, S, f, n, 1, x)), " +
			"        H)",
	},
		"ExtraDegeneracySection and ExtraDegeneracyHomotopy at FixedNamesExtra give the "+
			"section and the homotopy from the identity to the section after the augmentation "+
			"of the last vertex; that augmentation is triangle_row_augmentation(R, S, f, p, "+
			"1), P's augmentation in degree p being the one in degree 0 after the 0-th faces "+
			"(StandardToBaseDef, StandardToBaseFaceIndependent, FreeAlgebraEvalUnique), and "+
			"it is simplicial into the constant simplicial set (ExtraDegeneracyCoequalizes)"),
})}

// ---------------------------------------------------------------------------
// The rows of the right term
// ---------------------------------------------------------------------------

// RightRowHomotopyEquivalence — in every row the augmentation contracts the
// simplicial set of relative names onto the names of the same degree of
// the standard resolution of T over S.
var RightRowHomotopyEquivalence = rightRowHomotopyEquivalenceThm{family.Add(registry.ProofEntry{
	Name: "RightRowHomotopyEquivalence",
	Key:  "prop_2a2cc6c47edf005d",
	Reading: "The statement is the induction's: a homotopy equivalence of simplicial sets with the " +
		"augmentation, the section and the homotopy explicit, because the step carries it through the " +
		"renaming, a functor on sets of names; a contraction of chains would not carry over, and the " +
		"rows from q = 2 on have no extra degeneracy. Row 0 is constant, the relative names of row 0 " +
		"being standard_names(S, T, 0) (RelativeNamesZero). The section is built recursively as ι_{q+1} " +
		"= rename(ι_q) ∘ s_0ⁿ b. Row 1's homotopy is exactly s_0ʲσd_0ʲ: the renamed homotopy of row 0 " +
		"is trivial and cancels in the join. Each May identity is affine in h, and only the two ends " +
		"carry constant terms, which telescope; the join h = h_A − s(ι_A ε_A) + ι_A h_B ε_A needs the " +
		"row closed under + and − with additive faces and degeneracies (RelativeHorizontalHom, every " +
		"row from 1 on), s_j ∘ G a homotopy from G to G (HomotopyTrivial), and whiskering " +
		"(HomotopyComposeLeft, HomotopyComposeRight) — nothing else additive.",
	Deps: []registry.EntryLike{
		AuxiliaryToFixedNames,
		FixedNamesContractible,
		triangleRowNameDef,
		TriangleRowAugmentationDef,
		triangleFixedNamesDef,
		standard_resolution.RelativeNamesZero,
		standard_resolution.RelativeHorizontalHom,
		standard_resolution.StandardNamesDef,
		standard_resolution.StandardTermsDef,
		simplicial_homotopy.HomotopyTrivial,
		simplicial_homotopy.SimplicialHomotopy,
		simplicial_homotopy.HomotopyComposeLeft,
		simplicial_homotopy.HomotopyComposeRight,
		simplicial_set.MapCompose,
		free_algebra.FreeAlgebraCommRingOn,
		free_algebra.FreeAlgebraEvalUnique,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀T:ring_ops(C). " +
			"∀g:(B → C). " +
			"∀N:module_ops(C, D). " +
			"∀q:num.",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"cotangent_universe(T, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"ring_homomorphism(S, T, g)",
			"module_on(T, N)",
		},
		Conclusion: "∃ι:(num → U → U). ∃H:(num → num → U → U). " +
			"    simplicial_map(mk_simplicial(λp:num. relative_names(R, S, T, p, q), " +
			"            λp:num. λi:num. triangle_row_name(R, standard_face(R, S, f, p, i), q), " +
			"            λp:num. λi:num. triangle_row_name(R, standard_degeneracy(R, p, i), q)), " +
			"        mk_simplicial(λn:num. standard_names(S, T, q), " +
			"            λn:num. λi:num. λz:U. z, " +
			"            λn:num. λi:num. λz:U. z), " +
			"        λp:num. triangle_row_augmentation(R, S, f, p, q)) ∧ " +
			"    simplicial_map(mk_simplicial(λn:num. standard_names(S, T, q), " +
			"            λn:num. λi:num. λz:U. z, " +
			"            λn:num. λi:num. λz:U. z), " +
			"        mk_simplicial(λp:num. relative_names(R, S, T, p, q), " +
			"            λp:num. λi:num. triangle_row_name(R, standard_face(R, S, f, p, i), q), " +
			"            λp:num. λi:num. triangle_row_name(R, standard_degeneracy(R, p, i), q)), " +
			"        ι) ∧ " +
			"    (∀n:num. ∀z:U. " +
			"        z ∈ standard_names(S, T, q) ⇒ triangle_row_augmentation(R, S, f, n, q, ι(n, z)) = z) ∧ " +
			"    simplicial_homotopy(mk_simplicial(λp:num. relative_names(R, S, T, p, q), " +
			"            λp:num. λi:num. triangle_row_name(R, standard_face(R, S, f, p, i), q), " +
			"            λp:num. λi:num. triangle_row_name(R, standard_degeneracy(R, p, i), q)), " +
			"        mk_simplicial(λp:num. relative_names(R, S, T, p, q), " +
			"            λp:num. λi:num. triangle_row_name(R, standard_face(R, S, f, p, i), q), " +
			"            λp:num. λi:num. triangle_row_name(R, standard_degeneracy(R, p, i), q)), " +
			"        λn:num. λx:U. x, " +
			"        λn:num. λx:U. ι(n, triangle_row_augmentation(R, S, f, n, q, x)), " +
			"        H)",
	},
		"induction on q. Row 0: the names are standard_names(S, T, 0) in every column "+
			"(RelativeNamesZero) and the row maps and the augmentation are the identity "+
			"(triangleRowNameDef, TriangleRowAugmentationDef): the identity section and the trivial "+
			"homotopy (HomotopyTrivial). Row q + 1: AuxiliaryToFixedNames at the hypothesis contracts it "+
			"onto triangle_fixed_names(R, S, standard_names(S, T, q), •), and FixedNamesContractible at W = "+
			"standard_names(S, T, q) contracts that onto universe_algebra(S, standard_names(S, T, q)), "+
			"which is standard_names(S, T, q + 1) (StandardNamesDef, StandardTermsDef). Compose: the "+
			"augmentations compose to triangle_row_augmentation(R, S, f, p, q + 1) (FreeAlgebraEvalUnique), "+
			"the sections compose, and the two homotopies, from the identity to ι₁ε₁ and from ι₁ε₁ to "+
			"ι₁ι₂ε₂ε₁, join into one by the additive structure of the free algebras, h_j = h₁_j − s_j(ι₁ε₁) "+
			"+ ι₁ h₂_j ε₁, the faces and degeneracies of the row being ring maps (RelativeHorizontalHom)"),
})}

// RightRowAcyclic — every row of the right term, augmented by the chains
// along the row augmentation onto the cotangent complex of T over S, is
// exact: the row hypotheses of the augmented assembly along the rows.
var RightRowAcyclic = rightRowAcyclicThm{family.Add(registry.ProofEntry{
	Name: "RightRowAcyclic",
	Key:  "prop_bd570a0febae101",
	Reading: "Row q is the chains with values in N on the simplicial set of relative names " +
		"of row q, and the augmentation the chains along its augmentation in column 0; a " +
		"homotopy equivalence of simplicial sets onto the constant names gives a chain homotopy " +
		"equivalence of chains over T and, after the tensor step, with values in N. The four " +
		"conjuncts are AugmentedAssemblyRows's row hypotheses. Surjectivity comes from ε ∘ ι = " +
		"id. Exactness at column 0 comes from the chain map in degree 0 being exactly " +
		"triangle_right_eps and H_0 of the constant chains being finite_supp(N, S_q), ∂_1 = 0 " +
		"there. If T is the zero ring, N is the zero module and every conjunct is trivial.",
	Deps: []registry.EntryLike{
		RightRowHomotopyEquivalence,
		triangleRightDef,
		triangleRightHorizontalDef,
		TriangleRightEpsDef,
		simplicial_module.HomotopyEquivalenceChainHomotopyEquivalence,
		simplicial_module.SimplicialChainsFreeComplex,
		simplicial_module.ConstantSimplicialChainsHomology,
		simplicial_homotopy.SimplicialHomotopyEquivalenceDef,
		tor_ext.TensorChainMap,
		tor_ext.TensorHomotopy,
		tor_ext.TensorComplexOf,
		tor_ext.FiniteSuppMapDef,
		free_module.FreePushforwardDef,
		cotangent_complex.CotangentComplexDef,
		cotangent_complex.DifferentialComplexDef,
		cotangent_complex.DifferentialTermsDef,
		module_homomorphism.ExactAtDef,
		ring_homomorphism.Target,
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
		Conclusion: "(∀q:num. " +
			"    module_homomorphism(T, " +
			"        restrict_module(finite_supp_module(N, 𝕌⟨A:U⟩), triangle_right(R, S, T, N, 0, q)), " +
			"        complex_module(cotangent_complex(S, T, g, T, λc:C. c, N), q), " +
			"        triangle_right_eps(R, S, f, T, N, q))) ∧ " +
			"(∀q:num. " +
			"    image(triangle_right_eps⟨U:U⟩(R, S, f, T, N, q), triangle_right(R, S, T, N, 0, q)) = " +
			"    cotangent_complex(S, T, g, T, λc:C. c, N).terms(q)) ∧ " +
			"(∀q:num. " +
			"    exact_at(cotangent_complex(S, T, g, T, λc:C. c, N).zero, " +
			"        triangle_right⟨U:U⟩(R, S, T, N, 1, q), " +
			"        triangle_right(R, S, T, N, 0, q), " +
			"        triangle_right_horizontal(R, S, f, T, N, 1, q), " +
			"        triangle_right_eps(R, S, f, T, N, q))) ∧ " +
			"(∀p q:num. " +
			"    exact_at(finite_supp_module(N, 𝕌⟨A:U⟩).zero, " +
			"        triangle_right(R, S, T, N, p + 2, q), " +
			"        triangle_right(R, S, T, N, p + 1, q), " +
			"        triangle_right_horizontal(R, S, f, T, N, p + 2, q), " +
			"        triangle_right_horizontal(R, S, f, T, N, p + 1, q)))",
	},
		"row q is tensor_complex over T of the chains on the simplicial set of relative names of row q "+
			"(triangleRightDef, triangleRightHorizontalDef, TensorComplexOf), and the augmentation the map "+
			"of chains along the augmentation in column 0 (TriangleRightEpsDef, FiniteSuppMapDef, "+
			"FreePushforwardDef). RightRowHomotopyEquivalence makes the augmentation a simplicial homotopy "+
			"equivalence onto the constant simplicial set standard_names(S, T, q) "+
			"(SimplicialHomotopyEquivalenceDef, a one-step zigzag each way); "+
			"HomotopyEquivalenceChainHomotopyEquivalence over T, a commutative ring (Target of g), gives a "+
			"chain homotopy equivalence of the chains over T, which TensorChainMap and TensorHomotopy "+
			"carry to the chains with values in N; the chains on the constant simplicial set have "+
			"boundaries the identity and zero alternately (ConstantSimplicialChainsHomology), so the "+
			"augmented row is exact and the augmentation onto the cotangent complex's term, finite_supp(N, "+
			"standard_names(S, T, q)) (CotangentComplexDef, DifferentialComplexDef, DifferentialTermsDef)"),
})}

// RightRowEpsVertical — the augmentations of the right term's rows
// commute with the vertical boundaries: the last hypothesis of the
// augmented assembly along the rows.
var RightRowEpsVertical = rightRowEpsVerticalThm{family.Add(registry.ProofEntry{
	Name: "RightRowEpsVertical",
	Key:  "prop_6d6eaab8f32ff9fb",
	Reading: "The augmentation is also the Jacobian of relative_horizontal_eps read at the second " +
		"tags, and that map commutes with the vertical structure; the vertical boundary of the right " +
		"term discards the derivatives in P's names, which relative_horizontal_eps sends to constants " +
		"with zero derivative. triangle_row_augmentation(0, q + 1) = relative_horizontal_eps(q) as " +
		"functions, the same recursion; the chain rule through it sums the second-tag derivatives over " +
		"the fibres of the row augmentation, the pushforward, and P's names go to constants. The " +
		"coefficients agree by RelativeHorizontalEpsVertical, its first conjunct iterated and its third.",
	Deps: []registry.EntryLike{
		TriangleRightEpsDef,
		TriangleRightVerticalDef,
		TriangleRowAugmentationDef,
		TriangleSectionDef,
		TriangleProjectionDef,
		standard_resolution.RelativeHorizontalEpsDef,
		standard_resolution.RelativeHorizontalEpsVertical,
		standard_resolution.RelativeHorizontalEpsHom,
		standard_resolution.StandardToBaseFaceIndependent,
		partial_derivative.JacobianDelta,
		partial_derivative.JacobianCompose,
		partial_derivative.JacobianCongruence,
		partial_derivative.PartialVar,
		cotangent_complex.CotangentComplexDef,
		cotangent_complex.DifferentialBoundaryDef,
		cotangent_complex.DifferentialFaceDef,
		chain_complex.AugmentedAssemblyRows,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀T:ring_ops(C). " +
			"∀g:(B → C). " +
			"∀N:module_ops(C, D). " +
			"∀q:num. " +
			"∀x:(U → D).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"cotangent_universe(T, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"ring_homomorphism(S, T, g)",
			"module_on(T, N)",
			"x ∈ triangle_right(R, S, T, N, 0, q + 1)",
		},
		Conclusion: "cotangent_complex(S, T, g, T, λc:C. c, N).d(q + 1)( " +
			"    triangle_right_eps(R, S, f, T, N, q + 1, x)) = " +
			"triangle_right_eps(R, S, f, T, N, q, triangle_right_vertical(R, S, f, T, g, N, 0, q + 1, x))",
	},
		"relative_horizontal_eps(R, S, f, q) carries the variable of the second tag of a relative "+
			"name to the variable over S of its row augmentation (RelativeHorizontalEpsDef, "+
			"TriangleRowAugmentationDef), whose Jacobian is the generator there (JacobianDelta, "+
			"PartialVar), and P's names to constants: so triangle_right_eps is the Jacobian of that map "+
			"at the section, the coefficients through the augmentation of the standard resolution of T "+
			"over S. Both sides are then Jacobians of composites (JacobianCompose, the augmentations "+
			"agreeing by StandardToBaseFaceIndependent), which agree on the variables because the row "+
			"augmentation commutes with the vertical faces (RelativeHorizontalEpsVertical, "+
			"JacobianCongruence); the cotangent complex's boundary is the alternating sum of the faces' "+
			"Jacobians (CotangentComplexDef, DifferentialBoundaryDef, DifferentialFaceDef)"),
})}

// RightTotalQuasiIsomorphism — the right total maps quasi-isomorphically
// onto the cotangent complex of T over S with coefficients in N, by the
// row augmentation at the coordinate 0.
var RightTotalQuasiIsomorphism = rightTotalQuasiIsomorphismThm{family.Add(registry.ProofEntry{
	Name: "RightTotalQuasiIsomorphism",
	Key:  "prop_b2d409e682c07ba",
	Reading: "The five hypotheses of AugmentedAssemblyRows are exactly the four " +
		"conjuncts of RightRowAcyclic and RightRowEpsVertical, with E the cotangent complex " +
		"of T over S, the signs alternating_sign and the edge λn u. triangle_right_eps(n, " +
		"u(0)); no sign appears in the square because alternating_sign(0) = T.one.",
	Deps: []registry.EntryLike{
		RightRowAcyclic,
		RightRowEpsVertical,
		TriangleRightDouble,
		TriangleRightTotalDef,
		chain_complex.AugmentedAssemblyRows,
		chain_complex.QuasiIsomorphismDef,
		cotangent_complex.CotangentChainComplex,
		ring_homomorphism.RingHomIdentity,
		ring_homomorphism.Target,
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
			"    triangle_right_total⟨U:U⟩(R, S, f, T, g, N), " +
			"    cotangent_complex(S, T, g, T, λc:C. c, N), " +
			"    λm:num. λu:(num → U → D). triangle_right_eps(R, S, f, T, N, m, u(0)))",
	},
		"AugmentedAssemblyRows at TriangleRightDouble over T, the right total being double_total at "+
			"T's alternating sign (TriangleRightTotalDef), E the cotangent complex of T over S at the "+
			"identity of T, a chain complex (CotangentChainComplex, RingHomIdentity, Target), b the row "+
			"augmentations: its row hypotheses are RightRowAcyclic and its square RightRowEpsVertical"),
})}
