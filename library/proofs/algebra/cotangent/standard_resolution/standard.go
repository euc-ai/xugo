// standard.go — the standard resolution of an algebra S over a ring R
// through the structure map f, inside the one host: the names of degree
// 0 are the tags of S's elements and the names of degree n + 1 are the
// members of the free algebra over R on the names of degree n, so the
// n-simplices are R[R[…R[S]…]] with n + 1 brackets. The 0-th face
// flattens the two outer brackets, the face i + 1 acts by the face i
// inside the outer bracket, and at the bottom the augmentation evaluates
// S's names back into S; the 0-th degeneracy doubles the outer bracket
// by the variables, the degeneracy j + 1 acts by the degeneracy j inside
// it. The extra degeneracy u ↦ [u] − [0], with its bottom on S, keeps
// zero; the augmentation read in every degree is the composite with the
// 0-th faces; an algebra map out of S induces a map of the standard
// resolutions. In a universe for R and S the faces and degeneracies are
// algebra maps satisfying the simplicial identities by the monad laws of
// the free algebra, the augmentation is a ring map coequalizing the two
// faces of an edge, and the extra degeneracy, keeping zero, makes the
// underlying simplicial module acyclic: the standard resolution is a
// polynomial resolution of S, a Kan complex whose homotopy groups vanish
// above degree 0.

package standard_resolution

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/simplicial_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/free_algebra"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/simplicial/kan_complex"
	"github.com/euc-ai/xugo/library/proofs/simplicial/simplicial_group"
	"github.com/euc-ai/xugo/library/proofs/simplicial/simplicial_homotopy"
	"github.com/euc-ai/xugo/library/proofs/simplicial/simplicial_module"
	"github.com/euc-ai/xugo/library/proofs/simplicial/simplicial_set"
	// set_basic mints the image of a set, which the names of degree 0
	// are; the import initializes that mint before the definitions here
	// are parsed.
	_ "github.com/euc-ai/xugo/library/proofs/sets/set_basic"

	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// Names and simplices
// ---------------------------------------------------------------------------

// StandardNamesDef — `standard_names(R, S, n)`: the names of degree n of
// the standard resolution of S over R — in degree 0 the tags of S's
// elements, in degree n + 1 the free algebra over R in the universe on
// the names of degree n.
var StandardNamesDef = standardNamesDefThm{family.Define(registry.DefEntry{
	Name:  "StandardNamesDef",
	Key:   "prop_8dd31a87404016cb",
	Const: "standard_names",
	Type:  "ring_ops(A) → ring_ops(B) → num → set(U)",
	Equations: []string{
		"∀R:ring_ops(A). ∀S:ring_ops(B). " +
			"    standard_names(R, S, 0) = image(carrier_tag(S.carrier), S.carrier)",
		"∀R:ring_ops(A). ∀S:ring_ops(B). ∀n:num. " +
			"    standard_names(R, S, suc(n)) = universe_algebra(R, standard_names(R, S, n))",
	},
	Reading: "The names of degree n + 1 are the simplices of degree n: every member of the " +
		"algebra below is a variable of the algebra above, and no further naming enters above degree " +
		"0. The structure map is not read; the names depend on S through its carrier only, named by " +
		"the one naming of that carrier, so the names of degree 0 are the same set for every base " +
		"ring R; above degree 0 they are free algebras over R, read through R's embedding. Over the " +
		"zero ring R every algebra is one point, so from degree 1 on there is one name.",
})}

// StandardTermsDef — `standard_terms(R, S, n)`: the n-simplices of the
// standard resolution of S over R, the free algebra over R in the
// universe on the names of degree n.
var StandardTermsDef = standardTermsDefThm{family.Define(registry.DefEntry{
	Name:  "StandardTermsDef",
	Key:   "prop_4a89837903a3bc30",
	Const: "standard_terms",
	Type:  "ring_ops(A) → ring_ops(B) → num → set(U)",
	Equations: []string{
		"∀R:ring_ops(A). ∀S:ring_ops(B). ∀n:num. " +
			"    standard_terms(R, S, n) = universe_algebra(R, standard_names(R, S, n))",
	},
	Reading: "standard_terms(R, S, n) and standard_names(R, S, n + 1) are one " +
		"set, unfolded from two definitions; a statement about the simplicial algebra " +
		"writes the names, polynomial_simplicial_algebra(R, standard_names(R, S), …), " +
		"and one about the simplices as a set writes the terms.",
	Deps: []registry.EntryLike{StandardNamesDef},
})}

// ---------------------------------------------------------------------------
// The augmentation, the faces and the degeneracies
// ---------------------------------------------------------------------------

// StandardEpsDef — `standard_eps(R, S, f, u)`: the augmentation of the
// standard resolution, u in degree 0 evaluated in S — each coefficient
// carried by f and each name, the tag of an element of S, read back as
// that element.
var StandardEpsDef = standardEpsDefThm{family.Define(registry.DefEntry{
	Name:  "StandardEpsDef",
	Key:   "prop_7a03f7dc2f851ca9",
	Const: "standard_eps",
	Type:  "ring_ops(A) → ring_ops(B) → (A → B) → U → B",
	Equations: []string{
		"∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B). ∀u:U. " +
			"    standard_eps(R, S, f, u) = " +
			"    universe_algebra_eval(R, S, f, λx:U. inverse_on(S.carrier, carrier_tag(S.carrier), x), u)",
	},
	Reading: "A name of degree 0 is the tag of an element of S's carrier and is read " +
		"back by the preimage chosen in that carrier, a member of the carrier whatever the " +
		"tag does elsewhere; that the preimage of carrier_tag(S.carrier, y) is y asks the " +
		"tag to be injective on the carrier, which cotangent_universe(S, 𝕌⟨A:U⟩) provides " +
		"(CarrierTagDecode). The value is read on standard_terms(R, S, 0) only.",
})}

// StandardFaceDef — `standard_face(R, S, f, n, i, u)`: the face i of the
// standard resolution on its n-simplices, a function of the whole host.
// In degree n + 1 the 0-th face is the multiplication of the free
// algebra, flattening the outer two brackets, and the face i + 1 is the
// map induced on the variables by the face i of degree n; in degree 0 it
// is the augmentation followed by the tag, the map from the names of
// degree 1 to the names of degree 0 that the last face of every degree
// is built on.
var StandardFaceDef = standardFaceDefThm{family.Define(registry.DefEntry{
	Name:  "StandardFaceDef",
	Key:   "prop_b43df0048f49d78a",
	Const: "standard_face",
	Type:  "ring_ops(A) → ring_ops(B) → (A → B) → num → num → U → U",
	Equations: []string{
		"∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B). " +
			"    standard_face(R, S, f, 0) = (λi:num. λu:U. carrier_tag(S.carrier, standard_eps(R, S, f, u)))",
		"∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B). ∀n:num. " +
			"    standard_face(R, S, f, suc(n)) = " +
			"    (λi:num. λu:U. " +
			"        COND(i = 0, " +
			"            universe_algebra_mult(R, u), " +
			"            universe_algebra_map(R, R, λa:A. a, standard_face(R, S, f, n, i - 1), u)))",
	},
	Reading: "The faces of the simplicial set are standard_face(R, S, f, n + 1, i) for " +
		"i ≤ n + 1; the values at degree 0 are not a face of simplices but the map of names " +
		"that makes the last face of degree 1 the augmentation on the variables, so that d_1 " +
		"s_0 = id holds in degree 0 and ε d_0 = ε d_1 holds in degree 1. Past the top index " +
		"the values are those of a lower face and are not read. The faces read f through the " +
		"augmentation, so the resolution of S over R depends on the structure map.",
	Deps: []registry.EntryLike{StandardEpsDef},
})}

// StandardDegeneracyDef — `standard_degeneracy(R, n, j, u)`: the
// degeneracy j of the standard resolution on its n-simplices, a function
// of the whole host — the 0-th the map induced by sending each name to
// its variable, the degeneracy j + 1 of degree n + 1 the map induced on
// the variables by the degeneracy j of degree n.
var StandardDegeneracyDef = standardDegeneracyDefThm{family.Define(registry.DefEntry{
	Name:  "StandardDegeneracyDef",
	Key:   "prop_6df495e49ad4e931",
	Const: "standard_degeneracy",
	Type:  "ring_ops(A) → num → num → U → U",
	Equations: []string{
		"∀R:ring_ops(A). " +
			"    standard_degeneracy(R, 0) = " +
			"    (λj:num. λu:U. universe_algebra_map(R, R, λa:A. a, universe_algebra_var(R), u))",
		"∀R:ring_ops(A). ∀n:num. " +
			"    standard_degeneracy(R, suc(n)) = " +
			"    (λj:num. λu:U. " +
			"        COND(j = 0, " +
			"            universe_algebra_map(R, R, λa:A. a, universe_algebra_var(R), u), " +
			"            universe_algebra_map(R, R, λa:A. a, standard_degeneracy(R, n, j - 1), u)))",
	},
	Reading: "The degeneracies read neither S nor the structure map: they are the " +
		"same functions of the host for every algebra resolved over R. Each carries the " +
		"variable of a name to the variable of a name, the variable of x going to the " +
		"variable of the variable of x or to the variable of a degeneracy of x. Only j " +
		"≤ n is read; past it the values are those of the last degeneracy s(n, n).",
})}

// StandardToBaseDef — `standard_to_base(R, S, f, n, u)`: the augmentation
// of the standard resolution read in degree n, the 0-th faces down to
// degree 0 followed by the augmentation.
var StandardToBaseDef = standardToBaseDefThm{family.Define(registry.DefEntry{
	Name:  "StandardToBaseDef",
	Key:   "prop_4e256d666a3e4b82",
	Const: "standard_to_base",
	Type:  "ring_ops(A) → ring_ops(B) → (A → B) → num → U → B",
	Equations: []string{
		"∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B). ∀n:num. " +
			"    standard_to_base(R, S, f, n) = " +
			"    augmentation_at(standard_face(R, S, f), standard_eps(R, S, f), n)",
	},
	Reading: "Composed with the 0-th faces; that any face gives the same " +
		"composite is a theorem of the augmented algebra. It is the coefficient " +
		"map an algebra built over the degree-n simplices reads into S.",
	Deps: []registry.EntryLike{StandardFaceDef, StandardEpsDef},
})}

// StandardRepresentativeDef — `standard_representative(R, S, f, u)`: the
// variable of the name of u's augmentation, τ(u) = [tag ε(u)], the member
// of the 0-simplices the 1-st face of degree 1 sends the variable of u to.
var StandardRepresentativeDef = standardRepresentativeDefThm{family.Define(registry.DefEntry{
	Name:  "StandardRepresentativeDef",
	Key:   "prop_b953d209d1763cde",
	Const: "standard_representative",
	Type:  "ring_ops(A) → ring_ops(B) → (A → B) → U → U",
	Equations: []string{
		"∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B). ∀u:U. " +
			"    standard_representative(R, S, f, u) = " +
			"    universe_algebra_var(R, carrier_tag(S.carrier, standard_eps(R, S, f, u)))",
	},
	Reading: "τ reads u through its augmentation only: two members with one augmentation " +
		"have one representative, so τ is constant on each coset of the kernel I of the " +
		"augmentation and u − τ(u) lies in I when the tag of S is injective on its carrier. It " +
		"is the 1-st face of degree 1 at the variable of u, the 0-th face giving u itself, so " +
		"the edge from τ(u) to u is the 1-simplex var(u), and a 1-cochain c of the cotangent " +
		"cochain complex is read on I through x ↦ c(x) − c(0) and back through u ↦ γ(u − τ(u)).",
	Deps: []registry.EntryLike{StandardEpsDef},
})}

// ---------------------------------------------------------------------------
// The extra degeneracy
// ---------------------------------------------------------------------------

// StandardExtraDef — `standard_extra(R, u)`: the extra degeneracy of the
// standard resolution, the variable of u less the variable of zero — the
// same function of the host in every degree, carrying the n-simplices to
// the (n + 1)-simplices.
var StandardExtraDef = standardExtraDefThm{family.Define(registry.DefEntry{
	Name:  "StandardExtraDef",
	Key:   "prop_bbcdbcc957e8a4a7",
	Const: "standard_extra",
	Type:  "ring_ops(A) → U → U",
	Equations: []string{
		"∀R:ring_ops(A). ∀u:U. " +
			"    standard_extra(R, u) = " +
			"    universe_algebra_ring(R, 𝕌⟨A:U⟩).sub(universe_algebra_var(R, u), " +
			"        universe_algebra_var(R, universe_algebra_ring(R, 𝕌⟨A:U⟩).zero))",
	},
	Reading: "It is not additive, the variable not being so, and satisfies the face " +
		"identities and s_{j+1} σ = σ s_j but not s_0 σ = σ σ. The subtracted variable of zero " +
		"makes it keep zero, which ExtraDegeneracyAcyclic's hypotheses and the coefficientwise " +
		"extra degeneracy of the transitivity triangle's right rows (FixedNamesExtra) read. " +
		"The variable alone, u ↦ [u] with bottom y ↦ [tag y], is an extra degeneracy as well, " +
		"s_0 σ = σ σ included, s_0 carrying [u] to [[u]], but it does not keep zero. An extra " +
		"degeneracy is read degreewise, so a statement passes λn:num. standard_extra(R).",
})}

// standardExtraBottomDef — `standard_extra_bottom(R, S, y)`: the bottom of
// the extra degeneracy, from S to the 0-simplices — the variable of the
// tag of y less the variable of the tag of S's zero.
var standardExtraBottomDef = standardExtraBottomDefThm{family.Define(registry.DefEntry{
	Name:  "standardExtraBottomDef",
	Key:   "prop_b97cbb93aa366da9",
	Const: "standard_extra_bottom",
	Type:  "ring_ops(A) → ring_ops(B) → B → U",
	Equations: []string{
		"∀R:ring_ops(A). ∀S:ring_ops(B). ∀y:B. " +
			"    standard_extra_bottom(R, S, y) = " +
			"    universe_algebra_ring(R, 𝕌⟨A:U⟩).sub(universe_algebra_var(R, carrier_tag(S.carrier, y)), " +
			"        universe_algebra_var(R, carrier_tag(S.carrier, S.zero)))",
	},
	Reading: "It keeps zero, carrying S's zero to the zero of the host " +
		"ring, and the augmentation reads it back as y because the " +
		"augmentation is additive and the tag of S's zero is read as S's zero.",
})}

// ---------------------------------------------------------------------------
// Functoriality in the algebra
// ---------------------------------------------------------------------------

// StandardMapDef — `standard_map(R, S, T, g, n, u)`: the map of standard
// resolutions over R induced by a map g from S to T, on the n-simplices:
// in degree 0 the map induced by carrying the name of y in S's carrier
// to the name of g(y) in T's, in degree n + 1 the map induced on the
// variables by the map of degree n.
var StandardMapDef = standardMapDefThm{family.Define(registry.DefEntry{
	Name:  "StandardMapDef",
	Key:   "prop_f401522cbc154c95",
	Const: "standard_map",
	Type:  "ring_ops(A) → ring_ops(B) → ring_ops(C) → (B → C) → num → U → U",
	Equations: []string{
		"∀R:ring_ops(A). ∀S:ring_ops(B). ∀T:ring_ops(C). ∀g:(B → C). " +
			"    standard_map(R, S, T, g, 0) = " +
			"    (λu:U. " +
			"        universe_algebra_map(R, " +
			"            R, " +
			"            λa:A. a, " +
			"            λz:U. carrier_tag(T.carrier, g(inverse_on(S.carrier, carrier_tag(S.carrier), z))), " +
			"            u))",
		"∀R:ring_ops(A). ∀S:ring_ops(B). ∀T:ring_ops(C). ∀g:(B → C). ∀n:num. " +
			"    standard_map(R, S, T, g, suc(n)) = " +
			"    (λu:U. universe_algebra_map(R, R, λa:A. a, standard_map(R, S, T, g, n), u))",
	},
	Reading: "The target ring is an argument because the names of degree 0 of its resolution " +
		"are the naming of its carrier: the map reads S's carrier, T's carrier and g only, and no " +
		"ring law of either. It commutes with the faces of the two resolutions when g is an algebra " +
		"map over R, g ∘ f = f' on R's carrier, since the face of degree 0 evaluates through the " +
		"two structure maps. The coefficients stay in R: both resolutions are over the one ring.",
})}

// ---------------------------------------------------------------------------
// Change of the coefficient ring
// ---------------------------------------------------------------------------

// StandardBaseChangeDef — `standard_base_change(R, S, f, n, u)`: the map
// from the standard resolution of an algebra over R to its standard
// resolution over S that changes the coefficients along f, on the
// n-simplices: in degree 0 the map induced by f on the coefficients and
// the identity on the names, the tags of the algebra's elements; in
// degree n + 1 the map induced by f and, on the names, by the map of
// degree n.
var StandardBaseChangeDef = standardBaseChangeDefThm{family.Define(registry.DefEntry{
	Name:  "StandardBaseChangeDef",
	Key:   "prop_e98bf4e5a90dcbf2",
	Const: "standard_base_change",
	Type:  "ring_ops(A) → ring_ops(B) → (A → B) → num → U → U",
	Equations: []string{
		"∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B). " +
			"    standard_base_change(R, S, f, 0) = (λu:U. universe_algebra_map(R, S, f, λx:U. x, u))",
		"∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B). ∀n:num. " +
			"    standard_base_change(R, S, f, suc(n)) = " +
			"    (λu:U. universe_algebra_map(R, S, f, standard_base_change(R, S, f, n), u))",
	},
	Reading: "It reads neither the algebra T resolved nor its structure maps: the names of " +
		"degree 0 of T over R and of T over S are one set, the tags of T's elements, and above it " +
		"each resolution's names are its own simplices, over R and over S, so the identity on the " +
		"tags and f on the coefficients carry the one to the other degree by degree. It is a map of " +
		"resolutions when the structure map over R is g ∘ f, g the one over S (StandardBaseChangeMap).",
})}

// ---------------------------------------------------------------------------
// The simplicial set
// ---------------------------------------------------------------------------

// StandardFaceIn — in a universe for R and S, each face carries the
// (n + 1)-simplices of the standard resolution into its n-simplices.
var StandardFaceIn = standardFaceInThm{family.Add(registry.ProofEntry{
	Name: "StandardFaceIn",
	Key:  "prop_34a342d8823b8954",
	Reading: "The universe for S is not read: the last face of degree 1 lands among the names " +
		"of degree 0, the tags of S's elements, because the augmentation reads each name back by " +
		"a preimage chosen in S's carrier, which lies there whether or not the tag is injective.",
	Deps: []registry.EntryLike{
		StandardFaceDef,
		StandardTermsDef,
		StandardNamesDef,
		StandardEpsDef,
		StandardEpsHom,
		simplicial_ring.UniverseEmbeddingHost,
		simplicial_ring.UniverseAlgebraDef,
		simplicial_ring.UniverseAlgebraMultDef,
		simplicial_ring.UniverseAlgebraMapDef,
		free_algebra.FreeAlgebraMultHom,
		free_algebra.FreeAlgebraMapHom,
		ring_homomorphism.MapIn,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B). ∀n i:num. ∀u:U.",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"i ≤ n + 1",
			"u ∈ standard_terms(R, S, n + 1)",
		},
		Conclusion: "standard_face(R, S, f, n + 1, i, u) ∈ standard_terms(R, S, n)",
	},
		"induct on n. The face 0 is the multiplication, carrying the algebra on standard_terms(R, "+
			"S, n) = standard_names(R, S, n + 1) into the algebra on standard_names(R, S, n) "+
			"(FreeAlgebraMultHom at the universe embedding, UniverseEmbeddingHost). The face i + 1 is "+
			"the map induced on the variables by d(n, i), which carries standard_names(R, S, n + 1) "+
			"into standard_names(R, S, n) by the induction hypothesis, and at n = 0 is the tag of the "+
			"augmentation, whose values lie in S's carrier (StandardEpsHom, MapIn); FreeAlgebraMapHom"),
})}

// StandardDegeneracyIn — in a universe for R, each degeneracy carries
// the n-simplices of the standard resolution into its (n + 1)-simplices.
var StandardDegeneracyIn = standardDegeneracyInThm{family.Add(registry.ProofEntry{
	Name: "StandardDegeneracyIn",
	Key:  "prop_aacf10778e8f4345",
	Reading: "Neither S's ring structure nor the injectivity of the tag is " +
		"read: the degeneracies rename variables and never evaluate. With S.carrier " +
		"= ∅ there is no name of degree 0 and the 0-simplices are the constants.",
	Deps: []registry.EntryLike{
		StandardDegeneracyDef,
		StandardTermsDef,
		StandardNamesDef,
		simplicial_ring.UniverseEmbeddingHost,
		simplicial_ring.UniverseAlgebraVarDef,
		simplicial_ring.UniverseAlgebraMapDef,
		free_algebra.FreeAlgebraVarIn,
		free_algebra.FreeAlgebraMapHom,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀n j:num. ∀u:U.",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"comm_ring_on(R)",
			"j ≤ n",
			"u ∈ standard_terms(R, S, n)",
		},
		Conclusion: "standard_degeneracy(R, n, j, u) ∈ standard_terms(R, S, n + 1)",
	},
		"induct on n. The degeneracy 0 is the map induced by the variables, which "+
			"carry standard_names(R, S, n) into standard_terms(R, S, n) = "+
			"standard_names(R, S, n + 1) (FreeAlgebraVarIn); the degeneracy j + 1 is "+
			"the map induced by s(n − 1, j), which carries standard_names(R, S, n) into "+
			"standard_names(R, S, n + 1) by the induction hypothesis; FreeAlgebraMapHom"),
})}

// StandardFaceFace — in a universe for R and S, the faces of the standard
// resolution satisfy d_i d_j = d_{j−1} d_i for i < j.
var StandardFaceFace = standardFaceFaceThm{family.Add(registry.ProofEntry{
	Name: "StandardFaceFace",
	Key:  "prop_ec8b336701db29d",
	Reading: "The universe for S is load-bearing only at n = 0, i = 1, j = 2, " +
		"where the identity is d(0, 0) d(1, 1) = d(0, 0) d(1, 0) on the 1-simplices, " +
		"the tag of ε d_0 = ε d_1; every other case is a monad law of the free algebra.",
	Deps: []registry.EntryLike{
		StandardFaceDef,
		StandardFaceIn,
		StandardFacesHom,
		StandardEpsCoequalizes,
		StandardTermsDef,
		StandardNamesDef,
		simplicial_ring.UniverseEmbeddingHost,
		simplicial_ring.UniverseAlgebraMultDef,
		simplicial_ring.UniverseAlgebraMapDef,
		free_algebra.FreeAlgebraMultAssoc,
		free_algebra.FreeAlgebraMultNatural,
		free_algebra.FreeAlgebraMapCompose,
		free_algebra.FreeAlgebraMapCongruence,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B). ∀n i j:num. ∀u:U.",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"u ∈ standard_terms(R, S, n + 2)",
			"i < j",
			"j ≤ n + 2",
		},
		Conclusion: "standard_face(R, S, f, n + 1, i, standard_face(R, S, f, n + 2, j, u)) = " +
			"standard_face(R, S, f, n + 1, j - 1, standard_face(R, S, f, n + 2, i, u))",
	},
		"induct on n. At i = 0 and j = 1 it is the associativity of the multiplication "+
			"(FreeAlgebraMultAssoc); at i = 0 and j ≥ 2 the multiplication is natural for the map "+
			"induced by d(n, j − 2) (FreeAlgebraMultNatural). At i ≥ 1 both sides are maps induced "+
			"on the variables (FreeAlgebraMapCompose) whose maps of names agree by the identity "+
			"one degree down (FreeAlgebraMapCongruence); at n = 0 that identity is d(0, 0) d(1, 1) "+
			"= d(0, 0) d(1, 0) on standard_terms(R, S, 1), the tag of StandardEpsCoequalizes"),
})}

// StandardFaceDegeneracyBelow — in a universe for R and S, d_i s_j =
// s_{j−1} d_i for i < j in the standard resolution.
var StandardFaceDegeneracyBelow = standardFaceDegeneracyBelowThm{family.Add(registry.ProofEntry{
	Name: "StandardFaceDegeneracyBelow",
	Key:  "prop_7aabd8f515949d4f",
	Reading: "Neither the augmentation nor the tag is read: at n = 0 the only case, i = 0 " +
		"and j = 1, is the naturality of the multiplication for the map induced by the variables.",
	Deps: []registry.EntryLike{
		StandardFaceDef,
		StandardDegeneracyDef,
		StandardFaceIn,
		StandardDegeneracyIn,
		StandardTermsDef,
		simplicial_ring.UniverseEmbeddingHost,
		free_algebra.FreeAlgebraMultNatural,
		free_algebra.FreeAlgebraMapCompose,
		free_algebra.FreeAlgebraMapCongruence,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B). ∀n i j:num. ∀u:U.",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"u ∈ standard_terms(R, S, n + 1)",
			"i < j",
			"j ≤ n + 1",
		},
		Conclusion: "standard_face(R, S, f, n + 2, i, standard_degeneracy(R, n + 1, j, u)) = " +
			"standard_degeneracy(R, n, j - 1, standard_face(R, S, f, n + 1, i, u))",
	},
		"induct on n. At i = 0 the degeneracy s(n + 1, j) is the map induced by "+
			"s(n, j − 1), itself a map induced on the variables, and the multiplication "+
			"is natural for it (FreeAlgebraMultNatural); at i ≥ 1 both sides are maps "+
			"induced on the variables (FreeAlgebraMapCompose) whose maps of names agree "+
			"by the identity one degree down (FreeAlgebraMapCongruence)"),
})}

// StandardFaceDegeneracyEqual — in a universe for R and S, d_i s_i and
// d_{i+1} s_i are the identity on the simplices of the standard
// resolution.
var StandardFaceDegeneracyEqual = standardFaceDegeneracyEqualThm{family.Add(registry.ProofEntry{
	Name: "StandardFaceDegeneracyEqual",
	Key:  "prop_12637e0c4c4b9aa1",
	Reading: "At n = 0 the second identity is d_1 s_0 = id on the degree-0 " +
		"algebra, which holds because the face of names d(0, 0) is the tag of " +
		"the augmentation: it carries the variable of a tag x back to x.",
	Deps: []registry.EntryLike{
		StandardFaceDef,
		StandardDegeneracyDef,
		StandardEpsDef,
		StandardTermsDef,
		StandardNamesDef,
		simplicial_ring.UniverseEmbeddingHost,
		free_algebra.FreeAlgebraMultUnitRight,
		free_algebra.FreeAlgebraMultVar,
		free_algebra.FreeAlgebraEvalVar,
		free_algebra.FreeAlgebraMapCompose,
		free_algebra.FreeAlgebraMapCongruence,
		free_algebra.FreeAlgebraMapIdentity,
		functions.InverseOnRight,
		functions.InverseOnIn,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B). ∀n i:num. ∀u:U.",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"i ≤ n",
			"u ∈ standard_terms(R, S, n)",
		},
		Conclusion: "standard_face(R, S, f, n + 1, i, standard_degeneracy(R, n, i, u)) = u ∧ " +
			"standard_face(R, S, f, n + 1, i + 1, standard_degeneracy(R, n, i, u)) = u",
	},
		"induct on n. d(n + 1, 0) s(n, 0) is the multiplication after the map induced by the "+
			"variables, the identity (FreeAlgebraMultUnitRight). d(n + 1, 1) s(n, 0) is the map "+
			"induced by x ↦ d(n, 0)(var x), which is x: the multiplication at a variable "+
			"(FreeAlgebraMultVar) for n ≥ 1, and at n = 0 the tag of the preimage chosen in S's "+
			"carrier of the tag x (FreeAlgebraEvalVar, InverseOnIn, InverseOnRight); so the "+
			"identity (FreeAlgebraMapCompose, FreeAlgebraMapCongruence, FreeAlgebraMapIdentity). "+
			"For i ≥ 1 both are induced on the variables by the identities one degree down"),
})}

// StandardFaceDegeneracyAbove — in a universe for R and S, d_i s_j =
// s_j d_{i−1} for i > j + 1 in the standard resolution.
var StandardFaceDegeneracyAbove = standardFaceDegeneracyAboveThm{family.Add(registry.ProofEntry{
	Name: "StandardFaceDegeneracyAbove",
	Key:  "prop_666bacccb53e1865",
	Reading: "At n = 0 the only case is d_2 s_0 = s_0 d_1, both sides the " +
		"map induced on the 0-simplices by x ↦ the variable of the tag of ε(x).",
	Deps: []registry.EntryLike{
		StandardFaceDef,
		StandardDegeneracyDef,
		StandardFaceIn,
		StandardDegeneracyIn,
		StandardTermsDef,
		simplicial_ring.UniverseEmbeddingHost,
		free_algebra.FreeAlgebraMapVar,
		free_algebra.FreeAlgebraMapCompose,
		free_algebra.FreeAlgebraMapCongruence,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B). ∀n i j:num. ∀u:U.",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"u ∈ standard_terms(R, S, n + 1)",
			"j + 1 < i",
			"i ≤ n + 2",
		},
		Conclusion: "standard_face(R, S, f, n + 2, i, standard_degeneracy(R, n + 1, j, u)) = " +
			"standard_degeneracy(R, n, j, standard_face(R, S, f, n + 1, i - 1, u))",
	},
		"i ≥ 2, so d(n + 2, i) is the map induced by d(n + 1, i − 1), itself induced on the "+
			"variables by d(n, i − 2). At j = 0 both sides are induced on the variables, by x ↦ d(n "+
			"+ 1, i − 1)(var x) and by x ↦ var(d(n, i − 2)(x)), equal by FreeAlgebraMapVar; at j ≥ "+
			"1 by the identity one degree down (FreeAlgebraMapCompose, FreeAlgebraMapCongruence)"),
})}

// StandardDegeneracyDegeneracy — in a universe for R, s_i s_j =
// s_{j+1} s_i for i ≤ j in the standard resolution.
var StandardDegeneracyDegeneracy = standardDegeneracyDegeneracyThm{family.Add(registry.ProofEntry{
	Name: "StandardDegeneracyDegeneracy",
	Key:  "prop_11bdd1f852da4764",
	Reading: "The degeneracies do not read S: the identities are " +
		"those of renaming variables, and hold for every record S.",
	Deps: []registry.EntryLike{
		StandardDegeneracyDef,
		StandardDegeneracyIn,
		StandardDegeneraciesHom,
		StandardTermsDef,
		simplicial_ring.UniverseEmbeddingHost,
		free_algebra.FreeAlgebraMapVar,
		free_algebra.FreeAlgebraMapConst,
		free_algebra.FreeAlgebraEvalUnique,
		free_algebra.FreeAlgebraMapCompose,
		free_algebra.FreeAlgebraMapCongruence,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀n i j:num. ∀u:U.",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"comm_ring_on(R)",
			"u ∈ standard_terms(R, S, n)",
			"i ≤ j",
			"j ≤ n",
		},
		Conclusion: "standard_degeneracy(R, n + 1, i, standard_degeneracy(R, n, j, u)) = " +
			"standard_degeneracy(R, n + 1, j + 1, standard_degeneracy(R, n, i, u))",
	},
		"at i = 0 both sides are algebra maps (StandardDegeneraciesHom) fixing the "+
			"constants and carrying the variable of x to the variable of the variable of "+
			"h(x), s(n, j) being induced on the variables by h (FreeAlgebraMapVar), so they "+
			"agree (FreeAlgebraEvalUnique); at i ≥ 1 both are induced on the variables by "+
			"the identity one degree down (FreeAlgebraMapCompose, FreeAlgebraMapCongruence)"),
})}

// StandardSimplicialSet — in a universe for R and S, the simplices of the
// standard resolution with its faces and degeneracies are a simplicial
// set.
var StandardSimplicialSet = standardSimplicialSetThm{family.Add(registry.ProofEntry{
	Name: "StandardSimplicialSet",
	Key:  "prop_b2a6a2da31a880ea",
	Deps: []registry.EntryLike{
		StandardFaceIn,
		StandardDegeneracyIn,
		StandardFaceFace,
		StandardDegeneracyDegeneracy,
		StandardFaceDegeneracyBelow,
		StandardFaceDegeneracyEqual,
		StandardFaceDegeneracyAbove,
		simplicial_set.SimplicialSet,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
		},
		Conclusion: "simplicial_set(standard_resolution⟨U:U⟩(R, S, f))",
	},
		"unfold SimplicialSet: the closures are StandardFaceIn and StandardDegeneracyIn, the "+
			"identities StandardFaceFace, StandardDegeneracyDegeneracy, StandardFaceDegeneracyBelow, "+
			"StandardFaceDegeneracyEqual and StandardFaceDegeneracyAbove"),
})}

// ---------------------------------------------------------------------------
// The polynomial simplicial algebra
// ---------------------------------------------------------------------------

// StandardFacesHom — in a universe for R and S, every face of the
// standard resolution is an algebra map over R between the free algebras
// on the names of adjacent degrees.
var StandardFacesHom = standardFacesHomThm{family.Add(registry.ProofEntry{
	Name: "StandardFacesHom",
	Key:  "prop_e08d84af6d0b3cff",
	Reading: "The universe for S is not read: the augmentation inside the last face of degree " +
		"1 lands in S's carrier, the preimage of a tag being chosen there, injective tag or not.",
	Deps: []registry.EntryLike{
		StandardFaceDef,
		StandardFaceIn,
		StandardEpsHom,
		StandardNamesDef,
		StandardTermsDef,
		simplicial_ring.UniverseEmbeddingHost,
		simplicial_ring.UniverseAlgebraHomomorphismDef,
		simplicial_ring.UniverseAlgebraMultDef,
		simplicial_ring.UniverseAlgebraMapDef,
		free_algebra.FreeAlgebraMultHom,
		free_algebra.FreeAlgebraMapHom,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B). ∀n i:num.",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"i ≤ n + 1",
		},
		Conclusion: "universe_algebra_homomorphism(R, " +
			"    standard_names⟨U:U⟩(R, S, n + 1), " +
			"    standard_names(R, S, n), " +
			"    standard_face(R, S, f, n + 1, i))",
	},
		"the face 0 is the multiplication, an algebra map from the algebra on the algebra on "+
			"standard_names(R, S, n) onto the algebra on standard_names(R, S, n) "+
			"(FreeAlgebraMultHom); the face i + 1 is the map induced by d(n, i), which carries "+
			"standard_names(R, S, n + 1) into standard_names(R, S, n) (StandardFaceIn one degree "+
			"down, at n = 0 StandardEpsHom), an algebra map over the identity of R (FreeAlgebraMapHom)"),
})}

// StandardDegeneraciesHom — in a universe for R, every degeneracy of the
// standard resolution is an algebra map over R between the free algebras
// on the names of adjacent degrees.
var StandardDegeneraciesHom = standardDegeneraciesHomThm{family.Add(registry.ProofEntry{
	Name: "StandardDegeneraciesHom",
	Key:  "prop_5a831054ffd34cec",
	Deps: []registry.EntryLike{
		StandardDegeneracyDef,
		StandardDegeneracyIn,
		StandardNamesDef,
		StandardTermsDef,
		simplicial_ring.UniverseEmbeddingHost,
		simplicial_ring.UniverseAlgebraHomomorphismDef,
		simplicial_ring.UniverseAlgebraMapDef,
		free_algebra.FreeAlgebraVarIn,
		free_algebra.FreeAlgebraMapHom,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀n j:num.",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"comm_ring_on(R)",
			"j ≤ n",
		},
		Conclusion: "universe_algebra_homomorphism(R, " +
			"    standard_names⟨U:U⟩(R, S, n), " +
			"    standard_names(R, S, n + 1), " +
			"    standard_degeneracy(R, n, j))",
	},
		"every degeneracy is the map induced on the variables by the variables (j = 0) or by a "+
			"degeneracy one degree down, which carry standard_names(R, S, n) into standard_names(R, "+
			"S, n + 1) (FreeAlgebraVarIn, StandardDegeneracyIn); FreeAlgebraMapHom"),
})}

// StandardGeneratorsClosed — in a universe for R, every degeneracy of the
// standard resolution carries the variable of a name of degree n to the
// variable of a name of degree n + 1.
var StandardGeneratorsClosed = standardGeneratorsClosedThm{family.Add(registry.ProofEntry{
	Name: "StandardGeneratorsClosed",
	Key:  "prop_e02fd9361e0352a4",
	Reading: "Stated on the variables, as polynomial_simplicial_algebra's own condition " +
		"is: a name is any member of U and need not lie in an algebra, so it is the variable " +
		"of a name, not the name, that a degeneracy is asked to keep among the generators.",
	Deps: []registry.EntryLike{
		StandardDegeneracyDef,
		StandardDegeneracyIn,
		StandardNamesDef,
		StandardTermsDef,
		simplicial_ring.UniverseEmbeddingHost,
		simplicial_ring.UniverseAlgebraVarDef,
		simplicial_ring.UniverseAlgebraMapDef,
		free_algebra.FreeAlgebraMapVar,
		free_algebra.FreeAlgebraVarIn,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀n j:num.",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"comm_ring_on(R)",
			"j ≤ n",
		},
		Conclusion: "image(standard_degeneracy⟨U:U⟩(R, n, j), " +
			"    image(universe_algebra_var(R), standard_names(R, S, n))) ⊆ " +
			"image(universe_algebra_var(R), standard_names(R, S, n + 1))",
	},
		"a degeneracy is induced on the variables by h, the variables themselves (j = "+
			"0) or a degeneracy one degree down, so it carries the variable of x to the "+
			"variable of h(x) (FreeAlgebraMapVar), and h carries standard_names(R, S, n) "+
			"into standard_names(R, S, n + 1) (FreeAlgebraVarIn, StandardDegeneracyIn)"),
})}

// StandardEpsHom — in a universe for R and S, the augmentation of the
// standard resolution is a ring map from its 0-simplices into S
// carrying the constant a to f(a).
var StandardEpsHom = standardEpsHomThm{family.Add(registry.ProofEntry{
	Name: "StandardEpsHom",
	Key:  "prop_5ec4c7b2246b00a5",
	Reading: "The universe for S is not read: each name is read back by a preimage " +
		"chosen in S's carrier, a member of it whether or not the tag is injective.",
	Deps: []registry.EntryLike{
		StandardEpsDef,
		StandardTermsDef,
		StandardNamesDef,
		simplicial_ring.UniverseEmbeddingHost,
		simplicial_ring.UniverseAlgebraEvalDef,
		simplicial_ring.UniverseAlgebraRingDef,
		simplicial_ring.UniverseAlgebraConstDef,
		free_algebra.FreeAlgebraEvalHom,
		free_algebra.FreeAlgebraEvalConst,
		free_algebra.FreeAlgebraRingDef,
		functions.InverseOnIn,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
		},
		Conclusion: "ring_homomorphism( " +
			"    restrict_ring(universe_algebra_ring(R, standard_names(R, S, 0)), standard_terms(R, S, 0)), " +
			"    S, " +
			"    standard_eps⟨U:U⟩(R, S, f)) ∧ " +
			"(∀a:A. a ∈ R.carrier ⇒ standard_eps(R, S, f, universe_algebra_const⟨U:U⟩(R, a)) = f(a))",
	},
		"an evaluation into S at the universe embedding, an embedding (UniverseEmbeddingHost), "+
			"with f a ring map and each name read as the preimage chosen in S's carrier, a member "+
			"of the carrier at every tag of an element of it (InverseOnIn): FreeAlgebraEvalHom, "+
			"whose ring record has the carrier standard_terms(R, S, 0) (UniverseAlgebraRingDef, "+
			"FreeAlgebraRingDef), and FreeAlgebraEvalConst"),
})}

// StandardEpsCoequalizes — in a universe for R and S, the augmentation
// takes one value on the two vertices of an edge of the standard
// resolution: ε d_0 = ε d_1 on its 1-simplices.
var StandardEpsCoequalizes = standardEpsCoequalizesThm{family.Add(registry.ProofEntry{
	Name: "StandardEpsCoequalizes",
	Key:  "prop_7748ba8ce49f8b11",
	Reading: "The face of names d(0, 0), the tag of the augmentation, is what makes " +
		"it hold: the last face of degree 1 is the augmentation applied to the variables, " +
		"so ε d_1 evaluates every inner polynomial in S, as ε d_0 does after flattening. " +
		"It needs the tag injective on S's carrier, read back by the chosen preimage.",
	Deps: []registry.EntryLike{
		StandardEpsHom,
		StandardFacesHom,
		StandardEpsDef,
		StandardFaceDef,
		StandardTermsDef,
		StandardNamesDef,
		simplicial_ring.UniverseEmbeddingHost,
		simplicial_ring.CarrierTagInjective,
		free_algebra.FreeAlgebraMultVar,
		free_algebra.FreeAlgebraMapVar,
		free_algebra.FreeAlgebraEvalVar,
		free_algebra.FreeAlgebraEvalUnique,
		functions.InverseOnLeft,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B). ∀u:U.",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"u ∈ standard_terms(R, S, 1)",
		},
		Conclusion: "standard_eps(R, S, f, standard_face(R, S, f, 1, 0, u)) = " +
			"standard_eps(R, S, f, standard_face(R, S, f, 1, 1, u))",
	},
		"both sides are ring maps from the algebra on standard_terms(R, S, 0) into S taking the constant "+
			"a to f(a) (StandardFacesHom, StandardEpsHom). At the variable of w ∈ standard_terms(R, S, 0) "+
			"the left side is ε(w) (FreeAlgebraMultVar) and the right side ε at the variable of the tag of "+
			"ε(w) (FreeAlgebraMapVar), the preimage chosen in S's carrier of that tag, which is ε(w) as the "+
			"tag is injective (CarrierTagInjective, InverseOnLeft, FreeAlgebraEvalVar); FreeAlgebraEvalUnique"),
})}

// StandardPolynomialAlgebra — in a universe for R and S, the standard
// resolution is a polynomial simplicial algebra over R augmented over S
// by standard_eps.
var StandardPolynomialAlgebra = standardPolynomialAlgebraThm{family.Add(registry.ProofEntry{
	Name: "StandardPolynomialAlgebra",
	Key:  "prop_96fb72804b1f8274",
	Deps: []registry.EntryLike{
		simplicial_ring.AugmentedPolynomialAlgebra,
		simplicial_ring.PolynomialSimplicialAlgebra,
		StandardSimplicialSet,
		StandardTermsDef,
		StandardFacesHom,
		StandardDegeneraciesHom,
		StandardGeneratorsClosed,
		StandardEpsHom,
		StandardEpsCoequalizes,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
		},
		Conclusion: "augmented_polynomial_algebra(R, " +
			"    standard_names⟨U:U⟩(R, S), " +
			"    standard_face(R, S, f), " +
			"    standard_degeneracy(R), " +
			"    S, " +
			"    f, " +
			"    standard_eps(R, S, f))",
	},
		"unfold AugmentedPolynomialAlgebra and PolynomialSimplicialAlgebra: R is a commutative ring and "+
			"f a ring map (the hypothesis); the simplicial set is StandardSimplicialSet, the free algebras "+
			"on standard_names(R, S, n) being standard_terms(R, S, n) (StandardTermsDef); the faces and "+
			"degeneracies are algebra maps (StandardFacesHom, StandardDegeneraciesHom) keeping the variables "+
			"(StandardGeneratorsClosed); the augmentation is StandardEpsHom and StandardEpsCoequalizes"),
})}

// ---------------------------------------------------------------------------
// The extra degeneracy and acyclicity
// ---------------------------------------------------------------------------

// StandardExtraIn — in a universe for R and S, the extra degeneracy
// carries the n-simplices into the (n + 1)-simplices and its bottom
// carries S's carrier into the 0-simplices.
var StandardExtraIn = standardExtraInThm{family.Add(registry.ProofEntry{
	Name: "StandardExtraIn",
	Key:  "prop_2d4ebf641b0c140b",
	Reading: "The universe for S is not read: the bottom is the difference of the variables " +
		"of two tags of members of S's carrier, names of degree 0 whatever the tag does.",
	Deps: []registry.EntryLike{
		StandardExtraDef,
		standardExtraBottomDef,
		StandardTermsDef,
		StandardNamesDef,
		simplicial_ring.UniverseEmbeddingHost,
		simplicial_ring.UniverseAlgebraVarDef,
		simplicial_ring.UniverseAlgebraRingDef,
		free_algebra.FreeAlgebraVarIn,
		free_algebra.FreeAlgebraCommRingOn,
		free_algebra.FreeAlgebraOpsIndependentOfVariables,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
		},
		Conclusion: "(∀n:num. ∀u:U. " +
			"    u ∈ standard_terms(R, S, n) ⇒ standard_extra(R, u) ∈ standard_terms(R, S, n + 1)) ∧ " +
			"(∀y:B. y ∈ S.carrier ⇒ standard_extra_bottom⟨U:U⟩(R, S, y) ∈ standard_terms(R, S, 0))",
	},
		"the variables of u and of zero, both in standard_terms(R, S, n) = standard_names(R, S, n + "+
			"1), lie in the algebra on it (FreeAlgebraVarIn), a ring under the operations of the host ring "+
			"(FreeAlgebraCommRingOn, FreeAlgebraOpsIndependentOfVariables), so their difference does; the "+
			"bottom is the difference of the variables of the tags of y and of S.zero, both in S's carrier"),
})}

// StandardExtraFace — in a universe for R and S, the face identities of
// the extra degeneracy: d_0 σ = id and d_{i+1} σ = σ d_i.
var StandardExtraFace = standardExtraFaceThm{family.Add(registry.ProofEntry{
	Name: "StandardExtraFace",
	Key:  "prop_96e061e1cb745a69",
	Reading: "Every face out of a positive degree is a ring map and keeps the host's " +
		"zero, the zero of every free algebra over R in the universe, so the subtracted " +
		"variable of zero goes to the variable of zero and σ's shape survives the face.",
	Deps: []registry.EntryLike{
		StandardExtraDef,
		StandardFaceDef,
		StandardFacesHom,
		StandardFaceIn,
		StandardTermsDef,
		simplicial_ring.UniverseEmbeddingHost,
		free_algebra.FreeAlgebraMultVar,
		free_algebra.FreeAlgebraMapVar,
		free_algebra.FreeAlgebraOpsIndependentOfVariables,
		ring_homomorphism.AdditiveHomomorphism,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
		},
		Conclusion: "(∀n:num. ∀u:U. " +
			"    u ∈ standard_terms(R, S, n) ⇒ standard_face(R, S, f, n + 1, 0, standard_extra(R, u)) = u) ∧ " +
			"(∀n i:num. ∀u:U. " +
			"    u ∈ standard_terms(R, S, n + 1) ∧ i ≤ n + 1 ⇒ " +
			"    standard_face(R, S, f, n + 2, i + 1, standard_extra(R, u)) = " +
			"    standard_extra(R, standard_face(R, S, f, n + 1, i, u)))",
	},
		"the face 0 is the multiplication, a ring map (StandardFacesHom), taking the difference of the "+
			"variables of u and of zero to u − 0 = u (FreeAlgebraMultVar, AdditiveHomomorphism); the face "+
			"i + 1 is the map induced by d(n + 1, i), taking it to the difference of the variables of d(n "+
			"+ 1, i)(u) and of d(n + 1, i)(0) (FreeAlgebraMapVar), and d(n + 1, i) keeps zero, a ring map "+
			"whose two zeros are the host's (StandardFacesHom, FreeAlgebraOpsIndependentOfVariables)"),
})}

// StandardExtraDegeneracy — in a universe for R, the extra degeneracy
// commutes with the degeneracies one index up: s_{j+1} σ = σ s_j.
var StandardExtraDegeneracy = standardExtraDegeneracyThm{family.Add(registry.ProofEntry{
	Name: "StandardExtraDegeneracy",
	Key:  "prop_b5241079cac77592",
	Reading: "The case of s_0, s_0 σ = σ σ, is not claimed and is false: s_0 σ(u) is the " +
		"variable of the variable of u less the variable of the variable of zero, σ σ(u) the " +
		"variable of σ(u) less the variable of zero, and the variable is not additive.",
	Deps: []registry.EntryLike{
		StandardExtraDef,
		StandardDegeneracyDef,
		StandardDegeneraciesHom,
		StandardDegeneracyIn,
		StandardTermsDef,
		simplicial_ring.UniverseEmbeddingHost,
		free_algebra.FreeAlgebraMapVar,
		free_algebra.FreeAlgebraOpsIndependentOfVariables,
		ring_homomorphism.AdditiveHomomorphism,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀n j:num. ∀u:U.",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"comm_ring_on(R)",
			"u ∈ standard_terms(R, S, n)",
			"j ≤ n",
		},
		Conclusion: "standard_degeneracy(R, n + 1, j + 1, standard_extra(R, u)) = " +
			"standard_extra(R, standard_degeneracy(R, n, j, u))",
	},
		"the degeneracy j + 1 of degree n + 1 is the map induced by s(n, j), a ring map "+
			"(StandardDegeneraciesHom), so it takes the difference of the variables of u and of "+
			"zero to the difference of the variables of s(n, j)(u) and of s(n, j)(0), which is "+
			"zero (FreeAlgebraMapVar, AdditiveHomomorphism, FreeAlgebraOpsIndependentOfVariables)"),
})}

// StandardExtraBottom — in a universe for R and S, the bottom identities
// of the extra degeneracy: the augmentation reads the bottom of y back as
// y, and d_1 σ_0 = b ∘ ε on the 0-simplices.
var StandardExtraBottom = standardExtraBottomThm{family.Add(registry.ProofEntry{
	Name: "StandardExtraBottom",
	Key:  "prop_4feaad12ae0cd768",
	Reading: "The first conjunct needs the tag injective on S's carrier, which the augmentation " +
		"reads the tag of y back through; the second needs only that ε carries the host's zero to S.zero.",
	Deps: []registry.EntryLike{
		StandardExtraDef,
		standardExtraBottomDef,
		StandardEpsHom,
		StandardEpsDef,
		StandardFaceDef,
		StandardTermsDef,
		simplicial_ring.UniverseEmbeddingHost,
		simplicial_ring.CarrierTagInjective,
		free_algebra.FreeAlgebraEvalVar,
		free_algebra.FreeAlgebraMapVar,
		functions.InverseOnLeft,
		ring_homomorphism.AdditiveHomomorphism,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
		},
		Conclusion: "(∀y:B. " +
			"    y ∈ S.carrier ⇒ standard_eps(R, S, f, standard_extra_bottom⟨U:U⟩(R, S, y)) = y) ∧ " +
			"(∀u:U. " +
			"    u ∈ standard_terms(R, S, 0) ⇒ " +
			"    standard_face(R, S, f, 1, 1, standard_extra(R, u)) = " +
			"    standard_extra_bottom(R, S, standard_eps(R, S, f, u)))",
	},
		"the augmentation is a ring map (StandardEpsHom) reading the variable of the tag of "+
			"an element of S's carrier back as that element (CarrierTagInjective, InverseOnLeft, "+
			"FreeAlgebraEvalVar), so it takes the bottom of y to y − S.zero = y; the face 1 of "+
			"degree 1 is the map induced by the tag of the augmentation (StandardFaceDef), taking "+
			"the difference of the variables of u and of zero to the difference of the variables "+
			"of the tags of ε(u) and of ε(0) = S.zero (FreeAlgebraMapVar, StandardEpsHom)"),
})}

// StandardExtraPointed — in a universe for R, the extra degeneracy and
// its bottom keep zero.
var StandardExtraPointed = standardExtraPointedThm{family.Add(registry.ProofEntry{
	Name: "StandardExtraPointed",
	Key:  "prop_3d313c5a3e36088c",
	Reading: "The zero of the host ring is the zero of every free algebra over R " +
		"in the universe and of the module universe_algebra_module(R), which is the " +
		"zero the acyclicity of an extra degeneracy asks σ and the bottom to keep.",
	Deps: []registry.EntryLike{
		StandardExtraDef,
		standardExtraBottomDef,
		simplicial_ring.UniverseEmbeddingHost,
		simplicial_ring.UniverseAlgebraRingDef,
		simplicial_ring.UniverseAlgebraVarDef,
		free_algebra.FreeAlgebraCommRingOn,
		free_algebra.FreeAlgebraVarIn,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀S:ring_ops(B).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"comm_ring_on(R)",
		},
		Conclusion: "standard_extra(R, «hostZero») = «hostZero» ∧ " +
			"standard_extra_bottom(R, S, S.zero) = «hostZero»",
	},
		"each side is the difference of one variable with itself, a member "+
			"of the host ring (FreeAlgebraVarIn), a commutative ring at the "+
			"universe embedding (FreeAlgebraCommRingOn), where x − x is zero"),
})}

// StandardResolution — in a universe for R and S, the standard
// resolution is a polynomial resolution of S over R through f.
var StandardResolution = standardResolutionThm{family.Add(registry.ProofEntry{
	Name: "StandardResolution",
	Key:  "prop_e3a02408a8926c51",
	Reading: "S is any commutative algebra over R in the universe, the zero ring " +
		"among them. The extra degeneracy is not additive, so acyclicity is read on " +
		"the Moore complex, where σ enters as a map of sets keeping zero; nothing here " +
		"makes the resolution homotopy equivalent to the constant algebra as algebras.",
	Deps: []registry.EntryLike{
		StandardPolynomialAlgebra,
		StandardSimplicialSet,
		StandardEpsHom,
		StandardExtraIn,
		StandardExtraFace,
		StandardExtraDegeneracy,
		StandardExtraBottom,
		StandardExtraPointed,
		simplicial_ring.PolynomialResolution,
		simplicial_ring.PolynomialAlgebraSimplicialModule,
		simplicial_module.ExtraDegeneracyAcyclic,
		simplicial_homotopy.ExtraDegeneracy,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
		},
		Conclusion: "polynomial_resolution(R, " +
			"    standard_names⟨U:U⟩(R, S), " +
			"    standard_face(R, S, f), " +
			"    standard_degeneracy(R), " +
			"    S, " +
			"    f, " +
			"    standard_eps(R, S, f))",
	},
		"StandardPolynomialAlgebra; acyclicity is ExtraDegeneracyAcyclic at the simplicial "+
			"module of the resolution (PolynomialAlgebraSimplicialModule), with N the module S "+
			"over R through f, scalar_restriction(f, regular_module(S)), the augmentation linear "+
			"on the degree-0 algebra (StandardEpsHom), σ = λn:num. standard_extra(R) and the "+
			"bottom standard_extra_bottom(R, S): extra_degeneracy unfolds into "+
			"StandardSimplicialSet, StandardEpsHom, StandardExtraIn, StandardExtraBottom, "+
			"StandardExtraFace and StandardExtraDegeneracy, and σ keeps zero (StandardExtraPointed)"),
})}

// ---------------------------------------------------------------------------
// The augmentation in every degree
// ---------------------------------------------------------------------------

// StandardToBaseHom — in a universe for R and S, the augmentation read in
// degree n is a ring map from the n-simplices into S carrying the
// constant a to f(a).
var StandardToBaseHom = standardToBaseHomThm{family.Add(registry.ProofEntry{
	Name: "StandardToBaseHom",
	Key:  "prop_1400d45fd0db1e68",
	Reading: "At n = 0 it is StandardEpsHom: no face is composed, " +
		"and the augmentation read in degree 0 is the augmentation.",
	Deps: []registry.EntryLike{
		StandardToBaseDef,
		StandardPolynomialAlgebra,
		StandardTermsDef,
		simplicial_ring.AugmentationAtHom,
		simplicial_ring.UniverseAlgebraRingDef,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B). ∀n:num.",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
		},
		Conclusion: "ring_homomorphism( " +
			"    restrict_ring(universe_algebra_ring(R, standard_names(R, S, n)), standard_terms(R, S, n)), " +
			"    S, " +
			"    standard_to_base⟨U:U⟩(R, S, f, n)) ∧ " +
			"(∀a:A. a ∈ R.carrier ⇒ standard_to_base(R, S, f, n, universe_algebra_const⟨U:U⟩(R, a)) = f(a))",
	},
		"unfold StandardToBaseDef: AugmentationAtHom at StandardPolynomialAlgebra, the free "+
			"algebra on standard_names(R, S, n) being standard_terms(R, S, n) (StandardTermsDef)"),
})}

// StandardToBaseFaceIndependent — in a universe for R and S, the
// augmentation in degree n after any face out of degree n + 1 is the
// augmentation in degree n + 1.
var StandardToBaseFaceIndependent = standardToBaseFaceIndependentThm{family.Add(registry.ProofEntry{
	Name: "StandardToBaseFaceIndependent",
	Key:  "prop_978fed7c192be6d9",
	Reading: "At n = 0 it is StandardEpsCoequalizes: the augmentation " +
		"read in degree 1 is ε after the 0-th face, and the face 1 gives ε d_1.",
	Deps: []registry.EntryLike{
		StandardToBaseDef,
		StandardPolynomialAlgebra,
		StandardTermsDef,
		simplicial_ring.AugmentationAtFaceIndependent,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B). ∀n i:num. ∀u:U.",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"i ≤ n + 1",
			"u ∈ standard_terms(R, S, n + 1)",
		},
		Conclusion: "standard_to_base(R, S, f, n, standard_face(R, S, f, n + 1, i, u)) = " +
			"standard_to_base(R, S, f, n + 1, u)",
	},
		"unfold StandardToBaseDef: AugmentationAtFaceIndependent at StandardPolynomialAlgebra"),
})}

// ---------------------------------------------------------------------------
// The faces in degrees 1 and 2, and the representative
// ---------------------------------------------------------------------------

// StandardLowFaceFormulas — in a universe for R and S, the faces at a
// variable in degrees 1 and 2: d_0[u] = u and d_1[u] = τ(u) for u a
// 0-simplex; d_0[w] = w, d_1[w] = [d_0 w] and d_2[w] = [d_1 w] for w a
// 1-simplex; each expression in the simplices it is read in.
var StandardLowFaceFormulas = standardLowFaceFormulasThm{family.Add(registry.ProofEntry{
	Name: "StandardLowFaceFormulas",
	Key:  "prop_58816904dcff6244",
	Reading: "These are the faces the cochain complex reads in degrees 0 and 1: the coboundary " +
		"of a 0-cochain at u takes the faces of var(u), and the coboundary of a 1-cochain at w the " +
		"faces of var(w). A name of degree 1 is a 0-simplex and a name of degree 2 a 1-simplex, so " +
		"each variable lies one degree up. The universe for R gives the embedding through which " +
		"the multiplication and the induced maps read a variable back, and f supplies R as a " +
		"commutative ring with its identity a ring map; the universe for S is not read.",
	Deps: []registry.EntryLike{
		StandardFaceDef,
		StandardRepresentativeDef,
		StandardFaceIn,
		StandardTermsDef,
		StandardNamesDef,
		simplicial_ring.UniverseEmbeddingHost,
		simplicial_ring.UniverseAlgebraVarDef,
		simplicial_ring.UniverseAlgebraMultDef,
		simplicial_ring.UniverseAlgebraMapDef,
		free_algebra.FreeAlgebraMultVar,
		free_algebra.FreeAlgebraMapVar,
		free_algebra.FreeAlgebraVarIn,
		ring_homomorphism.RingHomIdentity,
		ring_homomorphism.Source,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
		},
		Conclusion: "(∀u:U. " +
			"    u ∈ standard_terms(R, S, 0) ⇒ " +
			"    universe_algebra_var(R, u) ∈ standard_terms(R, S, 1) ∧ " +
			"    standard_face(R, S, f, 1, 0, universe_algebra_var(R, u)) = u ∧ " +
			"    standard_face(R, S, f, 1, 1, universe_algebra_var(R, u)) = " +
			"    standard_representative(R, S, f, u)) ∧ " +
			"(∀w:U. " +
			"    w ∈ standard_terms(R, S, 1) ⇒ " +
			"    universe_algebra_var(R, w) ∈ standard_terms(R, S, 2) ∧ " +
			"    standard_face(R, S, f, 1, 0, w) ∈ standard_terms(R, S, 0) ∧ " +
			"    standard_face(R, S, f, 1, 1, w) ∈ standard_terms(R, S, 0) ∧ " +
			"    standard_face(R, S, f, 2, 0, universe_algebra_var(R, w)) = w ∧ " +
			"    standard_face(R, S, f, 2, 1, universe_algebra_var(R, w)) = " +
			"    universe_algebra_var(R, standard_face(R, S, f, 1, 0, w)) ∧ " +
			"    standard_face(R, S, f, 2, 2, universe_algebra_var(R, w)) = " +
			"    universe_algebra_var(R, standard_face(R, S, f, 1, 1, w)))",
	},
		"a member of standard_terms(R, S, n) is a name of degree n + 1, so its variable lies in "+
			"standard_terms(R, S, n + 1) (StandardNamesDef, StandardTermsDef, FreeAlgebraVarIn). Unfold "+
			"StandardFaceDef at degree 1 and 2: the face 0 is the multiplication, taking the variable of "+
			"u to u (FreeAlgebraMultVar); the face i + 1 is induced by the face i one degree down, taking "+
			"the variable of x to the variable of its image (FreeAlgebraMapVar) — at degree 1 the image "+
			"under the face of names, the tag of the augmentation, which is standard_representative "+
			"(StandardRepresentativeDef). The faces of w land in the 0-simplices by StandardFaceIn"),
})}

// StandardRepresentativeLaws — in a universe for R and S, the
// representative τ of a 0-simplex is a 0-simplex with the same
// augmentation, τ is idempotent, it sends the kernel of the augmentation
// to τ(0), and the two vertices of a 1-simplex have one representative.
var StandardRepresentativeLaws = standardRepresentativeLawsThm{family.Add(registry.ProofEntry{
	Name: "StandardRepresentativeLaws",
	Key:  "prop_dfbf5501a5420d2e",
	Reading: "The universe for S is load-bearing for the augmentation of τ(u): ε reads the " +
		"tag of ε(u) back through the preimage chosen in S's carrier, which is ε(u) only for the " +
		"tag injective there. The other laws read τ through the augmentation alone: ε(x) = S.zero " +
		"= ε(0) for x in the kernel, and ε d_0 = ε d_1 on a 1-simplex. So u − τ(u) lies in the " +
		"kernel for every 0-simplex u, and τ(0) = [tag S.zero] need not be the zero of the algebra.",
	Deps: []registry.EntryLike{
		StandardRepresentativeDef,
		StandardEpsDef,
		StandardEpsHom,
		StandardEpsCoequalizes,
		StandardFaceIn,
		StandardTermsDef,
		StandardNamesDef,
		simplicial_ring.UniverseEmbeddingHost,
		simplicial_ring.CarrierTagInjective,
		simplicial_ring.UniverseAlgebraVarDef,
		simplicial_ring.UniverseAlgebraEvalDef,
		free_algebra.FreeAlgebraEvalVar,
		free_algebra.FreeAlgebraVarIn,
		free_algebra.FreeAlgebraOpsIndependentOfVariables,
		simplicial_ring.UniverseAlgebraRingDef,
		functions.InverseOnLeft,
		ring_homomorphism.AdditiveHomomorphism,
		ring_homomorphism.MapIn,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
		},
		Conclusion: "(∀u:U. " +
			"    u ∈ standard_terms(R, S, 0) ⇒ " +
			"    standard_representative(R, S, f, u) ∈ standard_terms(R, S, 0) ∧ " +
			"    standard_eps(R, S, f, standard_representative(R, S, f, u)) = standard_eps(R, S, f, u) ∧ " +
			"    standard_representative(R, S, f, standard_representative(R, S, f, u)) = " +
			"    standard_representative(R, S, f, u)) ∧ " +
			"(∀x:U. " +
			"    x ∈ standard_terms(R, S, 0) ∧ standard_eps(R, S, f, x) = S.zero ⇒ " +
			"    standard_representative(R, S, f, x) = standard_representative(R, S, f, «hostZero»)) ∧ " +
			"(∀w:U. " +
			"    w ∈ standard_terms(R, S, 1) ⇒ " +
			"    standard_representative(R, S, f, standard_face(R, S, f, 1, 0, w)) = " +
			"    standard_representative(R, S, f, standard_face(R, S, f, 1, 1, w)))",
	},
		"ε(u) lies in S's carrier (MapIn at StandardEpsHom), so its tag is a name of degree 0 and its "+
			"variable a 0-simplex (StandardNamesDef, FreeAlgebraVarIn). The augmentation evaluates that "+
			"variable at the preimage chosen for the tag, ε(u) itself as the tag is injective on S's carrier "+
			"(FreeAlgebraEvalVar, CarrierTagInjective, InverseOnLeft); τ depends on its argument through the "+
			"augmentation only (StandardRepresentativeDef), so τ(τ(u)) = τ(u) by the second law, τ(x) = τ(0) "+
			"by ε(0) = S.zero (AdditiveHomomorphism at StandardEpsHom, the host's zero being the zero of the "+
			"0-simplices' ring by UniverseAlgebraRingDef and FreeAlgebraOpsIndependentOfVariables), and the "+
			"last law by StandardEpsCoequalizes, the faces of w being 0-simplices (StandardFaceIn)"),
})}

// ---------------------------------------------------------------------------
// Functoriality in the algebra
// ---------------------------------------------------------------------------

// StandardMapAugmentation — the map of standard resolutions induced by
// an algebra map g lies over g in degree 0: ε' after it is g after ε.
var StandardMapAugmentation = standardMapAugmentationThm{family.Add(registry.ProofEntry{
	Name: "StandardMapAugmentation",
	Key:  "prop_5b7877a13f008a90",
	Reading: "Only the naming's injectivity on the carrier of S' is read: ε' reads the " +
		"name of g(y) back as g(y), g(y) lying in that carrier, while on S's side the map " +
		"of names and the augmentation both read the one preimage chosen in S's carrier.",
	Deps: []registry.EntryLike{
		StandardMapDef,
		StandardEpsHom,
		StandardEpsDef,
		StandardTermsDef,
		StandardNamesDef,
		simplicial_ring.UniverseEmbeddingHost,
		simplicial_ring.CarrierTagDecode,
		free_algebra.FreeAlgebraMapHom,
		free_algebra.FreeAlgebraMapVar,
		free_algebra.FreeAlgebraMapConst,
		free_algebra.FreeAlgebraEvalVar,
		free_algebra.FreeAlgebraEvalUnique,
		ring_homomorphism.MapIn,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀S':ring_ops(C). " +
			"∀f:(A → B). " +
			"∀f':(A → C). " +
			"∀g:(B → C). " +
			"∀u:U.",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"cotangent_universe(S', 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"ring_homomorphism(R, S', f')",
			"ring_homomorphism(S, S', g)",
			"∀a:A. a ∈ R.carrier ⇒ g(f(a)) = f'(a)",
			"u ∈ standard_terms(R, S, 0)",
		},
		Conclusion: "standard_eps(R, S', f', standard_map(R, S, S', g, 0, u)) = " +
			"g(standard_eps(R, S, f, u))",
	},
		"both sides are ring maps from the algebra on the names of S's elements into S' "+
			"(FreeAlgebraMapHom then StandardEpsHom for S'; StandardEpsHom for S then g) taking "+
			"the constant a to f'(a) = g(f(a)) and the variable of the name of y to g(y): the "+
			"naming of the carrier of S' is injective there and g(y) lies in it (CarrierTagDecode, "+
			"MapIn, FreeAlgebraMapVar, FreeAlgebraEvalVar); FreeAlgebraEvalUnique"),
})}

// StandardMapAlgebraMap — an algebra map g from S to S' over R induces a
// simplicial algebra map from the standard resolution of S to that of
// S'.
var StandardMapAlgebraMap = standardMapAlgebraMapThm{family.Add(registry.ProofEntry{
	Name: "StandardMapAlgebraMap",
	Key:  "prop_ea87d65a384a30e1",
	Reading: "The map is the same in every degree's construction and reads g on S's carrier " +
		"only; both resolutions are over the one ring R, so the map fixes the constants. It " +
		"commutes with the last faces because g commutes with the structure maps: the face of " +
		"names d(0, 0) evaluates through f and f'. There the naming's injectivity on S's carrier " +
		"is load-bearing: the map of names reads the name of ε(x) back as ε(x) before applying g.",
	Deps: []registry.EntryLike{
		StandardMapDef,
		StandardMapAugmentation,
		StandardPolynomialAlgebra,
		StandardFaceDef,
		StandardDegeneracyDef,
		StandardTermsDef,
		StandardNamesDef,
		simplicial_ring.SimplicialAlgebraMap,
		simplicial_ring.UniverseEmbeddingHost,
		simplicial_ring.CarrierTagDecode,
		simplicial_set.SimplicialMap,
		free_algebra.FreeAlgebraMapHom,
		free_algebra.FreeAlgebraMultNatural,
		free_algebra.FreeAlgebraMapCompose,
		free_algebra.FreeAlgebraMapCongruence,
		free_algebra.FreeAlgebraMapVar,
		ring_homomorphism.MapIn,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀S':ring_ops(C). ∀f:(A → B). ∀f':(A → C). ∀g:(B → C).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"cotangent_universe(S', 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"ring_homomorphism(R, S', f')",
			"ring_homomorphism(S, S', g)",
			"∀a:A. a ∈ R.carrier ⇒ g(f(a)) = f'(a)",
		},
		Conclusion: "simplicial_algebra_map(R, " +
			"    standard_names⟨U:U⟩(R, S), " +
			"    standard_face(R, S, f), " +
			"    standard_degeneracy(R), " +
			"    standard_names(R, S'), " +
			"    standard_face(R, S', f'), " +
			"    standard_degeneracy(R), " +
			"    standard_map(R, S, S', g))",
	},
		"both ends are polynomial simplicial algebras (StandardPolynomialAlgebra). Induct on the "+
			"degree: standard_map(R, S, S', g, n) is induced on the variables, an algebra map "+
			"(FreeAlgebraMapHom) carrying the names of degree n of S into those of S' — in degree 0 the "+
			"names of S's elements to names of the elements of S', g landing in the carrier of S' (MapIn). "+
			"It commutes with the face 0, the multiplication, by FreeAlgebraMultNatural, with the faces i "+
			"+ 1 and the degeneracies by the identities one degree down (FreeAlgebraMapCompose, "+
			"FreeAlgebraMapCongruence, FreeAlgebraMapVar), whose base is StandardMapAugmentation named in "+
			"the carrier of S', the naming of S's carrier read back on its members (CarrierTagDecode)"),
})}

// StandardMapIdentity — in a universe for R, the identity of S induces
// the identity of its standard resolution.
var StandardMapIdentity = standardMapIdentityThm{family.Add(registry.ProofEntry{
	Name: "StandardMapIdentity",
	Key:  "prop_ad4dde2a62c1c073",
	Reading: "No injectivity of the naming is asked: the name of the " +
		"preimage chosen in S's carrier of a name is that name. The target ring " +
		"is S itself, so the names of degree 0 of the two ends are one naming.",
	Deps: []registry.EntryLike{
		StandardMapDef,
		StandardTermsDef,
		StandardNamesDef,
		simplicial_ring.UniverseEmbeddingHost,
		free_algebra.FreeAlgebraMapCongruence,
		free_algebra.FreeAlgebraMapIdentity,
		simplicial_ring.CarrierTagDecode,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀n:num. ∀u:U.",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"comm_ring_on(R)",
			"u ∈ standard_terms(R, S, n)",
		},
		Conclusion: "standard_map(R, S, S, λy:B. y, n, u) = u",
	},
		"induct on n: in degree 0 the map of names carries a name of S's carrier to the "+
			"name of the preimage chosen in S's carrier, the name itself (the first half of "+
			"CarrierTagDecode); above, the map of names is the map of degree n, the identity "+
			"on the names by the induction; FreeAlgebraMapCongruence and FreeAlgebraMapIdentity"),
})}

// StandardMapCompose — in a universe for R and S', the maps of standard
// resolutions induced by g from S to S' and by g' from S' to a third
// algebra compose to the map induced by g' ∘ g.
var StandardMapCompose = standardMapComposeThm{family.Add(registry.ProofEntry{
	Name: "StandardMapCompose",
	Key:  "prop_e2865a6bf06b6189",
	Reading: "Only the inner map is asked to land in the middle carrier, and the naming of " +
		"the middle carrier to be injective there: a map of standard resolutions reads the maps " +
		"of carriers alone. Both sides read the one preimage chosen in S's carrier and name the " +
		"result in the carrier of the last ring, so nothing is asked of the first ring or the last.",
	Deps: []registry.EntryLike{
		StandardMapDef,
		StandardTermsDef,
		StandardNamesDef,
		simplicial_ring.UniverseEmbeddingHost,
		simplicial_ring.CarrierTagDecode,
		free_algebra.FreeAlgebraMapCompose,
		free_algebra.FreeAlgebraMapCongruence,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀S':ring_ops(C). " +
			"∀S'':ring_ops(D). " +
			"∀g:(B → C). " +
			"∀g':(C → D). " +
			"∀n:num. " +
			"∀u:U.",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S', 𝕌⟨A:U⟩)",
			"comm_ring_on(R)",
			"∀y:B. y ∈ S.carrier ⇒ g(y) ∈ S'.carrier",
			"u ∈ standard_terms(R, S, n)",
		},
		Conclusion: "standard_map(R, S', S'', g', n, standard_map(R, S, S', g, n, u)) = " +
			"standard_map(R, S, S'', λy:B. g'(g(y)), n, u)",
	},
		"induct on n: in degree 0 the composite of the maps of names carries the name of y "+
			"to the name in the last carrier of g' at the preimage chosen in the middle "+
			"carrier of the name of g(y₀), y₀ the preimage chosen in S's carrier of the name "+
			"of y, which is g(y₀) as the naming of the middle carrier is injective there and "+
			"g(y₀) lies in it (CarrierTagDecode); above, the map of names is the map of degree "+
			"n, composed by the induction; FreeAlgebraMapCompose and FreeAlgebraMapCongruence"),
})}

// ---------------------------------------------------------------------------
// Change of the coefficient ring
// ---------------------------------------------------------------------------

// StandardBaseChangeAugmentation — in a universe for R and S, the change
// of coefficients from R to S lies over T in degree 0: the augmentation
// of T over S after it is the augmentation of T over R through g ∘ f.
var StandardBaseChangeAugmentation = standardBaseChangeAugmentationThm{family.Add(registry.ProofEntry{
	Name: "StandardBaseChangeAugmentation",
	Key:  "prop_fa1d37fb685ac938",
	Reading: "The universe for T is not read: both augmentations read a name back by the one " +
		"preimage chosen in T's carrier, a member of it whether or not the tag is injective. It is " +
		"read on the 0-simplices over R, the algebra over R on the tags of T's elements, every name " +
		"of which the change of coefficients fixes. The universe for S is load-bearing: the " +
		"augmentation over S reads standard_base_change(R, S, f, 0)(u) back through ι_S's preimage. " +
		"Over the zero ring R the ring maps force S and T to be zero rings, and both sides are T.zero.",
	Deps: []registry.EntryLike{
		StandardBaseChangeDef,
		StandardEpsDef,
		StandardTermsDef,
		StandardNamesDef,
		simplicial_ring.UniverseEmbeddingHost,
		simplicial_ring.UniverseAlgebraMapDef,
		simplicial_ring.UniverseAlgebraEvalDef,
		free_algebra.FreeAlgebraMapHom,
		free_algebra.FreeAlgebraMapConst,
		free_algebra.FreeAlgebraMapVar,
		free_algebra.FreeAlgebraEvalHom,
		free_algebra.FreeAlgebraEvalConst,
		free_algebra.FreeAlgebraEvalVar,
		free_algebra.FreeAlgebraEvalUnique,
		functions.InverseOnIn,
		ring_homomorphism.RingHomomorphism,
		ring_homomorphism.MapIn,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀T:ring_ops(C). ∀f:(A → B). ∀g:(B → C). ∀u:U.",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"ring_homomorphism(S, T, g)",
			"u ∈ standard_terms(R, T, 0)",
		},
		Conclusion: "standard_eps(S, T, g, standard_base_change(R, S, f, 0, u)) = " +
			"standard_eps(R, T, λa:A. g(f(a)), u)",
	},
		"both sides are ring maps from the algebra over R on the tags of T's elements into T, taking "+
			"the constant a to g(f(a)) and the variable of a tag x to the preimage chosen for x in T's "+
			"carrier. The left is the change of coefficients, an algebra map over f into the algebra "+
			"over S on the same tags (FreeAlgebraMapHom, FreeAlgebraMapConst, FreeAlgebraMapVar), "+
			"followed by an evaluation into T over g; the right an evaluation into T over g ∘ f, a ring "+
			"map as a composite of two (RingHomomorphism, MapIn); each evaluation is a ring map with "+
			"those values, the preimages lying in T's carrier (FreeAlgebraEvalHom, FreeAlgebraEvalConst, "+
			"FreeAlgebraEvalVar, InverseOnIn, UniverseEmbeddingHost for R and S); FreeAlgebraEvalUnique"),
})}

// StandardBaseChangeMap — in a universe for R, S and T, the change of
// coefficients from R to S along f is a simplicial map from the standard
// resolution of T over R through g ∘ f to the standard resolution of T
// over S through g, in every degree an algebra map over f.
var StandardBaseChangeMap = standardBaseChangeMapThm{family.Add(registry.ProofEntry{
	Name: "StandardBaseChangeMap",
	Key:  "prop_f591d5a65db87037",
	Reading: "The map fixes the names of degree 0, the tags of T's elements, and changes " +
		"the coefficients along f degree by degree. It commutes with the faces because the " +
		"structure map over R is g ∘ f: the last face of degree 1 is the tag of the " +
		"augmentation, where StandardBaseChangeAugmentation is the base. The universe for T " +
		"enters only through the two simplicial sets; the map identities need only the " +
		"universes for R and S, and these are the hypotheses on the map that the base change " +
		"of the cotangent complex asks. The second conjunct is about the algebras on the " +
		"names, carrying standard_terms(R, T, n) into standard_terms(S, T, n); on the names " +
		"themselves the map acts through the variables, var y ↦ var(standard_base_change(n − " +
		"1)(y)), and applied directly to a name of degree n ≥ 1 it is not a name over S.",
	Deps: []registry.EntryLike{
		StandardBaseChangeDef,
		StandardBaseChangeAugmentation,
		StandardSimplicialSet,
		StandardFaceDef,
		StandardDegeneracyDef,
		StandardNamesDef,
		StandardTermsDef,
		simplicial_set.SimplicialMap,
		simplicial_ring.UniverseEmbeddingHost,
		simplicial_ring.UniverseAlgebraMapDef,
		simplicial_ring.UniverseAlgebraMultDef,
		free_algebra.FreeAlgebraMapHom,
		free_algebra.FreeAlgebraMultNatural,
		free_algebra.FreeAlgebraMapCompose,
		free_algebra.FreeAlgebraMapCongruence,
		free_algebra.FreeAlgebraMapVar,
		ring_homomorphism.RingHomomorphism,
		ring_homomorphism.MapIn,
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
		Conclusion: "simplicial_map(standard_resolution⟨U:U⟩(R, T, λa:A. g(f(a))), " +
			"    standard_resolution⟨U:U⟩(S, T, g), " +
			"    standard_base_change(R, S, f)) ∧ " +
			"(∀n:num. " +
			"    free_algebra_homomorphism(universe_embedding⟨U:U⟩(R), " +
			"        universe_embedding(S), " +
			"        R, " +
			"        S, " +
			"        f, " +
			"        standard_names(R, T, n), " +
			"        standard_names(S, T, n), " +
			"        standard_base_change(R, S, f, n)))",
	},
		"induct on n. The map of degree n is induced by f on the coefficients and on the names by "+
			"the identity in degree 0 and by the map one degree down above (StandardBaseChangeDef), "+
			"which carries the names of degree n over R into those over S by the induction: an algebra "+
			"map over f (FreeAlgebraMapHom at both universe embeddings, UniverseEmbeddingHost). Both "+
			"ends are simplicial sets (StandardSimplicialSet at T over R through g ∘ f, a composite of "+
			"ring maps, and at T over S through g). The face 0, the multiplication, commutes with the "+
			"map by FreeAlgebraMultNatural; the faces i + 1 and the degeneracies are induced on the "+
			"names by maps one degree down, so both composites are induced over f by composed maps of "+
			"names (FreeAlgebraMapCompose) that agree on the names by the identity one degree down "+
			"(FreeAlgebraMapCongruence), whose base is the tag of StandardBaseChangeAugmentation for "+
			"the last face of degree 1 and the variables for the degeneracy 0 (FreeAlgebraMapVar)"),
})}

// ---------------------------------------------------------------------------
// The simplicial flagship's reading
// ---------------------------------------------------------------------------

// StandardResolutionKan — in a universe for R and S, the simplicial set of
// the standard resolution is a Kan complex.
var StandardResolutionKan = standardResolutionKanThm{family.Add(registry.ProofEntry{
	Name: "StandardResolutionKan",
	Key:  "prop_9ec81d519d49bfc7",
	Reading: "Stated with the simplicial flagship's kan_complex; " +
		"the resolution's acyclicity does not go through it.",
	Deps: []registry.EntryLike{
		StandardPolynomialAlgebra,
		StandardTermsDef,
		simplicial_ring.PolynomialAlgebraKan,
		simplicial_ring.PolynomialAlgebraSimplicialModule,
		simplicial_module.HornFillerExists,
		kan_complex.KanComplex,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
		},
		Conclusion: "kan_complex(standard_resolution⟨U:U⟩(R, S, f))",
	},
		"PolynomialAlgebraKan at StandardPolynomialAlgebra, whose simplices universe_algebra(R, "+
			"standard_names(R, S, n)) are standard_terms(R, S, n) (StandardTermsDef): Moore's theorem, "+
			"HornFillerExists, at the underlying simplicial module (PolynomialAlgebraSimplicialModule)"),
})}

// StandardResolutionHomotopyGroupsTrivial — in a universe for R and S,
// every homotopy group of positive dimension of the standard resolution,
// at every vertex, is the one class of its unit.
var StandardResolutionHomotopyGroupsTrivial = standardResolutionHomotopyGroupsTrivialThm{family.Add(registry.ProofEntry{
	Name: "StandardResolutionHomotopyGroupsTrivial",
	Key:  "prop_6503cf093f45c750",
	Reading: "The acyclicity of the resolution said with the simplicial flagship's homotopy " +
		"groups, the base point anywhere in the degree-0 algebra. Dimension 0 is excluded: the " +
		"vertices modulo the Moore boundaries are read by the augmentation onto S's carrier.",
	Deps: []registry.EntryLike{
		StandardResolution,
		StandardTermsDef,
		simplicial_ring.PolynomialResolution,
		simplicial_group.AcyclicHomotopyGroupsTrivial,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B). ∀x₀:U. ∀n:num.",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"x₀ ∈ standard_terms(R, S, 0)",
			"0 < n",
		},
		Conclusion: "simplicial_homotopy_group(standard_resolution⟨U:U⟩(R, S, f), x₀, n) = " +
			"{simplicial_homotopy_unit(standard_resolution⟨U:U⟩(R, S, f), x₀, n)}",
	},
		"StandardResolution carries acyclic_augmentation of the underlying "+
			"simplicial module (PolynomialResolution), its simplices "+
			"universe_algebra(R, standard_names(R, S, m)) being standard_terms(R, S, m) "+
			"(StandardTermsDef); AcyclicHomotopyGroupsTrivial reads it at the vertex x₀"),
})}
