// simplicial_group.go — the homotopy groups of a simplicial module read
// off its Moore complex. At the vertex V.zero the base simplex is V.zero
// in every dimension (simplicial_set's BaseSimplexFixedPoint, each
// 0-th degeneracy keeping zero), so a sphere there is a simplex all of
// whose faces vanish, a Moore cycle. A homotopy between two spheres reads faces n
// and n + 1 of an (n+1)-simplex and a Moore boundary reads face 0;
// subtracting a degeneracy moves the one nonzero face of a simplex to
// the next place, so the Moore boundaries are read through any face, two
// spheres are homotopic exactly when their difference is a Moore
// boundary, and πₙ at V.zero is the Moore homology Hₙ as a set of sets.
// Adding the base simplex at a vertex x₀ is an automorphism of the
// underlying simplicial set carrying V.zero to x₀, so πₙ at x₀ is in
// bijection with πₙ at V.zero; πₙ is one class at any vertex exactly
// when the Moore complex is exact in degree n, and every positive πₙ of
// an acyclic augmentation is its unit. The Kan property the classes are
// taken under is simplicial_module's HornFillerExists.

package simplicial_group

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/quotient_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/chain_complex"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/relations/equivalence"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/simplicial/homotopy_group"
	"github.com/euc-ai/xugo/library/proofs/simplicial/simplicial_module"
	"github.com/euc-ai/xugo/library/proofs/simplicial/simplicial_set"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// Spheres at zero and Moore cycles
// ---------------------------------------------------------------------------

// HomotopyGroupMooreCycles — the spheres at V.zero are the Moore cycles,
// in every dimension.
var HomotopyGroupMooreCycles = homotopyGroupMooreCyclesThm{family.Add(registry.ProofEntry{
	Name: "HomotopyGroupMooreCycles",
	Key:  "prop_608371f513accec8",
	Reading: "At n = 0 both sides are all of M(0): the sphere condition is guarded by 0 " +
		"< n, and the Moore condition on the faces 1, …, 0 is empty with no cycle condition " +
		"in degree 0. Above 0 a sphere at V.zero has every face V.zero, the 0-th included, " +
		"which is the Moore condition on the faces 1, …, n with the cycle condition on d_0.",
	Deps: []registry.EntryLike{
		simplicial_set.BaseSimplexFixedPoint,
		simplicial_module.DegeneracyZero,
		homotopy_group.SimplicialSphereDef,
		simplicial_module.MooreComplexDef,
		simplicial_module.MooreTermsDef,
		chain_complex.CyclesDef,
		set_basic.Extension,
	},
	Build: family.Card(
		simplicial_module.SimplicialModule.Statement(
			"∀n:num. simplicial_sphere(M, V.zero, n) = cycles(moore_complex(V, M), n)"),
		"for 0 < n the sphere condition reads d(n, i, x) = base_simplex(s, V.zero, n − 1) = V.zero "+
			"for every i ≤ n (SimplicialSphereDef, BaseSimplexFixedPoint, DegeneracyZero); a Moore cycle "+
			"of degree n is an x ∈ M(n) with d(n, i, x) = V.zero for 1 ≤ i ≤ n (MooreTermsDef) and d(n, "+
			"0, x) = V.zero (CyclesDef at MooreComplexDef); at n = 0 both sets are M(0) (Extension)"),
})}

// MooreBoundaryAtFace — the Moore boundaries of degree n are read through
// any face k ≤ n + 1: c is one exactly when some (n+1)-simplex has c as
// its k-th face and V.zero as every other.
var MooreBoundaryAtFace = mooreBoundaryAtFaceThm{family.Add(registry.ProofEntry{
	Name: "MooreBoundaryAtFace",
	Key:  "prop_1a9762d1677c26bb",
	Reading: "At k = 0 the right side is the definition of a Moore boundary, the image " +
		"of d_0 on the Moore terms. Moving the nonzero face by one place negates its " +
		"value, so the set read at face k is the Moore boundaries because they form a " +
		"subgroup. k ≤ n + 1 is load-bearing: past n + 1 the face is a value no axiom reads.",
	Deps: []registry.EntryLike{
		simplicial_module.SimplicialModule,
		simplicial_module.MooreComplexChain,
		simplicial_module.MooreComplexDef,
		simplicial_module.MooreTermsDef,
		chain_complex.BoundariesDef,
		chain_complex.BoundariesSubmodule,
		simplicial_set.FaceFace,
		simplicial_set.FaceIn,
		simplicial_set.DegeneracyIn,
		simplicial_set.FaceDegeneracyEqual,
		simplicial_set.FaceDegeneracyNext,
		simplicial_module.FaceDegeneracyBelowZero,
		simplicial_module.FaceDegeneracyAboveZero,
		simplicial_module.FaceSub,
		simplicial_module.FaceZero,
		submodule.SubmoduleSubgroup,
	},
	Build: family.Card(simplicial_module.SimplicialModule.Statement(Statement{
		Binders: "∀n k:num. ∀c:B.",
		Hypotheses: []string{
			"k ≤ n + 1",
		},
		Conclusion: "c ∈ boundaries(moore_complex(V, M), n) ⇔ " +
			"∃z:B. " +
			"    z ∈ M.simplices(n + 1) ∧ " +
			"    (∀i:num. i ≤ n + 1 ∧ ¬(i = k) ⇒ M.d(n + 1, i, z) = V.zero) ∧ " +
			"    M.d(n + 1, k, z) = c",
	}),
		"induction on k; at k = 0 the right side is BoundariesDef at MooreComplexDef and "+
			"MooreTermsDef. If every face of z ∈ M(n + 1) but one vanishes, the remaining face c "+
			"has every face V.zero (FaceFace, FaceZero), so s(n, k, c) has faces k and k + 1 equal "+
			"to c and every other face V.zero (FaceDegeneracyEqual, FaceDegeneracyNext, and "+
			"FaceDegeneracyBelowZero, FaceDegeneracyAboveZero on the zero faces of c); subtracting "+
			"it from z moves the nonzero face between the places k and k + 1 and negates it "+
			"(FaceSub). The step from k to k + 1 reads the induction at −c in both directions, the "+
			"Moore boundaries being a submodule (BoundariesSubmodule at MooreComplexChain)"),
})}

// ---------------------------------------------------------------------------
// Homotopy at zero is the Moore homology
// ---------------------------------------------------------------------------

// HomotopicIffMooreBoundary — two spheres at V.zero are homotopic exactly
// when their difference is a Moore boundary.
var HomotopicIffMooreBoundary = homotopicIffMooreBoundaryThm{family.Add(registry.ProofEntry{
	Name: "HomotopicIffMooreBoundary",
	Key:  "prop_8e48d0828c427b76",
	Reading: "The homotopy reads faces n and n + 1 of an (n+1)-simplex with every face " +
		"below n at the base simplex, V.zero here; the Moore boundary reads face 0 with " +
		"every face above it V.zero. The two conventions meet at MooreBoundaryAtFace with " +
		"k = n. At n = 0 the homotopy is an edge from y to x and the base point is not read.",
	Deps: []registry.EntryLike{
		MooreBoundaryAtFace,
		simplicial_set.BaseSimplexFixedPoint,
		simplicial_module.DegeneracyZero,
		homotopy_group.SimplicialSphereDef,
		homotopy_group.SimplicialHomotopicDef,
		simplicial_set.DegeneracyIn,
		simplicial_module.FaceDegeneracyBelowZero,
		simplicial_set.FaceDegeneracyEqual,
		simplicial_set.FaceDegeneracyNext,
		simplicial_module.FaceAdd,
		simplicial_module.FaceSub,
		module.AddGroupOn,
		submodule.SubmoduleSubgroup,
	},
	Build: family.Card(simplicial_module.SimplicialModule.Statement(Statement{
		Binders: "∀n:num. ∀x y:B.",
		Hypotheses: []string{
			"x ∈ simplicial_sphere(M, V.zero, n)",
			"y ∈ simplicial_sphere(M, V.zero, n)",
		},
		Conclusion: "simplicial_homotopic(M, V.zero, n, x, y) ⇔ " +
			"V.add(x, V.neg(y)) ∈ boundaries(moore_complex(V, M), n)",
	}),
		"the faces below n of a homotopy are base_simplex(s, V.zero, n) = V.zero "+
			"(BaseSimplexFixedPoint, DegeneracyZero). s(n, n, y) has faces n and n + 1 equal to y "+
			"(FaceDegeneracyEqual, FaceDegeneracyNext) and every face below n V.zero, the faces of the "+
			"sphere y being V.zero (FaceDegeneracyBelowZero). ⇒: for a homotopy h from x to y, h − s(n, "+
			"n, y) has every face V.zero but the n-th, which is x − y, and MooreBoundaryAtFace at k = n "+
			"reads it as a boundary. ⇐: MooreBoundaryAtFace at k = n gives z with x − y as its n-th face "+
			"and V.zero as every other, and z + s(n, n, y) is a homotopy from x to y (FaceAdd, FaceSub)"),
})}

// HomotopyClassMooreCoset — the homotopy class of a sphere at V.zero is
// its coset modulo the Moore boundaries.
var HomotopyClassMooreCoset = homotopyClassMooreCosetThm{family.Add(registry.ProofEntry{
	Name: "HomotopyClassMooreCoset",
	Key:  "prop_e3ab827c3eb8a294",
	Reading: "At n = 0 the class is the coset of x modulo " +
		"d_0(moore_terms(1)), the Moore boundaries of degree 0.",
	Deps: []registry.EntryLike{
		HomotopicIffMooreBoundary,
		HomotopyGroupMooreCycles,
		homotopy_group.HomotopicSphere,
		equivalence.EquivalenceClassDef,
		group.LeftCosetDef,
		group.InLeftCosetOn,
		module.AddGroupOn,
		simplicial_module.MooreComplexChain,
		chain_complex.BoundariesSubmodule,
		chain_complex.BoundariesSubsetCycles,
		chain_complex.CyclesSubmodule,
		set_basic.Extension,
	},
	Build: family.Card(simplicial_module.SimplicialModule.Statement(Statement{
		Binders: "∀n:num. ∀x:B.",
		Hypotheses: []string{
			"x ∈ simplicial_sphere(M, V.zero, n)",
		},
		Conclusion: "equivalence_class(simplicial_homotopic(M, V.zero, n), x) = " +
			"left_coset(V.add, x, boundaries(moore_complex(V, M), n))",
	}),
		"a simplex homotopic to the sphere x is a sphere (HomotopicSphere, V.zero lying in "+
			"M(0)), so the class is the spheres y with x − y a Moore boundary "+
			"(HomotopicIffMooreBoundary), and such a y is x + (y − x) with y − x = −(x − y) a "+
			"boundary; conversely x + b for a boundary b is a Moore cycle (BoundariesSubsetCycles, "+
			"CyclesSubmodule at MooreComplexChain), so a sphere (HomotopyGroupMooreCycles), with x "+
			"− (x + b) = −b a boundary (InLeftCosetOn at the additive group of V, AddGroupOn)"),
})}

// HomotopyGroupMooreHomology — πₙ of a simplicial module at V.zero is the
// n-th homology of its Moore complex: the class of a sphere is its coset
// modulo the Moore boundaries, so the two are one set of sets.
var HomotopyGroupMooreHomology = homotopyGroupMooreHomologyThm{family.Add(registry.ProofEntry{
	Name: "HomotopyGroupMooreHomology",
	Key:  "prop_1db11f5a44098a73",
	Reading: "The comparison is an equality, its map the identity: a class " +
		"under homotopy is a coset (HomotopyClassMooreCoset). The group structure " +
		"of πₙ is not read. At n = 0 the base point is not read and both sides are " +
		"M(0) modulo d_0(moore_terms(1)); for the zero module both are {{V.zero}}.",
	Deps: []registry.EntryLike{
		HomotopyClassMooreCoset,
		HomotopyGroupMooreCycles,
		HomotopicIffMooreBoundary,
		MooreBoundaryAtFace,
		homotopy_group.InHomotopyGroup,
		chain_complex.HomologyDef,
		quotient_group.LeftCosetsDef,
		set_basic.Extension,
	},
	Build: family.Card(
		simplicial_module.SimplicialModule.Statement(
			"∀n:num. simplicial_homotopy_group(M, V.zero, n) = homology(moore_complex(V, M), n)"),
		"πₙ is the set of classes of spheres (InHomotopyGroup) and Hₙ the set of cosets of the "+
			"boundaries by the cycles (HomologyDef, LeftCosetsDef); the spheres are the cycles "+
			"(HomotopyGroupMooreCycles) and the class of each is its coset (HomotopyClassMooreCoset). The "+
			"face conventions meet in HomotopicIffMooreBoundary: a homotopy reads faces n and n + 1 with "+
			"the faces below n at the base, the Moore complex intersects the kernels of d_1, …, d_n and "+
			"differentiates by d_0, and subtracting a degeneracy moves the one nonzero face of a simplex "+
			"to the next place (MooreBoundaryAtFace). Moore's comparison of the homotopy of a simplicial "+
			"group with its normalized complex (May, Simplicial Objects in Algebraic Topology, Ch. IV)"),
})}

// ---------------------------------------------------------------------------
// Other base points
// ---------------------------------------------------------------------------

// BasepointTranslationIsomorphism — for a vertex x₀, adding the base
// simplex at x₀ in every dimension is an automorphism of the underlying
// simplicial set; in dimension 0 it carries V.zero to x₀.
var BasepointTranslationIsomorphism = basepointTranslationIsomorphismThm{family.Add(registry.ProofEntry{
	Name: "BasepointTranslationIsomorphism",
	Key:  "prop_e4bbbaaafe3d0462",
	Reading: "The translation is additive only at x₀ = V.zero: it is an automorphism " +
		"of the simplicial set, not of the simplicial module, which is all the homotopy " +
		"relation reads. x₀ ∈ M(0) is load-bearing: it puts every base simplex in M(n), " +
		"where the translation keeps M(n) and is inverted by the negated base simplex.",
	Deps: []registry.EntryLike{
		simplicial_module.SimplicialModule,
		simplicial_set.SimplicialIsomorphismDef,
		simplicial_set.SimplicialMap,
		simplicial_set.BaseSimplexIn,
		simplicial_set.BaseSimplexFace,
		simplicial_set.BaseSimplexDegeneracy,
		simplicial_set.FaceIn,
		simplicial_set.DegeneracyIn,
		simplicial_module.FaceAdd,
		simplicial_module.DegeneracyAdd,
		module.AddGroupOn,
		submodule.SubmoduleSubgroup,
	},
	Build: family.Card(simplicial_module.SimplicialModule.Statement(Statement{
		Binders: "∀x₀:B.",
		Hypotheses: []string{
			"x₀ ∈ M.simplices(0)",
		},
		Conclusion: "simplicial_isomorphism(M, M, λn:num. λu:B. V.add(u, base_simplex(x₀, n)))",
	}),
		"the base simplex lies in M(n) (BaseSimplexIn), so the translation keeps M(n), "+
			"where it is a bijection with the translation by the negated base simplex as "+
			"inverse (AddGroupOn, SubmoduleSubgroup); it commutes with the faces since d(n + "+
			"1, i) carries base_simplex(s, x₀, n + 1) to base_simplex(s, x₀, n) (FaceAdd, "+
			"BaseSimplexFace), and with the degeneracies since s(n, i) carries base_simplex(s, "+
			"x₀, n) to base_simplex(s, x₀, n + 1) (DegeneracyAdd, BaseSimplexDegeneracy)"),
})}

// BasepointTranslation — πₙ at a vertex x₀ is the direct image of πₙ at
// V.zero under the translation by the base simplex at x₀, and the direct
// image is injective on the classes: the two are in bijection.
var BasepointTranslation = basepointTranslationThm{family.Add(registry.ProofEntry{
	Name: "BasepointTranslation",
	Key:  "prop_5ba4c33f2a60b633",
	Reading: "The bijection C ↦ image(T_n, C), T_n(u) = u + base_simplex(s, x₀, " +
		"n), is spelled through the direct image and reads no group structure on πₙ. " +
		"At n = 0 the homotopy relation does not read the base point, T_0 is the " +
		"translation by x₀, and the statement says that it permutes the classes of π₀.",
	Deps: []registry.EntryLike{
		BasepointTranslationIsomorphism,
		simplicial_set.BaseSimplexFixedPoint,
		simplicial_module.DegeneracyZero,
		homotopy_group.InHomotopyGroup,
		homotopy_group.SimplicialSphereDef,
		homotopy_group.SimplicialHomotopicDef,
		homotopy_group.MapSphere,
		homotopy_group.MapHomotopic,
		simplicial_set.IsomorphismInverse,
		equivalence.EquivalenceClassDef,
		module.AddGroupOn,
		set_basic.Extension,
	},
	Build: family.Card(simplicial_module.SimplicialModule.Statement(Statement{
		Binders: "∀x₀:B. ∀n:num.",
		Hypotheses: []string{
			"x₀ ∈ M.simplices(0)",
		},
		Conclusion: "simplicial_homotopy_group(M, x₀, n) = " +
			"image(λC:set(B). image(λu:B. V.add(u, base_simplex(x₀, n)), C), " +
			"    simplicial_homotopy_group(M, V.zero, n)) ∧ " +
			"injective_on(simplicial_homotopy_group(M, V.zero, n), " +
			"    λC:set(B). image(λu:B. V.add(u, base_simplex(x₀, n)), C))",
	}),
		"the translation T is a simplicial isomorphism with T(0, V.zero) = V.zero + x₀ = x₀ "+
			"(BasepointTranslationIsomorphism, AddGroupOn), so it carries spheres and homotopies "+
			"at V.zero to spheres and homotopies at x₀ (MapSphere, MapHomotopic), and its "+
			"inverse, the translation by the negated base simplex, carries them back "+
			"(IsomorphismInverse, BaseSimplexFixedPoint, DegeneracyZero); so T_n carries the "+
			"class at V.zero of a sphere x onto the class at x₀ of T_n(x), and every sphere at "+
			"x₀ is T_n of a sphere at V.zero (InHomotopyGroup, EquivalenceClassDef). The classes "+
			"lie in M(n), where T_n is injective, so the direct image is injective on them"),
})}

// HomotopyGroupTrivialIffMooreExact — at any vertex, πₙ is the one class
// of its unit exactly when the Moore complex is exact in degree n.
var HomotopyGroupTrivialIffMooreExact = homotopyGroupTrivialIffMooreExactThm{family.Add(registry.ProofEntry{
	Name: "HomotopyGroupTrivialIffMooreExact",
	Key:  "prop_711465e98dd1a89f",
	Reading: "The unit lies in πₙ (UnitIn), so the left side says only that πₙ has one " +
		"member. At n = 0 it says that M(0) is one class under the edges, and the right " +
		"side that every vertex is a Moore boundary, d_0 of an edge whose face 1 is V.zero.",
	Deps: []registry.EntryLike{
		BasepointTranslation,
		HomotopyGroupMooreHomology,
		homotopy_group.UnitIn,
		chain_complex.HomologyTrivialIffExact,
		simplicial_module.MooreComplexChain,
		chain_complex.HomologyDef,
		chain_complex.BoundariesSubmodule,
		group.LeftCosetDef,
		set_basic.Extension,
	},
	Build: family.Card(simplicial_module.SimplicialModule.Statement(Statement{
		Binders: "∀x₀:B. ∀n:num.",
		Hypotheses: []string{
			"x₀ ∈ M.simplices(0)",
		},
		Conclusion: "simplicial_homotopy_group(M, x₀, n) = {simplicial_homotopy_unit(M, x₀, n)} ⇔ " +
			"cycles(moore_complex(V, M), n) = boundaries(moore_complex(V, M), n)",
	}),
		"the unit is a class (UnitIn), so the left side says πₙ(M, x₀) has one member; the "+
			"direct image of the translation is a bijection onto it from πₙ(M, V.zero) "+
			"(BasepointTranslation), which is Hₙ of the Moore complex (HomotopyGroupMooreHomology); "+
			"Hₙ holds the boundaries themselves, the coset of V.zero, and is that one member exactly "+
			"when the cycles are the boundaries (HomologyTrivialIffExact at MooreComplexChain)"),
})}

// AcyclicHomotopyGroupsTrivial — a simplicial module acyclic over a set
// has, at every vertex, every homotopy group of positive dimension equal
// to the one class of its unit.
var AcyclicHomotopyGroupsTrivial = acyclicHomotopyGroupsTrivialThm{family.Add(registry.ProofEntry{
	Name: "AcyclicHomotopyGroupsTrivial",
	Key:  "prop_b03e36ad5832f714",
	Reading: "Only the simplicial module and the exactness of the Moore complex in " +
		"positive degrees are read; N and ε are not. n = 0 is excluded: π₀ is M(0) modulo " +
		"the Moore boundaries, which ε carries onto N, one class only when N is one point.",
	Deps: []registry.EntryLike{
		simplicial_module.AcyclicAugmentation,
		HomotopyGroupTrivialIffMooreExact,
	},
	Build: family.Card(simplicial_module.AcyclicAugmentation.Statement(Statement{
		Binders: "∀x₀:B. ∀n:num.",
		Hypotheses: []string{
			"x₀ ∈ M.simplices(0)",
			"0 < n",
		},
		Conclusion: "simplicial_homotopy_group(M, x₀, n) = {simplicial_homotopy_unit(M, x₀, n)}",
	}),
		"acyclic_augmentation carries simplicial_module and the equality of the "+
			"Moore cycles and boundaries in degree (n − 1) + 1 (AcyclicAugmentation), "+
			"which HomotopyGroupTrivialIffMooreExact reads as the conclusion"),
})}
