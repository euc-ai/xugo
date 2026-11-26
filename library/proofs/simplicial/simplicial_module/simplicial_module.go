// simplicial_module.go — simplicial modules over a ring: a simplicial
// set whose n-simplices are a submodule M(n) of one ambient module V and
// whose faces and degeneracies are linear, so that a face or a degeneracy
// carries sums to sums and keeps zero, and a degeneracy keeps a zero face
// zero on either side of its index; the alternating face complex,
// whose boundary out of dimension n is Σ_{i ≤ n} (−1)^i d_i, a chain
// complex; linear simplicial maps and homotopies, which give chain maps,
// chain homotopies and short exact sequences of face complexes; the
// constant simplicial module; the Moore complex, the simplices all of
// whose faces but the 0-th vanish, with d_0 as its differential; horns
// and spheres, which fill in a simplicial module and in an acyclic one;
// and an acyclic augmentation, the Moore complex exact in positive
// degrees and its 0-th homology carried onto a set by the augmentation,
// which a simplicial homotopy keeping zero from the identity to a
// section after the augmentation provides, and so an extra degeneracy
// keeping zero.

package simplicial_module

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/chain_complex"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_monus"
	"github.com/euc-ai/xugo/library/proofs/nat_num/peano"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/simplicial/kan_complex"
	"github.com/euc-ai/xugo/library/proofs/simplicial/simplicial_chain"
	"github.com/euc-ai/xugo/library/proofs/simplicial/simplicial_homotopy"
	"github.com/euc-ai/xugo/library/proofs/simplicial/simplicial_set"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// Simplicial modules and the face complex
// ---------------------------------------------------------------------------

// SimplicialModule — `simplicial_module(R, V, M)`: V is a module over
// the ring R, each M.simplices(n) a submodule of V, M a simplicial set, and
// every face M.d(n + 1, i) and degeneracy M.s(n, i) a homomorphism
// between the modules M(n + 1), M(n) cut out of V.
var SimplicialModule = simplicialModuleThm{family.DefineStructure(registry.DefEntry{
	Name:  "SimplicialModule",
	Key:   "prop_6fa5ea86352d3786",
	Const: "simplicial_module",
	Type:  "ring_ops(A) → module_ops(A, B) → simplicial_ops(B) → bool",
	Equations: []string{
		"∀R:ring_ops(A). ∀V:module_ops(A, B). ∀M:simplicial_ops(B). " +
			"    simplicial_module(R, V, M) ⇔ " +
			"    module_on(R, V) ∧ " +
			"    (∀n:num. submodule(R, V, M.simplices(n))) ∧ " +
			"    simplicial_set(M) ∧ " +
			"    (∀n i:num. " +
			"        i ≤ n + 1 ⇒ " +
			"        module_homomorphism(R, «degree module»(n + 1), «degree module»(n), M.d(n + 1, i))) ∧ " +
			"    (∀n i:num. " +
			"        i ≤ n ⇒ module_homomorphism(R, «degree module»(n), «degree module»(n + 1), M.s(n, i)))",
	},
	Reading: "All the M(n) are submodules of the one module V, so the terms of every " +
		"complex built from them share V's operations and only the carriers vary with n. " +
		"The faces of vertices, d(0, i), are not asked to be linear; no axiom reads them.",
})}

// AmbientModule — V is a module over R.
var AmbientModule = ambientModuleThm{family.Add(registry.ProofEntry{
	Name:  "AmbientModule",
	Key:   "prop_7e6155404cdda175",
	Build: SimplicialModule.Axiom("module_on(R, V)"),
})}

// SimplicesSubmodule — the n-simplices are a submodule of V.
var SimplicesSubmodule = simplicesSubmoduleThm{family.Add(registry.ProofEntry{
	Name:  "SimplicesSubmodule",
	Key:   "prop_afac0ed7dd5206f2",
	Build: SimplicialModule.Axiom("∀n:num. submodule(R, V, M.simplices(n))"),
})}

// ModuleSimplicialSet — a simplicial module is a simplicial set.
var ModuleSimplicialSet = moduleSimplicialSetThm{family.Add(registry.ProofEntry{
	Name:  "ModuleSimplicialSet",
	Key:   "prop_c3c3bf76666f620a",
	Build: SimplicialModule.Axiom("simplicial_set(M)"),
})}

// FaceHom — every face M.d(n + 1, i) is a homomorphism from M(n + 1) to
// M(n).
var FaceHom = faceHomThm{family.Add(registry.ProofEntry{
	Name: "FaceHom",
	Key:  "prop_1bd16db22f5645e7",
	Build: SimplicialModule.Axiom(Statement{
		Binders: "∀n i:num.",
		Hypotheses: []string{
			"i ≤ n + 1",
		},
		Conclusion: "module_homomorphism(R, «degree module»(n + 1), «degree module»(n), M.d(n + 1, i))",
	}),
})}

// DegeneracyHom — every degeneracy M.s(n, i) is a homomorphism from
// M(n) to M(n + 1).
var DegeneracyHom = degeneracyHomThm{family.Add(registry.ProofEntry{
	Name: "DegeneracyHom",
	Key:  "prop_9c72810025918afc",
	Build: SimplicialModule.Axiom(Statement{
		Binders: "∀n i:num.",
		Hypotheses: []string{
			"i ≤ n",
		},
		Conclusion: "module_homomorphism(R, «degree module»(n), «degree module»(n + 1), M.s(n, i))",
	}),
})}

// FaceBoundaryDef — `face_boundary(R, V, d, n, x)`: the alternating sum
// Σ_{i ≤ n} (−1)^i • d(n, i, x) of the faces of the n-simplex x in V,
// the sign (−1)^i being `alternating_sign(R.one, R.neg, i)`; the
// boundary out of dimension n.
var FaceBoundaryDef = faceBoundaryDefThm{family.Define(registry.DefEntry{
	Name:  "FaceBoundaryDef",
	Key:   "prop_1297f46a0b83dc47",
	Const: "face_boundary",
	Type:  "ring_ops(A) → module_ops(A, B) → (num → num → B → B) → num → B → B",
	Equations: []string{
		"∀R:ring_ops(A). ∀V:module_ops(A, B). ∀d:(num → num → B → B). ∀n:num. ∀x:B. " +
			"    face_boundary(R, V, d, n, x) = " +
			"    module_sum(V.add, " +
			"        V.zero, " +
			"        0 .. n, " +
			"        λi:num. V.smul(alternating_sign(R.one, R.neg, i), d(n, i, x)))",
	},
	Reading: "At n = 0 the sum is the one face d(0, 0, x) of a vertex, a " +
		"value no axiom reads; the complex never reads its boundary out of degree 0.",
})}

// FaceComplexDef — `face_complex(R, V, M)`: the alternating face complex
// of the simplicial module, V's operations, the terms M(n) and the face
// boundaries as the differential.
var FaceComplexDef = faceComplexDefThm{family.Define(registry.DefEntry{
	Name:  "FaceComplexDef",
	Key:   "prop_cb1ec09fbf59c979",
	Const: "face_complex",
	Type:  "ring_ops(A) → module_ops(A, B) → simplicial_ops(B) → complex_ops(A, B)",
	Equations: []string{
		"∀R:ring_ops(A). ∀V:module_ops(A, B). ∀M:simplicial_ops(B). " +
			"    face_complex(R, V, M) = " +
			"    pack_complex(V.add, V.zero, V.neg, V.smul, M.simplices, face_boundary(R, V, M.d))",
	},
	Deps: []registry.EntryLike{FaceBoundaryDef},
})}

// ---------------------------------------------------------------------------
// Linear simplicial maps and homotopies
// ---------------------------------------------------------------------------

// SimplicialModuleMap — `simplicial_module_map(R, V, M, W, N, F)`: a simplicial map between two simplicial modules over R that is a
// homomorphism of the modules M(n) → N(n) in every dimension.
var SimplicialModuleMap = simplicialModuleMapThm{family.DefineStructure(registry.DefEntry{
	Name:  "SimplicialModuleMap",
	Key:   "prop_deb906cfa7f4f6e",
	Const: "simplicial_module_map",
	Type: "ring_ops(A) → " +
		"module_ops(A, B) → " +
		"simplicial_ops(B) → " +
		"module_ops(A, C) → " +
		"simplicial_ops(C) → " +
		"(num → B → C) → " +
		"bool",
	Equations: []string{
		"∀R:ring_ops(A). " +
			"∀V:module_ops(A, B). " +
			"∀M:simplicial_ops(B). " +
			"∀W:module_ops(A, C). " +
			"∀N:simplicial_ops(C). " +
			"∀F:(num → B → C). " +
			"    simplicial_module_map(R, V, M, W, N, F) ⇔ " +
			"    simplicial_module(R, V, M) ∧ " +
			"    simplicial_module(R, W, N) ∧ " +
			"    simplicial_map(M, N, F) ∧ " +
			"    (∀n:num. " +
			"        module_homomorphism(R, «degree module»(n), restrict_module(W, N.simplices(n)), F(n)))",
	},
	Deps: []registry.EntryLike{SimplicialModule},
})}

// SimplicialModuleHomotopy — `simplicial_module_homotopy(R, V, M, W, N, F, G, H)`: a simplicial homotopy H from F to G, both linear
// simplicial maps, every component H(n, j) a homomorphism of the modules
// M(n) → N(n + 1).
var SimplicialModuleHomotopy = simplicialModuleHomotopyThm{family.DefineStructure(registry.DefEntry{
	Name:  "SimplicialModuleHomotopy",
	Key:   "prop_1d8a797ed5fef4b6",
	Const: "simplicial_module_homotopy",
	Type: "ring_ops(A) → " +
		"module_ops(A, B) → " +
		"simplicial_ops(B) → " +
		"module_ops(A, C) → " +
		"simplicial_ops(C) → " +
		"(num → B → C) → " +
		"(num → B → C) → " +
		"(num → num → B → C) → " +
		"bool",
	Equations: []string{
		"∀R:ring_ops(A). " +
			"∀V:module_ops(A, B). " +
			"∀M:simplicial_ops(B). " +
			"∀W:module_ops(A, C). " +
			"∀N:simplicial_ops(C). " +
			"∀F G:(num → B → C). " +
			"∀H:(num → num → B → C). " +
			"    simplicial_module_homotopy(R, V, M, W, N, F, G, H) ⇔ " +
			"    simplicial_module_map(R, V, M, W, N, F) ∧ " +
			"    simplicial_module_map(R, V, M, W, N, G) ∧ " +
			"    simplicial_homotopy(M, N, F, G, H) ∧ " +
			"    (∀n j:num. " +
			"        j ≤ n ⇒ " +
			"        module_homomorphism(R, " +
			"            «degree module»(n), " +
			"            restrict_module(W, N.simplices(n + 1)), " +
			"            H(n, j)))",
	},
	Deps: []registry.EntryLike{SimplicialModuleMap},
})}

// ---------------------------------------------------------------------------
// The Moore complex and acyclic augmentations
// ---------------------------------------------------------------------------

// MooreTermsDef — `moore_terms(V, M, n)`: the n-simplices whose faces
// 1, …, n vanish; at n = 0 all of M(0).
var MooreTermsDef = mooreTermsDefThm{family.Define(registry.DefEntry{
	Name:  "MooreTermsDef",
	Key:   "prop_869dbd8c74c44275",
	Const: "moore_terms",
	Type:  "module_ops(A, B) → simplicial_ops(B) → num → set(B)",
	Equations: []string{
		"∀V:module_ops(A, B). ∀M:simplicial_ops(B). ∀n:num. " +
			"    moore_terms(V, M, n) = " +
			"    {x:B | x ∈ M.simplices(n) ∧ (∀i:num. 1 ≤ i ∧ i ≤ n ⇒ M.d(n, i, x) = V.zero)}",
	},
})}

// MooreComplexDef — `moore_complex(V, M)`: the Moore complex, V's
// operations, the terms moore_terms(V, M, n) and the 0-th face as the
// differential. Its cycles and boundaries are chain_complex's `cycles`
// and `boundaries` of this record: `boundaries(moore_complex(V, M), n)`
// is the image of M.d(n + 1, 0) on moore_terms(V, M, n + 1).
var MooreComplexDef = mooreComplexDefThm{family.Define(registry.DefEntry{
	Name:  "MooreComplexDef",
	Key:   "prop_691f0bdf938856fe",
	Const: "moore_complex",
	Type:  "module_ops(A, B) → simplicial_ops(B) → complex_ops(A, B)",
	Equations: []string{
		"∀V:module_ops(A, B). ∀M:simplicial_ops(B). " +
			"    moore_complex(V, M) = " +
			"    pack_complex(V.add, V.zero, V.neg, V.smul, moore_terms(V, M), λn:num. M.d(n, 0))",
	},
	Deps: []registry.EntryLike{MooreTermsDef},
})}

// AcyclicAugmentation — `acyclic_augmentation(R, V, M, N, ε)`: the
// simplicial module M is acyclic over N through ε — its Moore
// complex has cycles equal to boundaries in every positive degree, ε
// carries M(0) onto N, and two vertices have one image under ε exactly
// when their difference is a Moore boundary, so that ε reads
// M(0) / d_0(moore_terms(1)) onto N.
var AcyclicAugmentation = acyclicAugmentationThm{family.DefineStructure(registry.DefEntry{
	Name:  "AcyclicAugmentation",
	Key:   "prop_70e22503727b4788",
	Const: "acyclic_augmentation",
	Type:  "ring_ops(A) → module_ops(A, B) → simplicial_ops(B) → set(C) → (B → C) → bool",
	Equations: []string{
		"∀R:ring_ops(A). ∀V:module_ops(A, B). ∀M:simplicial_ops(B). ∀N:set(C). ∀ε:(B → C). " +
			"    acyclic_augmentation(R, V, M, N, ε) ⇔ " +
			"    simplicial_module(R, V, M) ∧ " +
			"    (∀n:num. cycles(moore_complex(V, M), n + 1) = boundaries(moore_complex(V, M), n + 1)) ∧ " +
			"    image(ε, M.simplices(0)) = N ∧ " +
			"    (∀x y:B. " +
			"        x ∈ M.simplices(0) ∧ y ∈ M.simplices(0) ⇒ " +
			"        (ε(x) = ε(y) ⇔ x + -y ∈ boundaries(moore_complex(V, M), 0)))",
	},
	Reading: "ε is a map of sets here: linearity, where a resolution needs it, is the " +
		"augmentation's own hypothesis. The degree-0 conjunct says the fibres of ε are the cosets " +
		"of d_0(moore_terms(1)), so the Moore complex is a resolution of N once ε is linear.",
	Deps: []registry.EntryLike{SimplicialModule, MooreComplexDef},
})}

// ---------------------------------------------------------------------------
// The faces and degeneracies are linear
// ---------------------------------------------------------------------------

// FaceAdd — a face of a sum of (n+1)-simplices is the sum of their faces:
// the face is linear on M(n + 1).
var FaceAdd = faceAddThm{family.Add(registry.ProofEntry{
	Name: "FaceAdd",
	Key:  "prop_14cd797bad8895a1",
	Build: SimplicialModule.Law(Statement{
		Binders: "∀n i:num. ∀x y:B.",
		Hypotheses: []string{
			"x ∈ M.simplices(n + 1)",
			"y ∈ M.simplices(n + 1)",
			"i ≤ n + 1",
		},
		Conclusion: "M.d(n + 1, i, x + y) = M.d(n + 1, i, x) + M.d(n + 1, i, y)",
	},
		func(a *Argument, h Fact, n, i *Expr[Nat], x, y *Expr[B], xIn, yIn, bound Fact) {
			linear := a.Simplified(GroupPremises(bound, FaceHom.Read(h).At(n, i)))
			a.Show(
				"so it carries the sum to the sum of the faces",
				ByChase(Depth(0), linear, xIn, yIn))
		}),
})}

// FaceSub — a face of a difference of (n+1)-simplices is the difference
// of their faces: the face is linear on M(n + 1).
var FaceSub = faceSubThm{family.Add(registry.ProofEntry{
	Name: "FaceSub",
	Key:  "prop_93ee61112e102fda",
	Build: SimplicialModule.Law(Statement{
		Binders: "∀n i:num. ∀x y:B.",
		Hypotheses: []string{
			"x ∈ M.simplices(n + 1)",
			"y ∈ M.simplices(n + 1)",
			"i ≤ n + 1",
		},
		Conclusion: "M.d(n + 1, i, x + -y) = M.d(n + 1, i, x) + -M.d(n + 1, i, y)",
	},
		func(a *Argument, h Fact, n, i *Expr[Nat], x, y *Expr[B], xIn, yIn, bound Fact) {
			linear := a.Simplified(GroupPremises(bound, FaceHom.Read(h).At(n, i)))
			a.Show(
				"so it carries the difference to the difference of the faces",
				ByChase(Depth(0), linear, xIn, yIn))
		}),
})}

// FaceZero — a face keeps zero: it is linear on M(n + 1), whose zero is
// V's.
var FaceZero = faceZeroThm{family.Add(registry.ProofEntry{
	Name: "FaceZero",
	Key:  "prop_8ac4e006ba4dfe14",
	Build: SimplicialModule.Law(Statement{
		Binders: "∀n i:num.",
		Hypotheses: []string{
			"i ≤ n + 1",
		},
		Conclusion: "M.d(n + 1, i, V.zero) = V.zero",
	},
		func(a *Argument, h Fact, n, i *Expr[Nat], bound Fact) {
			linear := a.Simplified(GroupPremises(bound, FaceHom.Read(h).At(n, i)))
			a.Show(
				"so it keeps zero",
				By(module_homomorphism.HomZero.Read(linear)))
		}),
})}

// DegeneracyAdd — a degeneracy of a sum of n-simplices is the sum of their
// degeneracies: the degeneracy is linear on M(n).
var DegeneracyAdd = degeneracyAddThm{family.Add(registry.ProofEntry{
	Name: "DegeneracyAdd",
	Key:  "prop_63e3e80f2485ef67",
	Build: SimplicialModule.Law(Statement{
		Binders: "∀n i:num. ∀x y:B.",
		Hypotheses: []string{
			"x ∈ M.simplices(n)",
			"y ∈ M.simplices(n)",
			"i ≤ n",
		},
		Conclusion: "M.s(n, i, x + y) = M.s(n, i, x) + M.s(n, i, y)",
	},
		func(a *Argument, h Fact, n, i *Expr[Nat], x, y *Expr[B], xIn, yIn, bound Fact) {
			linear := a.Simplified(GroupPremises(bound, DegeneracyHom.Read(h).At(n, i)))
			a.Show(
				"so it carries the sum to the sum of the degeneracies",
				ByChase(Depth(0), linear, xIn, yIn))
		}),
})}

// DegeneracyZero — a degeneracy keeps zero: it is linear on M(n), whose
// zero is V's.
var DegeneracyZero = degeneracyZeroThm{family.Add(registry.ProofEntry{
	Name: "DegeneracyZero",
	Key:  "prop_e17938290f7179dd",
	Build: SimplicialModule.Law(Statement{
		Binders: "∀n i:num.",
		Hypotheses: []string{
			"i ≤ n",
		},
		Conclusion: "M.s(n, i, V.zero) = V.zero",
	},
		func(a *Argument, h Fact, n, i *Expr[Nat], bound Fact) {
			linear := a.Simplified(GroupPremises(bound, DegeneracyHom.Read(h).At(n, i)))
			a.Show(
				"so it keeps zero",
				By(module_homomorphism.HomZero.Read(linear)))
		}),
})}

// FaceDegeneracyBelowZero — a degeneracy s_j above a zero face i keeps
// face i zero: d_i s_j = s_{j−1} d_i, a degeneracy of zero.
var FaceDegeneracyBelowZero = faceDegeneracyBelowZeroThm{family.Add(registry.ProofEntry{
	Name: "FaceDegeneracyBelowZero",
	Key:  "prop_552a5214d1398afd",
	Build: SimplicialModule.Law(Statement{
		Binders: "∀n i j:num. ∀z:B.",
		Hypotheses: []string{
			"z ∈ M.simplices(n + 1)",
			"i < j",
			"j ≤ n + 1",
			"M.d(n + 1, i, z) = V.zero",
		},
		Conclusion: "M.d(n + 2, i, M.s(n + 1, j, z)) = V.zero",
	},
		func(a *Argument, h Fact, n, i, j *Expr[Nat], z *Expr[B], zIn, below, bound, zero Fact) {
			simplicial := ModuleSimplicialSet.Read(h)
			lower := a.Have(
				"the lower degeneracy s_{j−1} is defined",
				"j - 1 ≤ n",
				ByArith(below, bound))
			a.Show(
				"d_i s_j = s_{j−1} d_i carries the zero face to a degeneracy of zero",
				By(
					zIn,
					below,
					bound,
					zero,
					lower,
					simplicial_set.FaceDegeneracyBelow.Read(simplicial).At(n, i, j, z),
					DegeneracyZero.Read(h).At(n, a.TermAs[Nat]("j - 1"))))
		}),
})}

// FaceDegeneracyAboveZero — a degeneracy s_j below a zero face i − 1
// carries it to a zero face i: d_i s_j = s_j d_{i−1}, a degeneracy of
// zero.
var FaceDegeneracyAboveZero = faceDegeneracyAboveZeroThm{family.Add(registry.ProofEntry{
	Name: "FaceDegeneracyAboveZero",
	Key:  "prop_2401f79a1e1b1dd3",
	Build: SimplicialModule.Law(Statement{
		Binders: "∀n i j:num. ∀z:B.",
		Hypotheses: []string{
			"z ∈ M.simplices(n + 1)",
			"j + 1 < i",
			"i ≤ n + 2",
			"M.d(n + 1, i - 1, z) = V.zero",
		},
		Conclusion: "M.d(n + 2, i, M.s(n + 1, j, z)) = V.zero",
	},
		func(a *Argument, h Fact, n, i, j *Expr[Nat], z *Expr[B], zIn, above, bound, zero Fact) {
			simplicial := ModuleSimplicialSet.Read(h)
			top := a.Have(
				"the degeneracy s_j is below the top",
				"j ≤ n",
				ByArith(above, bound))
			a.Show(
				"d_i s_j = s_j d_{i−1} carries the zero face to a degeneracy of zero",
				By(
					zIn,
					above,
					bound,
					zero,
					top,
					simplicial_set.FaceDegeneracyAbove.Read(simplicial).At(n, i, j, z),
					DegeneracyZero.Read(h).At(n, j)))
		}),
})}

// SimplicesModule — every M(n), under V's operations, is a module: a
// submodule of the module V.
var SimplicesModule = simplicesModuleThm{family.Add(registry.ProofEntry{
	Name: "SimplicesModule",
	Key:  "prop_4d8b39cfb4eb319c",
	Build: SimplicialModule.Law("∀n:num. module_on(R, «degree module»(n))",
		func(a *Argument, simplicial SimplicialModuleFact[on.R, on.V], n *Expr[Nat]) {
			a.Show(
				"a submodule of a module is a module",
				By(
					submodule.SubmoduleModuleOn.Read(AmbientModule.Read(simplicial)),
					SimplicesSubmodule.Read(simplicial).At(n)))
		}),
})}

// FaceIterateBottomHom — removing k ≤ n bottom vertices is linear, from
// M(n) to M(n − k): by induction on k, the next 0-th face, linear by
// FaceHom, composes with the iterate before it.
var FaceIterateBottomHom = faceIterateBottomHomThm{family.Add(registry.ProofEntry{
	Name: "FaceIterateBottomHom",
	Key:  "prop_1c41776b50dc2226",
	Build: SimplicialModule.Law(Statement{
		Binders: "∀n k:num.",
		Hypotheses: []string{
			"k ≤ n",
		},
		Conclusion: "module_homomorphism(R, " +
			"    «degree module»(n), " +
			"    «degree module»(n - k), " +
			"    λx:B. face_iterate_bottom(n, k, x))",
	},
		func(a *Argument, simplicial SimplicialModuleFact[on.R, on.V], n *Expr[Nat]) {
			R := a.TermAs[RingOps[A]]("R")
			a.Induct("k")
			a.Base(
				"removing no bottom vertex is the identity",
				func(b *Argument) {
					b.Assume()
					b.Do(Simp(Fwd(nat_monus.Sub), Fwd(simplicial_set.FaceIterateBottomDef)))
					b.Show(
						"the identity is linear",
						By(
							SimplicesModule.Read(simplicial).At(n),
							module_homomorphism.HomIdentity.At(R, b.TermAs[ModuleOps[A, B]]("«degree module»(n)")),
							functions.IdentityApply))
				})
			a.Step(
				"one more 0-th face composes two linear maps",
				func(b *Argument, ih Fact) {
					bound := b.Assume()
					dimensions := b.Have(
						"the previous iterate and the next face have matching degrees",
						"k ≤ n ∧ n - k = n - suc(k) + 1",
						ByArith(bound))
					previous := b.Have(
						"removing k bottom vertices is linear",
						"module_homomorphism(R, "+
							"    «degree module»(n), "+
							"    «degree module»(n - k), "+
							"    λx:B. face_iterate_bottom(n, k, x))",
						By(ih, dimensions))
					nextFace := b.Have(
						"the next 0-th face is linear",
						"module_homomorphism(R, "+
							"    «degree module»(n - suc(k) + 1), "+
							"    «degree module»(n - suc(k)), "+
							"    M.d(n - suc(k) + 1, 0))",
						ByArith(FaceHom.Read(simplicial).At(b.TermAs[Nat]("n - suc(k)"), b.TermAs[Nat]("0"))))
					b.Show(
						"the recursion is their composite",
						Simp(Fwd(dimensions), Fwd(simplicial_set.FaceIterateBottomDef)),
						By(
							dimensions,
							previous,
							nextFace,
							module_homomorphism.HomCompose.At(
								R,
								b.TermAs[ModuleOps[A, B]]("«degree module»(n)"),
								b.TermAs[ModuleOps[A, B]]("«degree module»(n - k)"),
								b.TermAs[ModuleOps[A, B]]("«degree module»(n - suc(k))"),
								b.TermAs[Fun[B, B]]("λx:B. face_iterate_bottom(n, k, x)"),
								b.TermAs[Fun[B, B]]("M.d(n - suc(k) + 1, 0)")),
							functions.ComposeApply))
				})
		}),
})}

// FaceIterateTopHom — removing k ≤ n top vertices is linear, from M(n)
// to M(n − k): by induction on k, the next last face, linear by
// FaceHom, composes with the iterate before it.
var FaceIterateTopHom = faceIterateTopHomThm{family.Add(registry.ProofEntry{
	Name: "FaceIterateTopHom",
	Key:  "prop_7a5c4fb131721b8a",
	Build: SimplicialModule.Law(Statement{
		Binders: "∀n k:num.",
		Hypotheses: []string{
			"k ≤ n",
		},
		Conclusion: "module_homomorphism(R, " +
			"    «degree module»(n), " +
			"    «degree module»(n - k), " +
			"    λx:B. face_iterate_top(n, k, x))",
	},
		func(a *Argument, simplicial SimplicialModuleFact[on.R, on.V], n *Expr[Nat]) {
			R := a.TermAs[RingOps[A]]("R")
			a.Induct("k")
			a.Base(
				"removing no top vertex is the identity",
				func(b *Argument) {
					b.Assume()
					b.Do(Simp(Fwd(nat_monus.Sub), Fwd(simplicial_set.FaceIterateTopDef)))
					b.Show(
						"the identity is linear",
						By(
							SimplicesModule.Read(simplicial).At(n),
							module_homomorphism.HomIdentity.At(R, b.TermAs[ModuleOps[A, B]]("«degree module»(n)")),
							functions.IdentityApply))
				})
			a.Step(
				"one more last face composes two linear maps",
				func(b *Argument, ih Fact) {
					bound := b.Assume()
					dimensions := b.Have(
						"the previous iterate and the next face have matching degrees",
						"k ≤ n ∧ n - k = n - suc(k) + 1",
						ByArith(bound))
					previous := b.Have(
						"removing k top vertices is linear",
						"module_homomorphism(R, "+
							"    «degree module»(n), "+
							"    «degree module»(n - k), "+
							"    λx:B. face_iterate_top(n, k, x))",
						By(ih, dimensions))
					nextFace := b.Have(
						"the next last face is linear",
						"module_homomorphism(R, "+
							"    «degree module»(n - suc(k) + 1), "+
							"    «degree module»(n - suc(k)), "+
							"    M.d(n - suc(k) + 1, n - suc(k) + 1))",
						ByArith(FaceHom.Read(simplicial).At(b.TermAs[Nat]("n - suc(k)"), b.TermAs[Nat]("n - suc(k) + 1"))))
					b.Show(
						"the recursion is their composite",
						Simp(Fwd(dimensions), Fwd(simplicial_set.FaceIterateTopDef)),
						By(
							dimensions,
							previous,
							nextFace,
							module_homomorphism.HomCompose.At(
								R,
								b.TermAs[ModuleOps[A, B]]("«degree module»(n)"),
								b.TermAs[ModuleOps[A, B]]("«degree module»(n - k)"),
								b.TermAs[ModuleOps[A, B]]("«degree module»(n - suc(k))"),
								b.TermAs[Fun[B, B]]("λx:B. face_iterate_top(n, k, x)"),
								b.TermAs[Fun[B, B]]("M.d(n - suc(k) + 1, n - suc(k) + 1)")),
							functions.ComposeApply))
				})
		}),
})}

// ---------------------------------------------------------------------------
// The face complex is a chain complex
// ---------------------------------------------------------------------------

// FaceComplexModule — the face complex's module in degree n is M(n) under
// V's operations: the complex packs V's operations with the terms
// M.simplices.
var FaceComplexModule = faceComplexModuleThm{family.Add(registry.ProofEntry{
	Name: "FaceComplexModule",
	Key:  "prop_dc443fc92d569817",
	Build: family.Theorem("∀R:ring_ops(A). ∀V:module_ops(A, B). ∀M:simplicial_ops(B). ∀n:num. "+
		"    complex_module(face_complex(R, V, M), n) = «degree module»(n)",
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			V *Expr[ModuleOps[A, B]],
			M *Expr[SimplicialOps[B]],
			n *Expr[Nat],
		) {
			a.Show(
				"both sides restrict V's operations to M.simplices(n)",
				Simp(
					Fwd(chain_complex.ComplexModuleDef),
					Fwd(FaceComplexDef),
					Fwd(chain_complex.ComplexAddDef),
					Fwd(chain_complex.ComplexZeroDef),
					Fwd(chain_complex.ComplexNegDef),
					Fwd(chain_complex.ComplexSmulDef),
					Fwd(chain_complex.ComplexTermsDef),
					Fwd(module_record.RestrictModuleDef)),
				Basic())
		}),
})}

// FaceBoundaryHom — the boundary out of dimension n + 1 is a homomorphism
// from M(n + 1) to M(n).
var FaceBoundaryHom = faceBoundaryHomThm{family.Add(registry.ProofEntry{
	Name: "FaceBoundaryHom",
	Key:  "prop_1f95a7caf748e735",
	Deps: []registry.EntryLike{
		SimplicialModule,
		FaceHom,
		AmbientModule,
		FaceBoundaryDef,
		comm_ring.AlternatingSignIn,
		module.RingOn,
		module_homomorphism.HomAdd,
		module_homomorphism.HomSmul,
		module_homomorphism.HomSum,
		module.ModuleSumIn,
		submodule.SubmoduleModuleOn,
	},
	Build: family.Card(
		SimplicialModule.Statement(
			"∀n:num. "+
				"    module_homomorphism(R, "+
				"        «degree module»(n + 1), "+
				"        «degree module»(n), "+
				"        face_boundary(R, V, M.d, n + 1))"),
		"each face d(n + 1, i) is a homomorphism of the restricted modules (FaceHom) and each sign "+
			"lies in R's carrier (AlternatingSignIn at the ring AmbientModule carries, RingOn); a finite "+
			"sum of scaled homomorphisms into the submodule M(n) is one (ModuleSumIn, HomAdd, HomSmul)"),
})}

// AlternatingDoubleSumCancel — in any module, the double alternating sum
// Σ_j Σ_i (−1)^{j+i} d_i d_j x over the faces of the faces of x vanishes
// once d_i d_j = d_{j−1} d_i for i < j.
var AlternatingDoubleSumCancel = alternatingDoubleSumCancelThm{family.Add(registry.ProofEntry{
	Name: "AlternatingDoubleSumCancel",
	Key:  "prop_4e8d728544d9f403",
	Reading: "Only the face–face identity for i < j and the membership of the " +
		"iterated faces in M's carrier are read, no simplicial set; the " +
		"commutativity of R, which module_on asks, makes the paired signs opposite.",
	Deps: []registry.EntryLike{
		module.ModuleOn,
		comm_ring.AlternatingSignDef,
		comm_ring.AlternatingSignIn,
		simplicial_chain.FaceSumCancel,
		module.ModuleSumDisjointUnion,
		module.ModuleSumImage,
		module.ModuleSumCross,
		module.ModuleSumNeg,
		module.SmulNeg,
	},
	Build: family.Card(module.ModuleOn.Statement(Statement{
		Binders: "∀d:(num → num → B → B). ∀n:num. ∀x:B.",
		Hypotheses: []string{
			"∀i j:num. i ≤ n + 1 ∧ j ≤ n + 2 ⇒ d(n + 1, i, d(n + 2, j, x)) ∈ M.carrier",
			"∀i j:num. i < j ∧ j ≤ n + 2 ⇒ d(n + 1, i, d(n + 2, j, x)) = d(n + 1, j - 1, d(n + 2, i, x))",
		},
		Conclusion: "module_sum(M.add, " +
			"    M.zero, " +
			"    0 .. n + 2, " +
			"    λj:num. " +
			"        module_sum(M.add, " +
			"            M.zero, " +
			"            0 .. n + 1, " +
			"            λi:num. " +
			"                M.smul(R.mul(alternating_sign(j), alternating_sign(i)), " +
			"                    d(n + 1, i, d(n + 2, j, x))))) = " +
			"M.zero",
	}),
		"FaceSumCancel's argument in any module: the double sum is the sum over pairs (ModuleSumCross); "+
			"the pairs with j ≤ i go one-to-one onto those with i < j by (j, i) ↦ (i + 1, j), where the "+
			"face identity makes the two vectors one and the signs are opposite (AlternatingSignDef), so "+
			"the sum over the second half is the negative of the sum over the first (ModuleSumImage, "+
			"SmulNeg, ModuleSumNeg) and the two halves cancel (ModuleSumDisjointUnion)"),
})}

// FaceComplexChain — the alternating face complex of a simplicial module
// is a chain complex.
var FaceComplexChain = faceComplexChainThm{family.Add(registry.ProofEntry{
	Name: "FaceComplexChain",
	Key:  "prop_48f0d2a71647fef6",
	Reading: "Only the face–face identities and the linearity of each d(n + 1, " +
		"i) are read: the degeneracies and the faces of the vertices play no role.",
	Deps: []registry.EntryLike{
		SimplicialModule,
		FaceComplexDef,
		FaceBoundaryDef,
		FaceBoundaryHom,
		AlternatingDoubleSumCancel,
		chain_complex.ChainComplex,
		chain_complex.ComplexModuleDef,
		submodule.SubmoduleModuleOn,
		simplicial_set.FaceFace,
		simplicial_set.FaceIn,
		module_homomorphism.HomSum,
		module_homomorphism.HomSmul,
	},
	Build: family.Card(SimplicialModule.Statement("chain_complex(R, face_complex(R, V, M))"),
		"the n-th term is the submodule M(n) under V's operations (SubmoduleModuleOn), "+
			"the boundary out of n + 1 is linear (FaceBoundaryHom), and the boundary of a "+
			"boundary is, by the linearity of each face (HomSum, HomSmul), the double "+
			"alternating sum of AlternatingDoubleSumCancel, the face identity being FaceFace"),
})}

// ConstantSimplicialModule — a submodule K of V is a simplicial module in
// every dimension, every face and degeneracy the identity.
var ConstantSimplicialModule = constantSimplicialModuleThm{family.Add(registry.ProofEntry{
	Name: "ConstantSimplicialModule",
	Key:  "prop_41689f7ca0a463a2",
	Deps: []registry.EntryLike{
		SimplicialModule,
		simplicial_set.ConstantSimplicialSet,
		module_homomorphism.HomIdentity,
		submodule.SubmoduleModuleOn,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀V:module_ops(A, B). ∀K:set(B).",
		Hypotheses: []string{
			"module_on(R, V)",
			"submodule(R, V, K)",
		},
		Conclusion: "simplicial_module(R, V, constant_simplicial_set(K))",
	},
		"the constant simplicial set on K (ConstantSimplicialSet), and the identity of "+
			"the module K cut out of V is a homomorphism (HomIdentity at SubmoduleModuleOn)"),
})}

// ConstantFaceComplexHomology — the face complex of a constant simplicial
// module has no boundaries in degree 0 and is exact above it: its
// homology is K in degree 0 and zero in every positive degree.
var ConstantFaceComplexHomology = constantFaceComplexHomologyThm{family.Add(registry.ProofEntry{
	Name: "ConstantFaceComplexHomology",
	Key:  "prop_5d7f195e3cdf4637",
	Reading: "The cycles in degree 0 are all of K, so the first conjunct says H_0 " +
		"is K itself; the boundary out of m is the identity for m even and zero for m " +
		"odd, so above degree 0 the cycles and the boundaries are both K or both {0}.",
	Deps: []registry.EntryLike{
		ConstantSimplicialModule,
		FaceComplexDef,
		FaceBoundaryDef,
		comm_ring.AlternatingSignDef,
		chain_complex.CyclesDef,
		chain_complex.BoundariesDef,
		module.ModuleSumInsert,
		module.ModuleSumEmpty,
		module.SmulAddLeft,
		module.SmulOne,
		module.ZeroSmul,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀V:module_ops(A, B). ∀K:set(B).",
		Hypotheses: []string{
			"module_on(R, V)",
			"submodule(R, V, K)",
		},
		Conclusion: "boundaries(face_complex(R, V, constant_simplicial_set(K)), 0) = {V.zero} ∧ " +
			"(∀n:num. " +
			"    cycles(face_complex(R, V, constant_simplicial_set(K)), n + 1) = " +
			"    boundaries(face_complex(R, V, constant_simplicial_set(K)), n + 1))",
	},
		"every face is the identity, so the boundary out of m is (Σ_{i ≤ m} (−1)^i) • x, by "+
			"induction on m x for m even and 0 for m odd (AlternatingSignDef, SmulAddLeft, ZeroSmul); "+
			"the boundary out of 1 is zero, giving {V.zero} in degree 0 (K holds V.zero), and in degree "+
			"n + 1 the cycles and the boundaries are K when n + 1 is odd and {V.zero} when it is even"),
})}

// ConstantAcyclicAugmentation — a constant simplicial module is acyclic
// over K through the identity.
var ConstantAcyclicAugmentation = constantAcyclicAugmentationThm{family.Add(registry.ProofEntry{
	Name: "ConstantAcyclicAugmentation",
	Key:  "prop_aa9e276e778e5066",
	Deps: []registry.EntryLike{
		AcyclicAugmentation,
		ConstantSimplicialModule,
		MooreComplexDef,
		MooreTermsDef,
		chain_complex.CyclesDef,
		chain_complex.BoundariesDef,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀V:module_ops(A, B). ∀K:set(B).",
		Hypotheses: []string{
			"module_on(R, V)",
			"submodule(R, V, K)",
		},
		Conclusion: "acyclic_augmentation(R, V, constant_simplicial_set(K), K, λx:B. x)",
	},
		"every face is the identity, so the Moore terms are K in degree 0 and {V.zero} "+
			"above it; the Moore cycles and boundaries in positive degrees are both {V.zero}, "+
			"the identity carries K onto K, and the one Moore boundary in degree 0 is V.zero, "+
			"so two vertices have one image exactly when their difference is V.zero"),
})}

// ---------------------------------------------------------------------------
// Linear simplicial maps and homotopies give chain maps and homotopies
// ---------------------------------------------------------------------------

// SimplicialModuleMapChainMap — a linear simplicial map is a chain map of
// the face complexes.
var SimplicialModuleMapChainMap = simplicialModuleMapChainMapThm{family.Add(registry.ProofEntry{
	Name: "SimplicialModuleMapChainMap",
	Key:  "prop_cea808a9aa78ad17",
	Deps: []registry.EntryLike{
		SimplicialModuleMap,
		FaceComplexDef,
		FaceBoundaryDef,
		chain_complex.ChainMapDef,
		chain_complex.ComplexModuleDef,
		simplicial_set.MapFace,
		module_homomorphism.HomSum,
		module_homomorphism.HomSmul,
	},
	Build: family.Card(
		SimplicialModuleMap.Statement("chain_map(R, face_complex(R, V, M), face_complex(R, W, N), F)"),
		"F(n) is a homomorphism of the terms; it commutes with each face "+
			"(MapFace) and is linear, so it carries the alternating sum of the "+
			"faces to the alternating sum of their images (HomSum, HomSmul)"),
})}

// SimplicialModuleHomotopyChainHomotopy — a linear simplicial homotopy H
// from F to G gives the chain homotopy Σ_{j ≤ n} (−1)^j H(n, j) between
// the chain maps F and G of the face complexes.
var SimplicialModuleHomotopyChainHomotopy = simplicialModuleHomotopyChainHomotopyThm{family.Add(registry.ProofEntry{
	Name: "SimplicialModuleHomotopyChainHomotopy",
	Key:  "prop_cce2ec8a135858de",
	Reading: "Only the face identities of H are read; its " +
		"degeneracy identities play no role in the chain homotopy.",
	Deps: []registry.EntryLike{
		SimplicialModuleHomotopy,
		simplicial_homotopy.SimplicialHomotopy,
		FaceComplexDef,
		FaceBoundaryDef,
		chain_complex.ChainHomotopyDef,
		chain_complex.ComplexModuleDef,
		module_homomorphism.HomSum,
		module_homomorphism.HomSmul,
		module.ModuleSumCross,
		module.ModuleSumDisjointUnion,
		module.ModuleSumImage,
		comm_ring.AlternatingSignDef,
	},
	Build: family.Card(
		SimplicialModuleHomotopy.Statement(
			"chain_homotopy(R, "+
				"    face_complex(R, V, M), "+
				"    face_complex(R, W, N), "+
				"    F, "+
				"    G, "+
				"    λn:num. λx:B. "+
				"        module_sum(W.add, W.zero, 0 .. n, λj:num. W.smul(alternating_sign(j), H(n, j, x))))"),
		"the homotopy is linear (HomSum, HomSmul). In ∂h + h∂ on M(n + 1) the terms d_i h_j "+
			"with i = j and i = j + 1 telescope through d_{j+1} h_{j+1} = d_{j+1} h_j to d_0 h_0 − "+
			"d_{n+2} h_{n+1} = F − G, and those with i < j and with i > j + 1 cancel the terms of "+
			"h∂ by d_i h_j = h_{j−1} d_i and d_i h_j = h_j d_{i−1}, the signs opposite; in degree "+
			"0, d_0 h_0 − d_1 h_0 = F − G (May, Simplicial Objects in Algebraic Topology, §5)"),
})}

// SimplicialModuleHomotopyEquivalenceChain — linear simplicial maps F and
// G whose composites are joined to the identities by linear simplicial
// homotopies are a chain homotopy equivalence of the face complexes.
var SimplicialModuleHomotopyEquivalenceChain = simplicialModuleHomotopyEquivalenceChainThm{family.Add(registry.ProofEntry{
	Name: "SimplicialModuleHomotopyEquivalenceChain",
	Key:  "prop_283cd60af54699a0",
	Reading: "The homotopies run from the identities to the composites; " +
		"chain_homotopy_equivalence asks for chain homotopies from the composites to the " +
		"identities, the negatives of the ones the homotopies give, chain homotopy being symmetric.",
	Deps: []registry.EntryLike{
		chain_complex.ChainHomotopyEquivalenceDef,
		SimplicialModuleMapChainMap,
		SimplicialModuleHomotopyChainHomotopy,
		chain_complex.ChainHomotopyDef,
		module_homomorphism.HomNeg,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀V:module_ops(A, B). " +
			"∀M:simplicial_ops(B). " +
			"∀W:module_ops(A, C). " +
			"∀N:simplicial_ops(C). " +
			"∀F:(num → B → C). " +
			"∀G:(num → C → B). " +
			"∀H:(num → num → B → B). " +
			"∀K:(num → num → C → C).",
		Hypotheses: []string{
			"simplicial_module_map(R, V, M, W, N, F)",
			"simplicial_module_map(R, W, N, V, M, G)",
			"simplicial_module_homotopy(R, V, M, V, M, λn:num. λx:B. x, λn:num. λx:B. G(n, F(n, x)), H)",
			"simplicial_module_homotopy(R, W, N, W, N, λn:num. λy:C. y, λn:num. λy:C. F(n, G(n, y)), K)",
		},
		Conclusion: "chain_homotopy_equivalence(R, face_complex(R, V, M), face_complex(R, W, N), F, G)",
	},
		"unfold ChainHomotopyEquivalenceDef: F and G are chain maps by SimplicialModuleMapChainMap, "+
			"and SimplicialModuleHomotopyChainHomotopy turns H and K into chain homotopies from the "+
			"identities to the composites, whose negatives run the other way (HomNeg)"),
})}

// DegreewiseShortExactComplexes — linear simplicial maps that are short
// exact in every dimension give a short exact sequence of the face
// complexes.
var DegreewiseShortExactComplexes = degreewiseShortExactComplexesThm{family.Add(registry.ProofEntry{
	Name: "DegreewiseShortExactComplexes",
	Key:  "prop_391c57b708ceeee2",
	Deps: []registry.EntryLike{
		FaceComplexChain,
		SimplicialModuleMapChainMap,
		chain_complex.ShortExactComplexes,
		chain_complex.ExactComplexesDef,
		module_homomorphism.ShortExactModules,
		FaceComplexDef,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀V':module_ops(A, B). " +
			"∀M':simplicial_ops(B). " +
			"∀V:module_ops(A, C). " +
			"∀M:simplicial_ops(C). " +
			"∀V'':module_ops(A, D). " +
			"∀M'':simplicial_ops(D). " +
			"∀i:(num → B → C). " +
			"∀p:(num → C → D).",
		Hypotheses: []string{
			"simplicial_module_map(R, V', M', V, M, i)",
			"simplicial_module_map(R, V, M, V'', M'', p)",
			"∀n:num. " +
				"    short_exact_modules(R, " +
				"        restrict_module(V', M'.simplices(n)), " +
				"        restrict_module(V, M.simplices(n)), " +
				"        restrict_module(V'', M''.simplices(n)), " +
				"        i(n), " +
				"        p(n))",
		},
		Conclusion: "short_exact_complexes(R, " +
			"    face_complex(R, V', M'), " +
			"    face_complex(R, V, M), " +
			"    face_complex(R, V'', M''), " +
			"    i, " +
			"    p)",
	},
		"the three face complexes are chain complexes (FaceComplexChain) and i, p chain "+
			"maps (SimplicialModuleMapChainMap); the terms of a face complex are the modules "+
			"M(n) cut out of the ambient one, so the injectivity, exactness and surjectivity "+
			"of exact_complexes are those of short_exact_modules in each dimension"),
})}

// ---------------------------------------------------------------------------
// The Moore complex, horns and spheres
// ---------------------------------------------------------------------------

// MooreSubcomplex — the 0-th face carries moore_terms(n + 1) into
// moore_terms(n), and two 0-th faces in a row vanish on the Moore terms:
// the face identity d_i d_0 = d_0 d_{i+1} moves the 0-th face outside a
// face of x that vanishes, and a face keeps zero.
var MooreSubcomplex = mooreSubcomplexThm{family.Add(registry.ProofEntry{
	Name: "MooreSubcomplex",
	Key:  "prop_290270218b71d225",
	Reading: "d_1 x = V.zero is read only in the second conjunct, at d_0 d_0 x = " +
		"d_0 d_1 x = V.zero; the first reads the vanishing of the faces 2, …, n + 1.",
	Build: SimplicialModule.Law(
		"(∀n:num. ∀x:B. x ∈ moore_terms(V, M, n + 1) ⇒ M.d(n + 1, 0, x) ∈ moore_terms(V, M, n)) ∧ "+
			"(∀n:num. ∀x:B. x ∈ moore_terms(V, M, n + 2) ⇒ M.d(n + 1, 0, M.d(n + 2, 0, x)) = V.zero)",
		func(a *Argument, h SimplicialModuleFact[on.R, on.V]) {
			simplicial := ModuleSimplicialSet.Read(h)
			zero := a.TermAs[Nat]("0")
			a.Do(SplitConj(
				Case(
					"the 0-th face carries a Moore term of degree n + 1 into degree n",
					Derive(func(b *Argument) {
						n := b.FixAs[Nat]("n")
						x := b.FixAs[B]("x")
						moore := b.Conjuncts(
							b.Unfolded(b.Assume(), MooreTermsDef),
							"x is an (n + 1)-simplex",
							"whose faces 1, …, n + 1 vanish")
						simplex, faces := moore[0], moore[1]
						vanish := b.Have(
							"the faces 1, …, n of d_0 x vanish",
							"∀i:num. 1 ≤ i ∧ i ≤ n ⇒ M.d(n, i, M.d(n + 1, 0, x)) = V.zero",
							Derive(func(c *Argument) {
								c.FixAs[Nat]("i")
								bounds := c.Assume()
								below := c.TermAs[Nat]("n - 1")
								above := c.TermAs[Nat]("i + 1")
								c.Show(
									"d_i d_0 x = d_0 d_{i+1} x = d_0 0 = 0",
									CalcEq(
										Leg(
											c.TermAs[B]("M.d(n, 0, M.d(n + 1, i + 1, x))"),
											"the face identity d_i d_0 = d_0 d_{i+1}, n being (n − 1) + 1",
											ByArith(simplex, bounds, simplicial_set.FaceFace.Read(simplicial).At(below, zero, above, x))),
										Leg(
											c.TermAs[B]("M.d(n, 0, V.zero)"),
											"the face i + 1 of x vanishes, as 2 ≤ i + 1 ≤ n + 1",
											ByArith(bounds, faces.At(above))),
										FinalLeg(
											"and a face keeps zero",
											ByArith(bounds, FaceZero.Read(h).At(below, zero))),
									))
							}))
						b.Show(
							"d_0 x is an n-simplex whose faces 1, …, n vanish, a Moore term of degree n",
							Unfold(MooreTermsDef),
							ByArith(simplex, vanish, simplicial_set.FaceIn.Read(simplicial).At(n, zero, x)))
					})),
				Case(
					"two 0-th faces in a row vanish on a Moore term",
					Derive(func(b *Argument) {
						n := b.FixAs[Nat]("n")
						x := b.FixAs[B]("x")
						moore := b.Conjuncts(
							b.Unfolded(b.Assume(), MooreTermsDef),
							"x is an (n + 2)-simplex",
							"whose faces 1, …, n + 2 vanish")
						simplex, faces := moore[0], moore[1]
						one := b.TermAs[Nat]("1")
						b.Show(
							"d_0 d_0 x = d_0 d_1 x = d_0 0 = 0",
							CalcEq(
								Leg(
									b.TermAs[B]("M.d(n + 1, 0, M.d(n + 2, 1, x))"),
									"the face identity d_0 d_0 = d_0 d_1",
									ByArith(simplex, simplicial_set.FaceFace.Read(simplicial).At(n, zero, one, x))),
								Leg(
									b.TermAs[B]("M.d(n + 1, 0, V.zero)"),
									"the face 1 of x vanishes",
									ByArith(faces.At(one))),
								FinalLeg(
									"and a face keeps zero",
									ByArith(FaceZero.Read(h).At(n, zero))),
							))
					})),
			))
		}),
})}

// MooreComplexChain — the Moore complex is a chain complex.
var MooreComplexChain = mooreComplexChainThm{family.Add(registry.ProofEntry{
	Name: "MooreComplexChain",
	Key:  "prop_84605f35d06434d1",
	Deps: []registry.EntryLike{
		SimplicialModule,
		MooreComplexDef,
		MooreTermsDef,
		MooreSubcomplex,
		chain_complex.ChainComplex,
		chain_complex.ComplexModuleDef,
		module_homomorphism.KernelSubmodule,
		submodule.SubmoduleInter,
		submodule.SubmoduleModuleOn,
		module_homomorphism.HomRestrict,
	},
	Build: family.Card(SimplicialModule.Statement("chain_complex(R, moore_complex(V, M))"),
		"moore_terms(V, M, d, n) is the intersection of the kernels of the faces 1, …, n on M(n), "+
			"a submodule (KernelSubmodule, SubmoduleInter, SubmoduleModuleOn); d_0 restricted to it "+
			"is a homomorphism into moore_terms(n) and squares to zero (MooreSubcomplex, HomRestrict)"),
})}

// HornFillerExists — a simplicial module is a Kan complex: every
// compatible horn has a filler. This is Moore's theorem for simplicial
// groups (May, Simplicial Objects in Algebraic Topology, §17;
// Goerss–Jardine, Simplicial Homotopy Theory, Lemma I.3.4). Starting
// with zero, correct the candidate w one face at a time: the faces r
// below the gap in increasing order by w ↦ w + s_r(y_r − d_r w), then
// the faces above it in decreasing order by w ↦ w + s_{r−1}(y_r − d_r w).
// Face r of the corrected candidate is d_r w + (y_r − d_r w) = y_r, d_r s_r
// and d_r s_{r−1} being the identity. A face i already fixed stays fixed:
// the defect's face there, d_i below r and d_{i−1} above it, is zero by
// FaceFace and the compatibility of the horn, and by the simplicial
// identities d_i of the degenerate term is a degeneracy of that zero face,
// zero again (FaceDegeneracyBelowZero, FaceDegeneracyAboveZero).
var HornFillerExists = hornFillerExistsThm{family.Add(registry.ProofEntry{
	Name: "HornFillerExists",
	Key:  "prop_a26b4f3e99be0bea",
	Reading: "Only the additive groups, the additivity of the " +
		"faces and the degeneracies keeping zero are read, no scalar.",
	Build: family.Sections(SimplicialModule.Statement(Statement{Conclusion: "kan_complex( " +
		"    M)", Abbrev: Abbrev{
		{Name: "face r of w", Text: "M.d(n + 2, r, w)"},
	}}), func(ctx *Script, headline string) *GoalStackNode {

		hornFaceIn := ctx.Lemma(Statement{
			Binders: "∀M:simplicial_ops(B). ∀n k i:num. ∀y:(num → B).",
			Hypotheses: []string{
				"face_family(M, n, horn_faces(n, k), y)",
				"i ≤ n + 1",
				"i ≠ k",
			},
			Conclusion: "y(i) ∈ M.simplices(n)",
		}, func(
			a *Argument,
			M *Expr[SimplicialOps[B]],
			n *Expr[Nat],
			k *Expr[Nat],
			i *Expr[Nat],
			y *Arrow[Nat, B],
			h Fact,
		) {
			a.Show(
				"a present horn face is a simplex",
				By(
					h,
					simplicial_set.FaceFamilyDef.At(M, n, a.TermAs[Set[Nat]]("horn_faces(n, k)"), y),
					kan_complex.HornFacesMember.At(n, k, i)))
		})

		hornCompatibility := ctx.Lemma(Statement{
			Binders: "∀M:simplicial_ops(B). ∀n k i j:num. ∀y:(num → B).",
			Hypotheses: []string{
				"face_family(M, n, horn_faces(n, k), y)",
				"i < j",
				"i ≤ n + 1",
				"j ≤ n + 1",
				"i ≠ k",
				"j ≠ k",
			},
			Conclusion: "M.d(n, i, y(j)) = M.d(n, j - 1, y(i))",
		}, func(
			a *Argument,
			M *Expr[SimplicialOps[B]],
			n *Expr[Nat],
			k *Expr[Nat],
			i *Expr[Nat],
			j *Expr[Nat],
			y *Arrow[Nat, B],
			h Fact,
		) {
			a.Show(
				"two present horn faces agree on their intersection",
				By(
					h,
					simplicial_set.FaceFamilyDef.At(M, n, a.TermAs[Set[Nat]]("horn_faces(n, k)"), y),
					simplicial_set.FacesCompatibleDef.At(
						a.TermAs[Fun3[Nat, Nat, B, B]]("M.d"), n, a.TermAs[Set[Nat]]("horn_faces(n, k)"), y),
					kan_complex.HornFacesMember.At(n, k, i),
					kan_complex.HornFacesMember.At(n, k, j)))
		})

		return ctx.Theorem(headline, func(
			a *Argument,
			R *Expr[RingOps[A]],
			V *Expr[ModuleOps[A, B]],
			M *Expr[SimplicialOps[B]],
			h Fact,
		) {
			simplicial := ModuleSimplicialSet.Read(h)

			simplexModule := a.Have(
				"each simplicial degree is a module",
				"∀n:num. module_on(R, «degree module»(n))",
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]("n")
					b.Show(
						"a submodule is a module",
						By(
							AmbientModule.Read(h),
							SimplicesSubmodule.Read(h).At(n),
							submodule.SubmoduleModuleOn.At(R, V, b.TermAs[Set[B]]("M.simplices(n)"))))
				}))
			simplexGroup := a.Have(
				"each simplicial degree is an additive group",
				"∀n:num. group_on(module_additive_group(«degree module»(n)))",
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]("n")
					b.Show(
						"the additive group of a module is a group",
						By(simplexModule.At(n), module.AddGroupOn.At(R, b.TermAs[ModuleOps[A, B]]("«degree module»(n)"))))
				}))

			differenceSelf := a.Have(
				"a simplex minus itself is zero",
				"∀n:num. ∀x:B. x ∈ M.simplices(n) ⇒ x + -x = V.zero",
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]("n")
					x := b.FixAs[B]("x")
					simplex := b.Assume()
					b.Show(
						"−x is a right inverse of x in the additive group of the degree",
						By(
							simplex,
							simplexGroup.At(n),
							group.RightInverseOn.At(
								b.TermAs[group.GroupOps[B]]("module_additive_group(«degree module»(n))"), x)))
				}))

			cancelDefect := a.Have(
				"adding y − x to x gives y",
				"∀n:num. ∀x y:B. x ∈ M.simplices(n) ∧ y ∈ M.simplices(n) ⇒ x + (y + -x) = y",
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]("n")
					b.FixAs[B]("x")
					b.FixAs[B]("y")
					p := b.Conjuncts(
						b.Assume(),
						"the first simplex",
						"the second simplex")
					b.Show(
						"x + (y − x) regroups to y in the module of the degree",
						ByChase(Depth(0), simplexModule.At(n), p[0], p[1]))
				}))

			addZero := a.Have(
				"adding zero keeps a simplex",
				"∀n:num. ∀x:B. x ∈ M.simplices(n) ⇒ x + V.zero = x",
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]("n")
					x := b.FixAs[B]("x")
					simplex := b.Assume()
					b.Show(
						"zero is a right identity of the additive group of the degree",
						By(
							simplex,
							simplexGroup.At(n),
							group.RightIdentityOn.At(
								b.TermAs[group.GroupOps[B]]("module_additive_group(«degree module»(n))"), x)))
				}))

			differenceFaceZero := a.Have(
				"two simplices with a common face differ by a simplex with that face zero",
				Statement{
					Binders: "∀n i:num. ∀x y:B.",
					Hypotheses: []string{
						"i ≤ n + 1",
						"x ∈ M.simplices(n + 1)",
						"y ∈ M.simplices(n + 1)",
						"M.d(n + 1, i, x) = M.d(n + 1, i, y)",
					},
					Conclusion: "M.d(n + 1, i, x + -y) = V.zero",
				},
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]("n")
					i := b.FixAs[Nat]("i")
					x := b.FixAs[B]("x")
					y := b.FixAs[B]("y")
					p := b.Conjuncts(
						b.Assume(),
						"the face bound",
						"the first simplex",
						"the second simplex",
						"their faces agree")
					faceIn := b.Have(
						"the common face is a simplex",
						"M.d(n + 1, i, x) ∈ M.simplices(n)",
						By(simplicial, p[0], p[1], simplicial_set.FaceIn.At(M, n, i, x)))
					b.Show(
						"the difference has this face zero",
						By(
							p[0],
							p[1],
							p[2],
							p[3],
							faceIn,
							FaceSub.Read(h).At(n, i, x, y),
							differenceSelf.At(n, b.TermAs[B]("M.d(n + 1, i, x)"))))
				}))

			correct := a.Have(
				"face r is corrected by a degeneracy of the defect, keeping every face the degeneracy passes by",
				Statement{
					Binders: "∀n k r j:num. ∀y:(num → B). ∀w:B.",
					Hypotheses: []string{
						"face_family(M, n + 1, horn_faces(n + 1, k), y)",
						"r ≤ n + 2",
						"r ≠ k",
						"j ≤ n + 1",
						"j = r ∨ j + 1 = r",
						"w ∈ M.simplices(n + 2)",
					},
					Conclusion: "∃u:B. " +
						"    u ∈ M.simplices(n + 2) ∧ " +
						"    M.d(n + 2, r, u) = y(r) ∧ " +
						"    (∀i:num. " +
						"        i ≤ n + 2 ∧ i ≠ k ∧ (i < j ∨ j + 1 < i) ∧ M.d(n + 2, i, w) = y(i) ⇒ " +
						"        M.d(n + 2, i, u) = y(i))",
				},
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]("n")
					k := b.FixAs[Nat]("k")
					r := b.FixAs[Nat]("r")
					j := b.FixAs[Nat]("j")
					y := b.FixAs[Fun[Nat, B]]("y")
					w := b.FixAs[B]("w")
					p := b.Conjuncts(
						b.Assume(),
						"the compatible horn",
						"face r is a face of the candidate",
						"face r is not the missing face",
						"the degeneracy is defined",
						"the degeneracy is s_r or s_{r−1}",
						"the candidate")
					face := b.TermAs[B]("«face r of w»")
					yr := b.TermAs[B]("y(r)")
					yIn := b.Have(
						"the prescribed face is a simplex",
						"y(r) ∈ M.simplices(n + 1)",
						ByArith(p[0], p[1], p[2], At(hornFaceIn, M, b.TermAs[Nat]("n + 1"), k, r, y)))
					// The laws read at degree n + 1 spell n + 1 + 1. Simplified with no
					// rules rewrites nothing: it makes the law a resident hypothesis, so
					// the RingNf of the step that reads it folds n + 1 + 1 to n + 2 there.
					faceLaw := b.Simplified(simplicial_set.FaceIn.Read(simplicial).At(b.TermAs[Nat]("n + 1"), r, w))
					faceIn := b.Have(
						"the candidate face is a simplex",
						"«face r of w» ∈ M.simplices(n + 1)",
						RingNf(),
						By(p[1], p[5], faceLaw))
					z, zDef := b.LetAs[B]("z", "y(r) + -«face r of w»")
					zIn := b.Have(
						"the defect is a simplex",
						"z ∈ M.simplices(n + 1)",
						By(
							yIn,
							faceIn,
							zDef,
							SimplicesSubmodule.Read(h).At(b.TermAs[Nat]("n + 1")),
							submodule.SubmoduleSub))
					degenerateLaw := b.Simplified(GroupPremises(
						p[3], zIn, simplicial_set.DegeneracyIn.Read(simplicial).At(b.TermAs[Nat]("n + 1"), j, z)))
					degenerate := b.Have(
						"the degenerate defect is a simplex",
						"M.s(n + 1, j, z) ∈ M.simplices(n + 2)",
						RingNf(),
						By(degenerateLaw))
					sz := b.TermAs[B]("M.s(n + 1, j, z)")
					u, uDef := b.LetAs[B]("u", "w + M.s(n + 1, j, z)")
					uIn := b.Have(
						"the correction is a simplex",
						"u ∈ M.simplices(n + 2)",
						By(
							p[5],
							degenerate,
							uDef,
							SimplicesSubmodule.Read(h).At(b.TermAs[Nat]("n + 2")),
							submodule.SubmoduleAdd))
					ownFace := b.Simplified(GroupPremises(
						p[3], zIn, simplicial_set.FaceDegeneracyEqual.Read(simplicial).At(b.TermAs[Nat]("n + 1"), j, z)))
					nextFace := b.Simplified(GroupPremises(
						p[3], zIn, simplicial_set.FaceDegeneracyNext.Read(simplicial).At(b.TermAs[Nat]("n + 1"), j, z)))
					retracts := b.Have(
						"face r of the degenerate defect is the defect",
						"M.d(n + 2, r, M.s(n + 1, j, z)) = z",
						RingNf(),
						By(p[4], ownFace, nextFace))
					additive := b.Simplified(FaceAdd.Read(h).At(b.TermAs[Nat]("n + 1"), r, w, sz))
					fixed := b.Have(
						"the correction fixes face r",
						"M.d(n + 2, r, u) = y(r)",
						RingNf(),
						By(
							p[1],
							p[5],
							degenerate,
							zIn,
							faceIn,
							yIn,
							zDef,
							uDef,
							retracts,
							additive,
							cancelDefect.At(b.TermAs[Nat]("n + 1"), face, yr)))
					kept := b.Have(
						"every face of w that the degeneracy passes by is kept",
						Statement{
							Binders: "∀i:num.",
							Hypotheses: []string{
								"i ≤ n + 2",
								"i ≠ k",
								"i < j ∨ j + 1 < i",
								"M.d(n + 2, i, w) = y(i)",
							},
							Conclusion: "M.d(n + 2, i, u) = y(i)",
						},
						b.ForEach(func(i *Expr[Nat]) Action {
							return Derive(func(c *Argument) {
								q := c.Conjuncts(
									c.Assume(),
									"face i is a face of the candidate",
									"face i is not the missing face",
									"the degeneracy passes face i by",
									"face i of w is already fixed")
								vanishes := c.Have(
									"the degenerate defect has face i zero",
									"M.d(n + 2, i, M.s(n + 1, j, z)) = V.zero",
									Derive(func(d *Argument) {
										d.Cases(d.Term("i < j"))
										d.When(
											"below the degeneracy, the degenerate defect has face i zero",
											func(e *Argument, below Fact) {
												order := e.Have(
													"face i lies below face r",
													"i < r ∧ i ≤ n + 1",
													ByArith(below, p[3], p[4]))
												compatible := e.Have(
													"the prescribed faces agree",
													"M.d(n + 1, i, y(r)) = M.d(n + 1, r - 1, y(i))",
													ByArith(
														order,
														q[1],
														p[0],
														p[1],
														p[2],
														At(hornCompatibility, M, e.TermAs[Nat]("n + 1"), k, i, r, y)))
												equalFaces := e.Have(
													"the candidate has the same intersection",
													"M.d(n + 1, i, y(r)) = M.d(n + 1, i, «face r of w»)",
													By(simplicial, order, p[1], p[5], compatible, q[3], simplicial_set.FaceFace.At(M, n, i, r, w)))
												zero := e.Have(
													"the defect has face i zero",
													"M.d(n + 1, i, z) = V.zero",
													By(order, zDef, faceIn, yIn, equalFaces, differenceFaceZero.At(n, i, yr, face)))
												e.Show(
													"a degeneracy above face i keeps its zero face",
													By(zIn, below, p[3], zero, FaceDegeneracyBelowZero.Read(h).At(n, i, j, z)))
											})
										d.Otherwise(
											"above the degeneracy, the degenerate defect has face i zero",
											func(e *Argument, notBelow Fact) {
												order := e.Have(
													"face i lies above face r",
													"j + 1 < i ∧ r < i ∧ i - 1 ≤ n + 1",
													ByArith(notBelow, q[0], q[2], p[4]))
												compatible := e.Have(
													"the prescribed faces agree",
													"M.d(n + 1, r, y(i)) = M.d(n + 1, i - 1, y(r))",
													ByArith(
														order,
														q[0],
														q[1],
														p[0],
														p[1],
														p[2],
														At(hornCompatibility, M, e.TermAs[Nat]("n + 1"), k, r, i, y)))
												equalFaces := e.Have(
													"the candidate has the same upper intersection",
													"M.d(n + 1, i - 1, y(r)) = M.d(n + 1, i - 1, «face r of w»)",
													By(simplicial, order, q[0], p[5], compatible, q[3], simplicial_set.FaceFace.At(M, n, r, i, w)))
												zero := e.Have(
													"the defect has face i − 1 zero",
													"M.d(n + 1, i - 1, z) = V.zero",
													By(
														order,
														zDef,
														faceIn,
														yIn,
														equalFaces,
														differenceFaceZero.At(n, e.TermAs[Nat]("i - 1"), yr, face)))
												e.Show(
													"a degeneracy below face i keeps the zero face",
													By(zIn, order, q[0], zero, FaceDegeneracyAboveZero.Read(h).At(n, i, j, z)))
											})
									}))
								yiIn := c.Have(
									"the prescribed face i is a simplex",
									"y(i) ∈ M.simplices(n + 1)",
									ByArith(q[0], q[1], p[0], At(hornFaceIn, M, c.TermAs[Nat]("n + 1"), k, i, y)))
								additiveAt := c.Simplified(FaceAdd.Read(h).At(c.TermAs[Nat]("n + 1"), i, w, sz))
								c.Show(
									"face i receives zero",
									RingNf(),
									By(
										q[0],
										p[5],
										degenerate,
										yiIn,
										vanishes,
										uDef,
										q[3],
										additiveAt,
										addZero.At(c.TermAs[Nat]("n + 1"), c.TermAs[B]("y(i)"))))
							})
						}))
					b.Show(
						"u fixes face r and keeps every face the degeneracy passes by",
						Witness(u),
						By(uIn, fixed, kept))
				}))

			below := a.Have(
				"the faces below the gap are filled one at a time",
				Statement{
					Binders: "∀n k:num. ∀y:(num → B). ∀r:num.",
					Hypotheses: []string{
						"k ≤ n + 2",
						"face_family(M, n + 1, horn_faces(n + 1, k), y)",
						"r ≤ k",
					},
					Conclusion: "∃w:B. w ∈ M.simplices(n + 2) ∧ (∀i:num. i < r ⇒ M.d(n + 2, i, w) = y(i))",
				},
				Derive(func(b *Argument) {
					b.Induct("r")
					b.Base(
						"zero faces require only the zero simplex",
						func(c *Argument) {
							c.FixAs[Nat]("n")
							c.FixAs[Nat]("k")
							c.FixAs[Fun[Nat, B]]("y")
							given := c.Assume()
							c.Show(
								"zero is a simplex of degree n + 2, and no face lies below 0",
								Witness(c.TermAs[B]("V.zero")),
								ByArith(given, SimplicesSubmodule.Read(h).At(c.TermAs[Nat]("n + 2")), submodule.SubmoduleZero))
						})
					b.Step(
						"a filling of the faces below r extends to face r",
						func(c *Argument, ih Fact) {
							c.StepArgs("r")
							n := c.FixAs[Nat]("n")
							k := c.FixAs[Nat]("k")
							y := c.FixAs[Fun[Nat, B]]("y")
							p := c.Conjuncts(
								c.Assume(),
								"the horn degree",
								"the compatible horn",
								"the next lower bound")
							bounds := c.Have(
								"face r lies below the missing face",
								"r ≤ k ∧ r ≠ k ∧ r ≤ n + 1 ∧ r ≤ n + 2",
								ByArith(p[0], p[2]))
							w, earlier := c.ObtainAs[B](
								"obtain a candidate for the earlier faces",
								"∃w:B. w ∈ M.simplices(n + 2) ∧ (∀i:num. i < r ⇒ M.d(n + 2, i, w) = y(i))",
								By(p[0], p[1], bounds, ih.At(n, k, y)))
							u, corrected := c.ObtainAs[B](
								"correct face r by s_r, which passes the earlier faces by",
								"∃u:B. "+
									"    u ∈ M.simplices(n + 2) ∧ "+
									"    M.d(n + 2, r, u) = y(r) ∧ "+
									"    (∀i:num. "+
									"        i ≤ n + 2 ∧ i ≠ k ∧ (i < r ∨ r + 1 < i) ∧ M.d(n + 2, i, w) = y(i) ⇒ "+
									"        M.d(n + 2, i, u) = y(i))",
								By(p[1], bounds, earlier, correct.At(n, k, c.TermAs[Nat]("r"), c.TermAs[Nat]("r"), y, w)))
							indices := c.Have(
								"the longer interval adds r to the earlier faces of the horn",
								"∀i:num. i < suc(r) ⇒ i = r ∨ (i < r ∧ i ≤ n + 2 ∧ i ≠ k)",
								ByArith(p[0], p[2]))
							c.Show(
								"u fills the faces below r + 1",
								Witness(u),
								By(corrected, earlier, indices))
						})
				}))

			passes := a.Have(
				"the faces above the gap are then filled one at a time from the top",
				Statement{
					Binders: "∀n k:num. ∀y:(num → B). ∀t:num.",
					Hypotheses: []string{
						"k ≤ n + 2",
						"face_family(M, n + 1, horn_faces(n + 1, k), y)",
						"t ≤ n + 2 - k",
					},
					Conclusion: "∃w:B. " +
						"    w ∈ M.simplices(n + 2) ∧ " +
						"    (∀i:num. i < k ⇒ M.d(n + 2, i, w) = y(i)) ∧ " +
						"    (∀i:num. n + 2 - t < i ∧ i ≤ n + 2 ⇒ M.d(n + 2, i, w) = y(i))",
				},
				Derive(func(b *Argument) {
					b.Induct("t")
					b.Base(
						"the lower pass starts the descending pass",
						func(c *Argument) {
							n := c.FixAs[Nat]("n")
							k := c.FixAs[Nat]("k")
							y := c.FixAs[Fun[Nat, B]]("y")
							given := c.Assume()
							w, lower := c.ObtainAs[B](
								"fill every face below the gap",
								"∃w:B. w ∈ M.simplices(n + 2) ∧ (∀i:num. i < k ⇒ M.d(n + 2, i, w) = y(i))",
								ByArith(given, below.At(n, k, y, k)))
							c.Show(
								"w fills the faces below the gap, and no face above it is fixed yet",
								Witness(w),
								ByArith(lower))
						})
					b.Step(
						"a filling below the gap and above n + 2 − t extends to face n + 2 − t",
						func(c *Argument, ih Fact) {
							c.StepArgs("t")
							n := c.FixAs[Nat]("n")
							k := c.FixAs[Nat]("k")
							y := c.FixAs[Fun[Nat, B]]("y")
							p := c.Conjuncts(
								c.Assume(),
								"the horn degree",
								"the compatible horn",
								"the descending stage bound")
							bounds := c.Have(
								"the next upper face lies above the gap",
								"t ≤ n + 2 - k ∧ "+
									"k < n + 2 - t ∧ "+
									"n + 2 - t ≤ n + 2 ∧ "+
									"n + 2 - suc(t) + 1 = n + 2 - t ∧ "+
									"n + 2 - t ≠ k ∧ "+
									"n + 2 - suc(t) ≤ n + 1",
								ByArith(p[0], p[2]))
							w, previous := c.ObtainAs[B](
								"obtain the preceding descending stage",
								"∃w:B. "+
									"    w ∈ M.simplices(n + 2) ∧ "+
									"    (∀i:num. i < k ⇒ M.d(n + 2, i, w) = y(i)) ∧ "+
									"    (∀i:num. n + 2 - t < i ∧ i ≤ n + 2 ⇒ M.d(n + 2, i, w) = y(i))",
								By(p[0], p[1], bounds, ih.At(n, k, y)))
							u, corrected := c.ObtainAs[B](
								"correct face n + 2 − t by s_{n+1−t}, which passes the faces already fixed by",
								"∃u:B. "+
									"    u ∈ M.simplices(n + 2) ∧ "+
									"    M.d(n + 2, n + 2 - t, u) = y(n + 2 - t) ∧ "+
									"    (∀i:num. "+
									"        i ≤ n + 2 ∧ "+
									"        i ≠ k ∧ "+
									"        (i < n + 2 - suc(t) ∨ n + 2 - suc(t) + 1 < i) ∧ "+
									"        M.d(n + 2, i, w) = y(i) ⇒ "+
									"        M.d(n + 2, i, u) = y(i))",
								By(
									p[1],
									bounds,
									previous,
									correct.At(n, k, c.TermAs[Nat]("n + 2 - t"), c.TermAs[Nat]("n + 2 - suc(t)"), y, w)))
							indices := c.Have(
								"the descending interval gains face n + 2 − t, and s_{n+1−t} passes the others by",
								"∀i:num. "+
									"    (i < k ⇒ i ≤ n + 2 ∧ i ≠ k ∧ i < n + 2 - suc(t)) ∧ "+
									"    (n + 2 - suc(t) < i ⇒ i = n + 2 - t ∨ (n + 2 - t < i ∧ i ≠ k ∧ n + 2 - suc(t) + 1 < i))",
								ByArith(p[0], p[2]))
							c.Show(
								"u fills the faces below the gap and those above n + 1 − t",
								Witness(u),
								By(corrected, previous, indices))
						})
				}))

			positive := a.Have(
				"so every compatible horn of dimension n + 2 has its filler",
				Statement{
					Binders: "∀n k:num. ∀y:(num → B).",
					Hypotheses: []string{
						"k ≤ n + 2",
						"face_family(M, n + 1, horn_faces(n + 1, k), y)",
					},
					Conclusion: "∃w:B. w ∈ M.simplices(n + 2) ∧ faces_filler(n + 1, horn_faces(n + 1, k), y, w)",
				},
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]("n")
					k := b.FixAs[Nat]("k")
					y := b.FixAs[Fun[Nat, B]]("y")
					p := b.Conjuncts(
						b.Assume(),
						"the horn degree",
						"the compatible horn")
					w, filled := b.ObtainAs[B](
						"complete both passes",
						"∃w:B. "+
							"    w ∈ M.simplices(n + 2) ∧ "+
							"    (∀i:num. i < k ⇒ M.d(n + 2, i, w) = y(i)) ∧ "+
							"    (∀i:num. n + 2 - (n + 2 - k) < i ∧ i ≤ n + 2 ⇒ M.d(n + 2, i, w) = y(i))",
						ByArith(p[0], p[1], passes.At(n, k, y, b.TermAs[Nat]("n + 2 - k"))))
					end := b.Have(
						"the descending pass ends at the missing face",
						"n + 2 - (n + 2 - k) = k",
						ByArith(p[0]))
					b.Do(end.Rw())
					indices := b.Have(
						"every other face lies on one side of the gap",
						"∀i:num. i ≠ k ⇒ i < k ∨ k < i",
						ByArith())
					b.Show(
						"the two passes fill the horn",
						Witness(w),
						Simp(Fwd(simplicial_set.FacesFillerDef), Fwd(kan_complex.HornFacesMember)),
						RingNf(),
						By(filled, indices))
				}))

			// The correction lemmas index the filler at n + 2, its defect a
			// simplex of degree n + 1 with faces of its own; a filler of degree 1
			// has a vertex for its defect, which has no faces, and the horn of an
			// edge is one vertex, filled by its degeneracy in any simplicial set.
			filler := a.Have(
				"every compatible horn has its filler",
				Statement{
					Binders: "∀n k:num. ∀y:(num → B).",
					Hypotheses: []string{
						"k ≤ n + 1",
						"face_family(M, n, horn_faces(n, k), y)",
					},
					Conclusion: "∃w:B. w ∈ M.simplices(n + 1) ∧ faces_filler(n, horn_faces(n, k), y, w)",
				},
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]("n")
					k := b.FixAs[Nat]("k")
					y := b.FixAs[Fun[Nat, B]]("y")
					p := b.Conjuncts(
						b.Assume(),
						"the horn degree",
						"the compatible horn")
					dimensions := b.Have(
						"a degree is zero or a successor",
						"n = 0 ∨ (∃m:num. n = suc(m))",
						By(peano.Cases.At(n)))
					b.Do(dimensions.SplitDisj(LeftHolds(
						"the horn of an edge is filled by the degeneracy of its vertex",
						Given(func(c *Argument, isZero Fact) {
							c.Do(isZero.Rw())
							c.Show(
								"the degenerate edge fills the horn",
								RingNf(),
								By(p[0], p[1], kan_complex.OneDimensionalHornFill.Read(simplicial).At(k, y)))
						})), RightHolds(
						"positive degrees admit both correction passes",
						Given(func(c *Argument, hasPredecessor Fact) {
							m, isSuccessor := c.UnpackAs[Nat](hasPredecessor, "m")
							degree := c.Have(
								"the positive degree is m + 1",
								"n = m + 1",
								ByArith(isSuccessor))
							c.Do(degree.Rw())
							c.Show(
								"the two correction passes fill the horn",
								RingNf(),
								By(p[0], p[1], positive.At(m, k, y)))
						}))))
				}))
			a.Show(
				"so M is a Kan complex",
				By(simplicial, filler, kan_complex.KanComplex.At(M)))
		})
	}),
})}

// SphereToMooreCycle — a compatible sphere of (n + 1)-simplices has a
// simplex w filling every face but the 0-th, and the defect
// z = y(0) − d_0 w is then a Moore cycle of degree n + 1: the faces
// 1, …, n + 2 form a horn, which fills as a simplicial module is a Kan
// complex; for every i ≤ n + 1 the face identity, the filling and the
// compatibility of the sphere at (0, i + 1) give
// d_i d_0 w = d_0 d_{i+1} w = d_0 y(i + 1) = d_i y(0), so the linear face
// d_i kills z.
var SphereToMooreCycle = sphereToMooreCycleThm{family.Add(registry.ProofEntry{
	Name: "SphereToMooreCycle",
	Key:  "prop_bdeb02d62913b0e1",
	Reading: "True in every simplicial module, with no " +
		"acyclicity: z is a Moore cycle whether or not it bounds.",
	Build: SimplicialModule.Law(Statement{
		Binders: "∀n:num. ∀y:(num → B).",
		Hypotheses: []string{
			"∀i:num. i ≤ n + 2 ⇒ y(i) ∈ M.simplices(n + 1)",
			"∀i j:num. i < j ∧ j ≤ n + 2 ⇒ M.d(n + 1, i, y(j)) = M.d(n + 1, j - 1, y(i))",
		},
		Conclusion: "∃w:B. " +
			"    w ∈ M.simplices(n + 2) ∧ " +
			"    (∀i:num. 1 ≤ i ∧ i ≤ n + 2 ⇒ M.d(n + 2, i, w) = y(i)) ∧ " +
			"    y(0) + -M.d(n + 2, 0, w) ∈ cycles(moore_complex(V, M), n + 1)",
	},
		func(
			a *Argument,
			h SimplicialModuleFact[on.R, on.V],
			n *Expr[Nat],
			y *Arrow[Nat, B],
			simplices, compatible Fact,
		) {
			simplicial := ModuleSimplicialSet.Read(h)
			zero := a.TermAs[Nat]("0")
			next := a.TermAs[Nat]("n + 1")
			horn := a.Have(
				"the faces 1, …, n + 2 of the sphere form a horn of M missing the face 0",
				"face_family(M, n + 1, horn_faces(n + 1, 0), y)",
				Unfold(simplicial_set.FaceFamilyDef),
				SplitConj(
					Case(
						"its members are faces of the sphere, (n + 1)-simplices",
						Derive(func(b *Argument) {
							i := b.FixAs[Nat]("i")
							face := b.Assume()
							b.Show(
								"a face of the horn is a face i ≤ n + 2 of the sphere",
								ByArith(face, simplices.At(i), kan_complex.HornFacesMember.At(next, zero, i)))
						})),
					Case(
						"and they are compatible, as the faces of the sphere are",
						Unfold(simplicial_set.FacesCompatibleDef),
						Derive(func(b *Argument) {
							i := b.FixAs[Nat]("i")
							j := b.FixAs[Nat]("j")
							pair := b.Assume()
							b.Show(
								"two faces i < j of the horn are two faces of the sphere, j ≤ n + 2",
								ByArith(pair, compatible.At(i, j), kan_complex.HornFacesMember.At(next, zero, j)))
						})),
				))
			dimension := a.Have(
				"the horn has dimension (n + 1) + 1 = n + 2, and its missing face 0 is at most that",
				"n + 1 + 1 = n + 2 ∧ 0 ≤ n + 1 + 1",
				ByArith())
			w, filled := a.ObtainAs[B](
				"a simplicial module is a Kan complex, so the horn has a filler w, an (n + 2)-simplex",
				"∃w:B. w ∈ M.simplices(n + 2) ∧ faces_filler(n + 1, horn_faces(n + 1, 0), y, w)",
				By(dimension, horn, kan_complex.KanFill.Read(HornFillerExists.Read(h)).At(next, zero, y)))
			filling := a.Conjuncts(
				filled,
				"w is an (n + 2)-simplex",
				"whose faces at the horn are the members of y")
			simplex, faceOf := filling[0], a.Unfolded(filling[1], simplicial_set.FacesFillerDef)
			faces := a.Have(
				"so the faces 1, …, n + 2 of w are y(1), …, y(n + 2)",
				"∀i:num. 1 ≤ i ∧ i ≤ n + 2 ⇒ M.d(n + 2, i, w) = y(i)",
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]("i")
					bounds := b.Assume()
					b.Show(
						"a face i with 1 ≤ i ≤ n + 2 is a face of the horn",
						ByArith(bounds, faceOf.At(i), kan_complex.HornFacesMember.At(next, zero, i)))
				}))
			agree := a.Have(
				"the faces of d_0 w are those of y(0)",
				"∀i:num. i ≤ n + 1 ⇒ M.d(n + 1, i, M.d(n + 2, 0, w)) = M.d(n + 1, i, y(0))",
				Derive(func(b *Argument) {
					b.FixAs[Nat]("i")
					bound := b.Assume()
					above := b.TermAs[Nat]("i + 1")
					b.Show(
						"d_i d_0 w = d_0 d_{i+1} w = d_0 y(i + 1) = d_i y(0)",
						CalcEq(
							Leg(
								b.TermAs[B]("M.d(n + 1, 0, M.d(n + 2, i + 1, w))"),
								"the face identity d_i d_0 = d_0 d_{i+1}",
								ByArith(bound, simplex, simplicial_set.FaceFace.Read(simplicial).At(n, zero, above, w))),
							Leg(
								b.TermAs[B]("M.d(n + 1, 0, y(i + 1))"),
								"w fills the face i + 1 of the sphere, 1 ≤ i + 1 ≤ n + 2",
								ByArith(bound, faces.At(above))),
							FinalLeg(
								"and the sphere is compatible at its faces 0 < i + 1",
								ByArith(bound, compatible.At(zero, above))),
						))
				}))
			y0In := a.Have(
				"y(0) is an (n + 1)-simplex",
				"y(0) ∈ M.simplices(n + 1)",
				ByArith(simplices.At(zero)))
			zerothFaceIn := a.Have(
				"and so is the face d_0 w of the (n + 2)-simplex w",
				"M.d(n + 2, 0, w) ∈ M.simplices(n + 1)",
				By(simplicial_set.FaceIn.Read(simplicial).At(next, zero, w), simplex, dimension))
			vanish := a.Have(
				"so every face of z = y(0) − d_0 w vanishes",
				"∀i:num. i ≤ n + 1 ⇒ M.d(n + 1, i, y(0) + -M.d(n + 2, 0, w)) = V.zero",
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]("i")
					bound := b.Assume()
					b.Show(
						"the face d_i is linear and agrees on y(0) and d_0 w",
						ByChase(Depth(0), bound, y0In, zerothFaceIn, agree.At(i), FaceHom.Read(h).At(n, i)))
				}))
			zIn := a.Have(
				"z is an (n + 1)-simplex, M(n + 1) being a submodule",
				"y(0) + -M.d(n + 2, 0, w) ∈ M.simplices(n + 1)",
				By(y0In, zerothFaceIn, SimplicesSubmodule.Read(h).At(next), submodule.SubmoduleSub))
			cycle := a.Have(
				"so z is a Moore cycle: its faces 1, …, n + 1 vanish, and its 0-th face too",
				"y(0) + -M.d(n + 2, 0, w) ∈ cycles(moore_complex(V, M), n + 1)",
				Unfold(MooreComplexDef),
				Unfold(chain_complex.CyclesDef),
				Unfold(MooreTermsDef),
				ByArith(zIn, vanish.At(zero), vanish))
			a.Take(w)
			a.Show(
				"w fills every face of the sphere but the 0-th, and leaves the Moore cycle z",
				By(simplex, faces, cycle))
		}),
})}

// MooreBoundaryFillsSphere — if w fills every face of the sphere but the
// 0-th and the defect y(0) − d_0 w is d_0 v for a Moore term v, then
// w + v fills the whole sphere.
var MooreBoundaryFillsSphere = mooreBoundaryFillsSphereThm{family.Add(registry.ProofEntry{
	Name: "MooreBoundaryFillsSphere",
	Key:  "prop_b352f9ea9169d324",
	Deps: []registry.EntryLike{
		SimplicialModule,
		MooreTermsDef,
		FaceAdd,
		module.AddGroupOn,
		submodule.SubmoduleSubgroup,
	},
	Build: family.Card(SimplicialModule.Statement(Statement{
		Binders: "∀n:num. ∀y:(num → B). ∀w v:B.",
		Hypotheses: []string{
			"∀i:num. i ≤ n + 2 ⇒ y(i) ∈ M.simplices(n + 1)",
			"w ∈ M.simplices(n + 2)",
			"∀i:num. 1 ≤ i ∧ i ≤ n + 2 ⇒ M.d(n + 2, i, w) = y(i)",
			"v ∈ moore_terms(V, M, n + 2)",
			"M.d(n + 2, 0, v) = y(0) + -M.d(n + 2, 0, w)",
		},
		Conclusion: "w + v ∈ M.simplices(n + 2) ∧ (∀i:num. i ≤ n + 2 ⇒ M.d(n + 2, i, w + v) = y(i))",
	}),
		"by FaceAdd, d_0(w + v) = d_0 w + (y(0) − d_0 w) = y(0), and for 1 ≤ i ≤ n + 2, "+
			"d_i(w + v) = y(i) + V.zero = y(i), v's faces above 0 vanishing (MooreTermsDef); the "+
			"arithmetic is the additive group of the submodule M(n + 1), where every vector lies"),
})}

// SphereFillsInAcyclic — under an acyclic augmentation every compatible
// sphere of (n + 1)-simplices is the boundary of an (n + 2)-simplex.
var SphereFillsInAcyclic = sphereFillsInAcyclicThm{family.Add(registry.ProofEntry{
	Name: "SphereFillsInAcyclic",
	Key:  "prop_b06b8680010143f2",
	Reading: "Of acyclicity only the positive-degree conjunct is read. " +
		"The case below, two vertices filled by an edge, is EdgeFillsInAcyclic.",
	Deps: []registry.EntryLike{
		AcyclicAugmentation,
		SphereToMooreCycle,
		MooreBoundaryFillsSphere,
		MooreComplexDef,
		chain_complex.BoundariesDef,
	},
	Build: family.Card(AcyclicAugmentation.Statement(Statement{
		Binders: "∀n:num. ∀y:(num → B).",
		Hypotheses: []string{
			"∀i:num. i ≤ n + 2 ⇒ y(i) ∈ M.simplices(n + 1)",
			"∀i j:num. i < j ∧ j ≤ n + 2 ⇒ M.d(n + 1, i, y(j)) = M.d(n + 1, j - 1, y(i))",
		},
		Conclusion: "∃w:B. w ∈ M.simplices(n + 2) ∧ (∀i:num. i ≤ n + 2 ⇒ M.d(n + 2, i, w) = y(i))",
	}),
		"SphereToMooreCycle gives w and the Moore cycle y(0) − d_0 w of degree n + "+
			"1; acyclicity makes it a Moore boundary, d_0 v with v ∈ moore_terms(n + 2) "+
			"(BoundariesDef), and MooreBoundaryFillsSphere fills the sphere with w + v"),
})}

// EdgeFillsInAcyclic — under an acyclic augmentation two vertices with one
// image under ε are the two faces of an edge: their difference is d_0 v for
// a Moore term v of degree 1, whose face 1 vanishes, and the edge
// v + s_0 y₁ has faces (y₀ − y₁) + y₁ = y₀ and 0 + y₁ = y₁.
var EdgeFillsInAcyclic = edgeFillsInAcyclicThm{family.Add(registry.ProofEntry{
	Name: "EdgeFillsInAcyclic",
	Key:  "prop_fd193da382a99811",
	Reading: "This is the sphere filling in dimension 0, where the sphere is two vertices with " +
		"no compatibility to ask; the condition ε(y₀) = ε(y₁) takes its place. Of acyclicity only " +
		"the ⇒ direction of the degree-0 conjunct is read. y₀ is face 0, the edge's last vertex.",
	Build: AcyclicAugmentation.Law(Statement{
		Binders: "∀y₀ y₁:B.",
		Hypotheses: []string{
			"y₀ ∈ M.simplices(0)",
			"y₁ ∈ M.simplices(0)",
			"ε(y₀) = ε(y₁)",
		},
		Conclusion: "∃w:B. w ∈ M.simplices(1) ∧ M.d(1, 0, w) = y₀ ∧ M.d(1, 1, w) = y₁",
	},
		func(a *Argument, acyclic Fact, y0, y1 *Expr[B], y0In, y1In, sameImage Fact) {
			parts := a.Conjuncts(
				a.Unfolded(acyclic, AcyclicAugmentation),
				"M is a simplicial module",
				"its Moore complex is exact in positive degrees",
				"ε carries the vertices onto N",
				"two vertices have one image under ε exactly when their difference is a Moore boundary")
			h, fibres := parts[0], parts[3]
			simplicial := ModuleSimplicialSet.Read(h)
			zero := a.TermAs[Nat]("0")
			one := a.TermAs[Nat]("1")
			vertices := SimplicesModule.Read(h).At(zero)
			boundary := a.Have(
				"y₀ − y₁ is a Moore boundary of degree 0",
				"y₀ + -y₁ ∈ boundaries(moore_complex(V, M), 0)",
				By(fibres.At(y0, y1), y0In, y1In, sameImage))
			v, preimage := a.ObtainAs[B](
				"so y₀ − y₁ is d_0 v for a Moore term v of degree 1",
				"∃v:B. v ∈ moore_terms(V, M, 1) ∧ M.d(1, 0, v) = y₀ + -y₁",
				By(
					a.Unfolded(a.Unfolded(boundary, MooreComplexDef), chain_complex.BoundariesDef),
					set_basic.InImage))
			found := a.Conjuncts(
				preimage,
				"v is a Moore term of degree 1",
				"whose face 0 is y₀ − y₁")
			mooreTerm, difference := found[0], found[1]
			moore := a.Conjuncts(
				a.Unfolded(mooreTerm, MooreTermsDef),
				"v is an edge",
				"whose face 1 vanishes")
			edge, faces := moore[0], moore[1]
			degenerateEdge := a.TermAs[B]("M.s(0, 0, y₁)")
			degenerateIn := a.Have(
				"the degenerate edge s_0 y₁ is an edge",
				"M.s(0, 0, y₁) ∈ M.simplices(1)",
				By(y1In, simplicial_set.DegeneracyIn.Read(simplicial).At(zero, zero, y1)))
			a.Take(a.TermAs[B]("v + M.s(0, 0, y₁)"))
			a.Do(SplitConjAll(
				Case(
					"v + s_0 y₁ is an edge, the edges being a submodule",
					By(edge, degenerateIn, SimplicesSubmodule.Read(h).At(one), submodule.SubmoduleAdd)),
				Case(
					"its face 0 is y₀",
					CalcEq(
						Leg(
							a.TermAs[B]("M.d(1, 0, v) + M.d(1, 0, M.s(0, 0, y₁))"),
							"the face is linear",
							By(edge, degenerateIn, FaceAdd.Read(h).At(zero, zero, v, degenerateEdge))),
						Leg(
							a.TermAs[B]("(y₀ + -y₁) + y₁"),
							"d_0 v is y₀ − y₁, and d_0 s_0 is the identity",
							ByArith(difference, y1In, simplicial_set.FaceDegeneracyEqual.Read(simplicial).At(zero, zero, y1))),
						FinalLeg(
							"the difference cancels in the module of the vertices",
							ByChase(Depth(0), vertices, y0In, y1In)),
					)),
				Case(
					"its face 1 is y₁",
					CalcEq(
						Leg(
							a.TermAs[B]("M.d(1, 1, v) + M.d(1, 1, M.s(0, 0, y₁))"),
							"the face is linear",
							By(edge, degenerateIn, FaceAdd.Read(h).At(zero, one, v, degenerateEdge))),
						Leg(
							a.TermAs[B]("V.zero + y₁"),
							"d_1 v vanishes, and d_1 s_0 is the identity",
							ByArith(
								faces.At(one),
								y1In,
								simplicial_set.FaceDegeneracyNext.Read(simplicial).At(zero, zero, y1))),
						FinalLeg(
							"zero adds nothing in the module of the vertices",
							ByChase(Depth(0), vertices, y1In)),
					)),
			))
		}),
})}

// PointedHomotopyAcyclic — a simplicial module augmented over a module N
// by a linear ε, whose identity is joined by a simplicial homotopy h
// keeping zero to ι after the augmentation of the last vertex, ι(0, ·)
// a section of ε, is acyclic over N's carrier.
var PointedHomotopyAcyclic = pointedHomotopyAcyclicThm{family.Add(registry.ProofEntry{
	Name: "PointedHomotopyAcyclic",
	Key:  "prop_ddfc3a1e6acd4438",
	Reading: "May's convention: d_0 h_0 = id and d_{n+1} h_n = ι(n, ε̄ x), ε̄ x = ε(d_0ⁿ x) the " +
		"augmentation of the last vertex, so the top face of Σ_j (−1)^j h_j x is zero on a Moore cycle " +
		"of positive degree. h and ι are maps of sets, never asked to be additive; the route has h " +
		"keep zero, and ι keeps zero as forced below, so that on a Moore cycle x, every face of which " +
		"is zero, only the extreme terms of Σ_j (−1)^j h(n, j, x) survive. ι(n, N.zero) = V.zero is " +
		"not asked: the rest forces it, d_{n+1} h_n(0) = ι(n, ε(0)) with h_n(0) = 0 and the faces " +
		"keeping zero. ε d_0 = ε d_1 on M(1) is not asked either: the second end is a simplicial map, " +
		"and at w and at s_0(d_0 w) it gives ι(0, ε(d_1 w)) = d_1 ι(1, ε(d_0 w)) = ι(0, ε(d_0 w)), " +
		"which ε reads back. Load-bearing are ε's closure into N's carrier and the degree-0 section " +
		"ι(0, c) ∈ M(0) with ε(ι(0, c)) = c, which gives onto-ness and cancels ι in the derived ε d_0 " +
		"= ε d_1. The zero-keeping of h and the additivity of ε carry no weight: the differences Σ_j " +
		"(−1)^j (h_j x − h_j 0) and h_0 x − h_0 y are Moore preimages by the same cancellations.",
	Deps: []registry.EntryLike{
		AcyclicAugmentation,
		SimplicialModule,
		simplicial_homotopy.SimplicialHomotopy,
		simplicial_set.FaceIterateBottomDef,
		simplicial_set.VertexDegeneracyFaces,
		MooreComplexChain,
		MooreComplexDef,
		MooreTermsDef,
		chain_complex.CyclesDef,
		chain_complex.BoundariesDef,
		chain_complex.BoundariesSubsetCycles,
		simplicial_set.MapFace,
		module_homomorphism.HomAdd,
		module_homomorphism.HomNeg,
		module_homomorphism.HomZero,
		module_homomorphism.HomSum,
		module_homomorphism.HomSmul,
		FaceZero,
		set_basic.Extension,
	},
	Build: family.Card(SimplicialModule.Statement(Statement{
		Binders: "∀N:module_ops(A, C). ∀ε:(B → C). ∀ι:(num → C → B). ∀h:(num → num → B → B).",
		Hypotheses: []string{
			"module_homomorphism(R, «degree module»(0), N, ε)",
			"∀c:C. c ∈ N.carrier ⇒ ι(0, c) ∈ M.simplices(0) ∧ ε(ι(0, c)) = c",
			"∀n j:num. j ≤ n ⇒ h(n, j, V.zero) = V.zero",
			"simplicial_homotopy(M, " +
				"    M, " +
				"    λn:num. λx:B. x, " +
				"    λn:num. λx:B. ι(n, ε(face_iterate_bottom(n, n, x))), " +
				"    h)",
		},
		Conclusion: "acyclic_augmentation(R, V, M, N.carrier, ε)",
	}),
		"positive degrees: a Moore cycle x of degree n + 1 has every face zero, so its last vertex "+
			"d_0^{n+1} x is zero, and ι(n + 1, ε(0)) = d_{n+2} h_{n+1}(0) = d_{n+2}(0) = 0 (FaceZero, "+
			"HomZero, h keeping zero). Put w = Σ_{j ≤ n+1} (−1)^j h(n + 1, j, x), the faces being linear "+
			"(HomSum, HomSmul): d_0 w = x, since d_0 h_0 = id and d_0 h_j = h_{j−1} d_0 = h_{j−1}(0) = 0 for "+
			"j ≥ 1; for 1 ≤ k ≤ n + 1 only j = k − 1 and j = k survive (d_k h_j = h_{j−1} d_k for j > k, h_j "+
			"d_{k−1} for j < k − 1), and they cancel by d_k h_{k−1} = d_k h_k; at k = n + 2 only d_{n+2} "+
			"h_{n+1} x = ι(n + 1, ε(0)) = 0 survives. So w ∈ moore_terms(n + 2) with d_0 w = x "+
			"(MooreTermsDef, BoundariesDef), and the converse inclusion is BoundariesSubsetCycles at "+
			"MooreComplexChain. Degree 0: ε is onto N's carrier through ι(0, ·); if ε(x) = ε(y), then z = x "+
			"− y has ε(z) = N.zero (HomAdd, HomNeg), and h_0(z) is an edge with d_0 = z and d_1 = ι(0, ε(z)) "+
			"= 0, a Moore term (the last vertex of a vertex is itself, FaceIterateBottomDef); conversely for "+
			"w ∈ moore_terms(1), ε(d_0 w) = ε(d_1 w) = ε(0) = N.zero: the second end is a simplicial map "+
			"(MapFace), so at w and at the degenerate edge s_0(d_0 w) (simplicial_set.VertexDegeneracyFaces) "+
			"ι(0, ε(d_1 w)) = d_1 ι(1, ε(d_0 w)) = ι(0, ε(d_0 w)), and ε reads ι(0, ·) back (May, Simplicial "+
			"Objects in Algebraic Topology, §5, for the homotopy identities)"),
})}

// ExtraDegeneracyAcyclic — a simplicial module with an extra degeneracy
// over a module N, the augmentation linear on M(0) and σ keeping zero, is
// acyclic over N's carrier.
var ExtraDegeneracyAcyclic = extraDegeneracyAcyclicThm{family.Add(registry.ProofEntry{
	Name: "ExtraDegeneracyAcyclic",
	Key:  "prop_f7e18b4b4f4bc8be",
	Reading: "The route of the note reads every identity of the extra degeneracy, through the " +
		"contraction s_0^j σ d_0^j, and σ(n, V.zero) = V.zero and the linearity of ε, which keep the " +
		"contraction at zero. The statement needs fewer: σ(x) − σ(V.zero) and σ_0(x) − σ_0(y) are the " +
		"Moore terms with the wanted d_0 in positive degrees and in degree 0, by the face identities, " +
		"the bottom identities and the closures alone, and from x − y = d_0 v the edge v + s_0 y has " +
		"faces x and y, which ε d_0 = ε d_1 (ExtraDegeneracyCoequalizes) sends to one value; so the " +
		"two hypotheses on zero and on ε carry no weight, and the statement keeps them all the same.",
	Deps: []registry.EntryLike{
		AcyclicAugmentation,
		PointedHomotopyAcyclic,
		simplicial_homotopy.ExtraDegeneracy,
		simplicial_homotopy.ExtraDegeneracyHomotopy,
		simplicial_homotopy.ExtraDegeneracySection,
		simplicial_homotopy.SimplicialFrontDegeneracyDef,
		simplicial_set.FaceIterateBottomDef,
		simplicial_set.BaseSimplexDef,
		FaceZero,
		DegeneracyZero,
	},
	Build: family.Card(SimplicialModule.Statement(Statement{
		Binders: "∀N:module_ops(A, C). ∀ε:(B → C). ∀σ:(num → B → B). ∀b:(C → B).",
		Hypotheses: []string{
			"extra_degeneracy(M, N.carrier, ε, σ, b)",
			"module_homomorphism(R, «degree module»(0), N, ε)",
			"∀n:num. σ(n, V.zero) = V.zero",
		},
		Conclusion: "acyclic_augmentation(R, V, M, N.carrier, ε)",
	}),
		"PointedHomotopyAcyclic at ι(n, c) = base_simplex(s, b(c), n), the degenerate section, "+
			"and h(n, j, x) = s_0^j σ d_0^j x, which ExtraDegeneracyHomotopy makes a simplicial "+
			"homotopy from the identity to ι after the augmentation of the last vertex. h keeps "+
			"zero, σ(n, V.zero) = V.zero (FaceIterateBottomDef, SimplicialFrontDegeneracyDef, "+
			"FaceZero, DegeneracyZero); ι(0, ·) = b (BaseSimplexDef) lands in M(0) and ε ∘ b = id "+
			"on N's carrier, two conjuncts of extra_degeneracy; and ε is linear on M(0)"),
})}
