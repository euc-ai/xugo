// simplicial_homotopy.go — combinatorial homotopies between simplicial
// maps in May's form, the equivalence relation they generate on the
// simplicial maps, and simplicial homotopy equivalences, with the
// trivial homotopy, whiskering by simplicial maps, the composite of two
// equivalences and the constant simplicial set; an augmented simplicial
// set with an extra degeneracy, the back faces d_0^k and the front
// degeneracies s_0^k, the augmentation coequalizing the two vertices of
// an edge, the degenerate section s_0^n ∘ b, the contraction
// h_j = s_0^j ∘ σ ∘ d_0^j onto it, and the homotopy equivalence with the
// constant simplicial set they give.

package simplicial_homotopy

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/simplicial/simplicial_set"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// Homotopies of simplicial maps
// ---------------------------------------------------------------------------

// SimplicialHomotopy — `simplicial_homotopy(X, Y, F, G, H)`:
// H is a combinatorial homotopy from the simplicial map F to the
// simplicial map G, May's form (Simplicial Objects in Algebraic
// Topology, Definition 5.1): for an n-simplex x and j ≤ n, H(n, j, x) is
// an (n+1)-simplex of Y, with d_0 h_0 = F, d_{n+1} h_n = G,
// d_i h_j = h_{j−1} d_i (i < j), d_{j+1} h_{j+1} = d_{j+1} h_j,
// d_i h_j = h_j d_{i−1} (i > j + 1), s_i h_j = h_{j+1} s_i (i ≤ j) and
// s_i h_j = h_j s_{i−1} (i > j), every identity on the simplices of X.
// It relates two MAPS of simplicial sets; homotopy_group's
// `simplicial_homotopic` relates two SIMPLICES of one simplicial set and
// is another notion.
var SimplicialHomotopy = simplicialHomotopyThm{family.DefineStructure(registry.DefEntry{
	Name:  "SimplicialHomotopy",
	Key:   "prop_7d58f9d71ffc719",
	Const: "simplicial_homotopy",
	Type: "simplicial_ops(A) → " +
		"simplicial_ops(B) → " +
		"(num → A → B) → " +
		"(num → A → B) → " +
		"(num → num → A → B) → " +
		"bool",
	Equations: []string{
		"∀X:simplicial_ops(A). ∀Y:simplicial_ops(B). ∀F G:(num → A → B). ∀H:(num → num → A → B). " +
			"    simplicial_homotopy(X, Y, F, G, H) ⇔ " +
			"    simplicial_map(X, Y, F) ∧ " +
			"    simplicial_map(X, Y, G) ∧ " +
			"    (∀n j:num. ∀x:A. x ∈ X.simplices(n) ∧ j ≤ n ⇒ H(n, j, x) ∈ Y.simplices(n + 1)) ∧ " +
			"    (∀n:num. ∀x:A. x ∈ X.simplices(n) ⇒ Y.d(n + 1, 0, H(n, 0, x)) = F(n, x)) ∧ " +
			"    (∀n:num. ∀x:A. x ∈ X.simplices(n) ⇒ Y.d(n + 1, n + 1, H(n, n, x)) = G(n, x)) ∧ " +
			"    (∀n i j:num. ∀x:A. " +
			"        x ∈ X.simplices(n + 1) ∧ i < j ∧ j ≤ n + 1 ⇒ " +
			"        Y.d(n + 2, i, H(n + 1, j, x)) = H(n, j - 1, X.d(n + 1, i, x))) ∧ " +
			"    (∀n j:num. ∀x:A. " +
			"        x ∈ X.simplices(n) ∧ j < n ⇒ " +
			"        Y.d(n + 1, j + 1, H(n, j + 1, x)) = Y.d(n + 1, j + 1, H(n, j, x))) ∧ " +
			"    (∀n i j:num. ∀x:A. " +
			"        x ∈ X.simplices(n + 1) ∧ j + 1 < i ∧ i ≤ n + 2 ⇒ " +
			"        Y.d(n + 2, i, H(n + 1, j, x)) = H(n, j, X.d(n + 1, i - 1, x))) ∧ " +
			"    (∀n i j:num. ∀x:A. " +
			"        x ∈ X.simplices(n) ∧ i ≤ j ∧ j ≤ n ⇒ " +
			"        Y.s(n + 1, i, H(n, j, x)) = H(n + 1, j + 1, X.s(n, i, x))) ∧ " +
			"    (∀n i j:num. ∀x:A. " +
			"        x ∈ X.simplices(n) ∧ j < i ∧ i ≤ n + 1 ⇒ " +
			"        Y.s(n + 1, i, H(n, j, x)) = H(n + 1, j, X.s(n, i - 1, x)))",
	},
	Reading: "Both ends are simplicial maps by definition, so a homotopy carries the two " +
		"maps it joins. At a vertex x the edge H(0, 0, x) has F(0, x) as its face 0 and G(0, x) " +
		"as its face 1. On simplicial sets that are not Kan the relation is neither symmetric " +
		"nor transitive; simplicial_maps_homotopic is the equivalence relation it generates.",
})}

// SimplicialMapsHomotopicDef — `simplicial_maps_homotopic(X, Y, F, G)`: F and G are simplicial maps joined by a finite zigzag of
// simplicial homotopies Φ(0) = F, Φ(1), …, Φ(k) = G, each step a
// homotopy Ψ(m) from Φ(m) to Φ(m + 1) or from Φ(m + 1) to Φ(m) — the
// equivalence relation simplicial homotopy generates on the simplicial
// maps from X to Y.
var SimplicialMapsHomotopicDef = simplicialMapsHomotopicDefThm{family.Define(registry.DefEntry{
	Name:  "SimplicialMapsHomotopicDef",
	Key:   "prop_7c163b6427b785ab",
	Const: "simplicial_maps_homotopic",
	Type:  "simplicial_ops(A) → simplicial_ops(B) → (num → A → B) → (num → A → B) → bool",
	Equations: []string{
		"∀X:simplicial_ops(A). ∀Y:simplicial_ops(B). ∀F G:(num → A → B). " +
			"    simplicial_maps_homotopic(X, Y, F, G) ⇔ " +
			"    simplicial_map(X, Y, F) ∧ " +
			"    simplicial_map(X, Y, G) ∧ " +
			"    (∃k:num. ∃Φ:(num → num → A → B). ∃Ψ:(num → num → num → A → B). " +
			"        Φ(0) = F ∧ " +
			"        Φ(k) = G ∧ " +
			"        (∀m:num. " +
			"            m < k ⇒ " +
			"            simplicial_homotopy(X, Y, Φ(m), Φ(m + 1), Ψ(m)) ∨ " +
			"            simplicial_homotopy(X, Y, Φ(m + 1), Φ(m), Ψ(m))))",
	},
	Reading: "The zigzag of length 0 makes the relation reflexive on the " +
		"simplicial maps, and only there: both ends are asked to be simplicial maps. Two " +
		"simplicial maps that agree on the simplices of X are homotopic by a one-step " +
		"zigzag, the trivial homotopy, though as functions they may differ off X.",
	Deps: []registry.EntryLike{SimplicialHomotopy},
})}

// SimplicialHomotopyEquivalenceDef —
// `simplicial_homotopy_equivalence(X, Y, F)`: F is a
// simplicial map with a simplicial map G back such that G ∘ F is
// homotopic to the identity of X and F ∘ G to the identity of Y, in the
// relation simplicial_maps_homotopic.
var SimplicialHomotopyEquivalenceDef = simplicialHomotopyEquivalenceDefThm{family.Define(registry.DefEntry{
	Name:  "SimplicialHomotopyEquivalenceDef",
	Key:   "prop_f6a5b9546fa9e0",
	Const: "simplicial_homotopy_equivalence",
	Type:  "simplicial_ops(A) → simplicial_ops(B) → (num → A → B) → bool",
	Equations: []string{
		"∀X:simplicial_ops(A). ∀Y:simplicial_ops(B). ∀F:(num → A → B). " +
			"    simplicial_homotopy_equivalence(X, Y, F) ⇔ " +
			"    simplicial_map(X, Y, F) ∧ " +
			"    (∃G:(num → B → A). " +
			"        simplicial_map(Y, X, G) ∧ " +
			"        simplicial_maps_homotopic(X, X, λn:num. λx:A. G(n, F(n, x)), λn:num. λx:A. x) ∧ " +
			"        simplicial_maps_homotopic(Y, Y, λn:num. λy:B. F(n, G(n, y)), λn:num. λy:B. y))",
	},
	Reading: "The two composites are compared with the identities through the generated " +
		"equivalence relation, so the order of the ends of each homotopy is immaterial and equivalences " +
		"compose. A simplicial isomorphism is one: its composites agree with the identities on the " +
		"simplices, and the trivial homotopy joins two simplicial maps that agree there.",
	Deps: []registry.EntryLike{SimplicialMapsHomotopicDef},
})}

// ---------------------------------------------------------------------------
// Laws of homotopies and homotopy equivalences
// ---------------------------------------------------------------------------

// HomotopyTrivial — a simplicial map is homotopic to itself through
// h_j = s'_j ∘ F.
var HomotopyTrivial = homotopyTrivialThm{family.Add(registry.ProofEntry{
	Name: "HomotopyTrivial",
	Key:  "prop_14168c4fa68f23f7",
	Reading: "The homotopy reads F only on X, so it is also a homotopy from " +
		"F to any simplicial map G that agrees with F on the simplices of X.",
	Deps: []registry.EntryLike{
		SimplicialHomotopy,
		simplicial_set.MapIn,
		simplicial_set.MapFace,
		simplicial_set.MapDegeneracy,
		simplicial_set.DegeneracyIn,
		simplicial_set.FaceDegeneracyEqual,
		simplicial_set.FaceDegeneracyNext,
		simplicial_set.FaceDegeneracyBelow,
		simplicial_set.FaceDegeneracyAbove,
		simplicial_set.DegeneracyDegeneracy,
	},
	Build: family.Card(
		simplicial_set.SimplicialMap.Statement(
			"simplicial_homotopy(X, Y, F, F, λn:num. λj:num. λx:A. Y.s(n, j, F(n, x)))"),
		"d'_0 s'_0 and d'_{n+1} s'_n are the identity (FaceDegeneracyEqual, FaceDegeneracyNext), "+
			"so both ends are F; each remaining identity of May's is a simplicial identity of Y at "+
			"F(n, x) (FaceDegeneracyBelow, FaceDegeneracyAbove, DegeneracyDegeneracy), with F moved "+
			"across a face or a degeneracy by MapFace or MapDegeneracy"),
})}

// HomotopyComposeLeft — a homotopy followed by a simplicial map K is a
// homotopy between the composites: K ∘ H from K ∘ F to K ∘ G.
var HomotopyComposeLeft = homotopyComposeLeftThm{family.Add(registry.ProofEntry{
	Name: "HomotopyComposeLeft",
	Key:  "prop_9d87a68ebb75d291",
	Reading: "K must be simplicial on all of Y: the simplices " +
		"H(n, j, x) of Y(n + 1) need not lie in the image of F or G.",
	Deps: []registry.EntryLike{
		SimplicialHomotopy,
		simplicial_set.MapCompose,
		simplicial_set.MapIn,
		simplicial_set.MapFace,
		simplicial_set.MapDegeneracy,
	},
	Build: family.Card(SimplicialHomotopy.Statement(Statement{
		Binders: "∀Z:simplicial_ops(C). ∀K:(num → B → C).",
		Hypotheses: []string{
			"simplicial_map(Y, Z, K)",
		},
		Conclusion: "simplicial_homotopy(X, " +
			"    Z, " +
			"    λn:num. λx:A. K(n, F(n, x)), " +
			"    λn:num. λx:A. K(n, G(n, x)), " +
			"    λn:num. λj:num. λx:A. K(n + 1, H(n, j, x)))",
	}),
		"the ends are simplicial maps by MapCompose; H(n, j, x) lies in Y(n + 1), "+
			"where K commutes with every face and degeneracy (MapFace, MapDegeneracy), "+
			"so each identity of H is carried by K to the same identity of K ∘ H"),
})}

// HomotopyComposeRight — a simplicial map L followed by a homotopy is a
// homotopy between the composites: H ∘ L from F ∘ L to G ∘ L.
var HomotopyComposeRight = homotopyComposeRightThm{family.Add(registry.ProofEntry{
	Name: "HomotopyComposeRight",
	Key:  "prop_a359cd3b80d33eb",
	Deps: []registry.EntryLike{
		SimplicialHomotopy,
		simplicial_set.MapCompose,
		simplicial_set.MapIn,
		simplicial_set.MapFace,
		simplicial_set.MapDegeneracy,
	},
	Build: family.Card(SimplicialHomotopy.Statement(Statement{
		Binders: "∀W:simplicial_ops(C). ∀L:(num → C → A).",
		Hypotheses: []string{
			"simplicial_map(W, X, L)",
		},
		Conclusion: "simplicial_homotopy(W, " +
			"    Y, " +
			"    λn:num. λw:C. F(n, L(n, w)), " +
			"    λn:num. λw:C. G(n, L(n, w)), " +
			"    λn:num. λj:num. λw:C. H(n, j, L(n, w)))",
	}),
		"the ends are simplicial maps by MapCompose; L carries W(n) into X(n) (MapIn) "+
			"and commutes with every face and degeneracy (MapFace, MapDegeneracy), so "+
			"each identity of H at L(n, w) is the identity of H ∘ L at w"),
})}

// ---------------------------------------------------------------------------
// Extra degeneracies
// ---------------------------------------------------------------------------

// ExtraDegeneracy — `extra_degeneracy(X, S, ε, σ, b)`: the simplicial
// set X, augmented over the set S by ε on its vertices, carries the extra
// degeneracy σ(n, ·) : X(n) → X(n + 1) with the bottom map b : S → X(0)
// in the role of σ at dimension −1. The conjuncts are the closures, the
// face identities d_0 σ = id and d_{i+1} σ_n = σ_{n−1} d_i (n ≥ 1), the
// bottom identities d_1 σ_0 = b ∘ ε on X(0) and ε ∘ b = id on S, and the
// degeneracy identities s_{j+1} σ_n = σ_{n+1} s_j for j ≥ 0.
var ExtraDegeneracy = extraDegeneracyThm{family.DefineStructure(registry.DefEntry{
	Name:  "ExtraDegeneracy",
	Key:   "prop_3f1ed6b46339fb32",
	Const: "extra_degeneracy",
	Type:  "simplicial_ops(A) → set(C) → (A → C) → (num → A → A) → (C → A) → bool",
	Equations: []string{
		"∀X:simplicial_ops(A). ∀S:set(C). ∀ε:(A → C). ∀σ:(num → A → A). ∀b:(C → A). " +
			"    extra_degeneracy(X, S, ε, σ, b) ⇔ " +
			"    simplicial_set(X) ∧ " +
			"    (∀x:A. x ∈ X.simplices(0) ⇒ ε(x) ∈ S) ∧ " +
			"    (∀c:C. c ∈ S ⇒ b(c) ∈ X.simplices(0)) ∧ " +
			"    (∀n:num. ∀x:A. x ∈ X.simplices(n) ⇒ σ(n, x) ∈ X.simplices(n + 1)) ∧ " +
			"    (∀c:C. c ∈ S ⇒ ε(b(c)) = c) ∧ " +
			"    (∀x:A. x ∈ X.simplices(0) ⇒ X.d(1, 1, σ(0, x)) = b(ε(x))) ∧ " +
			"    (∀n:num. ∀x:A. x ∈ X.simplices(n) ⇒ X.d(n + 1, 0, σ(n, x)) = x) ∧ " +
			"    (∀n i:num. ∀x:A. " +
			"        x ∈ X.simplices(n + 1) ∧ i ≤ n + 1 ⇒ " +
			"        X.d(n + 2, i + 1, σ(n + 1, x)) = σ(n, X.d(n + 1, i, x))) ∧ " +
			"    (∀n j:num. ∀x:A. " +
			"        x ∈ X.simplices(n) ∧ j ≤ n ⇒ X.s(n + 1, j + 1, σ(n, x)) = σ(n + 1, X.s(n, j, x)))",
	},
	Reading: "The closures with the face and bottom identities are what the acyclicity " +
		"of an augmented simplicial module reads, σ and b as maps of sets. The identity s_0 " +
		"σ_n = σ_{n+1} σ_n (the case j = −1) is NOT a conjunct, and nothing built on the " +
		"predicate needs it: it fails for the standard resolution's σ(u) = var(u) − var(0), " +
		"var not being additive, while the degenerate section s_0^n ∘ b and the contraction " +
		"s_0^j ∘ σ ∘ d_0^j are simplicial through the conjuncts alone. The augmentation needs " +
		"no conjunct of its own: that ε d_0 = ε d_1 on X(1) is ExtraDegeneracyCoequalizes.",
})}

// SimplicialFrontDegeneracyDef — `simplicial_front_degeneracy(s, n, k, x)`:
// s_0 applied k times to the n-simplex x, starting at dimension n, the
// (n + k)-simplex that repeats the first vertex of x k more times. From
// a vertex it is simplicial_set's base simplex:
// `simplicial_front_degeneracy(s, 0, k, x)` and `base_simplex(s, x, k)`
// unfold to the same k-simplex.
var SimplicialFrontDegeneracyDef = simplicialFrontDegeneracyDefThm{family.Define(registry.DefEntry{
	Name:  "SimplicialFrontDegeneracyDef",
	Key:   "prop_fc089038ae3586c",
	Const: "simplicial_front_degeneracy",
	Type:  "(num → num → A → A) → num → num → A → A",
	Equations: []string{
		"∀s:(num → num → A → A). ∀n:num. ∀x:A. simplicial_front_degeneracy(s, n, 0, x) = x",
		"∀s:(num → num → A → A). ∀n k:num. ∀x:A. " +
			"    simplicial_front_degeneracy(s, n, suc(k), x) = " +
			"    s(n + k, 0, simplicial_front_degeneracy(s, n, k, x))",
	},
})}

// ExtraDegeneracyCoequalizes — the augmentation takes one value on the two
// vertices of an edge: at the 2-simplex σ_1 x the face identity
// d_1 d_2 = d_1 d_1, read through the face identities of σ and the bottom
// identity, joins b(ε(d_1 x)) to b(ε(d_0 x)), and ε ∘ b = id on S cancels b.
var ExtraDegeneracyCoequalizes = extraDegeneracyCoequalizesThm{family.Add(registry.ProofEntry{
	Name:    "ExtraDegeneracyCoequalizes",
	Key:     "prop_42d6b531a7981437",
	Reading: "ε ∘ b = id on S is load-bearing: without it ε may part the two vertices of an edge.",
	Build: ExtraDegeneracy.Law(Statement{
		Binders: "∀x:A.",
		Hypotheses: []string{
			"x ∈ X.simplices(1)",
		},
		Conclusion: "ε(X.d(1, 0, x)) = ε(X.d(1, 1, x))",
	},
		func(a *Argument, extra ExtraDegeneracyFact[on.S], x *Expr[A], edge Fact) {
			given := a.Conjuncts(
				a.Unfolded(extra, ExtraDegeneracy),
				"X is a simplicial set",
				"ε carries the vertices into S",
				"b carries S into the vertices",
				"σ raises the dimension by one",
				"ε ∘ b is the identity on S",
				"the bottom identity d_1 σ_0 = b ∘ ε",
				"d_0 σ is the identity",
				"the face identity d_{i+1} σ = σ d_i",
				"the degeneracy identity s_{j+1} σ = σ s_j")
			simplicial, intoS, raise, section, bottom, faceσ :=
				given[0], given[1], given[3], given[4], given[5], given[7]
			zero, one, two := a.TermAs[Nat]("0"), a.TermAs[Nat]("1"), a.TermAs[Nat]("2")
			d0x, d1x := a.TermAs[A]("X.d(1, 0, x)"), a.TermAs[A]("X.d(1, 1, x)")
			vertices := a.Have(
				"both vertices of the edge are 0-simplices",
				"X.d(1, 0, x) ∈ X.simplices(0) ∧ X.d(1, 1, x) ∈ X.simplices(0)",
				By(
					edge,
					simplicial_set.FaceIn.Read(simplicial).At(zero, zero, x),
					simplicial_set.FaceIn.Read(simplicial).At(zero, one, x)))
			faces := a.Have(
				"σ_1 x has the faces σ_0 d_0 x and σ_0 d_1 x",
				"X.d(2, 1, σ(1, x)) = σ(0, X.d(1, 0, x)) ∧ X.d(2, 2, σ(1, x)) = σ(0, X.d(1, 1, x))",
				By(edge, faceσ.At(zero, zero, x), faceσ.At(zero, one, x)))
			agree := a.Have(
				"b ∘ ε takes one value on the two vertices",
				"b(ε(X.d(1, 1, x))) = b(ε(X.d(1, 0, x)))",
				CalcEq(
					Leg(
						a.TermAs[A]("X.d(1, 1, σ(0, X.d(1, 1, x)))"),
						"the bottom identity at d_1 x",
						By(vertices, bottom.At(d1x))),
					Leg(
						a.TermAs[A]("X.d(1, 1, X.d(2, 2, σ(1, x)))"),
						"d_2 σ_1 x = σ_0 d_1 x",
						By(faces)),
					Leg(
						a.TermAs[A]("X.d(1, 1, X.d(2, 1, σ(1, x)))"),
						"d_1 d_2 = d_1 d_1 at the 2-simplex σ_1 x",
						By(
							edge,
							raise.At(one, x),
							simplicial_set.FaceFace.Read(simplicial).At(zero, one, two, a.TermAs[A]("σ(1, x)")))),
					Leg(
						a.TermAs[A]("X.d(1, 1, σ(0, X.d(1, 0, x)))"),
						"d_1 σ_1 x = σ_0 d_0 x",
						By(faces)),
					FinalLeg(
						"the bottom identity at d_0 x",
						By(vertices, bottom.At(d0x)))))
			a.Show(
				"apply ε and cancel b by ε ∘ b = id on S",
				CalcEq(
					Leg(
						a.TermAs[C]("ε(b(ε(X.d(1, 0, x))))"),
						"ε ∘ b = id at ε(d_0 x), a point of S",
						By(vertices, intoS.At(d0x), section.At(a.TermAs[C]("ε(X.d(1, 0, x))")))),
					Leg(
						a.TermAs[C]("ε(b(ε(X.d(1, 1, x))))"),
						"b ∘ ε takes one value on the two vertices",
						By(agree)),
					FinalLeg(
						"ε ∘ b = id at ε(d_1 x), a point of S",
						By(vertices, intoS.At(d1x), section.At(a.TermAs[C]("ε(X.d(1, 1, x))"))))))
		}),
})}

// ---------------------------------------------------------------------------
// The degenerate section and the contraction of an extra degeneracy
// ---------------------------------------------------------------------------

// ExtraDegeneracySection — the degenerate section: c ↦ base_simplex(s,
// b(c), n), the vertex b(c) degenerated n times by s_0, is a simplicial
// map from the constant simplicial set on S to X, and ε of its last
// vertex is c.
var ExtraDegeneracySection = extraDegeneracySectionThm{family.Add(registry.ProofEntry{
	Name: "ExtraDegeneracySection",
	Key:  "prop_73e552c4739f8797",
	Reading: "No conjunct about σ is read: the section is built from b and s_0 alone, so it is " +
		"simplicial by the simplicial identities and reads of the extra degeneracy only b's closure " +
		"and ε ∘ b = id. S = ∅ forces X(0) = ∅ through the closure of ε, so every X(n) = ∅. The " +
		"iterated extra degeneracy c ↦ σ^n(b(c)) is no section in general: it commutes with s_0 only " +
		"through s_0 σ = σσ, which extra_degeneracy does not hold and the standard resolution's σ fails.",
	Deps: []registry.EntryLike{
		ExtraDegeneracy,
		simplicial_set.FaceIterateBottomDef,
		simplicial_set.ConstantSimplicialSet,
		simplicial_set.SimplicialMap,
		simplicial_set.BaseSimplexDef,
		simplicial_set.BaseSimplexIn,
		simplicial_set.BaseSimplexFace,
		simplicial_set.BaseSimplexDegeneracy,
	},
	Build: family.Card(ExtraDegeneracy.Statement(
		"simplicial_map(constant_simplicial_set(S), X, λn:num. λc:C. base_simplex(b(c), n)) ∧ "+
			"(∀n:num. ∀c:C. c ∈ S ⇒ ε(face_iterate_bottom(n, n, base_simplex(b(c), n))) = c)"),
		"b(c) is a vertex of X (the closure of b), so its base simplex lies in X(n) (BaseSimplexIn), "+
			"each face of it is the base simplex one dimension down (BaseSimplexFace) and each degeneracy "+
			"the one up (BaseSimplexDegeneracy): against the identity faces and degeneracies of the "+
			"constant simplicial set (ConstantSimplicialSet) these are the conditions of SimplicialMap. "+
			"By induction on k ≤ n, d_0^k of the base simplex at n is the base simplex at n − k "+
			"(FaceIterateBottomDef, BaseSimplexFace), so the last vertex is b(c), and ε ∘ b = id on S"),
})}

// ExtraDegeneracyHomotopy — h_j = s_0^j ∘ σ ∘ d_0^j, which on an
// n-simplex x lifts the back face d_0^j x, an (n − j)-simplex, by σ and
// degenerates the result j times by s_0, is a simplicial homotopy from
// the identity of X to the section after the augmentation,
// x ↦ base_simplex(s, b(ε(last vertex of x)), n).
var ExtraDegeneracyHomotopy = extraDegeneracyHomotopyThm{family.Add(registry.ProofEntry{
	Name: "ExtraDegeneracyHomotopy",
	Key:  "prop_49972f6d0ff11954",
	Reading: "s_0 σ = σσ is not needed: at May's s_i h_j = h_{j+1} s_i for i ≤ j, where the " +
		"classical contraction σ^{j+1} ∘ d_0^j meets s_0 σ, the j front degeneracies of h_j absorb " +
		"s_i (s_i s_0^j = s_0^{j+1}) and the extra d_0 of h_{j+1} cancels it (d_0^{j+1} s_i = d_0^j). " +
		"The extra degeneracy is read through d_0 σ = id at h_0, the bottom identity d_1 σ_0 = b ∘ ε " +
		"at h_n, and d_{i+1} σ = σ d_i, s_{j+1} σ = σ s_j at the faces and degeneracies past the " +
		"front j: at n = 0, h_0 = σ_0 with ends d_0 σ_0 = id and d_1 σ_0 = b ∘ ε, and in general each " +
		"of May's identities reads at most one identity of the extra degeneracy beside simplicial " +
		"identities of X. d_1 σ = σ d_0 applies at d_{j+1} h_{j+1} = d_{j+1} h_j because j < n keeps " +
		"σ above degree 0 there; the second end is simplicial only through ExtraDegeneracyCoequalizes.",
	Deps: []registry.EntryLike{
		ExtraDegeneracy,
		SimplicialFrontDegeneracyDef,
		simplicial_set.FaceIterateBottomDef,
		SimplicialHomotopy,
		ExtraDegeneracySection,
		ExtraDegeneracyCoequalizes,
		simplicial_set.BaseSimplexDef,
		simplicial_set.FaceFace,
		simplicial_set.DegeneracyDegeneracy,
		simplicial_set.FaceDegeneracyBelow,
		simplicial_set.FaceDegeneracyEqual,
		simplicial_set.FaceDegeneracyNext,
		simplicial_set.FaceDegeneracyAbove,
		simplicial_set.MapIdentity,
		simplicial_set.MapCompose,
	},
	Build: family.Card(ExtraDegeneracy.Statement(
		"simplicial_homotopy(X, "+
			"    X, "+
			"    λn:num. λx:A. x, "+
			"    λn:num. λx:A. base_simplex(b(ε(face_iterate_bottom(n, n, x))), n), "+
			"    λn:num. λj:num. λx:A. "+
			"        simplicial_front_degeneracy(X.s, n - j + 1, j, σ(n - j, face_iterate_bottom(n, j, x))))"),
		"four moves, each by induction on j from the simplicial identities (FaceFace, "+
			"DegeneracyDegeneracy, FaceDegeneracyBelow, FaceDegeneracyEqual, FaceDegeneracyNext, "+
			"FaceDegeneracyAbove), carry a face or a degeneracy past s_0^j or d_0^j: d_i s_0^j = s_0^{j−1} "+
			"for i ≤ j and s_0^j d_{i−j} for i > j; s_i s_0^j = s_0^{j+1} for i ≤ j and s_0^j s_{i−j} for "+
			"i > j; d_0^j d_i = d_0^{j+1} for i ≤ j and d_{i−j} d_0^j for i > j; d_0^{j+1} s_i = d_0^j for "+
			"i ≤ j and d_0^j s_i = s_{i−j} d_0^j for i ≥ j. With them d_0 h_0 = d_0 σ = id; d_{n+1} h_n = "+
			"s_0^n d_1 σ_0 d_0^n, the base simplex at b(ε(d_0^n x)) by the bottom identity (s_0^n from a "+
			"vertex is BaseSimplexDef's recursion); d_i h_j = h_{j−1} d_i (i < j) and s_i h_j = h_{j+1} "+
			"s_i (i ≤ j) by the moves alone; d_{j+1} h_{j+1} = s_0^j σ d_0^{j+1} = d_{j+1} h_j by d_1 σ = "+
			"σ d_0; d_i h_j = h_j d_{i−1} (i > j + 1) by d_{i−j} σ = σ d_{i−j−1}; s_i h_j = h_j s_{i−1} (i "+
			"> j) by s_{i−j} σ = σ s_{i−j−1}. The ends are simplicial maps: the identity (MapIdentity), "+
			"and the augmentation of the last vertex, simplicial into the constant simplicial set by "+
			"ExtraDegeneracyCoequalizes, followed by ExtraDegeneracySection (MapCompose)"),
})}

// ExtraDegeneracyHomotopyEquivalence — the augmentation, ε of the last
// vertex, is a simplicial homotopy equivalence from X to the constant
// simplicial set on S, the degenerate section its inverse.
var ExtraDegeneracyHomotopyEquivalence = extraDegeneracyHomotopyEquivalenceThm{family.Add(registry.ProofEntry{
	Name: "ExtraDegeneracyHomotopyEquivalence",
	Key:  "prop_e19480ec1c1a7e47",
	Reading: "On the side of S the augmentation after the degenerate section is the identity only on " +
		"S, not as a function of C, which suffices because the trivial homotopy reads its ends only on S.",
	Deps: []registry.EntryLike{
		SimplicialHomotopyEquivalenceDef,
		SimplicialMapsHomotopicDef,
		SimplicialHomotopy,
		ExtraDegeneracySection,
		ExtraDegeneracyHomotopy,
		ExtraDegeneracyCoequalizes,
		simplicial_set.ConstantSimplicialSet,
		simplicial_set.FaceIterateBottomDef,
		simplicial_set.FaceFace,
		simplicial_set.FaceDegeneracyBelow,
		simplicial_set.FaceDegeneracyEqual,
		simplicial_set.MapCompose,
	},
	Build: family.Card(ExtraDegeneracy.Statement(
		"simplicial_homotopy_equivalence(X, "+
			"    constant_simplicial_set(S), "+
			"    λn:num. λx:A. ε(face_iterate_bottom(n, n, x)))"),
		"the augmentation is a simplicial map to the constant simplicial set: a degeneracy and a face "+
			"d_i with i ≤ n keep the last vertex of an (n + 1)-simplex x (FaceFace, FaceDegeneracyBelow, "+
			"FaceDegeneracyEqual), and the last vertex of d_{n+1} x is the other vertex of the last edge "+
			"d_0^n x, on whose two vertices ε agrees (ExtraDegeneracyCoequalizes). Its inverse is the "+
			"degenerate section (ExtraDegeneracySection): augmentation after section is the identity on "+
			"S, joined to it in one step by the homotopy λn j c. c, and section after augmentation is "+
			"joined to the identity of X by ExtraDegeneracyHomotopy"),
})}
