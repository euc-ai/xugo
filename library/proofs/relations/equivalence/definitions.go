// definitions.go — the chapter's definitional layer: the three
// properties a relation can have and their conjunction, the
// equivalence, as the structure whose one component is the relation;
// the equivalence on a SET, the structure the whole-type one is the case
// c = 𝕌 of, with its axioms, the view that reads them on the whole type,
// and symmetry on a set by itself; the class of a point; the restriction
// of a relation to a set and the quotient of the set by it, with the
// lift of a map to the classes; and, on the other side of the
// correspondence, a partition of the type and the relation it induces.

package equivalence

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The equivalence relation
// ---------------------------------------------------------------------------

// ReflexiveDef — every point stands in the relation to itself.
var ReflexiveDef = reflexiveDefThm{family.Define(registry.DefEntry{
	Name:      "ReflexiveDef",
	Key:       "prop_8f6e94fed7d3ce0d",
	Const:     "reflexive",
	Type:      "(A → A → bool) → bool",
	Equations: []string{"∀R:(A → A → bool). reflexive(R) ⇔ ∀x:A. R(x, x)"},
})}

// SymmetricDef — the relation reads the same backwards.
var SymmetricDef = symmetricDefThm{family.Define(registry.DefEntry{
	Name:      "SymmetricDef",
	Key:       "prop_d1b5de9285ea2444",
	Const:     "symmetric",
	Type:      "(A → A → bool) → bool",
	Equations: []string{"∀R:(A → A → bool). symmetric(R) ⇔ ∀x y:A. R(x, y) ⇒ R(y, x)"},
})}

// TransitiveDef — two steps of the relation are one.
var TransitiveDef = transitiveDefThm{family.Define(registry.DefEntry{
	Name:      "TransitiveDef",
	Key:       "prop_545396f835d1076",
	Const:     "transitive",
	Type:      "(A → A → bool) → bool",
	Equations: []string{"∀R:(A → A → bool). transitive(R) ⇔ ∀x y z:A. R(x, y) ∧ R(y, z) ⇒ R(x, z)"},
})}

// Equivalence — an equivalence relation: all three at once. The
// structure's one component is the relation, so a law here is stated
// `equivalence(R) ⇒ body` and its proof receives the hypothesis. It is
// the equivalence on the set 𝕌 (EquivalenceOnUniverse), and its three
// laws below are the axioms of the equivalence on a set read there.
var Equivalence = equivalenceThm{family.DefineStructure(registry.DefEntry{
	Name:    "Equivalence",
	Key:     "prop_50ca6ba84afcf428",
	Const:   "equivalence",
	Subject: "R",
	Type:    "(A → A → bool) → bool",
	Equations: []string{
		"∀R:(A → A → bool). equivalence(R) ⇔ reflexive(R) ∧ symmetric(R) ∧ transitive(R)",
	},
	Deps: []registry.EntryLike{ReflexiveDef, SymmetricDef, TransitiveDef},
})}

// Reflexive — every point is related to itself: ReflexiveOn on the
// whole type.
var Reflexive = reflexiveThm{family.Add(registry.ProofEntry{
	Name:  "Reflexive",
	Key:   "prop_47d2beda35024b86",
	Build: EquivalenceAtUniverse.Law("∀x:A. R(x, x)", ReflexiveOn),
})}

// Symmetric — a related pair is related the other way round:
// SymmetricOn on the whole type.
var Symmetric = symmetricThm{family.Add(registry.ProofEntry{
	Name: "Symmetric",
	Key:  "prop_cb80f8a0e22c9b31",
	Build: EquivalenceAtUniverse.Law(Statement{
		Binders: "∀x y:A.",
		Hypotheses: []string{
			"R(x, y)",
		},
		Conclusion: "R(y, x)",
	}, SymmetricOn),
})}

// Transitive — two related pairs sharing their middle point make one:
// TransitiveOn on the whole type.
var Transitive = transitiveThm{family.Add(registry.ProofEntry{
	Name: "Transitive",
	Key:  "prop_12fbde5ad4fa6fa9",
	Build: EquivalenceAtUniverse.Law(Statement{
		Binders: "∀x y z:A.",
		Hypotheses: []string{
			"R(x, y)",
			"R(y, z)",
		},
		Conclusion: "R(x, z)",
	}, TransitiveOn),
})}

// ---------------------------------------------------------------------------
// The equivalence on a set
// ---------------------------------------------------------------------------

// EquivalenceOn — `equivalence_on(c, R)`: an equivalence relation on the
// set c rather than on the whole type — the three axioms asked of the
// points of c and of nothing outside it. The whole-type equivalence is
// the case c = 𝕌 (EquivalenceOnUniverse). What the relation does off c
// is not asked, so a relation an algebraic chapter defines on the type —
// "differ by a member of the subgroup", "have equal cross products" —
// is an equivalence on the carrier it is read at, and its quotient
// there is the quotient of the set (QuotientOnDef). The set comes first,
// as on every structure on a set and in the constants built over this
// one — relation_on, quotient_on, respects_on.
var EquivalenceOn = equivalenceOnThm{family.DefineStructure(registry.DefEntry{
	Name:    "EquivalenceOn",
	Key:     "prop_e6fec4b467e9024f",
	Const:   "equivalence_on",
	Subject: "c",
	Type:    "set(A) → (A → A → bool) → bool",
	Equations: []string{"∀c:set(A). ∀R:(A → A → bool). " +
		"    equivalence_on(c, R) ⇔ " +
		"    (∀x:A. x ∈ c ⇒ R(x, x)) ∧ " +
		"    (∀x y:A. x ∈ c ∧ y ∈ c ⇒ R(x, y) ⇒ R(y, x)) ∧ " +
		"    (∀x y z:A. x ∈ c ∧ y ∈ c ∧ z ∈ c ⇒ R(x, y) ∧ R(y, z) ⇒ R(x, z))"},
})}

// ReflexiveOn — a point of c is related to itself.
var ReflexiveOn = reflexiveOnThm{family.Add(registry.ProofEntry{
	Name: "ReflexiveOn",
	Key:  "prop_e450d40857a4e01b",
	Build: EquivalenceOn.Axiom(Statement{
		Binders: "∀x:A.",
		Hypotheses: []string{
			"x ∈ c",
		},
		Conclusion: "R(x, x)",
	}),
})}

// SymmetricOn — a related pair of points of c is related the other way
// round.
var SymmetricOn = symmetricOnThm{family.Add(registry.ProofEntry{
	Name: "SymmetricOn",
	Key:  "prop_73bc82dd143b6a7c",
	Build: EquivalenceOn.Axiom(Statement{
		Binders: "∀x y:A.",
		Hypotheses: []string{
			"x ∈ c",
			"y ∈ c",
			"R(x, y)",
		},
		Conclusion: "R(y, x)",
	}),
})}

// TransitiveOn — two related pairs of points of c sharing their middle
// point make one.
var TransitiveOn = transitiveOnThm{family.Add(registry.ProofEntry{
	Name: "TransitiveOn",
	Key:  "prop_2c4d092368d5db05",
	Build: EquivalenceOn.Axiom(Statement{
		Binders: "∀x y z:A.",
		Hypotheses: []string{
			"x ∈ c",
			"y ∈ c",
			"z ∈ c",
			"R(x, y)",
			"R(y, z)",
		},
		Conclusion: "R(x, z)",
	}),
})}

// EquivalenceOnUniverse — an equivalence on the whole type is an
// equivalence: every membership in 𝕌 holds, so the guarded axioms are
// the three properties.
var EquivalenceOnUniverse = equivalenceOnUniverseThm{family.Add(registry.ProofEntry{
	Name: "EquivalenceOnUniverse",
	Key:  "prop_26d3457998365788",
	Build: family.Theorem("∀R:(A → A → bool). equivalence(R) ⇔ equivalence_on(𝕌, R)",
		func(a *Argument, R *Arrow2[A, A, Bool]) {
			a.Show(
				"with every membership in 𝕌 true, the two predicates unfold to the same three properties",
				Unfold(Equivalence),
				Unfold(ReflexiveDef),
				Unfold(SymmetricDef),
				Unfold(TransitiveDef),
				Unfold(EquivalenceOn),
				Simp(Fwd(set_basic.InUniv)),
				Basic())
		}),
})}

// EquivalenceAtUniverse — the whole-type equivalence is the equivalence
// on 𝕌: a law is proved once on the set, and the whole-type member is
// its view through this door, the carrier read as 𝕌 and each guard
// discharged by InUniv (constitution §Structures, "One proof per law").
var EquivalenceAtUniverse = Equivalence.AtUniverse(
	EquivalenceOn, EquivalenceOnUniverse, set_basic.InUniv, set_order.SubsetUniv)

// EquivalenceOnMono — an equivalence on c is one on every part of c.
var EquivalenceOnMono = equivalenceOnMonoThm{family.Add(registry.ProofEntry{
	Name: "EquivalenceOnMono",
	Key:  "prop_1d4ceedf7a9e2673",
	Build: EquivalenceOn.Law(Statement{
		Binders: "∀d:set(A).",
		Hypotheses: []string{
			"d ⊆ c",
		},
		Conclusion: "equivalence_on(d, R)",
	},
		func(
			a *Argument,
			c *Expr[Set[A]],
			R *Arrow2[A, A, Bool],
			equiv EquivalenceFact[on.C],
			d *Expr[Set[A]],
			within Fact,
		) {
			inclusion := a.Unfolded(within, set_basic.SubsetDef)
			// The three axioms are had before the goal is opened: unfolding
			// equivalence_on rewrites the resident hypothesis too.
			reflexive := a.Have(
				"R is reflexive on c",
				"∀x:A. x ∈ c ⇒ R(x, x)",
				By(ReflexiveOn, equiv))
			symmetric := a.Have(
				"symmetric on c",
				"∀x y:A. x ∈ c ∧ y ∈ c ⇒ R(x, y) ⇒ R(y, x)",
				By(SymmetricOn, equiv))
			transitive := a.Have(
				"and transitive on c",
				"∀x y z:A. x ∈ c ∧ y ∈ c ∧ z ∈ c ⇒ R(x, y) ∧ R(y, z) ⇒ R(x, z)",
				By(TransitiveOn, equiv))
			a.Do(Unfold(EquivalenceOn), SplitConjAll(
				Case(
					"reflexive on d: a point of d is one of c",
					By(inclusion, reflexive)),
				Case(
					"symmetric on d: two points of d are points of c",
					By(inclusion, symmetric)),
				Case(
					"transitive on d: three points of d are points of c",
					By(inclusion, transitive)),
			))
		}),
})}

// SymmetricOnDef — `symmetric_on(c, R)`: the relation reads the same
// backwards between points of the set c, whatever it does off c — the
// symmetry axiom of EquivalenceOn on its own.
var SymmetricOnDef = symmetricOnDefThm{family.Define(registry.DefEntry{
	Name:  "SymmetricOnDef",
	Key:   "prop_20e2c7a97b751a11",
	Const: "symmetric_on",
	Type:  "set(A) → (A → A → bool) → bool",
	Equations: []string{
		"∀c:set(A). ∀R:(A → A → bool). symmetric_on(c, R) ⇔ ∀x y:A. x ∈ c ∧ y ∈ c ∧ R(x, y) ⇒ R(y, x)",
	},
})}

// ---------------------------------------------------------------------------
// The class of a point
// ---------------------------------------------------------------------------

// EquivalenceClassDef — `equivalence_class(R, x)`: the points related
// to x. Defined for any relation; what the definition gives an
// equivalence is the subject of the chapter.
var EquivalenceClassDef = equivalenceClassDefThm{family.Define(registry.DefEntry{
	Name:      "EquivalenceClassDef",
	Key:       "prop_cdc405e23aa13a8e",
	Const:     "equivalence_class",
	Type:      "(A → A → bool) → A → set(A)",
	Equations: []string{"∀R:(A → A → bool). ∀x:A. equivalence_class(R, x) = {y:A | R(x, y)}"},
})}

// ---------------------------------------------------------------------------
// The quotient of a set
// ---------------------------------------------------------------------------

// RelationOnDef — `relation_on(c, R)`: the relation R restricted to the
// set c — two points are related when both lie in c and R relates them.
// The class of a point of c under the restriction is its class inside
// c, whatever R does outside; the quotient of c by R is made of these.
var RelationOnDef = relationOnDefThm{family.Define(registry.DefEntry{
	Name:  "RelationOnDef",
	Key:   "prop_e68c6f0ce17db291",
	Const: "relation_on",
	Type:  "set(A) → (A → A → bool) → A → A → bool",
	Equations: []string{
		"∀c:set(A). ∀R:(A → A → bool). ∀x y:A. relation_on(c, R, x, y) ⇔ x ∈ c ∧ y ∈ c ∧ R(x, y)",
	},
})}

// QuotientOnDef — `quotient_on(c, R)`: the quotient of the set c by the
// relation R — the classes, inside c, of the points of c. It is a set of
// subsets of c for any relation; under `equivalence_on(c, R)` its members
// partition c and two points of c have one class exactly when R relates
// them (QuotientOnCovers, ClassOnEqIff). A quotient the corpus builds —
// the cosets of a subgroup, the fractions of a ring, the homotopy
// classes of spheres — is this constant at its relation.
var QuotientOnDef = quotientOnDefThm{family.Define(registry.DefEntry{
	Name:  "QuotientOnDef",
	Key:   "prop_520e238f0055bba0",
	Const: "quotient_on",
	Type:  "set(A) → (A → A → bool) → set(set(A))",
	Equations: []string{
		"∀c:set(A). ∀R:(A → A → bool). quotient_on(c, R) = image(equivalence_class(relation_on(c, R)), c)",
	},
	Deps: []registry.EntryLike{EquivalenceClassDef, RelationOnDef},
})}

// ---------------------------------------------------------------------------
// The lift of a map to the classes
// ---------------------------------------------------------------------------

// RespectsOnDef — `respects_on(c, R, f)`: f takes one value on related
// points of c. It is what a map must do to descend to the quotient: its
// induced map on a class is then the value at any member (InducedMapClass).
var RespectsOnDef = respectsOnDefThm{family.Define(registry.DefEntry{
	Name:  "RespectsOnDef",
	Key:   "prop_f43a728e4241190",
	Const: "respects_on",
	Type:  "set(A) → (A → A → bool) → (A → B) → bool",
	Equations: []string{
		"∀c:set(A). ∀R:(A → A → bool). ∀f:(A → B). " +
			"    respects_on(c, R, f) ⇔ ∀x y:A. x ∈ c ∧ y ∈ c ∧ R(x, y) ⇒ f(x) = f(y)",
	},
})}

// InducedMapDef — `induced_map(f, s)`: the value of f at a chosen member
// of s. On a class of a relation f respects the choice does not matter —
// f takes one value on the whole class (InducedMapClass) — and the map so
// defined on the quotient is the lift of f.
var InducedMapDef = inducedMapDefThm{family.Define(registry.DefEntry{
	Name:      "InducedMapDef",
	Key:       "prop_a699cc0cbad6528c",
	Const:     "induced_map",
	Type:      "(A → B) → set(A) → B",
	Equations: []string{"∀f:(A → B). ∀s:set(A). induced_map(f, s) = f(εx:A. x ∈ s)"},
})}

// ---------------------------------------------------------------------------
// Partitions
// ---------------------------------------------------------------------------

// SetPartition — a family of sets partitions the type: no block is
// empty, every point lies in a block, and two blocks that share a point
// are one block. The structure's one component is the family, and its
// three axioms below are the three clauses.
var SetPartition = setPartitionThm{family.DefineStructure(registry.DefEntry{
	Name:    "SetPartition",
	Key:     "prop_f15e087214d27b59",
	Const:   "set_partition",
	Subject: "P",
	Type:    "set(set(A)) → bool",
	Equations: []string{"∀P:set(set(A)). " +
		"    set_partition(P) ⇔ " +
		"    (∀c:set(A). c ∈ P ⇒ c ≠ ∅) ∧ " +
		"    (∀x:A. ∃c:set(A). c ∈ P ∧ x ∈ c) ∧ " +
		"    (∀c d:set(A). ∀x:A. c ∈ P ∧ d ∈ P ∧ x ∈ c ∧ x ∈ d ⇒ c = d)"},
})}

// BlockNonempty — no block of a partition is empty.
var BlockNonempty = blockNonemptyThm{family.Add(registry.ProofEntry{
	Name: "BlockNonempty",
	Key:  "prop_c60d7c41f357bf7",
	Build: SetPartition.Axiom(Statement{
		Binders: "∀c:set(A).",
		Hypotheses: []string{
			"c ∈ P",
		},
		Conclusion: "c ≠ ∅",
	}),
})}

// BlocksCover — every point lies in some block.
var BlocksCover = blocksCoverThm{family.Add(registry.ProofEntry{
	Name:  "BlocksCover",
	Key:   "prop_c3b0ba950bfc972",
	Build: SetPartition.Axiom("∀x:A. ∃c:set(A). c ∈ P ∧ x ∈ c"),
})}

// BlocksOverlapEqual — two blocks that share a point are one block.
var BlocksOverlapEqual = blocksOverlapEqualThm{family.Add(registry.ProofEntry{
	Name: "BlocksOverlapEqual",
	Key:  "prop_134123023312ebdb",
	Build: SetPartition.Axiom(Statement{
		Binders: "∀c d:set(A). ∀x:A.",
		Hypotheses: []string{
			"c ∈ P",
			"d ∈ P",
			"x ∈ c",
			"x ∈ d",
		},
		Conclusion: "c = d",
	}),
})}

// SameBlockDef — `same_block(P, x, y)`: the relation a family of sets
// induces, two points related when some block holds both. Defined for
// any family; that it is an equivalence when the family is a partition
// is the chapter's theorem in the other direction.
var SameBlockDef = sameBlockDefThm{family.Define(registry.DefEntry{
	Name:  "SameBlockDef",
	Key:   "prop_880517486e7ca9f9",
	Const: "same_block",
	Type:  "set(set(A)) → A → A → bool",
	Equations: []string{
		"∀P:set(set(A)). ∀x y:A. same_block(P, x, y) ⇔ ∃c:set(A). c ∈ P ∧ x ∈ c ∧ y ∈ c",
	},
})}
