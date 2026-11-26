// definitions.go — the constants the quotient group is built from — the
// product and the inverse of SETS of group elements, and the set of left
// cosets of a subgroup by the points of a carrier, the quotient of the
// carrier by the coset relation — each followed by the reading of
// membership in the set it builds, which every later member reads the set
// through, and by the law that the set a group on c builds from subsets
// of c lies in c.

package quotient_group

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/relations/equivalence"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/registry"
)

// SetMulDef — `set_mul(mul, s, t)`: the product of two sets of group
// elements, the products x * y with x from s and y from t. It is the
// quotient group's operation: the product of two cosets of a normal
// subgroup is a coset again (LeftCosetMul). Nothing is chosen — the
// product is the set of all the products, not the coset of a
// representative. A group record supplies its operation as `set_mul(G.mul, s, t)`.
var SetMulDef = setMulDefThm{family.Define(registry.DefEntry{
	Name:     "SetMulDef",
	Key:      "prop_1f6404f0aada958c",
	Const:    "set_mul",
	Type:     "(A → A → A) → set(A) → set(A) → set(A)",
	Implicit: []string{"mul"},
	Equations: []string{
		"∀mul:(A → A → A). ∀s t:set(A). set_mul(mul, s, t) = {mul(x, y) | x:A, y:A | x ∈ s ∧ y ∈ t}",
	},
})}

// SetMulMono — the product of sets grows with its right factor. Stated
// for any operation, no group.
var SetMulMono = setMulMonoThm{family.Add(registry.ProofEntry{
	Name: "SetMulMono",
	Key:  "prop_cbcc20a98924a695",
	Deps: []registry.EntryLike{InSetMul, set_basic.SubsetDef},
	Build: family.Card(Statement{
		Binders: "∀mul:(A → A → A). ∀s t t':set(A).",
		Hypotheses: []string{
			"t ⊆ t'",
		},
		Conclusion: "set_mul(mul, s, t) ⊆ set_mul(mul, s, t')",
	},
		"a point x * y with y ∈ t has y ∈ t'"),
})}

// SetMulAssoc — the product of sets inside a group on c is associative:
// each side is the set of x * y * z.
var SetMulAssoc = setMulAssocThm{family.Add(registry.ProofEntry{
	Name: "SetMulAssoc",
	Key:  "prop_ec43fef0fff4a8b5",

	Deps: []registry.EntryLike{InSetMul, group.AssocOn, set_basic.ExtensionWithin, SetMulIn},
	Build: family.Card(group.GroupOn.Statement(Statement{
		Binders: "∀s t u:set(A).",
		Hypotheses: []string{
			"s ⊆ G.carrier",
			"t ⊆ G.carrier",
			"u ⊆ G.carrier",
		},
		Conclusion: "set_mul(s, set_mul(t, u)) = set_mul(set_mul(s, t), u)",
	}),
		"both sides lie in G.carrier (SetMulIn); a point x * (y * z) is "+
			"(x * y) * z by AssocOn at the three points of G.carrier, and back"),
})}

// InSetMul — a point lies in the product of two sets exactly when it is
// the product of a member of each: the comprehension read off. Stated
// for any operation, no group.
var InSetMul = inSetMulThm{family.Add(registry.ProofEntry{
	Name: "InSetMul",
	Key:  "prop_68792cccf0d38e47",
	Build: family.Theorem("∀mul:(A → A → A). ∀s t:set(A). ∀z:A. "+
		"    z ∈ set_mul(mul, s, t) ⇔ ∃x y:A. x ∈ s ∧ y ∈ t ∧ z = mul(x, y)",
		func(a *Argument, mul *Arrow2[A, A, A], s, t *Expr[Set[A]], z *Expr[A]) {
			a.Show(
				"a point of the comprehension is a product of a member of s and a member of t, and conversely",
				Unfold(SetMulDef),
				BySets())
		}),
})}

// SetInvDef — `set_inv(inv, s)`: the inverses of the members of a set.
// It is the quotient group's inverse: the inverses of a coset of a
// normal subgroup form a coset (LeftCosetInv). The inverse map is
// supplied by the record in a group law: `set_inv(G.inv, s)`.
var SetInvDef = setInvDefThm{family.Define(registry.DefEntry{
	Name:      "SetInvDef",
	Key:       "prop_b08ece0948756f0f",
	Const:     "set_inv",
	Type:      "(A → A) → set(A) → set(A)",
	Implicit:  []string{"inv"},
	Equations: []string{"∀inv:(A → A). ∀s:set(A). set_inv(inv, s) = image(inv, s)"},
})}

// SetMulIn — the product of two subsets of the carrier lies in the
// carrier: each of its points is a product of two points of c.
var SetMulIn = setMulInThm{family.Add(registry.ProofEntry{
	Name: "SetMulIn",
	Key:  "prop_54ed059977d3c519",

	Build: group.GroupOn.Law(Statement{
		Binders: "∀s t:set(A).",
		Hypotheses: []string{
			"s ⊆ G.carrier",
			"t ⊆ G.carrier",
		},
		Conclusion: "set_mul(s, t) ⊆ G.carrier",
	},
		func(a *Argument, grp group.GroupFact[on.G], s, t *Expr[Set[A]], given Fact) {
			parts := a.Conjuncts(
				given,
				"s lies in G.carrier",
				"so does t")
			sInC, tInC := a.Unfolded(parts[0], set_basic.SubsetDef), a.Unfolded(parts[1], set_basic.SubsetDef)
			a.Do(Unfold(set_basic.SubsetDef))
			a.FixAs[A]("z")
			member := a.Assume()
			_, _, product := a.Unpack2As[A, A](a.Have(
				"z is x * y with x in s and y in t",
				"∃x y:A. x ∈ s ∧ y ∈ t ∧ z = x * y",
				By(member, InSetMul)), "x", "y")
			factors := a.Conjuncts(
				product,
				"x lies in s",
				"y lies in t",
				"z is x * y")
			a.Show(
				"so z is a product of two points of G.carrier",
				factors[2].Rw(),
				By(group.MulIn, grp, sInC, tInC, factors[0], factors[1]))
		}),
})}

// SetInvIn — the inverses of a subset of the carrier lie in the
// carrier.
var SetInvIn = setInvInThm{family.Add(registry.ProofEntry{
	Name: "SetInvIn",
	Key:  "prop_86e6195cb47b39ea",

	Build: group.GroupOn.Law(Statement{
		Binders: "∀s:set(A).",
		Hypotheses: []string{
			"s ⊆ G.carrier",
		},
		Conclusion: "set_inv(s) ⊆ G.carrier",
	},
		func(a *Argument, grp group.GroupFact[on.G], s *Expr[Set[A]], subset Fact) {
			sInC := a.Unfolded(subset, set_basic.SubsetDef)
			a.Do(
				Unfold(set_basic.SubsetDef),
				Unfold(SetInvDef),
				Simp(Fwd(set_basic.InImage.Inst(TypeBinder.BindA[A](), TypeBinder.BindB[A]()))))
			a.FixAs[A]("z")
			member := a.Assume()
			_, fromX := a.UnpackAs[A](member, "x")
			parts := a.Conjuncts(
				fromX,
				"z is G.inv(x)",
				"x lies in s")
			a.Show(
				"so z is the inverse of a point of G.carrier",
				parts[0].Rw(),
				By(group.InvIn, grp, sInC, parts[1]))
		}),
})}

// InSetInvOn — a point of the carrier lies in the inverses of a subset
// of it exactly when its own inverse lies in the subset: the inverses of
// s are its image under inv, and inv undoes itself on the carrier.
var InSetInvOn = inSetInvOnThm{family.Add(registry.ProofEntry{
	Name: "InSetInvOn",
	Key:  "prop_a53458e036631c44",

	Build: group.GroupOn.Law(Statement{
		Binders: "∀s:set(A). ∀z:A.",
		Hypotheses: []string{
			"s ⊆ G.carrier",
			"z ∈ G.carrier",
		},
		Conclusion: "z ∈ set_inv(s) ⇔ G.inv(z) ∈ s",
	},
		func(a *Argument, grp group.GroupFact[on.G], s *Expr[Set[A]], z *Expr[A], given Fact) {
			parts := a.Conjuncts(
				given,
				"s lies in G.carrier",
				"z lies in G.carrier")
			sInC := a.Unfolded(parts[0], set_basic.SubsetDef)
			// InImage is pinned at A → A: a Go Simp rule is not instantiated
			// at a type on its own, and fires nothing beside a sibling that is.
			a.Do(
				Unfold(SetInvDef), Simp(Fwd(set_basic.InImage.Inst(TypeBinder.BindA[A](), TypeBinder.BindB[A]()))))
			a.Iff()
			a.Forward(
				"z is G.inv(x) for some x in s, and G.inv undoes itself, so G.inv(z) is that x",
				func(b *Argument, member Fact) {
					_, fromX := b.UnpackAs[A](member, "x")
					factors := b.Conjuncts(
						fromX,
						"z is G.inv(x)",
						"x lies in s")
					b.Have(
						"x lies in G.carrier",
						"x ∈ G.carrier",
						By(sInC, factors[1]))
					b.Show(
						"G.inv(z) is G.inv(G.inv(x)), which is x, x lying in G.carrier",
						factors[0].Rw(),
						Simp(Fwd(group.InvInvOn)),
						By(factors[1]))
				})
			a.Backward(
				"G.inv(z) is a member of s whose inverse is z",
				func(b *Argument, invIn Fact) {
					b.Take(b.TermAs[A]("G.inv(z)"))
					b.Show(
						"G.inv(z) lies in s, and z is G.inv(G.inv(z)), z lying in G.carrier",
						Simp(Fwd(group.InvInvOn)),
						By(invIn))
				})
		}),
})}

// InSetInv — InSetInvOn on the whole type.
var InSetInv = inSetInvThm{family.Add(registry.ProofEntry{
	Name:  "InSetInv",
	Key:   "prop_12701dc6cd28de1d",
	Build: group.GroupAtUniverse.Law("∀s:set(A). ∀z:A. z ∈ set_inv(s) ⇔ G.inv(z) ∈ s", InSetInvOn),
})}

// LeftCosetsDef — `left_cosets(mul, c, h)`: the left cosets of h by the
// points of c — the quotient of c by the relation "y lies in x·h", the
// relations chapter's `quotient_on` at that relation. It is the quotient
// group's carrier, a set of the type set(A), which is why the quotient is
// a group on a set (`group.GroupOn`). For a subset h of a group's carrier
// its members are the cosets x·h of the points of c (LeftCosetsImage).
// The operation is an implicit argument: under a law over G the text writes
// `left_cosets(G.carrier, h)`, and a definition spells it out,
// `left_cosets(G.mul, G.carrier, h)`.
var LeftCosetsDef = leftCosetsDefThm{family.Define(registry.DefEntry{
	Name:     "LeftCosetsDef",
	Key:      "prop_dfa2d9000c241dfb",
	Const:    "left_cosets",
	Type:     "(A → A → A) → set(A) → set(A) → set(set(A))",
	Implicit: []string{"mul"},
	Equations: []string{
		"∀mul:(A → A → A). ∀c h:set(A). " +
			"    left_cosets(mul, c, h) = quotient_on(c, λx:A. λy:A. y ∈ left_coset(mul, x, h))",
	},
})}

// QuotientGroupDef — the quotient group G/N: the left cosets of N by the
// points of G's carrier, under the set product, with N as the identity and
// the set inverse as the inverse. The record is defined for any N; it is a
// group on its carrier when N is a normal subgroup (QuotientGroupOn). The
// quotient of a subgroup h of G is the quotient of G restricted to h,
// `quotient_group(restrict_group(G, h), N)`.
var QuotientGroupDef = quotientGroupDefThm{family.Define(registry.DefEntry{
	Name:  "QuotientGroupDef",
	Key:   "prop_ae974b76a1f4880b",
	Const: "quotient_group",
	Type:  "group_ops(A) → set(A) → group_ops(set(A))",
	Equations: []string{"∀G:group_ops(A). ∀N:set(A). " +
		"    quotient_group(G, N) = " +
		"    mk_group(set_mul(G.mul), N, set_inv(G.inv), left_cosets(G.mul, G.carrier, N))"},
	Deps: []registry.EntryLike{SetMulDef, SetInvDef, LeftCosetsDef},
})}

// LeftCosetsImage — for a subset h of the carrier, the cosets are the
// image of c under the coset map: c is closed under the coset relation
// (group.CosetClosedOn), so its quotient is the image of c under the class
// map (equivalence.QuotientOnClosed), and the class map of the coset
// relation is the coset map (group.LeftCosetClass).
var LeftCosetsImage = leftCosetsImageThm{family.Add(registry.ProofEntry{
	Name: "LeftCosetsImage",
	Key:  "prop_1f75661662269ad6",

	Build: group.GroupOn.Law(Statement{
		Binders: "∀h:set(A).",
		Hypotheses: []string{
			"h ⊆ G.carrier",
		},
		Conclusion: "left_cosets(G.carrier, h) = image(coset_map(G.mul, h), G.carrier)",
	},
		func(a *Argument, grp group.GroupFact[on.G], h *Expr[Set[A]], hInC Fact) {
			// The closure stays resident: it is the side condition of the
			// closed quotient law in the rewrite below.
			a.Have(
				"G.carrier is closed under the coset relation: a point "+
					"of the coset of a point of G.carrier lies in G.carrier",
				"∀x y:A. x ∈ G.carrier ∧ y ∈ left_coset(x, h) ⇒ y ∈ G.carrier",
				By(hInC, group.CosetClosedOn.Read(grp)))
			a.Show(
				"so the cosets are the image of G.carrier under the class map, which is the coset map",
				Unfold(LeftCosetsDef),
				Simp(Fwd(equivalence.QuotientOnClosed), Fwd(group.CosetMapDef)),
				By(group.LeftCosetClass))
		}),
})}

// LeftCosetsFinite — a finite set has finitely many left cosets of a set
// h by its points: they are the classes of its points under the coset
// relation (equivalence.QuotientOnFinite). Stated for any operation, no
// group.
var LeftCosetsFinite = leftCosetsFiniteThm{family.Add(registry.ProofEntry{
	Name: "LeftCosetsFinite",
	Key:  "prop_44d6842195e17805",
	Build: family.Theorem(Statement{
		Binders: "∀mul:(A → A → A). ∀c h:set(A).",
		Hypotheses: []string{
			"finite(c)",
		},
		Conclusion: "finite(left_cosets(mul, c, h))",
	},
		func(a *Argument, mul *Arrow2[A, A, A], c, h *Expr[Set[A]], finite Fact) {
			a.Show(
				"the cosets are the classes of the points of the finite c under the coset relation",
				Unfold(LeftCosetsDef),
				By(finite, equivalence.QuotientOnFinite))
		}),
})}

// InLeftCosets — a set is a left coset of h by c exactly when it is the
// coset of some point of c: c is closed under the coset relation
// (group.CosetClosedOn), so a member of its quotient is the class of a
// point of c (equivalence.InQuotientOnClosed), which is its coset
// (group.LeftCosetClass).
var InLeftCosets = inLeftCosetsThm{family.Add(registry.ProofEntry{
	Name: "InLeftCosets",
	Key:  "prop_bb85c3aadd911842",

	Build: group.GroupOn.Law(Statement{
		Binders: "∀h s:set(A).",
		Hypotheses: []string{
			"h ⊆ G.carrier",
		},
		Conclusion: "s ∈ left_cosets(G.carrier, h) ⇔ ∃x:A. s = left_coset(x, h) ∧ x ∈ G.carrier",
	},
		func(a *Argument, grp group.GroupFact[on.G], h, s *Expr[Set[A]], hInC Fact) {
			// The closure stays resident: it is the side condition of the
			// closed quotient law in the rewrite below.
			a.Have(
				"G.carrier is closed under the coset relation: a point "+
					"of the coset of a point of G.carrier lies in G.carrier",
				"∀x y:A. x ∈ G.carrier ∧ y ∈ left_coset(x, h) ⇒ y ∈ G.carrier",
				By(hInC, group.CosetClosedOn.Read(grp)))
			a.Show(
				"so a member of the quotient is the class of a point of G.carrier, which is its coset",
				Unfold(LeftCosetsDef),
				Simp(Fwd(equivalence.InQuotientOnClosed), Fwd(group.LeftCosetClass)),
				Basic())
		}),
})}

// LeftCosetInLeftCosets — the coset x·h of a point x of the carrier, h
// a subset of it, is one of the left cosets of h by the carrier: it is
// the coset of a point of the carrier, x itself (InLeftCosets).
var LeftCosetInLeftCosets = leftCosetInLeftCosetsThm{family.Add(registry.ProofEntry{
	Name: "LeftCosetInLeftCosets",
	Key:  "prop_91e7d4297fab94ba",

	Build: group.GroupOn.Law(Statement{
		Binders: "∀h:set(A). ∀x:A.",
		Hypotheses: []string{
			"h ⊆ G.carrier",
			"x ∈ G.carrier",
		},
		Conclusion: "left_coset(x, h) ∈ left_cosets(G.carrier, h)",
	},
		func(a *Argument, grp group.GroupFact[on.G], h *Expr[Set[A]], x *Member[A, on.G], hInC Fact) {
			a.Do(Simp(Fwd(InLeftCosets.Read(grp))))
			a.Take(x)
			a.Show(
				"x represents its own coset, and lies in G.carrier",
				By(x))
		}),
})}

// SubgroupInLeftCosets — a subgroup is one of its own left cosets by the
// carrier: it is the coset of the identity (group.LeftCosetOneOn), a
// point of the carrier.
var SubgroupInLeftCosets = subgroupInLeftCosetsThm{family.Add(registry.ProofEntry{
	Name: "SubgroupInLeftCosets",
	Key:  "prop_5d3e90348d1f8852",

	Build: group.GroupOn.Law(Statement{
		Binders: "∀N:set(A).",
		Hypotheses: []string{
			"subgroup(G, N)",
		},
		Conclusion: "N ∈ left_cosets(G.carrier, N)",
	},
		func(a *Argument, grp group.GroupFact[on.G], N *Expr[Set[A]], subgroup Fact) {
			nInC := a.Have(
				"N lies in G.carrier",
				"N ⊆ G.carrier",
				By(group.SubgroupSubset.Read(subgroup)))
			identity := a.Have(
				"N is the coset of G.one",
				"left_coset(G.one, N) = N",
				By(nInC, group.LeftCosetOneOn.Read(grp).At(N)))
			a.Do(Simp(Fwd(InLeftCosets.Read(grp))))
			a.Take(a.TermAs[A]("G.one"))
			a.Show(
				"G.one represents N, and lies in G.carrier",
				By(Normalized, identity, group.OneIn.Read(grp)))
		}),
})}

// ForallInLeftCosets — a property holds of every left coset of h by c
// exactly when it holds of the coset of every point of c: the cosets are
// the image of c under the coset map, and a quantifier over an image is
// one over its source. An argument about every coset starts here from a
// representative.
var ForallInLeftCosets = forallInLeftCosetsThm{family.Add(registry.ProofEntry{
	Name: "ForallInLeftCosets",
	Key:  "prop_5923e8ae395f34ad",

	Build: group.GroupOn.Law(Statement{
		Binders: "∀h:set(A). ∀P:(set(A) → bool).",
		Hypotheses: []string{
			"h ⊆ G.carrier",
		},
		Conclusion: "(∀s:set(A). s ∈ left_cosets(G.carrier, h) ⇒ P(s)) ⇔ " +
			"∀x:A. x ∈ G.carrier ⇒ P(left_coset(x, h))",
	},
		func(a *Argument, grp group.GroupFact[on.G], h *Expr[Set[A]], P *Arrow[Set[A], Bool], hInC Fact) {
			images := a.Unfolded(a.Have(
				"the cosets are the image of G.carrier under the coset map",
				"left_cosets(G.carrier, h) = image(coset_map(G.mul, h), G.carrier)",
				By(LeftCosetsImage, grp, hInC)), group.CosetMapDef)
			a.Show(
				"and a quantifier over an image is one over its source",
				images.Rw(),
				By(set_image.ForallInImage))
		}),
})}

// ForallInLeftCosetsPair — a property holds of every pair of left cosets
// of h by c exactly when it holds of the cosets of every pair of points
// of c: ForallInLeftCosets for two cosets at once. An argument about two
// cosets — their sum, whether they commute — starts here from two
// representatives.
var ForallInLeftCosetsPair = forallInLeftCosetsPairThm{family.Add(registry.ProofEntry{
	Name: "ForallInLeftCosetsPair",
	Key:  "prop_ba0e7f51beb84b86",

	Build: group.GroupOn.Law(Statement{
		Binders: "∀h:set(A). ∀P:(set(A) → set(A) → bool).",
		Hypotheses: []string{
			"h ⊆ G.carrier",
		},
		Conclusion: "(∀s t:set(A). " +
			"    s ∈ left_cosets(G.carrier, h) ∧ t ∈ left_cosets(G.carrier, h) ⇒ P(s, t)) ⇔ " +
			"∀x y:A. x ∈ G.carrier ∧ y ∈ G.carrier ⇒ P(left_coset(x, h), left_coset(y, h))",
	},
		func(
			a *Argument,
			grp group.GroupFact[on.G],
			h *Expr[Set[A]],
			P *Arrow2[Set[A], Set[A], Bool],
			hInC Fact,
		) {
			images := a.Unfolded(a.Have(
				"the cosets are the image of G.carrier under the coset map",
				"left_cosets(G.carrier, h) = image(coset_map(G.mul, h), G.carrier)",
				By(LeftCosetsImage, grp, hInC)), group.CosetMapDef)
			a.Show(
				"and a quantifier over two points of an image is one over two points of its source",
				images.Rw(),
				By(set_image.ForallInImagePair))
		}),
})}
