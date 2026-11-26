// zassenhaus.go — isomorphism as a relation between groups on sets, and
// the butterfly lemma: two subgroups a, b of a group on a set, each with
// a normal subgroup a', b', give two quotients
// a'(a ∩ b)/a'(a ∩ b') and b'(a ∩ b)/b'(a' ∩ b), and the lemma says they
// are isomorphic. Each is isomorphic to the middle quotient
// (a ∩ b)/((a' ∩ b)(a ∩ b')) by the second isomorphism theorem read
// inside a'(a ∩ b), respectively b'(a ∩ b), with Dedekind's law
// computing the kernel.

package group_isomorphism

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/quotient_group"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_algebra"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// Isomorphism as a relation
// ---------------------------------------------------------------------------
//
// An isomorphism carries its two groups with it (Source, Target), so
// these facts bind the operations and no group; reflexivity alone
// needs the group, for the identity map.

// IsomorphismInverse — the inverse laws transfer multiplication and
// bijectivity to the chosen inverse on the target carrier.
var IsomorphismInverse = isomorphismInverseThm{family.Add(registry.ProofEntry{
	Name: "IsomorphismInverse",
	Key:  "prop_7c8fd80e6985c0f",

	Build: family.Theorem(Statement{
		Binders: "∀G:group_ops(A). ∀H:group_ops(B). ∀f:(A → B).",
		Hypotheses: []string{
			"group_isomorphism(G, H, f)",
		},
		Conclusion: "group_isomorphism(H, G, inverse_on(G.carrier, f))",
	},
		func(
			a *Argument,
			G *Expr[group.GroupOps[A]],
			H *Expr[group.GroupOps[B]],
			f *Arrow[A, B],
			iso Fact,
		) {
			c := a.TermAs[Set[A]]("G.carrier")
			hom := a.Have(
				"retain the forward homomorphism",
				"group_homomorphism(G, H, f)",
				By(iso, group_homomorphism.IsomorphismHomomorphism))
			injective := a.Have(
				"the forward map is one-to-one on its carrier",
				"injective_on(G.carrier, f)",
				By(iso, group_homomorphism.IsomorphismInjective))
			onto := a.Have(
				"the forward image is the target carrier",
				"image(f, G.carrier) = H.carrier",
				By(iso, group_homomorphism.IsomorphismSurjective))
			source := a.Have(
				"the source carries the given group operations",
				"group_on(G)",
				By(hom, group_homomorphism.Source))
			target := a.Have(
				"the target carries the given group operations",
				"group_on(H)",
				By(hom, group_homomorphism.Target))
			inverseIn := a.Have(
				"the inverse returns to the source carrier",
				"∀y:B. y ∈ H.carrier ⇒ inverse_on(G.carrier, f, y) ∈ G.carrier",
				a.ForEach(func(y *Expr[B]) Action {
					return By(onto, functions.InverseOnIn.At(c, f, y))
				}))
			// Normalized reads the guard through onto; on this equation, unlike the membership above, a bare By records a refute key
			rightInverse := a.Have(
				"the forward map recovers each target point",
				"∀y:B. y ∈ H.carrier ⇒ f(inverse_on(G.carrier, f, y)) = y",
				a.ForEach(func(y *Expr[B]) Action {
					return By(Normalized, onto, functions.InverseOnRight.At(c, f, y))
				}))
			leftInverse := a.Have(
				"the inverse recovers each source point",
				"∀x:A. x ∈ G.carrier ⇒ inverse_on(G.carrier, f, f(x)) = x",
				a.ForEach(func(x *Expr[A]) Action {
					return By(injective, functions.InverseOnLeft)
				}))
			inverseMul := a.Have(
				"multiplication is determined by its forward image",
				Statement{
					Binders: "∀y z:B.",
					Hypotheses: []string{
						"y ∈ H.carrier",
						"z ∈ H.carrier",
					},
					Conclusion: "inverse_on(G.carrier, f, H.mul(y, z)) = " +
						"G.mul(inverse_on(G.carrier, f, y), inverse_on(G.carrier, f, z))",
				},
				Derive(func(b *Argument) {
					y := b.FixAs[B]("y")
					z := b.FixAs[B]("z")
					members := b.Assume()
					preimages := b.Have(
						"both preimages lie in the source carrier",
						"inverse_on(G.carrier, f, y) ∈ G.carrier ∧ inverse_on(G.carrier, f, z) ∈ G.carrier",
						By(members, inverseIn.At(y), inverseIn.At(z)))
					productIn := b.Have(
						"their product lies in the source carrier",
						"G.mul(inverse_on(G.carrier, f, y), inverse_on(G.carrier, f, z)) ∈ G.carrier",
						By(preimages, group.MulIn.Read(source)))
					mappedProduct := b.Have(
						"the forward homomorphism preserves this product",
						"f(G.mul(inverse_on(G.carrier, f, y), inverse_on(G.carrier, f, z))) = "+
							"H.mul(f(inverse_on(G.carrier, f, y)), f(inverse_on(G.carrier, f, z)))",
						By(preimages, group_homomorphism.MapMul.Read(hom)))
					product := b.TermAs[A]("G.mul(inverse_on(G.carrier, f, y), inverse_on(G.carrier, f, z))")
					b.Show(
						"the inverse laws recover the product of the preimages",
						By(
							productIn,
							members,
							mappedProduct,
							leftInverse.At(product),
							rightInverse.At(y),
							rightInverse.At(z)))
				}))
			inverseMap := a.TermAs[Fun[B, A]]("inverse_on(G.carrier, f)")
			inverseHom := a.Have(
				"the inverse is a homomorphism between the two groups",
				"group_homomorphism(H, G, inverse_on(G.carrier, f))",
				By(
					source,
					target,
					inverseIn,
					inverseMul,
					group_homomorphism.GroupHomomorphism.At(H, G, inverseMap)))
			inverseInjective := a.Have(
				"the inverse is one-to-one on the target carrier",
				"injective_on(H.carrier, inverse_on(G.carrier, f))",
				By(Normalized, onto, functions.InverseOnInjective.At(c, f)))
			inverseOnto := a.Have(
				"the inverse image is the whole source carrier",
				"image(inverse_on(G.carrier, f), H.carrier) = G.carrier",
				By(Normalized, onto, injective, functions.InverseOnImage.At(c, f)))
			a.Show(
				"the inverse homomorphism is bijective",
				By(
					inverseHom,
					inverseInjective,
					inverseOnto,
					group_homomorphism.GroupIsomorphismDef.At(H, G, inverseMap)))
		}),
})}

// IsomorphismCompose — isomorphisms compose.
var IsomorphismCompose = isomorphismComposeThm{family.Add(registry.ProofEntry{
	Name: "IsomorphismCompose",
	Key:  "prop_2eef73ec5825cc0d",

	Deps: []registry.EntryLike{
		group_homomorphism.GroupIsomorphismDef,
		group_homomorphism.ComposeHom,
		group_homomorphism.IsomorphismHomomorphism,
		group_homomorphism.IsomorphismInjective,
		group_homomorphism.IsomorphismSurjective,
		group_homomorphism.MapIn,
	},
	Build: family.Card(Statement{
		Binders: "∀G:group_ops(A). ∀H:group_ops(B). ∀K:group_ops(C). ∀f:(A → B). ∀g:(B → C).",
		Hypotheses: []string{
			"group_isomorphism(G, H, f)",
			"group_isomorphism(H, K, g)",
		},
		Conclusion: "group_isomorphism(G, K, g ∘ f)",
	},
		"ComposeHom for the homomorphism; one-to-one since g then f is; onto since "+
			"a point of K.carrier comes from H.carrier by g and that from G.carrier by f"),
})}

// IsomorphismFiniteCard — the carriers of two isomorphic groups are
// finite together, and then equally large: an isomorphism is one-to-one
// on the source carrier and its image is the target carrier, and a
// one-to-one image keeps finiteness and the count of a finite set.
var IsomorphismFiniteCard = isomorphismFiniteCardThm{family.Add(registry.ProofEntry{
	Name: "IsomorphismFiniteCard",
	Key:  "prop_c190964b9181a434",

	Build: family.Theorem(Statement{
		Binders: "∀G:group_ops(A). ∀H:group_ops(B). ∀f:(A → B).",
		Hypotheses: []string{
			"group_isomorphism(G, H, f)",
		},
		Conclusion: "(finite(G.carrier) ⇔ finite(H.carrier)) ∧ " +
			"(finite(G.carrier) ⇒ card(G.carrier) = card(H.carrier))",
	},
		func(
			a *Argument,
			G *Expr[group.GroupOps[A]],
			H *Expr[group.GroupOps[B]],
			f *Arrow[A, B],
			iso Fact,
		) {
			c := a.TermAs[Set[A]]("G.carrier")
			injective := a.Have(
				"f is one-to-one on G.carrier",
				"injective_on(G.carrier, f)",
				By(iso, group_homomorphism.IsomorphismInjective))
			onto := a.Have(
				"and its image is H.carrier",
				"image(f, G.carrier) = H.carrier",
				By(iso, group_homomorphism.IsomorphismSurjective))
			a.Show(
				"so H.carrier is the one-to-one image of G.carrier",
				onto.RwRev(),
				SplitConj(
					Case(
						"a one-to-one image is finite exactly when its source is",
						By(injective, finite_set.FiniteImageInjEq.At(f, c))),
					Case(
						"and a finite source has as many points as its one-to-one image",
						By(injective, cardinality.CardImageInj.At(f, c)))))
		}),
})}

// IsomorphicRefl — a group on a set is isomorphic to itself, by the
// identity.
var IsomorphicRefl = isomorphicReflThm{family.Add(registry.ProofEntry{
	Name: "IsomorphicRefl",
	Key:  "prop_e7711c15cb006a59",

	Deps: []registry.EntryLike{
		GroupIsomorphicDef,
		group_homomorphism.GroupIsomorphismDef,
		group_homomorphism.IdentityHom,
	},
	Build: family.Card(group.GroupOn.Statement("group_isomorphic(G, G)"),
		"the identity map (IdentityHom), one-to-one and onto"),
})}

// IsomorphicSym — isomorphism is symmetric.
var IsomorphicSym = isomorphicSymThm{family.Add(registry.ProofEntry{
	Name: "IsomorphicSym",
	Key:  "prop_a28b63aaec292b74",

	Deps: []registry.EntryLike{GroupIsomorphicDef, IsomorphismInverse},
	Build: family.Card(Statement{
		Binders: "∀G:group_ops(A). ∀H:group_ops(B).",
		Hypotheses: []string{
			"group_isomorphic(G, H)",
		},
		Conclusion: "group_isomorphic(H, G)",
	},
		"the inverse of the isomorphism in hand (IsomorphismInverse)"),
})}

// IsomorphicTrans — isomorphism is transitive.
var IsomorphicTrans = isomorphicTransThm{family.Add(registry.ProofEntry{
	Name: "IsomorphicTrans",
	Key:  "prop_5954fe23a8b5f1b3",

	Deps: []registry.EntryLike{GroupIsomorphicDef, IsomorphismCompose},
	Build: family.Card(Statement{
		Binders: "∀G:group_ops(A). ∀H:group_ops(B). ∀K:group_ops(C).",
		Hypotheses: []string{
			"group_isomorphic(G, H)",
			"group_isomorphic(H, K)",
		},
		Conclusion: "group_isomorphic(G, K)",
	},
		"the composite of the two isomorphisms in hand (IsomorphismCompose)"),
})}

// IsomorphicTrivial — isomorphic groups are trivial together: an
// isomorphism carries one to one', and a second point to a second.
var IsomorphicTrivial = isomorphicTrivialThm{family.Add(registry.ProofEntry{
	Name: "IsomorphicTrivial",
	Key:  "prop_1e00c10499ec302a",

	Deps: []registry.EntryLike{
		GroupIsomorphicDef,
		group_homomorphism.GroupIsomorphismDef,
		group_homomorphism.Source,
		group_homomorphism.Target,
		group_homomorphism.MapIn,
		group_homomorphism.MapOne,
		group_homomorphism.IsomorphismInjective,
		group_homomorphism.IsomorphismSurjective,
		group.OneIn,
		set_basic.InSing,
		set_basic.Extension,
	},
	Build: family.Card(Statement{
		Binders: "∀G:group_ops(A). ∀H:group_ops(B).",
		Hypotheses: []string{
			"group_isomorphic(G, H)",
		},
		Conclusion: "G.carrier = {G.one} ⇔ H.carrier = {H.one}",
	},
		"forward: a point of H.carrier comes from a point of G.carrier, which is "+
			"G.one, whose image is H.one (MapOne), and H.one lies in H.carrier (OneIn at "+
			"the target); backward: a point x of G.carrier has f(x) = H.one = f(G.one), "+
			"G.one lying in G.carrier (OneIn at the source), so x = G.one by injectivity"),
})}

// ---------------------------------------------------------------------------
// The butterfly lemma
// ---------------------------------------------------------------------------

// ZassenhausSubgroup — a'(a ∩ b) is a subgroup of a: a' is normal in a
// and a ∩ b a subgroup of it, and a normal subgroup commutes with any
// subgroup as a set. b' plays no part.
var ZassenhausSubgroup = zassenhausSubgroupThm{family.Add(registry.ProofEntry{
	Name: "ZassenhausSubgroup",
	Key:  "prop_b449517e581e148b",

	Deps: []registry.EntryLike{
		SetMulNormal,
		SetMulNormalSwap,
		SubgroupInter,
		SubgroupRestrict,
		group.SubgroupGroupOn,
		group.SubgroupSubset,
		set_order.SubsetInter,
	},
	Build: family.Card(group.GroupOn.Statement(Statement{
		Binders: "∀a a' b:set(A).",
		Hypotheses: []string{
			"subgroup(G, a)",
			"subgroup(G, b)",
			"normal_subgroup(restrict_group(G, a), a')",
		},
		Conclusion: "subgroup(restrict_group(G, a), set_mul(a', a ∩ b))",
	}),
		"inside the group on a (SubgroupGroupOn): a ∩ b is a subgroup of G.carrier "+
			"(SubgroupInter) lying in a, hence of a (SubgroupRestrict); a' normal, so (a "+
			"∩ b)a' is a subgroup (SetMulNormal) and equals a'(a ∩ b) (SetMulNormalSwap)"),
})}

// ZassenhausNormal — a'(a ∩ b') is normal in a'(a ∩ b): a conjugate of
// a point of a' by a point of a'(a ∩ b) stays in a', and a conjugate of
// a point of a ∩ b' by a point of a ∩ b stays in a ∩ b' since b' is
// normal in b; the a' factor of the conjugating point is absorbed.
var ZassenhausNormal = zassenhausNormalThm{family.Add(registry.ProofEntry{
	Name: "ZassenhausNormal",
	Key:  "prop_4774cd288cc0e7df",

	Deps: []registry.EntryLike{
		ZassenhausSubgroup,
		SubgroupTrans,
		SubgroupRestrict,
		quotient_group.SetMulMono,
		SetMulNormal,
		SetMulNormalSwap,
		NormalInter,
		group.NormalSubgroupDef,
		group.NormalSubgroupSubgroup,
		group.NormalSubgroupConjugate,
		group.SubgroupSubset,
		quotient_group.InSetMul,
	},
	Build: family.Card(group.GroupOn.Statement(Statement{
		Binders: "∀a a' b b':set(A).",
		Hypotheses: []string{
			"subgroup(G, a)",
			"subgroup(G, b)",
			"normal_subgroup(restrict_group(G, a), a')",
			"normal_subgroup(restrict_group(G, b), b')",
		},
		Conclusion: "normal_subgroup(restrict_group(G, set_mul(a', a ∩ b)), set_mul(a', a ∩ b'))",
	}),
		"a'(a ∩ b') is a subgroup of a by ZassenhausSubgroup at b' (a subgroup of G.carrier "+
			"through b, SubgroupTrans), lying in a'(a ∩ b) (SetMulMono, b' ⊆ b), hence a "+
			"subgroup of it (SubgroupRestrict); write a conjugating point as x * y with x in a', "+
			"y in a ∩ b: conjugation by x keeps a' and fixes the class modulo a', conjugation by "+
			"y keeps a' (normal in a) and keeps a ∩ b' (y ∈ a, and b' normal in b)"),
})}

// ZassenhausProduct — the product of a ∩ b with a'(a ∩ b') is a'(a ∩ b):
// the normal factor a' is moved to the right inside the group on a,
// a ∩ b absorbs a ∩ b', and a' is moved back.
var ZassenhausProduct = zassenhausProductThm{family.Add(registry.ProofEntry{
	Name: "ZassenhausProduct",
	Key:  "prop_cb16d054fbf4f2d7",

	Deps: []registry.EntryLike{
		SetMulNormalSwap,
		quotient_group.SetMulAssoc,
		SetMulAbsorb,
		SubgroupInter,
		SubgroupRestrict,
		group.SubgroupOne,
		group.SubgroupSubset,
		set_order.SubsetInter,
		set_basic.InInter,
	},
	Build: family.Card(group.GroupOn.Statement(Statement{
		Binders: "∀a a' b b':set(A).",
		Hypotheses: []string{
			"subgroup(G, a)",
			"subgroup(G, b)",
			"normal_subgroup(restrict_group(G, a), a')",
			"normal_subgroup(restrict_group(G, b), b')",
		},
		Conclusion: "set_mul(a ∩ b, set_mul(a', a ∩ b')) = set_mul(a', a ∩ b)",
	}),
		"in the group on a: a'(a ∩ b') = (a ∩ b')a' (SetMulNormalSwap, a ∩ b' ⊆ "+
			"a); (a ∩ b)((a ∩ b')a') = ((a ∩ b)(a ∩ b'))a' (SetMulAssoc) = (a ∩ b)a' "+
			"(SetMulAbsorb: a ∩ b' ⊆ a ∩ b holds G.one) = a'(a ∩ b) (SetMulNormalSwap)"),
})}

// ZassenhausMeet — what a ∩ b meets of a'(a ∩ b') is (a' ∩ b)(a ∩ b'):
// Dedekind's law inside the group on a, between two swaps of a normal
// factor.
var ZassenhausMeet = zassenhausMeetThm{family.Add(registry.ProofEntry{
	Name: "ZassenhausMeet",
	Key:  "prop_9a8f3aa534d766b9",

	Deps: []registry.EntryLike{
		SetMulNormalSwap,
		DedekindModular,
		NormalInter,
		SubgroupInter,
		SubgroupRestrict,
		group.SubgroupGroupOn,
		group.NormalSubgroupSubgroup,
		group.SubgroupSubset,
		set_algebra.InterComm,
		set_basic.Extension,
		set_basic.InInter,
	},
	Build: family.Card(group.GroupOn.Statement(Statement{
		Binders: "∀a a' b b':set(A).",
		Hypotheses: []string{
			"subgroup(G, a)",
			"subgroup(G, b)",
			"normal_subgroup(restrict_group(G, a), a')",
			"normal_subgroup(restrict_group(G, b), b')",
		},
		Conclusion: "a ∩ b ∩ set_mul(a', a ∩ b') = set_mul(a' ∩ b, a ∩ b')",
	}),
		"in the group on a: a'(a ∩ b') = (a ∩ b')a' (SetMulNormalSwap); DedekindModular "+
			"with k = a ∩ b, h = a ∩ b' ⊆ k, n = a' gives (a ∩ b')((a ∩ b) ∩ a') = (a ∩ b')(a' "+
			"∩ b), a' lying in a; in the group on a ∩ b, a' ∩ b is normal (NormalInter) and a "+
			"∩ b' ⊆ a ∩ b, so SetMulNormalSwap turns it into (a' ∩ b)(a ∩ b')"),
})}

// ZassenhausLeft — a'(a ∩ b)/a'(a ∩ b') is isomorphic to the middle
// quotient (a ∩ b)/((a' ∩ b)(a ∩ b')): the second isomorphism theorem
// inside the group on a'(a ∩ b) with h = a ∩ b and n = a'(a ∩ b'),
// whose product hn is the whole group (ZassenhausProduct) and whose
// meet h ∩ n is (a' ∩ b)(a ∩ b') (ZassenhausMeet).
var ZassenhausLeft = zassenhausLeftThm{family.Add(registry.ProofEntry{
	Name: "ZassenhausLeft",
	Key:  "prop_d4a4553c636ce4ec",

	Deps: []registry.EntryLike{
		GroupIsomorphicDef,
		SecondIsomorphism,
		IsomorphicSym,
		ZassenhausSubgroup,
		ZassenhausNormal,
		ZassenhausProduct,
		ZassenhausMeet,
		SubgroupInter,
		SubgroupRestrict,
		SubsetSetMulRight,
		group.SubgroupGroupOn,
	},
	Build: family.Card(group.GroupOn.Statement(Statement{
		Binders: "∀a a' b b':set(A).",
		Hypotheses: []string{
			"subgroup(G, a)",
			"subgroup(G, b)",
			"normal_subgroup(restrict_group(G, a), a')",
			"normal_subgroup(restrict_group(G, b), b')",
		},
		Conclusion: "group_isomorphic( " +
			"    quotient_group(restrict_group(G, set_mul(a', a ∩ b)), set_mul(a', a ∩ b')), " +
			"    quotient_group(restrict_group(G, a ∩ b), set_mul(a' ∩ b, a ∩ b')))",
	}),
		"in the group on a'(a ∩ b) (ZassenhausSubgroup, SubgroupGroupOn): h = a ∩ b is a subgroup of it "+
			"(SubgroupRestrict, a ∩ b ⊆ a'(a ∩ b)), n = a'(a ∩ b') is normal (ZassenhausNormal); "+
			"SecondIsomorphism gives h/(h ∩ n) ≅ hn/n; hn = a'(a ∩ b) (ZassenhausProduct) and h ∩ n = (a' ∩ "+
			"b)(a ∩ b') (ZassenhausMeet) are rewritten inside the components; IsomorphicSym turns it round"),
})}

// ZassenhausRight — the same with the roles of (a, a') and (b, b')
// exchanged: b'(a ∩ b)/b'(a' ∩ b) is isomorphic to the middle quotient.
var ZassenhausRight = zassenhausRightThm{family.Add(registry.ProofEntry{
	Name: "ZassenhausRight",
	Key:  "prop_1fa9234c358020b",

	Deps: []registry.EntryLike{
		GroupIsomorphicDef,
		ZassenhausLeft,
		SetMulNormalSwap,
		NormalInter,
		SubgroupInter,
		SubgroupRestrict,
		group.SubgroupGroupOn,
		set_algebra.InterComm,
	},
	Build: family.Card(group.GroupOn.Statement(Statement{
		Binders: "∀a a' b b':set(A).",
		Hypotheses: []string{
			"subgroup(G, a)",
			"subgroup(G, b)",
			"normal_subgroup(restrict_group(G, a), a')",
			"normal_subgroup(restrict_group(G, b), b')",
		},
		Conclusion: "group_isomorphic( " +
			"    quotient_group(restrict_group(G, set_mul(b', a ∩ b)), set_mul(b', a' ∩ b)), " +
			"    quotient_group(restrict_group(G, a ∩ b), set_mul(a' ∩ b, a ∩ b')))",
	}),
		"ZassenhausLeft at (b, b', a, a'), its meets read back as a ∩ b, a' ∩ b, a ∩ b' "+
			"(InterComm); its middle subgroup (a ∩ b')(a' ∩ b) is the stated G.one, the two factors "+
			"commuting in the group on a ∩ b (SetMulNormalSwap, a' ∩ b normal there by NormalInter)"),
})}

// Zassenhaus — the butterfly lemma: the two quotients are isomorphic,
// both being isomorphic to the middle one.
var Zassenhaus = zassenhausThm{family.Add(registry.ProofEntry{
	Name: "Zassenhaus",
	Key:  "prop_7d717af0af16648b",

	Deps: []registry.EntryLike{ZassenhausLeft, ZassenhausRight, IsomorphicSym, IsomorphicTrans},
	Build: family.Card(group.GroupOn.Statement(Statement{
		Binders: "∀a a' b b':set(A).",
		Hypotheses: []string{
			"subgroup(G, a)",
			"subgroup(G, b)",
			"normal_subgroup(restrict_group(G, a), a')",
			"normal_subgroup(restrict_group(G, b), b')",
		},
		Conclusion: "group_isomorphic( " +
			"    quotient_group(restrict_group(G, set_mul(a', a ∩ b)), set_mul(a', a ∩ b')), " +
			"    quotient_group(restrict_group(G, set_mul(b', a ∩ b)), set_mul(b', a' ∩ b)))",
	}),
		"ZassenhausLeft, then ZassenhausRight turned round by IsomorphicSym, "+
			"composed by IsomorphicTrans at the middle quotient group"),
})}
