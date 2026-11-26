// locally_ringed_space.go — ring presheaves and their stalks, sheaves of
// rings, locally ringed spaces, and their isomorphisms.
//
// Ring operations on sections are indexed by the open set. Restrictions
// preserve those operations, so they descend to germs and the ring laws
// hold on common representatives. The germ operations are defined by
// unions over representatives and require no choice of representatives.

package locally_ringed_space

import (
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/abelian_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/proofs/topology/presheaf"
	"github.com/euc-ai/xugo/library/proofs/topology/topological_space"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// Ring presheaves and their stalks
// ---------------------------------------------------------------------------

// PresheafOfRings — rings of sections with restriction homomorphisms.
// The homomorphism from U to itself supplies the ring on F(U).
var PresheafOfRings = presheafOfRingsThm{family.DefineStructure(registry.DefEntry{
	Name:    "PresheafOfRings",
	Key:     "prop_892e04364cfa0de8",
	Const:   "presheaf_of_rings",
	Subject: "F",
	Type:    "set(set(A)) → (set(A) → ring_ops(B)) → (set(A) → set(A) → B → B) → bool",
	Equations: []string{
		"∀T:set(set(A)). ∀F:(set(A) → ring_ops(B)). ∀res:(set(A) → set(A) → B → B). " +
			"    presheaf_of_rings(T, F, res) ⇔ " +
			"    presheaf(T, (λU:set(A). F(U).carrier), res) ∧ " +
			"    (∀U V:set(A). U ∈ T ∧ V ∈ T ∧ V ⊆ U ⇒ ring_homomorphism(F(U), F(V), res(U, V)))",
	},
})}

// Presheaf — forgetting the ring operations gives the underlying presheaf.
var Presheaf = presheafThm{family.Add(registry.ProofEntry{
	Name:  "Presheaf",
	Key:   "prop_e50182665ea17a4a",
	Build: PresheafOfRings.Axiom("presheaf(T, (λU:set(A). F(U).carrier), res)"),
})}

// PresheafRestrictHomomorphism — restriction preserves the section ring operations.
var PresheafRestrictHomomorphism = presheafRestrictHomomorphismThm{family.Add(registry.ProofEntry{
	Name: "PresheafRestrictHomomorphism",
	Key:  "prop_33ff27393a4ebef",
	Build: PresheafOfRings.Axiom(Statement{
		Binders: "∀U V:set(A).",
		Hypotheses: []string{
			"U ∈ T",
			"V ∈ T",
			"V ⊆ U",
		},
		Conclusion: "ring_homomorphism(F(U), F(V), res(U, V))",
	}),
})}

// SheafOfRings — a sheaf of section-ring records whose restrictions
// are ring homomorphisms. The identity restriction supplies each ring.
var SheafOfRings = sheafOfRingsThm{family.DefineStructure(registry.DefEntry{
	Name:    "SheafOfRings",
	Key:     "prop_114007f6ec9c9c1a",
	Const:   "sheaf_of_rings",
	Subject: "F",
	Type:    "set(set(A)) → (set(A) → ring_ops(B)) → (set(A) → set(A) → B → B) → bool",
	Equations: []string{
		"∀T:set(set(A)). ∀F:(set(A) → ring_ops(B)). ∀res:(set(A) → set(A) → B → B). " +
			"    sheaf_of_rings(T, F, res) ⇔ " +
			"    sheaf(T, (λU:set(A). F(U).carrier), res) ∧ " +
			"    (∀U V:set(A). U ∈ T ∧ V ∈ T ∧ V ⊆ U ⇒ ring_homomorphism(F(U), F(V), res(U, V)))",
	},
})}

// Sheaf — a sheaf of rings is a sheaf.
var Sheaf = sheafThm{family.Add(registry.ProofEntry{
	Name:  "Sheaf",
	Key:   "prop_78022ff7f973b940",
	Build: SheafOfRings.Axiom("sheaf(T, (λU:set(A). F(U).carrier), res)"),
})}

// RestrictHomomorphism — the restrictions are ring homomorphisms, from
// the ring of sections F(U) to F(V).
var RestrictHomomorphism = restrictHomomorphismThm{family.Add(registry.ProofEntry{
	Name: "RestrictHomomorphism",
	Key:  "prop_4ab5419956c384c6",
	Build: SheafOfRings.Axiom(Statement{
		Binders: "∀U V:set(A).",
		Hypotheses: []string{
			"U ∈ T",
			"V ∈ T",
			"V ⊆ U",
		},
		Conclusion: "ring_homomorphism(F(U), F(V), res(U, V))",
	}),
})}

// SheafPresheafOfRings — the underlying presheaf retains the restriction homomorphisms.
var SheafPresheafOfRings = sheafPresheafOfRingsThm{family.Add(registry.ProofEntry{
	Name: "SheafPresheafOfRings",
	Key:  "prop_9f66db372215f3ff",
	Build: SheafOfRings.Law("presheaf_of_rings(T, F, res)",
		func(a *Argument, ringSheaf SheafOfRingsFact[on.T]) {
			a.Do(Unfold(PresheafOfRings),
				SplitConj(
					Case(
						"the underlying sheaf is a presheaf",
						By(presheaf.SheafPresheaf.Read(Sheaf.Read(ringSheaf)))),
					Case(
						"restriction maps preserve the section rings",
						By(RestrictHomomorphism.Read(ringSheaf))),
				))
		}),
})}

// SheafRestriction — `sheaf_restriction(S, U)`: the sheaf of rings S
// over the open U, the topology restricted to U and the other
// components as they are, named once.
var SheafRestriction = family.Tuple("sheaf_restriction", []string{"S", "U"},
	"subtopology(U)", "S.F", "S.res")

// StalkAddDef — `stalk_add(T, F, res, x, g, h)`: the germs at x of
// s + t over U ∩ V, for (U, s) in g and (V, t) in h, each restricted to
// U ∩ V, united.
var StalkAddDef = stalkAddDefThm{family.Define(registry.DefEntry{
	Name:  "StalkAddDef",
	Key:   "prop_c74af14223829482",
	Const: "stalk_add",
	Type: "set(set(A)) → " +
		"(set(A) → ring_ops(B)) → " +
		"(set(A) → set(A) → B → B) → " +
		"A → " +
		"set(prod(set(A), B)) → " +
		"set(prod(set(A), B)) → " +
		"set(prod(set(A), B))",
	Implicit: []string{"T", "F", "res"},
	Equations: []string{
		"∀T:set(set(A)). " +
			"∀F:(set(A) → ring_ops(B)). " +
			"∀res:(set(A) → set(A) → B → B). " +
			"∀x:A. " +
			"∀g:set(prod(set(A), B)). " +
			"∀h:set(prod(set(A), B)). " +
			"    stalk_add(T, F, res, x, g, h) = " +
			"    ⋃{sheaf_germ(T, " +
			"            (λU:set(A). F(U).carrier), " +
			"            res, " +
			"            x, " +
			"            U ∩ V, " +
			"            F(U ∩ V).add(res(U, U ∩ V, s), res(V, U ∩ V, t))) | " +
			"        U:set(A), " +
			"        s:B, " +
			"        V:set(A), " +
			"        t:B | " +
			"        (U, s) ∈ g ∧ (V, t) ∈ h}",
	},
})}

// StalkMulDef — `stalk_mul(T, F, res, x, g, h)`: the germs of the
// products, united.
var StalkMulDef = stalkMulDefThm{family.Define(registry.DefEntry{
	Name:  "StalkMulDef",
	Key:   "prop_7c7ae331a46aed01",
	Const: "stalk_mul",
	Type: "set(set(A)) → " +
		"(set(A) → ring_ops(B)) → " +
		"(set(A) → set(A) → B → B) → " +
		"A → " +
		"set(prod(set(A), B)) → " +
		"set(prod(set(A), B)) → " +
		"set(prod(set(A), B))",
	Implicit: []string{"T", "F", "res"},
	Equations: []string{
		"∀T:set(set(A)). " +
			"∀F:(set(A) → ring_ops(B)). " +
			"∀res:(set(A) → set(A) → B → B). " +
			"∀x:A. " +
			"∀g:set(prod(set(A), B)). " +
			"∀h:set(prod(set(A), B)). " +
			"    stalk_mul(T, F, res, x, g, h) = " +
			"    ⋃{sheaf_germ(T, " +
			"            (λU:set(A). F(U).carrier), " +
			"            res, " +
			"            x, " +
			"            U ∩ V, " +
			"            F(U ∩ V).mul(res(U, U ∩ V, s), res(V, U ∩ V, t))) | " +
			"        U:set(A), " +
			"        s:B, " +
			"        V:set(A), " +
			"        t:B | " +
			"        (U, s) ∈ g ∧ (V, t) ∈ h}",
	},
})}

// StalkNegDef — `stalk_neg(T, F, res, x, g)`: the germs of the
// negations, united.
var StalkNegDef = stalkNegDefThm{family.Define(registry.DefEntry{
	Name:  "StalkNegDef",
	Key:   "prop_f08965a99dcca659",
	Const: "stalk_neg",
	Type: "set(set(A)) → " +
		"(set(A) → ring_ops(B)) → " +
		"(set(A) → set(A) → B → B) → " +
		"A → " +
		"set(prod(set(A), B)) → " +
		"set(prod(set(A), B))",
	Implicit: []string{"T", "F", "res"},
	Equations: []string{
		"∀T:set(set(A)). " +
			"∀F:(set(A) → ring_ops(B)). " +
			"∀res:(set(A) → set(A) → B → B). " +
			"∀x:A. " +
			"∀g:set(prod(set(A), B)). " +
			"    stalk_neg(T, F, res, x, g) = " +
			"    ⋃{sheaf_germ(T, (λU:set(A). F(U).carrier), res, x, U, F(U).neg(s)) | " +
			"        U:set(A), " +
			"        s:B | " +
			"        (U, s) ∈ g}",
	},
})}

// StalkSubDef — `stalk_sub(T, F, res, x, g, h)`: g plus the
// negation of h.
var StalkSubDef = stalkSubDefThm{family.Define(registry.DefEntry{
	Name:  "StalkSubDef",
	Key:   "prop_35ebd9ea37ea8c4c",
	Const: "stalk_sub",
	Type: "set(set(A)) → " +
		"(set(A) → ring_ops(B)) → " +
		"(set(A) → set(A) → B → B) → " +
		"A → " +
		"set(prod(set(A), B)) → " +
		"set(prod(set(A), B)) → " +
		"set(prod(set(A), B))",
	Implicit: []string{"T", "F", "res"},
	Equations: []string{
		"∀T:set(set(A)). " +
			"∀F:(set(A) → ring_ops(B)). " +
			"∀res:(set(A) → set(A) → B → B). " +
			"∀x:A. " +
			"∀g:set(prod(set(A), B)). " +
			"∀h:set(prod(set(A), B)). " +
			"    stalk_sub(T, F, res, x, g, h) = stalk_add(T, F, res, x, g, stalk_neg(T, F, res, x, h))",
	},
	Deps: []registry.EntryLike{StalkAddDef, StalkNegDef},
})}

// StalkZeroDef — `stalk_zero(T, F, res, x)`: the germ at x of the
// zero section over the whole space.
var StalkZeroDef = stalkZeroDefThm{family.Define(registry.DefEntry{
	Name:  "StalkZeroDef",
	Key:   "prop_b5612ffb88507285",
	Const: "stalk_zero",
	Type: "set(set(A)) → " +
		"(set(A) → ring_ops(B)) → " +
		"(set(A) → set(A) → B → B) → " +
		"A → " +
		"set(prod(set(A), B))",
	Implicit: []string{"T", "F", "res"},
	Equations: []string{
		"∀T:set(set(A)). ∀F:(set(A) → ring_ops(B)). ∀res:(set(A) → set(A) → B → B). ∀x:A. " +
			"    stalk_zero(T, F, res, x) = sheaf_germ(T, (λU:set(A). F(U).carrier), res, x, ⋃T, F(⋃T).zero)",
	},
})}

// StalkOneDef — `stalk_one(T, F, res, x)`: the germ at x of the
// one section over the whole space.
var StalkOneDef = stalkOneDefThm{family.Define(registry.DefEntry{
	Name:  "StalkOneDef",
	Key:   "prop_a0b1a18c2aaaee77",
	Const: "stalk_one",
	Type: "set(set(A)) → " +
		"(set(A) → ring_ops(B)) → " +
		"(set(A) → set(A) → B → B) → " +
		"A → " +
		"set(prod(set(A), B))",
	Implicit: []string{"T", "F", "res"},
	Equations: []string{
		"∀T:set(set(A)). ∀F:(set(A) → ring_ops(B)). ∀res:(set(A) → set(A) → B → B). ∀x:A. " +
			"    stalk_one(T, F, res, x) = sheaf_germ(T, (λU:set(A). F(U).carrier), res, x, ⋃T, F(⋃T).one)",
	},
})}

// StalkRingDef — the operations and carrier of the germs at x, held together.
var StalkRingDef = stalkRingDefThm{family.Define(registry.DefEntry{
	Name: "StalkRingDef",
	Key:  "prop_9c26fc426164c730", Const: "stalk_ring",
	Type: "set(set(A)) → " +
		"(set(A) → ring_ops(B)) → " +
		"(set(A) → set(A) → B → B) → " +
		"A → " +
		"ring_ops(set(prod(set(A), B)))",
	Implicit: []string{"T", "F", "res"},
	Equations: []string{
		"∀T:set(set(A)). ∀F:(set(A) → ring_ops(B)). ∀res:(set(A) → set(A) → B → B). ∀x:A. " +
			"    stalk_ring(T, F, res, x) = " +
			"    mk_ring(stalk_add(T, F, res, x), " +
			"        stalk_zero(T, F, res, x), " +
			"        stalk_neg(T, F, res, x), " +
			"        stalk_mul(T, F, res, x), " +
			"        stalk_one(T, F, res, x), " +
			"        stalk_sub(T, F, res, x), " +
			"        stalk(T, (λU:set(A). F(U).carrier), res, x))",
	},
	Deps: []registry.EntryLike{
		StalkAddDef,
		StalkZeroDef,
		StalkNegDef,
		StalkMulDef,
		StalkOneDef,
		StalkSubDef,
	},
})}

// SectionRing — the sections over an open set form a ring: restricting
// from U to U itself is a ring homomorphism, and its source is the ring
// on F(U).
var SectionRing = sectionRingThm{family.Add(registry.ProofEntry{
	Name: "SectionRing",
	Key:  "prop_63f1e7cd7d0699c3",
	Build: PresheafOfRings.Law(Statement{
		Binders: "∀U:set(A).",
		Hypotheses: []string{
			"U ∈ T",
		},
		Conclusion: "comm_ring_on(F(U))",
	},
		func(a *Argument, ringPresheaf PresheafOfRingsFact[on.T], U *Member[Set[A], on.T]) {
			selfRestrictionHom := a.Have(
				"restricting from U to U itself is a ring homomorphism",
				"ring_homomorphism(F(U), F(U), res(U, U))",
				By(PresheafRestrictHomomorphism.Read(ringPresheaf), U, set_order.SubsetRefl))
			a.Show(
				"and the source of a ring homomorphism is a ring",
				By(ring_homomorphism.Source.Read(selfRestrictionHom)))
		}),
})}

// GermAdd — the sum of the germs of two sections over one open W is the
// germ of their sum: the sum of sections keeps to the sections and
// commutes with restriction, each restriction being a ring
// homomorphism.
var GermAdd = germAddThm{family.Add(registry.ProofEntry{
	Name: "GermAdd",
	Key:  "prop_d098c2db9173b6fc",
	Build: PresheafOfRings.Law(Statement{
		Binders: "∀x:A. ∀W:set(A). ∀s t:B.",
		Hypotheses: []string{
			"W ∈ T",
			"x ∈ W",
			"s ∈ F(W).carrier",
			"t ∈ F(W).carrier",
		},
		Conclusion: "stalk_add(T, " +
			"    F, " +
			"    res, " +
			"    x, " +
			"    sheaf_germ(T, λU:set(A). F(U).carrier, res, x, W, s), " +
			"    sheaf_germ(T, λU:set(A). F(U).carrier, res, x, W, t)) = " +
			"sheaf_germ(T, λU:set(A). F(U).carrier, res, x, W, F(W).add(s, t))",
	},
		func(
			a *Argument,
			ringPresheaf PresheafOfRingsFact[on.T],
			x *Expr[A],
			W *Expr[Set[A]],
			s, t *Expr[B],
			hypotheses Fact,
		) {
			addClosed := a.Have(
				"a sum of sections over an open set is a section over it",
				"∀U:set(A). ∀u v:B. U ∈ T ∧ u ∈ F(U).carrier ∧ v ∈ F(U).carrier ⇒ F(U).add(u, v) ∈ F(U).carrier",
				Derive(func(b *Argument) {
					b.FixAs[Set[A]]("U")
					b.FixAs[B]("u")
					b.FixAs[B]("v")
					members := b.Assume()
					sectionRing := b.Have(
						"the sections over U form a ring",
						"comm_ring_on(F(U))",
						By(SectionRing.Read(ringPresheaf), members))
					b.Show(
						"closed under its sum",
						By(comm_ring.AddIn.Read(sectionRing), members))
				}))
			restrictAdd := a.Have(
				"restriction keeps the sum",
				Statement{
					Binders: "∀U V:set(A). ∀u v:B.",
					Hypotheses: []string{
						"U ∈ T",
						"V ∈ T",
						"V ⊆ U",
						"u ∈ F(U).carrier",
						"v ∈ F(U).carrier",
					},
					Conclusion: "res(U, V, F(U).add(u, v)) = F(V).add(res(U, V, u), res(U, V, v))",
				},
				Derive(func(b *Argument) {
					b.FixAs[Set[A]]("U")
					b.FixAs[Set[A]]("V")
					b.FixAs[B]("u")
					b.FixAs[B]("v")
					members := b.Assume()
					restrictionHom := b.Have(
						"restricting from U to V is a ring homomorphism",
						"ring_homomorphism(F(U), F(V), res(U, V))",
						By(PresheafRestrictHomomorphism.Read(ringPresheaf), members))
					b.Show(
						"which keeps the sum",
						By(ring_homomorphism.MapAdd.Read(restrictionHom), members))
				}))
			a.Show(
				"the sum of the germs is the union of the germs of "+
					"the sums of representatives, the germ of add(W, s, t)",
				Simp(Fwd(StalkAddDef)),
				By(
					Presheaf.Read(ringPresheaf),
					addClosed,
					restrictAdd,
					hypotheses,
					Where(presheaf.GermOperation, "op", a.Term("(λU:set(A). F(U).add)"))))
		}),
})}

// GermMul — the product of the germs of two sections over one open W is
// the germ of their product, as the sum is (GermAdd).
var GermMul = germMulThm{family.Add(registry.ProofEntry{
	Name: "GermMul",
	Key:  "prop_674fddeec77c429",
	Build: PresheafOfRings.Law(Statement{
		Binders: "∀x:A. ∀W:set(A). ∀s t:B.",
		Hypotheses: []string{
			"W ∈ T",
			"x ∈ W",
			"s ∈ F(W).carrier",
			"t ∈ F(W).carrier",
		},
		Conclusion: "stalk_mul(T, " +
			"    F, " +
			"    res, " +
			"    x, " +
			"    sheaf_germ(T, λU:set(A). F(U).carrier, res, x, W, s), " +
			"    sheaf_germ(T, λU:set(A). F(U).carrier, res, x, W, t)) = " +
			"sheaf_germ(T, λU:set(A). F(U).carrier, res, x, W, F(W).mul(s, t))",
	},
		func(
			a *Argument,
			ringPresheaf PresheafOfRingsFact[on.T],
			x *Expr[A],
			W *Expr[Set[A]],
			s, t *Expr[B],
			hypotheses Fact,
		) {
			mulClosed := a.Have(
				"a product of sections over an open set is a section over it",
				"∀U:set(A). ∀u v:B. U ∈ T ∧ u ∈ F(U).carrier ∧ v ∈ F(U).carrier ⇒ F(U).mul(u, v) ∈ F(U).carrier",
				Derive(func(b *Argument) {
					b.FixAs[Set[A]]("U")
					b.FixAs[B]("u")
					b.FixAs[B]("v")
					members := b.Assume()
					sectionRing := b.Have(
						"the sections over U form a ring",
						"comm_ring_on(F(U))",
						By(SectionRing.Read(ringPresheaf), members))
					b.Show(
						"closed under its product",
						By(comm_ring.MulIn.Read(sectionRing), members))
				}))
			restrictMul := a.Have(
				"restriction keeps the product",
				Statement{
					Binders: "∀U V:set(A). ∀u v:B.",
					Hypotheses: []string{
						"U ∈ T",
						"V ∈ T",
						"V ⊆ U",
						"u ∈ F(U).carrier",
						"v ∈ F(U).carrier",
					},
					Conclusion: "res(U, V, F(U).mul(u, v)) = F(V).mul(res(U, V, u), res(U, V, v))",
				},
				Derive(func(b *Argument) {
					b.FixAs[Set[A]]("U")
					b.FixAs[Set[A]]("V")
					b.FixAs[B]("u")
					b.FixAs[B]("v")
					members := b.Assume()
					restrictionHom := b.Have(
						"restricting from U to V is a ring homomorphism",
						"ring_homomorphism(F(U), F(V), res(U, V))",
						By(PresheafRestrictHomomorphism.Read(ringPresheaf), members))
					b.Show(
						"which keeps the product",
						By(ring_homomorphism.MapMul.Read(restrictionHom), members))
				}))
			a.Show(
				"the product of the germs is the union of the germs of "+
					"the products of representatives, the germ of mul(W, s, t)",
				Simp(Fwd(StalkMulDef)),
				By(
					Presheaf.Read(ringPresheaf),
					mulClosed,
					restrictMul,
					hypotheses,
					Where(presheaf.GermOperation, "op", a.Term("(λU:set(A). F(U).mul)"))))
		}),
})}

// GermNeg — negation preserves sections and commutes with restriction,
// so presheaf.GermUnaryOperation induces it on germs.
var GermNeg = germNegThm{family.Add(registry.ProofEntry{
	Name: "GermNeg",
	Key:  "prop_52b3303d0c9add8c",
	Build: PresheafOfRings.Law(Statement{
		Binders: "∀x:A. ∀U:set(A). ∀s:B.",
		Hypotheses: []string{
			"U ∈ T",
			"x ∈ U",
			"s ∈ F(U).carrier",
		},
		Conclusion: "stalk_neg(T, F, res, x, sheaf_germ(T, λU:set(A). F(U).carrier, res, x, U, s)) = " +
			"sheaf_germ(T, λU:set(A). F(U).carrier, res, x, U, F(U).neg(s))",
	},
		func(
			a *Argument,
			ringPresheaf PresheafOfRingsFact[on.T],
			x *Expr[A],
			U *Expr[Set[A]],
			s *Expr[B],
			hypotheses Fact,
		) {
			negClosed := a.Have(
				"the negation of a section over an open set is a section over it",
				"∀V:set(A). ∀u:B. V ∈ T ∧ u ∈ F(V).carrier ⇒ F(V).neg(u) ∈ F(V).carrier",
				Derive(func(b *Argument) {
					b.FixAs[Set[A]]("V")
					b.FixAs[B]("u")
					members := b.Assume()
					sectionRing := b.Have(
						"the sections over V form a ring",
						"comm_ring_on(F(V))",
						By(SectionRing.Read(ringPresheaf), members))
					b.Show(
						"closed under negation",
						By(comm_ring.NegIn.Read(sectionRing), members))
				}))
			restrictNeg := a.Have(
				"restriction keeps the negation",
				Statement{
					Binders: "∀V W:set(A). ∀u:B.",
					Hypotheses: []string{
						"V ∈ T",
						"W ∈ T",
						"W ⊆ V",
						"u ∈ F(V).carrier",
					},
					Conclusion: "res(V, W, F(V).neg(u)) = F(W).neg(res(V, W, u))",
				},
				Derive(func(b *Argument) {
					b.FixAs[Set[A]]("V")
					b.FixAs[Set[A]]("W")
					b.FixAs[B]("u")
					members := b.Assume()
					restrictionHom := b.Have(
						"restricting from V to W is a ring homomorphism",
						"ring_homomorphism(F(V), F(W), res(V, W))",
						By(PresheafRestrictHomomorphism.Read(ringPresheaf), members))
					b.Show(
						"which keeps the negation, as a homomorphism of the additive groups",
						By(ring_homomorphism.MapNeg.Read(restrictionHom), members))
				}))
			a.Show(
				"the unary operation on germs sends the germ of s to the germ of its negation",
				Simp(Fwd(StalkNegDef)),
				By(
					Presheaf.Read(ringPresheaf),
					negClosed,
					restrictNeg,
					hypotheses,
					Where(presheaf.GermUnaryOperation, "op", a.TermAs[Fun2[Set[A], B, B]]("(λU:set(A). F(U).neg)"))))
		}),
})}

// GermZero — zero sections are preserved by restriction, so their germs
// agree on every open neighbourhood of the point.
var GermZero = germZeroThm{family.Add(registry.ProofEntry{
	Name: "GermZero",
	Key:  "prop_9e0848cd681d91f6",
	Build: PresheafOfRings.Law(Statement{
		Binders: "∀x:A. ∀W:set(A).",
		Hypotheses: []string{
			"W ∈ T",
			"x ∈ W",
		},
		Conclusion: "stalk_zero(T, F, res, x) = " +
			"sheaf_germ(T, λU:set(A). F(U).carrier, res, x, W, F(W).zero)",
	},
		func(
			a *Argument,
			ringPresheaf PresheafOfRingsFact[on.T],
			x *Expr[A],
			W *Expr[Set[A]],
			neighborhood Fact,
		) {
			zeroSection := a.Have(
				"zero over an open set is a section over it",
				"∀U:set(A). U ∈ T ⇒ F(U).zero ∈ F(U).carrier",
				Derive(func(b *Argument) {
					b.FixAs[Set[A]]("U")
					open := b.Assume()
					sectionRing := b.Have(
						"the sections over U form a ring",
						"comm_ring_on(F(U))",
						By(SectionRing.Read(ringPresheaf), open))
					b.Show(
						"its zero is a section",
						By(comm_ring.ZeroIn.Read(sectionRing)))
				}))
			restrictZero := a.Have(
				"restriction preserves zero",
				"∀U:set(A). ∀V:set(A). U ∈ T ∧ V ∈ T ∧ V ⊆ U ⇒ res(U, V, F(U).zero) = F(V).zero",
				Derive(func(b *Argument) {
					b.FixAs[Set[A]]("U")
					b.FixAs[Set[A]]("V")
					opens := b.Assume()
					restrictionHom := b.Have(
						"restricting from U to V is a ring homomorphism",
						"ring_homomorphism(F(U), F(V), res(U, V))",
						By(PresheafRestrictHomomorphism.Read(ringPresheaf), opens))
					b.Show(
						"its additive homomorphism preserves zero",
						By(ring_homomorphism.MapZero.Read(restrictionHom)))
				}))
			a.Show(
				"the germ of zero is independent of its open neighbourhood",
				Simp(Fwd(StalkZeroDef)),
				By(
					restrictZero,
					zeroSection,
					neighborhood,
					presheaf.GermConstant.Read(Presheaf.Read(ringPresheaf)).AsFact().At(
						a.TermAs[Fun[Set[A], B]]("(λU:set(A). F(U).zero)"), x, W)))
		}),
})}

// GermOne — unit sections are preserved by restriction, so their germs
// agree on every open neighbourhood of the point.
var GermOne = germOneThm{family.Add(registry.ProofEntry{
	Name: "GermOne",
	Key:  "prop_96cbfa7d0a905aa8",
	Build: PresheafOfRings.Law(Statement{
		Binders: "∀x:A. ∀W:set(A).",
		Hypotheses: []string{
			"W ∈ T",
			"x ∈ W",
		},
		Conclusion: "stalk_one(T, F, res, x) = sheaf_germ(T, λU:set(A). F(U).carrier, res, x, W, F(W).one)",
	},
		func(
			a *Argument,
			ringPresheaf PresheafOfRingsFact[on.T],
			x *Expr[A],
			W *Expr[Set[A]],
			neighborhood Fact,
		) {
			oneSection := a.Have(
				"one over an open set is a section over it",
				"∀U:set(A). U ∈ T ⇒ F(U).one ∈ F(U).carrier",
				Derive(func(b *Argument) {
					b.FixAs[Set[A]]("U")
					open := b.Assume()
					sectionRing := b.Have(
						"the sections over U form a ring",
						"comm_ring_on(F(U))",
						By(SectionRing.Read(ringPresheaf), open))
					b.Show(
						"its one is a section",
						By(comm_ring.OneIn.Read(sectionRing)))
				}))
			restrictOne := a.Have(
				"restriction preserves one",
				"∀U:set(A). ∀V:set(A). U ∈ T ∧ V ∈ T ∧ V ⊆ U ⇒ res(U, V, F(U).one) = F(V).one",
				Derive(func(b *Argument) {
					b.FixAs[Set[A]]("U")
					b.FixAs[Set[A]]("V")
					opens := b.Assume()
					restrictionHom := b.Have(
						"restricting from U to V is a ring homomorphism",
						"ring_homomorphism(F(U), F(V), res(U, V))",
						By(PresheafRestrictHomomorphism.Read(ringPresheaf), opens))
					b.Show(
						"the homomorphism preserves one",
						By(ring_homomorphism.MapOne.Read(restrictionHom)))
				}))
			a.Show(
				"the germ of one is independent of its open neighbourhood",
				Simp(Fwd(StalkOneDef)),
				By(
					restrictOne,
					oneSection,
					neighborhood,
					presheaf.GermConstant.Read(Presheaf.Read(ringPresheaf)).AsFact().At(
						a.TermAs[Fun[Set[A], B]]("(λU:set(A). F(U).one)"), x, W)))
		}),
})}

// StalkRing — choose representatives over a common open neighbourhood and
// transfer each ring law from its section ring to the germs. Unfolding
// comm_ring_on, abelian_group_on, group_on and comm_monoid_on exposes the
// closure, identity, inverse, associativity and distributivity obligations.
var StalkRing = stalkRingThm{family.Add(registry.ProofEntry{
	Name: "StalkRing",
	Key:  "prop_5b9f579cd06b67bf",
	Reading: "x ∈ ⋃T is load-bearing: for x outside the space the stalk " +
		"is ∅, while comm_ring_on asks the zero germ to lie in the carrier.",
	Build: PresheafOfRings.Law(Statement{
		Binders: "∀x:A.",
		Hypotheses: []string{
			"x ∈ ⋃T",
		},
		Conclusion: "comm_ring_on(stalk_ring(T, F, res, x))",
	},
		func(a *Argument, ringPresheaf PresheafOfRingsFact[on.T], x *Expr[A], inSpace Fact) {
			underlyingPresheaf := a.Simplified(Presheaf.Read(ringPresheaf))
			spaceOpen := a.Have(
				"the whole space is open",
				"⋃T ∈ T",
				By(topological_space.SpaceOpen.Read(presheaf.Topology.Read(underlyingPresheaf))))
			germInStalk := presheaf.GermInStalk.Read(underlyingPresheaf)
			space := a.TermAs[Set[A]]("⋃T")
			ringOn := ext.WrapTerm(a.Ctx().ConstAs[Fun[module_record.RingOps[B], Bool]]("comm_ring_on").Core())
			zero := ext.WrapTerm(a.Ctx().ConstAs[Fun[module_record.RingOps[B], B]]("ring_zero").Core())
			one := ext.WrapTerm(a.Ctx().ConstAs[Fun[module_record.RingOps[B], B]]("ring_one").Core())
			F := a.Term("F")
			germ := a.Term("sheaf_germ(T, (λU:set(A). F(U).carrier), res, x)")

			// Each case fixes its germs before choosing common representatives.
			// The returned memberships and section ring are all over the final W.
			representGerms := func(
				b *Argument,
				germs ...*Expr[Set[Prod[Set[A], B]]],
			) (presheaf.CommonGerms, Fact) {
				germMembers := b.Assume()
				neighborhood := b.Have(
					"the whole space is an open neighbourhood of x",
					"⋃T ∈ T ∧ x ∈ ⋃T",
					By(spaceOpen, inSpace))
				inputs := make([]presheaf.GermInput, len(germs))
				for i, g := range germs {
					inputs[i] = presheaf.GermInput{Presheaf: underlyingPresheaf, Germ: g, Member: germMembers}
				}
				representatives := presheaf.CommonRepresentatives(b, x, space, neighborhood, inputs...)
				W := representatives.Neighborhood
				sectionRing := b.Have(
					"the sections over the common neighbourhood form a ring",
					MakeProp(ringOn.Apply(F.Apply(W))),
					By(SectionRing.Read(ringPresheaf), representatives.NeighborhoodFact))
				for _, germEquality := range representatives.Equalities {
					b.Do(germEquality.Rw())
				}
				return representatives, sectionRing
			}
			a.Do(Unfold(StalkRingDef), Unfold(comm_ring.CommRingOn), Unfold(
				abelian_group.AbelianGroupOn), Unfold(
				group.GroupOn), Unfold(comm_monoid.CommMonoidOn), SplitConjAll(
				Case(
					"the zero germ lies in the stalk",
					Derive(func(b *Argument) {
						sectionRing := b.Have(
							"the sections over the whole space form a ring",
							"comm_ring_on(F(⋃T))",
							By(SectionRing.Read(ringPresheaf), spaceOpen))
						b.Show(
							"zero over the whole space represents the zero germ",
							Simp(Fwd(StalkZeroDef)),
							By(germInStalk, spaceOpen, inSpace, comm_ring.ZeroIn.Read(sectionRing)))
					})),
				Case(
					"a sum of germs is a germ",
					Derive(func(b *Argument) {
						g, h := b.FixAs[Set[Prod[Set[A], B]]]("g"), b.FixAs[Set[Prod[Set[A], B]]]("h")
						representatives, sectionRing := representGerms(b, g, h)
						b.Show(
							"the sum is represented by a section over the common neighbourhood",
							Simp(Fwd(GermAdd.Read(ringPresheaf))),
							By(
								germInStalk,
								representatives.NeighborhoodFact,
								representatives.Members[0],
								representatives.Members[1],
								comm_ring.AddIn.Read(sectionRing)))
					})),
				Case(
					"the negation of a germ is a germ",
					Derive(func(b *Argument) {
						g := b.FixAs[Set[Prod[Set[A], B]]]("g")
						representatives, sectionRing := representGerms(b, g)
						b.Show(
							"negating its representative gives a section over the same neighbourhood",
							Simp(Fwd(GermNeg.Read(ringPresheaf))),
							By(
								germInStalk,
								representatives.NeighborhoodFact,
								representatives.Members[0],
								comm_ring.NegIn.Read(sectionRing)))
					})),
				Case(
					"addition associates",
					Derive(func(b *Argument) {
						g, h, k :=
							b.FixAs[Set[Prod[Set[A], B]]]("g"),
							b.FixAs[Set[Prod[Set[A], B]]]("h"),
							b.FixAs[Set[Prod[Set[A], B]]]("k")
						representatives, sectionRing := representGerms(b, g, h, k)
						b.Show(
							"both sums are germs of the associative sums in the section ring",
							Simp(Fwd(GermAdd.Read(ringPresheaf)), Fwd(comm_ring.AddIn.Read(sectionRing))),
							Congr(),
							ByArith(
								sectionRing,
								representatives.Members[0],
								representatives.Members[1],
								representatives.Members[2]))
					})),
				Case(
					"the zero germ is a left identity",
					Derive(func(b *Argument) {
						g := b.FixAs[Set[Prod[Set[A], B]]]("g")
						representatives, sectionRing := representGerms(b, g)
						W := representatives.Neighborhood
						zeroGerm := b.Have(
							"represent the zero germ over the final neighbourhood",
							MakeProp(Equal(b.Term("stalk_zero(T, F, res, x)"), germ.Apply(W, zero.Apply(F.Apply(W))))),
							By(GermZero.Read(ringPresheaf), representatives.NeighborhoodFact))
						b.Show(
							"zero is a left identity in the section ring",
							zeroGerm.Rw(),
							Simp(Fwd(GermAdd.Read(ringPresheaf)), Fwd(comm_ring.ZeroIn.Read(sectionRing))),
							Congr(),
							ByArith(sectionRing, representatives.Members[0]))
					})),
				Case(
					"the negation is a left inverse",
					Derive(func(b *Argument) {
						g := b.FixAs[Set[Prod[Set[A], B]]]("g")
						representatives, sectionRing := representGerms(b, g)
						W := representatives.Neighborhood
						zeroGerm := b.Have(
							"represent the zero germ over the final neighbourhood",
							MakeProp(Equal(b.Term("stalk_zero(T, F, res, x)"), germ.Apply(W, zero.Apply(F.Apply(W))))),
							By(GermZero.Read(ringPresheaf), representatives.NeighborhoodFact))
						b.Show(
							"the representative and its negation sum to zero",
							zeroGerm.Rw(),
							Simp(
								Fwd(GermNeg.Read(ringPresheaf)),
								Fwd(GermAdd.Read(ringPresheaf)),
								Fwd(comm_ring.NegIn.Read(sectionRing))),
							Congr(),
							ByArith(sectionRing, representatives.Members[0]))
					})),
				Case(
					"addition commutes",
					Derive(func(b *Argument) {
						g, h := b.FixAs[Set[Prod[Set[A], B]]]("g"), b.FixAs[Set[Prod[Set[A], B]]]("h")
						representatives, sectionRing := representGerms(b, g, h)
						b.Show(
							"addition commutes in the section ring",
							Simp(Fwd(GermAdd.Read(ringPresheaf))),
							Congr(),
							ByArith(sectionRing, representatives.Members[0], representatives.Members[1]))
					})),
				Case(
					"the one germ lies in the stalk",
					Derive(func(b *Argument) {
						sectionRing := b.Have(
							"the sections over the whole space form a ring",
							"comm_ring_on(F(⋃T))",
							By(SectionRing.Read(ringPresheaf), spaceOpen))
						b.Show(
							"one over the whole space represents the one germ",
							Simp(Fwd(StalkOneDef)),
							By(germInStalk, spaceOpen, inSpace, comm_ring.OneIn.Read(sectionRing)))
					})),
				Case(
					"a product of germs is a germ",
					Derive(func(b *Argument) {
						g, h := b.FixAs[Set[Prod[Set[A], B]]]("g"), b.FixAs[Set[Prod[Set[A], B]]]("h")
						representatives, sectionRing := representGerms(b, g, h)
						b.Show(
							"the product is represented by a section over the common neighbourhood",
							Simp(Fwd(GermMul.Read(ringPresheaf))),
							By(
								germInStalk,
								representatives.NeighborhoodFact,
								representatives.Members[0],
								representatives.Members[1],
								comm_ring.MulIn.Read(sectionRing)))
					})),
				Case(
					"multiplication commutes",
					Derive(func(b *Argument) {
						g, h := b.FixAs[Set[Prod[Set[A], B]]]("g"), b.FixAs[Set[Prod[Set[A], B]]]("h")
						representatives, sectionRing := representGerms(b, g, h)
						b.Show(
							"multiplication commutes in the section ring",
							Simp(Fwd(GermMul.Read(ringPresheaf))),
							Congr(),
							ByArith(sectionRing, representatives.Members[0], representatives.Members[1]))
					})),
				Case(
					"multiplication associates",
					Derive(func(b *Argument) {
						g, h, k :=
							b.FixAs[Set[Prod[Set[A], B]]]("g"),
							b.FixAs[Set[Prod[Set[A], B]]]("h"),
							b.FixAs[Set[Prod[Set[A], B]]]("k")
						representatives, sectionRing := representGerms(b, g, h, k)
						b.Show(
							"both products are germs of the associative products in the section ring",
							Simp(Fwd(GermMul.Read(ringPresheaf)), Fwd(comm_ring.MulIn.Read(sectionRing))),
							Congr(),
							ByArith(
								sectionRing,
								representatives.Members[0],
								representatives.Members[1],
								representatives.Members[2]))
					})),
				Case(
					"the one germ is a left identity",
					Derive(func(b *Argument) {
						g := b.FixAs[Set[Prod[Set[A], B]]]("g")
						representatives, sectionRing := representGerms(b, g)
						W := representatives.Neighborhood
						oneGerm := b.Have(
							"represent the one germ over the final neighbourhood",
							MakeProp(Equal(b.Term("stalk_one(T, F, res, x)"), germ.Apply(W, one.Apply(F.Apply(W))))),
							By(GermOne.Read(ringPresheaf), representatives.NeighborhoodFact))
						b.Show(
							"one is a left identity in the section ring",
							oneGerm.Rw(),
							Simp(Fwd(GermMul.Read(ringPresheaf)), Fwd(comm_ring.OneIn.Read(sectionRing))),
							Congr(),
							ByArith(sectionRing, representatives.Members[0]))
					})),
				Case(
					"multiplication distributes over addition",
					Derive(func(b *Argument) {
						g, h, k :=
							b.FixAs[Set[Prod[Set[A], B]]]("g"),
							b.FixAs[Set[Prod[Set[A], B]]]("h"),
							b.FixAs[Set[Prod[Set[A], B]]]("k")
						representatives, sectionRing := representGerms(b, g, h, k)
						b.Show(
							"distributivity in the section ring gives the equality of germs",
							Simp(
								Fwd(GermAdd.Read(ringPresheaf)),
								Fwd(GermMul.Read(ringPresheaf)),
								Fwd(comm_ring.AddIn.Read(sectionRing)),
								Fwd(comm_ring.MulIn.Read(sectionRing))),
							Congr(),
							ByArith(
								sectionRing,
								representatives.Members[0],
								representatives.Members[1],
								representatives.Members[2]))
					})),
				Case(
					"subtraction is addition of the negation",
					Unfold(StalkSubDef)),
			))
		}),
})}

// GermHomomorphism — taking germs at x is a ring homomorphism from the
// sections over an open neighbourhood U of x to the stalk at x. The
// sections over U form a ring, and so does the stalk, x being a point of
// the space; the germ of a section over U lies in the stalk, and over U
// the germ of a sum, of a product and of one is the sum, the product and
// the one of the stalk. Those are the six conditions of the definition.
var GermHomomorphism = germHomomorphismThm{family.Add(registry.ProofEntry{
	Name: "GermHomomorphism",
	Key:  "prop_47c66ce6924c0a94",
	Build: family.Theorem(Statement{
		Binders: "∀F:presheaf_of_rings(A, B). ∀x:A. ∀U:set(A).",
		Hypotheses: []string{
			"U ∈ T",
			"x ∈ U",
		},
		Conclusion: "ring_homomorphism(F(U), " +
			"    stalk_ring(T, F, res, x), " +
			"    λs:B. sheaf_germ(T, λU:set(A). F(U).carrier, res, x, U, s))",
	},
		func(a *Argument, F PresheafOfRingsFact[on.T], x *Expr[A], U *Expr[Set[A]], neighborhood Fact) {
			sectionRing := a.Have(
				"the sections over U form a ring",
				"comm_ring_on(F(U))",
				By(SectionRing.Read(F), neighborhood))
			inSpace := a.Have(
				"x is a point of the space, as a point of the open set U",
				"x ∈ ⋃T",
				BySets(neighborhood))
			stalkRing := a.Have(
				"so the stalk at x is a ring",
				"comm_ring_on(stalk_ring(T, F, res, x))",
				By(StalkRing.Read(F), inSpace))
			germIn := a.Have(
				"the germ of a section over U lies in the stalk",
				Statement{
					Binders: "∀s:B.",
					Hypotheses: []string{
						"s ∈ F(U).carrier",
					},
					Conclusion: "sheaf_germ(T, λU:set(A). F(U).carrier, res, x, U, s) ∈ " +
						"stalk(T, λU:set(A). F(U).carrier, res, x)",
				},
				By(presheaf.GermInStalk.Read(Presheaf.Read(F)), neighborhood))
			germAdd := a.Have(
				"the germ of a sum of sections over U is the sum of their germs",
				Statement{
					Binders: "∀s t:B.",
					Hypotheses: []string{
						"s ∈ F(U).carrier",
						"t ∈ F(U).carrier",
					},
					Conclusion: "sheaf_germ(T, λU:set(A). F(U).carrier, res, x, U, F(U).add(s, t)) = " +
						"stalk_add(T, " +
						"    F, " +
						"    res, " +
						"    x, " +
						"    sheaf_germ(T, λU:set(A). F(U).carrier, res, x, U, s), " +
						"    sheaf_germ(T, λU:set(A). F(U).carrier, res, x, U, t))",
				},
				By(GermAdd.Read(F), neighborhood))
			germMul := a.Have(
				"the germ of a product of sections over U is the product of their germs",
				Statement{
					Binders: "∀s t:B.",
					Hypotheses: []string{
						"s ∈ F(U).carrier",
						"t ∈ F(U).carrier",
					},
					Conclusion: "sheaf_germ(T, λU:set(A). F(U).carrier, res, x, U, F(U).mul(s, t)) = " +
						"stalk_mul(T, " +
						"    F, " +
						"    res, " +
						"    x, " +
						"    sheaf_germ(T, λU:set(A). F(U).carrier, res, x, U, s), " +
						"    sheaf_germ(T, λU:set(A). F(U).carrier, res, x, U, t))",
				},
				By(GermMul.Read(F), neighborhood))
			germOne := a.Have(
				"the germ of one over U is the one of the stalk",
				"sheaf_germ(T, (λU:set(A). F(U).carrier), res, x, U, F(U).one) = stalk_one(T, F, res, x)",
				By(GermOne.Read(F), neighborhood))
			a.Show(
				"these are the conditions of a ring homomorphism",
				Unfold(ring_homomorphism.RingHomomorphism),
				By(sectionRing, stalkRing, germIn, germAdd, germMul, germOne))
		}),
})}

// CoefficientGermHomomorphism — for a ring homomorphism α from R to the
// sections over the whole space, sending a in R to the germ at x of α(a)
// is a ring homomorphism from R to the stalk at x: it is α followed by
// taking germs at x of sections over the whole space, an open set holding
// x, and a composite of ring homomorphisms is one.
var CoefficientGermHomomorphism = coefficientGermHomomorphismThm{family.Add(registry.ProofEntry{
	Name: "CoefficientGermHomomorphism",
	Key:  "prop_f9061a659c789885",
	Build: family.Theorem(Statement{
		Binders: "∀F:presheaf_of_rings(A, B). ∀R:ring_ops(C). ∀α:(C → B). ∀x:A.",
		Hypotheses: []string{
			"ring_homomorphism(R, F(⋃T), α)",
			"x ∈ ⋃T",
		},
		Conclusion: "ring_homomorphism(R, " +
			"    stalk_ring(T, F, res, x), " +
			"    λa:C. sheaf_germ(T, λU:set(A). F(U).carrier, res, x, ⋃T, α(a)))",
	},
		func(
			a *Argument,
			F PresheafOfRingsFact[on.T],
			R *Expr[RingOps[C]],
			α *Arrow[C, B],
			x *Expr[A],
			hom, inSpace Fact,
		) {
			spaceOpen := topological_space.SpaceOpen.Read(presheaf.Topology.Read(Presheaf.Read(F)))
			a.Show(
				"taking germs at x is a ring homomorphism from the global sections "+
					"to the stalk, so its composite with α is one from R to the stalk",
				By(
					hom,
					GermHomomorphism.Read(F),
					spaceOpen,
					inSpace,
					Where(ring_homomorphism.RingHomCompose, "χ",
						a.TermAs[Fun[B, Set[Prod[Set[A], B]]]](
							"λs:B. sheaf_germ(T, (λU:set(A). F(U).carrier), res, x, ⋃T, s)"))))
		}),
})}

// ---------------------------------------------------------------------------
// Locally ringed spaces
// ---------------------------------------------------------------------------

// LocallyRingedSpace — a sheaf of section-ring records whose ring of
// germs at every point is local.
var LocallyRingedSpace = locallyRingedSpaceThm{family.DefineStructure(registry.DefEntry{
	Name:    "LocallyRingedSpace",
	Key:     "prop_7475998cec117a8",
	Const:   "locally_ringed_space",
	Subject: "F",
	Type:    "set(set(A)) → (set(A) → ring_ops(B)) → (set(A) → set(A) → B → B) → bool",
	Equations: []string{
		"∀T:set(set(A)). ∀F:(set(A) → ring_ops(B)). ∀res:(set(A) → set(A) → B → B). " +
			"    locally_ringed_space(T, F, res) ⇔ " +
			"    sheaf_of_rings(T, F, res) ∧ (∀x:A. x ∈ ⋃T ⇒ local_ring_on(stalk_ring(T, F, res, x)))",
	},
	Deps: []registry.EntryLike{SheafOfRings, StalkRingDef},
})}

// RingedSheaf — a locally ringed space is a sheaf of rings.
var RingedSheaf = ringedSheafThm{family.Add(registry.ProofEntry{
	Name:  "RingedSheaf",
	Key:   "prop_74c955c8b1f65604",
	Build: LocallyRingedSpace.Axiom("sheaf_of_rings(T, F, res)"),
})}

// StalkLocal — its rings of germs are local.
var StalkLocal = stalkLocalThm{family.Add(registry.ProofEntry{
	Name: "StalkLocal",
	Key:  "prop_69b9b2842d431310",
	Build: LocallyRingedSpace.Axiom(Statement{
		Binders: "∀x:A.",
		Hypotheses: []string{
			"x ∈ ⋃T",
		},
		Conclusion: "local_ring_on(stalk_ring(T, F, res, x))",
	}),
})}

// ---------------------------------------------------------------------------
// Isomorphisms
// ---------------------------------------------------------------------------

// LrsIsomorphismDef — `lrs_isomorphism(F, F', φ, ψ)`, the two sheaves
// of rings bundles: φ is a homeomorphism from the space T onto the
// space T', and for every open V of T', ψ(V) is a ring isomorphism from
// the sections of the second sheaf over V onto the sections of the
// first over the preimage of V, compatibly with the restrictions. The
// two spaces have points of two types, A and C, and sections of two
// types, B and D. An isomorphism of the sections over every open set is
// one on every stalk, so no locality condition is asked.
var LrsIsomorphismDef = lrsIsomorphismDefThm{family.Define(registry.DefEntry{
	Name:    "LrsIsomorphismDef",
	Key:     "prop_b3c92b05ba71c0c7",
	Const:   "lrs_isomorphism",
	Bundles: []string{"sheaf_of_rings(T, F, res)", "sheaf_of_rings(T', F', res')"},
	Type: "set(set(A)) → " +
		"(set(A) → ring_ops(B)) → " +
		"(set(A) → set(A) → B → B) → " +
		"set(set(C)) → " +
		"(set(C) → ring_ops(D)) → " +
		"(set(C) → set(C) → D → D) → " +
		"(A → C) → " +
		"(set(C) → D → B) → " +
		"bool",
	Equations: []string{
		"∀T:set(set(A)). " +
			"∀F:(set(A) → ring_ops(B)). " +
			"∀res:(set(A) → set(A) → B → B). " +
			"∀T':set(set(C)). " +
			"∀F':(set(C) → ring_ops(D)). " +
			"∀res':(set(C) → set(C) → D → D). " +
			"∀φ:(A → C). " +
			"∀ψ:(set(C) → D → B). " +
			"    lrs_isomorphism(T, F, res, T', F', res', φ, ψ) ⇔ " +
			"    homeomorphic_map(T, T', φ) ∧ " +
			"    (∀V:set(C). V ∈ T' ⇒ ring_isomorphism(F'(V), F(preimage_on(⋃T, φ, V)), ψ(V))) ∧ " +
			"    (∀V W:set(C). ∀s:D. " +
			"        V ∈ T' ∧ W ∈ T' ∧ W ⊆ V ∧ s ∈ F'(V).carrier ⇒ " +
			"        res(preimage_on(⋃T, φ, V), preimage_on(⋃T, φ, W), ψ(V, s)) = ψ(W, res'(V, W, s)))",
	},
})}
