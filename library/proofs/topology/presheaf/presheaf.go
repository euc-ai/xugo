// presheaf.go — the chapter: presheaves and sheaves on a topological
// space, their germs and their stalks.
//
// The sections of every open set live in one type B: F(U) is a set of
// them, and res(U, V, s) restricts a section over U to V. Nothing asks
// the sections over two open sets to be of two types, so a stalk — the
// germs at a point, each a class of pairs (U, s) — is a set of the type
// set(set(prod(set(A), B))), fixed by A and B alone. Two parts, marked
// by banners: the structures; germs and stalks.

package presheaf

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/relations/equivalence"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/topology/topological_space"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The structures
// ---------------------------------------------------------------------------

// Presheaf — `presheaf(T, F, res)`: on the topological space T, F assigns
// to each open set its sections and res restricts a section over U to an
// open V ⊆ U, landing in F(V); restricting to U itself changes nothing,
// and restricting in two steps is restricting once. The topology is the
// definition's first conjunct.
var Presheaf = presheafThm{family.DefineStructure(registry.DefEntry{
	Name:    "Presheaf",
	Key:     "prop_5a3da198122d1952",
	Const:   "presheaf",
	Subject: "F",
	Type:    "set(set(A)) → (set(A) → set(B)) → (set(A) → set(A) → B → B) → bool",
	Equations: []string{
		"∀T:set(set(A)). ∀F:(set(A) → set(B)). ∀res:(set(A) → set(A) → B → B). " +
			"    presheaf(T, F, res) ⇔ " +
			"    is_topology(T) ∧ " +
			"    (∀U V:set(A). ∀s:B. U ∈ T ∧ V ∈ T ∧ V ⊆ U ∧ s ∈ F(U) ⇒ res(U, V, s) ∈ F(V)) ∧ " +
			"    (∀U:set(A). ∀s:B. U ∈ T ∧ s ∈ F(U) ⇒ res(U, U, s) = s) ∧ " +
			"    (∀U V W:set(A). ∀s:B. " +
			"        U ∈ T ∧ V ∈ T ∧ W ∈ T ∧ W ⊆ V ∧ V ⊆ U ∧ s ∈ F(U) ⇒ " +
			"        res(V, W, res(U, V, s)) = res(U, W, s))",
	},
})}

// Topology — a presheaf's space is a topology.
var Topology = topologyThm{family.Add(registry.ProofEntry{
	Name:  "Topology",
	Key:   "prop_5e95490ce52fe738",
	Build: Presheaf.Axiom("is_topology(T)"),
})}

// RestrictIn — a restriction lands in the sections of the smaller set.
var RestrictIn = restrictInThm{family.Add(registry.ProofEntry{
	Name: "RestrictIn",
	Key:  "prop_ed11100dc2570b1d",
	Build: Presheaf.Axiom(Statement{
		Binders: "∀U V:set(A). ∀s:B.",
		Hypotheses: []string{
			"U ∈ T",
			"V ∈ T",
			"V ⊆ U",
			"s ∈ F(U)",
		},
		Conclusion: "res(U, V, s) ∈ F(V)",
	}),
})}

// RestrictSelf — restricting to the set itself changes nothing.
var RestrictSelf = restrictSelfThm{family.Add(registry.ProofEntry{
	Name: "RestrictSelf",
	Key:  "prop_bf4edb8d42533bdf",
	Build: Presheaf.Axiom(Statement{
		Binders: "∀U:set(A). ∀s:B.",
		Hypotheses: []string{
			"U ∈ T",
			"s ∈ F(U)",
		},
		Conclusion: "res(U, U, s) = s",
	}),
})}

// RestrictTwice — restricting in two steps is restricting once.
var RestrictTwice = restrictTwiceThm{family.Add(registry.ProofEntry{
	Name: "RestrictTwice",
	Key:  "prop_c22e97cedfad49e2",
	Build: Presheaf.Axiom(Statement{
		Binders: "∀U V W:set(A). ∀s:B.",
		Hypotheses: []string{
			"U ∈ T",
			"V ∈ T",
			"W ∈ T",
			"W ⊆ V",
			"V ⊆ U",
			"s ∈ F(U)",
		},
		Conclusion: "res(V, W, res(U, V, s)) = res(U, W, s)",
	}),
})}

// Sheaf — `sheaf(T, F, res)`: a presheaf whose sections are local and
// glue. A cover of an open set U is a family V of open sets whose union
// is U; two sections over U that agree on every member of V are equal,
// and sections g(W) over the members W of V that agree on every overlap
// W ∩ W' are the restrictions of one section over U. The sections to
// glue are indexed by the open sets themselves, g : set(A) → B, so no
// index type is asked for.
var Sheaf = sheafThm{family.DefineStructure(registry.DefEntry{
	Name:    "Sheaf",
	Key:     "prop_e7ea765e337a420",
	Const:   "sheaf",
	Subject: "F",
	Type:    "set(set(A)) → (set(A) → set(B)) → (set(A) → set(A) → B → B) → bool",
	Equations: []string{
		"∀T:set(set(A)). ∀F:(set(A) → set(B)). ∀res:(set(A) → set(A) → B → B). " +
			"    sheaf(T, F, res) ⇔ " +
			"    presheaf(T, F, res) ∧ " +
			"    (∀U:set(A). ∀V:set(set(A)). ∀s t:B. " +
			"        U ∈ T ∧ " +
			"        V ⊆ T ∧ " +
			"        ⋃V = U ∧ " +
			"        s ∈ F(U) ∧ " +
			"        t ∈ F(U) ∧ " +
			"        (∀W:set(A). W ∈ V ⇒ res(U, W, s) = res(U, W, t)) ⇒ " +
			"        s = t) ∧ " +
			"    (∀U:set(A). ∀V:set(set(A)). ∀g:(set(A) → B). " +
			"        U ∈ T ∧ " +
			"        V ⊆ T ∧ " +
			"        ⋃V = U ∧ " +
			"        (∀W:set(A). W ∈ V ⇒ g(W) ∈ F(W)) ∧ " +
			"        (∀W W':set(A). W ∈ V ∧ W' ∈ V ⇒ res(W, W ∩ W', g(W)) = res(W', W ∩ W', g(W'))) ⇒ " +
			"        (∃s:B. s ∈ F(U) ∧ (∀W:set(A). W ∈ V ⇒ res(U, W, s) = g(W))))",
	},
	Deps: []registry.EntryLike{Presheaf},
})}

// SheafPresheaf — a sheaf is a presheaf.
var SheafPresheaf = sheafPresheafThm{family.Add(registry.ProofEntry{
	Name:  "SheafPresheaf",
	Key:   "prop_973080ab33cbd994",
	Build: Sheaf.Axiom("presheaf(T, F, res)"),
})}

// Locality — sections that agree on a cover are equal.
var Locality = localityThm{family.Add(registry.ProofEntry{
	Name: "Locality",
	Key:  "prop_9e4090efc679203b",
	Build: Sheaf.Axiom(Statement{
		Binders: "∀U:set(A). ∀V:set(set(A)). ∀s t:B.",
		Hypotheses: []string{
			"U ∈ T",
			"V ⊆ T",
			"⋃V = U",
			"s ∈ F(U)",
			"t ∈ F(U)",
			"∀W:set(A). W ∈ V ⇒ res(U, W, s) = res(U, W, t)",
		},
		Conclusion: "s = t",
	}),
})}

// Gluing — sections over a cover that agree on the overlaps glue.
var Gluing = gluingThm{family.Add(registry.ProofEntry{
	Name: "Gluing",
	Key:  "prop_492de92a96e9cb26",
	Build: Sheaf.Axiom(Statement{
		Binders: "∀U:set(A). ∀V:set(set(A)). ∀g:(set(A) → B).",
		Hypotheses: []string{
			"U ∈ T",
			"V ⊆ T",
			"⋃V = U",
			"∀W:set(A). W ∈ V ⇒ g(W) ∈ F(W)",
			"∀W W':set(A). W ∈ V ∧ W' ∈ V ⇒ res(W, W ∩ W', g(W)) = res(W', W ∩ W', g(W'))",
		},
		Conclusion: "∃s:B. s ∈ F(U) ∧ (∀W:set(A). W ∈ V ⇒ res(U, W, s) = g(W))",
	}),
})}

// ---------------------------------------------------------------------------
// Germs and stalks
// ---------------------------------------------------------------------------

// SheafGermDef — `sheaf_germ(T, F, res, x, U, s)`: the germ at x of the
// section s over U, the pairs (V, t) with x ∈ V and t ∈ F(V) that agree
// with (U, s) on some open neighbourhood of x inside U ∩ V. The space,
// the sections and the restriction are implicit.
var SheafGermDef = sheafGermDefThm{family.Define(registry.DefEntry{
	Name:  "SheafGermDef",
	Key:   "prop_a49efd79f25cc519",
	Const: "sheaf_germ",
	Type: "set(set(A)) → " +
		"(set(A) → set(B)) → " +
		"(set(A) → set(A) → B → B) → " +
		"A → " +
		"set(A) → " +
		"B → " +
		"set(prod(set(A), B))",
	Implicit: []string{"T", "F", "res"},
	Equations: []string{
		"∀T:set(set(A)). ∀F:(set(A) → set(B)). ∀res:(set(A) → set(A) → B → B). ∀x:A. ∀U:set(A). ∀s:B. " +
			"    sheaf_germ(T, F, res, x, U, s) = " +
			"    {(V, t) | " +
			"        V:set(A), " +
			"        t:B | " +
			"        V ∈ T ∧ " +
			"        x ∈ V ∧ " +
			"        t ∈ F(V) ∧ " +
			"        (∃W:set(A). W ∈ T ∧ x ∈ W ∧ W ⊆ U ∩ V ∧ res(U, W, s) = res(V, W, t))}",
	},
})}

// StalkDef — `stalk(T, F, res, x)`: the germs at x of the sections over
// the open neighbourhoods of x.
var StalkDef = stalkDefThm{family.Define(registry.DefEntry{
	Name:  "StalkDef",
	Key:   "prop_e971ad95c49fcc36",
	Const: "stalk",
	Type: "set(set(A)) → " +
		"(set(A) → set(B)) → " +
		"(set(A) → set(A) → B → B) → " +
		"A → " +
		"set(set(prod(set(A), B)))",
	Implicit: []string{"T", "F", "res"},
	Equations: []string{"∀T:set(set(A)). ∀F:(set(A) → set(B)). ∀res:(set(A) → set(A) → B → B). ∀x:A. " +
		"    stalk(T, F, res, x) = " +
		"    {sheaf_germ(T, F, res, x, U, s) | U:set(A), s:B | U ∈ T ∧ x ∈ U ∧ s ∈ F(U)}"},
	Deps: []registry.EntryLike{SheafGermDef},
})}

// InGerm — a pair lies in the germ of (U, s) at x exactly when it meets
// the germ's condition: it lies in a set-builder of pairs when it equals
// one of the pairs the condition admits, and equal pairs have equal
// components.
var InGerm = inGermThm{family.Add(registry.ProofEntry{
	Name: "InGerm",
	Key:  "prop_88c03a1f8463d329",
	Build: family.Theorem("∀T:set(set(A)). "+
		"∀F:(set(A) → set(B)). "+
		"∀res:(set(A) → set(A) → B → B). "+
		"∀x:A. "+
		"∀U V:set(A). "+
		"∀s t:B. "+
		"    (V, t) ∈ sheaf_germ(T, F, res, x, U, s) ⇔ "+
		"    V ∈ T ∧ "+
		"    x ∈ V ∧ "+
		"    t ∈ F(V) ∧ "+
		"    (∃W:set(A). W ∈ T ∧ x ∈ W ∧ W ⊆ U ∩ V ∧ res(U, W, s) = res(V, W, t))",
		func(
			a *Argument,
			T *Expr[Set[Set[A]]],
			F *Expr[Fun[Set[A], Set[B]]],
			res *Expr[Fun3[Set[A], Set[A], B, B]],
			x *Expr[A],
			U, V *Expr[Set[A]],
			s, t *Expr[B],
		) {
			a.Iff()
			a.Forward(
				"(V, t) is one of the pairs the condition admits, so it meets the condition",
				func(b *Argument, member Fact) {
					admittedPair := b.Have(
						"(V, t) is one of the pairs the set-builder admits",
						"∃V':set(A). ∃t':B. "+
							"    (V' ∈ T ∧ "+
							"        x ∈ V' ∧ "+
							"        t' ∈ F(V') ∧ "+
							"        (∃W:set(A). W ∈ T ∧ x ∈ W ∧ W ⊆ U ∩ V' ∧ res(U, W, s) = res(V', W, t'))) ∧ "+
							"    (V, t) = (V', t')",
						member.Simp(
							Fwd(SheafGermDef),
							Fwd(set_basic.SetMemberDef.Inst[Prod[Set[A], B]]()),
							Fwd(set_basic.SetComprehensionDef.Inst[Prod[Set[A], B]]()),
							Fwd(set_basic.ComprehensionSpecDef.Inst[Prod[Set[A], B]]())),
						By(member))
					Vʹ, tʹ, admitted := b.Unpack2As[Set[A], B](admittedPair, "V'", "t'")
					pairEquality := pairs.PairEq.At(V, t, Vʹ, tʹ)
					sameNeighborhood := b.Have(
						"equal pairs have equal first components",
						"V = V'",
						By(pairEquality, admitted))
					sameSection := b.Have(
						"and equal second components",
						"t = t'",
						By(pairEquality, admitted))
					b.Show(
						"so the condition (V', t') meets is the condition at (V, t)",
						sameNeighborhood.RwRev(),
						sameSection.RwRev(),
						By(admitted))
				})
			a.Backward(
				"a pair meeting the condition is admitted by the set-builder",
				func(b *Argument, condition Fact) {
					b.Show(
						"(V, t) is admitted as itself",
						Simp(Fwd(SheafGermDef)),
						BySets(condition))
				})
		}),
})}

// GermOwn — a section's own pair lies in its germ: read through the
// definition, the pair (U, s) agrees with itself near x.
var GermOwn = germOwnThm{family.Add(registry.ProofEntry{
	Name: "GermOwn",
	Key:  "prop_c1be09068639b488",
	Build: Presheaf.Law(Statement{
		Binders: "∀x:A. ∀U:set(A). ∀s:B.",
		Hypotheses: []string{
			"U ∈ T",
			"x ∈ U",
			"s ∈ F(U)",
		},
		Conclusion: "(U, s) ∈ sheaf_germ(x, U, s)",
	},
		func(a *Argument, _ PresheafFact[on.T], x *Expr[A], U *Expr[Set[A]], s *Expr[B], hypotheses Fact) {
			a.Show(
				"the germ's condition at its own pair: U is open, holds x, and carries s",
				Simp(Fwd(SheafGermDef)),
				BySets(hypotheses))
		}),
})}

// AgreeNearTrans — agreeing near x is transitive: two agreements, on
// open neighbourhoods N and N' of x, both restrict to N ∩ N', open by
// the topology, where restricting in two steps is restricting once.
var AgreeNearTrans = agreeNearTransThm{family.Add(registry.ProofEntry{
	Name: "AgreeNearTrans",
	Key:  "prop_8b12878c5a408ec1",
	Build: Presheaf.Law(Statement{
		Binders: "∀x:A. ∀U V W:set(A). ∀r s t:B.",
		// The six memberships are one hypothesis, written after the two
		// agreements: in first place a conjunction reads as its conjuncts.
		Hypotheses: []string{
			"∃N:set(A). N ∈ T ∧ x ∈ N ∧ N ⊆ U ∩ V ∧ res(U, N, r) = res(V, N, s)",
			"∃N:set(A). N ∈ T ∧ x ∈ N ∧ N ⊆ V ∩ W ∧ res(V, N, s) = res(W, N, t)",
			"U ∈ T ∧ V ∈ T ∧ W ∈ T ∧ r ∈ F(U) ∧ s ∈ F(V) ∧ t ∈ F(W)",
		},
		Conclusion: "∃N:set(A). N ∈ T ∧ x ∈ N ∧ N ⊆ U ∩ W ∧ res(U, N, r) = res(W, N, t)",
	},
		func(
			a *Argument,
			presheaf PresheafFact[on.T],
			x *Expr[A],
			U, V, W *Expr[Set[A]],
			r, s, t *Expr[B],
			firstAgreement, secondAgreement, sections Fact,
		) {
			N, onN := a.UnpackAs[Set[A]](firstAgreement, "N")
			Nʹ, onNʹ := a.UnpackAs[Set[A]](secondAgreement, "N'")
			meet := a.TermAs[Set[A]]("N ∩ N'")
			open := a.Have(
				"N ∩ N' is open",
				"N ∩ N' ∈ T",
				By(topological_space.InterOpen.Read(Topology.Read(presheaf)), onN, onNʹ))
			inside := a.Have(
				"N ∩ N' lies in N and in N', which lie in U ∩ V and in V ∩ W",
				"N ∩ N' ⊆ N ∧ N ∩ N' ⊆ N' ∧ N ⊆ U ∧ N ⊆ V ∧ N' ⊆ V ∧ N' ⊆ W",
				BySets(onN, onNʹ))
			restrictTwice := RestrictTwice.Read(presheaf).AsFact()
			agree := a.Have(
				"r and t agree on N ∩ N'",
				"res(U, N ∩ N', r) = res(W, N ∩ N', t)",
				CalcEq(
					Leg(
						a.Term("res(N, N ∩ N', res(U, N, r))"),
						"restricting r to N ∩ N' passes through N",
						By(restrictTwice.At(U, N, meet, r), sections, onN, open, inside)),
					Leg(
						a.Term("res(N, N ∩ N', res(V, N, s))"),
						"on N, r and s agree",
						By(Normalized, onN)),
					Leg(
						a.Term("res(V, N ∩ N', s)"),
						"and s restricted through N is s restricted to N ∩ N'",
						By(restrictTwice.At(V, N, meet, s), sections, onN, open, inside)),
					Leg(
						a.Term("res(N', N ∩ N', res(V, N', s))"),
						"which passes through N' as well",
						By(restrictTwice.At(V, Nʹ, meet, s), sections, onNʹ, open, inside)),
					Leg(
						a.Term("res(N', N ∩ N', res(W, N', t))"),
						"on N', s and t agree",
						By(Normalized, onNʹ)),
					FinalLeg(
						"and t restricted through N' is t restricted to N ∩ N'",
						By(restrictTwice.At(W, Nʹ, meet, t), sections, onNʹ, open, inside)),
				))
			a.Take(meet)
			a.Show(
				"N ∩ N' is an open neighbourhood of x inside U ∩ W on which r and t agree",
				BySets(agree, open, onN, onNʹ))
		}),
})}

// GermEq — two germs at x are equal exactly when their sections agree on
// an open neighbourhood of x: identify germs with classes of the germ
// equivalence, apply class equality, and read its relation through InGerm.
var GermEq = germEqThm{family.Add(registry.ProofEntry{
	Name: "GermEq",
	Key:  "prop_ccc48e3f9031888c",
	Reading: "The hypotheses x ∈ U, x ∈ V, s ∈ F(U), t ∈ F(V) all matter: for x ∉ U the germ " +
		"of (U, s) is ∅, so two such germs are equal while no agreement neighbourhood exists.",
	Build: Presheaf.Law(Statement{
		Binders: "∀x:A. ∀U V:set(A). ∀s t:B.",
		Hypotheses: []string{
			"U ∈ T",
			"V ∈ T",
			"x ∈ U",
			"x ∈ V",
			"s ∈ F(U)",
			"t ∈ F(V)",
		},
		Conclusion: "sheaf_germ(x, U, s) = sheaf_germ(x, V, t) ⇔ " +
			"∃W:set(A). W ∈ T ∧ x ∈ W ∧ W ⊆ U ∩ V ∧ res(U, W, s) = res(V, W, t)",
	},
		func(
			a *Argument,
			presheaf PresheafFact[on.T],
			x *Expr[A],
			U, V *Expr[Set[A]],
			s, t *Expr[B],
			hypotheses Fact,
		) {
			equivalent := a.Simplified(GermEquivalence.Read(presheaf).At(x))
			members := a.Have(
				"both representatives lie in the carrier of the germ equivalence",
				"(U, s) ∈ {p:prod(set(A), B) | fst(p) ∈ T ∧ x ∈ fst(p) ∧ snd(p) ∈ F(fst(p))} ∧ "+
					"(V, t) ∈ {p:prod(set(A), B) | fst(p) ∈ T ∧ x ∈ fst(p) ∧ snd(p) ∈ F(fst(p))}",
				BySets(hypotheses, pairs.Fst, pairs.Snd))
			sameClass := a.Simplified(
				GroupPremises(members, equivalence.ClassOnEqIff.Read(equivalent).AsFact().At(
					a.TermAs[Prod[Set[A], B]]("(U, s)"), a.TermAs[Prod[Set[A], B]]("(V, t)"))),
				Rev(GermClass),
				Fwd(pairs.Fst),
				Fwd(pairs.Snd),
				Fwd(InGerm))
			a.Show(
				"class equality is agreement on an open neighbourhood of x",
				By(sameClass, members, hypotheses))
		}),
})}

// GermRestrict — a restriction has the germ of the section it restricts:
// V itself is an open neighbourhood of x inside V ∩ U on which the
// restriction and the section agree, since restricting the restriction
// to V once more changes nothing.
var GermRestrict = germRestrictThm{family.Add(registry.ProofEntry{
	Name: "GermRestrict",
	Key:  "prop_7f6f8a6d0d668d59",
	Build: Presheaf.Law(Statement{
		Binders: "∀x:A. ∀U V:set(A). ∀s:B.",
		Hypotheses: []string{
			"U ∈ T",
			"V ∈ T",
			"V ⊆ U",
			"x ∈ V",
			"s ∈ F(U)",
		},
		Conclusion: "sheaf_germ(x, V, res(U, V, s)) = sheaf_germ(x, U, s)",
	},
		func(
			a *Argument,
			presheaf PresheafFact[on.T],
			x *Expr[A],
			U, V *Expr[Set[A]],
			s *Expr[B],
			hypotheses Fact,
		) {
			restricted := a.Have(
				"the restriction is a section over V",
				"res(U, V, s) ∈ F(V)",
				By(RestrictIn.Read(presheaf), hypotheses))
			unchanged := a.Have(
				"restricting it to V once more changes nothing",
				"res(V, V, res(U, V, s)) = res(U, V, s)",
				By(RestrictSelf.Read(presheaf), restricted, hypotheses))
			xInU := a.Have(
				"x lies in V, hence in U",
				"x ∈ U",
				BySets(hypotheses))
			near := a.Have(
				"so V is an open neighbourhood of x inside V ∩ U on which the two sections agree",
				"∃W:set(A). W ∈ T ∧ x ∈ W ∧ W ⊆ V ∩ U ∧ res(V, W, res(U, V, s)) = res(U, W, s)",
				Derive(func(b *Argument) {
					b.Take(V)
					b.Show(
						"V is open, holds x, lies inside V ∩ U, and there the restriction is unchanged",
						BySets(unchanged, hypotheses))
				}))
			a.Show(
				"and sections that agree near x have the same germ",
				By(
					GermEq.Read(presheaf).AsFact().At(x, V, U, a.TermAs[B]("res(U, V, s)"), s),
					near,
					xInU,
					restricted,
					hypotheses))
		}),
})}

// GermConstant — compatible chosen sections have the germ of the chosen
// section over the whole space, by restriction to the given neighbourhood.
var GermConstant = germConstantThm{family.Add(registry.ProofEntry{
	Name: "GermConstant",
	Key:  "prop_fe5adc337f0eb06c",
	Build: Presheaf.Law(Statement{
		Binders: "∀e:(set(A) → B). ∀x:A. ∀W:set(A).",
		Hypotheses: []string{
			"∀U:set(A). U ∈ T ⇒ e(U) ∈ F(U)",
			"∀U V:set(A). U ∈ T ∧ V ∈ T ∧ V ⊆ U ⇒ res(U, V, e(U)) = e(V)",
			"W ∈ T ∧ x ∈ W",
		},
		Conclusion: "sheaf_germ(x, ⋃T, e(⋃T)) = sheaf_germ(x, W, e(W))",
	},
		func(
			a *Argument,
			presheaf PresheafFact[on.T],
			e *Arrow[Set[A], B],
			x *Expr[A],
			W *Expr[Set[A]],
			closed, natural, neighbourhood Fact,
		) {
			spaceOpen := a.Have(
				"the whole space is open",
				"⋃T ∈ T",
				By(topological_space.SpaceOpen.Read(Topology.Read(presheaf))))
			contained := a.Have(
				"W lies inside the whole space",
				"W ⊆ ⋃T",
				BySets(neighbourhood))
			section := a.Have(
				"the chosen global section belongs to its carrier",
				"e(⋃T) ∈ F(⋃T)",
				By(closed, spaceOpen))
			restricts := a.Have(
				"the global section restricts to the chosen section on W",
				"res(⋃T, W, e(⋃T)) = e(W)",
				By(natural, spaceOpen, contained, neighbourhood))
			a.Show(
				"restriction and compatibility identify the two germs",
				CalcEq(
					Leg(
						a.TermAs[Set[Prod[Set[A], B]]]("sheaf_germ(x, W, res(⋃T, W, e(⋃T)))"),
						"restriction preserves the germ",
						By(GermRestrict.Read(presheaf), section, spaceOpen, contained, neighbourhood)),
					FinalLeg(
						"compatibility identifies the restricted section",
						restricts.Rw(),
						Basic())))
		}),
})}

// GermUnaryOperation — a compatible map of sections carries representatives
// that agree near x to sections that agree on the same neighbourhood.
var GermUnaryOperation = germUnaryOperationThm{family.Add(registry.ProofEntry{
	Name: "GermUnaryOperation",
	Key:  "prop_a88b9cb7496ac859",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). " +
			"∀F:(set(A) → set(B)). " +
			"∀res:(set(A) → set(A) → B → B). " +
			"∀G:(set(A) → set(C)). " +
			"∀resG:(set(A) → set(A) → C → C). " +
			"∀op:(set(A) → B → C). " +
			"∀x:A. " +
			"∀W:set(A). " +
			"∀s:B.",
		Hypotheses: []string{
			"presheaf(T, F, res)",
			"presheaf(T, G, resG)",
			"∀U:set(A). ∀s:B. U ∈ T ∧ s ∈ F(U) ⇒ op(U, s) ∈ G(U)",
			"∀U V:set(A). ∀s:B. U ∈ T ∧ V ∈ T ∧ V ⊆ U ∧ s ∈ F(U) ⇒ resG(U, V, op(U, s)) = op(V, res(U, V, s))",
			"W ∈ T ∧ x ∈ W ∧ s ∈ F(W)",
		},
		Conclusion: "⋃{sheaf_germ(T, G, resG, x, U, op(U, u)) | " +
			"    U:set(A), " +
			"    u:B | " +
			"    (U, u) ∈ sheaf_germ(T, F, res, x, W, s)} = " +
			"sheaf_germ(T, G, resG, x, W, op(W, s))",
	},
		func(
			a *Argument,
			T *Expr[Set[Set[A]]],
			F *Expr[Fun[Set[A], Set[B]]],
			res *Expr[Fun3[Set[A], Set[A], B, B]],
			G *Expr[Fun[Set[A], Set[C]]],
			resG *Expr[Fun3[Set[A], Set[A], C, C]],
			structures Fact,
			op *Arrow2[Set[A], B, C],
			x *Expr[A],
			W *Expr[Set[A]],
			s *Expr[B],
			closed, natural, hypotheses Fact,
		) {
			presheaves := a.Conjuncts(
				structures,
				"F is the source presheaf",
				"G is the target presheaf")
			own := a.Have(
				"the section s represents its own germ",
				"(W, s) ∈ sheaf_germ(T, F, res, x, W, s)",
				By(GermOwn.Read(presheaves[0]), hypotheses))
			agree := a.Have(
				"every representative has the same image germ",
				Statement{
					Binders: "∀U:set(A). ∀u:B.",
					Hypotheses: []string{
						"(U, u) ∈ sheaf_germ(T, F, res, x, W, s)",
					},
					Conclusion: "sheaf_germ(T, G, resG, x, U, op(U, u)) = sheaf_germ(T, G, resG, x, W, op(W, s))",
				},
				Derive(func(b *Argument) {
					U := b.FixAs[Set[A]]("U")
					u := b.FixAs[B]("u")
					inGerm := b.Assume()
					represents := b.Have(
						"u is a section near x agreeing with s on a common neighbourhood",
						"U ∈ T ∧ x ∈ U ∧ u ∈ F(U) ∧ ∃N:set(A). N ∈ T ∧ x ∈ N ∧ N ⊆ W ∩ U ∧ res(W, N, s) = res(U, N, u)",
						inGerm.Simp(Fwd(InGerm)),
						By(inGerm))
					N, near := b.ObtainAs[Set[A]](
						"choose a neighbourhood on which u and s agree",
						"∃N:set(A). N ∈ T ∧ x ∈ N ∧ N ⊆ W ∩ U ∧ res(W, N, s) = res(U, N, u)",
						By(represents))
					inside := b.Have(
						"N lies in both representative domains",
						"N ⊆ U ∧ N ⊆ W ∧ N ⊆ U ∩ W",
						BySets(near))
					imageAgrees := b.Have(
						"the image sections agree on N",
						"resG(U, N, op(U, u)) = resG(W, N, op(W, s))",
						CalcEq(
							Leg(
								b.TermAs[C]("op(N, res(U, N, u))"),
								"op commutes with restriction from U to N",
								By(natural.At(U, N, u), inside, near, represents)),
							Leg(
								b.TermAs[C]("op(N, res(W, N, s))"),
								"the source restrictions agree on N",
								By(Normalized, near)),
							FinalLeg(
								"op commutes with restriction from W to N",
								By(natural.At(W, N, s), hypotheses, inside, near))))
					targetNear := b.Have(
						"the images agree near x inside U and W",
						"∃V:set(A). V ∈ T ∧ x ∈ V ∧ V ⊆ U ∩ W ∧ resG(U, V, op(U, u)) = resG(W, V, op(W, s))",
						Derive(func(c *Argument) {
							c.Take(N)
							c.Show(
								"N is the required neighbourhood",
								By(imageAgrees, inside, near))
						}))
					b.Show(
						"agreement near x identifies the target germs",
						By(
							GermEq.Read(presheaves[1]).AsFact().At(x, U, W, b.TermAs[C]("op(U, u)"), b.TermAs[C]("op(W, s)")),
							closed,
							targetNear,
							hypotheses,
							represents))
				}))
			a.Show(
				"the union of these equal image germs is the canonical image germ",
				BySets(agree, own))
		}),
})}

// GermBinaryOperation — compatible operations between two source presheaves
// and a target presheaf descend to germs. Intersecting the neighbourhoods
// where the input representatives agree makes their output sections agree.
var GermBinaryOperation = germBinaryOperationThm{family.Add(registry.ProofEntry{
	Name: "GermBinaryOperation",
	Key:  "prop_aa8dc8b8e1953c2f",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). " +
			"∀F:(set(A) → set(B)). " +
			"∀resF:(set(A) → set(A) → B → B). " +
			"∀G:(set(A) → set(C)). " +
			"∀resG:(set(A) → set(A) → C → C). " +
			"∀H:(set(A) → set(D)). " +
			"∀resH:(set(A) → set(A) → D → D). " +
			"∀op:(set(A) → B → C → D). " +
			"∀x:A. " +
			"∀W:set(A). " +
			"∀s:B. " +
			"∀t:C.",
		Hypotheses: []string{
			"presheaf(T, F, resF)",
			"presheaf(T, G, resG)",
			"presheaf(T, H, resH)",
			"∀U:set(A). ∀s:B. ∀t:C. U ∈ T ∧ s ∈ F(U) ∧ t ∈ G(U) ⇒ op(U, s, t) ∈ H(U)",
			"∀U V:set(A). ∀s:B. ∀t:C. " +
				"    U ∈ T ∧ V ∈ T ∧ V ⊆ U ∧ s ∈ F(U) ∧ t ∈ G(U) ⇒ " +
				"    resH(U, V, op(U, s, t)) = op(V, resF(U, V, s), resG(U, V, t))",
			"W ∈ T ∧ x ∈ W ∧ s ∈ F(W) ∧ t ∈ G(W)",
		},
		Conclusion: "⋃{ " +
			"    sheaf_germ(T, H, resH, x, U ∩ V, op(U ∩ V, resF(U, U ∩ V, u), resG(V, U ∩ V, v))) | " +
			"    U:set(A), " +
			"    u:B, " +
			"    V:set(A), " +
			"    v:C | " +
			"    (U, u) ∈ sheaf_germ(T, F, resF, x, W, s) ∧ (V, v) ∈ sheaf_germ(T, G, resG, x, W, t)} = " +
			"sheaf_germ(T, H, resH, x, W, op(W, s, t))",
	},
		func(
			a *Argument,
			T *Expr[Set[Set[A]]],
			F *Expr[Fun[Set[A], Set[B]]],
			resF *Expr[Fun3[Set[A], Set[A], B, B]],
			G *Expr[Fun[Set[A], Set[C]]],
			resG *Expr[Fun3[Set[A], Set[A], C, C]],
			H *Expr[Fun[Set[A], Set[D]]],
			resH *Expr[Fun3[Set[A], Set[A], D, D]],
			structures Fact,
			op *Expr[Fun3[Set[A], B, C, D]],
			x *Expr[A],
			W *Expr[Set[A]],
			s *Expr[B],
			t *Expr[C],
			closed, natural, hypotheses Fact,
		) {
			presheaves := a.Conjuncts(
				structures,
				"F is the first source presheaf",
				"G is the second source presheaf",
				"H is the target presheaf")
			sourceF, sourceG, target := presheaves[0], presheaves[1], presheaves[2]
			ownF := a.Have(
				"s represents its own germ",
				"(W, s) ∈ sheaf_germ(T, F, resF, x, W, s)",
				By(GermOwn.Read(sourceF), hypotheses))
			ownG := a.Have(
				"t represents its own germ",
				"(W, t) ∈ sheaf_germ(T, G, resG, x, W, t)",
				By(GermOwn.Read(sourceG), hypotheses))
			agree := a.Have(
				"every pair of representatives gives the canonical output germ",
				Statement{
					Binders: "∀P Q:set(A). ∀p:B. ∀q:C.",
					Hypotheses: []string{
						"(P, p) ∈ sheaf_germ(T, F, resF, x, W, s)",
						"(Q, q) ∈ sheaf_germ(T, G, resG, x, W, t)",
					},
					Conclusion: "sheaf_germ(T, H, resH, x, P ∩ Q, op(P ∩ Q, resF(P, P ∩ Q, p), resG(Q, P ∩ Q, q))) = " +
						"sheaf_germ(T, H, resH, x, W, op(W, s, t))",
				},
				Derive(func(b *Argument) {
					P := b.FixAs[Set[A]]("P")
					Q := b.FixAs[Set[A]]("Q")
					p := b.FixAs[B]("p")
					q := b.FixAs[C]("q")
					inGerms := b.Assume()
					repF := b.Have(
						"p is a section near x agreeing with s on a common neighbourhood",
						"P ∈ T ∧ x ∈ P ∧ p ∈ F(P) ∧ ∃N:set(A). N ∈ T ∧ x ∈ N ∧ N ⊆ W ∩ P ∧ resF(W, N, s) = resF(P, N, p)",
						By(InGerm.At(T, F, resF, x, W, P, s, p), inGerms))
					repG := b.Have(
						"q is a section near x agreeing with t on a common neighbourhood",
						"Q ∈ T ∧ x ∈ Q ∧ q ∈ G(Q) ∧ ∃M:set(A). M ∈ T ∧ x ∈ M ∧ M ⊆ W ∩ Q ∧ resG(W, M, t) = resG(Q, M, q)",
						By(InGerm.At(T, G, resG, x, W, Q, t, q), inGerms))
					N, nearF := b.ObtainAs[Set[A]](
						"choose a neighbourhood on which p and s agree",
						"∃N:set(A). N ∈ T ∧ x ∈ N ∧ N ⊆ W ∩ P ∧ resF(W, N, s) = resF(P, N, p)",
						By(repF))
					M, nearG := b.ObtainAs[Set[A]](
						"choose a neighbourhood on which q and t agree",
						"∃M:set(A). M ∈ T ∧ x ∈ M ∧ M ⊆ W ∩ Q ∧ resG(W, M, t) = resG(Q, M, q)",
						By(repG))
					meet := b.TermAs[Set[A]]("N ∩ M")
					domain := b.TermAs[Set[A]]("P ∩ Q")
					open := b.Have(
						"the common neighbourhood and representative domain are open",
						"N ∩ M ∈ T ∧ P ∩ Q ∈ T",
						By(topological_space.InterOpen.Read(Topology.Read(sourceF)), repF, repG, nearF, nearG))
					inside := b.Have(
						"the intersection holds x and lies inside each domain through which we restrict",
						"x ∈ N ∩ M ∧ "+
							"x ∈ P ∩ Q ∧ "+
							"N ∩ M ⊆ N ∧ "+
							"N ∩ M ⊆ M ∧ "+
							"N ∩ M ⊆ W ∧ "+
							"N ∩ M ⊆ P ∩ Q ∧ "+
							"N ∩ M ⊆ (P ∩ Q) ∩ W ∧ "+
							"N ⊆ W ∧ "+
							"N ⊆ P ∧ "+
							"M ⊆ W ∧ "+
							"M ⊆ Q ∧ "+
							"P ∩ Q ⊆ P ∧ "+
							"P ∩ Q ⊆ Q",
						BySets(nearF, nearG))
					twiceF := RestrictTwice.Read(sourceF).AsFact()
					twiceG := RestrictTwice.Read(sourceG).AsFact()
					onF := b.Have(
						"p and s agree on the common neighbourhood",
						"resF(P, N ∩ M, p) = resF(W, N ∩ M, s)",
						CalcEq(
							Leg(
								b.TermAs[B]("resF(N, N ∩ M, resF(P, N, p))"),
								"restrict p through N",
								By(twiceF.At(P, N, meet, p), repF, nearF, open, inside)),
							Leg(
								b.TermAs[B]("resF(N, N ∩ M, resF(W, N, s))"),
								"p and s already agree on N",
								By(Normalized, nearF)),
							FinalLeg(
								"restriction through N equals direct restriction",
								By(twiceF.At(W, N, meet, s), nearF, open, inside, hypotheses))))
					onG := b.Have(
						"q and t agree on the common neighbourhood",
						"resG(Q, N ∩ M, q) = resG(W, N ∩ M, t)",
						CalcEq(
							Leg(
								b.TermAs[C]("resG(M, N ∩ M, resG(Q, M, q))"),
								"restrict q through M",
								By(twiceG.At(Q, M, meet, q), repG, nearG, open, inside)),
							Leg(
								b.TermAs[C]("resG(M, N ∩ M, resG(W, M, t))"),
								"q and t already agree on M",
								By(Normalized, nearG)),
							FinalLeg(
								"restriction through M equals direct restriction",
								By(twiceG.At(W, M, meet, t), nearG, open, inside, hypotheses))))
					pRestricted := b.TermAs[B]("resF(P, P ∩ Q, p)")
					qRestricted := b.TermAs[C]("resG(Q, P ∩ Q, q)")
					restricted := b.Have(
						"both restricted representatives belong to their source carriers",
						"resF(P, P ∩ Q, p) ∈ F(P ∩ Q) ∧ resG(Q, P ∩ Q, q) ∈ G(P ∩ Q)",
						By(RestrictIn.Read(sourceF), RestrictIn.Read(sourceG), repF, repG, open, inside))
					imageAgrees := b.Have(
						"the output sections agree on the common neighbourhood",
						"resH(P ∩ Q, N ∩ M, op(P ∩ Q, resF(P, P ∩ Q, p), resG(Q, P ∩ Q, q))) = resH(W, N ∩ M, op(W, s, t))",
						CalcEq(
							Leg(
								b.TermAs[D](
									"op(N ∩ M, resF(P ∩ Q, N ∩ M, resF(P, P ∩ Q, p)), resG(P ∩ Q, N ∩ M, resG(Q, P ∩ Q, q)))"),
								"op commutes with restriction from the representative domain",
								By(natural.At(domain, meet, pRestricted, qRestricted), open, inside, restricted)),
							Leg(
								b.TermAs[D]("op(N ∩ M, resF(P, N ∩ M, p), resG(Q, N ∩ M, q))"),
								"each source restriction composes",
								By(twiceF.At(P, domain, meet, p), twiceG.At(Q, domain, meet, q), open, repF, repG, inside)),
							Leg(
								b.TermAs[D]("op(N ∩ M, resF(W, N ∩ M, s), resG(W, N ∩ M, t))"),
								"the source restrictions agree",
								onF.Rw(),
								onG.Rw(),
								Basic()),
							FinalLeg(
								"op commutes with restriction from W",
								By(natural.At(W, meet, s, t), open, inside, hypotheses))))
					near := b.Have(
						"the output sections agree near x inside both output domains",
						"∃V:set(A). "+
							"    V ∈ T ∧ "+
							"    x ∈ V ∧ "+
							"    V ⊆ (P ∩ Q) ∩ W ∧ "+
							"    resH(P ∩ Q, V, op(P ∩ Q, resF(P, P ∩ Q, p), resG(Q, P ∩ Q, q))) = resH(W, V, op(W, s, t))",
						Derive(func(c *Argument) {
							c.Take(meet)
							c.Show(
								"the common neighbourhood witnesses agreement",
								By(imageAgrees, open, inside))
						}))
					b.Show(
						"agreement near x identifies the target germs",
						By(
							GermEq.Read(target).AsFact().At(x, domain, W,
								b.TermAs[D]("op(P ∩ Q, resF(P, P ∩ Q, p), resG(Q, P ∩ Q, q))"), b.TermAs[D]("op(W, s, t)")),
							near,
							closed,
							restricted,
							open,
							hypotheses,
							inside))
				}))
			a.Show(
				"the union of these equal output germs is the canonical output germ",
				BySets(agree, ownF, ownG))
		}),
})}

// GermOperation — specialize GermBinaryOperation to one presheaf in both
// source positions and the target.
var GermOperation = germOperationThm{family.Add(registry.ProofEntry{
	Name: "GermOperation",
	Key:  "prop_aadae09a96b076b3",
	Build: Presheaf.Law(Statement{
		Binders: "∀op:(set(A) → B → B → B). ∀x:A. ∀W:set(A). ∀s t:B.",
		Hypotheses: []string{
			"∀U:set(A). ∀u v:B. U ∈ T ∧ u ∈ F(U) ∧ v ∈ F(U) ⇒ op(U, u, v) ∈ F(U)",
			"∀U V:set(A). ∀u v:B. " +
				"    U ∈ T ∧ V ∈ T ∧ V ⊆ U ∧ u ∈ F(U) ∧ v ∈ F(U) ⇒ " +
				"    res(U, V, op(U, u, v)) = op(V, res(U, V, u), res(U, V, v))",
			"W ∈ T ∧ x ∈ W ∧ s ∈ F(W) ∧ t ∈ F(W)",
		},
		Conclusion: "⋃{sheaf_germ(x, P ∩ Q, op(P ∩ Q, res(P, P ∩ Q, p), res(Q, P ∩ Q, q))) | " +
			"    P:set(A), " +
			"    p:B, " +
			"    Q:set(A), " +
			"    q:B | " +
			"    (P, p) ∈ sheaf_germ(x, W, s) ∧ (Q, q) ∈ sheaf_germ(x, W, t)} = " +
			"sheaf_germ(x, W, op(W, s, t))",
	},
		func(
			a *Argument,
			presheaf PresheafFact[on.T],
			op *Expr[Fun3[Set[A], B, B, B]],
			x *Expr[A],
			W *Expr[Set[A]],
			s, t *Expr[B],
			closed, natural, hypotheses Fact,
		) {
			T := a.TermAs[Set[Set[A]]]("T")
			F := a.TermAs[Fun[Set[A], Set[B]]]("F")
			res := a.TermAs[Fun3[Set[A], Set[A], B, B]]("res")
			a.Show(
				"the two sources and the target are the same presheaf",
				By(
					presheaf,
					closed,
					natural,
					hypotheses,
					GermBinaryOperation.At(T, F, res, F, res, F, res, op, x, W, s, t)))
		}),
})}

// InStalk — a set of pairs lies in the stalk at x exactly when it is the
// germ at x of a section over an open neighbourhood of x: the stalk is
// the set-builder of those germs.
var InStalk = inStalkThm{family.Add(registry.ProofEntry{
	Name: "InStalk",
	Key:  "prop_1f6db826a226f7f5",
	Build: family.Theorem("∀T:set(set(A)). "+
		"∀F:(set(A) → set(B)). "+
		"∀res:(set(A) → set(A) → B → B). "+
		"∀x:A. "+
		"∀g:set(prod(set(A), B)). "+
		"    g ∈ stalk(T, F, res, x) ⇔ "+
		"    ∃U:set(A). ∃s:B. U ∈ T ∧ x ∈ U ∧ s ∈ F(U) ∧ g = sheaf_germ(T, F, res, x, U, s)",
		func(
			a *Argument,
			T *Expr[Set[Set[A]]],
			F *Expr[Fun[Set[A], Set[B]]],
			res *Expr[Fun3[Set[A], Set[A], B, B]],
			x *Expr[A],
			g *Expr[Set[Prod[Set[A], B]]],
		) {
			a.Show(
				"the stalk is the set-builder of the germs at x of the sections over the open neighbourhoods of x",
				Simp(
					Fwd(StalkDef),
					Fwd(set_basic.SetMemberDef.Inst[Set[Prod[Set[A], B]]]()),
					Fwd(set_basic.SetComprehensionDef.Inst[Set[Prod[Set[A], B]]]()),
					Fwd(set_basic.ComprehensionSpecDef.Inst[Set[Prod[Set[A], B]]]())),
				Basic())
		}),
})}

// GermInStalk — the germ at x of a section over an open neighbourhood of
// x lies in the stalk at x, as the germ of that very section.
var GermInStalk = germInStalkThm{family.Add(registry.ProofEntry{
	Name: "GermInStalk",
	Key:  "prop_3ffc990bcba321fd",
	Reading: "The presheaf hypothesis is idle (InStalk needs none); the law " +
		"form is kept for the reading at a resident presheaf, which the apply " +
		"rung fires on where the bare theorem's conjunctive antecedent does not.",
	Build: Presheaf.Law(Statement{
		Binders: "∀x:A. ∀U:set(A). ∀s:B.",
		Hypotheses: []string{
			"U ∈ T",
			"x ∈ U",
			"s ∈ F(U)",
		},
		Conclusion: "sheaf_germ(x, U, s) ∈ stalk(x)",
	},
		func(a *Argument, _ PresheafFact[on.T], x *Expr[A], U *Expr[Set[A]], s *Expr[B], hypotheses Fact) {
			represented := a.Have(
				"it is the germ of a section over an open neighbourhood of x",
				"∃V:set(A). ∃t:B. V ∈ T ∧ x ∈ V ∧ t ∈ F(V) ∧ sheaf_germ(x, U, s) = sheaf_germ(x, V, t)",
				Derive(func(b *Argument) {
					b.Take(U)
					b.Take(s)
					b.Show(
						"the section s over U itself",
						By(hypotheses))
				}))
			a.Show(
				"so it lies in the stalk",
				By(represented, InStalk))
		}),
})}

// GermRepresentativeWithin — restrict any representative to its intersection
// with the prescribed neighbourhood; restriction preserves its germ.
var GermRepresentativeWithin = germRepresentativeWithinThm{family.Add(registry.ProofEntry{
	Name: "GermRepresentativeWithin",
	Key:  "prop_1e0876dc51a0de40",
	Build: Presheaf.Law(Statement{
		Binders: "∀x:A. ∀U:set(A). ∀g:set(prod(set(A), B)).",
		Hypotheses: []string{
			"U ∈ T",
			"x ∈ U",
			"g ∈ stalk(x)",
		},
		Conclusion: "∃V:set(A). ∃s:B. V ∈ T ∧ x ∈ V ∧ V ⊆ U ∧ s ∈ F(V) ∧ g = sheaf_germ(x, V, s)",
	},
		func(
			a *Argument,
			presheaf PresheafFact[on.T],
			x *Expr[A],
			U *Expr[Set[A]],
			g *Expr[Set[Prod[Set[A], B]]],
			hypotheses Fact,
		) {
			_, _, onW := a.Obtain2As[Set[A], B](
				"represent g over an open neighbourhood W of x",
				"∃W:set(A). ∃t:B. W ∈ T ∧ x ∈ W ∧ t ∈ F(W) ∧ g = sheaf_germ(x, W, t)",
				By(hypotheses, InStalk))
			meet := a.TermAs[Set[A]]("U ∩ W")
			restriction := a.TermAs[B]("res(W, U ∩ W, t)")
			open := a.Have(
				"the intersection is open",
				"U ∩ W ∈ T",
				By(topological_space.InterOpen.Read(Topology.Read(presheaf)), hypotheses, onW))
			inside := a.Have(
				"the intersection contains x and lies in both neighbourhoods",
				"x ∈ U ∩ W ∧ U ∩ W ⊆ U ∧ U ∩ W ⊆ W",
				BySets(hypotheses, onW))
			section := a.Have(
				"the restriction is a section over the intersection",
				"res(W, U ∩ W, t) ∈ F(U ∩ W)",
				By(RestrictIn.Read(presheaf), open, inside, onW))
			sameGerm := a.Have(
				"restriction preserves the germ",
				"sheaf_germ(x, U ∩ W, res(W, U ∩ W, t)) = sheaf_germ(x, W, t)",
				By(GermRestrict.Read(presheaf), open, inside, onW))
			a.Take(meet)
			a.Take(restriction)
			a.Show(
				"the restricted section represents g within U",
				By(sameGerm, section, open, inside, onW))
		}),
})}

// GermInduction — a property of germs at x holds of every germ at x once
// it holds of the germ of every section over an open neighbourhood of x:
// every member of the stalk is such a germ.
var GermInduction = germInductionThm{family.Add(registry.ProofEntry{
	Name: "GermInduction",
	Key:  "prop_4190f71df4153acb",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). " +
			"∀F:(set(A) → set(B)). " +
			"∀res:(set(A) → set(A) → B → B). " +
			"∀x:A. " +
			"∀P:(set(prod(set(A), B)) → bool). " +
			"∀g:set(prod(set(A), B)).",
		Hypotheses: []string{
			"∀W:set(A). ∀s:B. W ∈ T ∧ x ∈ W ∧ s ∈ F(W) ⇒ P(sheaf_germ(T, F, res, x, W, s))",
			"g ∈ stalk(T, F, res, x)",
		},
		Conclusion: "P(g)",
	},
		func(
			a *Argument,
			T *Expr[Set[Set[A]]],
			F *Expr[Fun[Set[A], Set[B]]],
			res *Expr[Fun3[Set[A], Set[A], B, B]],
			x *Expr[A],
			P *Arrow[Set[Prod[Set[A], B]], Bool],
			g *Expr[Set[Prod[Set[A], B]]],
			onEveryGerm, member Fact,
		) {
			represented := a.Have(
				"g is the germ of a section s over an open neighbourhood U of x",
				"∃U:set(A). ∃s:B. U ∈ T ∧ x ∈ U ∧ s ∈ F(U) ∧ g = sheaf_germ(T, F, res, x, U, s)",
				By(member, InStalk))
			_, _, onU := a.Unpack2As[Set[A], B](represented, "U", "s")
			section := a.Have(
				"s is a section over the open neighbourhood U of x",
				"U ∈ T ∧ x ∈ U ∧ s ∈ F(U)",
				By(onU))
			isGerm := a.Have(
				"and g is its germ",
				"g = sheaf_germ(T, F, res, x, U, s)",
				By(onU))
			a.Show(
				"so the property holds of g",
				isGerm.Rw(),
				By(onEveryGerm, section))
		}),
})}

// GermInduction3 — a property of three germs at x holds of every three
// germs at x once it holds of the germs of every three sections over one
// open neighbourhood of x: restricted to U ∩ V ∩ Z, each germ is the
// germ of its section's restriction.
var GermInduction3 = germInduction3Thm{family.Add(registry.ProofEntry{
	Name: "GermInduction3",
	Key:  "prop_f999cfd1303e2a99",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). " +
			"∀F:(set(A) → set(B)). " +
			"∀res:(set(A) → set(A) → B → B). " +
			"∀x:A. " +
			"∀P:(set(prod(set(A), B)) → set(prod(set(A), B)) → set(prod(set(A), B)) → bool). " +
			"∀g h k:set(prod(set(A), B)).",
		Hypotheses: []string{
			"presheaf(T, F, res)",
			"∀W:set(A). ∀s t r:B. " +
				"    W ∈ T ∧ x ∈ W ∧ s ∈ F(W) ∧ t ∈ F(W) ∧ r ∈ F(W) ⇒ " +
				"    P(sheaf_germ(x, W, s), sheaf_germ(x, W, t), sheaf_germ(x, W, r))",
			"g ∈ stalk(x) ∧ h ∈ stalk(x) ∧ k ∈ stalk(x)",
		},
		Conclusion: "P(g, h, k)",
	},
		func(
			a *Argument,
			T *Expr[Set[Set[A]]],
			F *Expr[Fun[Set[A], Set[B]]],
			res *Expr[Fun3[Set[A], Set[A], B, B]],
			x *Expr[A],
			P *Expr[Fun3[Set[Prod[Set[A], B]], Set[Prod[Set[A], B]], Set[Prod[Set[A], B]], Bool]],
			g, h, k *Expr[Set[Prod[Set[A], B]]],
			presheaf PresheafFact[on.T],
			onOneNeighbourhood, members Fact,
		) {
			inStalk := a.Conjuncts(
				members,
				"g lies in the stalk",
				"so does h",
				"and so does k")
			representedG := a.Have(
				"g is the germ of a section s over an open neighbourhood U of x",
				"∃U:set(A). ∃s:B. U ∈ T ∧ x ∈ U ∧ s ∈ F(U) ∧ g = sheaf_germ(x, U, s)",
				By(inStalk[0], InStalk))
			_, _, onU := a.Unpack2As[Set[A], B](representedG, "U", "s")
			sectionU := a.Have(
				"s is a section over the open neighbourhood U of x",
				"U ∈ T ∧ x ∈ U ∧ s ∈ F(U)",
				By(onU))
			representedH := a.Have(
				"h the germ of a section t over an open neighbourhood V of x",
				"∃V:set(A). ∃t:B. V ∈ T ∧ x ∈ V ∧ t ∈ F(V) ∧ h = sheaf_germ(x, V, t)",
				By(inStalk[1], InStalk))
			_, _, onV := a.Unpack2As[Set[A], B](representedH, "V", "t")
			sectionV := a.Have(
				"t one over the open neighbourhood V of x",
				"V ∈ T ∧ x ∈ V ∧ t ∈ F(V)",
				By(onV))
			representedK := a.Have(
				"and k the germ of a section r over an open neighbourhood Z of x",
				"∃Z:set(A). ∃r:B. Z ∈ T ∧ x ∈ Z ∧ r ∈ F(Z) ∧ k = sheaf_germ(x, Z, r)",
				By(inStalk[2], InStalk))
			_, _, onZ := a.Unpack2As[Set[A], B](representedK, "Z", "r")
			sectionZ := a.Have(
				"and r one over the open neighbourhood Z of x",
				"Z ∈ T ∧ x ∈ Z ∧ r ∈ F(Z)",
				By(onZ))
			interOpen := topological_space.InterOpen.Read(Topology.Read(presheaf))
			open := a.Have(
				"U ∩ V and U ∩ V ∩ Z are open",
				"U ∩ V ∈ T ∧ U ∩ V ∩ Z ∈ T",
				By(interOpen, sectionU, sectionV, sectionZ))
			inside := a.Have(
				"U ∩ V ∩ Z is a neighbourhood of x inside U, V and Z",
				"x ∈ U ∩ V ∩ Z ∧ U ∩ V ∩ Z ⊆ U ∧ U ∩ V ∩ Z ⊆ V ∧ U ∩ V ∩ Z ⊆ Z",
				BySets(sectionU, sectionV, sectionZ))
			isGermG := a.Have(
				"g is the germ of s",
				"g = sheaf_germ(x, U, s)",
				By(onU))
			isGermH := a.Have(
				"h is the germ of t",
				"h = sheaf_germ(x, V, t)",
				By(onV))
			isGermK := a.Have(
				"k is the germ of r",
				"k = sheaf_germ(x, Z, r)",
				By(onZ))
			restrictedG := a.Have(
				"so g is the germ of s restricted to U ∩ V ∩ Z",
				"g = sheaf_germ(x, U ∩ V ∩ Z, res(U, U ∩ V ∩ Z, s))",
				isGermG.Rw(),
				By(GermRestrict.Read(presheaf), sectionU, open, inside))
			restrictedH := a.Have(
				"h the germ of t restricted to U ∩ V ∩ Z",
				"h = sheaf_germ(x, U ∩ V ∩ Z, res(V, U ∩ V ∩ Z, t))",
				isGermH.Rw(),
				By(GermRestrict.Read(presheaf), sectionV, open, inside))
			restrictedK := a.Have(
				"and k the germ of r restricted to U ∩ V ∩ Z",
				"k = sheaf_germ(x, U ∩ V ∩ Z, res(Z, U ∩ V ∩ Z, r))",
				isGermK.Rw(),
				By(GermRestrict.Read(presheaf), sectionZ, open, inside))
			sections := a.Have(
				"the three restrictions are sections over U ∩ V ∩ Z",
				"res(U, U ∩ V ∩ Z, s) ∈ F(U ∩ V ∩ Z) ∧ "+
					"res(V, U ∩ V ∩ Z, t) ∈ F(U ∩ V ∩ Z) ∧ "+
					"res(Z, U ∩ V ∩ Z, r) ∈ F(U ∩ V ∩ Z)",
				By(RestrictIn.Read(presheaf), sectionU, sectionV, sectionZ, open, inside))
			a.Show(
				"so the property holds of g, h and k, the germs of three sections over U ∩ V ∩ Z",
				restrictedG.Rw(),
				restrictedH.Rw(),
				restrictedK.Rw(),
				By(onOneNeighbourhood, open, inside, sections))
		}),
})}

// GermInduction2 — a property of two germs at x holds of every two germs
// at x once it holds of the germs of every two sections over one open
// neighbourhood of x: it is GermInduction3 with an idle third germ.
var GermInduction2 = germInduction2Thm{family.Add(registry.ProofEntry{
	Name: "GermInduction2",
	Key:  "prop_c77a7a11a293563e",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). " +
			"∀F:(set(A) → set(B)). " +
			"∀res:(set(A) → set(A) → B → B). " +
			"∀x:A. " +
			"∀P:(set(prod(set(A), B)) → set(prod(set(A), B)) → bool). " +
			"∀g h:set(prod(set(A), B)).",
		Hypotheses: []string{
			"presheaf(T, F, res)",
			"∀W:set(A). ∀s t:B. " +
				"    W ∈ T ∧ x ∈ W ∧ s ∈ F(W) ∧ t ∈ F(W) ⇒ P(sheaf_germ(x, W, s), sheaf_germ(x, W, t))",
			"g ∈ stalk(x) ∧ h ∈ stalk(x)",
		},
		Conclusion: "P(g, h)",
	},
		func(
			a *Argument,
			T *Expr[Set[Set[A]]],
			F *Expr[Fun[Set[A], Set[B]]],
			res *Expr[Fun3[Set[A], Set[A], B, B]],
			x *Expr[A],
			P *Arrow2[Set[Prod[Set[A], B]], Set[Prod[Set[A], B]], Bool],
			g, h *Expr[Set[Prod[Set[A], B]]],
			presheaf PresheafFact[on.T],
			onOneNeighbourhood, members Fact,
		) {
			a.Show(
				"the three-germ principle at g, h and h again, for the property of the first two",
				By(
					At(
						GermInduction3,
						T,
						F,
						res,
						x,
						a.Term("λg:set(prod(set(A), B)). λh:set(prod(set(A), B)). λk:set(prod(set(A), B)). P(g, h)"),
						g,
						h,
						h),
					presheaf,
					onOneNeighbourhood,
					members))
		}),
})}

// GermActionDistributive — choose a scalar section and two vector sections
// over one neighbourhood; compatibility transfers their distributive law
// to the germs. The scalar and vector sections may have different types.
var GermActionDistributive = germActionDistributiveThm{family.Add(registry.ProofEntry{
	Name: "GermActionDistributive",
	Key:  "prop_4bbab493a305c578",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). " +
			"∀F:(set(A) → set(B)). " +
			"∀resF:(set(A) → set(A) → B → B). " +
			"∀G:(set(A) → set(C)). " +
			"∀resG:(set(A) → set(A) → C → C). " +
			"∀add:(set(A) → C → C → C). " +
			"∀act:(set(A) → B → C → C). " +
			"∀addGerm:(set(prod(set(A), C)) → set(prod(set(A), C)) → set(prod(set(A), C))). " +
			"∀actGerm:(set(prod(set(A), B)) → set(prod(set(A), C)) → set(prod(set(A), C))). " +
			"∀x:A. " +
			"∀c:set(prod(set(A), B)). " +
			"∀u v:set(prod(set(A), C)).",
		// The two presheaves and the point are one hypothesis, written
		// after the rules: in first place a conjunction reads as its
		// conjuncts.
		Hypotheses: []string{
			"∀U:set(A). ∀s t:C. U ∈ T ∧ s ∈ G(U) ∧ t ∈ G(U) ⇒ add(U, s, t) ∈ G(U)",
			"∀U:set(A). ∀b:B. ∀s:C. U ∈ T ∧ b ∈ F(U) ∧ s ∈ G(U) ⇒ act(U, b, s) ∈ G(U)",
			"∀U:set(A). ∀b:B. ∀s t:C. " +
				"    U ∈ T ∧ b ∈ F(U) ∧ s ∈ G(U) ∧ t ∈ G(U) ⇒ " +
				"    act(U, b, add(U, s, t)) = add(U, act(U, b, s), act(U, b, t))",
			"∀W:set(A). ∀s t:C. " +
				"    W ∈ T ∧ x ∈ W ∧ s ∈ G(W) ∧ t ∈ G(W) ⇒ " +
				"    addGerm(sheaf_germ(T, G, resG, x, W, s), sheaf_germ(T, G, resG, x, W, t)) = " +
				"    sheaf_germ(T, G, resG, x, W, add(W, s, t))",
			"∀W:set(A). ∀b:B. ∀s:C. " +
				"    W ∈ T ∧ x ∈ W ∧ b ∈ F(W) ∧ s ∈ G(W) ⇒ " +
				"    actGerm(sheaf_germ(T, F, resF, x, W, b), sheaf_germ(T, G, resG, x, W, s)) = " +
				"    sheaf_germ(T, G, resG, x, W, act(W, b, s))",
			"presheaf(T, F, resF) ∧ presheaf(T, G, resG) ∧ x ∈ ⋃T",
			"c ∈ stalk(T, F, resF, x) ∧ u ∈ stalk(T, G, resG, x) ∧ v ∈ stalk(T, G, resG, x)",
		},
		Conclusion: "actGerm(c, addGerm(u, v)) = addGerm(actGerm(c, u), actGerm(c, v))",
	},
		func(
			a *Argument,
			T *Expr[Set[Set[A]]],
			F *Expr[Fun[Set[A], Set[B]]],
			resF *Expr[Fun3[Set[A], Set[A], B, B]],
			G *Expr[Fun[Set[A], Set[C]]],
			resG *Expr[Fun3[Set[A], Set[A], C, C]],
			add *Expr[Fun3[Set[A], C, C, C]],
			act *Expr[Fun3[Set[A], B, C, C]],
			addGerm *Expr[Fun2[Set[Prod[Set[A], C]], Set[Prod[Set[A], C]], Set[Prod[Set[A], C]]]],
			actGerm *Expr[Fun2[Set[Prod[Set[A], B]], Set[Prod[Set[A], C]], Set[Prod[Set[A], C]]]],
			x *Expr[A],
			c *Expr[Set[Prod[Set[A], B]]],
			u, v *Expr[Set[Prod[Set[A], C]]],
			addClosed, actClosed, distributes, addCompatible, actCompatible, hypotheses, members Fact,
		) {
			presheavesAtPoint := a.Conjuncts(
				hypotheses,
				"F is the scalar presheaf",
				"G is the vector presheaf",
				"x lies in the space")
			inStalk := a.Conjuncts(
				members,
				"c is a scalar germ",
				"u is a vector germ",
				"v is a vector germ")
			spaceNeighborhood := a.Have(
				"the whole space is an open neighbourhood of x",
				"⋃T ∈ T ∧ x ∈ ⋃T",
				By(topological_space.SpaceOpen.Read(Topology.Read(presheavesAtPoint[0])), presheavesAtPoint[2]))
			representatives := CommonRepresentatives(a, x, a.TermAs[Set[A]]("⋃T"), spaceNeighborhood,
				GermInput{Presheaf: presheavesAtPoint[0], Germ: c, Member: inStalk[0]},
				GermInput{Presheaf: presheavesAtPoint[1], Germ: u, Member: inStalk[1]},
				GermInput{Presheaf: presheavesAtPoint[1], Germ: v, Member: inStalk[2]})
			W := representatives.Neighborhood
			s, t, r := representatives.Sections[0], representatives.Sections[1], representatives.Sections[2]
			neighborhood := representatives.NeighborhoodFact
			sIn, tIn, rIn := representatives.Members[0], representatives.Members[1], representatives.Members[2]
			a.Do(
				representatives.Equalities[0].Rw(),
				representatives.Equalities[1].Rw(),
				representatives.Equalities[2].Rw())

			addAt := a.Term("add").Apply(W)
			actAt := a.Term("act").Apply(W, s)
			vectorGerm := a.Term("sheaf_germ(T, G, resG, x)").Apply(W)
			scalarGerm := a.Term("sheaf_germ(T, F, resF, x)").Apply(W, s)
			inSections := a.Term("set_member⟨A:C⟩")
			sections := a.Term("G").Apply(W)
			sum, scaledT, scaledR := addAt.Apply(t, r), actAt.Apply(t), actAt.Apply(r)
			sumIn := a.Have(
				"the vector sum is a section over W",
				MakeProp(inSections.Apply(sum, sections)),
				By(addClosed, neighborhood, tIn, rIn))
			scaledTIn := a.Have(
				"the scalar action on t is a section over W",
				MakeProp(inSections.Apply(scaledT, sections)),
				By(actClosed, neighborhood, sIn, tIn))
			scaledRIn := a.Have(
				"the scalar action on r is a section over W",
				MakeProp(inSections.Apply(scaledR, sections)),
				By(actClosed, neighborhood, sIn, rIn))
			germAdd, germAct := a.Term("addGerm"), a.Term("actGerm")
			sumGerm := a.Have(
				"addition of the vector germs is the germ of their sum",
				MakeProp(Equal(germAdd.Apply(vectorGerm.Apply(t), vectorGerm.Apply(r)), vectorGerm.Apply(sum))),
				By(addCompatible, neighborhood, tIn, rIn))
			scaledSumGerm := a.Have(
				"the scalar action on the sum germ is represented over W",
				MakeProp(
					Equal(germAct.Apply(scalarGerm, vectorGerm.Apply(sum)), vectorGerm.Apply(actAt.Apply(sum)))),
				By(actCompatible, neighborhood, sIn, sumIn))
			scaledTGerm := a.Have(
				"the scalar action on the germ of t is represented over W",
				MakeProp(Equal(germAct.Apply(scalarGerm, vectorGerm.Apply(t)), vectorGerm.Apply(scaledT))),
				By(actCompatible, neighborhood, sIn, tIn))
			scaledRGerm := a.Have(
				"the scalar action on the germ of r is represented over W",
				MakeProp(Equal(germAct.Apply(scalarGerm, vectorGerm.Apply(r)), vectorGerm.Apply(scaledR))),
				By(actCompatible, neighborhood, sIn, rIn))
			sumOfScaledGerms := a.Have(
				"the sum of the acted germs is represented by the sum of their sections",
				MakeProp(Equal(
					germAdd.Apply(vectorGerm.Apply(scaledT), vectorGerm.Apply(scaledR)),
					vectorGerm.Apply(addAt.Apply(scaledT, scaledR)))),
				By(addCompatible, neighborhood, scaledTIn, scaledRIn))
			a.Show(
				"section distributivity gives the equality of germs",
				sumGerm.Rw(),
				scaledSumGerm.Rw(),
				scaledTGerm.Rw(),
				scaledRGerm.Rw(),
				sumOfScaledGerms.Rw(),
				Congr(),
				By(distributes, neighborhood, sIn, tIn, rIn))
		}),
})}

// GermsDetermineSection — on a sheaf, a section is determined by its
// germs: the open sets W ⊆ U on which s and t agree form a family V;
// equal germs at a point of U agree on an open neighbourhood of it
// inside U, so every point of U lies in a member of V and V covers U;
// and sections that agree on every member of a cover are equal.
var GermsDetermineSection = germsDetermineSectionThm{family.Add(registry.ProofEntry{
	Name: "GermsDetermineSection",
	Key:  "prop_729d92e53f957b8",
	Reading: "At U = ∅ the cover is ∅ or {∅} and Locality closes it; " +
		"otherwise the cover is the open W ⊆ U on which s and t agree.",
	Build: Sheaf.Law(Statement{
		Binders: "∀U:set(A). ∀s t:B.",
		Hypotheses: []string{
			"U ∈ T",
			"s ∈ F(U)",
			"t ∈ F(U)",
			"∀x:A. x ∈ U ⇒ sheaf_germ(x, U, s) = sheaf_germ(x, U, t)",
		},
		Conclusion: "s = t",
	},
		func(a *Argument, sheaf SheafFact[on.T], U *Expr[Set[A]], s, t *Expr[B], hypotheses Fact) {
			cover := a.Let("V", a.Term("{W:set(A) | W ∈ T ∧ W ⊆ U ∧ res(U, W, s) = res(U, W, t)}"))
			agree := a.Have(
				"s and t agree on every member of V",
				"∀W:set(A). W ∈ V ⇒ res(U, W, s) = res(U, W, t)",
				cover.Rw(),
				BySets())
			open := a.Have(
				"the members of V are open",
				"V ⊆ T",
				cover.Rw(),
				BySets())
			reached := a.Have(
				"each point of U lies in a member of V",
				"∀x:A. x ∈ U ⇒ ∃W:set(A). W ∈ V ∧ x ∈ W",
				Derive(func(b *Argument) {
					x := b.Fix("x")
					inU := b.Assume()
					W, near := b.ObtainAs[Set[A]](
						"the germs of s and t at x are equal, so s and t agree on an open W ∋ x inside U",
						"∃W:set(A). W ∈ T ∧ x ∈ W ∧ W ⊆ U ∩ U ∧ res(U, W, s) = res(U, W, t)",
						By(GermEq.Read(SheafPresheaf.Read(sheaf)).AsFact().At(x, U, U, s, t), inU, hypotheses))
					b.Take(W)
					b.Show(
						"W is open, lies inside U and carries the agreement, so it is a member of V, and it holds x",
						BySets(cover, near))
				}))
			covers := a.Have(
				"so V covers U, its members lying inside U",
				"⋃V = U",
				BySets(cover, reached))
			a.Show(
				"and sections that agree on every member of a cover are equal",
				By(Locality.Read(sheaf), agree, covers, open, hypotheses))
		}),
})}
