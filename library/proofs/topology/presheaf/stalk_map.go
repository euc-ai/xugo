// stalk_map.go — the map a continuous map and a compatible family of
// section maps induce on stalks: a germ goes to the germ of the image of
// any of its representatives over the preimage of its open.

package presheaf

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/topology/continuous"
	"github.com/euc-ai/xugo/library/registry"
)

// StalkMapDef — the germs of the images of all representatives, united.
var StalkMapDef = stalkMapDefThm{family.Define(registry.DefEntry{
	Name: "StalkMapDef", Const: "stalk_map",
	Key: "prop_860e8d78c5b41808",
	Type: "set(set(A)) → " +
		"(set(A) → set(B)) → " +
		"(set(A) → set(A) → B → B) → " +
		"(A → C) → " +
		"(set(C) → D → B) → " +
		"A → " +
		"set(prod(set(C), D)) → " +
		"set(prod(set(A), B))",
	Implicit: []string{"T", "F", "res"},
	Bundles:  []string{"presheaf(T, F, res)"},
	Equations: []string{
		"∀T:set(set(A)). " +
			"∀F:(set(A) → set(B)). " +
			"∀res:(set(A) → set(A) → B → B). " +
			"∀f:(A → C). " +
			"∀ψ:(set(C) → D → B). " +
			"∀x:A. " +
			"∀g:set(prod(set(C), D)). " +
			"    stalk_map(T, F, res, f, ψ, x, g) = " +
			"    ⋃{sheaf_germ(T, F, res, x, preimage_on(⋃T, f, V), ψ(V, t)) | V:set(C), t:D | (V, t) ∈ g}",
	},
})}

// StalkMapGerm — the stalk map sends the germ of t at f(x) to the germ
// at x of ψ(V, t). A representative (U, u) of the germ of t agrees with t
// on an open W ∋ f(x); the preimage of W is open by continuity, holds x,
// and on it the two image sections agree, since ψ commutes with
// restriction. So every image germ is the germ of ψ(V, t), and (V, t) is
// itself a representative. No locality is used.
var StalkMapGerm = stalkMapGermThm{family.Add(registry.ProofEntry{
	Name: "StalkMapGerm",
	Key:  "prop_4949885b760d89f8",
	Build: family.Theorem(Statement{
		Binders: "∀X:presheaf(A, B). " +
			"∀Y:presheaf(C, D). " +
			"∀f:(A → C). " +
			"∀ψ:(set(C) → D → B). " +
			"∀x:A. " +
			"∀V:set(C). " +
			"∀t:D.",
		Hypotheses: []string{
			"continuous_map(X.T, Y.T, f)",
			"∀V:set(C). ∀t:D. V ∈ Y.T ∧ t ∈ Y(V) ⇒ ψ(V, t) ∈ X(preimage_on(⋃X.T, f, V))",
			"∀V W:set(C). ∀t:D. " +
				"    V ∈ Y.T ∧ W ∈ Y.T ∧ W ⊆ V ∧ t ∈ Y(V) ⇒ " +
				"    X.res(preimage_on(⋃X.T, f, V), preimage_on(⋃X.T, f, W), ψ(V, t)) = ψ(W, Y.res(V, W, t))",
			"x ∈ ⋃X.T ∧ V ∈ Y.T ∧ f(x) ∈ V ∧ t ∈ Y(V)",
		},
		Conclusion: "stalk_map(X, f, ψ, x, sheaf_germ(Y.T, Y, Y.res, f(x), V, t)) = " +
			"sheaf_germ(X.T, X, X.res, x, preimage_on(⋃X.T, f, V), ψ(V, t))",
	},
		func(
			a *Argument,
			X PresheafFact[on.T],
			Y Fact,
			_ *Arrow[A, C],
			ψ *Arrow2[Set[C], D, B],
			morphism Fact,
			x *Expr[A],
			V *Expr[Set[C]],
			t *Expr[D],
			hypotheses Fact,
		) {
			parts := a.Conjuncts(
				morphism,
				"f is continuous",
				"ψ carries a section of Y over an open V to a section of X over the preimage of V",
				"ψ commutes with restriction")
			continuity, sections, natural := parts[0], parts[1], parts[2]
			own := a.Have(
				"t represents its own germ at f(x)",
				"(V, t) ∈ sheaf_germ(Y.T, Y, Y.res, f(x), V, t)",
				By(GermOwn.Read(Y), hypotheses))
			agree := a.Have(
				"every representative (U, u) of the germ of t at f(x) has the image germ of t at x",
				Statement{
					Binders: "∀U:set(C). ∀u:D.",
					Hypotheses: []string{
						"(U, u) ∈ sheaf_germ(Y.T, Y, Y.res, f(x), V, t)",
					},
					Conclusion: "sheaf_germ(X.T, X, X.res, x, preimage_on(⋃X.T, f, U), ψ(U, u)) = " +
						"sheaf_germ(X.T, X, X.res, x, preimage_on(⋃X.T, f, V), ψ(V, t))",
				},
				Derive(func(b *Argument) {
					U := b.FixAs[Set[C]]("U")
					u := b.FixAs[D]("u")
					inGerm := b.Assume()
					represents := b.Have(
						"u is a section over an open U ∋ f(x) agreeing with t near f(x)",
						"U ∈ Y.T ∧ "+
							"f(x) ∈ U ∧ "+
							"u ∈ Y(U) ∧ "+
							"∃W:set(C). W ∈ Y.T ∧ f(x) ∈ W ∧ W ⊆ V ∩ U ∧ Y.res(V, W, t) = Y.res(U, W, u)",
						inGerm.Simp(Fwd(InGerm)),
						By(inGerm))
					W, near := b.ObtainAs[Set[C]](
						"choose an open W ∋ f(x) inside V ∩ U on which t and u agree",
						"∃W:set(C). W ∈ Y.T ∧ f(x) ∈ W ∧ W ⊆ V ∩ U ∧ Y.res(V, W, t) = Y.res(U, W, u)",
						By(represents))
					open := b.Have(
						"the preimages of U, V and W are open, f being continuous",
						"preimage_on(⋃X.T, f, U) ∈ X.T ∧ preimage_on(⋃X.T, f, V) ∈ X.T ∧ preimage_on(⋃X.T, f, W) ∈ X.T",
						By(continuous.PreimageOpen.Read(continuity), hypotheses, represents, near))
					inside := b.Have(
						"x lies in the three preimages, and the preimage of W in the other two, as W lies in U and in V",
						"x ∈ preimage_on(⋃X.T, f, U) ∧ "+
							"x ∈ preimage_on(⋃X.T, f, V) ∧ "+
							"x ∈ preimage_on(⋃X.T, f, W) ∧ "+
							"preimage_on(⋃X.T, f, W) ⊆ preimage_on(⋃X.T, f, U) ∩ preimage_on(⋃X.T, f, V) ∧ "+
							"W ⊆ U ∧ "+
							"W ⊆ V",
						BySets(hypotheses, near))
					images := b.Have(
						"ψ(U, u) and ψ(V, t) are sections over the preimages of U and V",
						"ψ(U, u) ∈ X(preimage_on(⋃X.T, f, U)) ∧ ψ(V, t) ∈ X(preimage_on(⋃X.T, f, V))",
						By(sections, represents, hypotheses))
					imageAgrees := b.Have(
						"on the preimage of W the two image sections agree",
						"X.res(preimage_on(⋃X.T, f, U), preimage_on(⋃X.T, f, W), ψ(U, u)) = "+
							"X.res(preimage_on(⋃X.T, f, V), preimage_on(⋃X.T, f, W), ψ(V, t))",
						CalcEq(
							Leg(
								b.TermAs[B]("ψ(W, Y.res(U, W, u))"),
								"ψ commutes with restricting u from U to W",
								By(natural.At(U, W, u), represents, near, inside)),
							Leg(
								b.TermAs[B]("ψ(W, Y.res(V, W, t))"),
								"t and u agree on W",
								By(Normalized, near)),
							FinalLeg(
								"ψ commutes with restricting t from V to W",
								By(natural.At(V, W, t), hypotheses, near, inside))))
					imageNear := b.Have(
						"so the image sections agree on an open neighbourhood of x inside both preimages",
						"∃N:set(A). "+
							"    N ∈ X.T ∧ "+
							"    x ∈ N ∧ "+
							"    N ⊆ preimage_on(⋃X.T, f, U) ∩ preimage_on(⋃X.T, f, V) ∧ "+
							"    X.res(preimage_on(⋃X.T, f, U), N, ψ(U, u)) = X.res(preimage_on(⋃X.T, f, V), N, ψ(V, t))",
						Derive(func(c *Argument) {
							c.Take(c.TermAs[Set[A]]("preimage_on(⋃X.T, f, W)"))
							c.Show(
								"the preimage of W is such a neighbourhood",
								By(imageAgrees, open, inside))
						}))
					b.Show(
						"sections that agree near x have the same germ",
						By(
							imageNear,
							images,
							open,
							inside,
							GermEq.Read(X).AsFact().At(x,
								b.TermAs[Set[A]]("preimage_on(⋃X.T, f, U)"), b.TermAs[Set[A]]("preimage_on(⋃X.T, f, V)"),
								ψ.Apply(U, u), ψ.Apply(V, t))))
				}))
			a.Show(
				"the stalk map unites the image germs of the "+
					"representatives of the germ of t, each the germ of ψ(V, t)",
				Unfold(StalkMapDef),
				BySets(own, agree))
		}),
})}
