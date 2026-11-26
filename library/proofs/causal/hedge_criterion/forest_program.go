// forest_program.go — the class law of a forest program in closed form, and
// what it stands on: the forest mean reads the bits at a vertex only on the
// labels of the edges there, and a law reads only the labels its program
// reads.
//
// Two parts, marked by banners:
//
// - The labels a program reads
// - The forest program's law

package hedge_criterion

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/iterate/real/real_product"
	"github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_product"
	"github.com/euc-ai/xugo/library/registry"
)

// forestLabel is the type of a label of a forest program: an edge with a track.
type forestLabel = Prod[Prod[I, I], Set[I]]

// ---------------------------------------------------------------------------
// The labels a program reads
// ---------------------------------------------------------------------------

// forestSignMeanLocal — the forest mean reads σ at v only on the labels of the
// edges at v: two sets of labels that agree on every label (e, A) with e an
// edge of Ed at v and A a subset of U give v the same mean. This is the
// σ-locality signProgramDef asks of a sign program, N(p) being the two ends of
// p's edge, and the card ForestSignProgram reads it there. Off F the mean does
// not read σ at all; on F the spins of each track at v agree
// (real_product.Congruence), so the shares of the tracks agree, and so do their
// sums (real_sum.Congruence).
var forestSignMeanLocal = forestSignMeanLocalThm{family.Add(registry.ProofEntry{
	Name: "forestSignMeanLocal",
	Key:  "prop_a3bd745d850a87f6",
	Build: family.Theorem(Statement{
		Binders: "∀F R U:set(I). " +
			"∀Ed:set(prod(I, I)). " +
			"∀τ:(I → I). " +
			"∀W κ:(I → set(I) → real). " +
			"∀α:(I → real). " +
			"∀v:I. " +
			"∀z:set(I). " +
			"∀σ σ':set(prod(prod(I, I), set(I))).",
		Hypotheses: []string{
			"∀e:prod(I, I). ∀A:set(I). e ∈ «edgesAt»(v) ∧ A ⊆ U ⇒ ((e, A) ∈ σ ⇔ (e, A) ∈ σ')",
		},
		Conclusion: "«mean»(v, z, σ) = «mean»(v, z, σ')",
	}, func(
		a *Argument,
		F, R, U *Expr[Set[I]],
		Ed *Expr[Set[Prod[I, I]]],
		τ *Arrow[I, I],
		W, κ *Arrow2[I, Set[I], Real],
		α *Arrow[I, Real],
		v *Expr[I],
		z *Expr[Set[I]],
		σ, σp *Expr[Set[forestLabel]],
		agree Fact,
	) {
		sameSign := a.Have(
			"an edge at v on a track has the same sign in σ and in σ′",
			Statement{
				Binders:    "∀A:set(I). ∀e:prod(I, I).",
				Hypotheses: []string{"A ∈ «tracks»", "e ∈ «edgesAt»(v)"},
				Conclusion: "«sgn»((e, A) ∈ σ) = «sgn»((e, A) ∈ σ')",
			},
			By(agree))
		sameSpin := a.Have(
			"so on each track the spins at v multiply to the same sign",
			"∀A:set(I). A ∈ «tracks» ⇒ «trackSpin»(σ, A, v) = «trackSpin»(σ', A, v)",
			By(sameSign, real_product.Congruence))
		sameShare := a.Have(
			"and each track's share of the mean at v is the same",
			"∀A:set(I). A ∈ «tracks» ⇒ «share»(σ, v, A) = «share»(σ', v, A)",
			By(sameSpin))
		sameSum := a.Have(
			"so the shares add up to the same sum",
			"Σ_{A∈«tracks»} «share»(σ, v, A) = Σ_{A∈«tracks»} «share»(σ', v, A)",
			By(sameShare, real_sum.Congruence))
		a.Show(
			"which is the one place the mean reads σ",
			Unfold(forestSignMeanDef),
			sameSum.Rw(),
			Basic())
	}),
})}

// signLawOnReadLabels — the class law of a program that reads the bits only at
// the labels of Γ is the same over any finite Λ that holds Γ. The weight of σ,
// the product of the factors (1 ± g)/2, is that of σ ∩ Γ. A subset of Λ is a
// subset of Γ with a subset of the rest (real_sum.SubsetsSumDisjointUnion), and
// the sum over the second repeats one weight 2 ^ card(Λ ∖ Γ) times: the factor
// the labels off Γ add to 2 ^ card(Λ).
var signLawOnReadLabels = signLawOnReadLabelsThm{family.Add(registry.ProofEntry{
	Name: "signLawOnReadLabels",
	Key:  "prop_77dfd5aa87394bcc",
	Build: family.Theorem(Statement{
		Binders: "∀O X:set(I). ∀Λ Γ:set(C). ∀g:(I → set(I) → set(C) → real). ∀z:set(I).",
		Hypotheses: []string{
			"finite(Λ)",
			"Γ ⊆ Λ",
			"∀v:I. ∀σ:set(C). v ∈ O ∖ X ⇒ g(v, z, σ ∩ Γ) = g(v, z, σ)",
		},
		Conclusion: "latent_sign_law(O, Λ, g, X, z) = latent_sign_law(O, Γ, g, X, z)",
		Abbrev: Abbrev{
			{Name: "weight", Text: "λσ:set(C). Π_{v∈O ∖ X} (&1 + «sgn»(v ∈ z) * g(v, z, σ)) / &2"},
		},
	}, func(
		a *Argument,
		O, X *Expr[Set[I]],
		Λ, Γ *Expr[Set[C]],
		g *Expr[Fun3[I, Set[I], Set[C], Real]],
		z *Expr[Set[I]],
		finite, inside, reads Fact,
	) {
		rest := a.TermAs[Set[C]]("Λ ∖ Γ")
		weight := a.TermAs[Fun[Set[C], Real]]("«weight»")
		subsetsOfRead := a.TermAs[Set[Set[C]]]("{Y:set(C) | Y ⊆ Γ}")
		subsetsOfRest := a.TermAs[Set[Set[C]]]("{Z:set(C) | Z ⊆ Λ ∖ Γ}")
		same := a.Have(
			"the weight of σ is the weight of its part in Γ",
			"∀σ:set(C). «weight»(σ ∩ Γ) = «weight»(σ)",
			By(reads, real_product.Congruence))
		parts := a.Have(
			"Λ is Γ and the labels off Γ, two finite sets with nothing in common",
			"finite(Γ) ∧ finite(Λ ∖ Γ) ∧ disjoint(Γ, Λ ∖ Γ) ∧ Γ ∪ (Λ ∖ Γ) = Λ",
			BySets(finite, inside, finite_set.FiniteSubset.At(Γ, Λ), finite_set.FiniteDiff.At(Λ, Γ)))
		split := a.Have(
			"a subset of Λ is a subset of Γ with a subset of the rest",
			"Σ_{σ∈{σ:set(C) | σ ⊆ Λ}} «weight»(σ) = "+
				"Σ_{Y∈{Y:set(C) | Y ⊆ Γ}} Σ_{Z∈{Z:set(C) | Z ⊆ Λ ∖ Γ}} «weight»(Y ∪ Z)",
			By(parts, real_sum.SubsetsSumDisjointUnion.At(Γ, rest, weight)))
		inner := a.Have(
			"the inner sum repeats the weight of Y, once for each subset of the rest",
			Statement{
				Binders:    "∀Y:set(C).",
				Hypotheses: []string{"Y ⊆ Γ"},
				Conclusion: "Σ_{Z∈{Z:set(C) | Z ⊆ Λ ∖ Γ}} «weight»(Y ∪ Z) = &(2 ^ card(Λ ∖ Γ)) * «weight»(Y)",
			},
			Derive(func(b *Argument) {
				b.FixAs[Set[C]]()
				read := b.Assume()
				constant := b.Have(
					"labels adjoined off Γ do not move the weight",
					"∀Z:set(C). Z ⊆ Λ ∖ Γ ⇒ «weight»(Y ∪ Z) = «weight»(Y)",
					Derive(func(c *Argument) {
						c.FixAs[Set[C]]()
						unread := c.Assume()
						meet := c.Have(
							"the part of Y ∪ Z in Γ is Y",
							"(Y ∪ Z) ∩ Γ = Y",
							BySets(read, unread))
						c.Show(
							"so the two weights are that of one set",
							By(meet, same.At(c.TermAs[Set[C]]("Y ∪ Z"))))
					}))
				b.Show(
					"a constant summed over the subsets of the rest, 2 ^ card(Λ ∖ Γ) of them",
					By(
						constant,
						parts,
						real_sum.Congruence.At(
							subsetsOfRest,
							b.TermAs[Fun[Set[C], Real]]("λZ:set(C). «weight»(Y ∪ Z)"),
							b.TermAs[Fun[Set[C], Real]]("λZ:set(C). «weight»(Y)")),
						real_sum.Const.At(subsetsOfRest, b.TermAs[Real]("«weight»(Y)")),
						cardinality.CardPowerset.At(rest),
						finite_set.FinitePowerset.At(rest)))
			}))
		scaled := a.Have(
			"so the sum over the subsets of Λ is 2 ^ card(Λ ∖ Γ) times the sum over the subsets of Γ",
			"Σ_{σ∈{σ:set(C) | σ ⊆ Λ}} «weight»(σ) = &(2 ^ card(Λ ∖ Γ)) * Σ_{Y∈{Y:set(C) | Y ⊆ Γ}} «weight»(Y)",
			By(
				inner,
				split,
				real_sum.Congruence.At(
					subsetsOfRead,
					a.TermAs[Fun[Set[C], Real]]("λY:set(C). Σ_{Z∈{Z:set(C) | Z ⊆ Λ ∖ Γ}} «weight»(Y ∪ Z)"),
					a.TermAs[Fun[Set[C], Real]]("λY:set(C). &(2 ^ card(Λ ∖ Γ)) * «weight»(Y)")),
				real_sum.ScalarLeft.At(a.TermAs[Real]("&(2 ^ card(Λ ∖ Γ))"), weight, subsetsOfRead)))
		count := a.Have(
			"the labels are counted in the two parts",
			"card(Λ) = card(Γ) + card(Λ ∖ Γ)",
			BySets(finite, inside, cardinality.CardOfDisjointParts.At(Γ, rest, Λ)))
		a.Show(
			"the factor 2 ^ card(Λ ∖ Γ) of the sum, a positive "+
				"number, cancels against the same factor of 2 ^ card(Λ)",
			Unfold(signLawDef),
			count.Rw(),
			Simp(Fwd(nat_arith.PowAdd), Fwd(real_construction.OfNumMul)),
			scaled.Rw(),
			ByArith(nat_order.PowPositive.At(a.TermAs[Nat]("2"), a.TermAs[Nat]("card(Λ ∖ Γ)"))))
	}),
})}

// ---------------------------------------------------------------------------
// The forest program's law
// ---------------------------------------------------------------------------

// forestTrackProduct — along one track A the terms of the forest multiply to
// the coefficients, the signed κ of the roots and the signed W of the track.
// Write the signed factor of v for its sign times W on the track, κ at a root
// and 1 elsewhere. Off R and off A it is a sign, so the signed factors
// telescope along τ to those of R and of A (StepSignTelescope); a vertex
// stepping to v is off R and off A, so the product of the signs stepping to v
// is the product of their signed factors, and the term of the track at v is its
// coefficient times the telescoping factor.
var forestTrackProduct = forestTrackProductThm{family.Add(registry.ProofEntry{
	Name: "forestTrackProduct",
	Key:  "prop_bdf2f3f08c9aad97",
	Build: family.Theorem(Statement{
		Binders: "∀F R A:set(I). ∀τ:(I → I). ∀W κ:(I → set(I) → real). ∀α:(I → real). ∀z:set(I).",
		Hypotheses: []string{
			"finite(F)",
			"R ⊆ F",
			"A ⊆ F ∖ R",
			"∀w:I. w ∈ F ∧ w ∉ R ⇒ τ(w) ∈ F",
		},
		Conclusion: "Π_{v∈F} «term»(v, A) = " +
			"(Π_{v∈F} α(v)) * (Π_{r∈R} «sgn»(r ∈ z) * κ(r, z)) * Π_{u∈A} «sgn»(u ∈ z) * W(u, z)",
		Abbrev: Abbrev{
			{Name: "signed", Text: "λv:I. «sgn»(v ∈ z) * COND(v ∈ A, W(v, z), COND(v ∈ R, κ(v, z), &1))"},
		},
	}, func(
		a *Argument,
		F, R, A *Expr[Set[I]],
		τ *Arrow[I, I],
		W, κ *Arrow2[I, Set[I], Real],
		α *Arrow[I, Real],
		z *Expr[Set[I]],
		finite, roots, track, steps Fact,
	) {
		signed := a.TermAs[Fun[I, Real]]("«signed»")
		square := a.Have(
			"off R and off A the signed factor is a sign, which squares to 1",
			"∀w:I. w ∈ F ∧ w ∉ R ∧ w ∉ A ⇒ «signed»(w) * «signed»(w) = &1",
			ByArith())
		telescope := a.Have(
			"the signed factors telescope along τ to those of the roots and of the track",
			"Π_{v∈F} «signed»(v) * Π_{w∈«stepsTo»(A, v)} «signed»(w) = "+
				"(Π_{r∈R} «signed»(r)) * Π_{u∈A} «signed»(u)",
			By(finite, roots, track, steps, square, StepSignTelescope.At(F, R, A, τ, signed)))
		atRoot := a.Have(
			"at a root, which is off the track, the signed factor is the sign times κ",
			"∀r:I. r ∈ R ⇒ «signed»(r) = «sgn»(r ∈ z) * κ(r, z)",
			BySets(track))
		overRoots := a.Have(
			"so over the roots the signed factors are the signed κ",
			"Π_{r∈R} «signed»(r) = Π_{r∈R} «sgn»(r ∈ z) * κ(r, z)",
			By(
				atRoot,
				real_product.Congruence.At(R, signed, a.TermAs[Fun[I, Real]]("λr:I. «sgn»(r ∈ z) * κ(r, z)"))))
		onTrack := a.Have(
			"on the track the signed factor is the sign times W",
			"∀u:I. u ∈ A ⇒ «signed»(u) = «sgn»(u ∈ z) * W(u, z)",
			ByArith())
		overTrack := a.Have(
			"so over the track the signed factors are the signed W",
			"Π_{u∈A} «signed»(u) = Π_{u∈A} «sgn»(u ∈ z) * W(u, z)",
			By(
				onTrack,
				real_product.Congruence.At(A, signed, a.TermAs[Fun[I, Real]]("λu:I. «sgn»(u ∈ z) * W(u, z)"))))
		steppingIn := a.Have(
			"a vertex stepping to v is off R and off A, where the signed factor is the sign",
			"∀v w:I. w ∈ «stepsTo»(A, v) ⇒ «signed»(w) = «sgn»(w ∈ z)",
			ByArith())
		signsIn := a.Have(
			"so the signed factors stepping to v multiply to the product of the signs stepping to v",
			"∀v:I. Π_{w∈«stepsTo»(A, v)} «signed»(w) = Π_{w∈«stepsTo»(A, v)} «sgn»(w ∈ z)",
			By(steppingIn, real_product.Congruence))
		regroup := a.Have(
			"the term of the track at v is its coefficient times the telescoping factor",
			"∀v:I. «term»(v, A) = α(v) * («signed»(v) * Π_{w∈«stepsTo»(A, v)} «signed»(w))",
			ByArith(signsIn))
		whole := a.Have(
			"the coefficients leave the product over F",
			"Π_{v∈F} «term»(v, A) = (Π_{v∈F} α(v)) * Π_{v∈F} «signed»(v) * Π_{w∈«stepsTo»(A, v)} «signed»(w)",
			Simp(Fwd(regroup)),
			By(finite, real_product.Pointwise))
		a.Show(
			"the coefficients, then the telescoped factors read on the roots and on the track",
			ByArith(whole, telescope, overRoots, overTrack))
	}),
})}

// forestSignLaw — the class law of a forest program in closed form: the product
// of the route factors 1 + s(v)·W(v), where s(v) = «sgn»(v ∈ z) is the sign of
// v, over the vertices off X and, when X misses F, the forest's term. The mean
// reads the spins of its own labels alone (forestSignMeanLocal), the edges of
// Ed with the subsets of U, so the law over Λ is the law over them
// (signLawOnReadLabels). There the halves leave each product
// (real_product.ProductOfHalves) and the product over the vertices off X splits
// at F: off F the factors are route factors and leave the sum; on F each is the
// route factor of v and, for each track, a term times the track's spins at v.
// Averaged over the spins the product over F ∖ X keeps the term with no track
// and, over all of F, the terms that follow one track (spinTrackExpansion),
// which cancels the 2 to the number of labels. One track contributes the
// coefficients, the signed κ of the roots and its own signed W
// (forestTrackProduct), and the sum over the tracks turns the last into the
// route factors of U (real_product.SubsetProductsSum). F ∖ X is all of F
// exactly when X misses F.
var forestSignLaw = forestSignLawThm{family.Add(registry.ProofEntry{
	Name: "forestSignLaw",
	Key:  "prop_2f4dadc71e3ec0dc",
	Reading: "The class law of a forest program in closed form, at any functions W and κ and " +
		"any coefficients α: no locality and no bound is read. With X meeting F the forest's " +
		"term is gone — this is what holding a vertex of the forest does. Λ may hold labels the " +
		"mean does not read; they average out. F ≠ ∅ and connectivity are load-bearing as in " +
		"spinTrackExpansion, and τ keeping F ∖ R inside F as in StepSignTelescope.",
	Build: family.Sections(Statement{
		Binders: "∀O X F R U:set(I). " +
			"∀Ed:set(prod(I, I)). " +
			"∀Λ:set(prod(prod(I, I), set(I))). " +
			"∀τ:(I → I). " +
			"∀W κ:(I → set(I) → real). " +
			"∀α:(I → real). " +
			"∀z:set(I).",
		Hypotheses: []string{
			"finite(O)",
			"F ⊆ O",
			"F ≠ ∅",
			"finite(Ed)",
			"∀e:prod(I, I). e ∈ Ed ⇒ fst(e) ∈ F ∧ snd(e) ∈ F ∧ fst(e) ≠ snd(e)",
			"∀u v:I. u ∈ F ∧ v ∈ F ⇒ reflexive_transitive_closure(«adjacent», u, v)",
			"R ⊆ F",
			"U ⊆ F ∖ R",
			"∀w:I. w ∈ F ∧ w ∉ R ⇒ τ(w) ∈ F",
			"finite(Λ)",
			"«labels» ⊆ Λ",
		},
		Conclusion: "latent_sign_law(O, Λ, «mean», X, z) = " +
			"(Π_{v∈O ∖ X} (&1 + «sgn»(v ∈ z) * W(v, z)) + " +
			"    COND(F ∩ X = ∅, " +
			"        (Π_{v∈F} α(v)) * " +
			"        (Π_{r∈R} «sgn»(r ∈ z) * κ(r, z)) * " +
			"        (Π_{u∈U} (&1 + «sgn»(u ∈ z) * W(u, z))) * " +
			"        Π_{v∈(O ∖ X) ∖ F} (&1 + «sgn»(v ∈ z) * W(v, z)), " +
			"        &0)) / " +
			"&(2 ^ card(O ∖ X))",
		Abbrev: Abbrev{
			{Name: "labels", Text: "set_cross(Ed, «tracks»)"},
			{Name: "configs", Text: "{σ:set(prod(prod(I, I), set(I))) | σ ⊆ «labels»}"},
			{Name: "route", Text: "λv:I. &1 + «sgn»(v ∈ z) * W(v, z)"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		factorsOffX := ctx.Lemma(Statement{
			Binders: "∀O X F R U:set(I). " +
				"∀Ed:set(prod(I, I)). " +
				"∀τ:(I → I). " +
				"∀W κ:(I → set(I) → real). " +
				"∀α:(I → real). " +
				"∀z:set(I). " +
				"∀σ:set(prod(prod(I, I), set(I))).",
			Hypotheses: []string{
				"finite(O)",
				"F ⊆ O",
			},
			Conclusion: "Π_{v∈O ∖ X} (&1 + «sgn»(v ∈ z) * «mean»(v, z, σ)) / &2 = " +
				"(Π_{v∈(O ∖ X) ∖ F} «route»(v)) * " +
				"(Π_{v∈F ∖ X} («route»(v) + Σ_{A∈«tracks»} «term»(v, A) * «trackSpin»(σ, A, v))) / " +
				"&(2 ^ card(O ∖ X))",
		}, func(
			a *Argument,
			O, X, F, R, U *Expr[Set[I]],
			Ed *Expr[Set[Prod[I, I]]],
			τ *Arrow[I, I],
			W, κ *Arrow2[I, Set[I], Real],
			α *Arrow[I, Real],
			z *Expr[Set[I]],
			σ *Expr[Set[forestLabel]],
			finiteO, inO Fact,
		) {
			offX := a.TermAs[Set[I]]("O ∖ X")
			forestOffX := a.TermAs[Set[I]]("F ∖ X")
			factorAt := a.TermAs[Fun[I, Real]]("λv:I. &1 + «sgn»(v ∈ z) * «mean»(v, z, σ)")
			offForest := a.Have(
				"off F the mean is the route term",
				"∀v:I. v ∉ F ⇒ &1 + «sgn»(v ∈ z) * «mean»(v, z, σ) = «route»(v)",
				Unfold(forestSignMeanDef),
				ByArith())
			onForest := a.Have(
				"on F the factor is the route factor and, for each track, a term times the track's spins at v",
				Statement{
					Binders:    "∀v:I.",
					Hypotheses: []string{"v ∈ F"},
					Conclusion: "&1 + «sgn»(v ∈ z) * «mean»(v, z, σ) = " +
						"«route»(v) + Σ_{A∈«tracks»} «term»(v, A) * «trackSpin»(σ, A, v)",
				},
				Derive(func(b *Argument) {
					b.FixAs[I]()
					inForest := b.Assume()
					through := b.Have(
						"the sign and the coefficient of v go through the sum over the tracks",
						"«sgn»(v ∈ z) * α(v) * (Σ_{A∈«tracks»} «share»(σ, v, A)) = "+
							"Σ_{A∈«tracks»} «term»(v, A) * «trackSpin»(σ, A, v)",
						Simp(Fwd(real_sum.ScalarLeft)),
						ByArith())
					b.Show(
						"the mean of a vertex of F is its route term and its coefficient times the sum of the shares",
						Unfold(forestSignMeanDef),
						ByArith(through, inForest))
				}))
			finiteOffX := a.Have(
				"the vertices off X are finitely many",
				"finite(O ∖ X)",
				By(finiteO, finite_set.FiniteDiff.At(O, X)))
			sets := a.Conjuncts(
				a.Have(
					"F ∖ X is the part of O ∖ X inside F",
					"F ∖ X ⊆ O ∖ X ∧ (O ∖ X) ∖ (F ∖ X) = (O ∖ X) ∖ F",
					BySets(inO)),
				"F ∖ X lies in O ∖ X",
				"what O ∖ X has off F ∖ X is what it has off F")
			insideOffX, remainder := sets[0], sets[1]
			outside := a.Have(
				"off F the factors are the route factors",
				"Π_{v∈(O ∖ X) ∖ F} (&1 + «sgn»(v ∈ z) * «mean»(v, z, σ)) = Π_{v∈(O ∖ X) ∖ F} «route»(v)",
				By(offForest, set_basic.InDiff, real_product.Congruence))
			within := a.Have(
				"on F they are in track form",
				"Π_{v∈F ∖ X} (&1 + «sgn»(v ∈ z) * «mean»(v, z, σ)) = "+
					"Π_{v∈F ∖ X} («route»(v) + Σ_{A∈«tracks»} «term»(v, A) * «trackSpin»(σ, A, v))",
				By(onForest, set_basic.InDiff, real_product.Congruence))
			split := a.Have(
				"the product over O ∖ X is the product off F times the product over F ∖ X",
				"Π_{v∈O ∖ X} (&1 + «sgn»(v ∈ z) * «mean»(v, z, σ)) = "+
					"(Π_{v∈(O ∖ X) ∖ F} «route»(v)) * "+
					"Π_{v∈F ∖ X} («route»(v) + Σ_{A∈«tracks»} «term»(v, A) * «trackSpin»(σ, A, v))",
				By(
					outside,
					within,
					finiteOffX,
					insideOffX,
					remainder,
					real_product.Diff.At(offX, forestOffX, factorAt)))
			a.Show(
				"and the halves leave the product",
				By(split, finiteOffX, real_product.ProductOfHalves.At(offX, factorAt)))
		})

		averaged := ctx.Lemma(Statement{
			Binders: "∀X F R U:set(I). " +
				"∀Ed:set(prod(I, I)). " +
				"∀τ:(I → I). " +
				"∀W κ:(I → set(I) → real). " +
				"∀α:(I → real). " +
				"∀z:set(I).",
			Hypotheses: []string{
				"finite(F)",
				"F ≠ ∅",
				"finite(Ed)",
				"∀e:prod(I, I). e ∈ Ed ⇒ fst(e) ∈ F ∧ snd(e) ∈ F ∧ fst(e) ≠ snd(e)",
				"∀u v:I. u ∈ F ∧ v ∈ F ⇒ reflexive_transitive_closure(«adjacent», u, v)",
				"R ⊆ F",
				"U ⊆ F ∖ R",
				"∀w:I. w ∈ F ∧ w ∉ R ⇒ τ(w) ∈ F",
			},
			Conclusion: "Σ_{σ∈«configs»} Π_{v∈F ∖ X} («route»(v) + Σ_{A∈«tracks»} «term»(v, A) * «trackSpin»(σ, A, v)) = " +
				"&(2 ^ (card(Ed) * card(«tracks»))) * " +
				"(Π_{v∈F ∖ X} «route»(v) + " +
				"    COND(F ∖ X = F, (Π_{v∈F} α(v)) * (Π_{r∈R} «sgn»(r ∈ z) * κ(r, z)) * Π_{u∈U} «route»(u), &0))",
		}, func(
			a *Argument,
			X, F, R, U *Expr[Set[I]],
			Ed *Expr[Set[Prod[I, I]]],
			τ *Arrow[I, I],
			W, κ *Arrow2[I, Set[I], Real],
			α *Arrow[I, Real],
			z *Expr[Set[I]],
			finiteF, nonempty, finiteEd, edges, connected, roots, reentry, steps Fact,
		) {
			tracks := a.TermAs[Set[Set[I]]]("«tracks»")
			route := a.TermAs[Fun[I, Real]]("«route»")
			term := a.TermAs[Fun2[I, Set[I], Real]]("«term»")
			forestOffX := a.TermAs[Set[I]]("F ∖ X")
			finiteU := a.Have(
				"U lies in the finite F",
				"finite(U)",
				By(
					finiteF,
					reentry,
					finite_set.FiniteDiff.At(F, R),
					finite_set.FiniteSubset.At(U, a.TermAs[Set[I]]("F ∖ R"))))
			finiteTracks := a.Have(
				"so its subsets, the tracks, are finitely many",
				"finite(«tracks»)",
				By(finiteU, finite_set.FinitePowerset.At(U)))
			insideF := a.Have(
				"F ∖ X lies in F",
				"F ∖ X ⊆ F",
				BySets())
			expansion := a.Have(
				"averaged over the spins, the product over F ∖ X keeps the "+
					"term with no track and, over all of F, one term for each track",
				"Σ_{σ∈«configs»} Π_{v∈F ∖ X} («route»(v) + Σ_{A∈«tracks»} «term»(v, A) * «trackSpin»(σ, A, v)) = "+
					"&(2 ^ (card(Ed) * card(«tracks»))) * "+
					"(Π_{v∈F ∖ X} «route»(v) + COND(F ∖ X = F, Σ_{A∈«tracks»} Π_{v∈F} «term»(v, A), &0))",
				By(
					finiteEd,
					edges,
					connected,
					finiteTracks,
					nonempty,
					insideF,
					spinTrackExpansion.At(F, forestOffX, Ed, tracks, route, term)))
			oneTrack := a.Have(
				"one track contributes the coefficients, the signed κ of the roots and its own signed W",
				Statement{
					Binders:    "∀A:set(I).",
					Hypotheses: []string{"A ∈ «tracks»"},
					Conclusion: "Π_{v∈F} «term»(v, A) = " +
						"(Π_{v∈F} α(v)) * (Π_{r∈R} «sgn»(r ∈ z) * κ(r, z)) * Π_{u∈A} «sgn»(u ∈ z) * W(u, z)",
				},
				Derive(func(b *Argument) {
					A := b.FixAs[Set[I]]()
					isTrack := b.Assume()
					offRoots := b.Have(
						"a track lies in F off the roots",
						"A ⊆ F ∖ R",
						BySets(isTrack, reentry))
					b.Show(
						"the product of the terms of the track A",
						By(finiteF, roots, offRoots, steps, forestTrackProduct.At(F, R, A, τ, W, κ, α, z)))
				}))
			trackSum := a.Have(
				"summed over the tracks, the signed W of the track becomes the route factors of U",
				"Σ_{A∈«tracks»} Π_{v∈F} «term»(v, A) = "+
					"(Π_{v∈F} α(v)) * (Π_{r∈R} «sgn»(r ∈ z) * κ(r, z)) * Π_{u∈U} «route»(u)",
				By(
					oneTrack,
					finiteU,
					real_product.SubsetProductsSum.At(U, a.TermAs[Fun[I, Real]]("λu:I. «sgn»(u ∈ z) * W(u, z)")),
					real_sum.Congruence.At(
						tracks,
						a.TermAs[Fun[Set[I], Real]]("λA:set(I). Π_{v∈F} «term»(v, A)"),
						a.TermAs[Fun[Set[I], Real]](
							"λA:set(I). (Π_{v∈F} α(v)) * (Π_{r∈R} «sgn»(r ∈ z) * κ(r, z)) * Π_{u∈A} «sgn»(u ∈ z) * W(u, z)")),
					real_sum.ScalarLeft.At(
						a.TermAs[Real]("(Π_{v∈F} α(v)) * Π_{r∈R} «sgn»(r ∈ z) * κ(r, z)"),
						a.TermAs[Fun[Set[I], Real]]("λA:set(I). Π_{u∈A} «sgn»(u ∈ z) * W(u, z)"),
						tracks)))
			a.Show(
				"so the forest's term is the coefficients, the signed κ of the roots and the route factors of U",
				By(expansion, trackSum))
		})

		return ctx.Theorem(headline, func(
			a *Argument,
			O, X, F, R, U *Expr[Set[I]],
			Ed *Expr[Set[Prod[I, I]]],
			Λ *Expr[Set[forestLabel]],
			τ *Arrow[I, I],
			W, κ *Arrow2[I, Set[I], Real],
			α *Arrow[I, Real],
			z *Expr[Set[I]],
			finiteO, inO, nonempty, finiteEd, edges, connected, roots, reentry, steps, finiteΛ, own Fact,
		) {
			tracks := a.TermAs[Set[Set[I]]]("«tracks»")
			labels := a.TermAs[Set[forestLabel]]("«labels»")
			mean := a.TermAs[Fun3[I, Set[I], Set[forestLabel], Real]]("«mean»")
			route := a.TermAs[Fun[I, Real]]("«route»")
			offX := a.TermAs[Set[I]]("O ∖ X")
			forestOffX := a.TermAs[Set[I]]("F ∖ X")
			reads := a.Have(
				"the mean reads the spins of its own labels alone, an edge at v with a track being a label",
				"∀v:I. ∀σ:set(prod(prod(I, I), set(I))). «mean»(v, z, σ ∩ «labels») = «mean»(v, z, σ)",
				By(forestSignMeanLocal, set_product.InCross, set_basic.InInter))
			finiteF := a.Have(
				"F lies in the finite O",
				"finite(F)",
				By(finiteO, inO, finite_set.FiniteSubset.At(F, O)))
			finiteTracks := a.Have(
				"U lies in F, so its subsets, the tracks, are finitely many",
				"finite(«tracks»)",
				By(
					finiteF,
					reentry,
					finite_set.FiniteDiff.At(F, R),
					finite_set.FiniteSubset.At(U, a.TermAs[Set[I]]("F ∖ R")),
					finite_set.FinitePowerset.At(U)))
			count := a.Have(
				"the labels are the edges with the tracks",
				"card(«labels») = card(Ed) * card(«tracks»)",
				By(finiteEd, finiteTracks, cardinality.CardProduct.At(Ed, tracks)))
			finiteOffX := a.Have(
				"the vertices off X are finitely many",
				"finite(O ∖ X)",
				By(finiteO, finite_set.FiniteDiff.At(O, X)))
			sets := a.Conjuncts(
				a.Have(
					"F ∖ X is the part of O ∖ X inside F, and it is all of F exactly when X misses F",
					"F ∖ X ⊆ O ∖ X ∧ (O ∖ X) ∖ (F ∖ X) = (O ∖ X) ∖ F ∧ (F ∖ X = F ⇔ F ∩ X = ∅)",
					BySets(inO)),
				"F ∖ X lies in O ∖ X",
				"what O ∖ X has off F ∖ X is what it has off F",
				"F ∖ X is F exactly when X misses F")
			insideOffX, remainder, allOfF := sets[0], sets[1], sets[2]
			whole := a.Have(
				"the route factors off F and over F ∖ X are those of O ∖ X",
				"(Π_{v∈(O ∖ X) ∖ F} «route»(v)) * Π_{v∈F ∖ X} «route»(v) = Π_{v∈O ∖ X} «route»(v)",
				By(finiteOffX, insideOffX, remainder, real_product.Diff.At(offX, forestOffX, route)))
			positive := a.Have(
				"a power of two is positive",
				"&0 < &(2 ^ (card(Ed) * card(«tracks»)))",
				ByArith(nat_order.PowPositive.At(a.TermAs[Nat]("2"), a.TermAs[Nat]("card(Ed) * card(«tracks»)"))))
			factor := a.Have(
				"for each σ the product over the vertices off X splits at F, the halves taken out",
				"∀σ:set(prod(prod(I, I), set(I))). "+
					"    Π_{v∈O ∖ X} (&1 + «sgn»(v ∈ z) * «mean»(v, z, σ)) / &2 = "+
					"    (Π_{v∈(O ∖ X) ∖ F} «route»(v)) * "+
					"    (Π_{v∈F ∖ X} («route»(v) + Σ_{A∈«tracks»} «term»(v, A) * «trackSpin»(σ, A, v))) / "+
					"    &(2 ^ card(O ∖ X))",
				a.ForEach(func(σ *Expr[Set[forestLabel]]) Action {
					return By(finiteO, inO, At(factorsOffX, O, X, F, R, U, Ed, τ, W, κ, α, z, σ))
				}))
			a.Show(
				"the law over the mean's own labels, written out, split at F and averaged over the spins",
				CalcEq(
					Leg(
						a.TermAs[Real]("latent_sign_law(O, «labels», «mean», X, z)"),
						"the mean reads its own labels alone, so the law over Λ is the law over them",
						By(finiteΛ, own, reads, signLawOnReadLabels.At(O, X, Λ, labels, mean, z))),
					Leg(
						a.TermAs[Real](
							"(Σ_{σ∈«configs»} Π_{v∈O ∖ X} (&1 + «sgn»(v ∈ z) * «mean»(v, z, σ)) / &2) / &(2 ^ card(«labels»))"),
						"the law is the average over the configurations of the labels",
						Simp(Fwd(signLawDef))),
					Leg(
						a.TermAs[Real](
							"((Π_{v∈(O ∖ X) ∖ F} «route»(v)) / "+
								"    &(2 ^ card(O ∖ X)) * "+
								"    Σ_{σ∈«configs»} Π_{v∈F ∖ X} («route»(v) + Σ_{A∈«tracks»} «term»(v, A) * «trackSpin»(σ, A, v))) / "+
								"&(2 ^ card(«labels»))"),
						"for each σ the halves leave the product, which "+
							"splits at F, and the route factors off F leave the sum",
						Simp(Fwd(factor), Fwd(real_sum.ScalarLeft)),
						ByArith()),
					Leg(
						a.TermAs[Real](
							"((Π_{v∈(O ∖ X) ∖ F} «route»(v)) / "+
								"    &(2 ^ card(O ∖ X)) * "+
								"    (&(2 ^ (card(Ed) * card(«tracks»))) * "+
								"        (Π_{v∈F ∖ X} «route»(v) + "+
								"            COND(F ∖ X = F, "+
								"                (Π_{v∈F} α(v)) * (Π_{r∈R} «sgn»(r ∈ z) * κ(r, z)) * Π_{u∈U} «route»(u), "+
								"                &0)))) / "+
								"&(2 ^ (card(Ed) * card(«tracks»)))"),
						"averaged over the spins only the term with no track and the "+
							"forest's term remain, and the labels are the edges with the tracks",
						By(
							finiteF,
							nonempty,
							finiteEd,
							edges,
							connected,
							roots,
							reentry,
							steps,
							count,
							At(averaged, X, F, R, U, Ed, τ, W, κ, α, z))),
					FinalLeg(
						"the power of two for the labels cancels, the route factors "+
							"join over O ∖ X, and F ∖ X is F exactly when X misses F",
						whole.RwRev(),
						Derive(func(b *Argument) {
							b.Cases(b.TermAs[Bool]("F ∩ X = ∅"))
							b.When(
								"X misses F: the product runs over all of F, and the forest's term stays",
								func(c *Argument, misses Fact) {
									c.Show(
										"the forest's term is there on both sides",
										ByArith(allOfF, misses, positive))
								})
							b.Otherwise(
								"X meets F: the product over F ∖ X is not over all of F, and only the route factors remain",
								func(c *Argument, meets Fact) {
									c.Show(
										"the forest's term is on neither side",
										ByArith(allOfF, meets, positive))
								})
						}))))
		})
	}),
})}
