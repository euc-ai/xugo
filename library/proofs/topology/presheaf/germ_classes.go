package presheaf

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/relations/equivalence"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// GermEquivalence — germ membership is an equivalence relation on the
// section representatives at a point: each representative lies in its own
// germ, agreement is symmetric, and nearby agreements compose.
var GermEquivalence = germEquivalenceThm{family.Add(registry.ProofEntry{
	Name: "GermEquivalence",
	Key:  "prop_d1247fc5c31c472d",
	Build: Presheaf.Law("∀x:A. "+
		"    equivalence_on({p:prod(set(A), B) | fst(p) ∈ T ∧ x ∈ fst(p) ∧ snd(p) ∈ F(fst(p))}, "+
		"        λp:prod(set(A), B). λq:prod(set(A), B). q ∈ sheaf_germ(x, fst(p), snd(p)))",
		func(a *Argument, presheaf PresheafFact[on.T], x *Expr[A]) {
			T := a.TermAs[Set[Set[A]]]("T")
			F := a.TermAs[Fun[Set[A], Set[B]]]("F")
			res := a.TermAs[Fun3[Set[A], Set[A], B, B]]("res")
			a.Do(Unfold(equivalence.EquivalenceOn), SplitConjAll(
				Case(
					"every lawful representative lies in its own germ",
					BySets(GermOwn.Read(presheaf), pairs.PairEta)),
				Case(
					"agreement on one neighbourhood is symmetric",
					Derive(func(b *Argument) {
						p := b.FixAs[Prod[Set[A], B]]("p")
						q := b.FixAs[Prod[Set[A], B]]("q")
						members := b.Assume()
						related := b.Assume()
						U, V := b.TermAs[Set[A]]("fst(p)"), b.TermAs[Set[A]]("fst(q)")
						s, t := b.TermAs[B]("snd(p)"), b.TermAs[B]("snd(q)")
						agreement := b.Have(
							"the representatives agree near x",
							"∃N:set(A). N ∈ T ∧ x ∈ N ∧ N ⊆ fst(p) ∩ fst(q) ∧ res(fst(p), N, snd(p)) = res(fst(q), N, snd(q))",
							By(related, InGerm.At(T, F, res, x, U, V, s, t), pairs.PairEta.At(q)))
						reverse := b.Have(
							"the same neighbourhood witnesses the reversed agreement",
							"∃N:set(A). N ∈ T ∧ x ∈ N ∧ N ⊆ fst(q) ∩ fst(p) ∧ res(fst(q), N, snd(q)) = res(fst(p), N, snd(p))",
							BySets(agreement))
						b.Show(
							"p belongs to the germ represented by q",
							BySets(reverse, members, InGerm.At(T, F, res, x, V, U, t, s), pairs.PairEta.At(p)))
					})),
				Case(
					"two nearby agreements compose",
					Derive(func(b *Argument) {
						b.FixAs[Prod[Set[A], B]]("p")
						q := b.FixAs[Prod[Set[A], B]]("q")
						r := b.FixAs[Prod[Set[A], B]]("r")
						members := b.Assume()
						related := b.Assume()
						U, V, W := b.TermAs[Set[A]]("fst(p)"), b.TermAs[Set[A]]("fst(q)"), b.TermAs[Set[A]]("fst(r)")
						u, v, w := b.TermAs[B]("snd(p)"), b.TermAs[B]("snd(q)"), b.TermAs[B]("snd(r)")
						sections := b.Have(
							"the three representatives carry sections on open sets",
							"fst(p) ∈ T ∧ "+
								"fst(q) ∈ T ∧ "+
								"fst(r) ∈ T ∧ "+
								"snd(p) ∈ F(fst(p)) ∧ "+
								"snd(q) ∈ F(fst(q)) ∧ "+
								"snd(r) ∈ F(fst(r))",
							BySets(members))
						first := b.Have(
							"p and q agree near x",
							"∃N:set(A). N ∈ T ∧ x ∈ N ∧ N ⊆ fst(p) ∩ fst(q) ∧ res(fst(p), N, snd(p)) = res(fst(q), N, snd(q))",
							By(related, InGerm.At(T, F, res, x, U, V, u, v), pairs.PairEta.At(q)))
						second := b.Have(
							"q and r agree near x",
							"∃N:set(A). N ∈ T ∧ x ∈ N ∧ N ⊆ fst(q) ∩ fst(r) ∧ res(fst(q), N, snd(q)) = res(fst(r), N, snd(r))",
							By(related, InGerm.At(T, F, res, x, V, W, v, w), pairs.PairEta.At(r)))
						composed := b.Have(
							"p and r agree after restricting both agreements",
							"∃N:set(A). N ∈ T ∧ x ∈ N ∧ N ⊆ fst(p) ∩ fst(r) ∧ res(fst(p), N, snd(p)) = res(fst(r), N, snd(r))",
							By(first, second, sections, AgreeNearTrans.Read(presheaf).AsFact().At(x, U, V, W, u, v, w)))
						b.Show(
							"r belongs to the germ represented by p",
							BySets(composed, members, InGerm.At(T, F, res, x, U, W, u, w), pairs.PairEta.At(r)))
					})),
			))
		}),
})}

// GermClass — the germ of a lawful representative is its class inside the
// section representatives at the point: germ membership already supplies
// the carrier conditions of every other representative.
var GermClass = germClassThm{family.Add(registry.ProofEntry{
	Name: "GermClass",
	Key:  "prop_396dbabb42e2a113",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). " +
			"∀F:(set(A) → set(B)). " +
			"∀res:(set(A) → set(A) → B → B). " +
			"∀x:A. " +
			"∀U:set(A). " +
			"∀s:B.",
		Hypotheses: []string{
			"U ∈ T",
			"s ∈ F(U)",
		},
		Conclusion: "sheaf_germ(T, F, res, x, U, s) = " +
			"equivalence_class(relation_on( " +
			"        {p:prod(set(A), B) | fst(p) ∈ T ∧ x ∈ fst(p) ∧ snd(p) ∈ F(fst(p))}, " +
			"        λp:prod(set(A), B). λq:prod(set(A), B). q ∈ sheaf_germ(T, F, res, x, fst(p), snd(p))), " +
			"    (U, s))",
	},
		func(
			a *Argument,
			T *Expr[Set[Set[A]]],
			F *Arrow[Set[A], Set[B]],
			res *Expr[Fun3[Set[A], Set[A], B, B]],
			x *Expr[A],
			U *Expr[Set[A]],
			s *Expr[B],
			lawful Fact,
		) {
			a.Show(
				"the germ and the class have the same representatives",
				Simp(Fwd(set_basic.Extension), Fwd(equivalence.InClassOn), Fwd(pairs.Fst), Fwd(pairs.Snd)),
				Derive(func(b *Argument) {
					p := b.FixAs[Prod[Set[A], B]]("p")
					b.Show(
						"a member of the germ already belongs to the carrier",
						BySets(
							lawful,
							InGerm.At(T, F, res, x, U, b.TermAs[Set[A]]("fst(p)"), s, b.TermAs[B]("snd(p)")),
							pairs.PairEta.At(p),
							pairs.Fst,
							pairs.Snd))
				}))
		}),
})}

// StalkQuotient — the stalk is the quotient of lawful section
// representatives by germ membership: a section supplies a pair, and a
// pair's projections recover the same germ.
var StalkQuotient = stalkQuotientThm{family.Add(registry.ProofEntry{
	Name: "StalkQuotient",
	Key:  "prop_f032005dedd30e34",
	Build: family.Theorem("∀T:set(set(A)). "+
		"∀F:(set(A) → set(B)). "+
		"∀res:(set(A) → set(A) → B → B). "+
		"∀x:A. "+
		"    stalk(T, F, res, x) = "+
		"    quotient_on({p:prod(set(A), B) | fst(p) ∈ T ∧ x ∈ fst(p) ∧ snd(p) ∈ F(fst(p))}, "+
		"        λp:prod(set(A), B). λq:prod(set(A), B). q ∈ sheaf_germ(T, F, res, x, fst(p), snd(p)))",
		func(
			a *Argument,
			T *Expr[Set[Set[A]]],
			F *Arrow[Set[A], Set[B]],
			res *Expr[Fun3[Set[A], Set[A], B, B]],
			x *Expr[A],
		) {
			a.Show(
				"the stalk and quotient contain the same germs",
				Simp(Fwd(set_basic.Extension)),
				Derive(func(b *Argument) {
					b.FixAs[Set[Prod[Set[A], B]]]("g")
					b.Do(Simp(Fwd(InStalk), Fwd(equivalence.InQuotientOn)))
					b.Iff()
					b.Forward(
						"a section representative supplies a quotient representative",
						func(c *Argument, represented Fact) {
							U, s, lawful := c.Unpack2As[Set[A], B](represented, "U", "s")
							c.Take(c.TermAs[Prod[Set[A], B]]("(U, s)"))
							c.Show(
								"the pair is lawful and has the required class",
								SplitConj(
									Case(
										"the germ is the class of its representative",
										By(lawful, GermClass.At(T, F, res, x, U, s))),
									Case(
										"the pair carries the given section",
										BySets(lawful, pairs.Fst.At(U, s), pairs.Snd.At(U, s))),
								))
						})
					b.Backward(
						"the projections of a quotient representative supply a section",
						func(c *Argument, represented Fact) {
							p, member := c.UnpackAs[Prod[Set[A], B]](represented, "p")
							U, s := c.TermAs[Set[A]]("fst(p)"), c.TermAs[B]("snd(p)")
							c.Take(U)
							c.Take(s)
							lawful := c.Have(
								"the pair carries a section on a neighbourhood of x",
								"fst(p) ∈ T ∧ x ∈ fst(p) ∧ snd(p) ∈ F(fst(p))",
								BySets(member))
							c.Show(
								"the projected section represents the given class",
								By(member, lawful, GermClass.At(T, F, res, x, U, s), pairs.PairEta.At(p)))
						})
				}))
		}),
})}
