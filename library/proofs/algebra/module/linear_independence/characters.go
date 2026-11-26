// characters.go — independence of characters: distinct multiplicative maps
// from a set closed under a product, with values in an integral domain, are
// independent over the domain. The maps are read through an index, so a
// client's own type of maps serves, and the product need not associate.

package linear_independence

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_domain"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// CharactersIndependent — distinct multiplicative maps into an integral
// domain are independent over it: a combination of finitely many of them
// with coefficients in the domain that vanishes at every point of G has
// every coefficient zero. By induction on the finite set: adding σ to s, the
// combination twisted at y ∈ G — d(r) (χ(r, y) − χ(σ, y)) in place of d(r) —
// vanishes too and has no σ-term, so it is a combination over s, and by
// induction each twisted coefficient is zero; a member r of s differs from σ
// at some y, so d(r) is zero; what is left is d(σ) χ(σ, e), zero at e, where
// χ(σ, e) is one.
var CharactersIndependent = charactersIndependentThm{family.Add(registry.ProofEntry{
	Name: "CharactersIndependent",
	Key:  "prop_42f3801a9a5c5763",
	Reading: "The maps are indexed, so two members of H could name one " +
		"map: the separation hypothesis asks them to differ on G. Nothing " +
		"asks op to associate, only that G hold e and be closed under it.",
	Build: family.Theorem(Statement{
		Binders: "∀R:integral_domain_on(A). " +
			"∀op:(B → B → B). " +
			"∀e:B. " +
			"∀G:set(B). " +
			"∀H:set(C). " +
			"∀χ:(C → B → A). " +
			"∀c:(C → A). " +
			"∀p:C.",
		Hypotheses: []string{
			"e ∈ G",
			"∀x y:B. x ∈ G ∧ y ∈ G ⇒ op(x, y) ∈ G",
			"finite(H)",
			"∀q:C. " +
				"    q ∈ H ⇒ " +
				"    χ(q, e) = R.one ∧ " +
				"    (∀x:B. x ∈ G ⇒ χ(q, x) ∈ R.carrier) ∧ " +
				"    (∀x y:B. x ∈ G ∧ y ∈ G ⇒ χ(q, op(x, y)) = χ(q, x) * χ(q, y))",
			"∀q r:C. q ∈ H ∧ r ∈ H ∧ q ≠ r ⇒ ∃x:B. x ∈ G ∧ χ(q, x) ≠ χ(r, x)",
			"∀q:C. q ∈ H ⇒ c(q) ∈ R.carrier",
			"∀x:B. x ∈ G ⇒ module_sum(R.add, R.zero, H, λq:C. c(q) * χ(q, x)) = R.zero",
			"p ∈ H",
		},
		Conclusion: "c(p) = R.zero",
	},
		func(
			a *Argument,
			R integral_domain.IntegralDomainFact[on.R],
			_ *Arrow2[B, B, B],
			e *Expr[B],
			_ *Expr[Set[B]],
			H *Expr[Set[C]],
			_ *Arrow2[C, B, A],
			_ *Arrow[C, A],
			h Fact,
		) {
			parts := a.Conjuncts(
				h,
				"G holds e",
				"G is closed under op",
				"H is finite",
				"the members of H are multiplicative on G, with values in R",
				"they differ on G",
				"the coefficients lie in R",
				"the combination vanishes on G")
			eIn, closed, finH, multiplicative, separated, coefficients, vanishes :=
				parts[0], parts[1], parts[2], parts[3], parts[4], parts[5], parts[6]
			ring := integral_domain.Ring.Read(R)
			regular := module.RegularModuleOn.Read(ring)

			twist := a.Have(
				"a combination vanishing on G still vanishes with "+
					"each coefficient d(r) twisted to d(r) (χ(r, y) − z)",
				Statement{
					Binders: "∀s:set(C). ∀d:(C → A). ∀y:B. ∀z:A.",
					Hypotheses: []string{
						"finite(s)",
						"s ⊆ H",
						"∀q:C. q ∈ s ⇒ d(q) ∈ R.carrier",
						"y ∈ G",
						"z ∈ R.carrier",
						"∀x:B. x ∈ G ⇒ module_sum(R.add, R.zero, s, λr:C. d(r) * χ(r, x)) = R.zero",
					},
					Conclusion: "∀x:B. " +
						"    x ∈ G ⇒ module_sum(R.add, R.zero, s, λr:C. d(r) * (χ(r, y) - z) * χ(r, x)) = R.zero",
				},
				Derive(func(b *Argument) {
					s := b.FixAs[Set[C]]("s")
					b.FixAs[Fun[C, A]]("d")
					b.FixAs[B]("y")
					b.FixAs[A]("z")
					given := b.Conjuncts(
						b.Assume(),
						"s is finite",
						"s lies in H",
						"the coefficients lie in R",
						"y lies in G",
						"z lies in R",
						"the combination over s vanishes on G")
					finS, sInH, coefficientsS, yIn, zIn, vanishesS :=
						given[0], given[1], given[2], given[3], given[4], given[5]
					x := b.FixAs[B]("x")
					xIn := b.Assume()
					yx := b.TermAs[B]("op(y, x)")
					yxIn := b.Have(
						"op(y, x) lies in G",
						"op(y, x) ∈ G",
						By(closed, yIn, xIn))
					termwise := b.Have(
						"termwise, d(r) (χ(r, y) − z) χ(r, x) = d(r) χ(r, op(y, x)) + (−z) (d(r) χ(r, x)), each term in R",
						Statement{
							Binders: "∀r:C.",
							Hypotheses: []string{
								"r ∈ s",
							},
							Conclusion: "d(r) * (χ(r, y) - z) * χ(r, x) = d(r) * χ(r, op(y, x)) + -z * (d(r) * χ(r, x)) ∧ " +
								"d(r) * χ(r, op(y, x)) ∈ R.carrier ∧ " +
								"-z * (d(r) * χ(r, x)) ∈ R.carrier ∧ " +
								"d(r) * χ(r, x) ∈ R.carrier",
						},
						Derive(func(f *Argument) {
							f.FixAs[C]("r")
							rIn := f.Assume()
							member := f.Have(
								"r is a member of H",
								"r ∈ H",
								BySets(rIn, sInH))
							laws := f.Have(
								"so its values at x, y and op(y, x) lie in R, and it keeps the product",
								"χ(r, x) ∈ R.carrier ∧ "+
									"χ(r, y) ∈ R.carrier ∧ "+
									"χ(r, op(y, x)) ∈ R.carrier ∧ "+
									"χ(r, op(y, x)) = χ(r, y) * χ(r, x)",
								By(member, multiplicative, xIn, yIn, yxIn))
							values := f.Have(
								"so d(r) and these values lie in R",
								"d(r) ∈ R.carrier ∧ χ(r, x) ∈ R.carrier ∧ χ(r, y) ∈ R.carrier ∧ χ(r, op(y, x)) ∈ R.carrier",
								By(coefficientsS, rIn, laws))
							expanded := f.Have(
								"multiplied out, a ring identity",
								"d(r) * (χ(r, y) - z) * χ(r, x) = d(r) * (χ(r, y) * χ(r, x)) + -z * (d(r) * χ(r, x))",
								ByArith(ring, values, zIn))
							f.Show(
								"χ(r, op(y, x)) = χ(r, y) χ(r, x) turns it into the "+
									"split, and R is closed under products and negatives",
								By(expanded, laws, values, zIn, comm_ring.MulIn.Read(ring), comm_ring.NegIn.Read(ring)))
						}))
					atYX := b.TermAs[Fun[C, A]]("λr:C. d(r) * χ(r, op(y, x))")
					scaledAtX := b.TermAs[Fun[C, A]]("λr:C. -z * (d(r) * χ(r, x))")
					atX := b.TermAs[Fun[C, A]]("λr:C. d(r) * χ(r, x)")
					b.Show(
						"the twisted combination is the combination at "+
							"op(y, x) minus z times the one at x, and both vanish",
						CalcEq(
							Leg(
								b.TermAs[A]("module_sum(R.add, R.zero, s, λr:C. d(r) * χ(r, op(y, x)) + -z * (d(r) * χ(r, x)))"),
								"split each term",
								By(termwise, module.ModuleSumCongruence)),
							Leg(
								b.TermAs[A](
									"module_sum(R.add, R.zero, s, λr:C. d(r) * χ(r, op(y, x))) + "+
										"module_sum(R.add, R.zero, s, λr:C. -z * (d(r) * χ(r, x)))"),
								"a sum of two families is the sum of their sums",
								By(finS, termwise, module.ModuleSumAdd.Read(regular).At(s, atYX, scaledAtX))),
							Leg(
								b.TermAs[A](
									"module_sum(R.add, R.zero, s, λr:C. d(r) * χ(r, op(y, x))) + "+
										"-z * module_sum(R.add, R.zero, s, λr:C. d(r) * χ(r, x))"),
								"the scalar −z comes out of the second sum",
								By(
									finS,
									termwise,
									zIn,
									comm_ring.NegIn.Read(ring),
									module.ModuleSumSmul.Read(regular).AsFact().At(s, b.TermAs[A]("-z"), atX))),
							Leg(
								b.TermAs[A]("R.zero + -z * R.zero"),
								"the combination vanishes at op(y, x) and at x",
								By(vanishesS.At(yx), vanishesS.At(x), yxIn, xIn)),
							FinalLeg(
								"zero + (−z) zero is zero",
								ByArith(ring, zIn)),
						))
				}))
			independence := a.Have(
				"finitely many members of H are independent over R: induction on the finite set s",
				"∀s:set(C). "+
					"    finite(s) ⇒ "+
					"    ∀d:(C → A). "+
					"        s ⊆ H ∧ "+
					"        (∀q:C. q ∈ s ⇒ d(q) ∈ R.carrier) ∧ "+
					"        (∀x:B. x ∈ G ⇒ module_sum(R.add, R.zero, s, λr:C. d(r) * χ(r, x)) = R.zero) ⇒ "+
					"        ∀p:C. p ∈ s ⇒ d(p) = R.zero",
				ByInduction(finite_set.FiniteInductFresh,
					Case(
						"the empty set has no member to carry a coefficient",
						By(set_basic.NotInEmpty.Inst[C]())),
					Case(
						"adding σ to s: the twisted combination drops σ, the "+
							"claim for s clears the rest, and d(σ) vanishes at e",
						Derive(func(b *Argument) {
							σ := b.FixAs[C]("σ")
							s := b.FixAs[Set[C]]("s")
							carried := b.Conjuncts(
								b.Assume(),
								"the claim for s",
								"σ is not in s",
								"s is finite")
							claimS, fresh, finS := carried[0], carried[1], carried[2]
							d := b.FixAs[Fun[C, A]]("d")
							given := b.Conjuncts(
								b.Assume(),
								"σ and the members of s lie in H",
								"the coefficients lie in R",
								"the combination over insert(σ, s) vanishes on G")
							inHIns, coefficientsIns, vanishesIns := given[0], given[1], given[2]
							withσ := b.TermAs[Set[C]]("insert(σ, s)")
							sInH := b.Have(
								"the members of s lie in H",
								"s ⊆ H",
								BySets(inHIns))
							finIns := b.Have(
								"insert(σ, s) is finite, and holds s",
								"finite(insert(σ, s)) ∧ s ⊆ insert(σ, s)",
								BySets(finS, finite_set.FiniteInsert.At(σ, s)))
							members := b.Have(
								"σ and the members of s lie in insert(σ, s)",
								"σ ∈ insert(σ, s) ∧ (∀r:C. r ∈ s ⇒ r ∈ insert(σ, s))",
								BySets())
							inH := b.Have(
								"every member of insert(σ, s) lies in H",
								"∀r:C. r ∈ insert(σ, s) ⇒ r ∈ H",
								BySets(inHIns))
							values := b.Have(
								"their coefficients, and their values on G, lie in R",
								"∀r:C. ∀v:B. r ∈ insert(σ, s) ∧ v ∈ G ⇒ d(r) ∈ R.carrier ∧ χ(r, v) ∈ R.carrier",
								By(coefficientsIns, inH, multiplicative))
							terms := b.Have(
								"and so do the terms d(r) χ(r, v)",
								"∀r:C. ∀v:B. r ∈ insert(σ, s) ∧ v ∈ G ⇒ d(r) * χ(r, v) ∈ R.carrier",
								By(values, comm_ring.MulIn.Read(ring)))

							shortened := b.Have(
								"twisted at y ∈ G by χ(σ, y), the combination loses "+
									"its σ-term: a combination over s vanishing on G",
								"∀y:B. "+
									"    y ∈ G ⇒ "+
									"    ∀u:B. "+
									"        u ∈ G ⇒ module_sum(R.add, R.zero, s, λr:C. d(r) * (χ(r, y) - χ(σ, y)) * χ(r, u)) = R.zero",
								Derive(func(f *Argument) {
									y := f.FixAs[B]("y")
									yIn := f.Assume()
									σy := f.TermAs[A]("χ(σ, y)")
									σyIn := f.Have(
										"χ(σ, y) lies in R",
										"χ(σ, y) ∈ R.carrier",
										By(values.At(σ, y), members, yIn))
									overInsert := f.Have(
										"over insert(σ, s) the twisted combination vanishes",
										Statement{
											Binders: "∀u:B.",
											Hypotheses: []string{
												"u ∈ G",
											},
											Conclusion: "module_sum(R.add, " +
												"    R.zero, " +
												"    insert(σ, s), " +
												"    λr:C. d(r) * (χ(r, y) - χ(σ, y)) * χ(r, u)) = " +
												"R.zero",
										},
										By(twist.At(withσ, d, y, σy), finIns, inHIns, coefficientsIns, yIn, σyIn, vanishesIns))
									u := f.FixAs[B]("u")
									uIn := f.Assume()
									twisted := f.TermAs[Fun[C, A]]("λr:C. d(r) * (χ(r, y) - χ(σ, y)) * χ(r, u)")
									twistedIn := f.Have(
										"each twisted term lies in R",
										"∀r:C. r ∈ insert(σ, s) ⇒ d(r) * (χ(r, y) - χ(σ, y)) * χ(r, u) ∈ R.carrier",
										By(values, σyIn, yIn, uIn, comm_ring.MulIn.Read(ring), comm_ring.SubIn.Read(ring)))
									σValues := f.Have(
										"d(σ) and χ(σ, u) lie in R",
										"d(σ) ∈ R.carrier ∧ χ(σ, u) ∈ R.carrier",
										By(values.At(σ, u), members, uIn))
									σTerm := f.Have(
										"the σ-term is d(σ) (χ(σ, y) − χ(σ, y)) χ(σ, u) = zero",
										"d(σ) * (χ(σ, y) - χ(σ, y)) * χ(σ, u) = R.zero",
										ByArith(ring, σValues, σyIn))
									offS := f.Have(
										"so the twisted terms vanish off s",
										"∀r:C. r ∈ insert(σ, s) ∧ r ∉ s ⇒ d(r) * (χ(r, y) - χ(σ, y)) * χ(r, u) = R.zero",
										By(Normalized, σTerm, At(set_basic.InInsert.Inst[C](), s, σ)))
									f.Show(
										"the sum over s is the sum over insert(σ, s), which vanishes",
										CalcEq(
											Leg(
												f.TermAs[A]("module_sum(R.add, R.zero, insert(σ, s), λr:C. d(r) * (χ(r, y) - χ(σ, y)) * χ(r, u))"),
												"the terms off s vanish",
												By(finIns, members, twistedIn, offS, module.ModuleSumSupport.Read(regular).At(withσ, s, twisted))),
											FinalLeg(
												"the twisted combination over insert(σ, s) vanishes at u",
												By(overInsert.At(u), uIn)),
										))
								}))

							twistedZero := b.Have(
								"by the claim for s, each twisted coefficient d(r) (χ(r, y) − χ(σ, y)) on s is zero",
								"∀y:B. y ∈ G ⇒ ∀r:C. r ∈ s ⇒ d(r) * (χ(r, y) - χ(σ, y)) = R.zero",
								Derive(func(f *Argument) {
									y := f.FixAs[B]("y")
									yIn := f.Assume()
									coefficientsIn := f.Have(
										"the twisted coefficients on s lie in R",
										"∀q:C. q ∈ s ⇒ d(q) * (χ(q, y) - χ(σ, y)) ∈ R.carrier",
										Derive(func(g *Argument) {
											q := g.FixAs[C]("q")
											qIn := g.Assume()
											qσ := g.Have(
												"q and σ lie in insert(σ, s)",
												"q ∈ insert(σ, s) ∧ σ ∈ insert(σ, s)",
												By(members, qIn))
											g.Show(
												"d(q), χ(q, y) and χ(σ, y) lie in R, which is closed under differences and products",
												By(
													values.At(q, y),
													values.At(σ, y),
													yIn,
													qσ,
													comm_ring.MulIn.Read(ring).AsFact().At(g.TermAs[A]("d(q)"), g.TermAs[A]("χ(q, y) - χ(σ, y)")),
													comm_ring.SubIn.Read(ring).AsFact().At(g.TermAs[A]("χ(q, y)"), g.TermAs[A]("χ(σ, y)"))))
										}))
									f.Show(
										"the claim for s at the twisted coefficients",
										By(
											claimS.At(f.TermAs[Fun[C, A]]("λr:C. d(r) * (χ(r, y) - χ(σ, y))")),
											sInH,
											coefficientsIn,
											shortened.At(y),
											yIn))
								}))

							onS := b.Have(
								"every coefficient on s is zero: a member of s differs from σ somewhere on G",
								"∀r:C. r ∈ s ⇒ d(r) = R.zero",
								Derive(func(f *Argument) {
									r := f.FixAs[C]("r")
									rIn := f.Assume()
									distinct := f.Have(
										"r and σ are distinct members of H, σ not being in s",
										"r ∈ insert(σ, s) ∧ r ∈ H ∧ σ ∈ H ∧ r ≠ σ",
										By(Normalized, rIn, fresh, members, inH))
									y, differ := f.ObtainAs[B](
										"so they differ at some y ∈ G",
										"∃y:B. y ∈ G ∧ χ(r, y) ≠ χ(σ, y)",
										By(distinct, separated))
									ry, σy := f.TermAs[A]("χ(r, y)"), f.TermAs[A]("χ(σ, y)")
									product := f.Have(
										"the twisted coefficient at y is zero",
										"d(r) * (χ(r, y) - χ(σ, y)) = R.zero",
										By(twistedZero.At(y), differ, rIn))
									vals := f.Have(
										"d(r), χ(r, y) and χ(σ, y) lie in R",
										"d(r) ∈ R.carrier ∧ χ(r, y) ∈ R.carrier ∧ χ(σ, y) ∈ R.carrier",
										By(values.At(r, y), values.At(σ, y), distinct, members, differ))
									nonzero := f.SupposeNot()
									difference := f.Have(
										"then χ(r, y) − χ(σ, y) is zero, R having no zero divisors",
										"χ(r, y) - χ(σ, y) = R.zero",
										By(
											nonzero,
											product,
											vals,
											integral_domain.NoZeroDivisors.Read(R).AsFact().At(
												f.TermAs[A]("d(r)"), f.TermAs[A]("χ(r, y) - χ(σ, y)")),
											comm_ring.SubIn.Read(ring).AsFact().At(ry, σy)))
									same := f.Have(
										"that is, χ(r, y) = χ(σ, y)",
										"χ(r, y) = χ(σ, y)",
										ByArith(ring, difference, vals))
									f.Show(
										"against the choice of y",
										By(same, differ))
								}))

							σIn := b.Have(
								"σ lies in H",
								"σ ∈ H",
								By(members, inH))
							σOne := b.Have(
								"so χ(σ, e) = one",
								"χ(σ, e) = R.one",
								By(σIn, multiplicative))
							σValues := b.Have(
								"d(σ) and χ(σ, e) lie in R",
								"d(σ) ∈ R.carrier ∧ χ(σ, e) ∈ R.carrier",
								By(values.At(σ, e), members, eIn))
							restAtE := b.Have(
								"at e, the terms over s are zero",
								"∀r:C. r ∈ s ⇒ d(r) * χ(r, e) = R.zero",
								Derive(func(f *Argument) {
									r := f.FixAs[C]("r")
									rIn := f.Assume()
									f.Show(
										"d(r) = zero and χ(r, e) lies in R",
										By(Normalized, onS.At(r), rIn, values.At(r, e), members, eIn, comm_ring.MulLeftZeroOn.Read(ring)))
								}))
							atE := b.TermAs[Fun[C, A]]("λr:C. d(r) * χ(r, e)")
							restSum := b.Have(
								"so their sum is zero",
								"module_sum(R.add, R.zero, s, λr:C. d(r) * χ(r, e)) = R.zero",
								By(finS, restAtE, module.ModuleSumZero.Read(regular).At(s, atE)))
							σZero := b.Have(
								"what is left at e is d(σ) χ(σ, e) = d(σ), so d(σ) = zero",
								"d(σ) = R.zero",
								CalcEq(
									Leg(
										b.TermAs[A]("d(σ) * χ(σ, e) + R.zero"),
										"χ(σ, e) = one",
										ByArith(ring, Scaled(b.TermAs[A]("d(σ)"), σOne), σValues)),
									Leg(
										b.TermAs[A]("d(σ) * χ(σ, e) + module_sum(R.add, R.zero, s, λr:C. d(r) * χ(r, e))"),
										"the terms over s vanish at e",
										By(restSum)),
									Leg(
										b.TermAs[A]("module_sum(R.add, R.zero, insert(σ, s), λr:C. d(r) * χ(r, e))"),
										"σ is new to s",
										By(finS, fresh, terms, members, eIn, module.ModuleSumInsert.Read(regular).At(s, σ, atE))),
									FinalLeg(
										"the combination vanishes at e",
										By(vanishesIns.At(e), eIn)),
								))
							b.Show(
								"every coefficient on insert(σ, s) is zero",
								BySets(onS, σZero))
						}))))

			a.Show(
				"the independence of the finitely many members of H",
				By(independence.At(H), finH, set_order.SubsetRefl.At(H), coefficients, vanishes))
		}),
})}
