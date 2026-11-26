// nakayama.go — Nakayama's lemma for ideals: an ideal that finitely many
// of its members generate modulo J, and that J and I·N cover, is carried
// into J by a member of the ring congruent to one modulo I.

package local_ring

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/quotient_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_ideal"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// Nakayama — Nakayama's lemma: an ideal N that a finite part G of it
// spans modulo an ideal J, and that J and I·N together cover, is carried
// into J by some s congruent to one modulo I. By induction on G. With no
// generators N lies in J, and s = 1. A further generator x is a member of
// H = J + R·x, so the generators before it span N modulo H and give b ≡ 1
// with b·N ⊆ H; then b carries I·N into L = J + I·x, the multiples of x by I
// added to J, and x = j₀ + w with j₀ in J and w in I·N has b·x = b·j₀ + j₁ +
// c·x with j₁ in J and c in I. So (b − c)·x lies in J, and s = (b − c)·b
// carries N into J.
var Nakayama = nakayamaThm{family.Add(registry.ProofEntry{
	Name: "Nakayama",
	Key:  "prop_cef0b4ad6ebe1386",
	Reading: "G ⊆ N is load-bearing: without it G = {one} would empty the first covering, " +
		"and N = I·N alone gives no s — the maximal ideal of a valuation ring with value group " +
		"ℚ is its own square and no unit kills it. At J = {zero} it is the familiar form, s·N " +
		"= zero for a finitely generated N = I·N; at I = R.carrier it says nothing, s = zero.",
	Build: family.Theorem(Statement{
		Binders: "∀R:comm_ring_on(A). ∀I N G J:set(A).",
		Hypotheses: []string{
			"ring_ideal(R, I)",
			"ring_ideal(R, N)",
			"finite(G)",
			"G ⊆ N",
			"ring_ideal(R, J)",
			"N ⊆ set_mul(R.add, ideal_span(R, G), J)",
			"N ⊆ set_mul(R.add, J, ideal_mul(R, I, N))",
		},
		Conclusion: "∃s:A. s ∈ R.carrier ∧ s - R.one ∈ I ∧ (∀z:A. z ∈ N ⇒ s * z ∈ J)",
		Abbrev: Abbrev{
			{Name: "carriedInto", Text: "λT:set(A). ∀Q:set(A). " +
				"    ring_ideal(R, Q) ∧ " +
				"    N ⊆ set_mul(R.add, ideal_span(R, T), Q) ∧ " +
				"    N ⊆ set_mul(R.add, Q, ideal_mul(R, I, N)) ⇒ " +
				"    ∃s:A. s ∈ R.carrier ∧ s - R.one ∈ I ∧ (∀z:A. z ∈ N ⇒ s * z ∈ Q)"},
		},
	}, func(a *Argument, R comm_ring.CommRingFact[on.R], I, N, G, J *Expr[Set[A]], h Fact) {
		given := a.Conjuncts(
			h,
			"I is an ideal",
			"N is an ideal",
			"G is finite",
			"G lies in N",
			"J is an ideal",
			"G spans N modulo J",
			"N lies in J plus I·N")
		idealI, idealN, finiteG, generatorsInN := given[0], given[1], given[2], given[3]
		r := a.TermAs[RingOps[A]]("R")
		NInRing := a.Have(
			"N lies in the ring",
			"N ⊆ R.carrier",
			By(idealN, ring_ideal.IdealSubset.At(r, N)))
		IInRing := a.Have(
			"so does I",
			"I ⊆ R.carrier",
			By(idealI, ring_ideal.IdealSubset.At(r, I)))
		members := a.Have(
			"every generator lies in N",
			"∀y:A. y ∈ G ⇒ y ∈ N",
			BySets(generatorsInN))
		everyIdeal := a.Have(
			"by induction on the finite set G of generators, for every ideal Q modulo which G spans N",
			"«carriedInto»(G)",
			ByInduction(finite_set.FiniteInductFreshOn, finiteG, members,
				Case(
					"with no generators N lies in Q, and s = 1 carries it there",
					Derive(func(b *Argument) {
						Q := b.FixAs[Set[A]]("Q")
						assumed := b.Conjuncts(
							b.Assume(),
							"Q is an ideal",
							"N lies in the span of ∅ plus Q",
							"N lies in Q plus I·N")
						idealQ, cover := assumed[0], assumed[1]
						empty := b.TermAs[Set[A]]("∅")
						spanInQ := b.Have(
							"the span of ∅ lies in Q",
							"ideal_span(R, ∅) ⊆ Q",
							By(idealQ, set_order.EmptySubset.At(Q), ring_ideal.SpanLeast.At(r, empty, Q)))
						inQ := b.Have(
							"so N lies in Q",
							"∀z:A. z ∈ N ⇒ z ∈ Q",
							Derive(func(c *Argument) {
								c.FixAs[A]("z")
								zIn := c.Assume()
								sum := c.Have(
									"z is a member of the span of ∅ plus a member of Q",
									"z ∈ set_mul(R.add, ideal_span(R, ∅), Q)",
									BySets(cover, zIn))
								y, j, parts := c.Unpack2As[A, A](c.Unfolded(sum, quotient_group.SetMulDef), "y", "j")
								split := c.Conjuncts(
									parts,
									"y lies in the span of ∅",
									"j lies in Q",
									"z is their sum")
								yInQ := c.Have(
									"y lies in Q",
									"y ∈ Q",
									BySets(split[0], spanInQ))
								c.Show(
									"and z, a sum of two members of Q, lies in Q",
									By(Normalized, split[2], yInQ, split[1], idealQ, ring_ideal.IdealAdd.At(r, Q, y, j)))
							}))
						one := b.TermAs[A]("R.one")
						cancel := b.Have(
							"one minus one is zero",
							"R.one - R.one = R.zero",
							ByArith(R))
						congruent := b.Have(
							"so one is one modulo I",
							"R.one - R.one ∈ I",
							By(Normalized, cancel, idealI, ring_ideal.IdealZero.At(r, I)))
						carried := b.Have(
							"and one carries N into Q",
							"∀z:A. z ∈ N ⇒ R.one * z ∈ Q",
							Derive(func(c *Argument) {
								z := c.FixAs[A]("z")
								zIn := c.Assume()
								c.Show(
									"Q absorbs the product of one with its member z",
									By(inQ.At(z), zIn, idealQ, comm_ring.OneIn.Read(R), ring_ideal.IdealMul.At(r, Q, one, z)))
							}))
						b.Take(one)
						b.Show(
							"one lies in the ring, is one modulo I and carries N into Q",
							By(comm_ring.OneIn.Read(R), congruent, carried))
					})),
				Case(
					"a further generator x is absorbed into Q by the generators before it",
					Derive(func(b *Argument) {
						x := b.FixAs[A]("x")
						t := b.FixAs[Set[A]]("t")
						carried := b.Conjuncts(
							b.Assume(),
							"the claim holds along t",
							"x is new to t",
							"t is finite",
							"x lies in N",
							"so does every member of t")
						ih, xInN, tInN := carried[0], carried[3], carried[4]
						Q := b.FixAs[Set[A]]("Q")
						assumed := b.Conjuncts(
							b.Assume(),
							"Q is an ideal",
							"N lies in the span of insert(x, t) plus Q",
							"N lies in Q plus I·N")
						idealQ, cover, absorb := assumed[0], assumed[1], assumed[2]
						xIn := b.Have(
							"x lies in the ring",
							"x ∈ R.carrier",
							BySets(xInN, NInRing))
						xm := b.MemberOf[on.R](x, xIn)
						tInRing := b.Have(
							"t lies in the ring",
							"t ⊆ R.carrier",
							BySets(tInN, NInRing))
						QInRing := b.Have(
							"Q lies in the ring",
							"Q ⊆ R.carrier",
							By(idealQ, ring_ideal.IdealSubset.At(r, Q)))
						H, HDef := b.LetAs[Set[A]]("H", "ideal_span(R, insert(x, Q))")
						above := b.Conjuncts(
							b.Have(
								"H, the ideal Q and x generate, is an ideal holding Q and x",
								"ring_ideal(R, H) ∧ Q ⊆ H ∧ x ∈ H",
								Simp(Fwd(HDef)),
								By(QInRing, xIn, ring_ideal.SpanInsertAbove.Read(R).At(Q, xm))),
							"H is an ideal",
							"Q lies in H",
							"x lies in H")
						idealH, QInH := above[0], above[1]
						HForm := b.Have(
							"H is Q plus the multiples of x",
							"H = {β * x + e | β:A, e:A | β ∈ R.carrier ∧ e ∈ Q}",
							Simp(Fwd(HDef)),
							By(idealQ, xIn, ring_ideal.SpanInsertIdeal.Read(R).At(Q, xm)))
						spanForm := b.Have(
							"the span of insert(x, t) is the multiples of x plus the span of t",
							"ideal_span(R, insert(x, t)) = {β * x + u | β:A, u:A | β ∈ R.carrier ∧ u ∈ ideal_span(R, t)}",
							By(tInRing, xIn, ring_ideal.SpanInsert.Read(R).At(t, xm)))
						spanT := b.TermAs[Set[A]]("ideal_span(R, t)")
						spanTInRing := b.Have(
							"the span of t lies in the ring",
							"ideal_span(R, t) ⊆ R.carrier",
							By(tInRing, ring_ideal.SpanIdeal.Read(R).At(t), ring_ideal.IdealSubset.At(r, spanT)))
						coverAlongT := b.Have(
							"N lies in the span of t plus H",
							"∀z:A. z ∈ N ⇒ z ∈ set_mul(R.add, ideal_span(R, t), H)",
							Derive(func(c *Argument) {
								c.FixAs[A]("z")
								zIn := c.Assume()
								sum := c.Have(
									"z is a member of the span of insert(x, t) plus a member of Q",
									"z ∈ set_mul(R.add, ideal_span(R, insert(x, t)), Q)",
									BySets(cover, zIn))
								_, _, parts := c.Unpack2As[A, A](c.Unfolded(sum, quotient_group.SetMulDef), "y", "j")
								split := c.Conjuncts(
									parts,
									"y lies in the span of insert(x, t)",
									"j lies in Q",
									"z is their sum")
								_, _, yForm := c.Obtain2As[A, A](
									"write y as β times x plus a member u of the span of t",
									"∃β u:A. β ∈ R.carrier ∧ u ∈ ideal_span(R, t) ∧ y = β * x + u",
									BySets(spanForm, split[0]))
								yParts := c.Conjuncts(
									yForm,
									"β lies in the ring",
									"u lies in the span of t",
									"y is β times x plus u")
								atoms := c.Have(
									"u and j lie in the ring",
									"u ∈ R.carrier ∧ j ∈ R.carrier",
									BySets(yParts[1], spanTInRing, split[1], QInRing))
								regroup := c.Have(
									"β times x plus u, plus j, regroups as u plus β times x plus j",
									"(β * x + u) + j = u + (β * x + j)",
									ByArith(R, yParts[0], xIn, atoms))
								inH := c.Have(
									"β times x plus j lies in H",
									"β * x + j ∈ H",
									BySets(HForm, yParts[0], split[1]))
								c.Do(Unfold(quotient_group.SetMulDef))
								c.Show(
									"so z is a member of the span of t plus one of H",
									By(split[2], yParts[2], regroup, yParts[1], inH))
							}))
						coverT := b.Have(
							"that is, N lies in the span of t plus H",
							"N ⊆ set_mul(R.add, ideal_span(R, t), H)",
							BySets(coverAlongT))
						absorbH := b.Have(
							"and, Q lying in H, in H plus I·N",
							"N ⊆ set_mul(R.add, H, ideal_mul(R, I, N))",
							Unfold(quotient_group.SetMulDef),
							BySets(b.Unfolded(absorb, quotient_group.SetMulDef), QInH))
						unit, unitFacts := b.UnpackAs[A](
							GroupPremises(idealH, coverT, absorbH, ih.At(H)),
							"b")
						unitParts := b.Conjuncts(
							unitFacts,
							"b lies in the ring",
							"b is one modulo I",
							"b carries N into H")
						bIn, bOne, bCarries := unitParts[0], unitParts[1], unitParts[2]
						bm := b.MemberOf[on.R](unit, bIn)
						xSum := b.Have(
							"x is a member of Q plus a member of I·N",
							"x ∈ set_mul(R.add, Q, ideal_mul(R, I, N))",
							BySets(absorb, xInN))
						j0, _, xParts := b.Unpack2As[A, A](b.Unfolded(xSum, quotient_group.SetMulDef), "j₀", "w")
						xSplit := b.Conjuncts(
							xParts,
							"j₀ lies in Q",
							"w lies in I·N",
							"x is their sum")
						L, LDef := b.LetAs[Set[A]]("L", "{e + c * x | e:A, c:A | e ∈ Q ∧ c ∈ I}")
						idealL := b.Have(
							"L, Q plus the multiples of x by I, is an ideal",
							"ring_ideal(R, L)",
							Simp(Fwd(LDef), Fwd(ring_ideal.RingIdealDef)),
							SplitConjAll(
								Case(
									"a sum of a member of Q and a multiple of x lies in the ring",
									Simp(Fwd(set_basic.SubsetDef)),
									Derive(func(c *Argument) {
										c.FixAs[A]("v")
										vIn := c.Assume()
										e, d, vForm := c.Unpack2As[A, A](vIn, "e", "d")
										vParts := c.Conjuncts(
											vForm,
											"e lies in Q",
											"d lies in I",
											"v is e plus d times x")
										eIn := c.Have(
											"e lies in the ring",
											"e ∈ R.carrier",
											BySets(vParts[0], QInRing))
										dIn := c.Have(
											"and d lies in the ring",
											"d ∈ R.carrier",
											BySets(vParts[1], IInRing))
										em := c.MemberOf[on.R](e, eIn)
										dm := c.MemberOf[on.R](d, dIn)
										c.Show(
											"a sum of products of members of the ring",
											By(Normalized, vParts[2], comm_ring.AddIn.Read(R).At(em, comm_ring.MulIn.Read(R).At(dm, xm))))
									})),
								Case(
									"zero is zero plus zero times x",
									Derive(func(c *Argument) {
										cancel := c.Have(
											"zero is zero plus zero times x",
											"R.zero = R.zero + R.zero * x",
											ByArith(R, xIn))
										c.Show(
											"zero lies in Q and in I",
											By(cancel, idealQ, idealI, ring_ideal.IdealZero.At(r, Q), ring_ideal.IdealZero.At(r, I)))
									})),
								Case(
									"the sum of two such sums is one",
									Derive(func(c *Argument) {
										c.FixAs[A]("v")
										c.FixAs[A]("v₁")
										both := c.Conjuncts(
											c.Assume(),
											"v lies in L",
											"so does v₁")
										e, d, vForm := c.Unpack2As[A, A](both[0], "e", "d")
										e1, d1, v1Form := c.Unpack2As[A, A](both[1], "e₁", "d₁")
										vParts := c.Conjuncts(
											vForm,
											"e lies in Q",
											"d lies in I",
											"v is e plus d times x")
										v1Parts := c.Conjuncts(
											v1Form,
											"e₁ lies in Q",
											"d₁ lies in I",
											"v₁ is e₁ plus d₁ times x")
										atoms := c.Have(
											"e, d, e₁ and d₁ lie in the ring",
											"e ∈ R.carrier ∧ d ∈ R.carrier ∧ e₁ ∈ R.carrier ∧ d₁ ∈ R.carrier",
											BySets(vParts[0], vParts[1], v1Parts[0], v1Parts[1], QInRing, IInRing))
										regroup := c.Have(
											"the two sums regroup",
											"(e + d * x) + (e₁ + d₁ * x) = (e + e₁) + (d + d₁) * x",
											ByArith(R, atoms, xIn))
										c.Show(
											"Q and I are closed under addition",
											By(
												vParts[2],
												v1Parts[2],
												regroup,
												idealQ,
												idealI,
												vParts[0],
												v1Parts[0],
												vParts[1],
												v1Parts[1],
												ring_ideal.IdealAdd.At(r, Q, e, e1),
												ring_ideal.IdealAdd.At(r, I, d, d1)))
									})),
								Case(
									"a multiple of such a sum is one",
									Derive(func(c *Argument) {
										p := c.FixAs[A]("p")
										c.FixAs[A]("v")
										both := c.Conjuncts(
											c.Assume(),
											"p lies in the ring",
											"v lies in L")
										e, d, vForm := c.Unpack2As[A, A](both[1], "e", "d")
										vParts := c.Conjuncts(
											vForm,
											"e lies in Q",
											"d lies in I",
											"v is e plus d times x")
										atoms := c.Have(
											"e and d lie in the ring",
											"e ∈ R.carrier ∧ d ∈ R.carrier",
											BySets(vParts[0], QInRing, vParts[1], IInRing))
										spread := c.Have(
											"the multiple spreads over the sum",
											"p * (e + d * x) = p * e + (p * d) * x",
											ByArith(R, both[0], atoms, xIn))
										c.Show(
											"Q and I absorb multiples",
											By(
												vParts[2],
												spread,
												both[0],
												idealQ,
												idealI,
												vParts[0],
												vParts[1],
												ring_ideal.IdealMul.At(r, Q, p, e),
												ring_ideal.IdealMul.At(r, I, p, d)))
									}))))
						K, KDef := b.LetAs[Set[A]]("K", "{v:A | v ∈ R.carrier ∧ v * b ∈ L}")
						idealK := b.Have(
							"the members of the ring that b carries into L form an ideal",
							"ring_ideal(R, K)",
							Simp(Fwd(KDef)),
							By(idealL, ring_ideal.ColonIdeal.Read(R).At(L, bm)))
						products := b.Have(
							"b carries the product of a member of I and a member of N into L",
							"∀p q:A. p ∈ I ∧ q ∈ N ⇒ p * q ∈ K",
							Derive(func(c *Argument) {
								p := c.FixAs[A]("p")
								q := c.FixAs[A]("q")
								factors := c.Conjuncts(
									c.Assume(),
									"p lies in I",
									"q lies in N")
								qCarried := c.Have(
									"b carries q into H",
									"b * q ∈ H",
									By(bCarries.At(q), factors[1]))
								β, e, qForm := c.Obtain2As[A, A](
									"write b times q as β times x plus a member e of Q",
									"∃β e:A. β ∈ R.carrier ∧ e ∈ Q ∧ b * q = β * x + e",
									BySets(HForm, qCarried))
								qParts := c.Conjuncts(
									qForm,
									"β lies in the ring",
									"e lies in Q",
									"b times q is β times x plus e")
								atoms := c.Have(
									"p, q and e lie in the ring",
									"p ∈ R.carrier ∧ q ∈ R.carrier ∧ e ∈ R.carrier",
									BySets(factors[0], IInRing, factors[1], NInRing, qParts[1], QInRing))
								spread := c.Have(
									"the product times b is p times e plus β p times x",
									"(p * q) * b = p * e + (β * p) * x",
									ByArith(R, atoms, bIn, qParts[0], xIn, Scaled(p, qParts[2])))
								inL := c.Have(
									"which lies in L",
									"(p * q) * b ∈ L",
									Simp(Fwd(LDef)),
									By(
										spread,
										idealQ,
										idealI,
										atoms,
										qParts[0],
										qParts[1],
										factors[0],
										ring_ideal.IdealMul.At(r, Q, p, e),
										ring_ideal.IdealMul.At(r, I, β, p)))
								c.Show(
									"so p times q lies in K",
									Simp(Fwd(KDef)),
									By(inL, atoms, comm_ring.MulIn.Read(R)))
							}))
						productsInK := b.Have(
							"so b carries I·N into L",
							"ideal_mul(R, I, N) ⊆ K",
							By(idealK, products, ring_ideal.IdealMulLeast.At(r, I, N, K)))
						wInK := b.Have(
							"in particular w times b lies in L",
							"w ∈ R.carrier ∧ w * b ∈ L",
							BySets(KDef, productsInK, xSplit[1]))
						j1, c0, wForm := b.Obtain2As[A, A](
							"write w times b as j₁ plus c times x",
							"∃j₁ c:A. j₁ ∈ Q ∧ c ∈ I ∧ w * b = j₁ + c * x",
							BySets(LDef, wInK))
						wParts := b.Conjuncts(
							wForm,
							"j₁ lies in Q",
							"c lies in I",
							"w times b is j₁ plus c times x")
						atoms := b.Have(
							"j₀ and j₁ lie in the ring",
							"j₀ ∈ R.carrier ∧ j₁ ∈ R.carrier",
							BySets(xSplit[0], wParts[0], QInRing))
						cIn := b.Have(
							"and so does c",
							"c ∈ R.carrier",
							BySets(wParts[1], IInRing))
						cm := b.MemberOf[on.R](c0, cIn)
						relation := b.Have(
							"so b minus c carries x to b times j₀ plus j₁",
							"(b - c) * x = b * j₀ + j₁",
							ByArith(R, bIn, atoms, cIn, wInK, xIn, Scaled(unit, xSplit[2]), wParts[2]))
						relationInQ := b.Have(
							"which lies in Q",
							"(b - c) * x ∈ Q",
							By(
								Normalized,
								relation,
								idealQ,
								bIn,
								xSplit[0],
								wParts[0],
								ring_ideal.IdealMul.At(r, Q, unit, j0),
								ring_ideal.IdealAdd.At(r, Q, b.TermAs[A]("b * j₀"), j1)))
						difference := comm_ring.SubIn.Read(R).At(bm, cm)
						s := comm_ring.MulIn.Read(R).At(difference, bm)
						one := b.MemberOf[on.R](b.TermAs[A]("R.one"), comm_ring.OneIn.Read(R))
						raised := comm_ring.AddIn.Read(R).At(bm, one)
						negated := comm_ring.NegIn.Read(R).At(bm)
						lowered := b.TermAs[A]("b - R.one")
						shift := b.Have(
							"s minus one is (b + 1)(b − 1) minus b times c",
							"(b - c) * b - R.one = (b + R.one) * (b - R.one) + -b * c",
							ByArith(R, bIn, cIn))
						sOne := b.Have(
							"so s is one modulo I",
							"(b - c) * b - R.one ∈ I",
							By(
								shift,
								idealI,
								bOne,
								wParts[1],
								raised,
								negated,
								ring_ideal.IdealMul.At(r, I, raised, lowered),
								ring_ideal.IdealMul.At(r, I, negated, c0),
								ring_ideal.IdealAdd.At(r, I, b.TermAs[A]("(b + R.one) * (b - R.one)"), b.TermAs[A]("-b * c"))))
						sCarries := b.Have(
							"and s carries N into Q",
							"∀z:A. z ∈ N ⇒ (b - c) * b * z ∈ Q",
							Derive(func(c *Argument) {
								z := c.FixAs[A]("z")
								zIn := c.Assume()
								zCarried := c.Have(
									"b carries z into H",
									"b * z ∈ H",
									By(bCarries.At(z), zIn))
								β, e, zForm := c.Obtain2As[A, A](
									"write b times z as β times x plus a member e of Q",
									"∃β e:A. β ∈ R.carrier ∧ e ∈ Q ∧ b * z = β * x + e",
									BySets(HForm, zCarried))
								zParts := c.Conjuncts(
									zForm,
									"β lies in the ring",
									"e lies in Q",
									"b times z is β times x plus e")
								zAtoms := c.Have(
									"z and e lie in the ring",
									"z ∈ R.carrier ∧ e ∈ R.carrier",
									BySets(zIn, NInRing, zParts[1], QInRing))
								spread := c.Have(
									"s times z is β times (b − c) x plus (b − c) e",
									"(b - c) * b * z = β * ((b - c) * x) + (b - c) * e",
									ByArith(R, bIn, cIn, zAtoms, zParts[0], xIn, Scaled(difference, zParts[2])))
								c.Show(
									"Q absorbs both terms",
									By(
										spread,
										idealQ,
										relationInQ,
										zParts[0],
										zParts[1],
										difference,
										ring_ideal.IdealMul.At(r, Q, β, c.TermAs[A]("(b - c) * x")),
										ring_ideal.IdealMul.At(r, Q, difference, e),
										ring_ideal.IdealAdd.At(r, Q, c.TermAs[A]("β * ((b - c) * x)"), c.TermAs[A]("(b - c) * e"))))
							}))
						b.Take(s)
						b.Show(
							"s = (b − c) times b is one modulo I and carries N into Q",
							By(s, sOne, sCarries))
					}))))
		a.Show(
			"in particular modulo J",
			By(everyIdeal.At(J), given[4], given[5], given[6]))
	}),
})}
