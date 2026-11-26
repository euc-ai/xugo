// localization.go — the relational interface to localization, stated
// over ring records and a map from the source to the localization, its
// companion for a module over the ring, and the size of a localization.

package ring_localization

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_ideal"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinal"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_product"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// IsLocalizationOnDef — denominators become units, every target element
// has a fraction representation, and a denominator annihilates each
// source element that maps to zero.
var IsLocalizationOnDef = isLocalizationOnDefThm{family.Define(registry.DefEntry{
	Name:  "IsLocalizationOnDef",
	Key:   "prop_54c482ed1f0c294f",
	Const: "is_localization_on",
	Type:  "ring_ops(A) → set(A) → ring_ops(B) → (A → B) → bool",
	Reading: "The homomorphism condition supplies both commutative ring " +
		"structures and restricts the map to their carriers. Zero rings and " +
		"denominator sets containing zero are allowed; no nonzero condition is imposed.",
	Equations: []string{
		"∀R:ring_ops(A). ∀S:set(A). ∀L:ring_ops(B). ∀ι:(A → B). " +
			"    is_localization_on(R, S, L, ι) ⇔ " +
			"    multiplicative_set(R.mul, R.one, R.carrier, S) ∧ " +
			"    ring_homomorphism(R, L, ι) ∧ " +
			"    (∀s:A. s ∈ S ⇒ ring_unit(L, ι(s))) ∧ " +
			"    (∀y:B. y ∈ L.carrier ⇒ ∃a s:A. a ∈ R.carrier ∧ s ∈ S ∧ L.mul(y, ι(s)) = ι(a)) ∧ " +
			"    (∀a:A. a ∈ R.carrier ∧ ι(a) = L.zero ⇒ ∃s:A. s ∈ S ∧ R.mul(s, a) = R.zero)",
	},
	Deps: []registry.EntryLike{MultiplicativeSetDef},
})}

// IsModuleLocalizationOnDef — `is_module_localization_on(R, Q, S', ρ, N,
// N', ν)`: ν, from the module N over R into the module N' over S', is the
// localization of N at Q along the ring map ρ: N' is a module over S', ν
// is linear over R with N' read over R through ρ, every member of N'
// times the image of some q in Q is the image of a member of N, and a
// member of N that ν kills is killed by some q in Q.
var IsModuleLocalizationOnDef = isModuleLocalizationOnDefThm{family.Define(registry.DefEntry{
	Name:  "IsModuleLocalizationOnDef",
	Key:   "prop_696da35497813ebe",
	Const: "is_module_localization_on",
	Type: "ring_ops(A) → " +
		"set(A) → " +
		"ring_ops(B) → " +
		"(A → B) → " +
		"module_ops(A, C) → " +
		"module_ops(B, D) → " +
		"(C → D) → " +
		"bool",
	Equations: []string{
		"∀R:ring_ops(A). " +
			"∀Q:set(A). " +
			"∀S':ring_ops(B). " +
			"∀ρ:(A → B). " +
			"∀N:module_ops(A, C). " +
			"∀N':module_ops(B, D). " +
			"∀ν:(C → D). " +
			"    is_module_localization_on(R, Q, S', ρ, N, N', ν) ⇔ " +
			"    module_on(S', N') ∧ " +
			"    module_homomorphism(R, N, scalar_restriction(ρ, N'), ν) ∧ " +
			"    (∀y:D. y ∈ N'.carrier ⇒ ∃n:C. ∃q:A. n ∈ N.carrier ∧ q ∈ Q ∧ N'.smul(ρ(q), y) = ν(n)) ∧ " +
			"    (∀n:C. n ∈ N.carrier ∧ ν(n) = N'.zero ⇒ ∃q:A. q ∈ Q ∧ N.smul(q, n) = N.zero)",
	},
	Reading: "S' need not be the localization of R at Q: that is the separate hypothesis " +
		"is_localization_on(R, Q, S', ρ), stated beside this one wherever N' is read as N[Q⁻¹], and " +
		"without it nothing makes ρ(q) act invertibly on N' (a module N over R with the identity " +
		"satisfies the predicate at S' = R.carrier, ρ the identity, for any Q holding R.one). Nor is Q " +
		"asked to be a multiplicative set inside R's carrier; is_localization_on asks it. At Q = {R.one} " +
		"the predicate makes ν an isomorphism onto N' read over R, R.one acting as the identity on both " +
		"sides. At Q ∋ R.zero the last two conjuncts hold of every linear ν, zero acting as zero on both " +
		"sides; it is is_localization_on, making S' the zero ring, that makes N' the zero module.",
})}

// LocalizationCarrierCardLe — a localization of R at S has no more
// members than the pairs of a member of R and a denominator: each member
// is a fraction.
var LocalizationCarrierCardLe = localizationCarrierCardLeThm{family.Add(registry.ProofEntry{
	Name: "LocalizationCarrierCardLe",
	Key:  "prop_f2b4cfc21c0260a",
	Reading: "Any localization, not only the fraction model: the bound is read " +
		"off the fraction representation IsLocalizationOnDef asks of every member " +
		"of L. At S ∋ R.zero L is the one-point ring and the bound holds trivially.",
	Deps: []registry.EntryLike{
		IsLocalizationOnDef,
		cardinal.CardLeCover,
		set_product.InCross,
		ring_ideal.RingUnitDef,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀S:set(A). ∀L:ring_ops(B). ∀ι:(A → B).",
		Hypotheses: []string{
			"is_localization_on(R, S, L, ι)",
		},
		Conclusion: "card_le(L.carrier, set_cross(R.carrier, S))",
	},
		"every y in L's carrier has a ∈ R.carrier and s ∈ S with y * ι(s) = ι(a) "+
			"(IsLocalizationOnDef), and ι(s) is a unit of L, so y is the one member of L's "+
			"carrier with that product; the map choosing, at (a, s), a member of L's carrier "+
			"with y * ι(s) = ι(a) covers L's carrier from the pairs (InCross, CardLeCover)"),
})}

// LocalizationHomomorphismExtensional — write an element with a unit
// denominator; agreement on the numerator and denominator determines its image.
var LocalizationHomomorphismExtensional = localizationHomomorphismExtensionalThm{family.Add(registry.ProofEntry{
	Name: "LocalizationHomomorphismExtensional",
	Key:  "prop_1cf1d33f34b5cd4f",
	Build: family.Theorem(
		Statement{
			Binders: "∀R:ring_ops(A). " +
				"∀S:set(A). " +
				"∀L:ring_ops(B). " +
				"∀ι:(A → B). " +
				"∀T:ring_ops(C). " +
				"∀h k:(B → C). " +
				"∀y:B.",
			Hypotheses: []string{
				"is_localization_on(R, S, L, ι)",
				"ring_homomorphism(L, T, h)",
				"ring_homomorphism(L, T, k)",
				"∀a:A. a ∈ R.carrier ⇒ h(ι(a)) = k(ι(a))",
				"y ∈ L.carrier",
			},
			Conclusion: "h(y) = k(y)",
		},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			S *Expr[Set[A]],
			L *Expr[RingOps[B]],
			ι *Arrow[A, B],
			T *Expr[RingOps[C]],
			h, k *Arrow[B, C],
			assumptions Fact,
			y *Expr[B],
			yIn Fact,
		) {
			a.Do(Unfold(IsLocalizationOnDef))
			fractions := a.Hyp("∀y:B. y ∈ L.carrier ⇒ ∃r s:A. r ∈ R.carrier ∧ s ∈ S ∧ L.mul(y, ι(s)) = ι(r)")
			units := a.Hyp("∀s:A. s ∈ S ⇒ ring_unit(L, ι(s))")
			multiplicative := a.Hyp("multiplicative_set(R.carrier, S)")
			agreement := a.Hyp("∀r:A. r ∈ R.carrier ⇒ h(ι(r)) = k(ι(r))")
			hHom := a.Hyp("ring_homomorphism(L, T, h)")
			kHom := a.Hyp("ring_homomorphism(L, T, k)")
			r, s, fraction := a.Obtain2As[A, A](
				"choose a numerator and denominator",
				"∃r s:A. r ∈ R.carrier ∧ s ∈ S ∧ L.mul(y, ι(s)) = ι(r)",
				By(yIn, fractions.At(y)))
			a.Have(
				"the denominator becomes a unit",
				"ring_unit(L, ι(s))",
				By(fraction, units.At(s)))
			a.Do(Unfold(ring_ideal.RingUnitDef))
			w, inverse := a.UnpackAs[B](a.Hyp("∃w:B. w ∈ L.carrier ∧ L.mul(ι(s), w) = L.one"), "w")
			rIn := a.Hyp("r ∈ R.carrier")
			sIn := a.Hyp("s ∈ S")
			denominatorIn := a.Hyp("ι(s) ∈ L.carrier")
			fractionEq := a.Hyp("L.mul(y, ι(s)) = ι(r)")
			sourceIn := a.Have(
				"the denominator lies in the source carrier",
				"s ∈ R.carrier",
				BySets(
					multiplicative,
					sIn,
					MultiplicativeSetDef.At(
						a.TermAs[Op[A]]("R.mul"), a.TermAs[A]("R.one"), a.TermAs[Set[A]]("R.carrier"), S)))
			agree := a.Have(
				"the maps agree on the numerator and denominator",
				"h(ι(r)) = k(ι(r)) ∧ h(ι(s)) = k(ι(s))",
				By(rIn, sourceIn, agreement.At(r), agreement.At(s)))
			denominator := ι.Apply(s)
			yMember := proof.MemberOf(y, yIn)
			denominatorMember := proof.MemberOf(denominator, denominatorIn)
			products := a.Have(
				"multiplication by the common denominator makes the images equal",
				"T.mul(h(y), h(ι(s))) = T.mul(k(y), h(ι(s)))",
				By(
					fractionEq,
					agree,
					ring_homomorphism.MapMul.Read(hHom).At(yMember, denominatorMember),
					ring_homomorphism.MapMul.Read(kHom).At(yMember, denominatorMember)))
			inverseParts := a.Conjuncts(
				inverse,
				"the inverse lies in the localization",
				"the inverse cancels the denominator")
			wMember := proof.MemberOf(w, inverseParts[0])
			imageInverse := a.Have(
				"the image of the inverse still cancels the denominator",
				"T.mul(h(ι(s)), h(w)) = T.one",
				By(
					Normalized,
					ring_homomorphism.MapOne.Read(hHom),
					inverse,
					ring_homomorphism.MapMul.Read(hHom).At(denominatorMember, wMember)))
			targetRing := a.Have(
				"the common target is a commutative ring",
				"comm_ring_on(T)",
				By(ring_homomorphism.Target.Read(hHom)))
			imagesIn := a.Have(
				"all factors lie in the target carrier",
				"h(y) ∈ T.carrier ∧ k(y) ∈ T.carrier ∧ h(ι(s)) ∈ T.carrier ∧ h(w) ∈ T.carrier",
				By(
					ring_homomorphism.MapIn.Read(hHom),
					ring_homomorphism.MapIn.Read(kHom),
					yIn,
					denominatorIn,
					inverse))
			monoid := comm_ring.MulMonoidOn.Read(targetRing)
			a.Show(
				"cancel the common unit denominator",
				CalcEq(
					Leg(
						a.TermAs[C]("T.mul(T.mul(h(y), h(ι(s))), h(w))"),
						"insert the denominator and its inverse",
						Simp(Rev(comm_monoid.AssocOn.Read(monoid))),
						imageInverse.Rw(),
						By(imagesIn, comm_monoid.RightIdentityOn.Read(monoid))),
					Leg(
						a.TermAs[C]("T.mul(T.mul(k(y), h(ι(s))), h(w))"),
						"replace the equal mapped products",
						products.Rw(),
						Basic()),
					FinalLeg(
						"cancel the denominator and its inverse",
						Simp(Rev(comm_monoid.AssocOn.Read(monoid))),
						imageInverse.Rw(),
						By(imagesIn, comm_monoid.RightIdentityOn.Read(monoid))),
				))
		}),
})}

// ToFractionIsLocalization — a class has a numerator and denominator;
// denominators become invertible, and some denominator annihilates the numerator of each zero class.
var ToFractionIsLocalization = toFractionIsLocalizationThm{family.Add(registry.ProofEntry{
	Name: "ToFractionIsLocalization",
	Key:  "prop_b38e913494234389",
	Build: family.Sections(
		Statement{
			Binders: "∀R:ring_ops(A). ∀S:set(A).",
			Hypotheses: []string{
				"comm_ring_on(R)",
				"multiplicative_set(R.carrier, S)",
			},
			Conclusion: "is_localization_on(R, " +
				"    S, " +
				"    mk_ring(fraction_add(R.carrier, S), " +
				"        fraction_zero(R.carrier, S), " +
				"        fraction_neg(R.carrier, S), " +
				"        fraction_mul(R.carrier, S), " +
				"        fraction_one(R.carrier, S), " +
				"        fraction_sub(R.carrier, S), " +
				"        ring_localization(R.carrier, S)), " +
				"    to_fraction(R.carrier, S))",
		},
		func(ctx *Script, headline string) *GoalStackNode {
			classIn := ctx.Lemma(
				Statement{
					Binders: "∀mul:(A → A → A). ∀c S:set(A). ∀a s:A.",
					Hypotheses: []string{
						"a ∈ c",
						"s ∈ S",
					},
					Conclusion: "fraction_class(mul, c, S, a, s) ∈ ring_localization(mul, c, S)",
				},
				func(q *Argument, mul *Arrow2[A, A, A], c, S *Expr[Set[A]], a, s *Expr[A], members Fact) {
					q.Show(
						"a fraction is the class of a member of c over a member "+
							"of S, and the class of (a, s) is that of a over s",
						Simp(Fwd(RingLocalizationMember)),
						Witness(a),
						Witness(s),
						By(members))
				})
			clearDenominator := ctx.Lemma(
				Statement{
					Binders: "∀R:ring_ops(A). ∀S:set(A). ∀a s:A.",
					Hypotheses: []string{
						"comm_ring_on(R)",
						"multiplicative_set(R.carrier, S)",
						"a ∈ R.carrier",
						"s ∈ S",
					},
					Conclusion: "fraction_mul(R.carrier, " +
						"    S, " +
						"    fraction_class(R.carrier, S, a, s), " +
						"    to_fraction(R.carrier, S, s)) = " +
						"to_fraction(R.carrier, S, a)",
				},
				func(q *Argument, R *Expr[RingOps[A]], S *Expr[Set[A]], a, s *Expr[A], assumptions Fact) {
					q.Do(Unfold(ToFractionDef))
					ring := q.Hyp("comm_ring_on(R)")
					multiplicative := q.Hyp("multiplicative_set(R.carrier, S)")
					aIn, sIn := q.Hyp("a ∈ R.carrier"), q.Hyp("s ∈ S")
					members := q.Have(
						"one is a denominator and every denominator lies in the carrier",
						"R.one ∈ S ∧ s ∈ R.carrier",
						BySets(
							sIn,
							multiplicative,
							MultiplicativeSetDef.At(
								q.TermAs[Op[A]]("R.mul"), q.TermAs[A]("R.one"), q.TermAs[Set[A]]("R.carrier"), S)))
					q.Do(Simp(
						Fwd(FractionMulClass.Read(ring)),
						Fwd(comm_monoid.RightIdentityOn.Read(comm_ring.MulMonoidOn.Read(ring)))))
					q.Do(Simp(Fwd(FractionClassEq.Read(ring)), Fwd(comm_ring.MulIn.Read(ring))))
					q.Take(q.TermAs[A]("R.one"))
					q.Show(
						"one witnesses the equality after multiplying the fractions",
						ByArith(aIn, members, ring))
				})
			return ctx.Theorem(headline,
				func(a *Argument, R *Expr[RingOps[A]], S *Expr[Set[A]], assumptions Fact) {
					mul := a.TermAs[Op[A]]("R.mul")
					one := a.TermAs[A]("R.one")
					carrier := a.TermAs[Set[A]]("R.carrier")
					a.Do(Unfold(IsLocalizationOnDef))
					ring := a.Hyp("comm_ring_on(R)")
					multiplicative := a.Hyp("multiplicative_set(R.carrier, S)")
					a.Do(SplitConjAll(
						Case(
							"the denominators form a multiplicative set, the hypothesis",
							By(multiplicative)),
						Case(
							"the natural map is a ring homomorphism",
							By(multiplicative, ToFractionHomomorphism.Read(ring))),
						Case(
							"each denominator maps to a unit",
							Derive(func(b *Argument) {
								s := b.FixAs[A]("s")
								sIn := b.Assume()
								b.Do(Unfold(ring_ideal.RingUnitDef))
								members := b.Have(
									"one is a denominator and s lies in the source carrier",
									"R.one ∈ S ∧ s ∈ R.carrier",
									BySets(sIn, multiplicative, MultiplicativeSetDef.At(mul, one, carrier, S)))
								b.Do(SplitConj(
									Case(
										"the image of the denominator belongs to the localization",
										Simp(Fwd(ToFractionDef)),
										By(members, At(classIn, mul, carrier, S, s, one))),
									Case(
										"the class of one over s is an inverse",
										Derive(func(c *Argument) {
											c.Take(c.TermAs[Set[Prod[A, A]]]("fraction_class(R.carrier, S, R.one, s)"))
											c.Do(SplitConj(
												Case(
													"the inverse belongs to the localization",
													By(sIn, comm_ring.OneIn.Read(ring), At(classIn, mul, carrier, S, one, s))),
												Case(
													"multiplication gives the unit fraction",
													By(sIn, multiplicative, DenominatorUnit.Read(ring))),
											))
										})),
								))
							})),
						Case(
							"each element has a fraction presentation",
							Derive(func(b *Argument) {
								b.FixAs[Set[Prod[A, A]]]("y")
								yIn := b.Assume()
								r, s, representative := b.Obtain2As[A, A](
									"a fraction is the class of a numerator over a denominator",
									"∃r s:A. r ∈ R.carrier ∧ s ∈ S ∧ y = fraction_class(R.carrier, S, r, s)",
									By(yIn, RingLocalizationMember))
								b.Take(r)
								b.Take(s)
								b.Show(
									"clear the chosen denominator",
									By(representative, multiplicative, ring, At(clearDenominator, R, S, r, s)))
							})),
						Case(
							"a denominator annihilates every element in the kernel",
							Derive(func(b *Argument) {
								r := b.FixAs[A]("r")
								killed := b.Assume()
								oneIn := b.Have(
									"one belongs to the denominator set",
									"R.one ∈ S",
									BySets(multiplicative, MultiplicativeSetDef.At(mul, one, carrier, S)))
								parts := b.Conjuncts(
									killed,
									"the numerator lies in the source carrier",
									"its image is zero")
								b.Show(
									"the zero-fraction criterion supplies an annihilating denominator",
									By(
										oneIn,
										killed,
										multiplicative,
										ToFractionDef.At(mul, one, carrier, S, r),
										FractionZeroIff.Read(ring).At(S, proof.MemberOf(r, parts[0]), one)))
							})),
					))
				})
		}),
})}

// LocalizationUniversal — solve each fraction equation in the target;
// the kernel condition makes the value independent of its presentation.
var LocalizationUniversal = localizationUniversalThm{family.Add(registry.ProofEntry{
	Name: "LocalizationUniversal",
	Key:  "prop_5fc92a35dd3e19d7",
	Build: family.Sections(
		Statement{
			Binders: "∀R:ring_ops(A). ∀S:set(A). ∀L:ring_ops(B). ∀ι:(A → B). ∀T:ring_ops(C). ∀u:(A → C).",
			Hypotheses: []string{
				"is_localization_on(R, S, L, ι)",
				"ring_homomorphism(R, T, u)",
				"∀s:A. s ∈ S ⇒ ring_unit(T, u(s))",
			},
			Conclusion: "∃h:(B → C). " +
				"    ring_homomorphism(L, T, h) ∧ " +
				"    (∀a:A. a ∈ R.carrier ⇒ h(ι(a)) = u(a)) ∧ " +
				"    (∀k:(B → C). " +
				"        ring_homomorphism(L, T, k) ∧ (∀a:A. a ∈ R.carrier ⇒ k(ι(a)) = u(a)) ⇒ " +
				"        ∀y:B. y ∈ L.carrier ⇒ k(y) = h(y))",
		},
		func(ctx *Script, headline string) *GoalStackNode {
			cancelUnit := ctx.Lemma(Statement{
				Binders: "∀T:ring_ops(C). ∀x y d:C.",
				Hypotheses: []string{
					"comm_ring_on(T)",
					"x ∈ T.carrier",
					"y ∈ T.carrier",
					"ring_unit(T, d)",
					"T.mul(x, d) = T.mul(y, d)",
				},
				Conclusion: "x = y",
			},
				func(q *Argument, T *Expr[RingOps[C]], x, y, d *Expr[C], assumptions Fact) {
					q.Do(Unfold(ring_ideal.RingUnitDef))
					w, inverse := q.UnpackAs[C](q.Hyp("∃w:C. w ∈ T.carrier ∧ T.mul(d, w) = T.one"), "w")
					_ = w
					ring := q.Hyp("comm_ring_on(T)")
					xIn, yIn := q.Hyp("x ∈ T.carrier"), q.Hyp("y ∈ T.carrier")
					products := q.Hyp("T.mul(x, d) = T.mul(y, d)")
					monoid := comm_ring.MulMonoidOn.Read(ring)
					q.Show(
						"cancel multiplication by a unit",
						CalcEq(
							Leg(
								q.TermAs[C]("T.mul(T.mul(x, d), w)"),
								"insert the denominator and its inverse",
								Simp(Rev(comm_monoid.AssocOn.Read(monoid))),
								By(Normalized, comm_monoid.RightIdentityOn.Read(monoid), xIn, inverse)),
							Leg(
								q.TermAs[C]("T.mul(T.mul(y, d), w)"),
								"replace the equal products",
								products.Rw(),
								Basic()),
							FinalLeg(
								"remove the denominator and its inverse",
								Simp(Rev(comm_monoid.AssocOn.Read(monoid))),
								By(Normalized, comm_monoid.RightIdentityOn.Read(monoid), yIn, inverse)),
						))
				})
			killsKernel := ctx.Lemma(Statement{
				Binders: "∀R:ring_ops(A). " +
					"∀S:set(A). " +
					"∀L:ring_ops(B). " +
					"∀ι:(A → B). " +
					"∀T:ring_ops(C). " +
					"∀u:(A → C). " +
					"∀a:A.",
				Hypotheses: []string{
					"is_localization_on(R, S, L, ι)",
					"ring_homomorphism(R, T, u)",
					"∀s:A. s ∈ S ⇒ ring_unit(T, u(s))",
					"a ∈ R.carrier",
					"ι(a) = L.zero",
				},
				Conclusion: "u(a) = T.zero",
			},
				func(
					q *Argument,
					R *Expr[RingOps[A]],
					S *Expr[Set[A]],
					L *Expr[RingOps[B]],
					ι *Arrow[A, B],
					T *Expr[RingOps[C]],
					u *Arrow[A, C],
					a *Expr[A],
					assumptions Fact,
				) {
					q.Do(Unfold(IsLocalizationOnDef))
					aIn, killed := q.Hyp("a ∈ R.carrier"), q.Hyp("ι(a) = L.zero")
					multiplicative := q.Hyp("multiplicative_set(R.carrier, S)")
					units := q.Hyp("∀s:A. s ∈ S ⇒ ring_unit(T, u(s))")
					kernel := q.Hyp("∀a:A. a ∈ R.carrier ∧ ι(a) = L.zero ⇒ ∃s:A. s ∈ S ∧ R.mul(s, a) = R.zero")
					hom := q.Hyp("ring_homomorphism(R, T, u)")
					s, annihilator := q.ObtainAs[A](
						"choose a denominator annihilating the kernel element",
						"∃s:A. s ∈ S ∧ R.mul(s, a) = R.zero",
						By(killed, aIn, kernel.At(a)))
					sIn := q.Have(
						"the annihilator is in the source carrier",
						"s ∈ R.carrier",
						BySets(multiplicative, annihilator, MultiplicativeSetDef))
					targetRing := q.Have(
						"the target is a commutative ring",
						"comm_ring_on(T)",
						By(ring_homomorphism.Target.Read(hom)))
					images := q.Have(
						"the images and zero lie in the target carrier",
						"u(a) ∈ T.carrier ∧ u(s) ∈ T.carrier ∧ T.zero ∈ T.carrier",
						By(aIn, sIn, ring_homomorphism.MapIn.Read(hom), comm_ring.ZeroIn.Read(targetRing)))
					mapped := q.Have(
						"the target map preserves the annihilating equation",
						"T.mul(u(s), u(a)) = T.zero",
						By(
							Normalized,
							annihilator,
							sIn,
							aIn,
							ring_homomorphism.MapMul.Read(hom).At(proof.MemberOf(s, sIn), proof.MemberOf(a, aIn)),
							ring_homomorphism.MapZero.Read(hom)))
					products := q.Have(
						"the image and zero have equal products with the denominator",
						"T.mul(u(a), u(s)) = T.mul(T.zero, u(s))",
						ByArith(targetRing, images, mapped))
					q.Show(
						"cancel the image of the annihilator",
						By(
							targetRing,
							images,
							annihilator,
							units.At(s),
							products,
							At(cancelUnit, T, u.Apply(a), q.TermAs[C]("T.zero"), u.Apply(s))))
				})
			respectsEquality := ctx.Lemma(Statement{
				Binders: "∀R:ring_ops(A). " +
					"∀S:set(A). " +
					"∀L:ring_ops(B). " +
					"∀ι:(A → B). " +
					"∀T:ring_ops(C). " +
					"∀u:(A → C). " +
					"∀a b:A.",
				Hypotheses: []string{
					"is_localization_on(R, S, L, ι)",
					"ring_homomorphism(R, T, u)",
					"∀s:A. s ∈ S ⇒ ring_unit(T, u(s))",
					"a ∈ R.carrier",
					"b ∈ R.carrier",
					"ι(a) = ι(b)",
				},
				Conclusion: "u(a) = u(b)",
			},
				func(
					q *Argument,
					R *Expr[RingOps[A]],
					S *Expr[Set[A]],
					L *Expr[RingOps[B]],
					ι *Arrow[A, B],
					T *Expr[RingOps[C]],
					u *Arrow[A, C],
					a, b *Expr[A],
					assumptions Fact,
				) {
					ιHom := q.Have(
						"the localization map is a ring homomorphism",
						"ring_homomorphism(R, L, ι)",
						Unfold(IsLocalizationOnDef))
					q.Do(Basic())
					loc := q.Hyp("is_localization_on(R, S, L, ι)")
					hom := q.Hyp("ring_homomorphism(R, T, u)")
					units := q.Hyp("∀s:A. s ∈ S ⇒ ring_unit(T, u(s))")
					aIn, bIn := q.Hyp("a ∈ R.carrier"), q.Hyp("b ∈ R.carrier")
					equal := q.Hyp("ι(a) = ι(b)")
					difference := q.TermAs[A]("R.add(R.neg(a), b)")
					aMember, bMember := proof.MemberOf(a, aIn), proof.MemberOf(b, bIn)
					kernel := q.Have(
						"the additive difference belongs to the localization kernel",
						"R.add(R.neg(a), b) ∈ R.carrier ∧ ι(R.add(R.neg(a), b)) = L.zero",
						By(
							aIn,
							bIn,
							equal,
							group_homomorphism.EqIffInKernel.Read(ring_homomorphism.AdditiveHomomorphism.Read(ιHom)).At(
								aMember, bMember),
							group_homomorphism.InKernel.At(
								q.TermAs[B]("L.zero"), q.TermAs[Set[A]]("R.carrier"), ι, difference)))
					killed := q.Have(
						"the target map kills the difference",
						"u(R.add(R.neg(a), b)) = T.zero",
						By(loc, hom, units, kernel, At(killsKernel, R, S, L, ι, T, u, difference)))
					q.Show(
						"the two target images are equal",
						By(
							aIn,
							bIn,
							kernel,
							killed,
							group_homomorphism.EqIffInKernel.Read(ring_homomorphism.AdditiveHomomorphism.Read(hom)).At(
								aMember, bMember),
							group_homomorphism.InKernel.At(
								q.TermAs[C]("T.zero"), q.TermAs[Set[A]]("R.carrier"), u, difference)))
				})
			fractionValuesAgree := ctx.Lemma(Statement{
				Binders: "∀R:ring_ops(A). " +
					"∀S:set(A). " +
					"∀L:ring_ops(B). " +
					"∀ι:(A → B). " +
					"∀T:ring_ops(C). " +
					"∀u:(A → C). " +
					"∀a b s t:A. " +
					"∀y:B. " +
					"∀x z:C.",
				Hypotheses: []string{
					"is_localization_on(R, S, L, ι)",
					"ring_homomorphism(R, T, u)",
					"∀r:A. r ∈ S ⇒ ring_unit(T, u(r))",
					"a ∈ R.carrier",
					"b ∈ R.carrier",
					"s ∈ S",
					"t ∈ S",
					"y ∈ L.carrier",
					"x ∈ T.carrier",
					"z ∈ T.carrier",
					"L.mul(y, ι(s)) = ι(a)",
					"L.mul(y, ι(t)) = ι(b)",
					"T.mul(x, u(s)) = u(a)",
					"T.mul(z, u(t)) = u(b)",
				},
				Conclusion: "x = z",
			},
				func(
					q *Argument,
					R *Expr[RingOps[A]],
					S *Expr[Set[A]],
					L *Expr[RingOps[B]],
					ι *Arrow[A, B],
					T *Expr[RingOps[C]],
					u *Arrow[A, C],
					a, b, s, t *Expr[A],
					y *Expr[B],
					x, z *Expr[C],
					assumptions Fact,
				) {
					q.Do(Basic())
					q.Have(
						"the localization supplies its map and denominator set",
						"ring_homomorphism(R, L, ι) ∧ multiplicative_set(R.carrier, S)",
						Unfold(IsLocalizationOnDef),
						Derive(func(b *Argument) {
							b.Show(
								"both are clauses of the localization",
								By(b.Hyp("ring_homomorphism(R, L, ι)"), b.Hyp("multiplicative_set(R.carrier, S)")))
						}))
					q.Do(Basic())
					loc := q.Hyp("is_localization_on(R, S, L, ι)")
					ιHom := q.Hyp("ring_homomorphism(R, L, ι)")
					hom := q.Hyp("ring_homomorphism(R, T, u)")
					mult := q.Hyp("multiplicative_set(R.carrier, S)")
					units := q.Hyp("∀r:A. r ∈ S ⇒ ring_unit(T, u(r))")
					aIn, bIn := q.Hyp("a ∈ R.carrier"), q.Hyp("b ∈ R.carrier")
					sIn, tIn := q.Hyp("s ∈ S"), q.Hyp("t ∈ S")
					yIn, xIn, zIn := q.Hyp("y ∈ L.carrier"), q.Hyp("x ∈ T.carrier"), q.Hyp("z ∈ T.carrier")
					sRepresentation, tRepresentation := q.Hyp("L.mul(y, ι(s)) = ι(a)"), q.Hyp("L.mul(y, ι(t)) = ι(b)")
					xValue, zValue := q.Hyp("T.mul(x, u(s)) = u(a)"), q.Hyp("T.mul(z, u(t)) = u(b)")
					denominators := q.Have(
						"both denominators lie in the source carrier",
						"s ∈ R.carrier ∧ t ∈ R.carrier",
						BySets(sIn, tIn, mult, MultiplicativeSetDef))
					sourceRing := q.Have(
						"the source is a commutative ring",
						"comm_ring_on(R)",
						By(ring_homomorphism.Source.Read(hom)))
					targetRing := q.Have(
						"the target is a commutative ring",
						"comm_ring_on(T)",
						By(ring_homomorphism.Target.Read(hom)))
					localImages := q.Have(
						"the four coefficient images lie in the localization",
						"ι(a) ∈ L.carrier ∧ ι(b) ∈ L.carrier ∧ ι(s) ∈ L.carrier ∧ ι(t) ∈ L.carrier",
						By(aIn, bIn, denominators, ring_homomorphism.MapIn.Read(ιHom)))
					cross := q.Have(
						"the localization cross products are equal",
						"L.mul(ι(a), ι(t)) = L.mul(ι(b), ι(s))",
						ByArith(
							ring_homomorphism.Target.Read(ιHom),
							yIn,
							localImages,
							Scaled(ι.Apply(t), sRepresentation),
							Scaled(ι.Apply(s), tRepresentation)))
					aMember, bMember := proof.MemberOf(a, aIn), proof.MemberOf(b, bIn)
					denominatorParts := q.Conjuncts(
						denominators,
						"the first denominator lies in the source carrier",
						"the second denominator lies in the source carrier")
					sMember, tMember := proof.MemberOf(s, denominatorParts[0]), proof.MemberOf(t, denominatorParts[1])
					sourceCross := q.Have(
						"the source cross products have equal localization images",
						"ι(R.mul(a, t)) = ι(R.mul(b, s))",
						By(
							Normalized,
							cross,
							aIn,
							bIn,
							denominators,
							ring_homomorphism.MapMul.Read(ιHom).At(aMember, tMember),
							ring_homomorphism.MapMul.Read(ιHom).At(bMember, sMember)))
					crossIn := q.Have(
						"the cross products belong to the source",
						"R.mul(a, t) ∈ R.carrier ∧ R.mul(b, s) ∈ R.carrier",
						By(aIn, bIn, denominators, comm_ring.MulIn.Read(sourceRing)))
					mappedCross := q.Have(
						"the target images of the cross products are equal",
						"u(R.mul(a, t)) = u(R.mul(b, s))",
						By(
							loc,
							hom,
							units,
							crossIn,
							sourceCross,
							At(respectsEquality, R, S, L, ι, T, u, q.TermAs[A]("R.mul(a,t)"), q.TermAs[A]("R.mul(b,s)"))))
					targetCross := q.Have(
						"the target cross products are equal",
						"T.mul(u(a), u(t)) = T.mul(u(b), u(s))",
						By(
							Normalized,
							mappedCross,
							aIn,
							bIn,
							denominators,
							ring_homomorphism.MapMul.Read(hom).At(aMember, tMember),
							ring_homomorphism.MapMul.Read(hom).At(bMember, sMember)))
					targetImages := q.Have(
						"the four target images lie in its carrier",
						"u(a) ∈ T.carrier ∧ u(b) ∈ T.carrier ∧ u(s) ∈ T.carrier ∧ u(t) ∈ T.carrier",
						By(aIn, bIn, denominators, ring_homomorphism.MapIn.Read(hom)))
					doubleProducts := q.Have(
						"both proposed values have the same product with both denominators",
						"T.mul(T.mul(x, u(s)), u(t)) = T.mul(T.mul(z, u(s)), u(t))",
						ByArith(
							targetRing,
							xIn,
							zIn,
							targetImages,
							targetCross,
							Scaled(u.Apply(t), xValue),
							Scaled(u.Apply(s), zValue)))
					productsIn := q.Have(
						"the first denominator products lie in the target carrier",
						"T.mul(x, u(s)) ∈ T.carrier ∧ T.mul(z, u(s)) ∈ T.carrier",
						By(xIn, zIn, targetImages, comm_ring.MulIn.Read(targetRing)))
					products := q.Have(
						"cancel the second denominator",
						"T.mul(x, u(s)) = T.mul(z, u(s))",
						By(
							targetRing,
							productsIn,
							doubleProducts,
							tIn,
							units.At(t),
							At(cancelUnit, T, q.TermAs[C]("T.mul(x,u(s))"), q.TermAs[C]("T.mul(z,u(s))"), u.Apply(t))))
					q.Show(
						"cancel the first denominator",
						By(targetRing, xIn, zIn, products, sIn, units.At(s), At(cancelUnit, T, x, z, u.Apply(s))))
				})
			solveDenominator := ctx.Lemma(Statement{
				Binders: "∀T:ring_ops(C). ∀a d:C.",
				Hypotheses: []string{
					"comm_ring_on(T)",
					"a ∈ T.carrier",
					"ring_unit(T, d)",
				},
				Conclusion: "∃z:C. z ∈ T.carrier ∧ T.mul(z, d) = a",
			},
				func(q *Argument, T *Expr[RingOps[C]], a, d *Expr[C], assumptions Fact) {
					q.Do(Unfold(ring_ideal.RingUnitDef))
					w, inverse := q.UnpackAs[C](q.Hyp("∃w:C. w ∈ T.carrier ∧ T.mul(d, w) = T.one"), "w")
					_ = w
					q.Do(Basic())
					ring := q.Hyp("comm_ring_on(T)")
					aIn, wIn, dIn := q.Hyp("a ∈ T.carrier"), q.Hyp("w ∈ T.carrier"), q.Hyp("d ∈ T.carrier")
					inverseEq := q.Hyp("T.mul(d, w) = T.one")
					_ = inverse
					q.Take(q.TermAs[C]("T.mul(a,w)"))
					q.Do(SplitConj(
						Case(
							"the quotient lies in the target carrier",
							By(aIn, wIn, comm_ring.MulIn.Read(ring))),
						Case(
							"the inverse solves the denominator equation",
							ByArith(ring, aIn, wIn, dIn, Scaled(a, inverseEq))),
					))
				})
			chooseValues := ctx.Lemma(Statement{
				Binders: "∀R:ring_ops(A). ∀S:set(A). ∀L:ring_ops(B). ∀ι:(A → B). ∀T:ring_ops(C). ∀u:(A → C).",
				Hypotheses: []string{
					"is_localization_on(R, S, L, ι)",
					"ring_homomorphism(R, T, u)",
					"∀s:A. s ∈ S ⇒ ring_unit(T, u(s))",
				},
				Conclusion: "∃h:(B → C). ∀y:B. " +
					"    y ∈ L.carrier ⇒ " +
					"    h(y) ∈ T.carrier ∧ " +
					"    (∀a s:A. a ∈ R.carrier ∧ s ∈ S ∧ L.mul(y, ι(s)) = ι(a) ⇒ T.mul(h(y), u(s)) = u(a))",
			},
				func(
					q *Argument,
					R *Expr[RingOps[A]],
					S *Expr[Set[A]],
					L *Expr[RingOps[B]],
					ι *Arrow[A, B],
					T *Expr[RingOps[C]],
					u *Arrow[A, C],
					assumptions Fact,
				) {
					q.Do(Basic())
					loc := q.Hyp("is_localization_on(R, S, L, ι)")
					hom := q.Hyp("ring_homomorphism(R, T, u)")
					units := q.Hyp("∀s:A. s ∈ S ⇒ ring_unit(T, u(s))")
					fractions := q.Have(
						"each localization element has a fraction presentation",
						"∀y:B. y ∈ L.carrier ⇒ ∃a s:A. a ∈ R.carrier ∧ s ∈ S ∧ L.mul(y, ι(s)) = ι(a)",
						Unfold(IsLocalizationOnDef))
					targetRing := q.Have(
						"the target is a commutative ring",
						"comm_ring_on(T)",
						By(ring_homomorphism.Target.Read(hom)))
					pointwise := q.Have(
						"each localization element has a value satisfying every fraction equation",
						Statement{
							Binders: "∀y:B.",
							Hypotheses: []string{
								"y ∈ L.carrier",
							},
							Conclusion: "∃x:C. " +
								"    x ∈ T.carrier ∧ " +
								"    (∀a s:A. a ∈ R.carrier ∧ s ∈ S ∧ L.mul(y, ι(s)) = ι(a) ⇒ T.mul(x, u(s)) = u(a))",
						},
						Derive(func(b *Argument) {
							y := b.FixAs[B]("y")
							yIn := b.Assume()
							a, s, chosenRepresentation := b.Obtain2As[A, A](
								"choose a fraction presentation",
								"∃a s:A. a ∈ R.carrier ∧ s ∈ S ∧ L.mul(y, ι(s)) = ι(a)",
								By(yIn, fractions.At(y)))
							x, value := b.ObtainAs[C](
								"solve the chosen denominator equation",
								"∃x:C. x ∈ T.carrier ∧ T.mul(x, u(s)) = u(a)",
								By(
									targetRing,
									ring_homomorphism.MapIn.Read(hom),
									chosenRepresentation,
									units.At(s),
									At(solveDenominator, T, u.Apply(a), u.Apply(s))))
							b.Take(x)
							b.Do(SplitConj(
								Case(
									"the chosen value lies in the target carrier",
									By(value)),
								Case(
									"every presentation gives the chosen value",
									Derive(func(c *Argument) {
										a1 := c.FixAs[A]("a₁")
										s1 := c.FixAs[A]("s₁")
										otherRepresentation := c.Assume()
										z, otherValue := c.ObtainAs[C](
											"solve the second denominator equation",
											"∃z:C. z ∈ T.carrier ∧ T.mul(z, u(s₁)) = u(a₁)",
											By(
												targetRing,
												ring_homomorphism.MapIn.Read(hom),
												otherRepresentation,
												units.At(s1),
												At(solveDenominator, T, u.Apply(a1), u.Apply(s1))))
										equal := c.Have(
											"the two fraction values agree",
											"x = z",
											By(
												loc,
												hom,
												units,
												yIn,
												chosenRepresentation,
												otherRepresentation,
												value,
												otherValue,
												At(fractionValuesAgree, R, S, L, ι, T, u, a, a1, s, s1, y, x, z)))
										c.Show(
											"the chosen value satisfies the second equation",
											equal.Rw(),
											By(otherValue))
									})),
							))
						}))
					q.Take(q.TermAs[Fun[B, C]](
						"λy:B. εx:C. " +
							"    x ∈ T.carrier ∧ " +
							"    (∀a s:A. a ∈ R.carrier ∧ s ∈ S ∧ L.mul(y, ι(s)) = ι(a) ⇒ T.mul(x, u(s)) = u(a))"))
					q.Show(
						"choose these values pointwise",
						By(pointwise))
				})
			return ctx.Theorem(headline,
				func(
					q *Argument,
					R *Expr[RingOps[A]],
					S *Expr[Set[A]],
					L *Expr[RingOps[B]],
					ι *Arrow[A, B],
					T *Expr[RingOps[C]],
					u *Arrow[A, C],
					assumptions Fact,
				) {
					q.Do(Basic())
					loc := q.Hyp("is_localization_on(R, S, L, ι)")
					hom := q.Hyp("ring_homomorphism(R, T, u)")
					units := q.Hyp("∀s:A. s ∈ S ⇒ ring_unit(T, u(s))")
					q.Have(
						"the localization supplies its map, denominators and fraction presentations",
						"ring_homomorphism(R, L, ι) ∧ "+
							"multiplicative_set(R.carrier, S) ∧ "+
							"(∀y:B. y ∈ L.carrier ⇒ ∃a s:A. a ∈ R.carrier ∧ s ∈ S ∧ L.mul(y, ι(s)) = ι(a))",
						Unfold(IsLocalizationOnDef),
						Derive(func(b *Argument) {
							b.Show(
								"all three are clauses of the localization",
								By(
									b.Hyp("ring_homomorphism(R, L, ι)"),
									b.Hyp("multiplicative_set(R.carrier, S)"),
									b.Hyp("∀y:B. y ∈ L.carrier ⇒ ∃a s:A. a ∈ R.carrier ∧ s ∈ S ∧ L.mul(y, ι(s)) = ι(a)")))
						}))
					q.Do(Basic())
					ιHom := q.Hyp("ring_homomorphism(R, L, ι)")
					mult := q.Hyp("multiplicative_set(R.carrier, S)")
					fractions := q.Hyp("∀y:B. y ∈ L.carrier ⇒ ∃a s:A. a ∈ R.carrier ∧ s ∈ S ∧ L.mul(y, ι(s)) = ι(a)")
					sourceRing := q.Have(
						"the source is a commutative ring",
						"comm_ring_on(R)",
						By(ring_homomorphism.Source.Read(hom)))
					localizationRing := q.Have(
						"the localization is a commutative ring",
						"comm_ring_on(L)",
						By(ring_homomorphism.Target.Read(ιHom)))
					targetRing := q.Have(
						"the target is a commutative ring",
						"comm_ring_on(T)",
						By(ring_homomorphism.Target.Read(hom)))
					h, chosen := q.ObtainAs[Fun[B, C]](
						"choose a value for every localization element",
						"∃h:(B → C). ∀y:B. "+
							"    y ∈ L.carrier ⇒ "+
							"    h(y) ∈ T.carrier ∧ "+
							"    (∀a s:A. a ∈ R.carrier ∧ s ∈ S ∧ L.mul(y, ι(s)) = ι(a) ⇒ T.mul(h(y), u(s)) = u(a))",
						By(loc, hom, units, At(chooseValues, R, S, L, ι, T, u)))
					mapIn := q.Have(
						"the chosen map preserves carriers",
						"∀y:B. y ∈ L.carrier ⇒ h(y) ∈ T.carrier",
						By(chosen))
					oneDenominator := q.Have(
						"one is an allowed denominator",
						"R.one ∈ S",
						BySets(mult, MultiplicativeSetDef))
					agreement := q.Have(
						"the chosen map extends the coefficient map",
						"∀a:A. a ∈ R.carrier ⇒ h(ι(a)) = u(a)",
						Derive(func(b *Argument) {
							a := b.FixAs[A]("a")
							aIn := b.Assume()
							imageIn := b.Have(
								"the coefficient image lies in the localization",
								"ι(a) ∈ L.carrier",
								By(aIn, ring_homomorphism.MapIn.Read(ιHom)))
							representation := b.Have(
								"a coefficient has denominator one",
								"L.mul(ι(a), ι(R.one)) = ι(a)",
								By(
									Normalized,
									imageIn,
									ring_homomorphism.MapOne.Read(ιHom),
									comm_monoid.RightIdentityOn.Read(comm_ring.MulMonoidOn.Read(localizationRing))))
							value := b.Have(
								"the coefficient value satisfies its denominator equation",
								"T.mul(h(ι(a)), u(R.one)) = u(a)",
								By(aIn, imageIn, oneDenominator, representation, chosen.At(ι.Apply(a))))
							b.Show(
								"remove the unit denominator",
								By(
									Normalized,
									value,
									imageIn,
									mapIn,
									ring_homomorphism.MapOne.Read(hom),
									comm_monoid.RightIdentityOn.Read(comm_ring.MulMonoidOn.Read(targetRing))))
						}))
					mapOne := q.Have(
						"the chosen map preserves one",
						"h(L.one) = T.one",
						By(
							Normalized,
							agreement,
							comm_ring.OneIn.Read(sourceRing),
							ring_homomorphism.MapOne.Read(ιHom),
							ring_homomorphism.MapOne.Read(hom)))
					values := q.Have(
						"the chosen map satisfies each fraction equation",
						Statement{
							Binders: "∀y:B. ∀a s:A.",
							Hypotheses: []string{
								"y ∈ L.carrier",
								"a ∈ R.carrier",
								"s ∈ S",
								"L.mul(y, ι(s)) = ι(a)",
							},
							Conclusion: "T.mul(h(y), u(s)) = u(a)",
						},
						By(chosen))
					operations := q.Have(
						"common denominators show preservation of addition and multiplication",
						Statement{
							Binders: "∀y z:B.",
							Hypotheses: []string{
								"y ∈ L.carrier",
								"z ∈ L.carrier",
							},
							Conclusion: "h(L.add(y, z)) = T.add(h(y), h(z)) ∧ h(L.mul(y, z)) = T.mul(h(y), h(z))",
						},
						Derive(func(b *Argument) {
							y := b.FixAs[B]("y")
							z := b.FixAs[B]("z")
							members := b.Assume()
							a, s, yRepresentation := b.Obtain2As[A, A](
								"choose a fraction presentation of the first element",
								"∃a s:A. a ∈ R.carrier ∧ s ∈ S ∧ L.mul(y, ι(s)) = ι(a)",
								By(members, fractions.At(y)))
							c, t, zRepresentation := b.Obtain2As[A, A](
								"choose a fraction presentation of the second element",
								"∃c t:A. c ∈ R.carrier ∧ t ∈ S ∧ L.mul(z, ι(t)) = ι(c)",
								By(members, fractions.At(z)))
							denominators := b.Have(
								"denominators belong to the source and their product remains allowed",
								"s ∈ R.carrier ∧ t ∈ R.carrier ∧ R.mul(s, t) ∈ S",
								BySets(yRepresentation, zRepresentation, mult, MultiplicativeSetDef))
							productsIn := b.Have(
								"all numerator and denominator products belong to the source",
								"R.mul(a, t) ∈ R.carrier ∧ "+
									"R.mul(c, s) ∈ R.carrier ∧ "+
									"R.mul(a, c) ∈ R.carrier ∧ "+
									"R.mul(s, t) ∈ R.carrier",
								By(yRepresentation, zRepresentation, denominators, comm_ring.MulIn.Read(sourceRing)))
							localImages := b.Have(
								"coefficient images lie in the localization",
								"ι(a) ∈ L.carrier ∧ ι(c) ∈ L.carrier ∧ ι(s) ∈ L.carrier ∧ ι(t) ∈ L.carrier",
								By(yRepresentation, zRepresentation, denominators, ring_homomorphism.MapIn.Read(ιHom)))
							targetImages := b.Have(
								"coefficient images lie in the target",
								"u(a) ∈ T.carrier ∧ u(c) ∈ T.carrier ∧ u(s) ∈ T.carrier ∧ u(t) ∈ T.carrier",
								By(yRepresentation, zRepresentation, denominators, ring_homomorphism.MapIn.Read(hom)))
							localResults := b.Have(
								"the sum and product belong to the localization",
								"L.add(y, z) ∈ L.carrier ∧ L.mul(y, z) ∈ L.carrier",
								By(members, comm_ring.AddIn.Read(localizationRing), comm_ring.MulIn.Read(localizationRing)))
							mappedResults := b.Have(
								"the chosen values lie in the target carrier",
								"h(y) ∈ T.carrier ∧ h(z) ∈ T.carrier ∧ h(L.add(y, z)) ∈ T.carrier ∧ h(L.mul(y, z)) ∈ T.carrier",
								By(mapIn, members, localResults))
							targetResults := b.Have(
								"the sum and product of chosen values lie in the target",
								"T.add(h(y), h(z)) ∈ T.carrier ∧ T.mul(h(y), h(z)) ∈ T.carrier",
								By(mappedResults, comm_ring.AddIn.Read(targetRing), comm_ring.MulIn.Read(targetRing)))
							yEquation := b.Have(
								"the first fraction equation",
								"L.mul(y, ι(s)) = ι(a)",
								By(yRepresentation))
							zEquation := b.Have(
								"the second fraction equation",
								"L.mul(z, ι(t)) = ι(c)",
								By(zRepresentation))
							yValue := b.Have(
								"the first value equation",
								"T.mul(h(y), u(s)) = u(a)",
								By(values.At(y, a, s), members, yRepresentation))
							zValue := b.Have(
								"the second value equation",
								"T.mul(h(z), u(t)) = u(c)",
								By(values.At(z, c, t), members, zRepresentation))
							commonUnit := b.Have(
								"the common denominator maps to a unit",
								"ring_unit(T, u(R.mul(s, t)))",
								By(units.At(b.TermAs[A]("R.mul(s,t)")), denominators))
							b.Do(SplitConj(
								Case(
									"addition is preserved",
									Derive(func(d *Argument) {
										representation := d.Have(
											"the sum has the common denominator representation",
											"L.mul(L.add(y, z), ι(R.mul(s, t))) = ι(R.add(R.mul(a, t), R.mul(c, s)))",
											Simp(Fwd(ring_homomorphism.MapAdd.Read(ιHom)), Fwd(ring_homomorphism.MapMul.Read(ιHom))),
											ByArith(
												localizationRing,
												members,
												localImages,
												Scaled(ι.Apply(t), yEquation),
												Scaled(ι.Apply(s), zEquation)))
										value := d.Have(
											"the chosen sum value satisfies that representation",
											"T.mul(h(L.add(y, z)), u(R.mul(s, t))) = u(R.add(R.mul(a, t), R.mul(c, s)))",
											By(
												localResults,
												productsIn,
												comm_ring.AddIn.Read(sourceRing),
												denominators,
												representation,
												values.At(
													d.TermAs[B]("L.add(y,z)"), d.TermAs[A]("R.add(R.mul(a,t),R.mul(c,s))"), d.TermAs[A]("R.mul(s,t)"))))
										sumValue := d.Have(
											"the sum of values satisfies the same representation",
											"T.mul(T.add(h(y), h(z)), u(R.mul(s, t))) = u(R.add(R.mul(a, t), R.mul(c, s)))",
											Simp(Fwd(ring_homomorphism.MapAdd.Read(hom)), Fwd(ring_homomorphism.MapMul.Read(hom))),
											ByArith(
												targetRing,
												mappedResults,
												targetImages,
												Scaled(u.Apply(t), yValue),
												Scaled(u.Apply(s), zValue)))
										d.Show(
											"cancel the common denominator for addition",
											By(
												targetRing,
												mappedResults,
												targetResults,
												commonUnit,
												value,
												sumValue,
												At(
													cancelUnit,
													T,
													d.TermAs[C]("h(L.add(y,z))"),
													d.TermAs[C]("T.add(h(y),h(z))"),
													d.TermAs[C]("u(R.mul(s,t))"))))
									})),
								Case(
									"multiplication is preserved",
									Derive(func(d *Argument) {
										representation := d.Have(
											"the product has the common denominator representation",
											"L.mul(L.mul(y, z), ι(R.mul(s, t))) = ι(R.mul(a, c))",
											Simp(Fwd(ring_homomorphism.MapMul.Read(ιHom))),
											ByArith(
												localizationRing,
												members,
												localImages,
												Scaled(d.TermAs[B]("L.mul(z,ι(t))"), yEquation),
												Scaled(ι.Apply(a), zEquation)))
										value := d.Have(
											"the chosen product value satisfies that representation",
											"T.mul(h(L.mul(y, z)), u(R.mul(s, t))) = u(R.mul(a, c))",
											By(
												localResults,
												productsIn,
												denominators,
												representation,
												values.At(d.TermAs[B]("L.mul(y,z)"), d.TermAs[A]("R.mul(a,c)"), d.TermAs[A]("R.mul(s,t)"))))
										productValue := d.Have(
											"the product of values satisfies the same representation",
											"T.mul(T.mul(h(y), h(z)), u(R.mul(s, t))) = u(R.mul(a, c))",
											Simp(Fwd(ring_homomorphism.MapMul.Read(hom))),
											ByArith(
												targetRing,
												mappedResults,
												targetImages,
												Scaled(d.TermAs[C]("T.mul(h(z),u(t))"), yValue),
												Scaled(u.Apply(a), zValue)))
										d.Show(
											"cancel the common denominator for multiplication",
											By(
												targetRing,
												mappedResults,
												targetResults,
												commonUnit,
												value,
												productValue,
												At(
													cancelUnit,
													T,
													d.TermAs[C]("h(L.mul(y,z))"),
													d.TermAs[C]("T.mul(h(y),h(z))"),
													d.TermAs[C]("u(R.mul(s,t))"))))
									})),
							))
						}))
					hHom := q.Have(
						"the chosen map is a ring homomorphism",
						"ring_homomorphism(L, T, h)",
						Unfold(ring_homomorphism.RingHomomorphism),
						By(localizationRing, targetRing, mapIn, operations, mapOne))
					q.Take(h)
					q.Do(SplitConj(
						Case(
							"the map is a homomorphism extending the coefficient map",
							By(agreement, hHom)),
						Case(
							"the extension is unique on the localization carrier",
							Derive(func(b *Argument) {
								k := b.FixAs[Fun[B, C]]("k")
								other := b.Assume()
								equal := b.Have(
									"the two maps agree on coefficient images",
									"∀a:A. a ∈ R.carrier ⇒ k(ι(a)) = h(ι(a))",
									By(Normalized, agreement, other))
								b.Show(
									"coefficient agreement determines the map on the localization",
									By(
										loc,
										hHom,
										other,
										equal,
										LocalizationHomomorphismExtensional.Inst(
											TypeBinder.BindA[A](), TypeBinder.BindB[B](), TypeBinder.BindC[C]()).At(
											R, S, L, ι, T, k, h)))
							})),
					))
				})
		}),
})}

// LocalizationIsomorphism — the two universal comparison maps have
// identity composites on their carriers, making the comparison an isomorphism.
var LocalizationIsomorphism = localizationIsomorphismThm{family.Add(registry.ProofEntry{
	Name: "LocalizationIsomorphism",
	Key:  "prop_f9f01c96abff301c",
	Build: family.Theorem(
		Statement{
			Binders: "∀R:ring_ops(A). ∀S:set(A). ∀L:ring_ops(B). ∀ι:(A → B). ∀M:ring_ops(C). ∀κ:(A → C).",
			Hypotheses: []string{
				"is_localization_on(R, S, L, ι)",
				"is_localization_on(R, S, M, κ)",
			},
			Conclusion: "∃h:(B → C). " +
				"    ring_isomorphism(L, M, h) ∧ " +
				"    (∀a:A. a ∈ R.carrier ⇒ h(ι(a)) = κ(a)) ∧ " +
				"    ring_isomorphism(M, L, inverse_on(L.carrier, h)) ∧ " +
				"    (∀a:A. a ∈ R.carrier ⇒ inverse_on(L.carrier, h, κ(a)) = ι(a)) ∧ " +
				"    (∀k:(B → C). " +
				"        ring_homomorphism(L, M, k) ∧ (∀a:A. a ∈ R.carrier ⇒ k(ι(a)) = κ(a)) ⇒ " +
				"        ∀y:B. y ∈ L.carrier ⇒ k(y) = h(y))",
		},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			S *Expr[Set[A]],
			L *Expr[RingOps[B]],
			ι *Arrow[A, B],
			M *Expr[RingOps[C]],
			κ *Arrow[A, C],
			assumptions Fact,
		) {
			localizations := a.Conjuncts(
				assumptions,
				"L is a localization",
				"M is a localization")
			locL, locM := localizations[0], localizations[1]
			data := a.Have(
				"both coefficient maps are homomorphisms and invert the denominators",
				"ring_homomorphism(R, L, ι) ∧ "+
					"(∀s:A. s ∈ S ⇒ ring_unit(L, ι(s))) ∧ "+
					"ring_homomorphism(R, M, κ) ∧ "+
					"(∀s:A. s ∈ S ⇒ ring_unit(M, κ(s)))",
				Unfold(IsLocalizationOnDef),
				Derive(func(b *Argument) {
					b.Show(
						"each is a clause of one of the two localizations",
						By(
							b.Hyp("ring_homomorphism(R, L, ι)"),
							b.Hyp("∀s:A. s ∈ S ⇒ ring_unit(L, ι(s))"),
							b.Hyp("ring_homomorphism(R, M, κ)"),
							b.Hyp("∀s:A. s ∈ S ⇒ ring_unit(M, κ(s))")))
				}))
			parts := a.Conjuncts(
				data,
				"ι preserves the ring operations",
				"ι inverts the denominators",
				"κ preserves the ring operations",
				"κ inverts the denominators")
			ιHom, ιUnits, κHom, κUnits := parts[0], parts[1], parts[2], parts[3]
			h, forward := a.ObtainAs[Fun[B, C]](
				"choose the universal map from L to M",
				"∃h:(B → C). "+
					"    ring_homomorphism(L, M, h) ∧ "+
					"    (∀a:A. a ∈ R.carrier ⇒ h(ι(a)) = κ(a)) ∧ "+
					"    (∀j:(B → C). "+
					"        ring_homomorphism(L, M, j) ∧ (∀a:A. a ∈ R.carrier ⇒ j(ι(a)) = κ(a)) ⇒ "+
					"        (∀y:B. y ∈ L.carrier ⇒ j(y) = h(y)))",
				By(κUnits, locL, κHom, LocalizationUniversal.At(R, S, L, ι, M, κ)))
			forwardParts := a.Conjuncts(
				forward,
				"h is a ring homomorphism",
				"h commutes with the coefficient maps",
				"h is unique on the carrier")
			hHom, hCoefficients, unique := forwardParts[0], forwardParts[1], forwardParts[2]
			k, reverse := a.ObtainAs[Fun[C, B]](
				"choose the universal map from M to L",
				"∃k:(C → B). ring_homomorphism(M, L, k) ∧ (∀a:A. a ∈ R.carrier ⇒ k(κ(a)) = ι(a))",
				By(ιUnits, locM, ιHom, LocalizationUniversal.At(R, S, M, κ, L, ι)))
			reverseParts := a.Conjuncts(
				reverse,
				"k is a ring homomorphism",
				"k commutes with the coefficient maps")
			kHom, kCoefficients := reverseParts[0], reverseParts[1]
			lRing := a.Have(
				"L is a commutative ring",
				"comm_ring_on(L)",
				By(ring_homomorphism.Source.Read(hHom)))
			mRing := a.Have(
				"M is a commutative ring",
				"comm_ring_on(M)",
				By(ring_homomorphism.Target.Read(κHom)))
			lIdentity := a.Have(
				"the identity of L is a ring homomorphism",
				"ring_homomorphism(L, L, λy:B. y)",
				By(ring_homomorphism.RingHomIdentity.Read(lRing)))
			mIdentity := a.Have(
				"the identity of M is a ring homomorphism",
				"ring_homomorphism(M, M, λz:C. z)",
				By(ring_homomorphism.RingHomIdentity.Read(mRing)))
			kh := a.TermAs[Fun[B, B]]("λy:B. k(h(y))")
			hk := a.TermAs[Fun[C, C]]("λz:C. h(k(z))")
			khHom := a.Have(
				"k composed with h is a ring endomorphism of L",
				"ring_homomorphism(L, L, λy:B. k(h(y)))",
				By(hHom, kHom, ring_homomorphism.RingHomCompose))
			hkHom := a.Have(
				"h composed with k is a ring endomorphism of M",
				"ring_homomorphism(M, M, λz:C. h(k(z)))",
				By(kHom, hHom, ring_homomorphism.RingHomCompose))
			khCoefficients := a.Have(
				"k composed with h fixes the coefficients in L",
				"∀a:A. a ∈ R.carrier ⇒ k(h(ι(a))) = ι(a)",
				By(Normalized, kCoefficients, hCoefficients))
			hkCoefficients := a.Have(
				"h composed with k fixes the coefficients in M",
				"∀a:A. a ∈ R.carrier ⇒ h(k(κ(a))) = κ(a)",
				By(Normalized, kCoefficients, hCoefficients))
			leftInverse := a.Have(
				"k composed with h is the identity on L",
				"∀y:B. y ∈ L.carrier ⇒ k(h(y)) = y",
				Derive(func(b *Argument) {
					y := b.FixAs[B]("y")
					yIn := b.Assume()
					b.Show(
						"coefficient agreement determines this value on L",
						By(
							khCoefficients,
							yIn,
							locL,
							lIdentity,
							khHom,
							LocalizationHomomorphismExtensional.At(R, S, L, ι, L, kh, b.TermAs[Fun[B, B]]("λy:B. y"), y)))
				}))
			rightInverse := a.Have(
				"h composed with k is the identity on M",
				"∀z:C. z ∈ M.carrier ⇒ h(k(z)) = z",
				Derive(func(b *Argument) {
					z := b.FixAs[C]("z")
					zIn := b.Assume()
					b.Show(
						"coefficient agreement determines this value on M",
						By(
							hkCoefficients,
							zIn,
							locM,
							mIdentity,
							hkHom,
							LocalizationHomomorphismExtensional.At(R, S, M, κ, M, hk, b.TermAs[Fun[C, C]]("λz:C. z"), z)))
				}))
			lCarrier, mCarrier := a.TermAs[Set[B]]("L.carrier"), a.TermAs[Set[C]]("M.carrier")
			bijection := a.Have(
				"the two inverse laws make h a bijection of carriers",
				"injective_on(L.carrier, h) ∧ image(h, L.carrier) = M.carrier",
				By(
					ring_homomorphism.MapIn.Read(hHom),
					ring_homomorphism.MapIn.Read(kHom),
					leftInverse,
					rightInverse,
					functions.TwoSidedInverseBijection.At(lCarrier, mCarrier, h, k)))
			bijectionParts := a.Conjuncts(
				bijection,
				"h is one-to-one on L",
				"and carries L onto M")
			isomorphism := a.Have(
				"the bijective homomorphism is an isomorphism",
				"ring_isomorphism(L, M, h)",
				Unfold(ring_homomorphism.RingIsomorphismDef),
				By(hHom, bijectionParts[0], bijectionParts[1]))
			inverseIsomorphism := a.Have(
				"the named inverse is an isomorphism from M to L",
				"ring_isomorphism(M, L, inverse_on(L.carrier, h))",
				By(isomorphism, ring_homomorphism.IsomorphismInverse))
			inverseCoefficients := a.Have(
				"the named inverse returns each coefficient image",
				"∀a:A. a ∈ R.carrier ⇒ inverse_on(L.carrier, h, κ(a)) = ι(a)",
				By(
					Normalized,
					ring_homomorphism.MapIn.Read(ιHom),
					hCoefficients,
					bijection,
					functions.InverseOnLeft.Inst(TypeBinder.BindA[B](), TypeBinder.BindB[C]()).At(lCarrier, h)))
			a.Take(h)
			a.Show(
				"h and its named inverse commute with coefficients, and h is unique on L",
				By(inverseCoefficients, hCoefficients, unique, isomorphism, inverseIsomorphism))
		}),
})}

// LocalizationAtProduct — localizing at the powers of f and then at the
// powers of the image of g is localizing at the powers of f · g: combine
// the two fraction representations and pad their denominators to a
// common power of the product.
var LocalizationAtProduct = localizationAtProductThm{family.Add(registry.ProofEntry{
	Name: "LocalizationAtProduct",
	Key:  "prop_30420eaaaea2b75f",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀L:ring_ops(B). ∀M:ring_ops(C). ∀ι:(A → B). ∀κ:(B → C). ∀f g:A.",
		Hypotheses: []string{
			"f ∈ R.carrier",
			"g ∈ R.carrier",
			"is_localization_on(R, monoid_powers(R.mul, R.one, f), L, ι)",
			"is_localization_on(L, monoid_powers(L.mul, L.one, ι(g)), M, κ)",
		},
		Conclusion: "is_localization_on(R, monoid_powers(R.mul, R.one, R.mul(f, g)), M, λa:A. κ(ι(a)))",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			L *Expr[RingOps[B]],
			M *Expr[RingOps[C]],
			ι *Arrow[A, B],
			κ *Arrow[B, C],
			f, g *Expr[A],
			assumptions Fact,
		) {
			a.Do(Unfold(IsLocalizationOnDef))
			fIn, gIn := a.Hyp("f ∈ R.carrier"), a.Hyp("g ∈ R.carrier")
			ιHom := a.Hyp("ring_homomorphism(R, L, ι)")
			κHom := a.Hyp("ring_homomorphism(L, M, κ)")
			unitsR := a.Hyp("∀s:A. s ∈ monoid_powers(R.mul, R.one, f) ⇒ ring_unit(L, ι(s))")
			unitsL := a.Hyp("∀s:B. s ∈ monoid_powers(L.mul, L.one, ι(g)) ⇒ ring_unit(M, κ(s))")
			fractionsR := a.Hyp(Statement{
				Binders: "∀y:B.",
				Hypotheses: []string{
					"y ∈ L.carrier",
				},
				Conclusion: "∃a s:A. a ∈ R.carrier ∧ s ∈ monoid_powers(R.mul, R.one, f) ∧ L.mul(y, ι(s)) = ι(a)",
			})
			fractionsL := a.Hyp(Statement{
				Binders: "∀y:C.",
				Hypotheses: []string{
					"y ∈ M.carrier",
				},
				Conclusion: "∃a s:B. a ∈ L.carrier ∧ s ∈ monoid_powers(L.mul, L.one, ι(g)) ∧ M.mul(y, κ(s)) = κ(a)",
			})
			kernelR := a.Hyp(Statement{
				Binders: "∀a:A.",
				Hypotheses: []string{
					"a ∈ R.carrier",
					"ι(a) = L.zero",
				},
				Conclusion: "∃s:A. s ∈ monoid_powers(R.mul, R.one, f) ∧ R.mul(s, a) = R.zero",
			})
			kernelL := a.Hyp(Statement{
				Binders: "∀a:B.",
				Hypotheses: []string{
					"a ∈ L.carrier",
					"κ(a) = M.zero",
				},
				Conclusion: "∃s:B. s ∈ monoid_powers(L.mul, L.one, ι(g)) ∧ L.mul(s, a) = L.zero",
			})
			ringR := a.Have(
				"R is a commutative ring",
				"comm_ring_on(R)",
				By(ring_homomorphism.Source.Read(ιHom)))
			ringL := a.Have(
				"L is a commutative ring",
				"comm_ring_on(L)",
				By(ring_homomorphism.Target.Read(ιHom)))
			ringM := a.Have(
				"M is a commutative ring",
				"comm_ring_on(M)",
				By(ring_homomorphism.Target.Read(κHom)))
			fgIn := a.Have(
				"the product of the generators belongs to R",
				"R.mul(f, g) ∈ R.carrier",
				By(fIn, gIn, comm_ring.MulIn.Read(ringR)))
			compositeHom := a.Have(
				"the composite is a ring homomorphism",
				"ring_homomorphism(R, M, λa:A. κ(ι(a)))",
				By(ιHom, κHom, ring_homomorphism.RingHomCompose))
			fg := a.TermAs[A]("R.mul(f,g)")
			monoidR := comm_ring.MulMonoidOn.Read(ringR)
			padPowers := a.Have(
				"a power of f · g pads into powers of f and of g",
				"∀m n:num. "+
					"    monoid_pow(R.mul, R.one, R.mul(f, g), m + n) = "+
					"    R.mul(R.mul(monoid_pow(R.mul, R.one, f, m), monoid_pow(R.mul, R.one, g, n)), "+
					"        R.mul(monoid_pow(R.mul, R.one, f, n), monoid_pow(R.mul, R.one, g, m)))",
				Derive(func(b *Argument) {
					b.FixAs[Nat]("m")
					b.FixAs[Nat]("n")
					b.Show(
						"expand the power of the product and regroup the four factors",
						Simp(Fwd(comm_monoid.MulPowOn.Read(monoidR)), Fwd(comm_monoid.PowAddOn.Read(monoidR))),
						ByArith(ringR, fIn, gIn))
				}))
			a.Do(SplitConjAll(
				Case(
					"powers of the product form a multiplicative set",
					By(fgIn, PowersMultiplicative.Read(ringR))),
				Case(
					"the composite preserves the ring structure",
					By(compositeHom)),
				Case(
					"every product power has a unit image",
					Derive(func(b *Argument) {
						fPower := b.Have(
							"f is its own first power",
							"f ∈ monoid_powers(R.mul, R.one, f)",
							BySets(fIn, comm_monoid.PowOneOn.Read(monoidR), comm_monoid.MonoidPowersDef))
						igPower := b.Have(
							"the image of g is its own first power",
							"ι(g) ∈ monoid_powers(L.mul, L.one, ι(g))",
							Derive(func(c *Argument) {
								exponent := c.Have(
									"one represents the generator",
									"∃n:num. ι(g)=monoid_pow(L.mul, L.one, ι(g), n)",
									Witness(c.TermAs[Nat]("1")),
									By(
										gIn,
										ring_homomorphism.MapIn.Read(ιHom),
										comm_monoid.PowOneOn.Read(comm_ring.MulMonoidOn.Read(ringL))))
								c.Show(
									"the exponent witnesses membership",
									BySets(exponent, comm_monoid.MonoidPowersDef.Inst[B]()))
							}))
						fUnit := b.Have(
							"the first localization inverts f, and the second homomorphism preserves this unit",
							"ring_unit(M, κ(ι(f)))",
							By(fPower, unitsR.At(f), ring_homomorphism.MapUnit.Read(κHom)))
						gUnit := b.Have(
							"the second localization inverts the image of g",
							"ring_unit(M, κ(ι(g)))",
							By(igPower, unitsL.At(ι.Apply(g))))
						productUnit := b.Have(
							"the product generator has a unit image",
							"ring_unit(M, κ(ι(R.mul(f, g))))",
							Derive(func(c *Argument) {
								productImage := c.Have(
									"the composite preserves the generator product",
									"κ(ι(R.mul(f,g)))=M.mul(κ(ι(f)),κ(ι(g)))",
									By(
										fIn,
										gIn,
										ring_homomorphism.MapMul.Read(compositeHom).At(proof.MemberOf(f, fIn), proof.MemberOf(g, gIn))))
								c.Do(productImage.Rw())
								c.Show(
									"a product of units is a unit",
									By(fUnit, gUnit, ring_ideal.RingUnitMul.Read(ringM).At(κ.Apply(ι.Apply(f)), κ.Apply(ι.Apply(g)))))
							}))
						b.FixAs[A]("s")
						denominator := b.Assume()
						n, exponent := b.ObtainAs[Nat](
							"choose the exponent of the denominator",
							"∃n:num. s=monoid_pow(R.mul, R.one, R.mul(f, g), n)",
							BySets(denominator, comm_monoid.MonoidPowersDef))
						imagePower := b.Have(
							"the composite preserves this power",
							"κ(ι(monoid_pow(R.mul, R.one, R.mul(f, g), n)))=monoid_pow(M.mul, M.one, κ(ι(R.mul(f, g))), n)",
							By(ring_homomorphism.RingMapPower.Read(compositeHom).At(n, proof.MemberOf(fg, fgIn))))
						b.Do(exponent.Rw(), imagePower.Rw())
						b.Show(
							"powers of a unit are units",
							By(productUnit, ring_ideal.RingUnitPow.Read(ringM).At(κ.Apply(ι.Apply(fg)), n)))
					})),
				Case(
					"every target element has a fraction over powers of the product",
					Derive(func(b *Argument) {
						y := b.FixAs[C]("y")
						yIn := b.Assume()
						l, _, second := b.Obtain2As[B, B](
							"choose a fraction in the second localization",
							"∃l t:B. l ∈ L.carrier ∧ t ∈ monoid_powers(L.mul, L.one, ι(g)) ∧ M.mul(y, κ(t))=κ(l)",
							By(yIn, fractionsL.At(y)))
						secondParts := b.Conjuncts(
							second,
							"the intermediate numerator belongs to L",
							"the second denominator is a power",
							"the second fraction equation")
						lIn, tIn := secondParts[0], secondParts[1]
						n, tPower := b.ObtainAs[Nat](
							"choose the second exponent",
							"∃n:num. t=monoid_pow(L.mul, L.one, ι(g), n)",
							BySets(tIn, comm_monoid.MonoidPowersDef.Inst[B]()))
						numerator, _, first := b.Obtain2As[A, A](
							"represent the intermediate numerator over R",
							"∃a s:A. a ∈ R.carrier ∧ s ∈ monoid_powers(R.mul, R.one, f) ∧ L.mul(l, ι(s))=ι(a)",
							By(lIn, fractionsR.At(l)))
						firstParts := b.Conjuncts(
							first,
							"the numerator belongs to R",
							"the first denominator is a power",
							"the first fraction equation")
						numeratorIn, sIn := firstParts[0], firstParts[1]
						m, sPower := b.ObtainAs[Nat](
							"choose the first exponent",
							"∃m:num. s=monoid_pow(R.mul, R.one, f, m)",
							BySets(sIn, comm_monoid.MonoidPowersDef))
						mapG := b.Have(
							"ι preserves the needed power of g",
							"ι(monoid_pow(R.mul, R.one, g, n))=monoid_pow(L.mul, L.one, ι(g), n)",
							By(ring_homomorphism.RingMapPower.Read(ιHom).At(n, proof.MemberOf(g, gIn))))
						b.Do(sPower.Rw(), tPower.Rw(), mapG.RwRev())
						firstEquation := b.Hyp("L.mul(l, ι(monoid_pow(R.mul, R.one, f, m)))=ι(a)")
						secondEquation := b.Hyp("M.mul(y, κ(ι(monoid_pow(R.mul, R.one, g, n))))=κ(l)")
						fm := b.TermAs[A]("monoid_pow(R.mul, R.one, f, m)")
						gn := b.TermAs[A]("monoid_pow(R.mul, R.one, g, n)")
						fmIn := b.Have(
							"the first denominator power belongs to R",
							"monoid_pow(R.mul, R.one, f, m) ∈ R.carrier",
							By(fIn, comm_monoid.PowIn.Read(monoidR)))
						gnIn := b.Have(
							"the second denominator power belongs to R",
							"monoid_pow(R.mul, R.one, g, n) ∈ R.carrier",
							By(gIn, comm_monoid.PowIn.Read(monoidR)))
						ifmIn := b.Have(
							"the first denominator image belongs to L",
							"ι(monoid_pow(R.mul, R.one, f, m)) ∈ L.carrier",
							By(fmIn, ring_homomorphism.MapIn.Read(ιHom)))
						mappedFirst := b.Have(
							"map the first fraction equation through κ",
							"M.mul(κ(l), κ(ι(monoid_pow(R.mul, R.one, f, m))))=κ(ι(a))",
							By(
								lIn,
								ifmIn,
								firstEquation,
								ring_homomorphism.MapMul.Read(κHom).At(proof.MemberOf(l, lIn), proof.MemberOf(ι.Apply(fm), ifmIn))))
						productImage := b.Have(
							"the composite preserves the denominator product",
							"κ(ι(R.mul(monoid_pow(R.mul, R.one, f, m), monoid_pow(R.mul, R.one, g, n))))=M.mul( "+
								"    κ(ι(monoid_pow(R.mul, R.one, f, m))), κ(ι(monoid_pow(R.mul, R.one, g, n))))",
							By(
								fmIn,
								gnIn,
								ring_homomorphism.MapMul.Read(compositeHom).At(proof.MemberOf(fm, fmIn), proof.MemberOf(gn, gnIn))))
						combined := b.Have(
							"combine the two fraction equations",
							"M.mul(y, κ(ι(R.mul(monoid_pow(R.mul, R.one, f, m), monoid_pow(R.mul, R.one, g, n)))))=κ(ι(a))",
							productImage.Rw(),
							CalcEq(
								Leg(
									b.TermAs[C](
										"M.mul(M.mul(y, κ(ι(monoid_pow(R.mul, R.one, g, n)))), κ(ι(monoid_pow(R.mul, R.one, f, m))))"),
									"move the first denominator beside the second fraction",
									ByArith(ringM, yIn, fmIn, ring_homomorphism.MapIn.Read(compositeHom), gnIn)),
								FinalLeg(
									"use the second equation and then the mapped first equation",
									By(secondEquation, mappedFirst)),
							))
						pad := b.TermAs[A]("R.mul(monoid_pow(R.mul, R.one, f, n), monoid_pow(R.mul, R.one, g, m))")
						denominator := b.TermAs[A]("R.mul(monoid_pow(R.mul, R.one, f, m), monoid_pow(R.mul, R.one, g, n))")
						padIn := b.Have(
							"the complementary product belongs to R",
							"R.mul(monoid_pow(R.mul, R.one, f, n), monoid_pow(R.mul, R.one, g, m)) ∈ R.carrier",
							By(fIn, comm_monoid.PowIn.Read(monoidR), gIn, comm_ring.MulIn.Read(ringR)))
						denominatorIn := b.Have(
							"the combined denominator belongs to R",
							"R.mul(monoid_pow(R.mul, R.one, f, m), monoid_pow(R.mul, R.one, g, n)) ∈ R.carrier",
							By(fmIn, gnIn, comm_ring.MulIn.Read(ringR)))
						padding := b.Have(
							"padding completes the product power",
							"monoid_pow(R.mul, R.one, R.mul(f, g), m+n)=R.mul( "+
								"    R.mul(monoid_pow(R.mul, R.one, f, m), monoid_pow(R.mul, R.one, g, n)), "+
								"    R.mul(monoid_pow(R.mul, R.one, f, n), monoid_pow(R.mul, R.one, g, m)))",
							By(padPowers.At(m, n)))
						paddedImage := b.Have(
							"the composite preserves multiplication by the padding",
							"κ(ι(R.mul(R.mul(monoid_pow(R.mul, R.one, f, m), monoid_pow(R.mul, R.one, g, n)), R.mul(monoid_pow(R.mul, R.one, f, n), monoid_pow(R.mul, R.one, g, m)))))=M.mul( "+
								"    κ(ι(R.mul(monoid_pow(R.mul, R.one, f, m), monoid_pow(R.mul, R.one, g, n)))), "+
								"    κ(ι(R.mul(monoid_pow(R.mul, R.one, f, n), monoid_pow(R.mul, R.one, g, m)))))",
							By(
								denominatorIn,
								padIn,
								ring_homomorphism.MapMul.Read(compositeHom).At(
									proof.MemberOf(denominator, denominatorIn), proof.MemberOf(pad, padIn))))
						numeratorImage := b.Have(
							"the numerator scales by the same padding",
							"κ(ι(R.mul(a, R.mul(monoid_pow(R.mul, R.one, f, n), monoid_pow(R.mul, R.one, g, m)))))=M.mul( "+
								"    κ(ι(a)), κ(ι(R.mul(monoid_pow(R.mul, R.one, f, n), monoid_pow(R.mul, R.one, g, m)))))",
							By(
								numeratorIn,
								padIn,
								ring_homomorphism.MapMul.Read(compositeHom).At(
									proof.MemberOf(numerator, numeratorIn), proof.MemberOf(pad, padIn))))
						b.Take(
							b.TermAs[A]("R.mul(a, R.mul(monoid_pow(R.mul, R.one, f, n), monoid_pow(R.mul, R.one, g, m)))"))
						b.Take(b.TermAs[A]("monoid_pow(R.mul, R.one, R.mul(f, g), m+n)"))
						b.Do(SplitConjAll(
							Case(
								"the padded numerator belongs to R",
								By(numeratorIn, padIn, comm_ring.MulIn.Read(ringR))),
							Case(
								"the denominator is the power with exponent m plus n",
								BySets(comm_monoid.MonoidPowersDef)),
							Case(
								"the padded fraction represents the original element",
								padding.Rw(),
								paddedImage.Rw(),
								numeratorImage.Rw(),
								CalcEq(
									Leg(
										b.TermAs[C](
											"M.mul(M.mul(y, κ(ι(R.mul(monoid_pow(R.mul, R.one, f, m), monoid_pow(R.mul, R.one, g, n))))), "+
												"    κ(ι(R.mul(monoid_pow(R.mul, R.one, f, n), monoid_pow(R.mul, R.one, g, m)))))"),
										"associate the padding after the combined denominator",
										ByArith(ringM, yIn, denominatorIn, ring_homomorphism.MapIn.Read(compositeHom), padIn)),
									FinalLeg(
										"scale the combined fraction equation",
										By(combined)),
								)),
						))
					})),
				Case(
					"a product power annihilates every element killed by the composite",
					Derive(func(b *Argument) {
						element := b.FixAs[A]("a")
						killed := b.Assume()
						pieces := b.Conjuncts(
							killed,
							"the element belongs to R",
							"the composite kills the element")
						elementIn, killedImage := pieces[0], pieces[1]
						_, second := b.ObtainAs[B](
							"the second localization supplies an annihilator",
							"∃t:B. t ∈ monoid_powers(L.mul, L.one, ι(g)) ∧ L.mul(t, ι(a))=L.zero",
							By(elementIn, ring_homomorphism.MapIn.Read(ιHom), killedImage, kernelL.At(ι.Apply(element))))
						secondParts := b.Conjuncts(
							second,
							"the second annihilator is a power",
							"the second annihilation equation")
						n, tPower := b.ObtainAs[Nat](
							"choose the second annihilator exponent",
							"∃n:num. t=monoid_pow(L.mul, L.one, ι(g), n)",
							BySets(secondParts[0], comm_monoid.MonoidPowersDef.Inst[B]()))
						mapG := b.Have(
							"ι preserves the annihilator power of g",
							"ι(monoid_pow(R.mul, R.one, g, n))=monoid_pow(L.mul, L.one, ι(g), n)",
							By(ring_homomorphism.RingMapPower.Read(ιHom).At(n, proof.MemberOf(g, gIn))))
						b.Do(tPower.Rw(), mapG.RwRev())
						localZero := b.Hyp("L.mul(ι(monoid_pow(R.mul, R.one, g, n)), ι(a))=L.zero")
						gn := b.TermAs[A]("monoid_pow(R.mul, R.one, g, n)")
						gnIn := b.Have(
							"the power of g belongs to R",
							"monoid_pow(R.mul, R.one, g, n) ∈ R.carrier",
							By(gIn, comm_monoid.PowIn.Read(monoidR)))
						productIn := b.Have(
							"multiply the source element by this power",
							"R.mul(monoid_pow(R.mul, R.one, g, n), a) ∈ R.carrier",
							By(gnIn, elementIn, comm_ring.MulIn.Read(ringR)))
						firstZero := b.Have(
							"the resulting source product maps to zero",
							"ι(R.mul(monoid_pow(R.mul, R.one, g, n), a))=L.zero",
							By(
								gnIn,
								elementIn,
								localZero,
								ring_homomorphism.MapMul.Read(ιHom).At(
									proof.MemberOf(gn, gnIn), proof.MemberOf(element, elementIn))))
						_, first := b.ObtainAs[A](
							"the first localization supplies an annihilator",
							"∃s:A. "+
								"    s ∈ monoid_powers(R.mul, R.one, f) ∧ "+
								"    R.mul(s, R.mul(monoid_pow(R.mul, R.one, g, n), a))=R.zero",
							By(productIn, firstZero, kernelR.At(b.TermAs[A]("R.mul(monoid_pow(R.mul, R.one, g, n), a)"))))
						firstParts := b.Conjuncts(
							first,
							"the first annihilator is a power",
							"the first annihilation equation")
						m, sPower := b.ObtainAs[Nat](
							"choose the first annihilator exponent",
							"∃m:num. s=monoid_pow(R.mul, R.one, f, m)",
							BySets(firstParts[0], comm_monoid.MonoidPowersDef))
						b.Do(sPower.Rw())
						annihilation := b.Hyp(
							"R.mul(monoid_pow(R.mul, R.one, f, m), R.mul(monoid_pow(R.mul, R.one, g, n), a))=R.zero")
						padding := b.Have(
							"padding completes the annihilating product power",
							"monoid_pow(R.mul, R.one, R.mul(f, g), m+n)=R.mul( "+
								"    R.mul(monoid_pow(R.mul, R.one, f, m), monoid_pow(R.mul, R.one, g, n)), "+
								"    R.mul(monoid_pow(R.mul, R.one, f, n), monoid_pow(R.mul, R.one, g, m)))",
							By(padPowers.At(m, n)))
						b.Take(b.TermAs[A]("monoid_pow(R.mul, R.one, R.mul(f, g), m+n)"))
						b.Do(SplitConj(
							Case(
								"the annihilator is a power of the product",
								BySets(comm_monoid.MonoidPowersDef)),
							Case(
								"multiply the annihilation equation by the complementary powers",
								padding.Rw(),
								ByArith(
									ringR,
									elementIn,
									fIn,
									comm_monoid.PowIn.Read(monoidR),
									gnIn,
									gIn,
									Scaled(
										b.TermAs[A]("R.mul(monoid_pow(R.mul, R.one, f, n), monoid_pow(R.mul, R.one, g, m))"),
										annihilation))),
						))
					})),
			))
		}),
})}

// LocalizationAtUnits — extend the source identity across the localization;
// coefficient agreement makes the resulting reverse map a two-sided inverse.
var LocalizationAtUnits = localizationAtUnitsThm{family.Add(registry.ProofEntry{
	Name: "LocalizationAtUnits",
	Key:  "prop_454dbb102345580e",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀S:set(A). ∀L:ring_ops(B). ∀ι:(A → B).",
		Hypotheses: []string{
			"is_localization_on(R, S, L, ι)",
			"∀s:A. s ∈ S ⇒ ring_unit(R, s)",
		},
		Conclusion: "ring_isomorphism(R, L, ι)",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			S *Expr[Set[A]],
			L *Expr[RingOps[B]],
			ι *Arrow[A, B],
			assumptions Fact,
		) {
			premises := a.Conjuncts(
				assumptions,
				"L localizes R at S",
				"the denominators are already units in R")
			localization, units := premises[0], premises[1]
			ιHom := a.Have(
				"the original coefficient map is a ring homomorphism",
				"ring_homomorphism(R, L, ι)",
				Unfold(IsLocalizationOnDef))
			rIdentity := a.Have(
				"the identity of R is a ring homomorphism",
				"ring_homomorphism(R, R, λx:A. x)",
				By(ring_homomorphism.RingHomIdentity.Read(ring_homomorphism.Source.Read(ιHom))))
			h, reverse := a.ObtainAs[Fun[B, A]](
				"extend the identity of R across the localization",
				"∃h:(B → A). ring_homomorphism(L, R, h) ∧ (∀a:A. a ∈ R.carrier ⇒ h(ι(a)) = a)",
				By(
					units,
					localization,
					rIdentity,
					LocalizationUniversal.At(R, S, L, ι, R, a.TermAs[Fun[A, A]]("λx:A. x"))))
			reverseParts := a.Conjuncts(
				reverse,
				"h is a ring homomorphism",
				"h is a left inverse on R")
			hHom, leftInverse := reverseParts[0], reverseParts[1]
			lIdentity := a.Have(
				"the identity of L is a ring homomorphism",
				"ring_homomorphism(L, L, λy:B. y)",
				By(ring_homomorphism.RingHomIdentity.Read(ring_homomorphism.Target.Read(ιHom))))
			composite := a.TermAs[Fun[B, B]]("λy:B. ι(h(y))")
			compositeHom := a.Have(
				"ι composed with h is a ring endomorphism of L",
				"ring_homomorphism(L, L, λy:B. ι(h(y)))",
				By(hHom, ιHom, ring_homomorphism.RingHomCompose))
			coefficientAgreement := a.Have(
				"the composite fixes the coefficient images",
				"∀a:A. a ∈ R.carrier ⇒ ι(h(ι(a))) = ι(a)",
				Derive(func(b *Argument) {
					element := b.FixAs[A]("a")
					elementIn := b.Assume()
					b.Show(
						"apply ι to the left inverse equation",
						By(Normalized, elementIn, leftInverse.At(element)))
				}))
			rightInverse := a.Have(
				"the composite is the identity on L",
				"∀y:B. y ∈ L.carrier ⇒ ι(h(y)) = y",
				Derive(func(b *Argument) {
					y := b.FixAs[B]("y")
					yIn := b.Assume()
					b.Show(
						"coefficient agreement determines the value at y",
						By(
							coefficientAgreement,
							yIn,
							localization,
							lIdentity,
							compositeHom,
							LocalizationHomomorphismExtensional.At(
								R, S, L, ι, L, composite, b.TermAs[Fun[B, B]]("λy:B. y"), y)))
				}))
			bijection := a.Conjuncts(
				a.Have(
					"the inverse equations make the coefficient map a bijection",
					"injective_on(R.carrier, ι) ∧ image(ι, R.carrier) = L.carrier",
					By(
						ring_homomorphism.MapIn.Read(ιHom),
						ring_homomorphism.MapIn.Read(hHom),
						leftInverse,
						rightInverse,
						functions.TwoSidedInverseBijection.At(
							a.TermAs[Set[A]]("R.carrier"), a.TermAs[Set[B]]("L.carrier"), ι, h))),
				"ι is one-to-one on R",
				"and carries R onto L")
			a.Show(
				"the original coefficient map is a ring isomorphism",
				Unfold(ring_homomorphism.RingIsomorphismDef),
				By(ιHom, bijection[0], bijection[1]))
		}),
})}
