package galois_good_open

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_automorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/symmetric_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/twisted_counting"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/principal_ideal_domain"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_domain"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_evaluation"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_away"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// GroupKeepsChart — the Galois group of a good open holds the inverse of each
// of its members, and each member and its inverse keep the chart: the good open
// has every member map the chart onto itself.
var GroupKeepsChart = groupKeepsChartThm{family.Add(registry.ProofEntry{
	Name: "GroupKeepsChart",
	Key:  "prop_884e382a9f8c5f2c",
	Build: family.Theorem(Statement{
		Abbrev: Abbrev{
			{Name: "G", Text: "field_automorphisms(M, field_adjoin(M, k, {t}), L)"},
			{Name: "undo", Text: "permutation_map(permutation_inverse(s))"},
		},
		Binders: "∀M:field_on(A). ∀k L C:set(A). ∀t:A. ∀a:(num → A). ∀s:permutation(A).",
		Hypotheses: []string{
			"galois_good_open(M, k, L, t, C, a)",
			"s ∈ «G»",
		},
		Conclusion: "permutation_inverse(s) ∈ «G» ∧ " +
			"(∀y:A. y ∈ C ⇒ permutation_map(s, y) ∈ C ∧ «undo»(y) ∈ C)",
	}, func(
		arg *Argument,
		M field.FieldFact[on.M],
		k, L, C *Expr[Set[A]],
		t *Expr[A],
		a *Arrow[Nat, A],
		s *Expr[symmetric_group.Permutation[A]],
		good, inG Fact,
	) {
		base := arg.TermAs[Set[A]]("field_adjoin(M, k, {t})")
		automorphisms := arg.TermAs[Set[symmetric_group.Permutation[A]]]("«G»")
		permutations := arg.TermAs[group.GroupOps[symmetric_group.Permutation[A]]]("permutation_group")
		inverse := arg.TermAs[symmetric_group.Permutation[A]]("permutation_inverse(s)")
		mapsOnto := GoodOpenAutomorphismsKeepChart.Read(good)
		subgroupG := arg.Have(
			"G is a group of permutations",
			"subgroup(permutation_group, «G»)",
			By(field_automorphism.AutomorphismsSubgroup.Read(M).AsFact().At(base, L)))
		inverseIn := arg.Have(
			"so it holds the inverse of s",
			"permutation_inverse(s) ∈ «G»",
			By(inG, subgroupG, group.SubgroupInv.At(permutations, automorphisms, s)))
		keeps := arg.Have(
			"a map of C onto C keeps C",
			"∀y:A. y ∈ C ⇒ permutation_map(s, y) ∈ C ∧ «undo»(y) ∈ C",
			Derive(func(b *Argument) {
				b.FixAs[A]("y")
				inC := b.Assume()
				b.Show(
					"s and its inverse both map C onto C",
					BySets(mapsOnto.At(s), mapsOnto.At(inverse), inG, inverseIn, inC))
			}))
		arg.Show(
			"so G holds the inverse of s, and s and its inverse keep C",
			By(inverseIn, keeps))
	}),
})}

// AwayPowerFacts — what the powers of a nonzero g of K do on an extension L of
// K: they lie in K and are nonzero, they clear nothing out of L, and an
// automorphism over K moves a product with a member of K by moving the other
// factor alone.
var AwayPowerFacts = awayPowerFactsThm{family.Add(registry.ProofEntry{
	Name: "AwayPowerFacts",
	Key:  "prop_13a488c9f8c01319",
	Build: family.Theorem(Statement{
		Abbrev: Abbrev{
			{Name: "power", Text: "λn:num. monoid_pow(M.mul, M.one, g, n)"},
		},
		Binders: "∀M:field_on(A). ∀K L:set(A). ∀g:A.",
		Hypotheses: []string{
			"subfield(M, K)",
			"subfield(M, L)",
			"K ⊆ L",
			"g ∈ K",
			"g ≠ M.zero",
		},
		Conclusion: "(∀n:num. «power»(n) ∈ K ∧ «power»(n) ≠ M.zero) ∧ " +
			"(∀n:num. ∀x:A. x ∈ M.carrier ∧ «power»(n) * x ∈ L ⇒ x ∈ L) ∧ " +
			"(∀s:permutation(A). ∀h x:A. " +
			"    s ∈ field_automorphisms(M, K, L) ∧ h ∈ K ∧ x ∈ L ⇒ " +
			"    permutation_map(s, h * x) = h * permutation_map(s, x) ∧ permutation_map(s, x) ∈ L)",
	}, func(
		a *Argument,
		M field.FieldFact[on.M],
		K, L *Expr[Set[A]],
		g *Expr[A],
		subfieldK, subfieldL, KInL, gInK, nonzero Fact,
	) {
		ops := a.TermAs[FieldOps[A]]("M")
		ring := field.RingOn.Read(M)
		powers := comm_ring.MulMonoidOn.Read(ring)
		KInField := a.Have(
			"K lies in M",
			"K ⊆ M.carrier",
			By(subfieldK, field.SubfieldSubset.At(ops, K)))
		LInField := a.Have(
			"L lies in M",
			"L ⊆ M.carrier",
			By(subfieldL, field.SubfieldSubset.At(ops, L)))
		gm := a.MemberOf[on.M](g, a.Have(
			"g lies in M",
			"g ∈ M.carrier",
			BySets(gInK, KInField)))
		inverse := field.InvIn.Read(M).At(gm)
		onK := a.Have(
			"K is a ring under the operations of M",
			"comm_ring_on(restrict_ring(field_ring(M), K))",
			By(subfieldK, field.SubfieldCommRing.Read(M).At(K)))
		powerData := a.Have(
			"The powers of g lie in K and are nonzero",
			"∀n:num. «power»(n) ∈ K ∧ «power»(n) ≠ M.zero",
			a.ForEach(func(n *Expr[Nat]) Action {
				return By(
					gInK,
					nonzero,
					field.OneNotZeroOn.Read(M),
					field.MulLeftInverseOn.Read(M).At(gm),
					comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(onK)).AsFact().At(g, n),
					comm_monoid.PowInverseOn.Read(powers).At(inverse, gm, n),
					comm_ring.MulRightZeroOn.Read(ring).At(comm_monoid.PowIn.Read(powers).At(inverse, n)))
			}))
		shift := a.Have(
			"An automorphism moves h · x by moving x alone, for h in K, and it keeps L",
			Statement{
				Binders:    "∀s:permutation(A). ∀h x:A.",
				Hypotheses: []string{"s ∈ field_automorphisms(M, K, L)", "h ∈ K", "x ∈ L"},
				Conclusion: "permutation_map(s, h * x) = h * permutation_map(s, x) ∧ permutation_map(s, x) ∈ L",
			},
			Derive(func(b *Argument) {
				s := b.FixAs[symmetric_group.Permutation[A]]("s")
				h := b.FixAs[A]("h")
				x := b.FixAs[A]("x")
				given := b.Conjuncts(
					b.Assume(),
					"s is an automorphism",
					"h lies in K",
					"x lies in L")
				automorphism := b.Conjuncts(
					b.Have(
						"s permutes L, is multiplicative on L and fixes K",
						"s ∈ symmetric_group(L) ∧ "+
							"(∀u v:A. "+
							"    u ∈ L ∧ v ∈ L ⇒ "+
							"    permutation_map(s, u * v) = permutation_map(s, u) * permutation_map(s, v)) ∧ "+
							"(∀u:A. u ∈ K ⇒ permutation_map(s, u) = u)",
						BySets(given[0], field_automorphism.FieldAutomorphismsDef.At(ops, K, L))),
					"s permutes L",
					"s is multiplicative",
					"s fixes K")
				inL := b.Have(
					"h lies in L",
					"h ∈ L",
					BySets(given[1], KInL))
				b.Show(
					"s fixes h and keeps L",
					By(
						Normalized,
						given[1],
						given[2],
						inL,
						automorphism[1].At(h, x),
						automorphism[2].At(h),
						automorphism[0],
						symmetric_group.SymmetricGroupMapsInto.At(L, s, x)))
			}))
		descends := a.Have(
			"A member of M that a power of g brings into L lies in L",
			"∀n:num. ∀x:A. x ∈ M.carrier ∧ «power»(n) * x ∈ L ⇒ x ∈ L",
			Derive(func(b *Argument) {
				n := b.FixAs[Nat]("n")
				x := b.FixAs[A]("x")
				given := b.Conjuncts(
					b.Assume(),
					"x lies in M",
					"the product lies in L")
				xm := b.MemberOf[on.M](x, given[0])
				h, hIs := b.LetAs[A]("h", "«power»(n)")
				data := b.Conjuncts(
					b.Have(
						"The power lies in K and L and is nonzero",
						"h ∈ K ∧ h ∈ L ∧ h ≠ M.zero",
						BySets(hIs, powerData.At(n), KInL)),
					"h lies in K",
					"h lies in L",
					"h is nonzero")
				hm := b.MemberOf[on.M](h, b.Have(
					"h lies in M",
					"h ∈ M.carrier",
					BySets(data[1], LInField)))
				iv := field.InvIn.Read(M).At(hm)
				cancels := b.Have(
					"inv(h) inverts h",
					"M.inv(h) * h = M.one",
					By(data[2], hm, field.MulLeftInverseOn.Read(M).At(hm)))
				back := b.Have(
					"inv(h) undoes h on x",
					"M.inv(h) * (h * x) = x",
					ByArith(ring, Scaled(x, cancels), hm, iv, xm))
				inverseInL := b.Have(
					"inv(h) lies in L",
					"M.inv(h) ∈ L",
					By(subfieldL, data[1], field.SubfieldInv.At(ops, L, h)))
				b.Show(
					"so x is a product of members of L",
					By(
						Normalized,
						back,
						subfieldL,
						inverseInL,
						given[1],
						field.SubfieldMul.At(ops, L, b.TermAs[A]("M.inv(h)"), b.TermAs[A]("h * x"))))
			}))
		a.Show(
			"These are the three facts",
			By(powerData, descends, shift))
	}),
})}

// InvariantChartAway — inverting a member of K, which H fixes, commutes with
// taking the invariants of H: a power h of g brings x into C, and an
// automorphism moves h · x by moving x alone, so x is invariant exactly when
// h · x is, h being nonzero.
var InvariantChartAway = invariantChartAwayThm{family.Add(registry.ProofEntry{
	Name: "InvariantChartAway",
	Key:  "prop_abfb58725b7e4ea0",
	Build: family.Theorem(Statement{
		Abbrev: Abbrev{
			{Name: "away", Text: "ring_away(field_ring(M), C, g)"},
			{Name: "power", Text: "λn:num. monoid_pow(M.mul, M.one, g, n)"},
		},
		Binders: "∀M:field_on(A). ∀K L C:set(A). ∀H:set(permutation(A)). ∀g:A.",
		Hypotheses: []string{
			"subfield(M, K)",
			"subfield(M, L)",
			"K ⊆ L",
			"C ⊆ L",
			"H ⊆ field_automorphisms(M, K, L)",
			"g ∈ K",
			"g ≠ M.zero",
		},
		Conclusion: "invariant_chart(«away», H) = ring_away(field_ring(M), invariant_chart(C, H), g)",
	}, func(
		a *Argument,
		M field.FieldFact[on.M],
		K, L, C *Expr[Set[A]],
		H *Expr[Set[symmetric_group.Permutation[A]]],
		g *Expr[A],
		subfieldK, subfieldL, KInL, CInL, HInAutomorphisms, gInK, nonzero Fact,
	) {
		ops := a.TermAs[FieldOps[A]]("M")
		facts := a.Conjuncts(
			GroupPremises(subfieldK, subfieldL, KInL, gInK, nonzero, AwayPowerFacts.Read(M).At(K, L, g)),
			"the powers of g lie in K and are nonzero",
			"they clear nothing out of L",
			"automorphisms move a product by its other factor")
		powerData, descends, shifted := facts[0], facts[1], facts[2]
		KInField := a.Have(
			"K lies in M",
			"K ⊆ M.carrier",
			By(subfieldK, field.SubfieldSubset.At(ops, K)))
		LInField := a.Have(
			"L lies in M",
			"L ⊆ M.carrier",
			By(subfieldL, field.SubfieldSubset.At(ops, L)))
		shift := a.Have(
			"A member of H moves h · x by moving x alone, for h in K, and it keeps L",
			Statement{
				Binders:    "∀s:permutation(A). ∀h x:A.",
				Hypotheses: []string{"s ∈ H", "h ∈ K", "x ∈ L"},
				Conclusion: "permutation_map(s, h * x) = h * permutation_map(s, x) ∧ permutation_map(s, x) ∈ L",
			},
			Derive(func(b *Argument) {
				s := b.FixAs[symmetric_group.Permutation[A]]("s")
				h := b.FixAs[A]("h")
				x := b.FixAs[A]("x")
				given := b.Conjuncts(
					b.Assume(),
					"s lies in H",
					"h lies in K",
					"x lies in L")
				inAutomorphisms := b.Have(
					"s is an automorphism over K",
					"s ∈ field_automorphisms(M, K, L)",
					BySets(given[0], HInAutomorphisms))
				b.Show(
					"so the fact applies",
					By(inAutomorphisms, given[1], given[2], shifted.At(s, h, x)))
			}))
		domain := integral_domain.FieldIntegralDomain.Read(M)
		member := a.Have(
			"The invariant chart is its invariant members",
			"∀X:set(A). ∀x:A. "+
				"    x ∈ invariant_chart(X, H) ⇔ x ∈ X ∧ (∀s:permutation(A). s ∈ H ⇒ permutation_map(s, x) = x)",
			Unfold(InvariantChartDef),
			SetTac())
		away := a.TermAs[Set[A]]("«away»")
		a.Do(Simp(Fwd(set_basic.Extension)))
		x := a.FixAs[A]("x")
		a.Iff()
		a.Forward(
			"an invariant x makes its clearing invariant",
			func(c *Argument, inChart Fact) {
				parts := c.Conjuncts(
					c.Have(
						"x lies in C with g inverted, and H fixes it",
						"x ∈ «away» ∧ (∀s:permutation(A). s ∈ H ⇒ permutation_map(s, x) = x)",
						By(inChart, member.At(away, x))),
					"x lies in C with g inverted",
					"H fixes x")
				opened := c.Conjuncts(
					c.Simplified(parts[0], Fwd(ring_away.RingAwayMember)),
					"x lies in M",
					"a power of g brings it into C")
				n, cleared := c.UnpackAs[Nat](opened[1], "n")
				hInK := c.Have(
					"The power lies in K",
					"«power»(n) ∈ K",
					By(powerData.At(n)))
				inL := c.Have(
					"x lies in L",
					"x ∈ L",
					BySets(opened[0], cleared, CInL, descends.At(n, x)))
				fixed := c.Have(
					"H fixes the clearing",
					"∀s:permutation(A). s ∈ H ⇒ permutation_map(s, «power»(n) * x) = «power»(n) * x",
					Derive(func(d *Argument) {
						t := d.FixAs[symmetric_group.Permutation[A]]("s")
						inH := d.Assume()
						d.Show(
							"s moves x alone, and it fixes x",
							By(inH, hInK, inL, shift.At(t, d.TermAs[A]("«power»(n)"), x), parts[1].At(t)))
					}))
				invariant := c.Have(
					"so the clearing lies in the invariant chart of C",
					"∃j:num. «power»(j) * x ∈ invariant_chart(C, H)",
					Witness(n),
					By(cleared, fixed, member.At(C, c.TermAs[A]("«power»(n) * x"))))
				c.Show(
					"and x lies in that chart with g inverted",
					Simp(Fwd(ring_away.RingAwayMember)),
					By(opened[0], invariant))
			})
		a.Backward(
			"an invariant clearing makes x invariant",
			func(c *Argument, inAway Fact) {
				opened := c.Conjuncts(
					c.Simplified(inAway, Fwd(ring_away.RingAwayMember)),
					"x lies in M",
					"a power of g brings x into the invariant chart of C")
				xm := c.MemberOf[on.M](x, opened[0])
				n, cleared := c.UnpackAs[Nat](opened[1], "n")
				product := c.TermAs[A]("«power»(n) * x")
				data := c.Conjuncts(
					c.Have(
						"The clearing lies in C and H fixes it",
						"«power»(n) * x ∈ C ∧ "+
							"(∀s:permutation(A). s ∈ H ⇒ permutation_map(s, «power»(n) * x) = «power»(n) * x)",
						By(cleared, member.At(C, product))),
					"the clearing lies in C",
					"H fixes the clearing")
				power := c.Conjuncts(
					c.Have(
						"The power lies in K and is nonzero",
						"«power»(n) ∈ K ∧ «power»(n) ≠ M.zero",
						By(powerData.At(n))),
					"it lies in K",
					"it is nonzero")
				hm := c.MemberOf[on.M](c.TermAs[A]("«power»(n)"), c.Have(
					"The power lies in M",
					"«power»(n) ∈ M.carrier",
					BySets(power[0], KInField)))
				productInL := c.Have(
					"The clearing lies in L",
					"«power»(n) * x ∈ L",
					BySets(data[0], CInL))
				inL := c.Have(
					"x lies in L",
					"x ∈ L",
					By(opened[0], productInL, descends.At(n, x)))
				fixed := c.Have(
					"H fixes x, the power being nonzero",
					"∀s:permutation(A). s ∈ H ⇒ permutation_map(s, x) = x",
					Derive(func(d *Argument) {
						t := d.FixAs[symmetric_group.Permutation[A]]("s")
						inH := d.Assume()
						moved := d.Have(
							"The moved point stays in M",
							"permutation_map(s, x) ∈ M.carrier",
							BySets(inH, inL, power[0], shift.At(t, d.TermAs[A]("«power»(n)"), x), LInField))
						movedMember := d.MemberOf[on.M](d.TermAs[A]("permutation_map(s, x)"), moved)
						same := d.Have(
							"Its product with the power is the clearing",
							"«power»(n) * permutation_map(s, x) = «power»(n) * x",
							By(inH, power[0], inL, shift.At(t, d.TermAs[A]("«power»(n)"), x), data[1].At(t)))
						d.Show(
							"so it is x",
							By(
								same,
								power[1],
								hm,
								xm,
								movedMember,
								integral_domain.MulCancelLeft.Read(domain).At(hm, movedMember, xm)))
					}))
				clears := c.Have(
					"x lies in C with g inverted",
					"x ∈ «away»",
					Simp(Fwd(ring_away.RingAwayMember)),
					Derive(func(d *Argument) {
						bringsIn := d.Have(
							"a power of g brings x into C",
							"∃j:num. «power»(j) * x ∈ C",
							Witness(n),
							By(data[0]))
						d.Show(
							"and x lies in M",
							By(opened[0], bringsIn))
					}))
				c.Show(
					"so x is an invariant member",
					By(clears, fixed, member.At(away, x)))
			})
	}),
})}

// AutomorphismKeepsAway — inverting a nonzero member of K in a subset C of L
// stays in L, and an automorphism over K keeping C keeps C with g inverted: it
// moves the clearing of y by moving y alone.
var AutomorphismKeepsAway = automorphismKeepsAwayThm{family.Add(registry.ProofEntry{
	Name: "AutomorphismKeepsAway",
	Key:  "prop_9c94b9e043ca8d8",
	Build: family.Theorem(Statement{
		Abbrev: Abbrev{
			{Name: "away", Text: "ring_away(field_ring(M), C, g)"},
			{Name: "power", Text: "λn:num. monoid_pow(M.mul, M.one, g, n)"},
		},
		Binders: "∀M:field_on(A). ∀K L C:set(A). ∀g:A.",
		Hypotheses: []string{
			"subfield(M, K)",
			"subfield(M, L)",
			"K ⊆ L",
			"C ⊆ L",
			"g ∈ K",
			"g ≠ M.zero",
		},
		Conclusion: "«away» ⊆ L ∧ " +
			"(∀s:permutation(A). " +
			"    s ∈ field_automorphisms(M, K, L) ∧ (∀y:A. y ∈ C ⇒ permutation_map(s, y) ∈ C) ⇒ " +
			"    ∀y:A. y ∈ «away» ⇒ permutation_map(s, y) ∈ «away»)",
	}, func(
		a *Argument,
		M field.FieldFact[on.M],
		K, L, C *Expr[Set[A]],
		g *Expr[A],
		subfieldK, subfieldL, KInL, CInL, gInK, nonzero Fact,
	) {
		ops := a.TermAs[FieldOps[A]]("M")
		facts := a.Conjuncts(
			GroupPremises(subfieldK, subfieldL, KInL, gInK, nonzero, AwayPowerFacts.Read(M).At(K, L, g)),
			"the powers of g lie in K and are nonzero",
			"they clear nothing out of L",
			"automorphisms move a product by its other factor")
		powerData, descends, shifted := facts[0], facts[1], facts[2]
		LInField := a.Have(
			"L lies in M",
			"L ⊆ M.carrier",
			By(subfieldL, field.SubfieldSubset.At(ops, L)))
		inL := a.Have(
			"A member of C with g inverted lies in L",
			"«away» ⊆ L",
			Derive(func(b *Argument) {
				b.Do(Simp(Fwd(set_basic.SubsetDef)))
				y := b.FixAs[A]("y")
				inAway := b.Assume()
				opened := b.Conjuncts(
					b.Simplified(inAway, Fwd(ring_away.RingAwayMember)),
					"y lies in M",
					"a power of g brings y into C")
				n, cleared := b.UnpackAs[Nat](opened[1], "n")
				productInL := b.Have(
					"The clearing lies in L",
					"«power»(n) * y ∈ L",
					BySets(cleared, CInL))
				b.Show(
					"so y lies in L",
					By(opened[0], productInL, descends.At(n, y)))
			}))
		keeps := a.Have(
			"An automorphism keeping C keeps C with g inverted",
			Statement{
				Binders:    "∀s:permutation(A).",
				Hypotheses: []string{"s ∈ field_automorphisms(M, K, L)", "∀y:A. y ∈ C ⇒ permutation_map(s, y) ∈ C"},
				Conclusion: "∀y:A. y ∈ «away» ⇒ permutation_map(s, y) ∈ «away»",
			},
			Derive(func(b *Argument) {
				s := b.FixAs[symmetric_group.Permutation[A]]("s")
				given := b.Conjuncts(
					b.Assume(),
					"s is an automorphism",
					"s keeps C")
				y := b.FixAs[A]("y")
				inAway := b.Assume()
				yInL := b.Have(
					"y lies in L",
					"y ∈ L",
					BySets(inAway, inL))
				opened := b.Conjuncts(
					b.Simplified(inAway, Fwd(ring_away.RingAwayMember)),
					"y lies in M",
					"a power of g brings y into C")
				n, cleared := b.UnpackAs[Nat](opened[1], "n")
				powerInK := b.Have(
					"The power lies in K",
					"«power»(n) ∈ K",
					By(powerData.At(n)))
				moved := b.Conjuncts(
					b.Have(
						"s moves the clearing by moving y alone",
						"permutation_map(s, «power»(n) * y) = «power»(n) * permutation_map(s, y) ∧ "+
							"permutation_map(s, y) ∈ L",
						By(given[0], powerInK, yInL, shifted.At(s, b.TermAs[A]("«power»(n)"), y))),
					"s moves the clearing",
					"the moved point stays in L")
				movedInField := b.Have(
					"The moved point lies in M",
					"permutation_map(s, y) ∈ M.carrier",
					BySets(moved[1], LInField))
				stillCleared := b.Have(
					"The same power clears it",
					"«power»(n) * permutation_map(s, y) ∈ C",
					By(cleared, moved[0], given[1].At(b.TermAs[A]("«power»(n) * y"))))
				clearing := b.Have(
					"so some power clears it",
					"∃j:num. «power»(j) * permutation_map(s, y) ∈ C",
					Witness(n),
					By(stillCleared))
				b.Show(
					"and it lies in C with g inverted",
					Simp(Fwd(ring_away.RingAwayMember)),
					By(movedInField, clearing))
			}))
		a.Show(
			"Both facts",
			By(inL, keeps))
	}),
})}

// groupKeepsAway reads, on a good open (C, a) with c(t) inverted, that each
// member s of G keeps the localization: s keeps C (GroupKeepsChart), and an
// automorphism keeping C keeps C with c(t) inverted (keepsAway,
// AutomorphismKeepsAway's second clause). The claim spells the parameters'
// letters M, k, L, C, t and c.
func groupKeepsAway(
	arg *Argument,
	M field.FieldFact[on.M],
	k, L, C *Expr[Set[A]],
	t *Expr[A],
	a, c *Arrow[Nat, A],
	good, keepsAway Fact,
) Fact {
	return arg.Have(
		"G keeps the localization",
		Statement{
			Binders: "∀s:permutation(A). ∀y:A.",
			Hypotheses: []string{
				"s ∈ field_automorphisms(M, field_adjoin(M, k, {t}), L)",
				"y ∈ ring_away(field_ring(M), C, polynomial_eval(c, t))",
			},
			Conclusion: "permutation_map(s, y) ∈ ring_away(field_ring(M), C, polynomial_eval(c, t))",
		},
		Derive(func(b *Argument) {
			s := b.FixAs[symmetric_group.Permutation[A]]("s")
			y := b.FixAs[A]("y")
			given := b.Conjuncts(
				b.Assume(),
				"s lies in G",
				"y lies in the localization")
			keeps := b.Have(
				"s keeps C",
				"∀u:A. u ∈ C ⇒ permutation_map(s, u) ∈ C",
				By(good, given[0], GroupKeepsChart.Read(M).At(k, L, C, t, a, s)))
			b.Show(
				"so it keeps the localization",
				By(given[0], given[1], keeps, keepsAway.At(s).At(y)))
		}))
}

// GoodFibreAway — the fibre of C with c(t) inverted over a good point keeps the
// torsor structure of the fibre of C. Restriction to C is a bijection of the
// fibres, compatible with the action of G, and a map of a set with an action
// that is injective and compatible carries each clause back. For a subgroup H,
// invariant_chart(C[1/c(t)], H) = invariant_chart(C, H)[1/c(t)]
// (InvariantChartAway), so restriction is a bijection there too.
var GoodFibreAway = goodFibreAwayThm{family.Add(registry.ProofEntry{
	Name: "GoodFibreAway",
	Key:  "prop_401ff03a24ef8ef9",
	Build: family.Theorem(Statement{
		Abbrev: Abbrev{
			{Name: "base", Text: "field_adjoin(M, k, {t})"},
			{Name: "G", Text: "field_automorphisms(M, «base», L)"},
			{Name: "away", Text: "ring_away(field_ring(M), C, polynomial_eval(c, t))"},
			{Name: "fibre", Text: "λX:set(A). geometric_fibre(M, k, X, t, x)"},
			{Name: "restriction", Text: "λev:(A → A). λy:A. COND(y ∈ C, ev(y), M.zero)"},
			{Name: "undo", Text: "λs:permutation(A). permutation_map(permutation_inverse(s))"},
		},
		Binders: "∀M:field_on(A). ∀k L C:set(A). ∀t x:A. ∀a c:(num → A).",
		Hypotheses: []string{
			"galois_good_open(M, k, L, t, C, a)",
			"polynomial_over(k, c)",
			"polynomial_eval(c, t) ≠ M.zero",
			"x ∈ algebraic_elements(M, k)",
			"polynomial_eval(a, x) ≠ M.zero",
			"polynomial_eval(c, x) ≠ M.zero",
		},
		Conclusion: "free_finite_action(galois_group(M, «base», L), " +
			"    «fibre»(«away»), " +
			"    evaluation_action(field_ring(M), «away»)) ∧ " +
			"card(«fibre»(«away»)) = card(«G») ∧ " +
			"(∀ev ew:(A → A). " +
			"    ev ∈ «fibre»(«away») ∧ ew ∈ «fibre»(«away») ⇒ " +
			"    ∃s:permutation(A). s ∈ «G» ∧ evaluation_action(field_ring(M), «away», s, ev) = ew) ∧ " +
			"(∀H:set(permutation(A)). " +
			"    subgroup(galois_group(M, «base», L), H) ⇒ " +
			"    image((λev:(A → A).(λy:A. COND(y ∈ invariant_chart(«away», H), ev(y), M.zero))), " +
			"        «fibre»(«away»)) = " +
			"    «fibre»(invariant_chart(«away», H)) ∧ " +
			"    (∀ev ew:(A → A). " +
			"        ev ∈ «fibre»(«away») ∧ ew ∈ «fibre»(«away») ⇒ " +
			"        ((∀y:A. y ∈ invariant_chart(«away», H) ⇒ ev(y) = ew(y)) ⇔ " +
			"            ∃s:permutation(A). s ∈ H ∧ evaluation_action(field_ring(M), «away», s, ev) = ew)))",
	}, func(
		arg *Argument,
		M field.FieldFact[on.M],
		k, L, C *Expr[Set[A]],
		t, x *Expr[A],
		a, c *Arrow[Nat, A],
		good, overK, valueNonzero, xInClosure, rootFreeA, rootFreeC Fact,
	) {
		ops := arg.TermAs[FieldOps[A]]("M")
		fieldRing := arg.TermAs[RingOps[A]]("field_ring(M)")
		ring := field.RingOn.Read(M)
		base := arg.TermAs[Set[A]]("«base»")
		value := arg.TermAs[A]("polynomial_eval(c, t)")
		away := arg.TermAs[Set[A]]("«away»")
		subfieldK := arg.Have(
			"k is a subfield",
			"subfield(M, k)",
			By(GoodOpenConstantsSubfield.Read(good)))
		subfieldL := arg.Have(
			"L is a subfield",
			"subfield(M, L)",
			By(GoodOpenFieldSubfield.Read(good)))
		subfieldBase := arg.Have(
			"k(t) is a subfield",
			"subfield(M, «base»)",
			By(good, GoodOpenRationalSubfield.Read(M).At(k, L, C, t, a)))
		kInBase, tInBase := GoodOpenConstantsInRational.Read(good), GoodOpenParameterInRational.Read(good)
		baseInL := arg.Have(
			"k(t) lies in L",
			"«base» ⊆ L",
			By(GoodOpenRationalInField.Read(good)))
		subringC := arg.Have(
			"C is a subring",
			"subring(field_ring(M), C)",
			By(good, GoodOpenChartSubring.Read(M).At(k, L, C, t, a)))
		CInL := arg.Have(
			"C lies in L",
			"C ⊆ L",
			By(GoodOpenChartInField.Read(good)))
		clause := ReadGoodFibre(arg, good, x, xInClosure, rootFreeA)
		kInC := arg.Have(
			"k lies in C",
			"k ⊆ C",
			By(good, GoodOpenConstantsInChart.Read(M).At(k, L, C, t, a)))
		tInC := arg.Have(
			"t lies in C",
			"t ∈ C",
			By(good, GoodOpenParameterInChart.Read(M).At(k, L, C, t, a)))
		valueInPolynomials := arg.Have(
			"c(t) lies in k[t]",
			"polynomial_eval(c, t) ∈ polynomial_image(field_ring(M), k, t)",
			BySets(overK, algebraic_element.PolynomialImageDef.At(fieldRing, k, t)))
		tm := GoodParameterInField(arg, t, good)
		valueInBase := arg.Have(
			"so it lies in k(t), which holds k[t]",
			"polynomial_eval(c, t) ∈ «base»",
			BySets(valueInPolynomials, subfieldK, algebraic_element.PolynomialImageRing.Read(M).At(k, tm)))
		valueInC := arg.Have(
			"and in C, which holds k[t]",
			"polynomial_eval(c, t) ∈ C",
			BySets(valueInPolynomials, good, GoodOpenPolynomialsInChart.Read(M).At(k, L, C, t, a)))
		awayRing := arg.Conjuncts(
			arg.Have(
				"C with c(t) inverted is a subring holding C",
				"C ⊆ «away» ∧ subring(field_ring(M), «away»)",
				By(ring, subringC, valueInC, ring_away.RingAwaySubring.At(fieldRing, C, value))),
			"C lies in the localization",
			"the localization is a subring")
		kInAway := arg.Have(
			"k lies in the localization",
			"k ⊆ «away»",
			BySets(kInC, awayRing[0]))
		tInAway := arg.Have(
			"t lies in the localization",
			"t ∈ «away»",
			BySets(tInC, awayRing[0]))
		awayKeeps := arg.Conjuncts(
			GroupPremises(
				subfieldBase,
				subfieldL,
				baseInL,
				CInL,
				valueInBase,
				valueNonzero,
				AutomorphismKeepsAway.Read(M).At(base, L, C, value)),
			"the localization lies in L",
			"an automorphism keeping C keeps the localization")
		bijection := arg.Conjuncts(
			GroupPremises(
				subringC,
				kInC,
				tInC,
				overK,
				valueNonzero,
				xInClosure,
				subfieldK,
				rootFreeC,
				FibreAway.Read(M).At(k, C, t, x, c)),
			"restriction is injective on the fibre of the localization",
			"its image is the fibre of C")
		fibreMember := arg.Have(
			"A map lies in the fibre of the localization when it is a geometric point of it over x",
			"∀ev:(A → A). ev ∈ «fibre»(«away») ⇔ ev ∈ geometric_evaluation_points(M, k, «away») ∧ ev(t) = x",
			BySets(GeometricFibreDef.At(ops, k, away, t, x)))
		permutations := arg.TermAs[group.GroupOps[symmetric_group.Permutation[A]]]("permutation_group")
		automorphisms := arg.TermAs[Set[symmetric_group.Permutation[A]]]("«G»")
		subgroupG := arg.Have(
			"G is a group of permutations",
			"subgroup(permutation_group, «G»)",
			By(field_automorphism.AutomorphismsSubgroup.Read(M).AsFact().At(base, L)))
		keepsAway := groupKeepsAway(arg, M, k, L, C, t, a, c, good, awayKeeps[1])
		fixesBase := arg.Have(
			"G fixes k(t)",
			"∀s:permutation(A). ∀y:A. s ∈ «G» ∧ y ∈ «base» ⇒ permutation_map(s, y) = y",
			Derive(func(b *Argument) {
				b.FixAs[symmetric_group.Permutation[A]]("s")
				b.FixAs[A]("y")
				given := b.Conjuncts(
					b.Assume(),
					"s lies in G",
					"y lies in k(t)")
				b.Show(
					"by the definition of G",
					BySets(given[0], given[1], field_automorphism.FieldAutomorphismsDef.At(ops, base, L)))
			}))
		pointActs := arg.Have(
			"G moves the fibre of the localization into itself",
			Statement{
				Binders:    "∀s:permutation(A). ∀ev:(A → A).",
				Hypotheses: []string{"s ∈ «G»", "ev ∈ «fibre»(«away»)"},
				Conclusion: "evaluation_action(field_ring(M), «away», s, ev) ∈ «fibre»(«away»)",
			},
			Derive(func(b *Argument) {
				s := b.FixAs[symmetric_group.Permutation[A]]("s")
				ev := b.FixAs[Fun[A, A]]("ev")
				given := b.Conjuncts(
					b.Assume(),
					"s lies in G",
					"ev lies in the fibre")
				data := b.Conjuncts(
					b.Have(
						"ev is a point of the localization over x",
						"ev ∈ geometric_evaluation_points(M, k, «away») ∧ ev(t) = x",
						By(given[1], fibreMember.At(ev))),
					"ev is a point",
					"ev(t) = x")
				inverse := b.TermAs[symmetric_group.Permutation[A]]("permutation_inverse(s)")
				inverseIn := b.Have(
					"The inverse of s lies in G",
					"permutation_inverse(s) ∈ «G»",
					By(good, given[0], GroupKeepsChart.Read(M).At(k, L, C, t, a, s)))
				keeps := b.Have(
					"The inverse of s keeps the localization",
					"∀y:A. y ∈ «away» ⇒ permutation_map(permutation_inverse(s), y) ∈ «away»",
					Derive(func(d *Argument) {
						y := d.FixAs[A]("y")
						inAway := d.Assume()
						d.Show(
							"as G does",
							By(inverseIn, inAway, keepsAway.At(inverse, y)))
					}))
				point := b.Have(
					"The action is a point of the localization",
					"evaluation_action(field_ring(M), «away», s, ev) ∈ geometric_evaluation_points(M, k, «away»)",
					By(
						subfieldL,
						kInBase,
						awayRing[1],
						awayKeeps[0],
						kInAway,
						inverseIn,
						keeps,
						data[0],
						EvaluationActionPoint.Read(M).At(k, base, L, away, s, ev)))
				fixesT := b.Have(
					"The inverse of s fixes t",
					"permutation_map(permutation_inverse(s), t) = t",
					By(inverseIn, tInBase, fixesBase.At(inverse, t)))
				atT := b.Have(
					"so the action sends t to x",
					"evaluation_action(field_ring(M), «away», s, ev, t) = x",
					Simp(Fwd(EvaluationActionDef)),
					By(Normalized, tInAway, fixesT, data[1]))
				b.Show(
					"so it lies in the fibre",
					By(
						point,
						atT,
						fibreMember.At(b.TermAs[Fun[A, A]]("evaluation_action(field_ring(M), «away», s, ev)"))))
			}))
		intertwines := arg.Have(
			"Restriction to C carries the action on the localization to the action on C",
			Statement{
				Binders:    "∀s:permutation(A). ∀ev:(A → A).",
				Hypotheses: []string{"s ∈ «G»"},
				Conclusion: "«restriction»(evaluation_action(field_ring(M), «away», s, ev)) = " +
					"evaluation_action(field_ring(M), C, s, «restriction»(ev))",
			},
			Derive(func(b *Argument) {
				s := b.FixAs[symmetric_group.Permutation[A]]("s")
				b.FixAs[Fun[A, A]]("ev")
				inG := b.Assume()
				b.Do(Funext())
				b.FixAs[A]("y")
				b.Do(Simp(Fwd(EvaluationActionDef)))
				b.Cases(b.Term("y ∈ C"))
				b.When(
					"On C both are the point after the inverse of s",
					func(c *Argument, inC Fact) {
						inAway := c.Have(
							"y lies in the localization",
							"y ∈ «away»",
							BySets(inC, awayRing[0]))
						moved := c.Have(
							"The inverse of s keeps C",
							"permutation_map(permutation_inverse(s), y) ∈ C",
							By(good, inG, inC, GroupKeepsChart.Read(M).At(k, L, C, t, a, s)))
						c.Show(
							"both sides read ev after the inverse of s",
							By(inC, inAway, moved))
					})
				b.Otherwise(
					"Off C both vanish",
					func(c *Argument, outside Fact) {
						c.Show(
							"both conditions fail",
							By(outside))
					})
			}))
		fibreAway := arg.TermAs[Set[Fun[A, A]]]("«fibre»(«away»)")
		restriction := arg.TermAs[Fun[Fun[A, A], Fun[A, A]]]("«restriction»")
		determined := arg.Unfolded(bijection[0], functions.InjectiveOnDef)
		restricts := arg.Have(
			"The restriction of a point of the fibre lies in the fibre of C",
			"∀ev:(A → A). ev ∈ «fibre»(«away») ⇒ «restriction»(ev) ∈ «fibre»(C)",
			Derive(func(b *Argument) {
				ev := b.FixAs[Fun[A, A]]("ev")
				inFibre := b.Assume()
				_, wIs := b.LetAs[Fun[A, A]]("w", "«restriction»(ev)")
				witness := b.Have(
					"it is the restriction of ev",
					"∃e:(A → A). w = «restriction»(e) ∧ e ∈ «fibre»(«away»)",
					Witness(ev),
					By(wIs, inFibre))
				inImage := b.Have(
					"so it lies in the image of the fibre",
					"w ∈ image(«restriction», «fibre»(«away»))",
					Simp(Fwd(set_basic.InImage)),
					By(witness))
				b.Show(
					"which is the fibre of C",
					bijection[1].RwRev(),
					By(inImage))
			}))
		lifts := arg.Have(
			"A point of the fibre of C is the restriction of a point of the fibre",
			"∀e:(A → A). e ∈ «fibre»(C) ⇒ ∃ev:(A → A). e = «restriction»(ev) ∧ ev ∈ «fibre»(«away»)",
			Derive(func(b *Argument) {
				e := b.FixAs[Fun[A, A]]("e")
				inFibre := b.Assume()
				inImage := b.Have(
					"it lies in the image of the fibre",
					"e ∈ image(«restriction», «fibre»(«away»))",
					bijection[1].Rw(),
					By(inFibre))
				b.Show(
					"so it restricts a point of the fibre",
					By(inImage, set_basic.InImage.At(restriction, fibreAway, e)))
			}))
		freeFacts := arg.Conjuncts(
			arg.Unfolded(clause.Free, twisted_counting.FreeFiniteActionDef),
			"G is a group",
			"G is finite",
			"the fibre of C is finite",
			"the identity acts trivially on the fibre of C",
			"G acts freely on the fibre of C")
		imageFinite := arg.Have(
			"The image of the fibre of the localization is the finite fibre of C",
			"finite(image(«restriction», «fibre»(«away»)))",
			bijection[1].Rw(),
			By(freeFacts[2]))
		finiteAway := arg.Have(
			"The fibre of the localization is finite",
			"finite(«fibre»(«away»))",
			By(bijection[0], imageFinite, finite_set.FiniteImageInjEq.At(restriction, fibreAway)))
		identityIn := arg.Have(
			"The identity lies in G",
			"permutation_identity ∈ «G»",
			By(subgroupG, group.SubgroupOne.At(permutations, automorphisms)))
		identityActs := arg.Have(
			"The identity acts trivially on the fibre",
			Statement{
				Binders: "∀z:(A → A).",
				Hypotheses: []string{
					"z ∈ «fibre»(«away»)",
				},
				Conclusion: "evaluation_action(field_ring(M), «away», permutation_identity, z) = z",
			},
			Derive(func(b *Argument) {
				z := b.FixAs[Fun[A, A]]("z")
				inFibre := b.Assume()
				identity := b.TermAs[symmetric_group.Permutation[A]]("permutation_identity")
				moved := b.TermAs[Fun[A, A]]("evaluation_action(field_ring(M), «away», permutation_identity, z)")
				image := b.TermAs[Fun[A, A]]("«restriction»(z)")
				below := b.Have(
					"The action restricts to the action on C, where the identity is trivial",
					"«restriction»(evaluation_action(field_ring(M), «away», permutation_identity, z)) = "+
						"«restriction»(z)",
					By(identityIn, restricts.At(z), inFibre, intertwines.At(identity, z), freeFacts[3].At(image)))
				b.Show(
					"so the two points agree",
					By(identityIn, inFibre, pointActs.At(identity, z), below, determined.At(moved, z)))
			}))
		actionLaws := arg.Have(
			"The action laws hold on the fibre",
			Statement{
				Binders:    "∀g h:permutation(A). ∀z:(A → A).",
				Hypotheses: []string{"g ∈ «G»", "h ∈ «G»", "z ∈ «fibre»(«away»)"},
				Conclusion: "evaluation_action(field_ring(M), «away», g, z) ∈ «fibre»(«away») ∧ " +
					"evaluation_action(field_ring(M), «away», permutation_compose(g, h), z) = " +
					"evaluation_action(field_ring(M), «away», g, evaluation_action(field_ring(M), «away», h, z)) ∧ " +
					"(evaluation_action(field_ring(M), «away», g, z) = z ⇒ g = permutation_identity)",
			},
			Derive(func(b *Argument) {
				g := b.FixAs[symmetric_group.Permutation[A]]("g")
				h := b.FixAs[symmetric_group.Permutation[A]]("h")
				z := b.FixAs[Fun[A, A]]("z")
				given := b.Conjuncts(
					b.Assume(),
					"g lies in G",
					"h lies in G",
					"z lies in the fibre")
				product := b.TermAs[symmetric_group.Permutation[A]]("permutation_compose(g, h)")
				image := b.TermAs[Fun[A, A]]("«restriction»(z)")
				movedByH := b.TermAs[Fun[A, A]]("evaluation_action(field_ring(M), «away», h, z)")
				movedByProduct := b.TermAs[Fun[A, A]](
					"evaluation_action(field_ring(M), «away», permutation_compose(g, h), z)")
				movedTwice := b.TermAs[Fun[A, A]](
					"evaluation_action(field_ring(M), «away», g, evaluation_action(field_ring(M), «away», h, z))")
				productIn := b.Have(
					"The product lies in G",
					"permutation_compose(g, h) ∈ «G»",
					By(given[0], given[1], subgroupG, group.SubgroupMul.At(permutations, automorphisms, g, h)))
				imageIn := b.Have(
					"z restricts to a point of the fibre of C",
					"«restriction»(z) ∈ «fibre»(C)",
					By(given[2], restricts.At(z)))
				onC := b.Conjuncts(
					b.Have(
						"Two of the laws hold on the fibre of C at its restriction",
						"evaluation_action(field_ring(M), C, permutation_compose(g, h), «restriction»(z)) = "+
							"evaluation_action(field_ring(M), "+
							"    C, "+
							"    g, "+
							"    evaluation_action(field_ring(M), C, h, «restriction»(z))) ∧ "+
							"(evaluation_action(field_ring(M), C, g, «restriction»(z)) = «restriction»(z) ⇒ "+
							"    g = permutation_identity)",
						By(given[0], given[1], imageIn, freeFacts[4].At(g, h, image))),
					"the action of a product is the composite on C",
					"a fixed point of g forces g to be the identity")
				productOnC, fixedOnC := onC[0], onC[1]
				inFibreH := b.Have(
					"h moves z inside the fibre",
					"evaluation_action(field_ring(M), «away», h, z) ∈ «fibre»(«away»)",
					By(given[1], given[2], pointActs.At(h, z)))
				product1 := b.Have(
					"The action of the product restricts to the action on C",
					"«restriction»(evaluation_action(field_ring(M), «away», permutation_compose(g, h), z)) = "+
						"evaluation_action(field_ring(M), C, permutation_compose(g, h), «restriction»(z))",
					By(productIn, intertwines.At(product, z)))
				product2 := b.Have(
					"as does the action of g after h",
					"«restriction»(evaluation_action(field_ring(M), "+
						"        «away», "+
						"        g, "+
						"        evaluation_action(field_ring(M), «away», h, z))) = "+
						"evaluation_action(field_ring(M), C, g, evaluation_action(field_ring(M), C, h, «restriction»(z)))",
					GroupPremises(given[0], intertwines.At(g, movedByH)).Rw(),
					GroupPremises(given[1], intertwines.At(h, z)).Rw(),
					Basic())
				composite := b.Have(
					"so the two actions agree",
					"evaluation_action(field_ring(M), «away», permutation_compose(g, h), z) = "+
						"evaluation_action(field_ring(M), «away», g, evaluation_action(field_ring(M), «away», h, z))",
					By(
						productIn,
						given[0],
						given[2],
						inFibreH,
						product1,
						product2,
						productOnC,
						pointActs.At(product, z),
						pointActs.At(g, movedByH),
						determined.At(movedByProduct, movedTwice)))
				free := b.Have(
					"A fixed point forces the identity",
					"evaluation_action(field_ring(M), «away», g, z) = z ⇒ g = permutation_identity",
					Derive(func(d *Argument) {
						fixed := d.Assume()
						below := d.Have(
							"g fixes the restriction of z",
							"evaluation_action(field_ring(M), C, g, «restriction»(z)) = «restriction»(z)",
							GroupPremises(given[0], intertwines.At(g, z)).RwRev(),
							fixed.Rw(),
							Basic())
						d.Show(
							"which forces g to be the identity",
							By(below, fixedOnC))
					}))
				b.Show(
					"the three laws",
					By(given[0], given[2], pointActs.At(g, z), composite, free))
			}))
		freeClause := arg.Have(
			"G acts freely on the fibre of the localization",
			"free_finite_action(galois_group(M, «base», L), "+
				"    «fibre»(«away»), "+
				"    evaluation_action(field_ring(M), «away»))",
			Simp(Fwd(twisted_counting.FreeFiniteActionDef)),
			By(freeFacts[0], freeFacts[1], finiteAway, identityActs, actionLaws))
		imageCard := arg.Have(
			"The image of the fibre of the localization has the size of G",
			"card(image(«restriction», «fibre»(«away»))) = card(«G»)",
			bijection[1].Rw(),
			By(clause.Card))
		cardClause := arg.Have(
			"The fibre of the localization has the size of G",
			"card(«fibre»(«away»)) = card(«G»)",
			By(bijection[0], imageCard, finiteAway, cardinality.CardImageInj.At(restriction, fibreAway)))
		transitive := arg.Have(
			"G moves any point of the fibre to any other",
			Statement{
				Binders:    "∀ev ew:(A → A).",
				Hypotheses: []string{"ev ∈ «fibre»(«away»)", "ew ∈ «fibre»(«away»)"},
				Conclusion: "∃s:permutation(A). s ∈ «G» ∧ evaluation_action(field_ring(M), «away», s, ev) = ew",
			},
			Derive(func(b *Argument) {
				ev := b.FixAs[Fun[A, A]]("ev")
				ew := b.FixAs[Fun[A, A]]("ew")
				given := b.Conjuncts(
					b.Assume(),
					"ev lies in the fibre",
					"ew lies in the fibre")
				imageV := b.TermAs[Fun[A, A]]("«restriction»(ev)")
				imageW := b.TermAs[Fun[A, A]]("«restriction»(ew)")
				s, data := b.ObtainAs[symmetric_group.Permutation[A]](
					"G moves the restriction of ev to that of ew",
					"∃s:permutation(A). "+
						"    s ∈ «G» ∧ evaluation_action(field_ring(M), C, s, «restriction»(ev)) = «restriction»(ew)",
					By(given[0], given[1], restricts.At(ev), restricts.At(ew), clause.Transitive.At(imageV, imageW)))
				parts := b.Conjuncts(
					data,
					"s lies in G",
					"s moves the restriction")
				moved := b.TermAs[Fun[A, A]]("evaluation_action(field_ring(M), «away», s, ev)")
				same := b.Have(
					"So the restriction of the moved point is that of ew",
					"«restriction»(evaluation_action(field_ring(M), «away», s, ev)) = «restriction»(ew)",
					By(parts[0], parts[1], intertwines.At(s, ev)))
				b.Take(s)
				b.Show(
					"and the moved point is ew",
					By(parts[0], given[0], given[1], pointActs.At(s, ev), same, determined.At(moved, ew)))
			}))
		target := arg.TermAs[RingOps[A]]("restrict_ring(field_ring(M), algebraic_elements(M, k))")
		inverted := arg.TermAs[RingOps[A]]("restrict_ring(field_ring(M), «away»)")
		identityMap := arg.TermAs[Fun[A, A]]("λy:A. y")
		groupTerm := arg.TermAs[group.GroupOps[symmetric_group.Permutation[A]]](
			"galois_group(M, «base», L)")
		subgroupClause := arg.Have(
			"Each subgroup clause carries over",
			Statement{
				Binders:    "∀H:set(permutation(A)).",
				Hypotheses: []string{"subgroup(galois_group(M, «base», L), H)"},
				Conclusion: "image((λev:(A → A).(λy:A. COND(y ∈ invariant_chart(«away», H), ev(y), M.zero))), " +
					"    «fibre»(«away»)) = " +
					"«fibre»(invariant_chart(«away», H)) ∧ " +
					"(∀ev ew:(A → A). " +
					"    ev ∈ «fibre»(«away») ∧ ew ∈ «fibre»(«away») ⇒ " +
					"    ((∀y:A. y ∈ invariant_chart(«away», H) ⇒ ev(y) = ew(y)) ⇔ " +
					"        ∃s:permutation(A). s ∈ H ∧ evaluation_action(field_ring(M), «away», s, ev) = ew))",
			},
			Derive(func(b *Argument) {
				H := b.FixAs[Set[symmetric_group.Permutation[A]]]("H")
				subgroupH := b.Assume()
				atH := b.Conjuncts(
					GroupPremises(subgroupH, clause.Quotients.At(H)),
					"restriction carries the fibre of C onto the fibre of the invariants",
					"two points agree on the invariants exactly when H moves one to the other")
				HInG := b.Have(
					"H lies in G",
					"H ⊆ «G»",
					By(subgroupH, field_automorphism.GaloisGroupSubgroup.At(ops, base, L, H)))
				chartAwayEq := b.Have(
					"The invariants of the localization are the localization of the invariants",
					"invariant_chart(«away», H) = "+
						"ring_away(field_ring(M), invariant_chart(C, H), polynomial_eval(c, t))",
					By(
						subfieldBase,
						subfieldL,
						baseInL,
						CInL,
						HInG,
						valueInBase,
						valueNonzero,
						InvariantChartAway.Read(M).At(base, L, C, H, value)))
				chartC := b.Conjuncts(
					GroupPremises(subfieldL, subringC, CInL, HInG, InvariantChartFacts.Read(M).At(base, L, C, H)),
					"the invariants of C are a subring",
					"they lie in C",
					"they hold what lies in C and in k(t)")
				chartL := b.Conjuncts(
					GroupPremises(
						subfieldL, awayRing[1], awayKeeps[0], HInG, InvariantChartFacts.Read(M).At(base, L, away, H)),
					"the invariants of the localization are a subring",
					"they lie in the localization",
					"they hold what lies in the localization and in k(t)")
				invariants := b.TermAs[Set[A]]("invariant_chart(C, H)")
				invariantsAway := b.TermAs[Set[A]]("invariant_chart(«away», H)")
				kInInvariants := b.Have(
					"k lies in the invariants of C",
					"k ⊆ invariant_chart(C, H)",
					BySets(kInC, kInBase, chartC[2]))
				tInInvariants := b.Have(
					"t lies in the invariants of C",
					"t ∈ invariant_chart(C, H)",
					By(tInC, tInBase, chartC[2].At(t)))
				kInDAway := b.Have(
					"k lies in the invariants of the localization",
					"k ⊆ invariant_chart(«away», H)",
					BySets(kInAway, kInBase, chartL[2]))
				tInDAway := b.Have(
					"t lies in the invariants of the localization",
					"t ∈ invariant_chart(«away», H)",
					By(tInAway, tInBase, chartL[2].At(t)))
				onInvariants := b.Conjuncts(
					b.Simplified(
						GroupPremises(
							chartC[0],
							overK,
							valueNonzero,
							xInClosure,
							subfieldK,
							rootFreeC,
							kInInvariants,
							tInInvariants,
							FibreAway.Read(M).At(k, invariants, t, x, c)),
						Rev(chartAwayEq)),
					"restriction to the invariants of C is injective on the fibre of the localized invariants",
					"its image is the fibre of the invariants of C")
				valueInD := b.Have(
					"c(t) lies in the invariants of C",
					"polynomial_eval(c, t) ∈ invariant_chart(C, H)",
					By(valueInC, valueInBase, chartC[2].At(value)))
				invariantsInAway := b.Have(
					"The invariants of C lie in the invariants of the localization",
					"invariant_chart(C, H) ⊆ invariant_chart(«away», H)",
					chartAwayEq.Rw(),
					By(ring, chartC[0], valueInD, ring_away.RingAwaySubring.At(fieldRing, invariants, value)))
				toInvariants := b.TermAs[Fun[Fun[A, A], Fun[A, A]]](
					"λev:(A → A). λy:A. COND(y ∈ invariant_chart(«away», H), ev(y), M.zero)")
				pointRestricted := b.Have(
					"A point of the fibre restricts to the invariants of the localization",
					Statement{
						Binders:    "∀ev:(A → A).",
						Hypotheses: []string{"ev ∈ «fibre»(«away»)"},
						Conclusion: "(λy:A. COND(y ∈ invariant_chart(«away», H), ev(y), M.zero)) ∈ " +
							"«fibre»(invariant_chart(«away», H))",
					},
					Derive(func(d *Argument) {
						ev := d.FixAs[Fun[A, A]]("ev")
						inFibre := d.Assume()
						data := d.Conjuncts(
							d.Have(
								"ev is a point over x",
								"ev ∈ geometric_evaluation_points(M, k, «away») ∧ ev(t) = x",
								By(inFibre, fibreMember.At(ev))),
							"ev is a point",
							"ev(t) = x")
						inPoints := d.Have(
							"ev is a point of the localization",
							"ev ∈ "+
								"algebra_points(restrict_ring(field_ring(M), «away»), "+
								"    restrict_ring(field_ring(M), algebraic_elements(M, k)), "+
								"    k, "+
								"    λy:A. y)",
							By(data[0], GeometricEvaluationPointsDef.At(ops, k, away)))
						subringInside := d.Have(
							"The invariants are a subring of the localization",
							"subring(restrict_ring(field_ring(M), «away»), invariant_chart(«away», H))",
							By(chartL[0], chartL[1], comm_ring.SubringRestrict.At(fieldRing, invariantsAway, away)))
						restricted := d.Have(
							"so ev restricts to a point of the invariants",
							"(λy:A. COND(y ∈ invariant_chart(«away», H), ev(y), M.zero)) ∈ "+
								"algebra_points(restrict_ring(field_ring(M), invariant_chart(«away», H)), "+
								"    restrict_ring(field_ring(M), algebraic_elements(M, k)), "+
								"    k, "+
								"    λy:A. y)",
							By(
								subringInside,
								kInDAway,
								inPoints,
								module_record.RestrictRingTwice.At(fieldRing, away, invariantsAway),
								PointRestricts.At(inverted, target, invariantsAway, k, identityMap, ev)))
						d.Show(
							"over x, since t is invariant",
							BySets(
								restricted,
								tInDAway,
								data[1],
								GeometricFibreDef.At(ops, k, invariantsAway, t, x),
								GeometricEvaluationPointsDef.At(ops, k, invariantsAway)))
					}))
				imageEq := b.Have(
					"Restriction carries the fibre onto the fibre of the invariants of the localization",
					"image((λev:(A → A).(λy:A. COND(y ∈ invariant_chart(«away», H), ev(y), M.zero))), "+
						"    «fibre»(«away»)) = "+
						"«fibre»(invariant_chart(«away», H))",
					Simp(Fwd(set_basic.Extension)),
					Derive(func(d *Argument) {
						ψ := d.FixAs[Fun[A, A]]("ψ")
						d.Iff()
						d.Forward(
							"the restriction of a point of the fibre",
							func(e *Argument, inImage Fact) {
								ev, chosen := e.ObtainAs[Fun[A, A]](
									"ψ restricts a point of the fibre",
									"∃ev:(A → A). "+
										"    ψ = (λy:A. COND(y ∈ invariant_chart(«away», H), ev(y), M.zero)) ∧ ev ∈ «fibre»(«away»)",
									By(inImage, set_basic.InImage.At(toInvariants, fibreAway, ψ)))
								parts := e.Conjuncts(
									chosen,
									"ψ restricts ev",
									"ev lies in the fibre")
								e.Show(
									"so it lies in the fibre of the invariants",
									By(parts[0], parts[1], pointRestricted.At(ev)))
							})
						d.Backward(
							"a point of the invariants extends over C and over the localization",
							func(e *Argument, inFibre Fact) {
								toInvariantsOfC := e.TermAs[Fun[Fun[A, A], Fun[A, A]]](
									"λev:(A → A). λy:A. COND(y ∈ invariant_chart(C, H), ev(y), M.zero)")
								fibreOfC := e.TermAs[Set[Fun[A, A]]]("«fibre»(C)")
								p, pIs := e.LetAs[Fun[A, A]]("p", "λy:A. COND(y ∈ invariant_chart(C, H), ψ(y), M.zero)")
								restrictsψ := e.Have(
									"p is the restriction of ψ",
									"∃g:(A → A). "+
										"    p = (λy:A. COND(y ∈ invariant_chart(C, H), g(y), M.zero)) ∧ "+
										"    g ∈ «fibre»(invariant_chart(«away», H))",
									Witness(ψ),
									By(pIs, inFibre))
								inImageOfAway := e.Have(
									"so p lies in the image of the fibre of the localized invariants",
									"p ∈ "+
										"image((λev:(A → A).(λy:A. COND(y ∈ invariant_chart(C, H), ev(y), M.zero))), "+
										"    «fibre»(invariant_chart(«away», H)))",
									Simp(Fwd(set_basic.InImage)),
									By(restrictsψ))
								inFibreOfC := e.Have(
									"which is the fibre of the invariants of C",
									"p ∈ «fibre»(invariant_chart(C, H))",
									onInvariants[1].RwRev(),
									By(inImageOfAway))
								inImageOfC := e.Have(
									"which is the image of the fibre of C",
									"p ∈ image((λev:(A → A).(λy:A. COND(y ∈ invariant_chart(C, H), ev(y), M.zero))), «fibre»(C))",
									atH[0].Rw(),
									By(inFibreOfC))
								e0, chosen := e.ObtainAs[Fun[A, A]](
									"p restricts a point of the fibre of C",
									"∃e₀:(A → A). p = (λy:A. COND(y ∈ invariant_chart(C, H), e₀(y), M.zero)) ∧ e₀ ∈ «fibre»(C)",
									By(inImageOfC, set_basic.InImage.At(toInvariantsOfC, fibreOfC, p)))
								chosenParts := e.Conjuncts(
									chosen,
									"p restricts e₀",
									"e₀ lies in the fibre of C")
								h, lifted := e.ObtainAs[Fun[A, A]](
									"e₀ restricts a point of the fibre",
									"∃h:(A → A). e₀ = «restriction»(h) ∧ h ∈ «fibre»(«away»)",
									By(chosenParts[1], lifts.At(e0)))
								liftedParts := e.Conjuncts(
									lifted,
									"e₀ restricts h",
									"h lies in the fibre")
								φ, φIs := e.LetAs[Fun[A, A]]("φ", "λy:A. COND(y ∈ invariant_chart(«away», H), h(y), M.zero)")
								φIn := e.Have(
									"φ lies in the fibre of the localized invariants",
									"φ ∈ «fibre»(invariant_chart(«away», H))",
									By(φIs, liftedParts[1], pointRestricted.At(h)))
								sameOnD := e.Have(
									"φ and ψ have the same restriction to the invariants of C",
									"(λy:A. COND(y ∈ invariant_chart(C, H), φ(y), M.zero)) = "+
										"(λy:A. COND(y ∈ invariant_chart(C, H), ψ(y), M.zero))",
									Funext(),
									Derive(func(f *Argument) {
										f.FixAs[A]("y")
										f.Cases(f.Term("y ∈ invariant_chart(C, H)"))
										f.When(
											"On the invariants of C both read h",
											func(w *Argument, inD Fact) {
												inC := w.Have(
													"y lies in C",
													"y ∈ C",
													BySets(inD, chartC[1]))
												inAwayD := w.Have(
													"y lies in the invariants of the localization",
													"y ∈ invariant_chart(«away», H)",
													BySets(inD, invariantsInAway))
												atY1 := w.Have(
													"φ reads h at y",
													"φ(y) = h(y)",
													By(φIs, inAwayD))
												atY2 := w.Have(
													"so does e₀, y lying in C",
													"e₀(y) = h(y)",
													By(liftedParts[0], inC))
												atY3 := w.Have(
													"p reads ψ at y and e₀ at y",
													"ψ(y) = e₀(y)",
													By(pIs, chosenParts[0], inD))
												w.Show(
													"so the two agree at y",
													By(inD, atY1, atY2, atY3))
											})
										f.Otherwise(
											"Off the invariants of C both vanish",
											func(w *Argument, outside Fact) {
												w.Show(
													"both conditions fail",
													By(outside))
											})
									}))
								same := e.Have(
									"so φ is ψ",
									"φ = ψ",
									By(φIn, inFibre, sameOnD, e.Unfolded(onInvariants[0], functions.InjectiveOnDef).At(φ, ψ)))
								witness := e.Have(
									"ψ restricts h",
									"∃g:(A → A). ψ = (λy:A. COND(y ∈ invariant_chart(«away», H), g(y), M.zero)) ∧ g ∈ «fibre»(«away»)",
									Witness(h),
									By(φIs, same, liftedParts[1]))
								e.Show(
									"so ψ lies in the image of the fibre",
									Simp(Fwd(set_basic.InImage)),
									By(witness))
							})
					}))
				orbit := b.Have(
					"Two points of the fibre agree on the invariants exactly when H moves one to the other",
					Statement{
						Binders:    "∀ev ew:(A → A).",
						Hypotheses: []string{"ev ∈ «fibre»(«away»)", "ew ∈ «fibre»(«away»)"},
						Conclusion: "(∀y:A. y ∈ invariant_chart(«away», H) ⇒ ev(y) = ew(y)) ⇔ " +
							"∃s:permutation(A). s ∈ H ∧ evaluation_action(field_ring(M), «away», s, ev) = ew",
					},
					Derive(func(d *Argument) {
						ev := d.FixAs[Fun[A, A]]("ev")
						ew := d.FixAs[Fun[A, A]]("ew")
						given := d.Conjuncts(
							d.Assume(),
							"ev lies in the fibre",
							"ew lies in the fibre")
						imageV := d.TermAs[Fun[A, A]]("«restriction»(ev)")
						imageW := d.TermAs[Fun[A, A]]("«restriction»(ew)")
						d.Iff()
						d.Forward(
							"agreement on the invariants descends to the fibre of C",
							func(e *Argument, agree Fact) {
								onD := e.Have(
									"The restrictions agree on the invariants of C",
									"∀y:A. y ∈ invariant_chart(C, H) ⇒ «restriction»(ev)(y) = «restriction»(ew)(y)",
									Derive(func(f *Argument) {
										y := f.FixAs[A]("y")
										inD := f.Assume()
										inC := f.Have(
											"y lies in C",
											"y ∈ C",
											BySets(inD, chartC[1]))
										inAwayD := f.Have(
											"y lies in the invariants of the localization",
											"y ∈ invariant_chart(«away», H)",
											BySets(inD, invariantsInAway))
										f.Show(
											"ev and ew agree there",
											By(inC, inAwayD, agree.At(y)))
									}))
								s, data := e.ObtainAs[symmetric_group.Permutation[A]](
									"H moves the restriction of ev to that of ew",
									"∃s:permutation(A). "+
										"    s ∈ H ∧ evaluation_action(field_ring(M), C, s, «restriction»(ev)) = «restriction»(ew)",
									By(given[0], given[1], restricts.At(ev), restricts.At(ew), onD, atH[1].At(imageV, imageW)))
								parts := e.Conjuncts(
									data,
									"s lies in H",
									"s moves the restriction")
								sInG := e.Have(
									"s lies in G",
									"s ∈ «G»",
									BySets(parts[0], HInG))
								moved := e.TermAs[Fun[A, A]]("evaluation_action(field_ring(M), «away», s, ev)")
								same := e.Have(
									"So the restriction of the moved point is that of ew",
									"«restriction»(evaluation_action(field_ring(M), «away», s, ev)) = «restriction»(ew)",
									By(sInG, parts[1], intertwines.At(s, ev)))
								e.Take(s)
								e.Show(
									"and the moved point is ew",
									By(parts[0], given[0], given[1], sInG, pointActs.At(s, ev), same, determined.At(moved, ew)))
							})
						d.Backward(
							"H moves a point to another fixing the invariants",
							func(e *Argument, moved Fact) {
								s, data := e.UnpackAs[symmetric_group.Permutation[A]](moved, "s")
								parts := e.Conjuncts(
									data,
									"s lies in H",
									"s moves ev to ew")
								inverseInH := e.Have(
									"The inverse of s lies in H",
									"permutation_inverse(s) ∈ H",
									By(parts[0], subgroupH, group.SubgroupInv.At(groupTerm, H, s)))
								e.FixAs[A]("y")
								inD := e.Assume()
								inAwayY := e.Have(
									"y lies in the localization",
									"y ∈ «away»",
									BySets(inD, chartL[1]))
								fixed := e.Have(
									"The inverse of s fixes y",
									"permutation_map(permutation_inverse(s), y) = y",
									BySets(inD, inverseInH, InvariantChartDef.At(away, H)))
								e.Show(
									"so ew reads ev at y",
									parts[1].RwRev(),
									Simp(Fwd(EvaluationActionDef)),
									By(Normalized, inAwayY, fixed))
							})
					}))
				b.Show(
					"Both parts of the clause hold",
					By(orbit, imageEq))
			}))
		arg.Show(
			"The four clauses at the localization",
			By(freeClause, cardClause, transitive, subgroupClause))
	}),
})}

// GaloisGoodOpenLocalize — inverting c(t) in a good open, for c nonzero over k,
// leaves a good open with denominator a · c. Each ring clause passes to the
// localization, and the fibre clauses are GoodFibreAway, the good points of
// a · c being good points of a at which c does not vanish.
var GaloisGoodOpenLocalize = galoisGoodOpenLocalizeThm{family.Add(registry.ProofEntry{
	Name: "GaloisGoodOpenLocalize",
	Key:  "prop_a9d4e72bf435e893",
	Build: family.Theorem(Statement{
		Abbrev: Abbrev{
			{Name: "base", Text: "field_adjoin(M, k, {t})"},
			{Name: "G", Text: "field_automorphisms(M, «base», L)"},
			{Name: "polynomials", Text: "polynomial_image(field_ring(M), k, t)"},
			{Name: "away", Text: "ring_away(field_ring(M), C, polynomial_eval(c, t))"},
		},
		Binders: "∀M:field_on(A). ∀k L C:set(A). ∀t:A. ∀a c:(num → A).",
		Hypotheses: []string{
			"galois_good_open(M, k, L, t, C, a)",
			"polynomial_over(k, c)",
			"c ≠ vec_zero",
		},
		Conclusion: "galois_good_open(M, k, L, t, «away», polynomial_mul(a, c))",
	}, func(
		arg *Argument,
		M field.FieldFact[on.M],
		k, L, C *Expr[Set[A]],
		t *Expr[A],
		a, c *Arrow[Nat, A],
		good, overK, nonzeroC Fact,
	) {
		ops := arg.TermAs[FieldOps[A]]("M")
		fieldRing := arg.TermAs[RingOps[A]]("field_ring(M)")
		ring := field.RingOn.Read(M)
		base := arg.TermAs[Set[A]]("«base»")
		polynomials := arg.TermAs[Set[A]]("«polynomials»")
		denominator := arg.TermAs[A]("polynomial_eval(a, t)")
		value := arg.TermAs[A]("polynomial_eval(c, t)")
		away := arg.TermAs[Set[A]]("«away»")
		zero := arg.TermAs[A]("M.zero")
		carrier := arg.TermAs[Set[A]]("M.carrier")
		subfieldK, subfieldL := GoodOpenConstantsSubfield.Read(good), GoodOpenFieldSubfield.Read(good)
		subfieldBase := arg.Have(
			"k(t) is a subfield",
			"subfield(M, «base»)",
			By(good, GoodOpenRationalSubfield.Read(M).At(k, L, C, t, a)))
		subringPolynomials := arg.Have(
			"k[t] is a subring",
			"subring(field_ring(M), «polynomials»)",
			By(good, GoodOpenPolynomialsSubring.Read(M).At(k, L, C, t, a)))
		subringC := arg.Have(
			"C is a subring",
			"subring(field_ring(M), C)",
			By(good, GoodOpenChartSubring.Read(M).At(k, L, C, t, a)))
		denominatorInPolynomials := GoodOpenDenominatorInPolynomials.Read(good)
		denominatorNonzero := GoodOpenDenominatorValueNonzero.Read(good)
		LInField := arg.Have(
			"L lies in M",
			"L ⊆ M.carrier",
			By(subfieldL, field.SubfieldSubset.At(ops, L)))
		kInField := arg.Have(
			"k lies in M",
			"k ⊆ M.carrier",
			By(subfieldK, field.SubfieldSubset.At(ops, k)))
		tm := arg.MemberOf[on.M](t, arg.Have(
			"t lies in M",
			"t ∈ M.carrier",
			BySets(GoodOpenParameterIn.Read(good), LInField)))
		valueNonzero := arg.Have(
			"c(t) is nonzero",
			"polynomial_eval(c, t) ≠ M.zero",
			By(
				GoodOpenParameterTranscendental.Read(good),
				overK,
				nonzeroC,
				algebraic_element.AlgebraicOverDef.At(ops, k, t)))
		valueInPolynomials := arg.Have(
			"c(t) lies in k[t]",
			"polynomial_eval(c, t) ∈ «polynomials»",
			BySets(overK, algebraic_element.PolynomialImageDef.At(fieldRing, k, t)))
		valueInBase := arg.Have(
			"so it lies in k(t), which holds k[t]",
			"polynomial_eval(c, t) ∈ «base»",
			BySets(valueInPolynomials, subfieldK, algebraic_element.PolynomialImageRing.Read(M).At(k, tm)))
		valueInC := arg.Have(
			"and in C, which holds k[t]",
			"polynomial_eval(c, t) ∈ C",
			BySets(valueInPolynomials, good, GoodOpenPolynomialsInChart.Read(M).At(k, L, C, t, a)))
		denominatorInC := arg.Have(
			"a(t) lies in C",
			"polynomial_eval(a, t) ∈ C",
			By(good, GoodOpenDenominatorInChart.Read(M).At(k, L, C, t, a)))
		CInL := GoodOpenChartInField.Read(good)
		CInField := arg.Have(
			"C lies in M",
			"C ⊆ M.carrier",
			BySets(CInL, LInField))
		denominatorM := arg.MemberOf[on.M](denominator, arg.Have(
			"a(t) lies in M",
			"polynomial_eval(a, t) ∈ M.carrier",
			BySets(denominatorInC, CInField)))
		valueM := arg.MemberOf[on.M](value, arg.Have(
			"c(t) lies in M",
			"polynomial_eval(c, t) ∈ M.carrier",
			BySets(valueInC, CInField)))
		awayRing := arg.Conjuncts(
			arg.Have(
				"C with c(t) inverted is a subring holding C and the inverse of c(t)",
				"C ⊆ «away» ∧ subring(field_ring(M), «away») ∧ M.inv(polynomial_eval(c, t)) ∈ «away»",
				By(
					ring,
					subringC,
					valueInC,
					valueNonzero,
					field.InvIn.Read(M).At(valueM),
					field.MulRightInverseOn.Read(M).At(valueM),
					ring_away.RingAwaySubring.At(fieldRing, C, value))),
			"C lies in the localization",
			"the localization is a subring",
			"it holds the inverse of c(t)")
		awayKeeps := arg.Conjuncts(
			GroupPremises(
				subfieldL,
				GoodOpenRationalInField.Read(good),
				subfieldBase,
				CInL,
				valueInBase,
				valueNonzero,
				AutomorphismKeepsAway.Read(M).At(base, L, C, value)),
			"the localization lies in L",
			"an automorphism keeping C keeps the localization")
		awayOn := arg.Have(
			"The localization is a ring under the operations of M",
			"comm_ring_on(restrict_ring(field_ring(M), «away»))",
			By(awayRing[1], comm_ring.SubringRingOn.Read(ring).At(away)))
		overField := arg.Have(
			"a and c are polynomials over M",
			"polynomial_over(M.carrier, a) ∧ polynomial_over(M.carrier, c)",
			By(
				kInField,
				GoodOpenDenominatorOver.Read(good),
				overK,
				polynomial.PolynomialOverMono.At(zero, k, carrier, a),
				polynomial.PolynomialOverMono.At(zero, k, carrier, c)))
		productData := arg.Conjuncts(
			GroupPremises(
				subfieldK,
				GoodOpenDenominatorOver.Read(good),
				overK,
				polynomial_evaluation.PolynomialProductData.Read(M).At(k, a, c)),
			"a · c is a polynomial over k",
			"it is nonzero with its factors",
			"it evaluates to the product of the values")
		productOver := productData[0]
		productNonzero := arg.Have(
			"a · c is nonzero",
			"polynomial_mul(a, c) ≠ vec_zero",
			By(GoodOpenDenominatorNonzero.Read(good), nonzeroC, productData[1]))
		productValue := arg.Have(
			"a · c evaluates to the product of the values at t",
			"polynomial_eval(polynomial_mul(a, c), t) = polynomial_eval(a, t) * polynomial_eval(c, t)",
			By(tm, productData[2].At(t)))
		awayOfPolynomials := arg.Conjuncts(
			arg.Have(
				"k[t] with a(t) inverted is a subring holding k[t]",
				"«polynomials» ⊆ ring_away(field_ring(M), «polynomials», polynomial_eval(a, t)) ∧ "+
					"subring(field_ring(M), ring_away(field_ring(M), «polynomials», polynomial_eval(a, t)))",
				By(
					ring,
					subringPolynomials,
					denominatorInPolynomials,
					ring_away.RingAwaySubring.At(fieldRing, polynomials, denominator))),
			"it holds k[t]",
			"it is a subring")
		scalars := arg.TermAs[Set[A]]("ring_away(field_ring(M), «polynomials», polynomial_eval(a, t))")
		twice := arg.Have(
			"Inverting a(t) and then c(t) in k[t] is inverting the product",
			"ring_away(field_ring(M), "+
				"    ring_away(field_ring(M), «polynomials», polynomial_eval(a, t)), "+
				"    polynomial_eval(c, t)) = "+
				"ring_away(field_ring(M), «polynomials», polynomial_eval(a, t) * polynomial_eval(c, t))",
			By(
				subringPolynomials,
				denominatorInPolynomials,
				valueInPolynomials,
				ring_away.RingAwayTwice.Read(M).At(polynomials, denominator, value)))
		below := arg.Have(
			"k[t] with a(t) · c(t) inverted lies in the localization",
			"ring_away(field_ring(M), «polynomials», polynomial_eval(polynomial_mul(a, c), t)) ⊆ «away»",
			productValue.Rw(),
			twice.RwRev(),
			BySets(
				GoodOpenChartHoldsBase.Read(good),
				ring_away.RingAwayDef.At(fieldRing, scalars, value),
				ring_away.RingAwayDef.At(fieldRing, C, value)))
		denominatorInAway := arg.Have(
			"a(t) lies in the localization",
			"polynomial_eval(a, t) ∈ «away»",
			BySets(denominatorInC, awayRing[0]))
		valueInAway := arg.Have(
			"c(t) lies in the localization",
			"polynomial_eval(c, t) ∈ «away»",
			BySets(valueInC, awayRing[0]))
		inverseInAway := arg.Have(
			"the inverse of a(t) lies in C, so in the localization",
			"M.inv(polynomial_eval(a, t)) ∈ «away»",
			BySets(good, GoodOpenDenominatorInverseInChart.Read(M).At(k, L, C, t, a), awayRing[0]))
		denominatorUnit := arg.Have(
			"a(t) has the inverse",
			"polynomial_eval(a, t) * M.inv(polynomial_eval(a, t)) = M.one",
			By(denominatorM, denominatorNonzero, field.MulRightInverseOn.Read(M).At(denominatorM)))
		valueUnit := arg.Have(
			"c(t) has the inverse",
			"polynomial_eval(c, t) * M.inv(polynomial_eval(c, t)) = M.one",
			By(valueM, valueNonzero, field.MulRightInverseOn.Read(M).At(valueM)))
		inverseProduct := arg.TermAs[A]("M.inv(polynomial_eval(a, t)) * M.inv(polynomial_eval(c, t))")
		productUnit := arg.Have(
			"so a(t) · c(t) has the product of the inverses for inverse",
			"(polynomial_eval(a, t) * polynomial_eval(c, t)) * "+
				"(M.inv(polynomial_eval(a, t)) * M.inv(polynomial_eval(c, t))) = "+
				"M.one",
			ByArith(
				ring,
				Scaled(arg.TermAs[A]("polynomial_eval(c, t) * M.inv(polynomial_eval(c, t))"), denominatorUnit),
				valueUnit,
				denominatorM,
				valueM,
				field.InvIn.Read(M).At(denominatorM),
				field.InvIn.Read(M).At(valueM)))
		mulInAway := comm_ring.SubringMul.At(fieldRing, away, denominator, value)
		inverseMulInAway := comm_ring.SubringMul.At(
			fieldRing,
			away,
			arg.TermAs[A]("M.inv(polynomial_eval(a, t))"),
			arg.TermAs[A]("M.inv(polynomial_eval(c, t))"))
		stable := arg.Have(
			"The localization holds the inverse of a(t) · c(t)",
			"«away» = ring_away(field_ring(M), «away», polynomial_eval(polynomial_mul(a, c), t))",
			productValue.Rw(),
			By(
				awayRing[1],
				awayRing[2],
				denominatorInAway,
				valueInAway,
				inverseInAway,
				mulInAway,
				inverseMulInAway,
				productUnit,
				ring_away.AwayOfUnit.Read(M).At(
					away, arg.TermAs[A]("polynomial_eval(a, t) * polynomial_eval(c, t)"), inverseProduct)))
		fractionClause := arg.Have(
			"L is the fraction field of the localization, which holds C and lies in L",
			"fraction_field_carrier(restrict_ring(field_ring(M), L), «away»)",
			By(
				GoodOpenFractionField.Read(good),
				awayRing[0],
				awayKeeps[0],
				field.FractionFieldCarrierMono.At(
					arg.TermAs[RingOps[A]]("restrict_ring(field_ring(M), L)"), C, away)))
		valueInScalars := arg.Have(
			"c(t) lies in k[t] with a(t) inverted",
			"polynomial_eval(c, t) ∈ ring_away(field_ring(M), «polynomials», polynomial_eval(a, t))",
			BySets(valueInPolynomials, awayOfPolynomials[0]))
		E, generators := arg.UnpackAs[Set[A]](
			arg.Unfolded(GoodOpenChartFinite.Read(good), principal_ideal_domain.FinitelyGeneratedDef), "E")
		generated := arg.Conjuncts(
			generators,
			"E is finite",
			"E lies in C",
			"E spans C over k[t] with a(t) inverted")
		EInAway := arg.Have(
			"E lies in the localization",
			"E ⊆ «away»",
			BySets(generated[1], awayRing[0]))
		finiteClause := arg.Have(
			"The localization is finite over k[t] with a(t) · c(t) inverted, spanned by the generators E of C",
			"module_finitely_generated(restrict_ring(field_ring(M), "+
				"        ring_away(field_ring(M), «polynomials», polynomial_eval(polynomial_mul(a, c), t))), "+
				"    restrict_module(regular_module(field_ring(M)), «away»))",
			productValue.Rw(),
			twice.RwRev(),
			Unfold(principal_ideal_domain.FinitelyGeneratedDef),
			Witness(E),
			By(
				generated[0],
				EInAway,
				awayOfPolynomials[1],
				subringC,
				GoodOpenChartHoldsBase.Read(good),
				valueInScalars,
				valueNonzero,
				generated[1],
				generated[2],
				ring_away.SpanningAway.Read(M).At(scalars, C, value, E)))
		keepsAway := groupKeepsAway(arg, M, k, L, C, t, a, c, good, awayKeeps[1])
		keepsClause := arg.Have(
			"G maps the localization onto itself",
			"∀s:permutation(A). s ∈ «G» ⇒ image(permutation_map(s), «away») = «away»",
			Derive(func(b *Argument) {
				s := b.FixAs[symmetric_group.Permutation[A]]("s")
				inG := b.Assume()
				inverse := b.TermAs[symmetric_group.Permutation[A]]("permutation_inverse(s)")
				inverseIn := b.Have(
					"The inverse of s lies in G",
					"permutation_inverse(s) ∈ «G»",
					By(good, inG, GroupKeepsChart.Read(M).At(k, L, C, t, a, s)))
				b.Do(Simp(Fwd(set_basic.Extension)))
				y := b.FixAs[A]("y")
				b.Iff()
				b.Forward(
					"s keeps the localization",
					func(e *Argument, inImage Fact) {
						u, chosen := e.ObtainAs[A](
							"y is the image of a point of the localization",
							"∃u:A. y = permutation_map(s, u) ∧ u ∈ «away»",
							By(inImage, set_basic.InImage.At(b.TermAs[Fun[A, A]]("permutation_map(s)"), away, y)))
						parts := e.Conjuncts(
							chosen,
							"y is the image of u",
							"u lies in the localization")
						e.Show(
							"so y lies in the localization",
							By(inG, parts[0], parts[1], keepsAway.At(s, u)))
					})
				b.Backward(
					"the inverse of s keeps the localization",
					func(e *Argument, inAway Fact) {
						preimage := e.TermAs[A]("permutation_map(permutation_inverse(s), y)")
						source := e.Have(
							"The inverse of s keeps y in the localization",
							"permutation_map(permutation_inverse(s), y) ∈ «away»",
							By(inverseIn, inAway, keepsAway.At(inverse, y)))
						witness := e.Have(
							"y is the image of that point",
							"∃u:A. y = permutation_map(s, u) ∧ u ∈ «away»",
							Witness(preimage),
							By(source, symmetric_group.MapInverseRight.At(s, y)))
						e.Show(
							"so y lies in the image",
							By(witness, set_basic.InImage.At(b.TermAs[Fun[A, A]]("permutation_map(s)"), away, y)))
					})
			}))
		fibreClause := arg.Have(
			"Each good point of a · c is a good point of a at which c does not vanish",
			Statement{
				Binders: "∀x:A.",
				Hypotheses: []string{
					"x ∈ algebraic_elements(M, k)",
					"polynomial_eval(polynomial_mul(a, c), x) ≠ M.zero",
				},
				Conclusion: "free_finite_action(galois_group(M, «base», L), " +
					"    geometric_fibre(M, k, «away», t, x), " +
					"    evaluation_action(field_ring(M), «away»)) ∧ " +
					"card(geometric_fibre(M, k, «away», t, x)) = card(«G») ∧ " +
					"(∀ev ew:(A → A). " +
					"    ev ∈ geometric_fibre(M, k, «away», t, x) ∧ ew ∈ geometric_fibre(M, k, «away», t, x) ⇒ " +
					"    ∃s:permutation(A). s ∈ «G» ∧ evaluation_action(field_ring(M), «away», s, ev) = ew) ∧ " +
					"(∀H:set(permutation(A)). " +
					"    subgroup(galois_group(M, «base», L), H) ⇒ " +
					"    image((λev:(A → A).(λy:A. COND(y ∈ invariant_chart(«away», H), ev(y), M.zero))), " +
					"        geometric_fibre(M, k, «away», t, x)) = " +
					"    geometric_fibre(M, k, invariant_chart(«away», H), t, x) ∧ " +
					"    (∀ev ew:(A → A). " +
					"        ev ∈ geometric_fibre(M, k, «away», t, x) ∧ ew ∈ geometric_fibre(M, k, «away», t, x) ⇒ " +
					"        ((∀y:A. y ∈ invariant_chart(«away», H) ⇒ ev(y) = ew(y)) ⇔ " +
					"            ∃s:permutation(A). s ∈ H ∧ evaluation_action(field_ring(M), «away», s, ev) = ew)))",
			},
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				given := b.Conjuncts(
					b.Assume(),
					"x is algebraic over k",
					"a · c does not vanish at x")
				xm := b.MemberOf[on.M](x, b.Have(
					"x lies in M",
					"x ∈ M.carrier",
					BySets(given[0], algebraic_element.AlgebraicElementsDef.At(ops, k))))
				split := b.Have(
					"a · c evaluates to the product of the values at x",
					"polynomial_eval(polynomial_mul(a, c), x) = polynomial_eval(a, x) * polynomial_eval(c, x)",
					By(xm, productData[2].At(x)))
				ax := b.MemberOf[on.M](b.TermAs[A]("polynomial_eval(a, x)"), b.Have(
					"a(x) lies in M",
					"polynomial_eval(a, x) ∈ M.carrier",
					By(overField, xm, polynomial_evaluation.EvalIn.Read(ring).AsFact().At(a, x))))
				cx := b.MemberOf[on.M](b.TermAs[A]("polynomial_eval(c, x)"), b.Have(
					"c(x) lies in M",
					"polynomial_eval(c, x) ∈ M.carrier",
					By(overField, xm, polynomial_evaluation.EvalIn.Read(ring).AsFact().At(c, x))))
				neither := b.Have(
					"Neither value vanishes",
					"polynomial_eval(a, x) ≠ M.zero ∧ polynomial_eval(c, x) ≠ M.zero",
					By(given[1], split, ax, cx, field.MulEqZeroOn.Read(M).At(ax, cx)))
				b.Show(
					"so the fibre clauses hold at x",
					By(good, overK, valueNonzero, given[0], neither, GoodFibreAway.Read(M).At(k, L, C, t, x, a, c)))
			}))
		arg.Show(
			"Each clause of a good open holds at the localization",
			By(
				GoodOpenRegular.Read(good),
				GoodOpenConstantsFinite.Read(good),
				GoodOpenParameterIn.Read(good),
				GoodOpenParameterTranscendental.Read(good),
				GoodOpenGalois.Read(good),
				awayKeeps[0],
				awayOn,
				productOver,
				productNonzero,
				below,
				stable,
				fractionClause,
				finiteClause,
				keepsClause,
				fibreClause,
				GaloisGoodOpenDef.At(ops, k, L, away, t, arg.TermAs[Fun[Nat, A]]("polynomial_mul(a, c)"))))
	}),
})}

// ChartAwayFacts — inverting c(t) in a good open, c a nonzero polynomial over k,
// gives a good open between C and L: c(t) lies in C and is nonzero, t being
// transcendental, and GaloisGoodOpenLocalize gives the good open.
var ChartAwayFacts = chartAwayFactsThm{family.Add(registry.ProofEntry{
	Name: "ChartAwayFacts",
	Key:  "prop_6a5b7f00f1adc93f",
	Build: family.Theorem(Statement{
		Abbrev: Abbrev{
			{Name: "base", Text: "field_adjoin(M, k, {t})"},
			{Name: "polynomials", Text: "polynomial_image(field_ring(M), k, t)"},
			{Name: "away", Text: "ring_away(field_ring(M), C, polynomial_eval(c, t))"},
		},
		Binders: "∀M:field_on(A). ∀k L C:set(A). ∀t:A. ∀a c:(num → A).",
		Hypotheses: []string{
			"galois_good_open(M, k, L, t, C, a)",
			"polynomial_over(k, c)",
			"c ≠ vec_zero",
		},
		Conclusion: "polynomial_eval(c, t) ∈ C ∧ " +
			"polynomial_eval(c, t) ≠ M.zero ∧ " +
			"C ⊆ «away» ∧ " +
			"«away» ⊆ L ∧ " +
			"galois_good_open(M, k, L, t, «away», polynomial_mul(a, c))",
	}, func(
		arg *Argument,
		M field.FieldFact[on.M],
		k, L, C *Expr[Set[A]],
		t *Expr[A],
		a, c *Arrow[Nat, A],
		good, overK, nonzero Fact,
	) {
		ops := arg.TermAs[FieldOps[A]]("M")
		fieldRing := arg.TermAs[RingOps[A]]("field_ring(M)")
		ring := field.RingOn.Read(M)
		base := arg.TermAs[Set[A]]("«base»")
		value := arg.TermAs[A]("polynomial_eval(c, t)")
		tm := GoodParameterInField(arg, t, good)
		polynomialsInBase := arg.Have(
			"k[t] lies in k(t)",
			"«polynomials» ⊆ «base»",
			By(GoodOpenConstantsSubfield.Read(good), algebraic_element.PolynomialImageRing.Read(M).At(k, tm)))
		valueIn := arg.Conjuncts(
			arg.Have(
				"c(t) lies in k[t], so in k(t) and in C, both holding k[t]",
				"polynomial_eval(c, t) ∈ «base» ∧ polynomial_eval(c, t) ∈ C",
				BySets(
					overK,
					algebraic_element.PolynomialImageDef.At(fieldRing, k, t),
					polynomialsInBase,
					good,
					GoodOpenPolynomialsInChart.Read(M).At(k, L, C, t, a))),
			"c(t) lies in k(t)",
			"c(t) lies in C")
		valueNonzero := arg.Have(
			"c(t) is nonzero, t being transcendental",
			"polynomial_eval(c, t) ≠ M.zero",
			By(
				GoodOpenParameterTranscendental.Read(good),
				overK,
				nonzero,
				algebraic_element.AlgebraicOverDef.At(ops, k, t)))
		awayRing := arg.Have(
			"C lies in C with c(t) inverted",
			"C ⊆ «away» ∧ subring(field_ring(M), «away»)",
			By(
				ring,
				good,
				GoodOpenChartSubring.Read(M).At(k, L, C, t, a),
				valueIn[1],
				ring_away.RingAwaySubring.At(fieldRing, C, value)))
		inL := arg.Have(
			"which lies in L",
			"«away» ⊆ L",
			By(
				good,
				GoodOpenRationalSubfield.Read(M).At(k, L, C, t, a),
				GoodOpenFieldSubfield.Read(good),
				GoodOpenRationalInField.Read(good),
				GoodOpenChartInField.Read(good),
				valueIn[0],
				valueNonzero,
				AutomorphismKeepsAway.Read(M).At(base, L, C, value)))
		arg.Show(
			"and it is a good open",
			By(
				valueIn[1],
				valueNonzero,
				awayRing,
				inL,
				good,
				overK,
				nonzero,
				GaloisGoodOpenLocalize.Read(M).At(k, L, C, t, a, c)))
	}),
})}
