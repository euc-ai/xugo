// invertible.go — the invertible fractional ideals: the subring among
// them, closed under products and inverses, and the natural powers of an
// invertible ideal inside S; the multiples a · M of fractional ideals, the
// nonzero ones invertible exactly with M and the principal ideals a · S
// among the invertible; and the inverse into S of a set holding one, or
// lying inside S.

package fractional_ideal

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_extension"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// Products and inverses of invertible fractional ideals
// ---------------------------------------------------------------------------

// SubringInvertible — the subring is an invertible fractional ideal and
// its own inverse: S is a fractional ideal of itself and S · S = S, so
// FractionalInverseUnique applies at M = N = S.
var SubringInvertible = subringInvertibleThm{family.Add(registry.ProofEntry{
	Name: "SubringInvertible",
	Key:  "prop_30efcaac14afbd6",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S:set(A).",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
		},
		Conclusion: "«wfInvertible»(S) ∧ «wfInverse»(S) = S",
	},
		func(a *Argument, L field.FieldFact[on.L], S *Expr[Set[A]], subring Fact) {
			fractional := a.Have(
				"S is a fractional ideal of itself",
				"«wfFractional»(S)",
				By(SubringSubmodule.Read(L).At(S), subring))
			unit := a.Have(
				"S is the unit of the product, so S · S = S",
				"«wfMul»(S, S) = S",
				By(FractionalMulOne.Read(L).At(S, S), subring, fractional))
			a.Show(
				"a fractional ideal whose product with S is S, S is invertible and its own inverse",
				By(FractionalInverseUnique.Read(L).At(S, S, S), subring, fractional, unit))
		}),
})}

// InvertibleProduct — a product of invertible fractional ideals is
// invertible, its inverse the product of the inverses: in the commutative
// monoid of fractional ideals, associativity and left commutativity bring
// each factor next to its inverse, and the two cancellation equations
// reduce the product to S.
var InvertibleProduct = invertibleProductThm{family.Add(registry.ProofEntry{
	Name: "InvertibleProduct",
	Key:  "prop_b0d2a63d11ddf2ef",
	Reading: "For fractional ideals that are not invertible, (S : M · N) can be strictly " +
		"larger than (S : M) · (S : N); the invertibility of both factors is what makes them equal.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S M N:set(A).",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"«wfInvertible»(M)",
			"«wfInvertible»(N)",
		},
		Conclusion: "«wfInvertible»(«wfMul»(M, N)) ∧ " +
			"«wfInverse»(«wfMul»(M, N)) = «wfMul»(«wfInverse»(M), «wfInverse»(N))",
	},
		func(a *Argument, L field.FieldFact[on.L], S, M, N *Expr[Set[A]], h Fact) {
			parts := a.Conjuncts(
				h,
				"S is a subring of the field",
				"M is invertible",
				"and so is N")
			subring := parts[0]
			mData := a.Conjuncts(
				a.Unfolded(parts[1], InvertibleFractionalDef),
				"M is a fractional ideal",
				"whose product with its inverse is S")
			nData := a.Conjuncts(
				a.Unfolded(parts[2], InvertibleFractionalDef),
				"N is a fractional ideal",
				"whose product with its inverse is S")
			mModule, mCancel := mData[0], mData[1]
			nModule, nCancel := nData[0], nData[1]
			inverseM, inverseN := a.TermAs[Set[A]]("«wfInverse»(M)"), a.TermAs[Set[A]]("«wfInverse»(N)")
			product := a.TermAs[Set[A]]("«wfMul»(M, N)")
			inverseProduct := a.TermAs[Set[A]]("«wfMul»(«wfInverse»(M), «wfInverse»(N))")
			nPair := a.TermAs[Set[A]]("«wfMul»(N, «wfInverse»(N))")
			monoid := a.Have(
				"the fractional ideals form a commutative monoid under the product, with unit S",
				"comm_monoid_on({X:set(A) | «wfFractional»(X)}, «wfMul», S)",
				By(subring, FractionalIdealsCommMonoid.Read(L).At(S)))
			inverseMModule := a.Have(
				"the inverse of M is a fractional ideal",
				"«wfFractional»(«wfInverse»(M))",
				By(subring, submodule.SubmoduleSubset.Read(mModule), FractionalInverseSubmodule.Read(L).At(S, M)))
			inverseNModule := a.Have(
				"and so is the inverse of N",
				"«wfFractional»(«wfInverse»(N))",
				By(subring, submodule.SubmoduleSubset.Read(nModule), FractionalInverseSubmodule.Read(L).At(S, N)))
			productModule := a.Have(
				"the product M · N is a fractional ideal",
				"«wfFractional»(«wfMul»(M, N))",
				By(mModule, nModule, comm_monoid.OpIn.Read(monoid).AsFact().At(M, N)))
			inverseProductModule := a.Have(
				"and so is the product of the inverses",
				"«wfFractional»(«wfMul»(«wfInverse»(M), «wfInverse»(N)))",
				By(inverseMModule, inverseNModule, comm_monoid.OpIn.Read(monoid).AsFact().At(inverseM, inverseN)))
			nPairModule := a.Have(
				"and so is the product of N with its inverse",
				"«wfFractional»(«wfMul»(N, «wfInverse»(N)))",
				By(nModule, inverseNModule, comm_monoid.OpIn.Read(monoid).AsFact().At(N, inverseN)))
			unit := a.Have(
				"the product of M · N with the proposed inverse is S",
				"«wfMul»(«wfMul»(M, N), «wfMul»(«wfInverse»(M), «wfInverse»(N))) = S",
				CalcEq(
					Leg(
						a.TermAs[Set[A]]("«wfMul»(M, «wfMul»(N, «wfMul»(«wfInverse»(M), «wfInverse»(N))))"),
						"associate M outside",
						By(
							mModule,
							nModule,
							inverseProductModule,
							comm_monoid.AssocOn.Read(monoid).AsFact().At(M, N, inverseProduct))),
					Leg(
						a.TermAs[Set[A]]("«wfMul»(M, «wfMul»(«wfInverse»(M), «wfMul»(N, «wfInverse»(N))))"),
						"exchange N with the inverse of M",
						By(
							nModule,
							inverseMModule,
							inverseNModule,
							comm_monoid.LeftCommOn.Read(monoid).AsFact().At(N, inverseM, inverseN))),
					Leg(
						a.TermAs[Set[A]]("«wfMul»(«wfMul»(M, «wfInverse»(M)), «wfMul»(N, «wfInverse»(N)))"),
						"pair each ideal with its inverse",
						By(
							mModule,
							inverseMModule,
							nPairModule,
							comm_monoid.AssocOn.Read(monoid).AsFact().At(M, inverseM, nPair))),
					Leg(
						a.TermAs[Set[A]]("«wfMul»(S, S)"),
						"both inverse pairs cancel to S",
						mCancel.Rw(),
						nCancel.Rw(),
						Basic()),
					FinalLeg(
						"S is the product's unit",
						By(comm_monoid.IdentityIn.Read(monoid), comm_monoid.LeftIdentityOn.Read(monoid).AsFact().At(S)))))
			a.Show(
				"uniqueness of a fractional inverse proves invertibility and identifies the inverse",
				By(
					subring,
					productModule,
					inverseProductModule,
					unit,
					FractionalInverseUnique.Read(L).At(S, product, inverseProduct)))
		}),
})}

// InvertibleInverse — the inverse of an invertible fractional ideal is
// invertible, and its inverse is the ideal itself: (S : M) is a fractional
// ideal, its product with M is M · (S : M) = S the other way round, and the
// inverse of a fractional ideal is the one fractional ideal whose product
// with it is S.
var InvertibleInverse = invertibleInverseThm{family.Add(registry.ProofEntry{
	Name: "InvertibleInverse",
	Key:  "prop_e3a90b44da59f3fa",
	Reading: "For a fractional ideal that is not " +
		"invertible, (S : (S : M)) can be strictly larger than M.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S M:set(A).",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"«wfInvertible»(M)",
		},
		Conclusion: "«wfInvertible»(«wfInverse»(M)) ∧ «wfInverse»(«wfInverse»(M)) = M",
	},
		func(a *Argument, L field.FieldFact[on.L], S, M *Expr[Set[A]], hypotheses Fact) {
			parts := a.Conjuncts(
				hypotheses,
				"S is a subring of the field",
				"M is invertible")
			subring, invertible := parts[0], parts[1]
			opened := a.Conjuncts(
				a.Unfolded(invertible, InvertibleFractionalDef),
				"M is a fractional ideal",
				"whose product with (S : M) is S")
			fractional, product := opened[0], opened[1]
			inverse := a.TermAs[Set[A]]("«wfInverse»(M)")
			mInL := a.Have(
				"a fractional ideal lies in the field",
				"M ⊆ L.carrier",
				By(submodule.SubmoduleSubset.Read(fractional)))
			inverseFractional := a.Have(
				"(S : M) is a fractional ideal",
				"«wfFractional»(«wfInverse»(M))",
				By(FractionalInverseSubmodule.Read(L).At(S, M), subring, mInL))
			commuted := a.Have(
				"taken the other way round, the product of (S : M) with M is S",
				"«wfMul»(«wfInverse»(M), M) = S",
				CalcEq(
					Leg(
						a.TermAs[Set[A]]("«wfMul»(M, «wfInverse»(M))"),
						"the product commutes, (S : M) and M lying in the field",
						By(FractionalMulComm.Read(L).At(S, inverse, M), FractionalInverseSubset.Read(L).At(S, M), mInL)),
					FinalLeg(
						"and M · (S : M) is S, M being invertible",
						By(product)),
				))
			a.Show(
				"(S : M) and M are fractional ideals whose product is S, so (S : M) is invertible with inverse M",
				By(
					FractionalInverseUnique.Read(L).At(S, inverse, M),
					subring,
					inverseFractional,
					fractional,
					commuted))
		}),
})}

// InvertibleIdealPowers — the natural powers of an invertible ideal N inside
// S are invertible ideals inside S. By induction on n: the zeroth power is S,
// invertible and its own inverse; the next is N · Nⁿ, a product of invertible
// fractional ideals (InvertibleProduct), and it lies in S · Nⁿ = Nⁿ, N lying
// in S.
var InvertibleIdealPowers = invertibleIdealPowersThm{family.Add(registry.ProofEntry{
	Name: "InvertibleIdealPowers",
	Key:  "prop_47c3bf9706b73a6",
	Reading: "N ⊆ S is used only for the powers lying in S: the " +
		"powers of any invertible fractional ideal are invertible.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S N:set(A). ∀n:num.",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"«wfInvertible»(N)",
			"N ⊆ S",
		},
		Conclusion: "«wfInvertible»(«power»(n)) ∧ «power»(n) ⊆ S",
		Abbrev: Abbrev{
			{Name: "power", Text: "λn:num. " +
				"    monoid_pow(λX:set(A). λY:set(A). fractional_mul(field_ring(L), S, X, Y), S, N, n)"},
		},
	},
		func(a *Argument, L field.FieldFact[on.L], S, N *Expr[Set[A]], n *Expr[Nat], h Fact) {
			given := a.Conjuncts(
				h,
				"S is a subring of L",
				"N is invertible",
				"N lies in S")
			subring, invertible, inS := given[0], given[1], given[2]
			fieldRing := a.TermAs[RingOps[A]]("field_ring(L)")
			powers := a.Have(
				"every natural power of N is an invertible ideal inside S",
				"∀m:num. «wfInvertible»(«power»(m)) ∧ «power»(m) ⊆ S",
				Derive(func(b *Argument) {
					b.Induct("m")
					b.Base(
						"the zeroth power is S, invertible and inside itself",
						Simp(Fwd(comm_monoid.MonoidPowDef.Inst[Set[A]]())),
						By(subring, set_order.SubsetRefl, SubringInvertible.Read(L).At(S)))
					b.Step(
						"the next power is N times the last, invertible and inside the last",
						func(c *Argument, ih Fact) {
							last := c.TermAs[Set[A]]("«power»(m)")
							next := c.TermAs[Set[A]]("«wfMul»(N, «power»(m))")
							previous := c.Conjuncts(
								ih,
								"Nᵐ is invertible",
								"and lies inside S")
							productInvertible := c.Have(
								"N · Nᵐ is invertible",
								"«wfInvertible»(«wfMul»(N, «power»(m)))",
								By(subring, invertible, previous[0], InvertibleProduct.Read(L).At(S, N, last)))
							absorbed := c.Have(
								"N · Nᵐ lies in S · Nᵐ, which is Nᵐ",
								"«wfMul»(N, «power»(m)) ⊆ «power»(m)",
								By(
									subring,
									inS,
									previous[0],
									InvertibleFractionalDef.At(fieldRing, S, last),
									set_order.SubsetRefl,
									FractionalMulMono.Read(L).At(S, N, S, last, last),
									FractionalMulOne.Read(L).At(S, last)))
							c.Do(Simp(Fwd(comm_monoid.MonoidPowDef.Inst[Set[A]]())))
							c.Show(
								"so the next power is invertible and lies inside S",
								By(productInvertible, absorbed, previous[1], set_order.SubsetTrans.At(next, last, S)))
						})
				}))
			a.Show(
				"in particular the n-th",
				By(powers.At(n)))
		}),
})}

// ---------------------------------------------------------------------------
// Multiples
// ---------------------------------------------------------------------------

// FractionalInverseScale — dividing into a multiple: (S : a · X) is
// inv(a) · (S : X). The two sets have the same members. A member x of
// (S : a · X) multiplies each a · y, y ∈ X, into S, so x · a multiplies
// each y into S, (x · a) · y being x · (a · y); thus x · a lies in (S : X),
// and x = inv(a) · (x · a) since inv(a) · a = one. Conversely inv(a) · z,
// for z in (S : X), lies in L, and its product with a · y is z · y, which
// lies in S.
var FractionalInverseScale = fractionalInverseScaleThm{family.Add(registry.ProofEntry{
	Name: "FractionalInverseScale",
	Key:  "prop_ea9212fb4d79baee",
	Reading: "a ≠ L.zero is load-bearing: when L.zero ∈ S and X is non-empty, (S : " +
		"L.zero · X) is all of L, while L.inv(L.zero) · (S : X) is {L.zero}, L.inv(L.zero) " +
		"being L.zero in this encoding. X ⊆ L.carrier is load-bearing: (x · a) · y = x · (a " +
		"· y) is the field's associativity, which holds at members of L. S is unrestricted.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S X:set(A). ∀a:A.",
		Hypotheses: []string{
			"a ∈ L.carrier",
			"¬(a = L.zero)",
			"X ⊆ L.carrier",
		},
		Conclusion: "«wfInverse»(image(L.mul(a), X)) = image(L.mul(L.inv(a)), «wfInverse»(X))",
	},
		func(arg *Argument, L field.FieldFact[on.L], S, X *Expr[Set[A]], a *Expr[A], hypotheses Fact) {
			parts := arg.Conjuncts(
				hypotheses,
				"a lies in L",
				"a is not zero",
				"X lies in L")
			aIn, nonzero, xInL := parts[0], parts[1], parts[2]
			ring := field.RingOn.Read(L)
			invIn := arg.Have(
				"L.inv(a) lies in L",
				"L.inv(a) ∈ L.carrier",
				By(aIn, field.InvIn.Read(L)))
			inverts := arg.Have(
				"and inverts a, which is not zero",
				"L.inv(a) * a = L.one",
				By(aIn, nonzero, field.MulLeftInverseOn.Read(L)))
			byA, byInvA := arg.TermAs[Fun[A, A]]("L.mul(a)"), arg.TermAs[Fun[A, A]]("L.mul(L.inv(a))")
			inverse := arg.TermAs[Set[A]]("«wfInverse»(X)")

			members := arg.Have(
				"x lies in (S : a · X) exactly when it is L.inv(a) times a member of (S : X)",
				"∀x:A. x ∈ «wfInverse»(image(L.mul(a), X)) ⇔ x ∈ image(L.mul(L.inv(a)), «wfInverse»(X))",
				Derive(func(b *Argument) {
					x := b.FixAs[A]()
					intoS := b.TermAs[Set[A]]("λm:A. x * m ∈ S")
					b.Iff()
					b.Forward(
						"x · a lies in (S : X), and x = L.inv(a) · (x · a)",
						func(c *Argument, in Fact) {
							member := c.Have(
								"x lies in L and multiplies a · X into S",
								"x ∈ L.carrier ∧ (∀m:A. m ∈ image(L.mul(a), X) ⇒ x * m ∈ S)",
								BySets(c.Unfolded(in, FractionalInverseDef)))
							opened := c.Conjuncts(
								member,
								"x lies in L",
								"and multiplies a · X into S")
							xIn, multiplies := opened[0], opened[1]
							scaled := c.Have(
								"that is, x · (a · y) lies in S for each y ∈ X",
								"∀y:A. y ∈ X ⇒ x * (a * y) ∈ S",
								By(multiplies, set_image.ForallInImage.At(byA, X, intoS)))
							products := c.Have(
								"so (x · a) · y lies in S for each y ∈ X",
								"∀y:A. y ∈ X ⇒ x * a * y ∈ S",
								Derive(func(d *Argument) {
									d.FixAs[A]("y")
									yX := d.Assume()
									yIn := d.Have(
										"y lies in L",
										"y ∈ L.carrier",
										BySets(yX, xInL))
									regroup := d.Have(
										"(x · a) · y = x · (a · y) by associativity in L",
										"x * a * y = x * (a * y)",
										ByArith(ring, xIn, aIn, yIn))
									d.Show(
										"which lies in S",
										regroup.Rw(),
										By(scaled, yX))
								}))
							xaIn := c.Have(
								"x · a lies in L",
								"x * a ∈ L.carrier",
								By(xIn, aIn, comm_ring.MulIn.Read(ring)))
							divides := c.Have(
								"so x · a lies in (S : X)",
								"x * a ∈ «wfInverse»(X)",
								Unfold(FractionalInverseDef),
								BySets(xaIn, products))
							recovered := c.Have(
								"x = L.inv(a) · (x · a), as L.inv(a) · a = L.one",
								"x = L.inv(a) * (x * a)",
								ByArith(ring, xIn, aIn, invIn, Scaled(x, inverts)))
							c.Show(
								"so x is L.inv(a) times a member of (S : X)",
								By(recovered, divides, set_image.FunInImage.At(byInvA, inverse, c.TermAs[A]("x * a"))))
						})
					b.Backward(
						"x = L.inv(a) · z with z ∈ (S : X), whose product with a · y is z · y",
						func(c *Argument, in Fact) {
							_, written := c.ObtainAs[A](
								"x is L.inv(a) · z for some z in (S : X)",
								"∃z:A. x = L.inv(a) * z ∧ z ∈ «wfInverse»(X)",
								By(in, set_basic.InImage))
							given := c.Conjuncts(
								written,
								"x = L.inv(a) · z",
								"z lies in (S : X)")
							isScaled := given[0]
							member := c.Have(
								"z lies in L and multiplies X into S",
								"z ∈ L.carrier ∧ (∀m:A. m ∈ X ⇒ z * m ∈ S)",
								BySets(c.Unfolded(given[1], FractionalInverseDef)))
							opened := c.Conjuncts(
								member,
								"z lies in L",
								"and multiplies X into S")
							zIn, multiplies := opened[0], opened[1]
							xIn := c.Have(
								"x lies in L, a product of two members of L",
								"x ∈ L.carrier",
								isScaled.Rw(),
								By(invIn, zIn, comm_ring.MulIn.Read(ring)))
							products := c.Have(
								"x · (a · y) lies in S for each y ∈ X",
								"∀y:A. y ∈ X ⇒ x * (a * y) ∈ S",
								Derive(func(d *Argument) {
									d.FixAs[A]("y")
									yX := d.Assume()
									yIn := d.Have(
										"y lies in L",
										"y ∈ L.carrier",
										BySets(yX, xInL))
									cancel := d.Have(
										"L.inv(a) · z · (a · y) = z · y, as L.inv(a) · a = L.one",
										"x * (a * y) = z * y",
										ByArith(
											ring,
											xIn,
											zIn,
											aIn,
											invIn,
											yIn,
											Scaled(d.TermAs[A]("a * y"), isScaled),
											Scaled(d.TermAs[A]("z * y"), inverts)))
									d.Show(
										"which lies in S",
										cancel.Rw(),
										By(multiplies, yX))
								}))
							scaled := c.Have(
								"that is, x multiplies a · X into S",
								"∀m:A. m ∈ image(L.mul(a), X) ⇒ x * m ∈ S",
								By(products, set_image.ForallInImage.At(byA, X, intoS)))
							c.Show(
								"so x lies in (S : a · X)",
								Unfold(FractionalInverseDef),
								BySets(xIn, scaled))
						})
				}))
			arg.Show(
				"the two sets have the same members",
				By(members, set_basic.Extension))
		}),
})}

// ScaleSubmodule — a multiple of a fractional ideal is a fractional ideal:
// a · M is the image of the submodule M under multiplication by a, an
// S-linear map of L (ScaleLinear).
var ScaleSubmodule = scaleSubmoduleThm{family.Add(registry.ProofEntry{
	Name: "ScaleSubmodule",
	Key:  "prop_a932df2c23894e5a",
	Reading: "a may be zero, zero · M being {zero}; " +
		"neither a ≠ zero nor the invertibility of M enters.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S M:set(A). ∀a:A.",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"a ∈ L.carrier",
			"«wfFractional»(M)",
		},
		Conclusion: "«wfFractional»(image(L.mul(a), M))",
	},
		func(arg *Argument, L field.FieldFact[on.L], S, M *Expr[Set[A]], a *Expr[A], given Fact) {
			parts := arg.Conjuncts(
				given,
				"S is a subring of L",
				"a lies in L",
				"M is a fractional ideal")
			subring, aInL, fractional := parts[0], parts[1], parts[2]
			arg.Show(
				"a · M is the image of M under multiplication by a, which is S-linear on L, so a submodule",
				By(
					module_homomorphism.HomImageSubmodule,
					field_extension.ScaleLinear.Read(L).At(S, arg.MemberOf[on.L](a, aInL)),
					subring,
					fractional))
		}),
})}

// ScaleOne — multiplying by one leaves a subset of the field as it is: one is
// the unit of the field's product, one · m = m for every m in L.
var ScaleOne = scaleOneThm{family.Add(registry.ProofEntry{
	Name: "ScaleOne",
	Key:  "prop_bb1ec2e21758890f",
	Build: family.Theorem(Statement{
		Binders:    "∀L:field_on(A). ∀M:set(A).",
		Hypotheses: []string{"M ⊆ L.carrier"},
		Conclusion: "image(L.mul(L.one), M) = M",
	},
		func(arg *Argument, L field.FieldFact[on.L], M *Expr[Set[A]], inL Fact) {
			arg.Show(
				"one fixes every member of L, and M lies in L",
				BySets(inL, comm_monoid.LeftIdentityOn.Read(comm_ring.MulMonoidOn.Read(field.RingOn.Read(L)))))
		}),
})}

// ScaleScale — multiplying by a and then by b is multiplying by b · a, for a
// and b in the field and a subset of it: b · (a · m) = (b · a) · m for every m
// in L, the field's product being associative.
var ScaleScale = scaleScaleThm{family.Add(registry.ProofEntry{
	Name: "ScaleScale",
	Key:  "prop_baad58285f643a93",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀M:set(A). ∀a b:A.",
		Hypotheses: []string{
			"a ∈ L.carrier",
			"b ∈ L.carrier",
			"M ⊆ L.carrier",
		},
		Conclusion: "image(L.mul(b), image(L.mul(a), M)) = image(L.mul(b * a), M)",
	},
		func(arg *Argument, L field.FieldFact[on.L], M *Expr[Set[A]], a, b *Expr[A], given Fact) {
			parts := arg.Conjuncts(
				given,
				"a lies in L",
				"and so does b",
				"M lies in L")
			multiplicative := comm_ring.MulMonoidOn.Read(field.RingOn.Read(L))
			arg.Show(
				"(b · a) · m = b · (a · m) for every m in M, M lying in L",
				BySets(parts[0], parts[1], parts[2], comm_monoid.AssocOn.Read(multiplicative).AsFact().At(b, a)))
		}),
})}

// FractionalMulScale — a multiple comes out of the left factor of a
// product: (a · M) · N = a · (M · N). The fractional ideal a · (M · N)
// holds each product (a * m) * n = a * (m * n), so it holds (a · M) · N.
// Conversely the colon of (a · M) · N by {a} is a fractional ideal holding
// each m * n, as (m * n) * a = (a * m) * n; so it holds M · N, and
// a * w = w * a lies in (a · M) · N for every w in M · N.
var FractionalMulScale = fractionalMulScaleThm{family.Add(registry.ProofEntry{
	Name: "FractionalMulScale",
	Key:  "prop_9c7c53b9e07bcba3",
	Reading: "a may be L.zero, both sides being {L.zero} then. M ⊆ L.carrier and N ⊆ " +
		"L.carrier keep the products in L, where the field's product associates and commutes.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S M N:set(A). ∀a:A.",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"a ∈ L.carrier",
			"M ⊆ L.carrier",
			"N ⊆ L.carrier",
		},
		Conclusion: "«wfMul»(image(L.mul(a), M), N) = image(L.mul(a), «wfMul»(M, N))",
		Abbrev: Abbrev{
			// The colon ((a · M) · N : {a}): the members y of L with y * a in (a · M) · N.
			{Name: "colon", Text: "{y:A | " +
				"    y ∈ L.carrier ∧ (∀n:A. n ∈ {a} ⇒ y * n ∈ «wfMul»(image(L.mul(a), M), N))}"},
		},
	},
		func(arg *Argument, L field.FieldFact[on.L], S, M, N *Expr[Set[A]], a *Expr[A], given Fact) {
			parts := arg.Conjuncts(
				given,
				"S is a subring of L",
				"a lies in L",
				"M lies in L",
				"and so does N")
			subring, aInL, mInL, nInL := parts[0], parts[1], parts[2], parts[3]
			ringL := field.RingOn.Read(L)
			am := arg.MemberOf[on.L](a, aInL)
			byA := arg.TermAs[Fun[A, A]]("L.mul(a)")
			scaled, product := arg.TermAs[Set[A]]("image(L.mul(a), M)"), arg.TermAs[Set[A]]("«wfMul»(M, N)")
			left, right :=
				arg.TermAs[Set[A]]("«wfMul»(image(L.mul(a), M), N)"),
				arg.TermAs[Set[A]]("image(L.mul(a), «wfMul»(M, N))")
			fractional := arg.Have(
				"M · N is a fractional ideal",
				"«wfFractional»(«wfMul»(M, N))",
				By(FractionalMulSubmodule.Read(L).At(S, M, N), subring, mInL, nInL))
			scaledInL := arg.Have(
				"a · M lies in L",
				"image(L.mul(a), M) ⊆ L.carrier",
				BySets(aInL, mInL, comm_ring.MulIn.Read(ringL)))

			within := arg.Have(
				"(a · M) · N lies in a · (M · N), a fractional ideal holding each (a * m) * n = a * (m * n)",
				"«wfMul»(image(L.mul(a), M), N) ⊆ image(L.mul(a), «wfMul»(M, N))",
				Derive(func(b *Argument) {
					ideal := b.Have(
						"a · (M · N) is a fractional ideal",
						"«wfFractional»(image(L.mul(a), «wfMul»(M, N)))",
						By(ScaleSubmodule.Read(L).At(S, product, am), subring, fractional))
					holds := b.Have(
						"it holds each product of a · M with N",
						"∀x n:A. x ∈ image(L.mul(a), M) ∧ n ∈ N ⇒ x * n ∈ image(L.mul(a), «wfMul»(M, N))",
						Derive(func(c *Argument) {
							c.FixAs[A]("x")
							n := c.FixAs[A]("n")
							in := c.Conjuncts(
								c.Assume(),
								"x lies in a · M",
								"n lies in N")
							m, written := c.ObtainAs[A](
								"x is a * m for some m in M",
								"∃m:A. x = a * m ∧ m ∈ M",
								By(in[0], set_basic.InImage))
							w := c.Conjuncts(
								written,
								"x = a * m",
								"m lies in M")
							mm := c.MemberOf[on.L](m, c.Have(
								"m lies in L",
								"m ∈ L.carrier",
								BySets(mInL, w[1])))
							nm := c.MemberOf[on.L](n, c.Have(
								"n lies in L",
								"n ∈ L.carrier",
								BySets(nInL, in[1])))
							regroup := c.Have(
								"x * n = (a * m) * n = a * (m * n)",
								"x * n = a * (m * n)",
								w[0].Rw(),
								By(comm_monoid.AssocOn.Read(comm_ring.MulMonoidOn.Read(ringL)).At(am, mm, nm)))
							held := c.Have(
								"m * n lies in M · N",
								"m * n ∈ «wfMul»(M, N)",
								By(FractionalMulHolds.Read(L).At(S, M, N, m, n), w[1], in[1]))
							c.Show(
								"so x * n is a times a member of M · N",
								regroup.Rw(),
								By(held, set_image.FunInImage.At(byA, product, c.TermAs[A]("m * n"))))
						}))
					b.Show(
						"so (a · M) · N lies in it",
						By(FractionalMulLeast.Read(L).At(S, scaled, N, right), ideal, holds))
				}))

			covering := arg.Have(
				"a · (M · N) lies in (a · M) · N: the colon of (a · M) · N by {a} holds every m * n, so M · N",
				"image(L.mul(a), «wfMul»(M, N)) ⊆ «wfMul»(image(L.mul(a), M), N)",
				Derive(func(b *Argument) {
					outer := b.Have(
						"(a · M) · N is a fractional ideal",
						"«wfFractional»(«wfMul»(image(L.mul(a), M), N))",
						By(FractionalMulSubmodule.Read(L).At(S, scaled, N), subring, scaledInL, nInL))
					colonIdeal := b.Have(
						"so is its colon by {a}, the members y of L with y * a in (a · M) · N",
						"«wfFractional»(«colon»)",
						By(
							ColonSubmodule.Read(L).At(S, left, b.TermAs[Set[A]]("{a}")),
							comm_ring.SubringSubset.Read(subring),
							outer,
							aInL,
							set_order.SingSubset))
					holds := b.Have(
						"it holds each m * n, as (m * n) * a = (a * m) * n with a * m in a · M",
						"∀m n:A. m ∈ M ∧ n ∈ N ⇒ m * n ∈ «colon»",
						Derive(func(c *Argument) {
							m, n := c.FixAs[A]("m"), c.FixAs[A]("n")
							in := c.Conjuncts(
								c.Assume(),
								"m lies in M",
								"n lies in N")
							inL := c.Have(
								"m and n lie in L",
								"m ∈ L.carrier ∧ n ∈ L.carrier",
								BySets(mInL, nInL, in[0], in[1]))
							held := c.Have(
								"a * m lies in a · M, so (a * m) * n lies in (a · M) · N",
								"a * m * n ∈ «wfMul»(image(L.mul(a), M), N)",
								By(
									FractionalMulHolds.Read(L).At(S, scaled, N, c.TermAs[A]("a * m"), n),
									in[0],
									set_image.FunInImage.At(byA, M, m),
									in[1]))
							regroup := c.Have(
								"the field's product associates and commutes",
								"m * n * a = a * m * n",
								ByArith(ringL, inL, aInL))
							moved := c.Have(
								"so (m * n) * a lies in (a · M) · N",
								"m * n * a ∈ «wfMul»(image(L.mul(a), M), N)",
								regroup.Rw(),
								By(held))
							c.Show(
								"m * n lies in L, and its product with a lies in (a · M) · N",
								BySets(inL, comm_ring.MulIn.Read(ringL), moved))
						}))
					spanned := b.Have(
						"so it holds M · N",
						"«wfMul»(M, N) ⊆ «colon»",
						By(FractionalMulLeast.Read(L).At(S, M, N, b.TermAs[Set[A]]("«colon»")), colonIdeal, holds))
					b.Show(
						"so a * w = w * a lies in (a · M) · N for every w in M · N",
						BySets(spanned, aInL, comm_monoid.CommOn.Read(comm_ring.MulMonoidOn.Read(ringL))))
				}))
			arg.Show(
				"the two inclusions are the equation",
				By(within, covering, set_order.SubsetAntisym))
		}),
})}

// PrincipalProduct — principal fractional ideals multiply as their
// generators do: (xS) · (yS) = (xy)S for x and y in the field. The scalar x
// factors out of the product (FractionalMulScale), S is the unit on the
// fractional ideal yS (FractionalMulOne), and multiplying by y and then by x is
// multiplying by xy (ScaleScale).
var PrincipalProduct = principalProductThm{family.Add(registry.ProofEntry{
	Name: "PrincipalProduct",
	Key:  "prop_bb2bf853ceb7bd6d",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S:set(A). ∀x y:A.",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"x ∈ L.carrier",
			"y ∈ L.carrier",
		},
		Conclusion: "«wfMul»(image(L.mul(x), S), image(L.mul(y), S)) = image(L.mul(x * y), S)",
	},
		func(arg *Argument, L field.FieldFact[on.L], S *Expr[Set[A]], x, y *Expr[A], given Fact) {
			parts := arg.Conjuncts(
				given,
				"S is a subring of L",
				"x lies in L",
				"y lies in L")
			subring, xIn, yIn := parts[0], parts[1], parts[2]
			xm, ym := arg.MemberOf[on.L](x, xIn), arg.MemberOf[on.L](y, yIn)
			inField := arg.Have(
				"S lies in L",
				"S ⊆ L.carrier",
				By(comm_ring.SubringSubset.Read(subring)))
			yS := arg.TermAs[Set[A]]("image(L.mul(y), S)")
			fractional := arg.Have(
				"yS is a fractional ideal",
				"«wfFractional»(image(L.mul(y), S))",
				By(subring, ym, ScaleSubmodule.Read(L).At(S, S, ym), SubringSubmodule.Read(L).At(S)))
			ySIn := arg.Have(
				"yS lies in L",
				"image(L.mul(y), S) ⊆ L.carrier",
				By(submodule.SubmoduleSubset.Read(fractional)))
			arg.Show(
				"factor x out, drop the unit S, and compose the two scalings",
				CalcEq(
					Leg(
						arg.TermAs[Set[A]]("image(L.mul(x), «wfMul»(S, image(L.mul(y), S)))"),
						"the scalar x factors out of the product",
						By(subring, xm, inField, ySIn, FractionalMulScale.Read(L).At(S, S, yS, xm))),
					Leg(
						arg.TermAs[Set[A]]("image(L.mul(x), image(L.mul(y), S))"),
						"S fixes the fractional ideal yS",
						By(subring, fractional, FractionalMulOne.Read(L).At(S, yS))),
					FinalLeg(
						"successive scalings multiply their scalars",
						By(inField, ScaleScale.Read(L).At(S, ym, xm)))))
		}),
})}

// ScaleCancel — dividing by a nonzero member a of the field undoes
// multiplying by it: inv(a) · (a · M) = M for every subset M of the field.
// Each m in L has inv(a) · (a · m) = (inv(a) · a) · m = m.
var ScaleCancel = scaleCancelThm{family.Add(registry.ProofEntry{
	Name: "ScaleCancel",
	Key:  "prop_fa440afa943757eb",
	Reading: "a ≠ zero is load-bearing: inv(zero) is zero in this encoding, so at a " +
		"= zero the left side is {zero} for every non-empty M. M ⊆ L is load-bearing: " +
		"off L the product is unspecified, and a member of M outside L need not come back.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀M:set(A). ∀a:A.",
		Hypotheses: []string{
			"a ∈ L.carrier",
			"a ≠ L.zero",
			"M ⊆ L.carrier",
		},
		Conclusion: "image(L.mul(L.inv(a)), image(L.mul(a), M)) = M",
	},
		func(arg *Argument, L field.FieldFact[on.L], M *Expr[Set[A]], a *Expr[A], given Fact) {
			parts := arg.Conjuncts(
				given,
				"a lies in L",
				"a is not zero",
				"M lies in L")
			aInL, nonzero, mInL := parts[0], parts[1], parts[2]
			am := arg.MemberOf[on.L](a, aInL)
			cancel := arg.Have(
				"inv(a) undoes multiplication by a on L",
				"∀m:A. m ∈ L.carrier ⇒ L.inv(a) * (a * m) = m",
				Derive(func(b *Argument) {
					m := b.FixAs[A]("m")
					mm := b.MemberOf[on.L](m, b.Assume())
					b.Show(
						"inv(a) · (a · m) = (inv(a) · a) · m = m",
						ByArith(
							field.RingOn.Read(L),
							am,
							mm,
							field.InvIn.Read(L).At(am),
							nonzero,
							Scaled(m, field.MulLeftInverseOn.Read(L).AsFact().At(am))))
				}))
			arg.Show(
				"so inv(a) · (a · M) = M, M lying in L",
				BySets(cancel, mInL))
		}),
})}

// InvertibleScale — a nonzero multiple of a subset of the field is
// invertible exactly when the subset is, and the nonzero multiples of S
// are invertible: the principal fractional ideals. For an invertible M, a · M
// is a fractional ideal (ScaleSubmodule) whose inverse is inv(a) · (S : M)
// (FractionalInverseScale), and a and inv(a) come out of the product and
// cancel (FractionalMulScale), so (a · M) · (S : a · M) = M · (S : M) = S.
// Dividing by a undoes the multiple (ScaleCancel), which gives the
// converse, and S, its own inverse, is invertible, which gives a · S.
var InvertibleScale = invertibleScaleThm{family.Add(registry.ProofEntry{
	Name: "InvertibleScale",
	Key:  "prop_48b7ea365a13a7d5",
	Reading: "a ≠ zero is load-bearing: zero · M is {zero} or ∅, never " +
		"invertible, as one ∉ {zero}. M ⊆ L is load-bearing for ⇒: a member of " +
		"M outside L has a multiple nothing controls, which may land in a · M.",
	Build: family.Sections(Statement{
		Binders: "∀L:field_on(A). ∀S M:set(A). ∀a:A.",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"a ∈ L.carrier",
			"a ≠ L.zero",
			"M ⊆ L.carrier",
		},
		Conclusion: "(«wfInvertible»(image(L.mul(a), M)) ⇔ «wfInvertible»(M)) ∧ " +
			"«wfInvertible»(image(L.mul(a), S))",
	},
		func(ctx *Script, headline string) *GoalStackNode {
			scaling := ctx.Lemma(Statement{
				Binders: "∀L:field_on(A). ∀S M:set(A). ∀a:A.",
				Hypotheses: []string{
					"subring(field_ring(L), S)",
					"a ∈ L.carrier",
					"a ≠ L.zero",
					"«wfInvertible»(M)",
				},
				Conclusion: "«wfInvertible»(image(L.mul(a), M))",
			},
				func(arg *Argument, L field.FieldFact[on.L], S, M *Expr[Set[A]], a *Expr[A], given Fact) {
					parts := arg.Conjuncts(
						given,
						"S is a subring of L",
						"a lies in L",
						"a is not zero",
						"M is invertible")
					subring, aInL, nonzero, invertibleM := parts[0], parts[1], parts[2], parts[3]
					invertible := arg.Conjuncts(
						arg.Unfolded(invertibleM, InvertibleFractionalDef),
						"M is a fractional ideal",
						"whose product with (S : M) is S")
					fractional, unit := invertible[0], invertible[1]
					ringL := field.RingOn.Read(L)
					am := arg.MemberOf[on.L](a, aInL)
					invIn := field.InvIn.Read(L).At(am)
					scaled, inverse := arg.TermAs[Set[A]]("image(L.mul(a), M)"), arg.TermAs[Set[A]]("«wfInverse»(M)")
					inverseScaled := arg.TermAs[Set[A]]("image(L.mul(L.inv(a)), «wfInverse»(M))")
					inverseInL := FractionalInverseSubset.Read(L).At(S, M)
					mInL := arg.Have(
						"M lies in L",
						"M ⊆ L.carrier",
						By(submodule.SubmoduleSubset.Read(fractional)))
					scaledFractional := arg.Have(
						"a · M is a fractional ideal",
						"«wfFractional»(image(L.mul(a), M))",
						By(ScaleSubmodule.Read(L).At(S, M, am), subring, fractional))
					scaledInL := arg.Have(
						"so it lies in L",
						"image(L.mul(a), M) ⊆ L.carrier",
						By(submodule.SubmoduleSubset.Read(scaledFractional)))
					inverseScaledInL := arg.Have(
						"and inv(a) · (S : M) lies in L",
						"image(L.mul(L.inv(a)), «wfInverse»(M)) ⊆ L.carrier",
						BySets(invIn, inverseInL, comm_ring.MulIn.Read(ringL)))
					productInL := arg.Have(
						"M · (S : M) is S, which lies in L",
						"«wfMul»(M, «wfInverse»(M)) ⊆ L.carrier",
						By(Normalized, unit, comm_ring.SubringSubset.Read(subring)))
					inverseOfScaled := arg.Have(
						"the inverse of a · M is inv(a) · (S : M)",
						"«wfInverse»(image(L.mul(a), M)) = image(L.mul(L.inv(a)), «wfInverse»(M))",
						By(FractionalInverseScale.Read(L).At(S, M, am), nonzero, mInL))
					cancelled := arg.Have(
						"a and inv(a) cancel in the product: (a · M) · (inv(a) · (S : M)) = M · (S : M)",
						"«wfMul»(image(L.mul(a), M), image(L.mul(L.inv(a)), «wfInverse»(M))) = «wfMul»(M, «wfInverse»(M))",
						CalcEq(
							Leg(
								arg.TermAs[Set[A]]("«wfMul»(image(L.mul(L.inv(a)), «wfInverse»(M)), image(L.mul(a), M))"),
								"the product commutes",
								By(FractionalMulComm.Read(L).At(S, scaled, inverseScaled), scaledInL, inverseScaledInL)),
							Leg(
								arg.TermAs[Set[A]]("image(L.mul(L.inv(a)), «wfMul»(«wfInverse»(M), image(L.mul(a), M)))"),
								"inv(a) comes out of the left factor",
								By(FractionalMulScale.Read(L).At(S, inverse, scaled, invIn), subring, inverseInL, scaledInL)),
							Leg(
								arg.TermAs[Set[A]]("image(L.mul(L.inv(a)), «wfMul»(image(L.mul(a), M), «wfInverse»(M)))"),
								"the inner product commutes",
								By(FractionalMulComm.Read(L).At(S, inverse, scaled), inverseInL, scaledInL)),
							Leg(
								arg.TermAs[Set[A]]("image(L.mul(L.inv(a)), image(L.mul(a), «wfMul»(M, «wfInverse»(M))))"),
								"and a comes out of its left factor",
								By(FractionalMulScale.Read(L).At(S, M, inverse, am), subring, mInL, inverseInL)),
							FinalLeg(
								"inv(a) undoes a on M · (S : M), which lies in L",
								By(L, aInL, nonzero, productInL, ScaleCancel))))
					product := arg.Have(
						"so (a · M) · (S : a · M) = S",
						"«wfMul»(image(L.mul(a), M), «wfInverse»(image(L.mul(a), M))) = S",
						CalcEq(
							Leg(
								arg.TermAs[Set[A]]("«wfMul»(image(L.mul(a), M), image(L.mul(L.inv(a)), «wfInverse»(M)))"),
								"the inverse of a · M is inv(a) · (S : M)",
								By(inverseOfScaled)),
							Leg(
								arg.TermAs[Set[A]]("«wfMul»(M, «wfInverse»(M))"),
								"a and inv(a) cancel",
								By(cancelled)),
							FinalLeg(
								"M is invertible",
								By(unit))))
					arg.Show(
						"a · M is a fractional ideal whose product with its inverse is S",
						By(InvertibleFractionalDef, scaledFractional, product))
				})
			return ctx.Theorem(headline,
				func(arg *Argument, L field.FieldFact[on.L], S, M *Expr[Set[A]], a *Expr[A], given Fact) {
					parts := arg.Conjuncts(
						given,
						"S is a subring of L",
						"a lies in L",
						"a is not zero",
						"M lies in L")
					subring, aInL, nonzero, mInL := parts[0], parts[1], parts[2], parts[3]
					am := arg.MemberOf[on.L](a, aInL)
					equivalent := arg.Have(
						"a · M is invertible exactly when M is",
						"«wfInvertible»(image(L.mul(a), M)) ⇔ «wfInvertible»(M)",
						Derive(func(b *Argument) {
							b.Iff()
							b.Forward(
								"M is inv(a) · (a · M), a nonzero multiple of the invertible a · M",
								func(c *Argument, scaledInvertible Fact) {
									back := c.Have(
										"dividing a · M by a gives M back",
										"image(L.mul(L.inv(a)), image(L.mul(a), M)) = M",
										By(L, aInL, nonzero, mInL, ScaleCancel))
									divided := c.Have(
										"inv(a) · (a · M) is invertible",
										"«wfInvertible»(image(L.mul(L.inv(a)), image(L.mul(a), M)))",
										By(
											L,
											subring,
											field.InvIn.Read(L).At(am),
											field.InvEqZeroOn.Read(L).At(am),
											nonzero,
											scaledInvertible,
											scaling))
									c.Show(
										"and it is M",
										By(Normalized, back, divided))
								})
							b.Backward(
								"a nonzero multiple of the invertible M is invertible",
								func(c *Argument, invertibleM Fact) {
									c.Show(
										"a · M is invertible",
										By(L, subring, aInL, nonzero, invertibleM, scaling))
								})
						}))
					principal := arg.Have(
						"S is invertible, and so is its nonzero multiple a · S",
						"«wfInvertible»(image(L.mul(a), S))",
						By(L, subring, aInL, nonzero, SubringInvertible.Read(L).At(S), scaling))
					arg.Show(
						"a · M is invertible exactly when M is, and a · S is invertible",
						By(equivalent, principal))
				})
		}),
})}

// ---------------------------------------------------------------------------
// Inverses into S
// ---------------------------------------------------------------------------

// FractionalInverseOfUnit — the fractional inverse into S of a set holding 1 lies
// in S: a member of it, times 1, lies in S.
var FractionalInverseOfUnit = fractionalInverseOfUnitThm{family.Add(registry.ProofEntry{
	Name: "FractionalInverseOfUnit",
	Key:  "prop_27a01c76315468b7",
	Build: family.Theorem(Statement{
		Binders:    "∀L:field_on(A). ∀S T:set(A).",
		Hypotheses: []string{"L.one ∈ T"},
		Conclusion: "fractional_inverse(field_ring(L), S, T) ⊆ S",
	},
		func(a *Argument, L field.FieldFact[on.L], S, T *Expr[Set[A]], unit Fact) {
			pointwise := a.Have(
				"a member of the inverse lies in S",
				"∀x:A. x ∈ fractional_inverse(field_ring(L), S, T) ⇒ x ∈ S",
				Derive(func(b *Argument) {
					b.FixAs[A]("x")
					member := b.Simplified(b.Assume(), Fwd(FractionalInverseDef))
					parts := b.Conjuncts(
						b.Have(
							"x lies in L, and its multiples of T lie in S",
							"x ∈ L.carrier ∧ (∀m:A. m ∈ T ⇒ x * m ∈ S)",
							BySets(member)),
						"x lies in L",
						"its multiples of T lie in S")
					times := b.Have(
						"x times 1 is x",
						"x * L.one = x",
						ByArith(L, parts[0]))
					b.Show(
						"x is its multiple of 1",
						By(Normalized, times, unit, parts[1].At(b.TermAs[A]("L.one"))))
				}))
			a.Show(
				"so the inverse lies in S",
				BySets(pointwise))
		}),
})}

// FractionalInverseHoldsOne — one lies in the fractional inverse into a subring S of
// a set X inside S: one lies in L, and its product with a member of X is that member,
// which lies in S.
var FractionalInverseHoldsOne = fractionalInverseHoldsOneThm{family.Add(registry.ProofEntry{
	Name: "FractionalInverseHoldsOne",
	Key:  "prop_825e45698fda42e",
	Build: family.Theorem(Statement{
		Binders:    "∀L:field_on(A). ∀S X:set(A).",
		Hypotheses: []string{"subring(field_ring(L), S)", "X ⊆ S"},
		Conclusion: "L.one ∈ «wfInverse»(X)",
	},
		func(a *Argument, L field.FieldFact[on.L], S, X *Expr[Set[A]], subring, inside Fact) {
			ring := a.TermAs[RingOps[A]]("field_ring(L)")
			inField := a.Have(
				"S lies in L",
				"S ⊆ L.carrier",
				By(subring, comm_ring.SubringSubset.At(ring, S)))
			products := a.Have(
				"one fixes the members of X, which lie in S",
				"∀m:A. m ∈ X ⇒ L.one * m ∈ S",
				Derive(func(b *Argument) {
					b.FixAs[A]("m")
					member := b.Assume()
					memberships := b.Have(
						"m lies in S, inside L",
						"m ∈ S ∧ m ∈ L.carrier",
						BySets(inside, inField, member))
					fixed := b.Have(
						"one fixes m",
						"L.one * m = m",
						ByArith(L, memberships))
					b.Show(
						"so the product lies in S",
						By(Normalized, fixed, memberships))
				}))
			a.Do(Simp(Fwd(FractionalInverseDef)))
			a.Show(
				"one lies in L and carries X into S",
				By(products, comm_ring.OneIn.Read(field.RingOn.Read(L))))
		}),
})}
