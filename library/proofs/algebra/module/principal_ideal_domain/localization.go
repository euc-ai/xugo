// localization.go — modules over a subring S of a field and over its fraction
// field K: a finite subset of a K-span is cleared by one nonzero denominator of
// S, so finitely generated S-submodules with one K-span agree after saturation
// at a single denominator.

package principal_ideal_domain

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/linear_independence"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_element"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// ModuleSaturationMember — v lies in the saturation of U at s exactly when it
// is a vector that some power of s carries into U: the definition's
// set-builder read at v.
var ModuleSaturationMember = moduleSaturationMemberThm{family.Add(registry.ProofEntry{
	Name: "ModuleSaturationMember",
	Key:  "prop_849494488bdfd978",
	Build: family.Theorem(
		"∀R:ring_ops(A). ∀M:module_ops(A, B). ∀s:A. ∀U:set(B). ∀v:B. "+
			"    v ∈ module_saturation(R, M, s, U) ⇔ "+
			"    v ∈ M.carrier ∧ (∃n:num. monoid_pow(R.mul, R.one, s, n) • v ∈ U)",
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			s *Expr[A],
			U *Expr[Set[B]],
			v *Expr[B],
		) {
			a.Show(
				"the set-builder read at v",
				Unfold(ModuleSaturationDef),
				SetTacMembership())
		}),
})}

// ModuleSaturationHolds — a set of vectors lies in its own saturation at any s:
// the power at exponent zero is the ring's one, which fixes every vector.
var ModuleSaturationHolds = moduleSaturationHoldsThm{family.Add(registry.ProofEntry{
	Name: "ModuleSaturationHolds",
	Key:  "prop_736103d025c8ca02",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀s:A. ∀U:set(B).",
		Hypotheses: []string{
			"module_on(R, M)",
			"U ⊆ M.carrier",
		},
		Conclusion: "U ⊆ module_saturation(R, M, s, U)",
	}, func(
		a *Argument,
		R *Expr[RingOps[A]],
		M *Expr[ModuleOps[A, B]],
		overR module.ModuleFact[on.R, on.M],
		s *Expr[A],
		U *Expr[Set[B]],
		uInM Fact,
	) {
		a.Show(
			"a vector of U lies in the saturation at exponent zero",
			Simp(Fwd(set_basic.SubsetDef)),
			Derive(func(b *Argument) {
				v := b.FixAs[B]("v")
				inU := b.Assume()
				vm := b.MemberOf[on.M](v, b.Have(
					"v lies in M",
					"v ∈ M.carrier",
					BySets(inU, uInM)))
				exponent := b.Have(
					"s⁰ v = v lies in U",
					"∃n:num. monoid_pow(R.mul, R.one, s, n) • v ∈ U",
					Witness(b.TermAs[Nat]("0")),
					Simp(Fwd(comm_monoid.MonoidPowDef)),
					By(Normalized, inU, module.SmulOne.Read(overR).At(vm)))
				b.Show(
					"so v lies in the saturation",
					Simp(Fwd(ModuleSaturationMember)),
					By(vm, exponent))
			}))
	}),
})}

// ModuleSaturationMono — saturation at d is monotone along d·U ⊆ V: a vector
// that d^n carries into U is carried into V by d^(n+1).
var ModuleSaturationMono = moduleSaturationMonoThm{family.Add(registry.ProofEntry{
	Name: "ModuleSaturationMono",
	Key:  "prop_74f2f10066b4e3ae",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀d:A. ∀U V:set(B).",
		Hypotheses: []string{
			"module_on(R, M)",
			"d ∈ R.carrier",
			"image(M.smul(d), U) ⊆ V",
		},
		Conclusion: "module_saturation(R, M, d, U) ⊆ module_saturation(R, M, d, V)",
	}, func(
		a *Argument,
		R *Expr[RingOps[A]],
		M *Expr[ModuleOps[A, B]],
		overR module.ModuleFact[on.R, on.M],
		d *Member[A, on.R],
		U, V *Expr[Set[B]],
		inclusion Fact,
	) {
		ring := module.RingOn.Read(overR)
		a.Show(
			"a vector of the saturation of U lies in the saturation of V",
			Simp(Fwd(set_basic.SubsetDef)),
			Derive(func(b *Argument) {
				v := b.FixAs[B]("v")
				inSaturation := b.Assume()
				n, intoU := b.ObtainAs[Nat](
					"choose a power carrying v into U",
					"∃n:num. v ∈ M.carrier ∧ M.smul(monoid_pow(R.mul, R.one, d, n), v) ∈ U",
					BySets(inSaturation, ModuleSaturationDef.At(R, M, d, U)),
					Named("n"))
				next := b.Have(
					"one more power carries v into V",
					"∃m:num. v ∈ M.carrier ∧ M.smul(monoid_pow(R.mul, R.one, d, m), v) ∈ V",
					Derive(func(c *Argument) {
						c.Take(c.TermAs[Nat]("suc(n)"))
						c.Do(Simp(Fwd(comm_monoid.MonoidPowDef)))
						power := comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(ring)).At(d, n)
						c.Show(
							"d^(n+1) v = d (d^n v) ∈ d U ⊆ V",
							BySets(intoU, overR, inclusion, d, power, module.SmulMul.At(R, M, d, power, v)))
					}))
				b.Show(
					"this exponent witnesses membership in the saturation of V",
					BySets(next, ModuleSaturationDef.At(R, M, d, V)))
			}))
	}),
})}

// SaturationCommonExponent — one exponent serves a finite family: when each
// g(j) lies in the saturation of a submodule N at s, every power of s from one
// exponent on carries all the g(j) into N. A larger power is the smaller times
// a power of s, which N absorbs; by induction over E, the sum of the exponent
// of a new index and the exponent of the rest serves all.
var SaturationCommonExponent = saturationCommonExponentThm{family.Add(registry.ProofEntry{
	Name: "SaturationCommonExponent",
	Key:  "prop_cd009214d0424ca5",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀s:A. ∀N:set(B). ∀E:set(D). ∀g:(D → B).",
		Hypotheses: []string{
			"module_on(R, M)",
			"submodule(R, M, N)",
			"s ∈ R.carrier",
			"finite(E)",
			"∀j:D. j ∈ E ⇒ g(j) ∈ module_saturation(R, M, s, N)",
		},
		Conclusion: "∃n:num. ∀m:num. n ≤ m ⇒ ∀j:D. j ∈ E ⇒ monoid_pow(R.mul, R.one, s, m) • g(j) ∈ N",
	}, func(
		a *Argument,
		R *Expr[RingOps[A]],
		M *Expr[ModuleOps[A, B]],
		overR module.ModuleFact[on.R, on.M],
		s *Member[A, on.R],
		N *Expr[Set[B]],
		E *Expr[Set[D]],
		g *Arrow[D, B],
		submoduleN, finiteE, saturated Fact,
	) {
		monoid := comm_ring.MulMonoidOn.Read(module.RingOn.Read(overR))
		powerIn := comm_monoid.PowIn.Read(monoid)
		later := a.Have(
			"once a power of s carries x into N, every larger one does",
			Statement{
				Binders:    "∀x:B. ∀n m:num.",
				Hypotheses: []string{"x ∈ M.carrier", "monoid_pow(R.mul, R.one, s, n) • x ∈ N", "n ≤ m"},
				Conclusion: "monoid_pow(R.mul, R.one, s, m) • x ∈ N",
			},
			Derive(func(b *Argument) {
				x := b.FixAs[B]("x")
				n, m := b.FixAs[Nat]("n"), b.FixAs[Nat]("m")
				given := b.Conjuncts(
					b.Assume(),
					"x lies in M",
					"sⁿ • x lies in N",
					"n ≤ m")
				inM, intoN, atMost := given[0], given[1], given[2]
				d, gap := b.ObtainAs[Nat](
					"m exceeds n by some d",
					"∃d:num. m = n + d",
					By(atMost, nat_order.LessEqExists.At(m, n)),
					Named("d"))
				sn, sd := powerIn.At(s, n), powerIn.At(s, d)
				split := b.Have(
					"sⁿ⁺ᵈ = sᵈ sⁿ",
					"monoid_pow(R.mul, R.one, s, n + d) = "+
						"monoid_pow(R.mul, R.one, s, d) * monoid_pow(R.mul, R.one, s, n)",
					By(comm_monoid.PowAddOn.Read(monoid).At(s, n, d), comm_monoid.CommOn.Read(monoid).At(sn, sd)))
				b.Show(
					"so sᵐ • x = sᵈ • (sⁿ • x), which N absorbs, sᵈ being a scalar",
					By(
						gap,
						split,
						overR,
						submoduleN,
						sn,
						sd,
						inM,
						intoN,
						module.SmulMul.At(R, M, sd, sn, x),
						submodule.SubmoduleSmul.At(R, M, N, sd, b.TermAs[B]("monoid_pow(R.mul, R.one, s, n) • x"))))
			}))
		a.Show(
			"adjoin the indices of E one at a time",
			ByInduction(finite_set.FiniteInductFreshOn, finiteE, saturated,
				Case(
					"the empty set needs no power",
					Witness(a.TermAs[Nat]("0")),
					By(set_basic.NotInEmpty)),
				Case(
					"a new index x: the sum of its exponent and the exponent of the rest serves all",
					Derive(func(b *Argument) {
						x := b.FixAs[D]("x")
						t := b.FixAs[Set[D]]("t")
						step := b.Conjuncts(
							b.Assume(),
							"one exponent serves t",
							"x is new",
							"t is finite",
							"g(x) lies in the saturation of N",
							"so does g(j) for every j in t")
						servesT, saturatedX := step[0], step[3]
						_, rest := b.UnpackAs[Nat](servesT, "n")
						value := b.Conjuncts(
							b.Simplified(saturatedX, Fwd(ModuleSaturationMember)),
							"g(x) lies in M",
							"a power of s carries g(x) into N")
						xInM, clearing := value[0], value[1]
						q, clearsNew := b.UnpackAs[Nat](clearing, "q")
						b.Take(b.TermAs[Nat]("n + q"))
						m := b.FixAs[Nat]("m")
						beyond := b.Assume()
						summands := b.Have(
							"m is at least each exponent",
							"n ≤ m ∧ q ≤ m",
							ByArith(beyond))
						newIndex := b.Have(
							"sᵐ carries g(x) into N",
							"monoid_pow(R.mul, R.one, s, m) • g(x) ∈ N",
							By(later.At(g.Apply(x), q, m), xInM, clearsNew, summands))
						oldIndices := b.Have(
							"and g(j) for every j in t",
							"∀j:D. j ∈ t ⇒ monoid_pow(R.mul, R.one, s, m) • g(j) ∈ N",
							By(rest.At(m), summands))
						b.Show(
							"so sᵐ carries g over all of insert(x, t) into N",
							By(
								newIndex,
								oldIndices,
								set_basic.ForallInInsert.At(
									b.TermAs[Set[D]]("λj:D. monoid_pow(R.mul, R.one, s, m) • g(j) ∈ N"), x, t)))
					}))))
	}),
})}

// SaturationInSubfield — for a nonzero s of a subfield K and N ⊆ K, the
// saturation of N at s is one set in L and in K: s is invertible in K, so the
// inverse power brings a vector of L that a power of s carries into N back to
// itself, inside K.
var SaturationInSubfield = saturationInSubfieldThm{family.Add(registry.ProofEntry{
	Name: "SaturationInSubfield",
	Key:  "prop_c5c30521829677bb",
	Reading: "s ≠ L.zero is load-bearing: a positive power of zero kills every " +
		"vector, so at s = L.zero with L.zero ∈ N every vector of L saturates into " +
		"N, and the saturation in L is all of L while the one in K stops at K.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀K S N:set(A). ∀s:A.",
		Hypotheses: []string{
			"subfield(L, K)",
			"s ∈ K",
			"s ≠ L.zero",
			"N ⊆ K",
		},
		Conclusion: "module_saturation(«ScalarS», «Regular», s, N) = " +
			"module_saturation(«ScalarS», «VectorsK», s, N)",
		Abbrev: Abbrev{
			{Name: "ScalarS", Text: "restrict_ring(field_ring(L), S)"},
			{Name: "Regular", Text: "regular_module(field_ring(L))"},
			{Name: "VectorsK", Text: "restrict_module(«Regular», K)"},
		},
	}, func(
		a *Argument,
		L field.FieldFact[on.L],
		K, S, N *Expr[Set[A]],
		s *Expr[A],
		subK, sInK, nonzero, nInK Fact,
	) {
		fieldL := a.TermAs[FieldOps[A]]("L")
		ring := field.RingOn.Read(L)
		inverse := a.TermAs[A]("L.inv(s)")
		kInL := a.Have(
			"K lies in L",
			"K ⊆ L.carrier",
			By(field.SubfieldSubset.Read(subK)))
		ringK := a.Have(
			"K is a commutative ring under the field operations",
			"comm_ring_on(restrict_ring(field_ring(L), K))",
			By(subK, field.SubfieldCommRing.Read(L).At(K)))
		powersL, powersK := comm_ring.MulMonoidOn.Read(ring), comm_ring.MulMonoidOn.Read(ringK)
		sL := a.MemberOf[on.L](s, a.Have(
			"s lies in L",
			"s ∈ L.carrier",
			BySets(sInK, kInL)))
		inverseK := a.MemberOf[on.Any](inverse, a.Have(
			"the inverse of s lies in K",
			"L.inv(s) ∈ K",
			By(subK, sInK, field.SubfieldInv.At(fieldL, K, s))))
		inverseL := field.InvIn.Read(L).At(sL)
		undoes := a.Have(
			"the inverse undoes s",
			"L.inv(s) * s = L.one",
			By(sL, nonzero, field.MulLeftInverseOn.Read(L).At(sL)))
		a.Show(
			"the two saturations have the same members",
			Simp(Fwd(set_basic.Extension), Fwd(ModuleSaturationMember)),
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				b.Iff()
				b.Forward(
					"the inverse power brings x back from N, which lies in K",
					func(c *Argument, h Fact) {
						parts := c.Conjuncts(
							h,
							"x lies in L",
							"a power of s carries x into N")
						xL := c.MemberOf[on.L](x, parts[0])
						n, into := c.UnpackAs[Nat](parts[1], "n")
						powerL := comm_monoid.PowIn.Read(powersL).At(sL, n)
						backL := comm_monoid.PowIn.Read(powersL).At(inverseL, n)
						cancels := c.Have(
							"the inverse power undoes the power",
							"monoid_pow(L.mul, L.one, L.inv(s), n) * monoid_pow(L.mul, L.one, s, n) = L.one",
							By(sL, inverseL, undoes, comm_monoid.PowInverseOn.Read(powersL).AsFact().At(inverse, s, n)))
						recovered := c.Have(
							"so it brings the image of x back to x",
							"monoid_pow(L.mul, L.one, L.inv(s), n) * (monoid_pow(L.mul, L.one, s, n) * x) = x",
							ByArith(L, backL, powerL, xL, Scaled(x, cancels)))
						imageK := c.Have(
							"the image of x lies in K, as N does",
							"monoid_pow(L.mul, L.one, s, n) * x ∈ K",
							BySets(into, nInK))
						product := c.Have(
							"so that product lies in K",
							"monoid_pow(L.mul, L.one, L.inv(s), n) * (monoid_pow(L.mul, L.one, s, n) * x) ∈ K",
							By(
								subK,
								comm_monoid.PowIn.Read(powersK).At(inverseK, n),
								imageK,
								field.SubfieldMul.At(
									fieldL,
									K,
									c.TermAs[A]("monoid_pow(L.mul, L.one, L.inv(s), n)"),
									c.TermAs[A]("monoid_pow(L.mul, L.one, s, n) * x"))))
						c.Show(
							"so x lies in K, with the same power carrying it into N",
							By(Normalized, product, recovered, parts[1]))
					})
				b.Backward(
					"a vector of K is a vector of L",
					func(c *Argument, h Fact) {
						c.Show(
							"K lies in L",
							BySets(h, kInL))
					})
			}))
	}),
})}

// SpanHasDenominator — every vector in the fraction-field span of an
// S-submodule has a nonzero S-multiple in that submodule: clear the finitely
// many coefficients in a finite linear combination.
var SpanHasDenominator = spanHasDenominatorThm{family.Add(registry.ProofEntry{
	Name: "SpanHasDenominator",
	Key:  "prop_9af73d0ad727e2f2",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S:set(A). ∀M:module_ops(A, B). ∀V:set(B). ∀u:B.",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"fraction_field_carrier(field_ring(L), S)",
			"module_on(field_ring(L), M)",
			"submodule(restrict_ring(field_ring(L), S), M, V)",
			"u ∈ module_span(field_ring(L), M, V)",
		},
		Conclusion: "∃d:A. d ∈ S ∧ d ≠ L.zero ∧ M.smul(d, u) ∈ V",
	}, func(
		a *Argument,
		L field.FieldFact[on.L],
		S *Expr[Set[A]],
		M *Expr[ModuleOps[A, B]],
		V *Expr[Set[B]],
		u *Expr[B],
		h Fact,
	) {
		fieldRing := a.TermAs[RingOps[A]]("field_ring(L)")
		scalars := a.TermAs[RingOps[A]]("restrict_ring(field_ring(L), S)")
		vInM := a.Have(
			"V lies in the ambient module",
			"V ⊆ M.carrier",
			By(h, submodule.SubmoduleSubset))
		T, c, combination := a.Obtain2As[Set[B], Fun[B, A]](
			"write u as a combination with finite support in V",
			"∃T:set(B). ∃c:B → A. "+
				"    finite(T) ∧ "+
				"    T ⊆ V ∧ "+
				"    (∀x:B. x ∈ T ⇒ c(x) ∈ L.carrier) ∧ "+
				"    u = module_sum(M.add, M.zero, T, λx:B. M.smul(c(x), x))",
			By(h, vInM, linear_independence.SpanMembership.At(fieldRing, M, V, u)),
			Named("T", "c"))
		coefficients := a.Have(
			"the coefficient image is finite and lies in L",
			"finite(image(c, T)) ∧ image(c, T) ⊆ L.carrier",
			BySets(combination, finite_set.FiniteImage.At(c, T)))
		d, denominator := a.ObtainAs[A](
			"clear the finite coefficient image",
			"∃d:A. d ∈ S ∧ d ≠ L.zero ∧ image(L.mul(d), image(c, T)) ⊆ S",
			By(
				h,
				coefficients,
				integral_element.FiniteCommonDenominator.Read(L).At(S, a.TermAs[Set[A]]("image(c, T)"))),
			Named("d"))
		cleared := a.Have(
			"d lies in L and clears every coefficient",
			"d ∈ L.carrier ∧ (∀x:B. x ∈ T ⇒ L.mul(d, c(x)) ∈ S)",
			BySets(denominator, h, comm_ring.SubringSubset.At(fieldRing, S)))
		termsInV := a.Have(
			"each scaled summand lies in V",
			"∀x:B. x ∈ T ⇒ M.smul(d, M.smul(c(x), x)) ∈ V",
			Derive(func(b *Argument) {
				x := b.FixAs[B]("x")
				xIn := b.Assume()
				members := b.Have(
					"the coefficient is in S and the vector is in V",
					"L.mul(d, c(x)) ∈ S ∧ c(x) ∈ L.carrier ∧ x ∈ V ∧ x ∈ M.carrier",
					BySets(cleared, combination, xIn, vInM))
				b.Show(
					"associate the scalar actions and use closure of V",
					By(
						members,
						cleared,
						h,
						module.SmulMul.At(fieldRing, M, d, b.TermAs[A]("c(x)"), x),
						submodule.SubmoduleSmul.At(scalars, M, V, b.TermAs[A]("L.mul(d, c(x))"), x)))
			}))
		termsInM := a.Have(
			"the original summands lie in M",
			"∀x:B. x ∈ T ⇒ M.smul(c(x), x) ∈ M.carrier",
			BySets(combination, vInM, h, At(module.SmulIn, fieldRing, M)))
		scaledSum := a.Have(
			"bring d through the finite sum",
			"M.smul(d, u) = module_sum(M.add, M.zero, T, λx:B. M.smul(d, M.smul(c(x), x)))",
			By(
				combination,
				cleared,
				h,
				termsInM,
				module.ModuleSumSmul.At(fieldRing, M, T, d, a.TermAs[Fun[B, B]]("λx:B. M.smul(c(x), x)"))))
		a.Take(d)
		a.Show(
			"V contains the finite sum of the scaled summands",
			By(
				denominator,
				scaledSum,
				module.ModuleRestrictScalars,
				h,
				termsInV,
				combination,
				submodule.SubmoduleModuleSum.At(
					scalars, M, V, T, a.TermAs[Fun[B, B]]("λx:B. M.smul(d, M.smul(c(x), x))"))))
	}),
})}

// FiniteSpanHasDenominator — a finite subset of a fraction-field span has
// one nonzero denominator into the original submodule: multiply the
// denominators while adjoining its vectors one at a time.
var FiniteSpanHasDenominator = finiteSpanHasDenominatorThm{family.Add(registry.ProofEntry{
	Name: "FiniteSpanHasDenominator",
	Key:  "prop_6ea0dba26dcbeac5",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S:set(A). ∀M:module_ops(A, B). ∀V E:set(B).",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"fraction_field_carrier(field_ring(L), S)",
			"module_on(field_ring(L), M)",
			"submodule(restrict_ring(field_ring(L), S), M, V)",
			"finite(E)",
			"E ⊆ module_span(field_ring(L), M, V)",
		},
		Conclusion: "∃d:A. d ∈ S ∧ d ≠ L.zero ∧ image(M.smul(d), E) ⊆ V",
	}, func(
		a *Argument,
		L field.FieldFact[on.L],
		S *Expr[Set[A]],
		M *Expr[ModuleOps[A, B]],
		V, E *Expr[Set[B]],
		h Fact,
	) {
		fieldRing := a.TermAs[RingOps[A]]("field_ring(L)")
		scalars := a.TermAs[RingOps[A]]("restrict_ring(field_ring(L), S)")
		property := a.TermAs[Fun[Set[B], Bool]](
			"λT:set(B). " +
				"    T ⊆ module_span(field_ring(L), M, V) ⇒ ∃d:A. d ∈ S ∧ d ≠ L.zero ∧ image(M.smul(d), T) ⊆ V")
		a.Show(
			"multiply denominators across a finite set",
			ByInduction(finite_set.FiniteInduct.At(property, E), h,
				Case(
					"one clears the empty set",
					Derive(func(b *Argument) {
						b.Assume()
						b.Take(b.TermAs[A]("L.one"))
						b.Show(
							"one belongs to S and is nonzero",
							BySets(L, h, comm_ring.SubringOne, field.OneNotZeroOn))
					})),
				Case(
					"multiply the old denominator by a denominator of the new vector",
					Derive(func(b *Argument) {
						x := b.FixAs[B]("x")
						b.FixAs[Set[B]]("s")
						induction := b.Assume()
						inside := b.Assume()
						spanned := b.Have(
							"the old set and the new vector lie in the span",
							"x ∈ module_span(field_ring(L), M, V) ∧ s ⊆ module_span(field_ring(L), M, V)",
							BySets(inside))
						d, old := b.ObtainAs[A](
							"clear the old finite set",
							"∃d:A. d ∈ S ∧ d ≠ L.zero ∧ image(M.smul(d), s) ⊆ V",
							By(induction, spanned),
							Named("d"))
						e, point := b.ObtainAs[A](
							"clear the new vector",
							"∃e:A. e ∈ S ∧ e ≠ L.zero ∧ M.smul(e, x) ∈ V",
							By(h, spanned, SpanHasDenominator.Read(L).At(S, M, V, x)),
							Named("e"))
						inField := b.Have(
							"both denominators lie in L and V lies in M",
							"d ∈ L.carrier ∧ e ∈ L.carrier ∧ V ⊆ M.carrier",
							BySets(h, old, point, comm_ring.SubringSubset, submodule.SubmoduleSubset))
						inModule := b.Have(
							"the old set and the new vector lie in M",
							"x ∈ M.carrier ∧ s ⊆ M.carrier",
							BySets(
								spanned,
								h,
								inField,
								submodule.SpanSubmodule.At(fieldRing, M, V),
								submodule.SubmoduleSubset.At(fieldRing, M, b.TermAs[Set[B]]("module_span(field_ring(L), M, V)"))))
						product := b.Have(
							"the product is a nonzero scalar of S and its factors commute",
							"L.mul(d, e) ∈ S ∧ L.mul(d, e) ≠ L.zero ∧ L.mul(d, e) = L.mul(e, d)",
							By(
								L,
								h,
								old,
								point,
								inField,
								comm_ring.SubringMul.At(fieldRing, S, d, e),
								field.MulEqZeroOn.Read(L).AsFact().At(d, e),
								comm_monoid.CommOn.Read(comm_ring.MulMonoidOn.Read(field.RingOn.Read(L))).AsFact().At(d, e)))
						b.Take(b.TermAs[A]("L.mul(d, e)"))
						b.Show(
							"(d e) x = d (e x) ∈ V and (d e) y = e (d y) ∈ V for y ∈ s",
							BySets(
								product,
								old,
								point,
								inField,
								inModule,
								h,
								At(module.SmulMul, fieldRing, M, d, e),
								At(module.SmulMul, fieldRing, M, e, d),
								At(submodule.SubmoduleSmul, scalars, M, V, d),
								At(submodule.SubmoduleSmul, scalars, M, V, e)))
					}))))
	}),
})}

// FractionFieldScalars — a module over the fraction field K of S is a module
// over S, and K contains S: a fraction field's carrier holds the subring, so
// S is a subring of the restricted field, and the scalars restrict to it.
var FractionFieldScalars = fractionFieldScalarsThm{family.Add(registry.ProofEntry{
	Name: "FractionFieldScalars",
	Key:  "prop_d458a90bf8c7ee0c",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S K:set(A). ∀M:module_ops(A, B).",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"fraction_field_carrier(restrict_ring(field_ring(L), K), S)",
			"module_on(restrict_ring(field_ring(L), K), M)",
		},
		Conclusion: "S ⊆ K ∧ module_on(restrict_ring(field_ring(L), S), M)",
	}, func(
		a *Argument,
		L field.FieldFact[on.L],
		S, K *Expr[Set[A]],
		M *Expr[ModuleOps[A, B]],
		subringS, fractions, overK Fact,
	) {
		inK := a.Have(
			"as the fraction field of S, K contains S",
			"S ⊆ K",
			By(
				fractions,
				field.FractionFieldCarrierDef.At(a.TermAs[RingOps[A]]("restrict_ring(field_ring(L), K)"), S),
				module_record.RestrictRingDef.At(a.TermAs[RingOps[A]]("field_ring(L)"), K)))
		subringK := a.Have(
			"S is a subring of the restricted field K",
			"subring(field_ring(restrict_field(L, K)), S)",
			By(L, subringS, inK, comm_ring.SubringDef, field.RestrictFieldDef))
		overS := a.Have(
			"restrict the module scalars from K to S",
			"module_on(restrict_ring(field_ring(L), S), M)",
			By(
				overK,
				subringK,
				field.RestrictFieldRing,
				module.ModuleRestrictScalars,
				module_record.RestrictRingTwice))
		a.Show(
			"K contains S, and M is a module over S",
			By(inK, overS))
	}),
})}

// FiniteModuleInclusionAfterLocalization — a finitely generated S-submodule
// lying in the K-span of V has one nonzero S-multiple contained in V: clear
// its finite generators and extend the inclusion by linearity.
var FiniteModuleInclusionAfterLocalization = finiteModuleInclusionAfterLocalizationThm{family.Add(registry.ProofEntry{
	Name: "FiniteModuleInclusionAfterLocalization",
	Key:  "prop_6be320f56739c08c",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S K:set(A). ∀M:module_ops(A, B). ∀U V:set(B).",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"subfield(L, K)",
			"fraction_field_carrier(restrict_ring(field_ring(L), K), S)",
			"module_on(restrict_ring(field_ring(L), K), M)",
			"submodule(restrict_ring(field_ring(L), S), M, U)",
			"submodule(restrict_ring(field_ring(L), S), M, V)",
			"module_finitely_generated(restrict_ring(field_ring(L), S), restrict_module(M, U))",
			"U ⊆ module_span(restrict_ring(field_ring(L), K), M, V)",
		},
		Conclusion: "∃d:A. d ∈ S ∧ d ≠ L.zero ∧ image(M.smul(d), U) ⊆ V",
	}, func(
		a *Argument,
		L field.FieldFact[on.L],
		S, K *Expr[Set[A]],
		M *Expr[ModuleOps[A, B]],
		U, V *Expr[Set[B]],
		h Fact,
	) {
		fieldRing := a.TermAs[RingOps[A]]("field_ring(L)")
		scalars := a.TermAs[RingOps[A]]("restrict_ring(field_ring(L), S)")
		hypotheses := a.Conjuncts(
			h,
			"S is a subring of L",
			"K is a subfield of L",
			"K is the fraction field of S",
			"M is a module over K",
			"U is an S-submodule",
			"V is an S-submodule",
			"U is finitely generated",
			"U lies in the K-span of V")
		subringS, subfieldK, fractions, overK := hypotheses[0], hypotheses[1], hypotheses[2], hypotheses[3]
		subU, subV, generated, inclusion := hypotheses[4], hypotheses[5], hypotheses[6], hypotheses[7]
		restricted := a.Conjuncts(
			GroupPremises(
				hypotheses[0], hypotheses[2], hypotheses[3], FractionFieldScalars.Read(L).At(S, K, M)),
			"K contains S",
			"M is a module over S")
		inK, overS := restricted[0], restricted[1]
		generators := a.Unfolded(generated, FinitelyGeneratedDef)
		fieldK := a.Have(
			"K with the restricted operations is a field",
			"field_on(restrict_field(L, K))",
			By(L, subfieldK, field.SubfieldFieldOn))
		subringK := a.Have(
			"S is a subring of the restricted field K",
			"subring(field_ring(restrict_field(L, K)), S)",
			By(L, subringS, inK, comm_ring.SubringDef, field.RestrictFieldDef))
		E, generating := a.UnpackAs[Set[B]](generators, "E")
		ambientGenerators := a.Have(
			"E generates U in M and lies in the K-span of V",
			"module_span(restrict_ring(field_ring(L), S), M, E) = U ∧ "+
				"E ⊆ M.carrier ∧ "+
				"E ⊆ module_span(restrict_ring(field_ring(L), K), M, V)",
			BySets(
				generating,
				overS,
				subU,
				inclusion,
				linear_independence.SpanningRestrict.At(scalars, M, U, E),
				submodule.SubmoduleSubset.At(scalars, M, U)))
		d, denominator := a.ObtainAs[A](
			"clear the finite generators inside the field K",
			"∃d:A. d ∈ S ∧ d ≠ L.zero ∧ image(M.smul(d), E) ⊆ V",
			By(
				fieldK,
				subringK,
				fractions,
				overK,
				subV,
				generating,
				ambientGenerators,
				At(FiniteSpanHasDenominator, a.TermAs[FieldOps[A]]("restrict_field(L, K)"), S, M, V, E),
				field.RestrictFieldRing,
				field.RestrictFieldDef,
				module_record.RestrictRingTwice),
			Named("d"))
		scaling := a.Have(
			"multiplication by d is S-linear",
			"module_homomorphism(restrict_ring(field_ring(L), S), M, M, M.smul(d))",
			BySets(
				overK,
				subringS,
				inK,
				denominator,
				module_homomorphism.ScalingLinearOverSubring.At(fieldRing, K, S, M, d)))
		a.Take(d)
		a.Show(
			"linearity carries the span of E into V",
			By(
				denominator,
				ambientGenerators,
				scaling,
				subV,
				linear_independence.HomSpan.At(scalars, M, M, a.TermAs[Fun[B, B]]("M.smul(d)"), E),
				submodule.SpanLeast.At(scalars, M, a.TermAs[Set[B]]("image(M.smul(d), E)"), V)))
	}),
})}

// FiniteModulesSameLocalization — finitely generated submodules with the
// same fraction-field span have equal saturation at one nonzero scalar: the
// product d of the mutual denominators has d U ⊆ V and d V ⊆ U, and each
// saturation lies in the other, since d^(n+1) v = d (d^n v) ∈ d U ⊆ V.
var FiniteModulesSameLocalization = finiteModulesSameLocalizationThm{family.Add(registry.ProofEntry{
	Name: "FiniteModulesSameLocalization",
	Key:  "prop_81ab251a9ae02b69",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S K:set(A). ∀M:module_ops(A, B). ∀U V:set(B).",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"subfield(L, K)",
			"fraction_field_carrier(restrict_ring(field_ring(L), K), S)",
			"module_on(restrict_ring(field_ring(L), K), M)",
			"submodule(restrict_ring(field_ring(L), S), M, U)",
			"submodule(restrict_ring(field_ring(L), S), M, V)",
			"module_finitely_generated(restrict_ring(field_ring(L), S), restrict_module(M, U))",
			"module_finitely_generated(restrict_ring(field_ring(L), S), restrict_module(M, V))",
			"module_span(restrict_ring(field_ring(L), K), M, U) = " +
				"module_span(restrict_ring(field_ring(L), K), M, V)",
		},
		Conclusion: "∃d:A. " +
			"    d ∈ S ∧ " +
			"    d ≠ L.zero ∧ " +
			"    module_saturation(restrict_ring(field_ring(L), S), M, d, U) = " +
			"    module_saturation(restrict_ring(field_ring(L), S), M, d, V)",
	}, func(
		a *Argument,
		L field.FieldFact[on.L],
		S, K *Expr[Set[A]],
		M *Expr[ModuleOps[A, B]],
		U, V *Expr[Set[B]],
		h Fact,
	) {
		fieldRing := a.TermAs[RingOps[A]]("field_ring(L)")
		scalarsS := a.TermAs[RingOps[A]]("restrict_ring(field_ring(L), S)")
		scalarsK := a.TermAs[RingOps[A]]("restrict_ring(field_ring(L), K)")
		hypotheses := a.Conjuncts(
			h,
			"S is a subring of L",
			"K is a subfield of L",
			"K is the fraction field of S",
			"M is a module over K",
			"U is an S-submodule",
			"V is an S-submodule",
			"U is finitely generated",
			"V is finitely generated",
			"the K-spans agree")
		subringS, overK := hypotheses[0], hypotheses[3]
		subU, subV, spanEqual := hypotheses[4], hypotheses[5], hypotheses[8]
		restricted := a.Conjuncts(
			GroupPremises(
				hypotheses[0], hypotheses[2], hypotheses[3], FractionFieldScalars.Read(L).At(S, K, M)),
			"K contains S",
			"M is a module over S")
		inK, overS := restricted[0], restricted[1]
		spanned := a.Have(
			"each submodule lies in the K-span of the other",
			"U ⊆ module_span(restrict_ring(field_ring(L), K), M, V) ∧ "+
				"V ⊆ module_span(restrict_ring(field_ring(L), K), M, U)",
			By(
				Normalized,
				spanEqual,
				submodule.SubsetSpan.At(scalarsK, M, U),
				submodule.SubsetSpan.At(scalarsK, M, V)))
		p, fromU := a.ObtainAs[A](
			"clear the generators of U into V",
			"∃p:A. p ∈ S ∧ p ≠ L.zero ∧ image(M.smul(p), U) ⊆ V",
			By(h, spanned, FiniteModuleInclusionAfterLocalization.Read(L).At(S, K, M, U, V)),
			Named("p"))
		q, fromV := a.ObtainAs[A](
			"clear the generators of V into U",
			"∃q:A. q ∈ S ∧ q ≠ L.zero ∧ image(M.smul(q), V) ⊆ U",
			By(h, spanned, FiniteModuleInclusionAfterLocalization.Read(L).At(S, K, M, V, U)),
			Named("q"))
		d, dDef := a.LetAs[A]("d", "L.mul(p, q)")
		inField := a.Have(
			"both denominators are scalars of K and L",
			"p ∈ L.carrier ∧ q ∈ L.carrier ∧ p ∈ K ∧ q ∈ K",
			BySets(fromU, fromV, inK, subringS, comm_ring.SubringSubset.At(fieldRing, S)))
		product := a.Have(
			"d is nonzero in S and its factors can be reversed",
			"d ∈ S ∧ d ≠ L.zero ∧ d = L.mul(q, p)",
			By(
				Normalized,
				L,
				dDef,
				subringS,
				fromU,
				fromV,
				inField,
				comm_ring.SubringMul.At(fieldRing, S, p, q),
				field.MulEqZeroOn.Read(L).AsFact().At(p, q),
				comm_monoid.CommOn.Read(comm_ring.MulMonoidOn.Read(field.RingOn.Read(L))).AsFact().At(p, q)))
		transfers := a.Have(
			"d u = q (p u) ∈ V for u ∈ U and d v = p (q v) ∈ U for v ∈ V",
			"image(M.smul(d), U) ⊆ V ∧ image(M.smul(d), V) ⊆ U",
			BySets(
				dDef,
				product,
				fromU,
				fromV,
				inField,
				overK,
				subU,
				subV,
				At(module.SmulMul, scalarsK, M, p, q),
				At(module.SmulMul, scalarsK, M, q, p),
				submodule.SubmoduleSubset.At(scalarsS, M, U),
				submodule.SubmoduleSubset.At(scalarsS, M, V),
				At(submodule.SubmoduleSmul, scalarsS, M, U, p),
				At(submodule.SubmoduleSmul, scalarsS, M, V, q)))
		a.Take(d)
		a.Show(
			"each saturation lies in the other, one more power of d crossing between them",
			BySets(
				product,
				overS,
				transfers,
				ModuleSaturationMono.At(scalarsS, M, d, U, V),
				ModuleSaturationMono.At(scalarsS, M, d, V, U)))
	}),
})}
