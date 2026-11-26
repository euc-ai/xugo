// integral_closure.go — a principal ideal domain is integrally closed in its
// field of fractions; so the polynomials k[t] are integrally closed in k(t).

package principal_ideal_domain

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_extension"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/linear_independence"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/fractional_ideal"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_domain"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_element"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// PrincipalIdealDomainIntegrallyClosed — a principal ideal domain S inside a
// field is integrally closed in its field of fractions K. For x in K integral
// over S, finitely many powers of x span S[x], and one nonzero denominator in
// S clears them, so the conductor of S[x] into S — the members of L carrying
// S[x] into S — is a nonzero ideal of S, and S, a principal ideal domain,
// writes it g·S. Then g carries S[x], and with it x·S[x] ⊆ S[x], into S: g·x
// lies in the conductor g·S, and cancelling g ≠ 0 puts x in S.
var PrincipalIdealDomainIntegrallyClosed = principalIdealDomainIntegrallyClosedThm{family.Add(registry.ProofEntry{
	Name: "PrincipalIdealDomainIntegrallyClosed",
	Key:  "prop_7b03d467e5d5f42a",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S K:set(A).",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"principal_ideal_domain(restrict_ring(field_ring(L), S))",
			"subfield(L, K)",
			"fraction_field_carrier(restrict_ring(field_ring(L), K), S)",
		},
		Conclusion: "integrally_closed_in(restrict_ring(field_ring(L), S), K)",
		Abbrev: Abbrev{
			// S[w], its conductor into S, and the powers of w below the degree
			// of a polynomial f.
			{Name: "Sx", Text: "λw:A. polynomial_image(field_ring(L), S, w)"},
			{Name: "conductor", Text: "λw:A. fractional_inverse(field_ring(L), S, «Sx»(w))"},
			{Name: "powers", Text: "λw:A. λf:(num → A). " +
				"    {monoid_pow(L.mul, L.one, w, i) | i:num | i < polynomial_degree(f)}"},
		},
	}, func(
		a *Argument,
		L field.FieldFact[on.L],
		S, K *Expr[Set[A]],
		subring, pid, subfield, fractions Fact,
	) {
		ring := field.RingOn.Read(L)
		a.Show(
			"an element of K integral over S lies in S",
			Unfold(integral_element.IntegrallyClosedDef),
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				given := b.Conjuncts(
					b.Assume(),
					"x lies in K",
					"x is integral over S")
				xInK, integral := given[0], given[1]
				xIn := b.Have(
					"x lies in L, as K does",
					"x ∈ L.carrier",
					By(xInK, subfield, field.SubfieldSubset, set_basic.SubsetDef))
				xm := b.MemberOf[on.L](x, xIn)
				adjoined := b.Conjuncts(
					GroupPremises(subring, algebraic_element.PolynomialImageSubring.Read(L).At(S, xm)),
					"S[x] is a subring of L",
					"S lies in S[x]",
					"x lies in S[x]")
				ringSx, xInSx := adjoined[0], adjoined[2]
				Sx := b.TermAs[Set[A]]("«Sx»(x)")

				p, relation := b.UnpackAs[Fun[Nat, A]](b.Unfolded(integral, integral_element.IntegralOverDef), "p")
				powers := b.TermAs[Set[A]]("«powers»(x, p)")
				spanned := b.Have(
					"the powers of x below the degree of p span S[x]",
					"«Sx»(x) = "+
						"module_span(restrict_ring(field_ring(L), S), regular_module(field_ring(L)), «powers»(x, p))",
					By(subring, xIn, relation, integral_element.IntegralPowerSpan.Read(L).At(S, xm, p)))
				finitePowers := b.Have(
					"there are finitely many such powers",
					"finite(«powers»(x, p))",
					Derive(func(c *Argument) {
						segmentImage := c.Have(
							"they are the image of an initial segment of the exponents",
							"«powers»(x, p) = "+
								"image(λi:num. monoid_pow(L.mul, L.one, x, i), {i:num | i < polynomial_degree(p)})",
							BySets())
						c.Show(
							"a finite image is finite",
							segmentImage.Rw(),
							By(num_segment.FiniteBelowStrict, finite_set.FiniteImage))
					}))

				// K, a field under the operations of L, is the field of
				// fractions of S, and it holds the powers of x.
				fieldK := b.Have(
					"K is a field under the operations of L",
					"field_on(restrict_field(L, K))",
					By(subfield, field.SubfieldFieldOn.Read(L).At(K)))
				SInK := b.Have(
					"S lies in K",
					"S ⊆ K",
					By(fractions, field.FractionFieldCarrierDef))
				subringOfK := b.Have(
					"S is a subring of the field K",
					"subring(field_ring(restrict_field(L, K)), S)",
					Simp(Rev(field.RestrictFieldRing)),
					By(subring, SInK, comm_ring.SubringRestrict.At(b.TermAs[RingOps[A]]("field_ring(L)"), S, K)))
				fractionsOfK := b.Have(
					"K is the field of fractions of S",
					"fraction_field_carrier(field_ring(restrict_field(L, K)), S)",
					Simp(Rev(field.RestrictFieldRing)),
					By(fractions))
				powersInK := b.Have(
					"the powers of x lie in K",
					"«powers»(x, p) ⊆ K",
					BySets(comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(field.RingOn.Read(fieldK))), xInK))

				d, clearsPowers := b.ObtainAs[A](
					"the finitely many powers share a nonzero denominator d in S",
					"∃d:A. d ∈ S ∧ d ≠ L.zero ∧ image(L.mul(d), «powers»(x, p)) ⊆ S",
					By(
						fieldK,
						subringOfK,
						fractionsOfK,
						finitePowers,
						powersInK,
						integral_element.FiniteCommonDenominator.At(
							b.TermAs[FieldOps[A]]("restrict_field(L, K)"), S, powers)),
					Named("d"))
				dm := b.MemberOf[on.L](d, b.Have(
					"d lies in L",
					"d ∈ L.carrier",
					BySets(clearsPowers, comm_ring.SubringSubset.Read(subring))))
				scale := b.Have(
					"multiplication by d is S-linear",
					"module_homomorphism(restrict_ring(field_ring(L), S), "+
						"    regular_module(field_ring(L)), "+
						"    regular_module(field_ring(L)), "+
						"    L.mul(d))",
					By(subring, field_extension.ScaleLinear.Read(L).At(S, dm)))
				cleared := b.Have(
					"so it carries their span S[x] into the submodule S",
					"image(L.mul(d), «Sx»(x)) ⊆ S",
					spanned.Rw(),
					By(
						scale,
						clearsPowers,
						powersInK,
						subfield,
						subring,
						fractional_ideal.SubringSubmodule.Read(L).At(S),
						field.SubfieldSubset,
						set_order.SubsetTrans,
						linear_independence.HomSpanInSubmodule))

				conductor := b.TermAs[Set[A]]("«conductor»(x)")
				ideal := b.Have(
					"the conductor is an S-submodule of L, inside S since S[x] holds one: an ideal of S",
					"ring_ideal(restrict_ring(field_ring(L), S), «conductor»(x))",
					By(
						subring,
						ringSx,
						comm_ring.SubringSubset,
						comm_ring.SubringOne.Read(ringSx),
						fractional_ideal.FractionalInverseOfUnit.Read(L).At(S, Sx),
						fractional_ideal.FractionalInverseSubmodule.Read(L).At(S, Sx),
						fractional_ideal.IntegralIdealFractional.Read(L).At(S, conductor)))
				g, generated := b.ObtainAs[A](
					"S being a principal ideal domain, the conductor is g·S for some g in S",
					"∃g:A. g ∈ S ∧ «conductor»(x) = image(L.mul(g), S)",
					By(pid, ideal, PrincipalIdealDomainDef),
					Named("g"))
				dInConductor := b.Have(
					"d lies in the conductor",
					"d ∈ «conductor»(x)",
					Simp(Fwd(fractional_ideal.FractionalInverseDef)),
					BySets(clearsPowers, cleared, subring, comm_ring.SubringSubset))
				gNonzero := b.Have(
					"g is not zero, since the conductor g·S holds d ≠ 0",
					"g ≠ L.zero",
					BySets(
						dInConductor,
						generated,
						clearsPowers,
						subring,
						comm_ring.SubringSubset,
						comm_ring.MulLeftZeroOn.Read(ring)))
				gInConductor := b.Have(
					"g = g·1 lies in the conductor g·S",
					"g ∈ «conductor»(x)",
					BySets(
						generated,
						subring,
						comm_ring.SubringOne,
						comm_ring.SubringSubset,
						comm_monoid.RightIdentityOn.Read(comm_ring.MulMonoidOn.Read(ring))))
				gxInConductor := b.Have(
					"g·x lies in the conductor: (g·x)·m = g·(x·m), and x·m stays in S[x]",
					"g * x ∈ «conductor»(x)",
					Simp(Fwd(fractional_ideal.FractionalInverseDef)),
					BySets(
						b.Unfolded(gInConductor, fractional_ideal.FractionalInverseDef),
						xIn,
						xInSx,
						ringSx,
						comm_ring.SubringMul,
						comm_ring.SubringSubset,
						comm_ring.MulIn.Read(ring),
						comm_monoid.AssocOn.Read(comm_ring.MulMonoidOn.Read(ring))))
				r, quotient := b.ObtainAs[A](
					"so g·x = g·r for some r in S",
					"∃r:A. r ∈ S ∧ g * x = g * r",
					BySets(gxInConductor, generated),
					Named("r"))
				members := b.Conjuncts(
					b.Have(
						"g and r lie in L",
						"g ∈ L.carrier ∧ r ∈ L.carrier",
						BySets(generated, quotient, comm_ring.SubringSubset.Read(subring))),
					"g lies in L",
					"r lies in L")
				gm := b.MemberOf[on.L](g, members[0])
				rm := b.MemberOf[on.L](r, members[1])
				b.Show(
					"cancelling g ≠ 0 leaves x = r, a member of S",
					By(
						quotient,
						gNonzero,
						integral_domain.MulCancelLeft.Read(integral_domain.FieldIntegralDomain.Read(L)).At(gm, xm, rm)))
			}))
	}),
})}

// PolynomialRingIntegrallyClosed — the polynomials k[t] are integrally closed
// in the field k(t): k[t] is a principal ideal domain whose field of
// fractions is k(t).
var PolynomialRingIntegrallyClosed = polynomialRingIntegrallyClosedThm{family.Add(registry.ProofEntry{
	Name: "PolynomialRingIntegrallyClosed",
	Reading: "t need not be transcendental: k[t] is a principal ideal domain whose " +
		"field of fractions is k(t) either way, and for an algebraic t, k[t] = k(t).",
	Key: "prop_b70ef6d9e845479a",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀t:A.",
		Hypotheses: []string{
			"subfield(L, k)",
			"t ∈ L.carrier",
		},
		Conclusion: "integrally_closed_in( " +
			"    restrict_ring(field_ring(L), polynomial_image(field_ring(L), k, t)), field_adjoin(L, k, {t}))",
	}, func(a *Argument, L field.FieldFact[on.L], k *Expr[Set[A]], t *Expr[A], kSubfield, tIn Fact) {
		tm := a.MemberOf[on.L](t, tIn)
		a.Show(
			"k[t] is a principal ideal domain inside L whose field of fractions is the subfield k(t)",
			By(
				kSubfield,
				tIn,
				algebraic_element.PolynomialImageRing.Read(L).At(k, tm),
				PolynomialImagePrincipalIdealDomain.Read(L).At(k, tm),
				algebraic_element.AdjoinElementSubfield.Read(L).At(k, tm),
				integral_element.RationalFunctionsFractionField.Read(L).At(k, tm),
				PrincipalIdealDomainIntegrallyClosed.Read(L).At(
					a.TermAs[Set[A]]("polynomial_image(field_ring(L), k, t)"),
					a.TermAs[Set[A]]("field_adjoin(L, k, {t})"))))
	}),
})}
