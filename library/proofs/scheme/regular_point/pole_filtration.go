// pole_filtration.go — the functions with poles only at a regular rational
// point P, of order at most n. L(nP) is the meet of the charts' signed powers
// of P's components; the local ring at P holds the powers of its maximal
// ideal, which the order at P reads. Each step of the filtration adds at most
// one dimension, the order at P cuts L(nP) out of L(mP), and such a function
// is regular at every other regular point.

package regular_point

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/fractional_ideal"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/quotient_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_away"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_ideal"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/signed_ideal_power"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/subring_localization"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_embed"
	"github.com/euc-ai/xugo/library/proofs/scheme/algebraic_curve"
	"github.com/euc-ai/xugo/library/proofs/scheme/biaffine_rational_point"
	"github.com/euc-ai/xugo/library/proofs/scheme/invertible_lattice_pair"
	"github.com/euc-ai/xugo/library/proofs/scheme/lattice_pair"
	"github.com/euc-ai/xugo/library/proofs/scheme/lattice_pair_twist"
	"github.com/euc-ai/xugo/library/registry"
)

// PoleSpaceCharts — L(nP) is the meet of the two charts' (−n)-th signed
// powers of P's ideals: chart by chart, the n-th power of the inverse pair is
// the n-th power of the inverse ideal, and a negative signed power is a
// natural power of the inverse.
var PoleSpaceCharts = poleSpaceChartsThm{family.Add(registry.ProofEntry{
	Name: "PoleSpaceCharts",
	Key:  "prop_73321e36a46410cb",
	Build: family.Theorem(
		"∀R:ring_ops(A). ∀A₀ A₁:set(A). ∀P:prod(set(A), set(A)). ∀n:num. "+
			"    single_point_pole_space(R, A₀, A₁, P, n).carrier = "+
			"    signed_ideal_power(R, A₀, fst(P), -&n) ∩ signed_ideal_power(R, A₁, snd(P), -&n)",
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			A0, A1 *Expr[Set[A]],
			P *Expr[Prod[Set[A], Set[A]]],
			n *Expr[Nat],
		) {
			negative := a.Have(
				"a negative signed power is a natural power of the inverse",
				"∀S I:set(A). ∀m:num. "+
					"    signed_ideal_power(R, S, I, -&m) = "+
					"    monoid_pow(λX:set(A). λY:set(A). fractional_mul(R, S, X, Y), "+
					"        S, "+
					"        fractional_inverse(R, S, I), "+
					"        m)",
				Derive(func(b *Argument) {
					S, I, m := b.FixAs[Set[A]]("S"), b.FixAs[Set[A]]("I"), b.FixAs[Nat]("m")
					b.Cases(b.TermAs[Bool]("m = 0"))
					b.When(
						"at zero both sides are S",
						func(c *Argument, zero Fact) {
							negatedZero := c.Have(
								"−0 is 0",
								"-0 = int_of_num(0)",
								ByArith())
							c.Show(
								"the power at zero is the unit S on either branch",
								Simp(
									Fwd(zero),
									Fwd(signed_ideal_power.SignedIdealPowerDef),
									Fwd(negatedZero),
									Fwd(int_embed.OfNumRetract),
									Fwd(comm_monoid.MonoidPowDef)),
								Basic())
						})
					b.Otherwise(
						"off zero −m is negative, and the power is the m-th power of the inverse",
						func(c *Argument, nonzero Fact) {
							sign := c.Conjuncts(
								c.Have(
									"−m is negative and its negative is m",
									"¬(0 ≤ -int_of_num(m)) ∧ - -m = int_of_num(m)",
									ByArith(nonzero, int_embed.OfNumLe.At(m, c.TermAs[Nat]("0")))),
								"−m is negative",
								"its negative is m")
							c.Show(
								"the second branch at m",
								By(
									Normalized,
									sign[0],
									sign[1],
									signed_ideal_power.SignedIdealPowerDef.At(R, S, I, c.TermAs[Int]("-&m")),
									int_embed.OfNumRetract.At(m)))
						})
				}))
			firstProduct := a.Have(
				"chart 0 of a product of pairs is the product of the charts 0",
				"∀u v:prod(set(A), set(A)). "+
					"    fst(lattice_pair_mul(R, A₀, A₁, u, v)) = fractional_mul(R, A₀, fst(u), fst(v))",
				Simp(Fwd(invertible_lattice_pair.LatticePairMulDef), Fwd(pairs.Fst)),
				Basic())
			secondProduct := a.Have(
				"chart 1 of a product of pairs is the product of the charts 1",
				"∀u v:prod(set(A), set(A)). "+
					"    snd(lattice_pair_mul(R, A₀, A₁, u, v)) = fractional_mul(R, A₁, snd(u), snd(v))",
				Simp(Fwd(invertible_lattice_pair.LatticePairMulDef), Fwd(pairs.Snd)),
				Basic())
			inverse := invertible_lattice_pair.LatticePairInverseDef.At(R, A0, A1, P)
			first := a.Have(
				"chart 0 of the m-th power of the inverse pair is the m-th power of the inverse of fst(P)",
				"∀m:num. "+
					"    fst(monoid_pow(λX:prod(set(A), set(A)). λY:prod(set(A), set(A)). "+
					"                lattice_pair_mul(R, A₀, A₁, X, Y), "+
					"            (A₀, A₁), "+
					"            lattice_pair_inverse(R, A₀, A₁, P), "+
					"            m)) = "+
					"    monoid_pow(λX:set(A). λY:set(A). fractional_mul(R, A₀, X, Y), "+
					"        A₀, "+
					"        fractional_inverse(R, A₀, fst(P)), "+
					"        m)",
				Derive(func(b *Argument) {
					b.Induct("m")
					b.Base(
						"both zeroth powers are A₀",
						Simp(Fwd(comm_monoid.MonoidPowDef), Fwd(pairs.Fst)),
						Refl())
					b.Step(
						"one more factor of the inverse on each side",
						func(c *Argument, ih Fact) {
							c.Show(
								"chart 0 of the inverse pair is the inverse of fst(P)",
								Simp(
									Fwd(comm_monoid.MonoidPowDef),
									Fwd(firstProduct),
									Fwd(ih),
									Fwd(invertible_lattice_pair.LatticePairInverseDef),
									Fwd(pairs.Fst)),
								By(ih, inverse))
						})
				}))
			second := a.Have(
				"chart 1 of the m-th power of the inverse pair is the m-th power of the inverse of snd(P)",
				"∀m:num. "+
					"    snd(monoid_pow(λX:prod(set(A), set(A)). λY:prod(set(A), set(A)). "+
					"                lattice_pair_mul(R, A₀, A₁, X, Y), "+
					"            (A₀, A₁), "+
					"            lattice_pair_inverse(R, A₀, A₁, P), "+
					"            m)) = "+
					"    monoid_pow(λX:set(A). λY:set(A). fractional_mul(R, A₁, X, Y), "+
					"        A₁, "+
					"        fractional_inverse(R, A₁, snd(P)), "+
					"        m)",
				Derive(func(b *Argument) {
					b.Induct("m")
					b.Base(
						"both zeroth powers are A₁",
						Simp(Fwd(comm_monoid.MonoidPowDef), Fwd(pairs.Snd)),
						Basic())
					b.Step(
						"one more factor of the inverse on each side",
						func(c *Argument, ih Fact) {
							c.Show(
								"chart 1 of the inverse pair is the inverse of snd(P)",
								Simp(Fwd(comm_monoid.MonoidPowDef), Fwd(secondProduct)),
								By(ih, inverse, pairs.Snd))
						})
				}))
			a.Show(
				"the sections of the n-th power are its two charts met",
				Simp(
					Fwd(SinglePointPoleSpaceDef),
					Fwd(lattice_pair.LatticePairH0Def),
					Fwd(first),
					Fwd(second),
					Fwd(negative)),
				Basic())
		}),
})}

// RegularPointLocalRing — at a regular rational point P of a curve: P's
// chart is a subring in which P's ideal is maximal and invertible, the local
// ring at P is a subring holding the chart whose maximal ideal is invertible,
// each signed power of P's ideal lies in the same power of the maximal ideal
// of the local ring, and those powers are fractional ideals of the local ring. P's ideal is rational and
// invertible in its chart (RegularPointChart), so maximal, its residues lying
// in k. P's ideal generates the maximal ideal of the local ring, its
// extension there, which keeps it invertible (subring_localization.LocalExtensionLaws), and the
// powers extend to the local ring (subring_localization.ExtensionOfSignedPowers).
var RegularPointLocalRing = regularPointLocalRingThm{family.Add(registry.ProofEntry{
	Name: "RegularPointLocalRing",
	Key:  "prop_3d5d1d119d676023",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀P:prod(set(A), set(A)).",
		Hypotheses: []string{
			"curve_over_line(L, k, t, A₀, A₁, A₀₁)",
			"biaffine_regular_point(field_ring(L), k, A₀, A₁, A₀₁, P)",
		},
		Conclusion: "subring(field_ring(L), point_chart(A₀, A₁, P)) ∧ " +
			"maximal_ideal(restrict_ring(field_ring(L), point_chart(A₀, A₁, P)), point_ideal(A₀, P)) ∧ " +
			"invertible_fractional(field_ring(L), point_chart(A₀, A₁, P), point_ideal(A₀, P)) ∧ " +
			"subring(field_ring(L), «local») ∧ " +
			"point_chart(A₀, A₁, P) ⊆ «local» ∧ " +
			"invertible_fractional(field_ring(L), «local», «maximal») ∧ " +
			"(∀j:int. " +
			"    signed_ideal_power(field_ring(L), point_chart(A₀, A₁, P), point_ideal(A₀, P), j) ⊆ " +
			"    «power»(j)) ∧ " +
			"(∀j:int. " +
			"    submodule(restrict_ring(field_ring(L), «local»), regular_module(field_ring(L)), «power»(j)))",
		Abbrev: Abbrev{
			{Name: "local", Text: "point_local_ring(field_ring(L), A₀, A₁, P)"},
			{Name: "maximal", Text: "ideal_span(restrict_ring(field_ring(L), «local»), point_ideal(A₀, P))"},
			{Name: "power", Text: "λn:int. signed_ideal_power(field_ring(L), «local», «maximal», n)"},
		},
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			P *Expr[Prod[Set[A], Set[A]]],
			curve, regular Fact,
		) {
			fieldOps := a.TermAs[RingOps[A]]("field_ring(L)")
			chart, ideal := a.TermAs[Set[A]]("point_chart(A₀, A₁, P)"), a.TermAs[Set[A]]("point_ideal(A₀, P)")
			local := a.TermAs[Set[A]]("«local»")
			chartParts := a.Conjuncts(
				GroupPremises(curve, regular, RegularPointChart.Read(L).At(k, A0, A1, A01, t, P)),
				"P's chart is a subring of L",
				"k is a subfield of L",
				"k lies in P's chart",
				"L is the chart's field of fractions",
				"P's ideal is the ideal of a k-rational point of the chart",
				"and invertible there",
				"each nonzero principal ideal of the chart has finite colength")
			subring, invertible := chartParts[0], chartParts[5]
			inverse := a.TermAs[Fun[A, A]]("L.inv")
			maximal := a.Have(
				"P's ideal is maximal in the chart, its residues lying in the subfield k",
				"maximal_ideal(restrict_ring(field_ring(L), point_chart(A₀, A₁, P)), point_ideal(A₀, P))",
				By(
					field.RingOn.Read(L),
					chartParts[1],
					field.SubfieldRingSubfield.Read(L).At(k, chart),
					field.RingSubfieldRestrict.At(fieldOps, chart, inverse, k),
					subring,
					chartParts[2],
					chartParts[4],
					quotient_ring.FieldResiduesMaximal.At(fieldOps, k, inverse, chart, ideal)))
			chartRing := a.Have(
				"P's chart is a ring under L's operations",
				"comm_ring_on(restrict_ring(field_ring(L), point_chart(A₀, A₁, P)))",
				By(subring, comm_ring.SubringRingOn.Read(field.RingOn.Read(L)).At(chart)))
			prime := a.Have(
				"so P's ideal is prime there",
				"prime_ideal(restrict_ring(field_ring(L), point_chart(A₀, A₁, P)), point_ideal(A₀, P))",
				By(maximal, ring_ideal.MaximalIsPrime.Read(chartRing).At(ideal)))
			fractions := a.Have(
				"the local ring is the localization of the chart at P's ideal",
				"«local» = subring_localization(field_ring(L), point_chart(A₀, A₁, P), point_ideal(A₀, P))",
				By(PointLocalRingDef.At(fieldOps, A0, A1, P)))
			localFacts := a.Have(
				"the local ring is a subring holding the chart, and P's ideal generates its maximal ideal",
				"subring(field_ring(L), «local») ∧ "+
					"point_chart(A₀, A₁, P) ⊆ «local» ∧ "+
					"module_span(restrict_ring(field_ring(L), «local»), "+
					"    regular_module(field_ring(L)), "+
					"    point_ideal(A₀, P)) = "+
					"«maximal»",
				fractions.Rw(),
				By(
					prime,
					subring,
					subring_localization.LocalRingSubring.Read(L).At(chart, ideal),
					subring_localization.LocalExtensionLaws.Read(L).At(chart, ideal)))
			localParts := a.Conjuncts(
				localFacts,
				"the local ring is a subring",
				"it holds the chart",
				"P's ideal generates its maximal ideal")
			extension := a.Conjuncts(
				GroupPremises(subring, prime, subring_localization.LocalExtensionLaws.Read(L).At(chart, ideal)),
				"the localization is a subring",
				"the chart extends to it",
				"extension is multiplicative on invertible ideals",
				"and keeps invertible ideals invertible with their inverses",
				"P's ideal extends to the ideal it generates",
				"which lies in the localization",
				"and misses one",
				"an ideal holding a function off P's ideal extends to the whole local ring")
			invertibleMaximal := a.Have(
				"the maximal ideal is invertible, as the extension of P's invertible ideal",
				"invertible_fractional(field_ring(L), «local», «maximal»)",
				fractions.Rw(),
				By(invertible, extension[3].At(ideal), extension[4]))
			inclusion := a.Have(
				"each signed power of P's ideal lies in the same power of the maximal ideal",
				"∀j:int. "+
					"    signed_ideal_power(field_ring(L), point_chart(A₀, A₁, P), point_ideal(A₀, P), j) ⊆ «power»(j)",
				Derive(func(b *Argument) {
					j := b.FixAs[Int]("j")
					b.Show(
						"its extension to the local ring contains it",
						By(
							subring,
							invertible,
							localFacts,
							subring_localization.ExtensionOfSignedPowers.Read(L).At(chart, local, ideal, j),
							submodule.SubsetSpan.At(
								b.TermAs[RingOps[A]]("restrict_ring(field_ring(L), «local»)"),
								b.TermAs[module_record.ModuleOps[A, A]]("regular_module(field_ring(L))"),
								b.TermAs[Set[A]](
									"signed_ideal_power(field_ring(L), point_chart(A₀, A₁, P), point_ideal(A₀, P), j)"))))
				}))
			fractional := a.Have(
				"the powers of the maximal ideal are fractional ideals of the local ring",
				"∀j:int. "+
					"    submodule(restrict_ring(field_ring(L), «local»), regular_module(field_ring(L)), «power»(j))",
				By(
					localParts[0],
					invertibleMaximal,
					signed_ideal_power.SignedIdealPowerLaws.Read(L).At(local, a.TermAs[Set[A]]("«maximal»"))))
			a.Show(
				"the chart facts, the local ring and the powers",
				By(
					subring,
					maximal,
					invertible,
					localParts[0],
					localParts[1],
					invertibleMaximal,
					inclusion,
					fractional))
		}),
})}

// OrderReadsPowers — at a regular rational ideal the order of a nonzero
// function reads off its powers: f lies in the j-th power of the maximal ideal
// of the local ring exactly when j is at most the order of f. The function
// generates the power its order names (OrderAtRegularPoint, the order being
// the choice of that exponent), a power holds f exactly when it holds that
// principal ideal (signed_ideal_power.SignedPowerHoldsPrincipal), and the powers
// decrease strictly.
var OrderReadsPowers = orderReadsPowersThm{family.Add(registry.ProofEntry{
	Name: "OrderReadsPowers",
	Key:  "prop_5d97ada8dac5366f",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀P:prod(set(A), set(A)). ∀f:A. ∀j:int.",
		Hypotheses: []string{
			"curve_over_line(L, k, t, A₀, A₁, A₀₁)",
			"biaffine_regular_point(field_ring(L), k, A₀, A₁, A₀₁, P)",
			"f ∈ L.carrier",
			"f ≠ L.zero",
		},
		Conclusion: "f ∈ «power»(j) ⇔ j ≤ regular_point_order(field_ring(L), A₀, A₁, P, f)",
		Abbrev: Abbrev{
			{Name: "local", Text: "point_local_ring(field_ring(L), A₀, A₁, P)"},
			{Name: "maximal", Text: "ideal_span(restrict_ring(field_ring(L), «local»), point_ideal(A₀, P))"},
			{Name: "power", Text: "λn:int. signed_ideal_power(field_ring(L), «local», «maximal», n)"},
		},
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			P *Expr[Prod[Set[A], Set[A]]],
			f *Expr[A],
			j *Expr[Int],
			curve, point, fInL, nonzero Fact,
		) {
			local := a.TermAs[Set[A]]("«local»")
			order := a.Conjuncts(
				GroupPremises(curve, point, OrderAtRegularPoint.Read(L).At(k, A0, A1, A01, t, P)),
				"the order is a valuation",
				"every nonzero function generates exactly one power",
				"the powers decrease strictly")
			generates := a.Have(
				"f generates some power of the maximal ideal",
				"∃n:int. image(L.mul(f), «local») = «power»(n)",
				By(fInL, nonzero, order[1]))
			named := a.Have(
				"f generates the power its order names",
				"image(L.mul(f), «local») = «power»(regular_point_order(field_ring(L), A₀, A₁, P, f))",
				By(generates, RegularPointOrderDef.At(a.TermAs[RingOps[A]]("field_ring(L)"), A0, A1, P, f)))
			localRing := a.Conjuncts(
				GroupPremises(curve, point, RegularPointLocalRing.Read(L).At(k, A0, A1, A01, t, P)),
				"P's chart is a subring",
				"P's ideal is maximal there",
				"and invertible",
				"the local ring is a subring",
				"it holds the chart",
				"its maximal ideal is invertible",
				"each signed power of P's ideal lies in the same power of the maximal ideal",
				"those powers are fractional ideals of the local ring")
			reads := GroupPremises(
				localRing[3],
				localRing[5],
				signed_ideal_power.SignedPowerHoldsPrincipal.Read(L).At(
					local, a.TermAs[Set[A]]("«maximal»"), a.MemberOf[on.L](f, fInL), j))
			a.Show(
				"the power f generates lies in the j-th exactly when j is at most its order",
				By(reads, named, order[2]))
		}),
})}

// PoleFiltrationAtRegularPoint — the spaces L(nP) of functions with a pole of
// order at most n at a regular rational point P and none elsewhere grow by at
// most one dimension at each step, are cut out of each other by the order at P,
// and hold only functions regular at every other regular point. L(nP) is H⁰ of
// the n-th power of P⁻¹, and the next power is its twist by P
// (lattice_pair_twist.TwistH0Step). A member of L(nP) lies in the (−n)-th power
// of P's ideal in P's chart, hence in the (−n)-th power of the maximal ideal of
// the local ring, which the order reads (OrderReadsPowers).
var PoleFiltrationAtRegularPoint = poleFiltrationAtRegularPointThm{family.Add(registry.ProofEntry{
	Name: "PoleFiltrationAtRegularPoint",
	Reading: "A₀ ∩ A₁ = k makes L(0P) the constants, so every L(nP) is finite-dimensional " +
		"by the one-step bound and module_dim reads a dimension. The span clause of " +
		"biaffine_rational_point turns Q ≠ P into different ideals in a common chart.",
	Key: "prop_641fa4ae6b118d61",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀P:prod(set(A), set(A)).",
		Hypotheses: []string{
			"curve_over_line(L, k, t, A₀, A₁, A₀₁)",
			"biaffine_regular_point(field_ring(L), k, A₀, A₁, A₀₁, P)",
		},
		Conclusion: "(∀n:num. " +
			"    module_dim(restrict_ring(field_ring(L), k), «poles»(n + 1)) ≤ " +
			"    module_dim(restrict_ring(field_ring(L), k), «poles»(n)) + 1) ∧ " +
			"(∀f:A. ∀n:num. f ∈ «poles»(n).carrier ∧ f ≠ L.zero ⇒ -n ≤ «order»(f)) ∧ " +
			"(∀f:A. ∀m n:num. " +
			"    f ∈ «poles»(m).carrier ∧ n ≤ m ⇒ (f ∈ «poles»(n).carrier ⇔ f = L.zero ∨ -n ≤ «order»(f))) ∧ " +
			"(∀f:A. ∀n:num. ∀Q:prod(set(A), set(A)). " +
			"    f ∈ «poles»(n).carrier ∧ biaffine_regular_point(field_ring(L), k, A₀, A₁, A₀₁, Q) ∧ Q ≠ P ⇒ " +
			"    f ∈ point_local_ring(field_ring(L), A₀, A₁, Q))",
		Abbrev: Abbrev{
			{Name: "poles", Text: "λn:num. single_point_pole_space(field_ring(L), A₀, A₁, P, n)"},
			{Name: "order", Text: "regular_point_order(field_ring(L), A₀, A₁, P)"},
		},
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			P *Expr[Prod[Set[A], Set[A]]],
			curve, point Fact,
		) {
			ring := a.TermAs[RingOps[A]]("field_ring(L)")
			localRing := a.Conjuncts(
				GroupPremises(curve, point, RegularPointLocalRing.Read(L).At(k, A0, A1, A01, t, P)),
				"P's chart is a subring",
				"P's ideal is maximal there",
				"and invertible",
				"the local ring is a subring",
				"it holds the chart",
				"its maximal ideal is invertible",
				"each signed power of P's ideal lies in the same power of the maximal ideal",
				"those powers are fractional ideals of the local ring")
			bound := a.Have(
				"a nonzero member of L(nP) has order at least −n",
				"∀f:A. ∀n:num. f ∈ «poles»(n).carrier ∧ f ≠ L.zero ⇒ -n ≤ «order»(f)",
				Derive(func(b *Argument) {
					f, n := b.FixAs[A]("f"), b.FixAs[Nat]("n")
					hyps := b.Conjuncts(
						b.Assume(),
						"f lies in L(nP)",
						"f is nonzero")
					minusN := b.TermAs[Int]("-&n")
					charts := PoleSpaceCharts.At(ring, A0, A1, P, n)
					both := b.Conjuncts(
						b.Have(
							"f lies in both charts' (−n)-th powers",
							"f ∈ signed_ideal_power(field_ring(L), A₀, fst(P), -n) ∧ "+
								"f ∈ signed_ideal_power(field_ring(L), A₁, snd(P), -n)",
							BySets(hyps[0], charts, lattice_pair.LatticePairH0Def)),
						"f lies in chart 0's power",
						"and in chart 1's")
					inChart := b.Have(
						"f lies in the (−n)-th power of P's ideal in P's chart",
						"f ∈ signed_ideal_power(field_ring(L), point_chart(A₀, A₁, P), point_ideal(A₀, P), -n)",
						Derive(func(c *Argument) {
							c.Cases(c.TermAs[Bool]("fst(P) = A₀"))
							c.When(
								"off chart 0, P's chart is A₁ and its ideal snd(P)",
								func(d *Argument, off Fact) {
									d.Show(
										"the chart 1 component",
										By(Normalized, off, biaffine_rational_point.PointOffChartZero.At(A0, A1, P), both[1]))
								})
							c.Otherwise(
								"on chart 0, P's chart is A₀ and its ideal fst(P)",
								func(d *Argument, on0 Fact) {
									d.Show(
										"the chart 0 component",
										By(Normalized, on0, biaffine_rational_point.PointOnChartZero.At(A0, A1, P), both[0]))
								})
						}))
					inLocal := b.Have(
						"hence f lies in the (−n)-th power of the maximal ideal of the local ring",
						"f ∈ "+
							"signed_ideal_power(field_ring(L), "+
							"    point_local_ring(field_ring(L), A₀, A₁, P), "+
							"    ideal_span(restrict_ring(field_ring(L), point_local_ring(field_ring(L), A₀, A₁, P)), "+
							"        point_ideal(A₀, P)), "+
							"    -n)",
						BySets(inChart, localRing[6].At(minusN)))
					inL := b.Have(
						"a fractional ideal of the local ring lies in L",
						"f ∈ L.carrier",
						BySets(
							inLocal,
							localRing[7].At(minusN),
							submodule.SubmoduleSubset.At(
								b.TermAs[RingOps[A]]("restrict_ring(field_ring(L), point_local_ring(field_ring(L), A₀, A₁, P))"),
								b.TermAs[module_record.ModuleOps[A, A]]("regular_module(field_ring(L))"),
								b.TermAs[Set[A]](
									"signed_ideal_power(field_ring(L), "+
										"    point_local_ring(field_ring(L), A₀, A₁, P), "+
										"    ideal_span(restrict_ring(field_ring(L), point_local_ring(field_ring(L), A₀, A₁, P)), "+
										"        point_ideal(A₀, P)), "+
										"    -n)"))))
					b.Show(
						"the order reads the power",
						By(
							curve,
							point,
							hyps[1],
							inLocal,
							OrderReadsPowers.Read(L).At(k, A0, A1, A01, t, P, b.MemberOf[on.L](f, inL), minusN)))
				}))
			data := a.Conjuncts(
				GroupPremises(curve, algebraic_curve.CurveLatticeData.Read(L).At(k, A0, A1, A01, t)),
				"the overlap lies in L",
				"the charts and their overlap are a biaffine datum",
				"k is a subfield of L",
				"the structure pair is a lattice pair",
				"its ambient is the overlap",
				"the structure pair is invertible",
				"the constants form a field",
				"the constants lie in both charts")
			invertiblePairs := a.Have(
				"the invertible pairs form a commutative monoid, which holds the inverse of P",
				"comm_monoid_on( "+
					"    {N:prod(set(A), set(A)) | invertible_lattice_pair(field_ring(L), A₀, A₁, A₀₁, N)}, "+
					"    lattice_pair_mul(field_ring(L), A₀, A₁), "+
					"    (A₀, A₁)) ∧ "+
					"invertible_lattice_pair(field_ring(L), "+
					"    A₀, "+
					"    A₁, "+
					"    A₀₁, "+
					"    lattice_pair_inverse(field_ring(L), A₀, A₁, P))",
				By(
					data[0],
					data[1],
					point,
					invertible_lattice_pair.InvertiblePairsCommMonoid.Read(L).At(A0, A1, A01, t),
					invertible_lattice_pair.InvertibleLatticeInverse.Read(L).At(A0, A1, A01, t, P),
					lattice_pair_twist.BiaffineRegularPointDef.At(ring, k, A0, A1, A01, P)))
			pairParts := a.Conjuncts(
				invertiblePairs,
				"the invertible pairs form a commutative monoid",
				"the inverse of P is one of them")
			step := a.Have(
				"each step of the filtration adds at most one dimension",
				"∀n:num. "+
					"    module_dim(restrict_ring(field_ring(L), k), «poles»(n + 1)) ≤ "+
					"    module_dim(restrict_ring(field_ring(L), k), «poles»(n)) + 1",
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]("n")
					inverse := b.TermAs[Prod[Set[A], Set[A]]]("lattice_pair_inverse(field_ring(L), A₀, A₁, P)")
					power := b.TermAs[Prod[Set[A], Set[A]]](
						"monoid_pow(λX:prod(set(A), set(A)). λY:prod(set(A), set(A)). " +
							"        lattice_pair_mul(field_ring(L), A₀, A₁, X, Y), " +
							"    (A₀, A₁), " +
							"    lattice_pair_inverse(field_ring(L), A₀, A₁, P), " +
							"    n)")
					invertible := b.Have(
						"the n-th power of the inverse of P is invertible",
						"invertible_lattice_pair(field_ring(L), "+
							"    A₀, "+
							"    A₁, "+
							"    A₀₁, "+
							"    monoid_pow(λX:prod(set(A), set(A)). λY:prod(set(A), set(A)). "+
							"            lattice_pair_mul(field_ring(L), A₀, A₁, X, Y), "+
							"        (A₀, A₁), "+
							"        lattice_pair_inverse(field_ring(L), A₀, A₁, P), "+
							"        n))",
						By(pairParts[1], At(comm_monoid.PowIn.Read(pairParts[0]), inverse, n)))
					finite := b.Have(
						"so its cohomology is finite",
						"lattice_pair_finite(restrict_ring(field_ring(L), A₀₁), "+
							"    k, "+
							"    regular_module(field_ring(L)), "+
							"    monoid_pow(λX:prod(set(A), set(A)). λY:prod(set(A), set(A)). "+
							"            lattice_pair_mul(field_ring(L), A₀, A₁, X, Y), "+
							"        (A₀, A₁), "+
							"        lattice_pair_inverse(field_ring(L), A₀, A₁, P), "+
							"        n))",
						By(curve, invertible, algebraic_curve.InvertibleFinite.Read(L).At(k, A0, A1, A01, t, power)))
					twisted := b.Have(
						"the next power is the twist by P, which adds at most one section",
						"lattice_pair_h0_dim(restrict_ring(field_ring(L), A₀₁), "+
							"    k, "+
							"    regular_module(field_ring(L)), "+
							"    monoid_pow(λX:prod(set(A), set(A)). λY:prod(set(A), set(A)). "+
							"            lattice_pair_mul(field_ring(L), A₀, A₁, X, Y), "+
							"        (A₀, A₁), "+
							"        lattice_pair_inverse(field_ring(L), A₀, A₁, P), "+
							"        suc(n))) ≤ "+
							"lattice_pair_h0_dim(restrict_ring(field_ring(L), A₀₁), "+
							"    k, "+
							"    regular_module(field_ring(L)), "+
							"    monoid_pow(λX:prod(set(A), set(A)). λY:prod(set(A), set(A)). "+
							"            lattice_pair_mul(field_ring(L), A₀, A₁, X, Y), "+
							"        (A₀, A₁), "+
							"        lattice_pair_inverse(field_ring(L), A₀, A₁, P), "+
							"        n)) + "+
							"1",
						By(
							data[0],
							data[1],
							data[2],
							data[7],
							invertible,
							finite,
							point,
							lattice_pair_twist.TwistH0Step.Read(L).At(k, A0, A1, A01, t, power, P),
							lattice_pair_twist.LatticePairTwistDef,
							comm_monoid.MonoidPowDef))
					successor := b.Have(
						"n + 1 is the successor of n",
						"n + 1 = suc(n)",
						ByArith())
					b.Show(
						"the sections are L(nP) and L((n + 1)P)",
						By(
							b.Simplified(twisted, Fwd(module_record.RestrictRingTwice), Fwd(lattice_pair.LatticePairH0DimDef)),
							successor,
							SinglePointPoleSpaceDef))
				}))
			cut := a.Have(
				"within L(mP), L(nP) is cut out by the order at P",
				Statement{
					Binders:    "∀f:A. ∀m n:num.",
					Hypotheses: []string{"f ∈ «poles»(m).carrier", "n ≤ m"},
					Conclusion: "f ∈ «poles»(n).carrier ⇔ f = L.zero ∨ -n ≤ «order»(f)",
				},
				Derive(func(b *Argument) {
					f, m, n := b.FixAs[A]("f"), b.FixAs[Nat]("m"), b.FixAs[Nat]("n")
					hyps := b.Conjuncts(
						b.Assume(),
						"f lies in L(mP)",
						"n ≤ m")
					b.Iff()
					b.Forward(
						"a member of L(nP) is zero or of order at least −n",
						func(c *Argument, inN Fact) {
							c.Show(
								"by the order bound",
								By(inN, bound))
						})
					b.Backward(
						"the order cuts L(nP) out of L(mP)",
						func(c *Argument, orders Fact) {
							c.Show(
								"by the order criterion",
								By(
									curve,
									point,
									hyps[0],
									hyps[1],
									orders,
									PoleSpaceCutByOrder.Read(L).At(k, A0, A1, A01, t, P, f, m, n)))
						})
				}))
			a.Show(
				"the step bound, the order bound, the cut, and regularity away from P",
				By(step, bound, cut, curve, point, Read(PoleSpaceRegularElsewhere, L)))
		}),
})}

// PoleSpaceRegularElsewhere — a function with poles only at P is regular at
// every other regular rational point Q. On a chart where Q's component q is
// proper, f lies in the (−n)-th power of P's component C there
// (PoleSpaceCharts), and C does not lie inside q, two rational points being
// told apart on a chart where one is proper
// (biaffine_rational_point.RationalPointsSeparate). A prime that does not hold
// C has its localization holding every signed power of C
// (subring_localization.LocalHoldsSignedPowers), and on Q's chart that
// localization is the local ring at Q.
var PoleSpaceRegularElsewhere = poleSpaceRegularElsewhereThm{family.Add(registry.ProofEntry{
	Name: "PoleSpaceRegularElsewhere",
	Key:  "prop_798b403c4b1a7ffb",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀P Q:prod(set(A), set(A)). ∀f:A. ∀n:num.",
		Hypotheses: []string{
			"curve_over_line(L, k, t, A₀, A₁, A₀₁)",
			"biaffine_regular_point(field_ring(L), k, A₀, A₁, A₀₁, P)",
			"biaffine_regular_point(field_ring(L), k, A₀, A₁, A₀₁, Q)",
			"Q ≠ P",
			"f ∈ single_point_pole_space(field_ring(L), A₀, A₁, P, n).carrier",
		},
		Conclusion: "f ∈ point_local_ring(field_ring(L), A₀, A₁, Q)",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			P, Q *Expr[Prod[Set[A], Set[A]]],
			f *Expr[A],
			n *Expr[Nat],
			curve, pointP, pointQ, distinct, poles Fact,
		) {
			ring := a.TermAs[RingOps[A]]("field_ring(L)")
			overlap := a.TermAs[RingOps[A]]("restrict_ring(field_ring(L), A₀₁)")
			inverseT := a.TermAs[A]("L.inv(t)")
			inverse := a.TermAs[Fun[A, A]]("L.inv")
			firstP, secondP := a.TermAs[Set[A]]("fst(P)"), a.TermAs[Set[A]]("snd(P)")
			firstQ, secondQ := a.TermAs[Set[A]]("fst(Q)"), a.TermAs[Set[A]]("snd(Q)")
			minusN := a.TermAs[Int]("-&n")
			inCharts := a.Conjuncts(
				a.Have(
					"f lies in the (−n)-th power of P's component on each chart",
					"f ∈ signed_ideal_power(field_ring(L), A₀, fst(P), -n) ∧ "+
						"f ∈ signed_ideal_power(field_ring(L), A₁, snd(P), -n)",
					poles.Simp(Fwd(PoleSpaceCharts)),
					BySets(poles)),
				"on chart 0",
				"and on chart 1")
			datum := a.Conjuncts(
				a.Have(
					"the overlap is a biaffine datum over the constants, "+
						"which lie in both charts, and the charts are subrings of L",
					"biaffine(restrict_ring(field_ring(L), A₀₁), A₀, A₁, t, L.inv(t)) ∧ "+
						"ring_subfield(restrict_ring(field_ring(L), A₀₁), L.inv, k) ∧ "+
						"k ⊆ A₀ ∧ "+
						"k ⊆ A₁ ∧ "+
						"subring(field_ring(L), A₀) ∧ "+
						"subring(field_ring(L), A₁)",
					BySets(
						curve,
						algebraic_curve.CurveOverItsLine.Read(L).At(k, A0, A1, A01, t),
						field.SubfieldRingSubfield.Read(L).At(k, A01))),
				"the overlap is a biaffine datum",
				"the constants are a field under its operations",
				"they lie in chart 0",
				"and in chart 1",
				"chart 0 is a subring of L",
				"and so is chart 1")
			biaffine, constants, constants0, constants1, chart0, chart1 :=
				datum[0], datum[1], datum[2], datum[3], datum[4], datum[5]
			rational := a.Conjuncts(
				a.Have(
					"P and Q are rational points of the overlap, and P's "+
						"components are invertible ideals inside their charts",
					"biaffine_rational_point(restrict_ring(field_ring(L), A₀₁), k, A₀, A₁, P) ∧ "+
						"biaffine_rational_point(restrict_ring(field_ring(L), A₀₁), k, A₀, A₁, Q) ∧ "+
						"invertible_fractional(field_ring(L), A₀, fst(P)) ∧ "+
						"invertible_fractional(field_ring(L), A₁, snd(P)) ∧ "+
						"fst(P) ⊆ A₀ ∧ "+
						"snd(P) ⊆ A₁",
					By(
						biaffine,
						pointP,
						pointQ,
						lattice_pair_twist.BiaffineRegularPointDef.At(ring, k, A0, A1, A01, P),
						lattice_pair_twist.BiaffineRegularPointDef.At(ring, k, A0, A1, A01, Q),
						invertible_lattice_pair.InvertibleLatticePairDef.At(ring, A0, A1, A01, P),
						biaffine_rational_point.PointIdealLattice.At(overlap, A0, A1, t, inverseT, k, P))),
				"P is a rational point of the overlap",
				"so is Q",
				"P's component on chart 0 is invertible",
				"and so is its component on chart 1",
				"P's component on chart 0 lies in chart 0",
				"and its component on chart 1 in chart 1")
			rationalP, rationalQ := rational[0], rational[1]
			maximal := a.Have(
				"a proper component of Q is a maximal ideal of its chart",
				"(fst(Q) ≠ A₀ ⇒ maximal_ideal(restrict_ring(field_ring(L), A₀), fst(Q))) ∧ "+
					"(snd(Q) ≠ A₁ ⇒ maximal_ideal(restrict_ring(field_ring(L), A₁), snd(Q)))",
				By(
					Normalized,
					constants0,
					constants1,
					constants,
					biaffine,
					rationalQ,
					biaffine_rational_point.RationalPointMaximal.At(overlap, A0, A1, t, inverseT, k, inverse, Q),
					module_record.RestrictRingTwice.At(ring, A01, A0),
					module_record.RestrictRingTwice.At(ring, A01, A1)))
			apart := a.Have(
				"P is not Q",
				"P ≠ Q",
				By(distinct))
			separated := a.Conjuncts(
				GroupPremises(
					biaffine,
					constants,
					constants0,
					constants1,
					rationalQ,
					rationalP,
					apart,
					biaffine_rational_point.RationalPointsSeparate.At(overlap, A0, A1, t, inverseT, k, inverse, Q, P)),
				"where Q's component on chart 0 is proper, P's does not lie inside it",
				"and likewise on chart 1")
			chartRing := comm_ring.SubringRingOn.Read(field.RingOn.Read(L))
			primes := a.Have(
				"Q's proper components are prime ideals of their charts",
				"(fst(Q) ≠ A₀ ⇒ prime_ideal(restrict_ring(field_ring(L), A₀), fst(Q))) ∧ "+
					"(snd(Q) ≠ A₁ ⇒ prime_ideal(restrict_ring(field_ring(L), A₁), snd(Q)))",
				By(
					chart0,
					chart1,
					maximal,
					chartRing.At(A0),
					chartRing.At(A1),
					ring_ideal.MaximalIsPrime.At(a.TermAs[RingOps[A]]("restrict_ring(field_ring(L), A₀)"), firstQ),
					ring_ideal.MaximalIsPrime.At(a.TermAs[RingOps[A]]("restrict_ring(field_ring(L), A₁)"), secondQ)))
			localized0 := a.Have(
				"where Q's component on chart 0 is proper, f lies in the localization of chart 0 at it",
				"fst(Q) ≠ A₀ ⇒ f ∈ subring_localization(field_ring(L), A₀, fst(Q))",
				Derive(func(b *Argument) {
					proper := b.Assume()
					b.Show(
						"the localization holds every signed power of P's component, which is not inside Q's",
						BySets(
							chart0,
							rational[4],
							rational[2],
							inCharts[0],
							separated[0],
							primes,
							proper,
							subring_localization.LocalHoldsSignedPowers.Read(L).At(A0, firstQ, firstP, minusN)))
				}))
			localized1 := a.Have(
				"where Q's component on chart 1 is proper, f lies in the localization of chart 1 at it",
				"snd(Q) ≠ A₁ ⇒ f ∈ subring_localization(field_ring(L), A₁, snd(Q))",
				Derive(func(b *Argument) {
					proper := b.Assume()
					b.Show(
						"the localization holds every signed power of P's component, which is not inside Q's",
						BySets(
							chart1,
							rational[5],
							rational[3],
							inCharts[1],
							separated[1],
							primes,
							proper,
							subring_localization.LocalHoldsSignedPowers.Read(L).At(A1, secondQ, secondP, minusN)))
				}))
			a.Cases(a.TermAs[Bool]("fst(Q) = A₀"))
			a.When(
				"Q lies off chart 0, so on chart 1 with a proper "+
					"component there, and its local ring is that localization",
				func(b *Argument, off Fact) {
					b.Show(
						"the local ring at Q is the localization of its chart at its ideal",
						Simp(
							Fwd(PointLocalRingDef),
							Fwd(biaffine_rational_point.PointChartDef),
							Fwd(biaffine_rational_point.PointIdealDef)),
						By(
							off,
							localized1,
							rationalQ,
							biaffine_rational_point.BiaffineRationalPointDef.At(overlap, k, A0, A1, Q)))
				})
			a.Otherwise(
				"Q lies on chart 0, and its local ring is the localization of chart 0 at fst(Q)",
				func(b *Argument, on0 Fact) {
					b.Show(
						"the local ring at Q is the localization of its chart at its ideal",
						Simp(
							Fwd(PointLocalRingDef),
							Fwd(biaffine_rational_point.PointChartDef),
							Fwd(biaffine_rational_point.PointIdealDef)),
						By(on0, localized0))
				})
		}),
})}

// PoleSpaceCutByLocalPower — within L(mP), n ≤ m, a function that lies in the
// (−n)-th power of the maximal ideal 𝔪 of the local ring at P whenever it is
// nonzero lies in L(nP). L(nP) is the meet of the charts' (−n)-th signed
// powers of P's components (PoleSpaceCharts), and q^(−n) is the inverse of qⁿ
// (signed_ideal_power.SignedPowerInverse). So f, lying in q^(−m) for a maximal
// invertible component q of a chart T, lies in q^(−n) once each f·x with x in
// qⁿ is brought into T by some b off q: f·x lies in q^(n−m), the inverse of
// q^(m−n), and b, a unit modulo q^(m−n), brings it into T
// (subring_localization.ClearedOffMaximalIntegral). In P's chart, f·x lies in
// 𝔪^(−n)·𝔪ⁿ = 𝔪⁰, the local ring, the localization of the chart at P's
// ideal, so a fraction of the chart with denominator off that ideal. A
// component equal to its chart has every signed power equal to the chart
// (signed_ideal_power.SignedPowerOfRing). On the overlap of the charts, f and x
// extend to opposite powers of the one ideal of A₀₁ that both components
// generate (P's pair is a lattice pair, subring_localization.ExtensionOfSignedPowers), so f·x lies
// in A₀₁, and a power of s = t⁻¹ brings it into A₁; s lies off snd(P), whose
// span in A₀₁ misses one.
var PoleSpaceCutByLocalPower = poleSpaceCutByLocalPowerThm{family.Add(registry.ProofEntry{
	Name: "PoleSpaceCutByLocalPower",
	Key:  "prop_fbb7148fe2f6e280",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀P:prod(set(A), set(A)). ∀f:A. ∀m n:num.",
		Hypotheses: []string{
			"curve_over_line(L, k, t, A₀, A₁, A₀₁)",
			"biaffine_regular_point(field_ring(L), k, A₀, A₁, A₀₁, P)",
			"f ∈ single_point_pole_space(field_ring(L), A₀, A₁, P, m).carrier",
			"n ≤ m",
			"f ∈ L.carrier ∧ f ≠ L.zero ⇒ f ∈ «power»(-int_of_num(n))",
		},
		Conclusion: "f ∈ single_point_pole_space(field_ring(L), A₀, A₁, P, n).carrier",
		Abbrev: Abbrev{
			{Name: "local", Text: "point_local_ring(field_ring(L), A₀, A₁, P)"},
			{Name: "maximal", Text: "ideal_span(restrict_ring(field_ring(L), «local»), point_ideal(A₀, P))"},
			{Name: "power", Text: "λj:int. signed_ideal_power(field_ring(L), «local», «maximal», j)"},
			{Name: "extended", Text: "module_span(restrict_ring(field_ring(L), A₀₁), " +
				"    regular_module(field_ring(L)))"},
		},
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			P *Expr[Prod[Set[A], Set[A]]],
			f *Expr[A],
			m, n *Expr[Nat],
			h Fact,
		) {
			given := a.Conjuncts(
				h,
				"the charts present a curve over the line of t",
				"P is a regular rational point",
				"f lies in L(mP)",
				"n ≤ m",
				"f, if a nonzero function, lies in 𝔪^(−n)")
			curve, regular, inPoles, below, nonzeroPower := given[0], given[1], given[2], given[3], given[4]
			fieldRing := a.TermAs[RingOps[A]]("field_ring(L)")
			overlapRing := a.TermAs[RingOps[A]]("restrict_ring(field_ring(L), A₀₁)")
			chart1Ring := a.TermAs[RingOps[A]]("restrict_ring(field_ring(L), A₁)")
			vectors := a.TermAs[module_record.ModuleOps[A, A]]("regular_module(field_ring(L))")
			chart, ideal := a.TermAs[Set[A]]("point_chart(A₀, A₁, P)"), a.TermAs[Set[A]]("point_ideal(A₀, P)")
			offChart0, onChart0 :=
				biaffine_rational_point.PointOffChartZero.At(A0, A1, P),
				biaffine_rational_point.PointOnChartZero.At(A0, A1, P)
			local := a.TermAs[Set[A]]("«local»")
			first, second := a.TermAs[Set[A]]("fst(P)"), a.TermAs[Set[A]]("snd(P)")
			s := a.TermAs[A]("L.inv(t)")
			minusM, minusN := a.TermAs[Int]("-&m"), a.TermAs[Int]("-&n")
			plusN := a.TermAs[Int]("n")
			localRing := a.Conjuncts(
				GroupPremises(curve, regular, RegularPointLocalRing.Read(L).At(k, A0, A1, A01, t, P)),
				"P's chart is a subring",
				"P's ideal is maximal there",
				"and invertible",
				"the local ring is a subring",
				"it holds the chart",
				"its maximal ideal 𝔪 is invertible",
				"each signed power of P's ideal lies in the same power of 𝔪",
				"those powers are fractional ideals of the local ring")
			chartSubring, idealMaximal, idealInvertible := localRing[0], localRing[1], localRing[2]
			localSubring, maximalInvertible := localRing[3], localRing[5]
			powersBelow, powersFractional := localRing[6], localRing[7]
			charts := a.Conjuncts(
				a.Have(
					"the charts and their overlap are subrings of L, the overlap being chart 1 with s = t⁻¹ inverted",
					"subring(field_ring(L), A₀₁) ∧ "+
						"subring(field_ring(L), A₀) ∧ "+
						"subring(field_ring(L), A₁) ∧ "+
						"A₀ ⊆ A₀₁ ∧ "+
						"A₁ ⊆ A₀₁ ∧ "+
						"t ∈ A₀₁ ∧ "+
						"L.inv(t) ∈ A₁ ∧ "+
						"t * L.inv(t) = L.one ∧ "+
						"A₀₁ = ring_away(restrict_ring(field_ring(L), A₀₁), A₁, L.inv(t))",
					BySets(curve, algebraic_curve.CurveOverItsLine.Read(L).At(k, A0, A1, A01, t))),
				"the overlap is a subring",
				"so is chart 0",
				"and chart 1",
				"chart 0 lies in the overlap",
				"and so does chart 1",
				"t lies in the overlap",
				"s lies in chart 1",
				"t·s is one",
				"the overlap is chart 1 with s inverted")
			overlapSubring, chart0Subring, chart1Subring := charts[0], charts[1], charts[2]
			chart0InOverlap, chart1InOverlap := charts[3], charts[4]
			tInOverlap, sInChart1, tsOne, overlapAway := charts[5], charts[6], charts[7], charts[8]
			both := a.Conjuncts(
				a.Have(
					"f lies in both charts' (−m)-th powers",
					"f ∈ signed_ideal_power(field_ring(L), A₀, fst(P), -int_of_num(m)) ∧ "+
						"f ∈ signed_ideal_power(field_ring(L), A₁, snd(P), -int_of_num(m))",
					BySets(inPoles, PoleSpaceCharts.At(fieldRing, A0, A1, P, m), lattice_pair.LatticePairH0Def)),
				"f lies in chart 0's (−m)-th power",
				"and in chart 1's")
			fInPower0, fInPower1 := both[0], both[1]
			inChart := a.Have(
				"f lies in the (−m)-th power of P's ideal in P's chart",
				"f ∈ signed_ideal_power(field_ring(L), point_chart(A₀, A₁, P), point_ideal(A₀, P), -int_of_num(m))",
				Derive(func(b *Argument) {
					b.Cases(b.TermAs[Bool]("fst(P) = A₀"))
					b.When(
						"off chart 0, P's chart is A₁",
						func(c *Argument, off Fact) {
							c.Show(
								"the chart 1 component",
								By(Normalized, off, offChart0, fInPower1))
						})
					b.Otherwise(
						"on chart 0, P's chart is A₀",
						func(c *Argument, on0 Fact) {
							c.Show(
								"the chart 0 component",
								By(Normalized, on0, onChart0, fInPower0))
						})
				}))
			fInL := a.Have(
				"f lies in L, a fractional ideal holding it",
				"f ∈ L.carrier",
				BySets(
					inChart,
					chartSubring,
					idealInvertible,
					signed_ideal_power.SignedIdealPowerLaws.Read(L).At(chart, ideal),
					submodule.SubmoduleSubset.At(
						a.TermAs[RingOps[A]]("restrict_ring(field_ring(L), point_chart(A₀, A₁, P))"),
						vectors,
						a.TermAs[Set[A]](
							"signed_ideal_power(field_ring(L), point_chart(A₀, A₁, P), point_ideal(A₀, P), -int_of_num(m))"))))
			exponent := a.Have(
				"n − m is −(m − n), as n ≤ m",
				"-&m + int_of_num(n) = -int_of_num(m - n)",
				ByArith(below, At(int_embed.OfNumSub, n, m)))
			cancel := a.Have(
				"−n and n cancel",
				"-n + int_of_num(n) = 0",
				ByArith())
			clearing := a.Have(
				"f, in q^(−m) for a maximal invertible ideal q of T, lies in "+
					"q^(−n) once each f·x with x in qⁿ is brought into T by some b off q",
				Statement{
					Binders: "∀T q:set(A).",
					Hypotheses: []string{
						"subring(field_ring(L), T)",
						"maximal_ideal(restrict_ring(field_ring(L), T), q)",
						"invertible_fractional(field_ring(L), T, q)",
						"f ∈ signed_ideal_power(field_ring(L), T, q, -int_of_num(m))",
						"∀x:A. " +
							"    x ∈ signed_ideal_power(field_ring(L), T, q, int_of_num(n)) ⇒ " +
							"    ∃b:A. b ∈ T ∧ b ∉ q ∧ f * x * b ∈ T",
					},
					Conclusion: "f ∈ signed_ideal_power(field_ring(L), T, q, -int_of_num(n))",
				},
				Derive(func(b *Argument) {
					T, q := b.FixAs[Set[A]]("T"), b.FixAs[Set[A]]("q")
					hyps := b.Conjuncts(
						b.Assume(),
						"T is a subring of L",
						"q is a maximal ideal of T",
						"q is invertible over T",
						"f lies in q^(−m)",
						"each f·x with x in qⁿ is brought into T by some b off q")
					subringT, maximalQ, invertibleQ, fInPower, clears := hyps[0], hyps[1], hyps[2], hyps[3], hyps[4]
					multiples := b.Have(
						"f multiplies qⁿ into T",
						"∀x:A. x ∈ signed_ideal_power(field_ring(L), T, q, int_of_num(n)) ⇒ f * x ∈ T",
						Derive(func(c *Argument) {
							x := c.FixAs[A]("x")
							xIn := c.Assume()
							den, brought := c.UnpackAs[A](GroupPremises(xIn, clears.At(x)), "b")
							parts := c.Conjuncts(
								brought,
								"b lies in T",
								"b lies off q",
								"f·x·b lies in T")
							product := c.Have(
								"f·x lies in q^(−m)·qⁿ, the power q^(n−m)",
								"f * x ∈ signed_ideal_power(field_ring(L), T, q, -int_of_num(m) + int_of_num(n))",
								By(
									fInPower,
									xIn,
									subringT,
									invertibleQ,
									fractional_ideal.FractionalMulHolds.Read(L).At(
										T,
										c.TermAs[Set[A]]("signed_ideal_power(field_ring(L), T, q, -int_of_num(m))"),
										c.TermAs[Set[A]]("signed_ideal_power(field_ring(L), T, q, int_of_num(n))"),
										f,
										x),
									signed_ideal_power.SignedIdealPowerLaws.Read(L).At(T, q)))
							inverse := c.Have(
								"which is the inverse of q^(m−n)",
								"f * x ∈ "+
									"fractional_inverse(field_ring(L), "+
									"    T, "+
									"    monoid_pow(λX:set(A). λY:set(A). fractional_mul(field_ring(L), T, X, Y), T, q, m - n))",
								By(
									product,
									exponent,
									subringT,
									invertibleQ,
									signed_ideal_power.SignedPowerInverse.Read(L).At(T, q, c.TermAs[Int]("m - n")),
									signed_ideal_power.SignedIdealPowerLaws.Read(L).At(T, q)))
							c.Show(
								"b, a unit modulo q^(m−n), brings f·x into T",
								By(
									subringT,
									maximalQ,
									inverse,
									parts[0],
									parts[1],
									parts[2],
									subring_localization.ClearedOffMaximalIntegral.Read(L).At(
										T, q, c.TermAs[A]("f * x"), den, c.TermAs[Nat]("m - n"))))
						}))
					b.Show(
						"so f lies in the inverse of qⁿ, which is q^(−n)",
						BySets(
							multiples,
							fInL,
							subringT,
							invertibleQ,
							signed_ideal_power.SignedPowerInverse.Read(L).At(T, q, plusN),
							fractional_ideal.FractionalInverseDef.At(
								fieldRing, T, b.TermAs[Set[A]]("signed_ideal_power(field_ring(L), T, q, int_of_num(n))"))))
				}))
			inPower := a.Have(
				"f lies in 𝔪^(−n)",
				"f ∈ «power»(-int_of_num(n))",
				Derive(func(b *Argument) {
					b.Cases(b.TermAs[Bool]("f = L.zero"))
					b.When(
						"zero lies in every power of 𝔪, a fractional ideal",
						func(c *Argument, zero Fact) {
							c.Show(
								"the (−n)-th power holds zero",
								By(
									zero,
									powersFractional.At(minusN),
									submodule.SubmoduleZero.At(
										c.TermAs[RingOps[A]]("restrict_ring(field_ring(L), «local»)"),
										vectors,
										c.TermAs[Set[A]]("«power»(-int_of_num(n))"))))
						})
					b.Otherwise(
						"a nonzero f lies there by hypothesis",
						func(c *Argument, nonzero Fact) {
							c.Show(
								"f is a nonzero function",
								By(nonzeroPower, fInL, nonzero))
						})
				}))
			clearChart := a.Have(
				"each f·x with x in the n-th power of P's ideal is "+
					"brought into P's chart by a denominator off P's ideal",
				Statement{
					Binders: "∀x:A.",
					Hypotheses: []string{
						"x ∈ signed_ideal_power(field_ring(L), point_chart(A₀, A₁, P), point_ideal(A₀, P), int_of_num(n))",
					},
					Conclusion: "∃b:A. " +
						"    b ∈ point_chart(A₀, A₁, P) ∧ b ∉ point_ideal(A₀, P) ∧ f * x * b ∈ point_chart(A₀, A₁, P)",
				},
				Derive(func(b *Argument) {
					x := b.FixAs[A]("x")
					xIn := b.Assume()
					xLocal := b.Have(
						"x lies in 𝔪ⁿ",
						"x ∈ «power»(int_of_num(n))",
						BySets(xIn, powersBelow.At(plusN)))
					inLocal := b.Have(
						"so f·x lies in 𝔪^(−n)·𝔪ⁿ = 𝔪⁰, the local ring",
						"f * x ∈ «local»",
						By(
							inPower,
							xLocal,
							cancel,
							localSubring,
							maximalInvertible,
							fractional_ideal.FractionalMulHolds.Read(L).At(
								local,
								b.TermAs[Set[A]]("«power»(-int_of_num(n))"),
								b.TermAs[Set[A]]("«power»(int_of_num(n))"),
								f,
								x),
							signed_ideal_power.SignedIdealPowerLaws.Read(L).At(local, b.TermAs[Set[A]]("«maximal»"))))
					_, den, fraction := b.Obtain2As[A, A](
						"f·x is a fraction a / b of P's chart with b off P's ideal",
						"∃a b:A. "+
							"    a ∈ point_chart(A₀, A₁, P) ∧ "+
							"    b ∈ point_chart(A₀, A₁, P) ∧ "+
							"    b ∉ point_ideal(A₀, P) ∧ "+
							"    f * x * b = a",
						BySets(
							inLocal,
							PointLocalRingDef.At(fieldRing, A0, A1, P),
							subring_localization.SubringLocalizationDef.At(fieldRing, chart, ideal)))
					b.Take(den)
					b.Show(
						"b brings f·x to a, in the chart",
						By(Normalized, fraction))
				}))
			main := a.Have(
				"f lies in the (−n)-th power of P's ideal in P's chart",
				"f ∈ signed_ideal_power(field_ring(L), point_chart(A₀, A₁, P), point_ideal(A₀, P), -int_of_num(n))",
				By(clearing.At(chart, ideal), chartSubring, idealMaximal, idealInvertible, inChart, clearChart))
			// On the overlap of the charts, chart 1 is cleared through A₀₁.
			overlap := a.Have(
				"on the overlap of the charts, f lies in chart 1's (−n)-th power too",
				"fst(P) ≠ A₀ ∧ snd(P) ≠ A₁ ⇒ f ∈ signed_ideal_power(field_ring(L), A₁, snd(P), -int_of_num(n))",
				Derive(func(b *Argument) {
					sides := b.Conjuncts(
						b.Assume(),
						"P lies on chart 0",
						"and on chart 1")
					chart0 := b.Have(
						"f lies in fst(P)^(−n), P's chart being A₀",
						"f ∈ signed_ideal_power(field_ring(L), A₀, fst(P), -int_of_num(n))",
						By(Normalized, sides[0], onChart0, main))
					pair := b.Conjuncts(
						b.Have(
							"P is a rational point whose components are invertible and generate one A₀₁-module",
							"biaffine_rational_point(restrict_ring(field_ring(L), A₀₁), k, A₀, A₁, P) ∧ "+
								"invertible_fractional(field_ring(L), A₀, fst(P)) ∧ "+
								"invertible_fractional(field_ring(L), A₁, snd(P)) ∧ "+
								"«extended»(fst(P)) = «extended»(snd(P))",
							By(
								regular,
								lattice_pair_twist.BiaffineRegularPointDef.At(fieldRing, k, A0, A1, A01, P),
								invertible_lattice_pair.InvertibleLatticePairDef.At(fieldRing, A0, A1, A01, P),
								lattice_pair.LatticePairDef.At(overlapRing, A0, A1, vectors, P))),
						"P is a rational point",
						"fst(P) is invertible over A₀",
						"snd(P) is invertible over A₁",
						"the two components generate one A₀₁-module")
					rationalP, firstInvertible, secondInvertible, sameModule := pair[0], pair[1], pair[2], pair[3]
					proper := b.Have(
						"the ideal snd(P) generates in A₀₁ misses one, P lying on both charts",
						"L.one ∉ ideal_span(restrict_ring(field_ring(L), A₀₁), snd(P))",
						By(
							rationalP,
							sides[0],
							sides[1],
							biaffine_rational_point.BiaffineRationalPointDef.At(overlapRing, k, A0, A1, P)))
					data := b.Conjuncts(
						GroupPremises(curve, algebraic_curve.CurveLatticeData.Read(L).At(k, A0, A1, A01, t)),
						"the overlap lies in L",
						"the charts and their overlap are a biaffine datum",
						"k is a subfield of L",
						"the structure pair is a lattice pair",
						"its ambient is the overlap",
						"the structure pair is invertible",
						"the constants form a field under L's operations",
						"the constants lie in both charts")
					kInCharts := b.Have(
						"k lies in each chart",
						"k ⊆ A₀ ∧ k ⊆ A₁",
						BySets(data[7]))
					maximal := b.Have(
						"snd(P), a proper component, is a maximal ideal of A₁",
						"maximal_ideal(restrict_ring(field_ring(L), A₁), snd(P))",
						By(
							Normalized,
							data[1],
							data[2],
							kInCharts,
							rationalP,
							sides[1],
							field.SubfieldRingSubfield.Read(L).At(k, A01),
							biaffine_rational_point.RationalPointMaximal.At(
								overlapRing, A0, A1, t, s, k, b.TermAs[Fun[A, A]]("L.inv"), P),
							module_record.RestrictRingTwice.At(fieldRing, A01, A1)))
					overlapIsRing := b.Have(
						"A₀₁ is a ring under L's operations",
						"comm_ring_on(restrict_ring(field_ring(L), A₀₁))",
						By(overlapSubring, comm_ring.SubringRingOn.Read(field.RingOn.Read(L)).At(A01)))
					inOverlap := b.Have(
						"snd(P), an ideal of A₁, lies in A₀₁",
						"snd(P) ⊆ A₀₁",
						BySets(
							maximal,
							chart1InOverlap,
							ring_ideal.MaximalIdealIdeal.At(chart1Ring, second),
							ring_ideal.IdealSubset.At(chart1Ring, second)))
					sOff := b.Have(
						"s lies off snd(P): else t·s = one would lie in the ideal snd(P) generates in A₀₁",
						"L.inv(t) ∉ snd(P)",
						BySets(
							proper,
							tsOne,
							tInOverlap,
							inOverlap,
							ring_ideal.SpanContains.At(overlapRing, second),
							ring_ideal.SpanIdeal.Read(overlapIsRing).At(second),
							ring_ideal.IdealMul.At(
								overlapRing, b.TermAs[Set[A]]("ideal_span(restrict_ring(field_ring(L), A₀₁), snd(P))"), t, s)))
					chart1IsRing := b.Have(
						"A₁ is a ring under L's operations",
						"comm_ring_on(restrict_ring(field_ring(L), A₁))",
						By(chart1Subring, comm_ring.SubringRingOn.Read(field.RingOn.Read(L)).At(A1)))
					prime1 := b.Have(
						"so snd(P) is prime in A₁",
						"prime_ideal(restrict_ring(field_ring(L), A₁), snd(P))",
						By(maximal, ring_ideal.MaximalIsPrime.Read(chart1IsRing).At(second)))
					fExtended := b.Have(
						"extended to A₀₁, f lies in the (−n)-th power of the ideal fst(P) generates there",
						"f ∈ signed_ideal_power(field_ring(L), A₀₁, «extended»(fst(P)), -int_of_num(n))",
						BySets(
							chart0,
							chart0Subring,
							overlapSubring,
							chart0InOverlap,
							firstInvertible,
							subring_localization.ExtensionOfSignedPowers.Read(L).At(A0, A01, first, minusN),
							submodule.SubsetSpan.At(
								overlapRing,
								vectors,
								b.TermAs[Set[A]]("signed_ideal_power(field_ring(L), A₀, fst(P), -int_of_num(n))"))))
					invertibleExtended := b.Have(
						"that ideal is invertible over A₀₁",
						"invertible_fractional(field_ring(L), A₀₁, «extended»(fst(P)))",
						By(
							chart0Subring,
							overlapSubring,
							chart0InOverlap,
							firstInvertible,
							subring_localization.ExtensionOfInvertible.Read(L).At(A0, A01, first)))
					clearOverlap := b.Have(
						"each f·x with x in snd(P)ⁿ is brought into A₁ by a power of s, which lies off snd(P)",
						Statement{
							Binders:    "∀x:A.",
							Hypotheses: []string{"x ∈ signed_ideal_power(field_ring(L), A₁, snd(P), int_of_num(n))"},
							Conclusion: "∃b:A. b ∈ A₁ ∧ b ∉ snd(P) ∧ f * x * b ∈ A₁",
						},
						Derive(func(c *Argument) {
							x := c.FixAs[A]("x")
							xIn := c.Assume()
							xExtended := c.Have(
								"extended to A₀₁, x lies in the n-th power of that ideal, which snd(P) generates too",
								"x ∈ signed_ideal_power(field_ring(L), A₀₁, «extended»(fst(P)), int_of_num(n))",
								BySets(
									xIn,
									chart1Subring,
									overlapSubring,
									chart1InOverlap,
									secondInvertible,
									sameModule,
									subring_localization.ExtensionOfSignedPowers.Read(L).At(A1, A01, second, plusN),
									submodule.SubsetSpan.At(
										overlapRing,
										vectors,
										c.TermAs[Set[A]]("signed_ideal_power(field_ring(L), A₁, snd(P), int_of_num(n))"))))
							inA01 := c.Have(
								"so f·x lies in the 0-th power, A₀₁",
								"f * x ∈ A₀₁",
								By(
									fExtended,
									xExtended,
									cancel,
									overlapSubring,
									invertibleExtended,
									fractional_ideal.FractionalMulHolds.Read(L).At(
										A01,
										c.TermAs[Set[A]]("signed_ideal_power(field_ring(L), A₀₁, «extended»(fst(P)), -int_of_num(n))"),
										c.TermAs[Set[A]]("signed_ideal_power(field_ring(L), A₀₁, «extended»(fst(P)), int_of_num(n))"),
										f,
										x),
									signed_ideal_power.SignedIdealPowerLaws.Read(L).At(A01, c.TermAs[Set[A]]("«extended»(fst(P))"))))
							N, brought := c.ObtainAs[Nat](
								"a power of s brings f·x into A₁, A₀₁ being A₁ with s inverted",
								"∃N:num. monoid_pow(L.mul, L.one, L.inv(t), N) * (f * x) ∈ A₁",
								BySets(inA01, overlapAway, ring_away.RingAwayDef.At(overlapRing, A1, s)))
							power := c.Have(
								"sᴺ lies in A₁, and off the prime snd(P) as s does",
								"monoid_pow(L.mul, L.one, L.inv(t), N) ∈ A₁ ∧ monoid_pow(L.mul, L.one, L.inv(t), N) ∉ snd(P)",
								By(
									prime1,
									sInChart1,
									sOff,
									comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(chart1IsRing)).AsFact().At(s, N),
									ring_ideal.PrimeIdealPow.Read(chart1IsRing).AsFact().At(second, s, N)))
							members := c.Have(
								"x and sᴺ lie in L",
								"x ∈ L.carrier ∧ monoid_pow(L.mul, L.one, L.inv(t), N) ∈ L.carrier",
								BySets(
									xIn,
									chart1Subring,
									secondInvertible,
									power,
									signed_ideal_power.SignedIdealPowerLaws.Read(L).At(A1, second),
									submodule.SubmoduleSubset.At(
										chart1Ring,
										vectors,
										c.TermAs[Set[A]]("signed_ideal_power(field_ring(L), A₁, snd(P), int_of_num(n))")),
									comm_ring.SubringSubset.At(fieldRing, A1)))
							swap := c.Have(
								"f·x·sᴺ = sᴺ·(f·x)",
								"f * x * monoid_pow(L.mul, L.one, L.inv(t), N) = monoid_pow(L.mul, L.one, L.inv(t), N) * (f * x)",
								ByArith(L, fInL, members))
							c.Take(c.TermAs[A]("monoid_pow(L.mul, L.one, L.inv(t), N)"))
							c.Show(
								"sᴺ brings f·x into A₁",
								By(swap, brought, power))
						}))
					b.Show(
						"by the clearing in chart 1",
						By(clearing.At(A1, second), chart1Subring, maximal, secondInvertible, fInPower1, clearOverlap))
				}))
			// The two components of L(nP).
			chart0Part := a.Have(
				"f lies in chart 0's (−n)-th power",
				"f ∈ signed_ideal_power(field_ring(L), A₀, fst(P), -int_of_num(n))",
				Derive(func(b *Argument) {
					b.Cases(b.TermAs[Bool]("fst(P) = A₀"))
					b.When(
						"off chart 0, fst(P) is all of A₀, and so is each of its powers",
						func(c *Argument, off Fact) {
							c.Show(
								"both powers are A₀",
								By(
									Normalized,
									off,
									chart0Subring,
									fInPower0,
									signed_ideal_power.SignedPowerOfRing.Read(L).At(A0, minusM),
									signed_ideal_power.SignedPowerOfRing.Read(L).At(A0, minusN)))
						})
					b.Otherwise(
						"on chart 0, P's chart is A₀",
						func(c *Argument, on0 Fact) {
							c.Show(
								"the chart of P",
								By(Normalized, on0, onChart0, main))
						})
				}))
			chart1Part := a.Have(
				"f lies in chart 1's (−n)-th power",
				"f ∈ signed_ideal_power(field_ring(L), A₁, snd(P), -int_of_num(n))",
				Derive(func(b *Argument) {
					b.Cases(b.TermAs[Bool]("fst(P) = A₀"))
					b.When(
						"off chart 0, P's chart is A₁",
						func(c *Argument, off Fact) {
							c.Show(
								"the chart of P",
								By(Normalized, off, offChart0, main))
						})
					b.Otherwise(
						"on chart 0",
						func(c *Argument, on0 Fact) {
							c.Cases(c.TermAs[Bool]("snd(P) = A₁"))
							c.When(
								"off chart 1, snd(P) is all of A₁, and so is each of its powers",
								func(d *Argument, off1 Fact) {
									d.Show(
										"both powers are A₁",
										By(
											Normalized,
											off1,
											chart1Subring,
											fInPower1,
											signed_ideal_power.SignedPowerOfRing.Read(L).At(A1, minusM),
											signed_ideal_power.SignedPowerOfRing.Read(L).At(A1, minusN)))
								})
							c.Otherwise(
								"on both charts",
								func(d *Argument, on1 Fact) {
									d.Show(
										"the overlap",
										By(overlap, on0, on1))
								})
						})
				}))
			a.Show(
				"L(nP) is the meet of the two components",
				BySets(
					chart0Part,
					chart1Part,
					PoleSpaceCharts.At(fieldRing, A0, A1, P, n),
					lattice_pair.LatticePairH0Def))
		}),
})}

// PoleSpaceCutByOrder — inside L(mP), a function lies in L(nP), n ≤ m,
// when it is zero or its order at P is at least −n: a nonzero function of
// order at least −n lies in the (−n)-th power of the maximal ideal of the
// local ring at P (OrderReadsPowers), and that power cuts L(nP) out of L(mP)
// (PoleSpaceCutByLocalPower).
var PoleSpaceCutByOrder = poleSpaceCutByOrderThm{family.Add(registry.ProofEntry{
	Name: "PoleSpaceCutByOrder",
	Key:  "prop_49c754cb31b71869",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀P:prod(set(A), set(A)). ∀f:A. ∀m n:num.",
		Hypotheses: []string{
			"curve_over_line(L, k, t, A₀, A₁, A₀₁)",
			"biaffine_regular_point(field_ring(L), k, A₀, A₁, A₀₁, P)",
			"f ∈ single_point_pole_space(field_ring(L), A₀, A₁, P, m).carrier",
			"n ≤ m",
			"f = L.zero ∨ -n ≤ regular_point_order(field_ring(L), A₀, A₁, P, f)",
		},
		Conclusion: "f ∈ single_point_pole_space(field_ring(L), A₀, A₁, P, n).carrier",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			P *Expr[Prod[Set[A], Set[A]]],
			f *Expr[A],
			m, n *Expr[Nat],
			curve, point, inPoles, below, order Fact,
		) {
			nonzero := a.Have(
				"a nonzero f of L, of order at least −n, lies in the "+
					"(−n)-th power of the maximal ideal of the local ring at P",
				Statement{
					Hypotheses: []string{"f ∈ L.carrier", "f ≠ L.zero"},
					Conclusion: "f ∈ " +
						"signed_ideal_power(field_ring(L), " +
						"    point_local_ring(field_ring(L), A₀, A₁, P), " +
						"    ideal_span(restrict_ring(field_ring(L), point_local_ring(field_ring(L), A₀, A₁, P)), " +
						"        point_ideal(A₀, P)), " +
						"    -n)",
				},
				By(
					curve,
					point,
					order,
					OrderReadsPowers.Read(L).AsFact().At(k, A0, A1, A01, t, P, f, a.TermAs[Int]("-&n"))))
			a.Show(
				"the cut by the local power is the cut by the order",
				By(
					curve,
					point,
					inPoles,
					below,
					nonzero,
					PoleSpaceCutByLocalPower.Read(L).At(k, A0, A1, A01, t, P, f, m, n)))
		}),
})}
