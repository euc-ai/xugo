// localizations.go — the structure sheaf computed by localizations of the
// ring, in two parts marked by banners: the sections over a basic open
// set D(f), the global sections among them; and the stalks, which make
// the spectrum a locally ringed space.

package structure_sheaf

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/local_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_ideal"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_localization"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/scheme/locally_ringed_space"
	"github.com/euc-ai/xugo/library/proofs/scheme/prime_spectrum"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/proofs/topology/compact"
	"github.com/euc-ai/xugo/library/proofs/topology/presheaf"
	"github.com/euc-ai/xugo/library/proofs/topology/topological_space"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The sections over a basic open set
// ---------------------------------------------------------------------------

// CoefficientSectionHomomorphism — coefficients give a ring
// homomorphism into the sections over an open set. At each prime this
// is the coefficient map into its localization; outside the open set
// the sections and their pointwise operations are empty.
var CoefficientSectionHomomorphism = coefficientSectionHomomorphismThm{family.Add(registry.ProofEntry{
	Name: "CoefficientSectionHomomorphism",
	Key:  "prop_b6a5c469ae5cf83",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀U:set(set(A)).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"U ∈ zariski_topology(R)",
		},
		Conclusion: "ring_homomorphism(R, spec_section_ops(R, U), «coefficientSection»(R, U))",
	}, func(
		a *Argument,
		R *Expr[RingOps[A]],
		ring comm_ring.CommRingFact[on.R],
		U *Expr[Set[Set[A]]],
		open Fact,
	) {
		a.Do(Simp(Fwd(ring_homomorphism.RingHomomorphism)), SplitConjAll(
			Case(
				"the source is the given ring",
				By(ring)),
			Case(
				"the target is the section ring",
				By(ring, open, StructureSectionRing.At(R, U))),
			Case(
				"each coefficient defines a section",
				Derive(func(b *Argument) {
					x := b.FixAs[A]("x")
					xIn := b.Assume()
					oneOutside := b.Have(
						"one lies outside every prime of U",
						"∀q:set(A). q ∈ U ⇒ R.one ∉ q",
						By(open, ZariskiPointPrime.Inst[A]().At(R, U), ring_ideal.PrimeIdealProper))
					b.Show(
						"the constant fraction with denominator one is a section",
						By(
							oneOutside,
							xIn,
							open,
							comm_ring.OneIn.Read(ring),
							ConstantFractionSection.At(R, U, x, b.TermAs[A]("R.one"))))
				})),
			Case(
				"the coefficient map preserves addition",
				Derive(func(b *Argument) {
					x := b.FixAs[A]("x")
					y := b.FixAs[A]("y")
					members := b.Assume()
					pointwise := b.Have(
						"addition is preserved at every point",
						"∀q:set(A). "+
							"    «coefficientSection»(R, U, x + y, q) = "+
							"    structure_add(R, U, «coefficientSection»(R, U, x), «coefficientSection»(R, U, y), q)",
						Derive(func(c *Argument) {
							q := c.FixAs[Set[A]]("q")
							c.Do(Simp(Fwd(StructureAddDef), Fwd(FractionSectionDef)))
							inside := c.Assuming(
								c.TermAs[Bool]("q ∈ U"),
								"both sides are empty outside U",
								Given(func(d *Argument, outside Fact) {
									d.Show(
										"empty values agree",
										By(outside))
								}))
							c.Do(Simp(Fwd(inside)), CondRewrite())
							localMap := c.Have(
								"the coefficient map into the localization at the prime q is a ring homomorphism",
								"ring_homomorphism(R, "+
									"    localized_ring(R, R.carrier ∖ q), "+
									"    λa:A. fraction_class(R.carrier, R.carrier ∖ q, a, R.one))",
								Simp(Fwd(ring_localization.LocalizedRingDef), Rev(ring_localization.ToFractionDef)),
								By(
									inside,
									open,
									ZariskiPointPrime.At(R, U, q),
									local_ring.PrimeComplementMultiplicative.Read(ring).At(q),
									ring_localization.ToFractionHomomorphism.Read(ring).At(c.TermAs[Set[A]]("R.carrier ∖ q"))))
							c.Show(
								"read preservation of addition in that local ring",
								By(
									members,
									localMap,
									ring_localization.LocalizedRingDef.At(R, c.TermAs[Set[A]]("R.carrier ∖ q")),
									ring_homomorphism.MapAdd.Read(localMap).AsFact().At(x, y)))
						}))
					b.Show(
						"the sections are equal pointwise",
						By(pointwise))
				})),
			Case(
				"the coefficient map preserves multiplication",
				Derive(func(b *Argument) {
					x := b.FixAs[A]("x")
					y := b.FixAs[A]("y")
					members := b.Assume()
					pointwise := b.Have(
						"multiplication is preserved at every point",
						"∀q:set(A). "+
							"    «coefficientSection»(R, U, x * y, q) = "+
							"    structure_mul(R, U, «coefficientSection»(R, U, x), «coefficientSection»(R, U, y), q)",
						Derive(func(c *Argument) {
							q := c.FixAs[Set[A]]("q")
							c.Do(Simp(Fwd(StructureMulDef), Fwd(FractionSectionDef)))
							inside := c.Assuming(
								c.TermAs[Bool]("q ∈ U"),
								"both sides are empty outside U",
								Given(func(d *Argument, outside Fact) {
									d.Show(
										"empty values agree",
										By(outside))
								}))
							c.Do(Simp(Fwd(inside)), CondRewrite())
							localMap := c.Have(
								"the coefficient map into the localization at the prime q is a ring homomorphism",
								"ring_homomorphism(R, "+
									"    localized_ring(R, R.carrier ∖ q), "+
									"    λa:A. fraction_class(R.carrier, R.carrier ∖ q, a, R.one))",
								Simp(Fwd(ring_localization.LocalizedRingDef), Rev(ring_localization.ToFractionDef)),
								By(
									inside,
									open,
									ZariskiPointPrime.At(R, U, q),
									local_ring.PrimeComplementMultiplicative.Read(ring).At(q),
									ring_localization.ToFractionHomomorphism.Read(ring).At(c.TermAs[Set[A]]("R.carrier ∖ q"))))
							c.Show(
								"read preservation of multiplication in that local ring",
								By(
									members,
									localMap,
									ring_localization.LocalizedRingDef.At(R, c.TermAs[Set[A]]("R.carrier ∖ q")),
									ring_homomorphism.MapMul.Read(localMap).AsFact().At(x, y)))
						}))
					b.Show(
						"the sections are equal pointwise",
						By(pointwise))
				})),
			Case(
				"the coefficient of one is the one section",
				Unfold(StructureOneDef),
				Unfold(ring_localization.FractionOneDef),
				Unfold(FractionSectionDef)),
		))
	}),
})}

// BasicOpenCoefficientKernel — a coefficient vanishing at every point
// of D(h) is killed by a power of h. Its annihilator is an ideal; if
// that ideal held no power of h, a prime above it missing h would give
// a point where the coefficient does not vanish.
var BasicOpenCoefficientKernel = basicOpenCoefficientKernelThm{family.Add(registry.ProofEntry{
	Name: "BasicOpenCoefficientKernel",
	Key:  "prop_aa382a999ec27483",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀h a:A.",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"h ∈ R.carrier",
			"a ∈ R.carrier",
			"∀p:set(A). " +
				"    p ∈ zariski_open(R, h) ⇒ " +
				"    fraction_class(R.carrier, R.carrier ∖ p, a, R.one) = fraction_zero(R.carrier, R.carrier ∖ p)",
		},
		Conclusion: "∃n:num. monoid_pow(R.mul, R.one, h, n) * a = R.zero",
		Abbrev: Abbrev{
			{Name: "Ann", Text: "{w:A | w ∈ R.carrier ∧ w * a = R.zero}"},
		},
	},
		func(
			arg *Argument,
			R *Expr[RingOps[A]],
			ring comm_ring.CommRingFact[on.R],
			h, a *Member[A, on.R],
			vanishes Fact,
		) {
			annihilator := arg.Have(
				"the annihilator of a is an ideal",
				"ring_ideal(R, «Ann»)",
				BySets(
					ring_ideal.ZeroIdeal.Read(ring),
					a,
					ring_ideal.ColonIdeal.Read(ring).At(arg.TermAs[Set[A]]("{R.zero}"), a)))
			noPowerExists := arg.SupposeNot()
			noPower := arg.Have(
				"the annihilator then holds no power of h",
				"∀n:num. monoid_pow(R.mul, R.one, h, n) ∉ «Ann»",
				BySets(noPowerExists))
			p, above := arg.ObtainAs[Set[A]](
				"a prime above the annihilator misses h",
				"∃p:set(A). prime_ideal(R, p) ∧ «Ann» ⊆ p ∧ h ∉ p",
				By(ring_ideal.PrimeAvoidingPowers.Read(ring), noPower, annihilator, h))
			inBasic := arg.Have(
				"that prime is a point of D(h)",
				"p ∈ zariski_open(R, h)",
				By(above, prime_spectrum.ZariskiOpenMember.Read(ring).At(h, p)))
			outside := arg.Have(
				"vanishing gives an annihilator outside that prime",
				"∃t:A. t ∈ R.carrier ∖ p ∧ t * a = R.zero",
				BySets(
					inBasic,
					vanishes.At(p),
					a,
					above,
					local_ring.PrimeComplementMultiplicative.Read(ring).At(p),
					ring_localization.MultiplicativeSetDef,
					ring_localization.FractionZeroIff.Read(ring).At(
						arg.TermAs[Set[A]]("R.carrier ∖ p"), a, arg.TermAs[A]("R.one"))))
			arg.Show(
				"the prime cannot hold the annihilator and miss one of its members",
				BySets(outside, above))
		}),
})}

// BasicOpenSectionKernel — if a section over D(f) vanishes on its
// intersection with D(h), a power of h kills the section on all of D(f).
// Local fractions give such a power on each basic neighborhood, and
// compactness supplies finitely many neighborhoods whose exponents add
// to an exponent valid on the whole basic open set.
var BasicOpenSectionKernel = basicOpenSectionKernelThm{family.Add(registry.ProofEntry{
	Name: "BasicOpenSectionKernel",
	Key:  "prop_d8be94e76c44ba06",
	Build: family.Sections(Statement{
		Binders: "∀R:ring_ops(A). ∀f h:A. ∀s:(set(A) → set(prod(A, A))).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"f ∈ R.carrier",
			"h ∈ R.carrier",
			"s ∈ structure_sections(R, zariski_open(R, f))",
			"∀q:set(A). " +
				"    q ∈ zariski_open(R, f) ∩ zariski_open(R, h) ⇒ s(q) = fraction_zero(R.carrier, R.carrier ∖ q)",
		},
		Conclusion: "∃n:num. «powerKills»(R, h, s, n, zariski_open(R, f))",
	}, func(ctx *Script, headline string) *GoalStackNode {
		fractionKernel := ctx.Lemma(Statement{
			Binders: "∀R:ring_ops(A). ∀h a b:A.",
			Hypotheses: []string{
				"comm_ring_on(R)", "h ∈ R.carrier", "a ∈ R.carrier", "b ∈ R.carrier",
				"∀p:set(A). " +
					"    p ∈ zariski_open(R, h) ⇒ " +
					"    b ∉ p ∧ " +
					"    fraction_class(R.carrier, R.carrier ∖ p, a, b) = fraction_zero(R.carrier, R.carrier ∖ p)",
			},
			Conclusion: "∃n:num. monoid_pow(R.mul, R.one, h, n) * a = R.zero",
		}, func(
			arg *Argument,
			R *Expr[RingOps[A]],
			ring comm_ring.CommRingFact[on.R],
			h, a, b *Member[A, on.R],
			vanishes Fact,
		) {
			coefficientVanishes := arg.Have(
				"the numerator coefficient vanishes wherever the fraction does",
				Statement{
					Binders:    "∀p:set(A).",
					Hypotheses: []string{"p ∈ zariski_open(R, h)"},
					Conclusion: "fraction_class(R.carrier, R.carrier ∖ p, a, R.one) = " +
						"fraction_zero(R.carrier, R.carrier ∖ p)",
				},
				Derive(func(d *Argument) {
					p := d.FixAs[Set[A]]("p")
					point := d.Assume()
					annihilator := d.Have(
						"a denominator outside p kills the numerator",
						"∃t:A. t ∈ R.carrier ∖ p ∧ t * a = R.zero",
						Derive(func(e *Argument) {
							value := e.Have(
								"the local fraction vanishes and its denominator misses p",
								"b ∉ p ∧ fraction_class(R.carrier, R.carrier ∖ p, a, b) = fraction_zero(R.carrier, R.carrier ∖ p)",
								By(point, vanishes.At(p)))
							denominator := e.Have(
								"the denominator lies in the prime complement",
								"b ∈ R.carrier ∖ p",
								BySets(b, value))
							e.Show(
								"the zero-fraction criterion gives the annihilator",
								By(
									a,
									denominator,
									point,
									value,
									prime_spectrum.ZariskiOpenMember.Read(ring).At(h, p),
									local_ring.PrimeComplementMultiplicative.Read(ring).At(p),
									ring_localization.FractionZeroIff.Read(ring).At(e.TermAs[Set[A]]("R.carrier ∖ p"), a, b)))
						}))
					one := d.Have(
						"one lies in the prime complement",
						"R.one ∈ R.carrier ∖ p",
						BySets(
							comm_ring.OneIn.Read(ring),
							point,
							prime_spectrum.ZariskiOpenMember.Read(ring).At(h, p),
							ring_ideal.PrimeIdealProper))
					d.Show(
						"the same annihilator kills the coefficient fraction",
						By(
							annihilator,
							a,
							one,
							point,
							prime_spectrum.ZariskiOpenMember.Read(ring).At(h, p),
							local_ring.PrimeComplementMultiplicative.Read(ring).At(p),
							ring_localization.FractionZeroIff.Read(ring).At(
								d.TermAs[Set[A]]("R.carrier ∖ p"), a, d.TermAs[A]("R.one"))))
				}))
			arg.Show(
				"a power of h kills the numerator",
				By(ring, coefficientVanishes, a, h, BasicOpenCoefficientKernel.At(R, h, a)))
		})

		clearLocalFraction := ctx.Lemma(Statement{
			Binders: "∀R:ring_ops(A). ∀h g a b:A. ∀n:num. ∀p:set(A).",
			Hypotheses: []string{
				"comm_ring_on(R)", "h ∈ R.carrier", "g ∈ R.carrier", "a ∈ R.carrier", "b ∈ R.carrier",
				"prime_ideal(R, p)", "g ∉ p", "b ∉ p", "monoid_pow(R.mul, R.one, h * g, n) * a = R.zero",
			},
			Conclusion: "fraction_mul(R.carrier, " +
				"    R.carrier ∖ p, " +
				"    fraction_class(R.carrier, R.carrier ∖ p, monoid_pow(R.mul, R.one, h, n), R.one), " +
				"    fraction_class(R.carrier, R.carrier ∖ p, a, b)) = " +
				"fraction_zero(R.carrier, R.carrier ∖ p)",
		}, func(
			arg *Argument,
			R *Expr[RingOps[A]],
			ring comm_ring.CommRingFact[on.R],
			h, g, a, b *Member[A, on.R],
			n *Expr[Nat],
			p *Expr[Set[A]],
			hypotheses Fact,
		) {
			parts := arg.Conjuncts(
				hypotheses,
				"p is prime",
				"g misses p",
				"b misses p",
				"the product power kills a")
			prime, gOutside, bOutside, productKills := parts[0], parts[1], parts[2], parts[3]
			denominators := arg.Have(
				"the prime complement supplies the fraction denominators",
				"multiplicative_set(R.carrier, R.carrier ∖ p) ∧ R.one ∈ R.carrier ∖ p ∧ b ∈ R.carrier ∖ p",
				BySets(
					comm_ring.OneIn.Read(ring),
					bOutside,
					prime,
					b,
					ring_ideal.PrimeIdealProper,
					local_ring.PrimeComplementMultiplicative.Read(ring).At(p)))
			powers := arg.Have(
				"the h power lies in R and the g power misses p",
				"monoid_pow(R.mul, R.one, h, n) ∈ R.carrier ∧ monoid_pow(R.mul, R.one, g, n) ∈ R.carrier ∖ p",
				BySets(
					gOutside,
					prime,
					g,
					h,
					comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(ring)).At(h, n),
					comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(ring)).At(g, n),
					ring_ideal.PrimeIdealPow.Read(ring).At(p, g, n)))
			annihilates := arg.Have(
				"multiplying (hg)ⁿ = hⁿgⁿ by a gives gⁿ(hⁿa) = (hg)ⁿa, which is zero",
				"monoid_pow(R.mul, R.one, g, n) * (monoid_pow(R.mul, R.one, h, n) * a) = R.zero",
				ByArith(
					comm_ring.MulIn.Read(ring),
					productKills,
					a,
					g,
					h,
					powers,
					Scaled(a, comm_monoid.MulPowOn.Read(comm_ring.MulMonoidOn.Read(ring)).At(h, g, n)),
					comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(ring)).At(g, n),
					comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(ring)).AsFact().At(arg.TermAs[A]("h * g"), n)))
			arg.Show(
				"the g power is a denominator witnessing vanishing of the multiplied fraction",
				Simp(
					Fwd(ring_localization.FractionMulClass.Read(ring)),
					Fwd(comm_monoid.LeftIdentityOn.Read(comm_ring.MulMonoidOn.Read(ring))),
					Fwd(denominators)),
				Simp(
					Fwd(ring_localization.FractionZeroIff.Read(ring)),
					Fwd(comm_ring.MulIn.Read(ring)),
					Fwd(denominators)),
				Witness(arg.TermAs[A]("monoid_pow(R.mul, R.one, g, n)")),
				By(annihilates, powers))
		})

		localPower := ctx.Lemma(Statement{
			Binders: "∀R:ring_ops(A). ∀f h:A. ∀s:(set(A) → set(prod(A, A))). ∀p:set(A).",
			Hypotheses: []string{
				"comm_ring_on(R)", "f ∈ R.carrier", "h ∈ R.carrier",
				"s ∈ structure_sections(R, zariski_open(R, f))",
				"∀q:set(A). " +
					"    q ∈ zariski_open(R, f) ∩ zariski_open(R, h) ⇒ s(q) = fraction_zero(R.carrier, R.carrier ∖ q)",
				"p ∈ zariski_open(R, f)",
			},
			Conclusion: "∃g:A. ∃n:num. " +
				"    g ∈ R.carrier ∧ " +
				"    p ∈ zariski_open(R, g) ∧ " +
				"    zariski_open(R, g) ⊆ zariski_open(R, f) ∧ " +
				"    «powerKills»(R, h, s, n, zariski_open(R, g))",
		}, func(
			arg *Argument,
			R *Expr[RingOps[A]],
			ring comm_ring.CommRingFact[on.R],
			f, h *Member[A, on.R],
			s *Arrow[Set[A], Set[Prod[A, A]]],
			section Fact,
			vanishes Fact,
			p *Expr[Set[A]],
			point Fact,
		) {
			_, a, b, representation := arg.Obtain3As[Set[Set[A]], A, A](
				"choose a fraction representing s near p",
				"∃V:set(set(A)). ∃a b:A. "+
					"    V ∈ zariski_topology(R) ∧ "+
					"    p ∈ V ∧ "+
					"    V ⊆ zariski_open(R, f) ∧ "+
					"    a ∈ R.carrier ∧ "+
					"    b ∈ R.carrier ∧ "+
					"    (∀q:set(A). q ∈ V ⇒ b ∉ q ∧ s(q) = fraction_class(R.carrier, R.carrier ∖ q, a, b))",
				BySets(point, arg.Unfolded(arg.Unfolded(section, StructureSectionsDef), LocallyFractionDef)))
			local := arg.Conjuncts(
				representation,
				"V is open",
				"p lies in V",
				"V lies in D(f)",
				"a lies in R",
				"b lies in R",
				"the fraction represents s on V")
			g, basic := arg.ObtainAs[A](
				"refine that neighborhood to a basic open set",
				"∃g:A. g ∈ R.carrier ∧ p ∈ zariski_open(R, g) ∧ zariski_open(R, g) ⊆ V",
				By(prime_spectrum.ZariskiOpenBase.Read(ring), representation))
			overlap := arg.Have(
				"the local fraction vanishes on D(hg)",
				Statement{
					Binders:    "∀q:set(A).",
					Hypotheses: []string{"q ∈ zariski_open(R, h * g)"},
					Conclusion: "b ∉ q ∧ " +
						"fraction_class(R.carrier, R.carrier ∖ q, a, b) = fraction_zero(R.carrier, R.carrier ∖ q)",
				},
				Derive(func(d *Argument) {
					q := d.FixAs[Set[A]]("q")
					inside := d.Assume()
					near := d.Have(
						"a point of D(hg) lies in the fraction neighborhood and the vanishing locus",
						"q ∈ V ∧ q ∈ zariski_open(R, f) ∩ zariski_open(R, h)",
						BySets(h, inside, local[2], basic, prime_spectrum.ZariskiOpenMul.Read(ring).AsFact().At(h, g)))
					d.Show(
						"the representation is zero there",
						By(near, local[5].At(q), vanishes.At(q)))
				}))
			n, killsNumerator := arg.ObtainAs[Nat](
				"a power of hg kills the local numerator",
				"∃n:num. monoid_pow(R.mul, R.one, h * g, n) * a = R.zero",
				By(
					comm_ring.MulIn.Read(ring),
					overlap,
					h,
					basic,
					representation,
					At(fractionKernel, R, arg.TermAs[A]("h * g"), a, b)))
			killsNearby := arg.Have(
				"the corresponding h power kills s on D(g)",
				Statement{
					Binders:    "∀q:set(A).",
					Hypotheses: []string{"q ∈ zariski_open(R, g)"},
					Conclusion: "fraction_mul(R.carrier, " +
						"    R.carrier ∖ q, " +
						"    fraction_class(R.carrier, R.carrier ∖ q, monoid_pow(R.mul, R.one, h, n), R.one), " +
						"    s(q)) = " +
						"fraction_zero(R.carrier, R.carrier ∖ q)",
				},
				Derive(func(d *Argument) {
					q := d.FixAs[Set[A]]("q")
					inside := d.Assume()
					near := d.Have(
						"q lies in V and its prime misses g",
						"q ∈ V ∧ prime_ideal(R, q) ∧ g ∉ q",
						BySets(inside, basic, prime_spectrum.ZariskiOpenMember.Read(ring).At(g, q)))
					value := d.Have(
						"read the local fraction at q",
						"b ∉ q ∧ s(q) = fraction_class(R.carrier, R.carrier ∖ q, a, b)",
						By(near, local[5].At(q)))
					d.Show(
						"the local clearing calculation kills this fraction",
						Simp(Fwd(value)),
						By(
							ring,
							killsNumerator,
							local[3],
							local[4],
							h,
							value,
							basic,
							near,
							At(clearLocalFraction, R, h, g, a, b, n, q)))
				}))
			arg.Take(g)
			arg.Take(n)
			arg.Show(
				"the basic neighborhood and exponent have the required properties",
				BySets(killsNearby, basic, representation))
		})

		powerPersists := ctx.Lemma(Statement{
			Binders: "∀R:ring_ops(A). ∀L:ring_ops(B). ∀ι:(A → B). ∀h:A. ∀x:B. ∀n m:num.",
			Hypotheses: []string{
				"ring_homomorphism(R, L, ι)",
				"h ∈ R.carrier",
				"x ∈ L.carrier",
				"L.mul(ι(monoid_pow(R.mul, R.one, h, n)), x) = L.zero",
			},
			Conclusion: "L.mul(ι(monoid_pow(R.mul, R.one, h, n + m)), x) = L.zero",
		}, func(
			arg *Argument,
			R *Expr[RingOps[A]],
			L *Expr[RingOps[B]],
			ι *Arrow[A, B],
			hom Fact,
			h *Expr[A],
			hIn Fact,
			x *Expr[B],
			xIn Fact,
			n, m *Expr[Nat],
			kills Fact,
		) {
			multiplicative := comm_ring.MulMonoidOn.Read(ring_homomorphism.Source.Read(hom))
			arg.Do(Simp(
				Fwd(comm_monoid.PowAddOn.Read(multiplicative)),
				Fwd(comm_monoid.PowIn.Read(multiplicative)),
				Fwd(ring_homomorphism.MapMul.Read(hom))))
			images := arg.Have(
				"both powers map into the target carrier",
				"ι(monoid_pow(R.mul, R.one, h, n)) ∈ L.carrier ∧ ι(monoid_pow(R.mul, R.one, h, m)) ∈ L.carrier",
				By(
					ring_homomorphism.MapIn.Read(hom),
					hIn,
					comm_monoid.PowIn.Read(multiplicative).AsFact().At(h, n),
					comm_monoid.PowIn.Read(multiplicative).AsFact().At(h, m)))
			arg.Show(
				"multiplying the annihilating equation by the image of the other power still gives zero",
				ByArith(
					ring_homomorphism.Target.Read(hom),
					Scaled(arg.TermAs[B]("ι(monoid_pow(R.mul, R.one, h, m))"), kills),
					xIn,
					images))
		})

		finiteUniform := ctx.Lemma(Statement{
			Binders: "∀P:(num → A → bool). ∀E:set(A).",
			Hypotheses: []string{
				"finite(E)",
				"∀x:A. x ∈ E ⇒ ∃n:num. P(n, x)",
				"∀x:A. ∀n m:num. P(n, x) ⇒ P(n + m, x)",
			},
			Conclusion: "∃N:num. ∀x:A. x ∈ E ⇒ P(N, x)",
		}, func(arg *Argument, P *Arrow2[Nat, A, Bool], E *Expr[Set[A]], hypotheses Fact) {
			parts := arg.Conjuncts(
				hypotheses,
				"E is finite",
				"each member has an exponent",
				"adding an exponent preserves the property")
			finiteE, each, persists := parts[0], parts[1], parts[2]
			arg.Show(
				"one exponent works for the finite family",
				ByInduction(finite_set.FiniteInduct, finiteE, Generalizing(each),
					Case(
						"the empty family needs no positive exponent",
						Derive(func(d *Argument) {
							d.Assume()
							d.Take(d.TermAs[Nat]("0"))
							d.Show(
								"every member of the empty family has the property",
								BySets())
						})),
					Case(
						"add the new member's exponent to the exponent for the old family",
						Derive(func(d *Argument) {
							x := d.FixAs[A]("x")
							d.FixAs[Set[A]]("t")
							ih := d.Assume()
							available := d.Assume()
							N, old := d.ObtainAs[Nat](
								"choose an exponent for the old members",
								"∃N:num. ∀y:A. y ∈ t ⇒ P(N, y)",
								BySets(available, ih))
							m, newMember := d.ObtainAs[Nat](
								"choose an exponent for the inserted member",
								"∃m:num. P(m, x)",
								BySets(available.At(x)))
							d.Take(d.TermAs[Nat]("N + m"))
							y := d.FixAs[A]("y")
							member := d.Assume()
							d.Show(
								"the sum of exponents works for either an old member or the inserted member",
								BySets(
									persists.At(y, N, m),
									persists.At(x, m, N),
									old.At(y),
									newMember,
									member,
									nat_arith.AddSym.At(N, m)))
						}))))
		})

		return ctx.Theorem(headline, func(
			arg *Argument,
			R *Expr[RingOps[A]],
			ring comm_ring.CommRingFact[on.R],
			f, h *Member[A, on.R],
			s *Arrow[Set[A], Set[Prod[A, A]]],
			section Fact,
			vanishes Fact,
		) {
			_, coverDef := arg.LetAs[Set[Set[Set[A]]]](
				"C",
				"{V:set(set(A)) | "+
					"    V ∈ zariski_topology(R) ∧ ∃n:num. «powerKills»(R, h, s, n, V ∩ zariski_open(R, f))}")
			inCover := arg.Have(
				"the cover consists of open neighborhoods with an annihilating exponent",
				"∀V:set(set(A)). "+
					"    V ∈ C ⇔ V ∈ zariski_topology(R) ∧ ∃n:num. «powerKills»(R, h, s, n, V ∩ zariski_open(R, f))",
				BySets(coverDef))
			openCover := arg.Have(
				"all members of C are open",
				"C ⊆ zariski_topology(R)",
				BySets(inCover))
			nearby := arg.Have(
				"each point lies in a basic member of C",
				"∀p:set(A). p ∈ zariski_open(R, f) ⇒ ∃g:A. p ∈ zariski_open(R, g) ∧ zariski_open(R, g) ∈ C",
				Derive(func(d *Argument) {
					p := d.FixAs[Set[A]]("p")
					point := d.Assume()
					g, n, near := d.Obtain2As[A, Nat](
						"a power kills the section on a basic neighborhood of p",
						"∃g:A. ∃n:num. "+
							"    g ∈ R.carrier ∧ "+
							"    p ∈ zariski_open(R, g) ∧ "+
							"    zariski_open(R, g) ⊆ zariski_open(R, f) ∧ "+
							"    «powerKills»(R, h, s, n, zariski_open(R, g))",
						By(ring, vanishes, f, h, point, section, At(localPower, R, f, h, s, p)))
					d.Take(g)
					restricted := d.Have(
						"the same exponent works after intersecting with D(f)",
						"∃m:num. «powerKills»(R, h, s, m, zariski_open(R, g) ∩ zariski_open(R, f))",
						Derive(func(e *Argument) {
							e.Take(n)
							e.FixAs[Set[A]]("q")
							e.Show(
								"the smaller neighborhood inherits vanishing",
								BySets(e.Assume(), near))
						}))
					d.Show(
						"that neighborhood belongs to C",
						By(
							inCover.At(d.TermAs[Set[Set[A]]]("zariski_open(R, g)")),
							restricted,
							near,
							prime_spectrum.ZariskiOpenOpen.Read(ring).AsFact().At(g)))
				}))
			covers := arg.Have(
				"C covers the basic open set",
				"zariski_open(R, f) ⊆ ⋃C",
				BySets(nearby))
			D, finiteCover := arg.ObtainAs[Set[Set[Set[A]]]](
				"compactness selects finitely many neighborhoods",
				"∃D:set(set(set(A))). D ⊆ C ∧ finite(D) ∧ zariski_open(R, f) ⊆ ⋃D",
				By(
					f,
					covers,
					openCover,
					prime_spectrum.ZariskiOpenCompact.Read(ring).At(f),
					compact.CompactInDef.Inst[Set[A]]().At(
						arg.TermAs[Set[Set[Set[A]]]]("zariski_topology(R)"),
						arg.TermAs[Set[Set[A]]]("zariski_open(R, f)"))))
			persists := arg.Have(
				"adding an exponent preserves vanishing on each neighborhood",
				Statement{
					Binders:    "∀V:set(set(A)). ∀n m:num.",
					Hypotheses: []string{"«powerKills»(R, h, s, n, V ∩ zariski_open(R, f))"},
					Conclusion: "«powerKills»(R, h, s, n + m, V ∩ zariski_open(R, f))",
				},
				Derive(func(d *Argument) {
					d.FixAs[Set[Set[A]]]("V")
					n := d.FixAs[Nat]("n")
					m := d.FixAs[Nat]("m")
					killed := d.Assume()
					q := d.FixAs[Set[A]]("q")
					inside := d.Assume()
					value := d.Have(
						"q is prime and the section value is a local fraction",
						"prime_ideal(R, q) ∧ s(q) ∈ ring_localization(R.mul, R.carrier, R.carrier ∖ q)",
						BySets(
							inside,
							section,
							prime_spectrum.ZariskiOpenMember.Read(ring).At(f, q),
							StructureSectionValue.At(R, d.TermAs[Set[Set[A]]]("zariski_open(R, f)"), s, q)))
					coefficients := d.Have(
						"the coefficient map into the localization at the prime q is a ring homomorphism",
						"ring_homomorphism(R, "+
							"    localized_ring(R, R.carrier ∖ q), "+
							"    λa:A. fraction_class(R.carrier, R.carrier ∖ q, a, R.one))",
						Simp(Fwd(ring_localization.LocalizedRingDef), Rev(ring_localization.ToFractionDef)),
						By(
							value,
							local_ring.PrimeComplementMultiplicative.Read(ring).At(q),
							ring_localization.ToFractionHomomorphism.Read(ring).At(d.TermAs[Set[A]]("R.carrier ∖ q"))))
					d.Show(
						"the local power-persistence law applies to the section value",
						By(
							h,
							inside,
							killed.At(q),
							value,
							coefficients,
							ring_localization.LocalizedRingDef.At(R, d.TermAs[Set[A]]("R.carrier ∖ q")),
							At(
								powerPersists,
								R,
								d.TermAs[RingOps[Set[Prod[A, A]]]]("localized_ring(R, R.carrier ∖ q)"),
								d.TermAs[Fun[A, Set[Prod[A, A]]]]("λa:A. fraction_class(R.carrier, R.carrier ∖ q, a, R.one)"),
								h,
								s.Apply(q),
								n,
								m)))
				}))
			each := arg.Have(
				"each selected neighborhood has an exponent",
				"∀V:set(set(A)). V ∈ D ⇒ ∃n:num. «powerKills»(R, h, s, n, V ∩ zariski_open(R, f))",
				BySets(inCover, finiteCover))
			N, uniform := arg.ObtainAs[Nat](
				"one exponent works on the finite subcover",
				"∃N:num. ∀V:set(set(A)). V ∈ D ⇒ «powerKills»(R, h, s, N, V ∩ zariski_open(R, f))",
				By(
					persists,
					each,
					finiteCover,
					At(
						finiteUniform,
						arg.TermAs[Fun2[Nat, Set[Set[A]], Bool]](
							"λn:num. λV:set(set(A)). «powerKills»(R, h, s, n, V ∩ zariski_open(R, f))"),
						D)))
			arg.Take(N)
			arg.Show(
				"the selected neighborhoods cover every point of D(f)",
				BySets(uniform, finiteCover))
		})
	}),
})}

// BasicOpenSectionRepresentation — a power of f times a section on D(f)
// is a coefficient section. The coefficients which clear the section form
// an ideal. At a prime p of D(f) the section is a fraction a/b on some
// D(g) around p; its error b·s − a vanishes there, so it is annihilated by
// a power of g, and gⁿb is a clearing coefficient outside p. An ideal that
// holds no power of f lies in a prime missing f, a point of D(f); so some
// power of f clears the section.
var BasicOpenSectionRepresentation = basicOpenSectionRepresentationThm{family.Add(registry.ProofEntry{
	Name: "BasicOpenSectionRepresentation",
	Key:  "prop_8d7a8772c1fe197f",
	Build: family.Sections(Statement{
		Binders: "∀R:ring_ops(A). ∀f:A. ∀s:(set(A) → set(prod(A, A))).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"f ∈ R.carrier",
			"s ∈ structure_sections(R, zariski_open(R, f))",
		},
		Conclusion: "∃n:num. ∃a:A. " +
			"    a ∈ R.carrier ∧ " +
			"    spec_section_ops(R, zariski_open(R, f)).mul( " +
			"        «coefficientSection»(R, zariski_open(R, f), monoid_pow(R.mul, R.one, f, n)), s) = " +
			"    «coefficientSection»(R, zariski_open(R, f), a)",
		Abbrev: Abbrev{
			{Name: "clearingIdeal", Text: "λR:ring_ops(A). λL:ring_ops(B). λι:(A → B). λx:B. " +
				"    {r:A | r ∈ R.carrier ∧ ∃a:A. a ∈ R.carrier ∧ L.mul(ι(r), x) = ι(a)}"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		clearingIdeal := ctx.Lemma(Statement{
			Binders:    "∀R:ring_ops(A). ∀L:ring_ops(B). ∀ι:(A → B). ∀x:B.",
			Hypotheses: []string{"ring_homomorphism(R, L, ι)", "x ∈ L.carrier"},
			Conclusion: "ring_ideal(R, «clearingIdeal»(R, L, ι, x))",
		}, func(
			arg *Argument,
			R *Expr[RingOps[A]],
			L *Expr[RingOps[B]],
			ι *Arrow[A, B],
			hom Fact,
			x *Expr[B],
			xIn Fact,
		) {
			source := ring_homomorphism.Source.Read(hom)
			target := ring_homomorphism.Target.Read(hom)
			arg.Do(Simp(Fwd(ring_ideal.RingIdealDef)), SplitConjAll(
				Case(
					"clearing coefficients lie in R",
					BySets()),
				Case(
					"zero clears the section",
					BySets(
						comm_ring.ZeroIn.Read(source),
						ring_homomorphism.MapZero.Read(hom),
						comm_ring.MulLeftZeroOn.Read(target),
						xIn)),
				Case(
					"sums of clearing coefficients clear the section",
					Derive(func(d *Argument) {
						d.FixAs[A]("u")
						d.FixAs[A]("v")
						members := d.Assume()
						_, _, witnesses := d.Obtain2As[A, A](
							"choose the two cleared numerators",
							"∃a b:A. "+
								"    u ∈ R.carrier ∧ "+
								"    v ∈ R.carrier ∧ "+
								"    a ∈ R.carrier ∧ "+
								"    b ∈ R.carrier ∧ "+
								"    L.mul(ι(u), x) = ι(a) ∧ "+
								"    L.mul(ι(v), x) = ι(b)",
							BySets(members))
						images := d.Have(
							"the four coefficient images lie in L",
							"ι(u) ∈ L.carrier ∧ ι(v) ∈ L.carrier ∧ ι(a) ∈ L.carrier ∧ ι(b) ∈ L.carrier",
							By(ring_homomorphism.MapIn.Read(hom), witnesses))
						sum := d.Have(
							"addition adds the cleared numerators",
							"L.mul(ι(R.add(u, v)), x) = ι(R.add(a, b))",
							Simp(Fwd(ring_homomorphism.MapAdd.Read(hom))),
							ByArith(target, xIn, images, witnesses))
						d.Show(
							"the sum is a clearing coefficient",
							BySets(comm_ring.AddIn.Read(source), sum, witnesses))
					})),
				Case(
					"multiples of clearing coefficients clear the section",
					Derive(func(d *Argument) {
						r := d.FixAs[A]("r")
						d.FixAs[A]("u")
						members := d.Assume()
						_, witness := d.ObtainAs[A](
							"choose a cleared numerator",
							"∃a:A. r ∈ R.carrier ∧ u ∈ R.carrier ∧ a ∈ R.carrier ∧ L.mul(ι(u), x) = ι(a)",
							BySets(members))
						images := d.Have(
							"the three coefficient images lie in L",
							"ι(r) ∈ L.carrier ∧ ι(u) ∈ L.carrier ∧ ι(a) ∈ L.carrier",
							By(ring_homomorphism.MapIn.Read(hom), witness))
						parts := d.Conjuncts(
							witness,
							"r lies in R",
							"u lies in R",
							"a lies in R",
							"u clears x to a")
						product := d.Have(
							"ι(r) times ι(u)·x = ι(a): r·u clears x to r·a",
							"L.mul(ι(R.mul(r, u)), x) = ι(R.mul(r, a))",
							Simp(Fwd(ring_homomorphism.MapMul.Read(hom))),
							ByArith(target, Scaled(ι.Apply(r), parts[3]), xIn, images))
						d.Show(
							"the multiple is a clearing coefficient",
							BySets(comm_ring.MulIn.Read(source), product, witness))
					}))))
		})
		clearError := ctx.Lemma(Statement{
			Binders: "∀R:ring_ops(A). ∀L:ring_ops(B). ∀ι:(A → B). ∀h a b:A. ∀x:B.",
			Hypotheses: []string{
				"ring_homomorphism(R, L, ι)",
				"h ∈ R.carrier",
				"a ∈ R.carrier",
				"b ∈ R.carrier",
				"x ∈ L.carrier",
				"L.mul(ι(h), L.sub(L.mul(ι(b), x), ι(a))) = L.zero",
			},
			Conclusion: "L.mul(ι(R.mul(h, b)), x) = ι(R.mul(h, a))",
		}, func(
			arg *Argument,
			R *Expr[RingOps[A]],
			L *Expr[RingOps[B]],
			ι *Arrow[A, B],
			hom Fact,
			h *Expr[A],
			hIn Fact,
			a *Expr[A],
			aIn Fact,
			b *Expr[A],
			bIn Fact,
			x *Expr[B],
			xIn, killed Fact,
		) {
			arg.Do(Simp(Fwd(ring_homomorphism.MapMul.Read(hom))))
			images := arg.Have(
				"all three coefficient images lie in L",
				"ι(h) ∈ L.carrier ∧ ι(a) ∈ L.carrier ∧ ι(b) ∈ L.carrier",
				By(
					aIn,
					bIn,
					hIn,
					At(ring_homomorphism.MapIn.Read(hom), a),
					At(ring_homomorphism.MapIn.Read(hom), b),
					At(ring_homomorphism.MapIn.Read(hom), h)))
			arg.Show(
				"annihilating the error gives a cleared numerator",
				ByArith(ring_homomorphism.Target.Read(hom), killed, xIn, images))
		})
		localClearing := ctx.Lemma(Statement{
			Binders: "∀R:ring_ops(A). ∀f:A. ∀s:(set(A) → set(prod(A, A))). ∀p:set(A).",
			Hypotheses: []string{
				"comm_ring_on(R)",
				"f ∈ R.carrier",
				"s ∈ structure_sections(R, zariski_open(R, f))",
				"p ∈ zariski_open(R, f)",
			},
			Conclusion: "∃r:A. " +
				"    r ∈ " +
				"    «clearingIdeal»(R, " +
				"        spec_section_ops(R, zariski_open(R, f)), " +
				"        «coefficientSection»(R, zariski_open(R, f)), " +
				"        s) ∧ " +
				"    r ∉ p",
		}, func(
			arg *Argument,
			R *Expr[RingOps[A]],
			ring comm_ring.CommRingFact[on.R],
			f *Member[A, on.R],
			s *Arrow[Set[A], Set[Prod[A, A]]],
			section Fact,
			p *Expr[Set[A]],
			point Fact,
		) {
			U := arg.TermAs[Set[Set[A]]]("zariski_open(R, f)")
			hom := arg.Have(
				"coefficients map into the section ring",
				"ring_homomorphism(R, "+
					"    spec_section_ops(R, zariski_open(R, f)), "+
					"    «coefficientSection»(R, zariski_open(R, f)))",
				By(f, prime_spectrum.ZariskiOpenOpen.Read(ring).At(f), CoefficientSectionHomomorphism.At(R, U)))
			V, a, b, representation := arg.Obtain3As[Set[Set[A]], A, A](
				"choose a local fraction for s at p",
				"∃V:set(set(A)). ∃a b:A. "+
					"    V ∈ zariski_topology(R) ∧ "+
					"    p ∈ V ∧ "+
					"    V ⊆ zariski_open(R, f) ∧ "+
					"    a ∈ R.carrier ∧ "+
					"    b ∈ R.carrier ∧ "+
					"    (∀q:set(A). q ∈ V ⇒ b ∉ q ∧ s(q) = fraction_class(R.carrier, R.carrier ∖ q, a, b))",
				BySets(point, arg.Unfolded(arg.Unfolded(section, StructureSectionsDef), LocallyFractionDef)))
			g, basic := arg.ObtainAs[A](
				"refine the fraction neighborhood to D(g)",
				"∃g:A. g ∈ R.carrier ∧ p ∈ zariski_open(R, g) ∧ zariski_open(R, g) ⊆ V",
				BySets(representation, At(prime_spectrum.ZariskiOpenBase.Read(ring), V, p)))
			e, errorDef := arg.LetAs[_Section](
				"e",
				"spec_section_ops(R, zariski_open(R, f)).sub(spec_section_ops(R, zariski_open(R, f)).mul( "+
					"        «coefficientSection»(R, zariski_open(R, f), b), s), "+
					"    «coefficientSection»(R, zariski_open(R, f), a))")
			local := arg.Conjuncts(
				representation,
				"V is open",
				"p lies in V",
				"V lies in D(f)",
				"a lies in R",
				"b lies in R",
				"the fraction represents s on V")
			errorIn := arg.Have(
				"the error is a section",
				"e ∈ structure_sections(R, zariski_open(R, f))",
				Simp(Fwd(errorDef)),
				By(
					local[3],
					local[4],
					section,
					At(ring_homomorphism.MapIn.Read(hom), a),
					At(ring_homomorphism.MapIn.Read(hom), b),
					At(
						comm_ring.MulIn.Read(ring_homomorphism.Target.Read(hom)),
						arg.TermAs[_Section]("«coefficientSection»(R, zariski_open(R, f), b)"),
						s),
					At(
						comm_ring.SubIn.Read(ring_homomorphism.Target.Read(hom)),
						arg.TermAs[_Section](
							"spec_section_ops(R, zariski_open(R, f)).mul(«coefficientSection»(R, zariski_open(R, f), b), s)"),
						arg.TermAs[_Section]("«coefficientSection»(R, zariski_open(R, f), a)"))))
			vanishes := arg.Have(
				"the error vanishes on D(g)",
				Statement{
					Binders:    "∀q:set(A).",
					Hypotheses: []string{"q ∈ zariski_open(R, f) ∩ zariski_open(R, g)"},
					Conclusion: "e(q) = fraction_zero(R.carrier, R.carrier ∖ q)",
				},
				Derive(func(d *Argument) {
					q := d.FixAs[Set[A]]("q")
					inside := d.Assume()
					value := d.Have(
						"the local fraction is valid at q",
						"q ∈ zariski_open(R, f) ∧ "+
							"prime_ideal(R, q) ∧ "+
							"b ∉ q ∧ "+
							"s(q) = fraction_class(R.carrier, R.carrier ∖ q, a, b)",
						BySets(local[5].At(q), inside, basic, f, prime_spectrum.ZariskiOpenMember.Read(ring).At(f, q)))
					atQ := d.Conjuncts(
						value,
						"q lies in D(f)",
						"q is prime",
						"b avoids q",
						"the fraction equals the section value")
					complement := d.Have(
						"the complement of the prime q is a multiplicative set holding b",
						"multiplicative_set(R.carrier, R.carrier ∖ q) ∧ b ∈ R.carrier ∖ q",
						BySets(atQ[1], atQ[2], local[4], local_ring.PrimeComplementMultiplicative.Read(ring).At(q)))
					localHom := d.Have(
						"the coefficient map into the localization at the prime q is a ring homomorphism",
						"ring_homomorphism(R, "+
							"    localized_ring(R, R.carrier ∖ q), "+
							"    λa:A. fraction_class(R.carrier, R.carrier ∖ q, a, R.one))",
						Simp(Fwd(ring_localization.LocalizedRingDef), Rev(ring_localization.ToFractionDef)),
						By(
							complement,
							ring_localization.ToFractionHomomorphism.Read(ring).At(d.TermAs[Set[A]]("R.carrier ∖ q"))))
					d.Show(
						"the local error vanishes",
						CalcEq(
							Leg(
								d.TermAs[Set[Prod[A, A]]](
									"fraction_sub(R.carrier, "+
										"    R.carrier ∖ q, "+
										"    fraction_mul(R.carrier, "+
										"        R.carrier ∖ q, "+
										"        fraction_class(R.carrier, R.carrier ∖ q, b, R.one), "+
										"        fraction_class(R.carrier, R.carrier ∖ q, a, b)), "+
										"    fraction_class(R.carrier, R.carrier ∖ q, a, R.one))"),
								"at q in D(f) the error is b / 1 times s(q) = a / b, less a / 1",
								Simp(
									Fwd(errorDef),
									Fwd(StructureSubDef),
									Fwd(StructureMulDef),
									Fwd(FractionSectionDef),
									Fwd(atQ[0]),
									Fwd(atQ[3])),
								CondRewrite(),
								Basic()),
							Leg(
								d.TermAs[Set[Prod[A, A]]](
									"fraction_sub(R.carrier, "+
										"    R.carrier ∖ q, "+
										"    fraction_class(R.carrier, R.carrier ∖ q, a, R.one), "+
										"    fraction_class(R.carrier, R.carrier ∖ q, a, R.one))"),
								"b / 1 times a / b is a / 1",
								Simp(Fwd(ring_localization.DenominatorClearsFraction.Read(ring))),
								Refl()),
							FinalLeg(
								"a / 1 less itself is zero",
								ByArith(
									ring_homomorphism.Target.Read(localHom),
									local[3],
									At(ring_homomorphism.MapIn.Read(localHom), a)))))
				}))
			n, killed := arg.ObtainAs[Nat](
				"a power of g kills the error globally",
				"∃n:num. «powerKills»(R, g, e, n, zariski_open(R, f))",
				By(ring, vanishes, f, errorIn, basic, BasicOpenSectionKernel.At(R, f, g, e)))
			annihilates := arg.Have(
				"the error is annihilated in the section ring",
				"spec_section_ops(R, zariski_open(R, f)).mul( "+
					"    «coefficientSection»(R, zariski_open(R, f), monoid_pow(R.mul, R.one, g, n)), e) = "+
					"spec_section_ops(R, zariski_open(R, f)).zero",
				Simp(Fwd(StructureMulDef), Fwd(StructureZeroDef), Fwd(FractionSectionDef)),
				BySets(killed))
			guards := arg.Have(
				"the power lies in R, and g and b avoid p",
				"monoid_pow(R.mul, R.one, g, n) ∈ R.carrier ∧ prime_ideal(R, p) ∧ g ∉ p ∧ b ∉ p",
				By(
					local[5].At(p),
					local[1],
					basic,
					prime_spectrum.ZariskiOpenMember.Read(ring).At(g, p),
					At(comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(ring)), g, n)))
			sectionRing := arg.TermAs[RingOps[_Section]]("spec_section_ops(R, zariski_open(R, f))")
			coefficients := arg.TermAs[Fun[A, _Section]]("«coefficientSection»(R, zariski_open(R, f))")
			cleared := arg.Have(
				"g to the n times b clears s to g to the n times a",
				"spec_section_ops(R, zariski_open(R, f)).mul( "+
					"    «coefficientSection»(R, zariski_open(R, f), R.mul(monoid_pow(R.mul, R.one, g, n), b)), s) = "+
					"«coefficientSection»(R, zariski_open(R, f), R.mul(monoid_pow(R.mul, R.one, g, n), a))",
				By(
					arg.Simplified(annihilates, Fwd(errorDef)),
					local[3],
					local[4],
					section,
					guards,
					hom,
					At(
						clearError,
						R,
						sectionRing,
						coefficients,
						arg.TermAs[A]("monoid_pow(R.mul, R.one, g, n)"),
						a,
						b,
						s)))
			coefficientIn := arg.Have(
				"the clearing coefficient lies in R",
				"R.mul(monoid_pow(R.mul, R.one, g, n), b) ∈ R.carrier",
				By(
					local[4],
					guards,
					comm_ring.MulIn.Read(ring).AsFact().At(arg.TermAs[A]("monoid_pow(R.mul, R.one, g, n)"), b)))
			numeratorIn := arg.Have(
				"the cleared numerator lies in R",
				"R.mul(monoid_pow(R.mul, R.one, g, n), a) ∈ R.carrier",
				By(
					local[3],
					guards,
					comm_ring.MulIn.Read(ring).AsFact().At(arg.TermAs[A]("monoid_pow(R.mul, R.one, g, n)"), a)))
			arg.Take(arg.TermAs[A]("R.mul(monoid_pow(R.mul, R.one, g, n), b)"))
			arg.Do(SplitConj(
				Case(
					"this coefficient clears s",
					BySets(cleared, coefficientIn, numeratorIn)),
				Case(
					"this coefficient avoids p",
					By(
						local[4],
						basic,
						guards,
						At(ring_ideal.PrimeIdealPow.Read(ring), p, g, n),
						ring_ideal.PrimeIdealPrime.At(R, p, arg.TermAs[A]("monoid_pow(R.mul, R.one, g, n)"), b)))))
		})
		return ctx.Theorem(headline, func(
			arg *Argument,
			R *Expr[RingOps[A]],
			ring comm_ring.CommRingFact[on.R],
			f *Member[A, on.R],
			s *Arrow[Set[A], Set[Prod[A, A]]],
			section Fact,
		) {
			J, idealDef := arg.LetAs[Set[A]](
				"J",
				"«clearingIdeal»(R, "+
					"    spec_section_ops(R, zariski_open(R, f)), "+
					"    «coefficientSection»(R, zariski_open(R, f)), "+
					"    s)")
			hom := arg.Have(
				"coefficients map into the section ring",
				"ring_homomorphism(R, "+
					"    spec_section_ops(R, zariski_open(R, f)), "+
					"    «coefficientSection»(R, zariski_open(R, f)))",
				By(
					ring,
					f,
					prime_spectrum.ZariskiOpenOpen.Read(ring).At(f),
					CoefficientSectionHomomorphism.At(R, arg.TermAs[Set[Set[A]]]("zariski_open(R, f)"))))
			sectionRing := arg.TermAs[RingOps[_Section]]("spec_section_ops(R, zariski_open(R, f))")
			coefficients := arg.TermAs[Fun[A, _Section]]("«coefficientSection»(R, zariski_open(R, f))")
			ideal := arg.Have(
				"the clearing coefficients form an ideal",
				"ring_ideal(R, J)",
				Simp(Fwd(idealDef)),
				By(section, hom, At(clearingIdeal, R, sectionRing, coefficients, s)))
			n, power := arg.ObtainAs[Nat](
				"some power of f clears s",
				"∃n:num. monoid_pow(R.mul, R.one, f, n) ∈ J",
				Derive(func(d *Argument) {
					noPower := d.SupposeNot()
					p, above := d.ObtainAs[Set[A]](
						"otherwise a prime containing J misses f",
						"∃p:set(A). prime_ideal(R, p) ∧ J ⊆ p ∧ f ∉ p",
						By(noPower, ideal, f, ring_ideal.PrimeAvoidingPowers.Read(ring).At(J, f)))
					outside := d.Have(
						"a clearing coefficient lies outside this prime",
						"∃r:A. r ∈ J ∧ r ∉ p",
						Simp(Fwd(idealDef)),
						By(
							ring,
							f,
							section,
							above,
							prime_spectrum.ZariskiOpenMember.Read(ring).At(f, p),
							At(localClearing, R, f, s, p)))
					d.Show(
						"a prime containing J contains every clearing coefficient",
						BySets(outside, above))
				}))
			arg.Take(n)
			arg.Show(
				"membership in the clearing ideal supplies the numerator",
				BySets(idealDef, power))
		})
	}),
})}

// SectionsAtBasicOpen — the coefficient section a/one makes the ring
// of sections over D(f) a localization at the powers of f. Reciprocal
// sections invert these powers; representation and the coefficient
// kernel give the remaining localization conditions.
var SectionsAtBasicOpen = sectionsAtBasicOpenThm{family.Add(registry.ProofEntry{
	Name: "SectionsAtBasicOpen",
	Key:  "prop_2bef8ace0e9a1b63",
	Reading: "f ∈ R.carrier makes its powers multiplicative " +
		"(ring_localization.PowersMultiplicative). If D(f) is empty, f is nilpotent and the section " +
		"carrier is the singleton {λq. ∅}; a zero power of f supplies every kernel annihilator and " +
		"the sole target element is a unit. Zero rings and zero denominators are allowed.",
	Build: family.Sections(Statement{
		Binders:    "∀R:ring_ops(A). ∀f:A.",
		Hypotheses: []string{"comm_ring_on(R)", "f ∈ R.carrier"},
		Conclusion: "is_localization_on(R, " +
			"    monoid_powers(R.mul, R.one, f), " +
			"    «basicSectionRing»(R, f), " +
			"    «coefficientSection»(R, zariski_open(R, f)))",
		Abbrev: Abbrev{
			{Name: "basicSectionRing", Text: "λR:ring_ops(A). λf:A. " +
				"    mk_ring(structure_add(R, zariski_open(R, f)), " +
				"        structure_zero(R, zariski_open(R, f)), " +
				"        structure_neg(R, zariski_open(R, f)), " +
				"        structure_mul(R, zariski_open(R, f)), " +
				"        structure_one(R, zariski_open(R, f)), " +
				"        structure_sub(R, zariski_open(R, f)), " +
				"        structure_sections(R, zariski_open(R, f)))"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		reciprocal := ctx.Lemma(Statement{
			Binders: "∀R:ring_ops(A). ∀U:set(set(A)). ∀b:A.",
			Hypotheses: []string{
				"comm_ring_on(R)",
				"U ∈ zariski_topology(R)",
				"b ∈ R.carrier",
				"∀q:set(A). q ∈ U ⇒ b ∉ q",
			},
			Conclusion: "ring_unit(spec_section_ops(R, U), «coefficientSection»(R, U, b))",
		}, func(
			arg *Argument,
			R *Expr[RingOps[A]],
			ring comm_ring.CommRingFact[on.R],
			U *Expr[Set[Set[A]]],
			open Fact,
			b *Member[A, on.R],
			avoids Fact,
		) {
			v, inverseDef := arg.LetAs[_Section]("v", "fraction_section(R, U, R.one, b)")
			inverseIn := arg.Have(
				"one over b is a section",
				"v ∈ structure_sections(R, U)",
				By(
					Normalized,
					avoids,
					inverseDef,
					b,
					open,
					comm_ring.OneIn.Read(ring),
					ConstantFractionSection.At(R, U, arg.TermAs[A]("R.one"), b)))
			pointwise := arg.Have(
				"b times one over b is one at every point",
				Statement{
					Binders:    "∀q:set(A).",
					Hypotheses: []string{"q ∈ U"},
					Conclusion: "fraction_mul(R.carrier, " +
						"    R.carrier ∖ q, " +
						"    fraction_class(R.carrier, R.carrier ∖ q, b, R.one), " +
						"    fraction_class(R.carrier, R.carrier ∖ q, R.one, b)) = " +
						"fraction_class(R.carrier, R.carrier ∖ q, R.one, R.one)",
				},
				Derive(func(d *Argument) {
					q := d.FixAs[Set[A]]("q")
					inside := d.Assume()
					denominators := d.Have(
						"the prime complement is multiplicative and contains b",
						"multiplicative_set(R.carrier, R.carrier ∖ q) ∧ b ∈ R.carrier ∖ q",
						BySets(
							ring,
							avoids.At(q),
							b,
							inside,
							open,
							ZariskiPointPrime.At(R, U, q),
							local_ring.PrimeComplementMultiplicative.Read(ring).At(q)))
					d.Show(
						"the local denominator calculation gives one",
						By(d.Simplified(
							GroupPremises(
								denominators,
								ring_localization.DenominatorUnit.Read(ring).At(d.TermAs[Set[A]]("R.carrier ∖ q"), b)),
							Fwd(ring_localization.ToFractionDef),
							Fwd(ring_localization.FractionOneDef))))
				}))
			inverse := arg.Have(
				"the reciprocal is an inverse in the section ring",
				"spec_section_ops(R, U).mul(«coefficientSection»(R, U, b), v) = spec_section_ops(R, U).one",
				Simp(
					Fwd(inverseDef),
					Fwd(StructureMulDef),
					Fwd(StructureOneDef),
					Fwd(FractionSectionDef),
					Fwd(ring_localization.FractionOneDef)),
				BySets(pointwise))
			hom := arg.Have(
				"coefficients map to sections",
				"ring_homomorphism(R, spec_section_ops(R, U), «coefficientSection»(R, U))",
				By(ring, open, CoefficientSectionHomomorphism.At(R, U)))
			arg.Do(Simp(Fwd(ring_ideal.RingUnitDef)), SplitConj(
				Case(
					"the coefficient is a section",
					By(b, ring_homomorphism.MapIn.Read(hom).AsFact().At(b))),
				Case(
					"the reciprocal witnesses invertibility",
					Witness(v),
					By(inverse, inverseIn))))
		})
		return ctx.Theorem(headline, func(
			arg *Argument,
			R *Expr[RingOps[A]],
			ring comm_ring.CommRingFact[on.R],
			f *Member[A, on.R],
		) {
			U := arg.TermAs[Set[Set[A]]]("zariski_open(R, f)")
			hom := arg.Have(
				"the coefficient section map is a ring homomorphism",
				"ring_homomorphism(R, "+
					"    spec_section_ops(R, zariski_open(R, f)), "+
					"    «coefficientSection»(R, zariski_open(R, f)))",
				By(
					ring,
					f,
					prime_spectrum.ZariskiOpenOpen.Read(ring).At(f),
					CoefficientSectionHomomorphism.At(R, U)))
			arg.Do(Simp(Rev(SpecSectionOps)), Simp(Fwd(ring_localization.IsLocalizationOnDef)), SplitConjAll(
				Case(
					"powers of f form a multiplicative set",
					By(f, ring_localization.PowersMultiplicative.Read(ring).At(f))),
				Case(
					"the coefficient map preserves the ring operations",
					By(hom)),
				Case(
					"every power of f maps to a unit",
					Derive(func(d *Argument) {
						u := d.FixAs[A]("u")
						powerIn := d.Assume()
						n, power := d.ObtainAs[Nat](
							"write the denominator as a power of f",
							"∃n:num. u = monoid_pow(R.mul, R.one, f, n)",
							BySets(
								powerIn,
								comm_monoid.MonoidPowersDef.At(d.TermAs[Fun2[A, A, A]]("R.mul"), d.TermAs[A]("R.one"), f)))
						guards := d.Have(
							"the power lies in R and avoids every point of D(f)",
							"u ∈ R.carrier ∧ (∀q:set(A). q ∈ zariski_open(R, f) ⇒ u ∉ q)",
							SplitConj(
								Case(
									"powers remain in R",
									By(Normalized, power, f, comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(ring)).At(f, n))),
								Case(
									"a prime missing f misses its powers",
									Derive(func(e *Argument) {
										q := e.FixAs[Set[A]]("q")
										inside := e.Assume()
										e.Show(
											"the prime cannot contain this power",
											By(
												Normalized,
												power,
												f,
												inside,
												prime_spectrum.ZariskiOpenMember.Read(ring).At(f, q),
												ring_ideal.PrimeIdealPow.Read(ring).At(q, f, n)))
									}))))
						d.Show(
							"the reciprocal section makes this power a unit",
							By(ring, f, guards, prime_spectrum.ZariskiOpenOpen.Read(ring).At(f), At(reciprocal, R, U, u)))
					})),
				Case(
					"every section has a numerator and a power denominator",
					Derive(func(d *Argument) {
						y := d.FixAs[_Section]("y")
						section := d.Assume()
						n, a, representation := d.Obtain2As[Nat, A](
							"a power of f clears the section",
							"∃n:num. ∃a:A. "+
								"    a ∈ R.carrier ∧ "+
								"    spec_section_ops(R, zariski_open(R, f)).mul( "+
								"        «coefficientSection»(R, zariski_open(R, f), monoid_pow(R.mul, R.one, f, n)), y) = "+
								"    «coefficientSection»(R, zariski_open(R, f), a)",
							By(ring, f, section, BasicOpenSectionRepresentation.At(R, f, y)))
						readRepresentation := d.Unfolded(representation, SpecSectionOps)
						switchFactors := d.Have(
							"the clearing power can multiply on either side",
							"structure_mul(R, "+
								"    zariski_open(R, f), "+
								"    y, "+
								"    «coefficientSection»(R, zariski_open(R, f), monoid_pow(R.mul, R.one, f, n))) = "+
								"structure_mul(R, "+
								"    zariski_open(R, f), "+
								"    «coefficientSection»(R, zariski_open(R, f), monoid_pow(R.mul, R.one, f, n)), "+
								"    y)",
							By(
								f,
								section,
								At(comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(ring)), f, n),
								At(ring_homomorphism.MapIn.Read(hom), d.TermAs[A]("monoid_pow(R.mul, R.one, f, n)")),
								At(
									comm_monoid.CommOn.Read(comm_ring.MulMonoidOn.Read(ring_homomorphism.Target.Read(hom))),
									y,
									d.TermAs[_Section]("«coefficientSection»(R, zariski_open(R, f), monoid_pow(R.mul, R.one, f, n))"))))
						d.Take(a)
						d.Take(d.TermAs[A]("monoid_pow(R.mul, R.one, f, n)"))
						d.Do(SplitConjAll(
							Case(
								"the numerator lies in R",
								By(representation)),
							Case(
								"the denominator is a power of f",
								BySets(comm_monoid.MonoidPowersDef.At(d.TermAs[Fun2[A, A, A]]("R.mul"), d.TermAs[A]("R.one"), f))),
							Case(
								"multiplying by the denominator gives the numerator",
								By(switchFactors, readRepresentation))))
					})),
				Case(
					"zero coefficient sections have a power annihilator",
					Derive(func(d *Argument) {
						a := d.FixAs[A]("a")
						zero := d.Assume()
						parts := d.Conjuncts(
							zero,
							"a lies in R",
							"the coefficient section is zero")
						pointwise := d.Have(
							"the coefficient vanishes at every point of D(f)",
							Statement{
								Binders:    "∀q:set(A).",
								Hypotheses: []string{"q ∈ zariski_open(R, f)"},
								Conclusion: "fraction_class(R.carrier, R.carrier ∖ q, a, R.one) = " +
									"fraction_zero(R.carrier, R.carrier ∖ q)",
							},
							By(
								parts[1],
								StructureZeroDef.Inst[A]().At(R, U),
								FractionSectionDef.Inst[A]().At(R, U, a, d.TermAs[A]("R.one"))))
						killed := d.Have(
							"a power of f annihilates a",
							"∃n:num. R.mul(monoid_pow(R.mul, R.one, f, n), a) = R.zero",
							By(ring, pointwise, parts[0], f, BasicOpenCoefficientKernel.At(R, f, a)))
						d.Show(
							"the annihilator belongs to the multiplicative set",
							BySets(
								killed,
								comm_monoid.MonoidPowersDef.At(d.TermAs[Fun2[A, A, A]]("R.mul"), d.TermAs[A]("R.one"), f)))
					}))))
		})
	}),
})}

// GlobalSections — the global sections are the ring: r ↦ the section
// p ↦ r / one is a ring isomorphism. No prime holds one, so D(one) is
// the whole spectrum and its sections localize the ring at the powers of
// one; every power of one is a unit, and a localization at units is an
// isomorphism.
var GlobalSections = globalSectionsThm{family.Add(registry.ProofEntry{
	Name:    "GlobalSections",
	Key:     "prop_c05ed50d11e50d",
	Reading: "In the zero ring the spectrum is empty and both carriers have one point.",
	Build: comm_ring.CommRingOn.Law("ring_isomorphism(R, "+
		"    spec_section_ops(R, prime_spectrum(R)), "+
		"    «coefficientSection»(R, prime_spectrum(R)))",
		func(a *Argument, ring comm_ring.CommRingFact[on.R]) {
			fullSpectrum := a.Have(
				"no prime holds one, so D(one) is the whole spectrum",
				"zariski_open(R, R.one) = prime_spectrum(R)",
				Unfold(prime_spectrum.ZariskiOpenDef),
				Unfold(prime_spectrum.PrimeSpectrumDef),
				BySets(ring_ideal.PrimeIdealProper))
			powersAreUnits := a.Have(
				"every power of one is one, a unit",
				"∀s:A. s ∈ monoid_powers(R.mul, R.one, R.one) ⇒ ring_unit(R, s)",
				Unfold(comm_monoid.MonoidPowersDef),
				BySets(
					ring_ideal.OneUnit.Read(ring),
					comm_monoid.IdentityPowOn.Read(comm_ring.MulMonoidOn.Read(ring))))
			one := a.TermAs[A]("R.one")
			baseRing := a.TermAs[RingOps[A]]("R")
			localized := a.Have(
				"the coefficient sections over D(one) localize the ring at the powers of one",
				"is_localization_on(R, "+
					"    monoid_powers(R.mul, R.one, R.one), "+
					"    spec_section_ops(R, prime_spectrum(R)), "+
					"    «coefficientSection»(R, prime_spectrum(R)))",
				fullSpectrum.RwRev(),
				Simp(Fwd(SpecSectionOps)),
				By(ring, comm_ring.OneIn.Read(ring), SectionsAtBasicOpen.At(baseRing, one)))
			sectionRing := a.TermAs[RingOps[_Section]]("spec_section_ops(R, prime_spectrum(R))")
			coefficients := a.TermAs[Fun[A, _Section]]("«coefficientSection»(R, prime_spectrum(R))")
			powers := a.TermAs[Set[A]]("monoid_powers(R.mul, R.one, R.one)")
			a.Show(
				"a localization at units is an isomorphism",
				By(
					localized,
					powersAreUnits,
					ring_localization.LocalizationAtUnits.At(baseRing, powers, sectionRing, coefficients)))
		}),
})}

// ---------------------------------------------------------------------------
// The stalks
// ---------------------------------------------------------------------------

// StalkAtPrime — the germ of the coefficient section a/one makes the
// stalk at p a localization at the complement of p. For s outside p, the
// germ of one over s on D(s) is an inverse of the coefficient germ of s.
// Every stalk element is the germ of a fraction a/b near p, so multiplying
// it by the coefficient germ of b gives the coefficient germ of a. A zero
// coefficient germ agrees with the zero section on a neighborhood of p, and
// evaluating there at p gives the zero fraction, whose criterion supplies
// an annihilator outside p.
var StalkAtPrime = stalkAtPrimeThm{family.Add(registry.ProofEntry{
	Name: "StalkAtPrime",
	Key:  "prop_1908e25a6c9082c9",
	Reading: "The prime hypothesis makes R.carrier ∖ p multiplicative, containing one and " +
		"excluding zero. Every representative neighborhood contains p. The zero ring has no prime, so " +
		"this statement is vacuous there; the coefficient map is constrained only on the source carrier.",
	Build: family.Sections(Statement{
		Binders:    "∀R:ring_ops(A). ∀p:set(A).",
		Hypotheses: []string{"comm_ring_on(R)", "p ∈ prime_spectrum(R)"},
		Conclusion: "is_localization_on(R, R.carrier ∖ p, spec_stalk_ops(R, p), «coefficientGerm»(R, p))",
		Abbrev: Abbrev{
			{Name: "germ", Text: "λR:ring_ops(A). λp:set(A). λU:set(set(A)). λs:(set(A) → set(prod(A, A))). " +
				"    sheaf_germ(zariski_topology(R), structure_sections(R), structure_restrict, p, U, s)"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		clearDenominator := ctx.Lemma(Statement{
			Binders: "∀R:comm_ring_on(A). ∀U:set(set(A)). ∀a b:A.",
			Hypotheses: []string{
				"U ∈ zariski_topology(R)",
				"a ∈ R.carrier",
				"b ∈ R.carrier",
				"∀q:set(A). q ∈ U ⇒ b ∉ q",
			},
			Conclusion: "structure_mul(R, U, «coefficientSection»(R, U, b), fraction_section(R, U, a, b)) = " +
				"«coefficientSection»(R, U, a)",
		}, func(
			arg *Argument,
			ring comm_ring.CommRingFact[on.R],
			U *Expr[Set[Set[A]]],
			a, b *Expr[A],
			h Fact,
		) {
			parts := arg.Conjuncts(
				h,
				"U is open",
				"the numerator lies in R",
				"the denominator lies in R",
				"the denominator avoids U")
			open, aIn, bIn, avoids := parts[0], parts[1], parts[2], parts[3]
			R := arg.TermAs[RingOps[A]]("R")
			pointwise := arg.Have(
				"multiplication by the denominator clears the local fraction at every point",
				"∀q:set(A). "+
					"    structure_mul(R, U, «coefficientSection»(R, U, b), fraction_section(R, U, a, b), q) = "+
					"    «coefficientSection»(R, U, a, q)",
				Derive(func(c *Argument) {
					q := c.FixAs[Set[A]]("q")
					c.Do(Simp(Fwd(StructureMulDef), Fwd(FractionSectionDef)))
					inside := c.Assuming(
						c.TermAs[Bool]("q ∈ U"),
						"both sides are empty outside U",
						Given(func(d *Argument, outside Fact) {
							d.Show(
								"use the empty values",
								By(outside))
						}))
					c.Show(
						"inside U, b / 1 times a / b is a / 1 at the prime q",
						Simp(Fwd(inside)),
						CondRewrite(),
						BySets(
							ring,
							aIn,
							bIn,
							inside,
							open,
							avoids.At(q),
							ZariskiPointPrime.At(R, U, q),
							local_ring.PrimeComplementMultiplicative.Read(ring).At(q),
							ring_localization.DenominatorClearsFraction.Read(ring).AsFact().At(
								c.TermAs[Set[A]]("R.carrier ∖ q"), a, b)))
				}))
			arg.Show(
				"the sections agree pointwise",
				By(pointwise))
		})
		restrictCoefficient := ctx.Lemma(Statement{
			Binders:    "∀R:ring_ops(A). ∀U V:set(set(A)). ∀a:A.",
			Hypotheses: []string{"V ⊆ U"},
			Conclusion: "structure_restrict(U, V, «coefficientSection»(R, U, a)) = " +
				"«coefficientSection»(R, V, a)",
		}, func(arg *Argument, R *Expr[RingOps[A]], U, V *Expr[Set[Set[A]]], a *Expr[A], subset Fact) {
			arg.Show(
				"restriction keeps the coefficient values on V",
				Unfold(StructureRestrictDef),
				Unfold(FractionSectionDef),
				BySets(subset))
		})
		return ctx.Theorem(headline, func(
			arg *Argument,
			R *Expr[RingOps[A]],
			ring comm_ring.CommRingFact[on.R],
			p *Expr[Set[A]],
			atPrime Fact,
		) {
			space := arg.TermAs[Set[Set[A]]]("prime_spectrum(R)")
			one := arg.TermAs[A]("R.one")
			presheafRings := arg.Have(
				"the section rings form a presheaf of rings",
				"presheaf_of_rings(spec_sheaf(R))",
				By(locally_ringed_space.SheafPresheafOfRings.Read(StructureSheafOfRings.Read(ring))))
			presheafSets := arg.Have(
				"the section carriers and restrictions form a presheaf",
				"presheaf(zariski_topology(R), structure_sections(R), structure_restrict)",
				By(locally_ringed_space.Presheaf.Read(presheafRings), SpecSectionOps))
			openSpace := arg.Have(
				"the whole spectrum is open",
				"prime_spectrum(R) ∈ zariski_topology(R)",
				By(
					Normalized,
					topological_space.SpaceOpen.Read(prime_spectrum.ZariskiIsTopology.Read(ring)),
					prime_spectrum.ZariskiSpace.Read(ring)))
			globalHom := arg.Have(
				"coefficients define global sections",
				"ring_homomorphism(R, "+
					"    spec_section_ops(R, prime_spectrum(R)), "+
					"    «coefficientSection»(R, prime_spectrum(R)))",
				By(ring, openSpace, At(CoefficientSectionHomomorphism, R, space)))
			hom := arg.Have(
				"the coefficient germs define a ring homomorphism, the coefficient map followed by the germ map",
				"ring_homomorphism(R, spec_stalk_ops(R, p), «coefficientGerm»(R, p))",
				By(
					atPrime,
					globalHom,
					prime_spectrum.ZariskiSpace.Read(ring),
					locally_ringed_space.CoefficientGermHomomorphism.Read(presheafRings).At(
						R,
						arg.TermAs[Fun[A, _Section]]("«coefficientSection»(R, prime_spectrum(R))"),
						p),
					SpecSectionOps,
					SpecStalkOps.At(R, p)))
			globalSections := arg.Have(
				"every coefficient in R gives a global section",
				Statement{
					Binders:    "∀a:A.",
					Hypotheses: []string{"a ∈ R.carrier"},
					Conclusion: "«coefficientSection»(R, prime_spectrum(R), a) ∈ " +
						"structure_sections(R, prime_spectrum(R))",
				},
				Derive(func(c *Argument) {
					a := c.FixAs[A]("a")
					inR := c.Assume()
					c.Show(
						"read the coefficient map on its carrier",
						By(inR, ring_homomorphism.MapIn.Read(globalHom).AsFact().At(a), SpecSectionOps.At(R, space)))
				}))
			localCoefficient := arg.Have(
				"a coefficient germ is independent of its representative neighborhood",
				Statement{
					Binders:    "∀U:set(set(A)). ∀a:A.",
					Hypotheses: []string{"U ∈ zariski_topology(R)", "p ∈ U", "a ∈ R.carrier"},
					Conclusion: "«germ»(R, p, U, «coefficientSection»(R, U, a)) = «coefficientGerm»(R, p, a)",
				},
				Derive(func(c *Argument) {
					U := c.FixAs[Set[Set[A]]]("U")
					a := c.FixAs[A]("a")
					data := c.Assume()
					subset := c.Have(
						"the open neighborhood lies in the spectrum",
						"U ⊆ prime_spectrum(R)",
						BySets(
							data,
							prime_spectrum.ZariskiSpace.Read(ring),
							set_order.MemberSubsetUnions.Inst[Set[A]]().At(
								c.TermAs[Set[Set[Set[A]]]]("zariski_topology(R)"), U)))
					c.Show(
						"restriction preserves the germ of the coefficient section",
						By(
							data,
							openSpace,
							subset,
							globalSections.At(a),
							At(restrictCoefficient, R, space, U, a),
							presheaf.GermRestrict.Read(presheafSets).AsFact().At(
								p, space, U, c.TermAs[_Section]("«coefficientSection»(R, prime_spectrum(R), a)"))))
				}))
			fractionGerm := arg.Have(
				"multiplication by the denominator clears a fraction germ",
				Statement{
					Binders: "∀U:set(set(A)). ∀a b:A.",
					Hypotheses: []string{
						"U ∈ zariski_topology(R)",
						"p ∈ U",
						"a ∈ R.carrier",
						"b ∈ R.carrier",
						"∀q:set(A). q ∈ U ⇒ b ∉ q",
					},
					Conclusion: "stalk_mul(spec_sheaf(R), " +
						"    p, " +
						"    «coefficientGerm»(R, p, b), " +
						"    «germ»(R, p, U, fraction_section(R, U, a, b))) = " +
						"«coefficientGerm»(R, p, a)",
				},
				Derive(func(c *Argument) {
					U := c.FixAs[Set[Set[A]]]("U")
					a := c.FixAs[A]("a")
					b := c.FixAs[A]("b")
					parts := c.Conjuncts(
						c.Assume(),
						"U is open",
						"p lies in U",
						"the numerator lies in R",
						"the denominator lies in R",
						"the denominator avoids U")
					open, point, aIn, bIn, avoids := parts[0], parts[1], parts[2], parts[3], parts[4]
					localHom := c.Have(
						"coefficients map into the section ring on U",
						"ring_homomorphism(R, spec_section_ops(R, U), «coefficientSection»(R, U))",
						By(ring, open, At(CoefficientSectionHomomorphism, R, U)))
					factors := c.Have(
						"both factors are sections on U",
						"«coefficientSection»(R, U, b) ∈ structure_sections(R, U) ∧ "+
							"fraction_section(R, U, a, b) ∈ structure_sections(R, U)",
						SplitConj(
							Case(
								"the coefficient of b is a section",
								By(bIn, ring_homomorphism.MapIn.Read(localHom).AsFact().At(b), SpecSectionOps.At(R, U))),
							Case(
								"the fraction is a section because its denominator avoids U",
								By(avoids, aIn, bIn, open, At(ConstantFractionSection, R, U, a, b)))))
					coefficient := c.TermAs[_Section]("«coefficientSection»(R, U, b)")
					fraction := c.TermAs[_Section]("fraction_section(R, U, a, b)")
					c.Show(
						"take germs of the section identity",
						CalcEq(
							Leg(
								c.TermAs[_Germ](
									"stalk_mul(spec_sheaf(R), "+
										"    p, "+
										"    «germ»(R, p, U, «coefficientSection»(R, U, b)), "+
										"    «germ»(R, p, U, fraction_section(R, U, a, b)))"),
								"use the local representative of the coefficient germ",
								By(bIn, point, open, localCoefficient.At(U, b))),
							Leg(
								c.TermAs[_Germ](
									"«germ»(R, "+
										"    p, "+
										"    U, "+
										"    structure_mul(R, U, «coefficientSection»(R, U, b), fraction_section(R, U, a, b)))"),
								"germs preserve multiplication",
								By(
									point,
									open,
									factors,
									locally_ringed_space.GermMul.Read(presheafRings).AsFact().At(p, U, coefficient, fraction),
									SpecSectionOps)),
							Leg(
								c.TermAs[_Germ]("«germ»(R, p, U, «coefficientSection»(R, U, a))"),
								"clear the denominator on U",
								By(ring, avoids, aIn, bIn, open, At(clearDenominator, c.TermAs[RingOps[A]]("R"), U, a, b))),
							FinalLeg(
								"use the global representative of the numerator germ",
								By(aIn, point, open, localCoefficient.At(U, a)))))
				}))
			multiplicative := arg.Have(
				"the complement of p is multiplicative",
				"multiplicative_set(R.carrier, R.carrier ∖ p)",
				BySets(
					atPrime,
					prime_spectrum.PrimeSpectrumDef.At(R),
					local_ring.PrimeComplementMultiplicative.Read(ring).At(p)))
			arg.Do(Unfold(ring_localization.IsLocalizationOnDef), SplitConjAll(
				Case(
					"the denominators form a multiplicative set",
					By(multiplicative)),
				Case(
					"the coefficient germ map is a ring homomorphism",
					By(hom)),
				Case(
					"every denominator becomes a unit",
					Derive(func(c *Argument) {
						u := c.FixAs[A]("u")
						denominator := c.Assume()
						neighborhood := c.Have(
							"D(u) is a neighborhood of p on which u avoids every prime",
							"zariski_open(R, u) ∈ zariski_topology(R) ∧ "+
								"p ∈ zariski_open(R, u) ∧ "+
								"(∀q:set(A). q ∈ zariski_open(R, u) ⇒ u ∉ q)",
							BySets(
								denominator,
								atPrime,
								prime_spectrum.ZariskiOpenOpen.Read(ring).AsFact().At(u),
								prime_spectrum.ZariskiOpenDef.At(R, u)))
						D := c.TermAs[Set[Set[A]]]("zariski_open(R, u)")
						reciprocal := c.TermAs[_Section]("fraction_section(R, zariski_open(R, u), R.one, u)")
						reciprocalIn := c.Have(
							"one over u is a section on D(u)",
							"fraction_section(R, zariski_open(R, u), R.one, u) ∈ structure_sections(R, zariski_open(R, u))",
							BySets(
								denominator,
								neighborhood,
								comm_ring.OneIn.Read(ring),
								At(ConstantFractionSection, R, D, one, u)))
						openData := c.Conjuncts(
							neighborhood,
							"D(u) is open",
							"p lies in D(u)",
							"u avoids D(u)")
						c.Do(Unfold(ring_ideal.RingUnitDef), SplitConj(
							Case(
								"the coefficient germ lies in the stalk",
								BySets(denominator, ring_homomorphism.MapIn.Read(hom).AsFact().At(u))),
							Case(
								"the reciprocal germ is an inverse",
								Derive(func(d *Argument) {
									d.Take(d.TermAs[_Germ](
										"«germ»(R, p, zariski_open(R, u), fraction_section(R, zariski_open(R, u), R.one, u))"))
									d.Do(SplitConj(
										Case(
											"the reciprocal germ lies in the stalk",
											By(
												openData[1],
												openData[0],
												reciprocalIn,
												presheaf.GermInStalk.Read(presheafSets).AsFact().At(p, D, reciprocal))),
										Case(
											"multiplication by the reciprocal germ gives one",
											Derive(func(e *Argument) {
												denominatorData := e.Conjuncts(
													e.Unfolded(denominator, set_basic.SetDifferenceDef),
													"u lies in R",
													"u avoids p")
												e.Show(
													"clear the denominator with numerator one",
													By(
														denominatorData[0],
														openData[2],
														openData[1],
														openData[0],
														fractionGerm.At(D, one, u),
														comm_ring.OneIn.Read(ring),
														ring_homomorphism.MapOne.Read(hom)))
											}))))
								}))))
					})),
				Case(
					"every stalk element is a fraction of coefficient germs",
					Derive(func(c *Argument) {
						y := c.FixAs[_Germ]("y")
						yIn := c.Assume()
						U, s, representative := c.Unpack2As[Set[Set[A]], _Section](
							c.Unfolded(yIn, presheaf.StalkDef), "U", "s")
						representativeData := c.Conjuncts(
							representative,
							"the representative is on an open set",
							"its open set contains p",
							"its function is a section",
							"its germ is y")
						V, numerator, denominator, local := c.Obtain3As[Set[Set[A]], A, A](
							"represent the section by a fraction near p",
							"∃V:set(set(A)). ∃a b:A. "+
								"    V ∈ zariski_topology(R) ∧ "+
								"    p ∈ V ∧ "+
								"    V ⊆ U ∧ "+
								"    a ∈ R.carrier ∧ "+
								"    b ∈ R.carrier ∧ "+
								"    (∀q:set(A). q ∈ V ⇒ b ∉ q ∧ s(q) = fraction_class(R.carrier, R.carrier ∖ q, a, b))",
							By(
								representativeData[1],
								c.Unfolded(c.Unfolded(representativeData[2], StructureSectionsDef), LocallyFractionDef)))
						localData := c.Conjuncts(
							local,
							"V is open",
							"p lies in V",
							"V lies in U",
							"a lies in R",
							"b lies in R",
							"the section is a over b on V")
						restricted := c.Have(
							"restriction to V is the constant fraction section",
							"structure_restrict(U, V, s) = fraction_section(R, V, a, b)",
							Unfold(StructureRestrictDef),
							Unfold(FractionSectionDef),
							BySets(localData[5]))
						fractionRepresents := c.Have(
							"the smaller fraction section represents the same germ",
							"«germ»(R, p, V, fraction_section(R, V, a, b)) = y",
							By(
								Normalized,
								restricted,
								representative,
								local,
								presheaf.GermRestrict.Read(presheafSets).AsFact().At(p, U, V, s)))
						c.Take(numerator)
						c.Take(denominator)
						c.Do(SplitConj(
							Case(
								"a lies in R and b avoids p",
								BySets(localData[3], localData[4], localData[1], localData[5].At(p))),
							Case(
								"multiplying y by the coefficient of b gives the coefficient of a",
								CalcEq(
									Leg(
										c.TermAs[_Germ]("stalk_mul(spec_sheaf(R), p, «coefficientGerm»(R, p, b), y)"),
										"commute the two factors in the stalk ring",
										By(
											localData[4],
											yIn,
											ring_homomorphism.MapIn.Read(hom).AsFact().At(denominator),
											comm_monoid.CommOn.Read(comm_ring.MulMonoidOn.Read(ring_homomorphism.Target.Read(hom))).AsFact().At(
												y, c.TermAs[_Germ]("«coefficientGerm»(R, p, b)")))),
									FinalLeg(
										"clear the denominator of the representative fraction",
										By(local, fractionRepresents, fractionGerm.At(V, numerator, denominator)))))))
					})),
				Case(
					"a zero coefficient germ has an annihilator outside p",
					Derive(func(c *Argument) {
						a := c.FixAs[A]("a")
						zeroGerm := c.Assume()
						zeroIn := c.Have(
							"the zero section is a global section",
							"structure_zero(R, prime_spectrum(R)) ∈ structure_sections(R, prime_spectrum(R))",
							By(comm_ring.ZeroIn.Read(ring_homomorphism.Target.Read(globalHom))))
						germsEqual := c.Have(
							"the coefficient germ equals the germ of the zero section",
							"«coefficientGerm»(R, p, a) = "+
								"«germ»(R, p, prime_spectrum(R), structure_zero(R, prime_spectrum(R)))",
							By(
								atPrime,
								openSpace,
								zeroGerm,
								locally_ringed_space.GermZero.Read(presheafRings).AsFact().At(p, space),
								SpecSectionOps))
						W, agreement := c.ObtainAs[Set[Set[A]]](
							"equal germs agree on a neighborhood of p inside the "+
								"overlap of their domains, both the whole spectrum",
							"∃W:set(set(A)). "+
								"    W ∈ zariski_topology(R) ∧ "+
								"    p ∈ W ∧ "+
								"    W ⊆ prime_spectrum(R) ∩ prime_spectrum(R) ∧ "+
								"    structure_restrict(prime_spectrum(R), W, «coefficientSection»(R, prime_spectrum(R), a)) = "+
								"    structure_restrict(prime_spectrum(R), W, structure_zero(R, prime_spectrum(R)))",
							By(
								zeroGerm,
								globalSections.At(a),
								atPrime,
								openSpace,
								zeroIn,
								germsEqual,
								presheaf.GermEq.Read(presheafSets).AsFact().At(
									p,
									space,
									space,
									c.TermAs[_Section]("«coefficientSection»(R, prime_spectrum(R), a)"),
									c.TermAs[_Section]("structure_zero(R, prime_spectrum(R))"))))
						valueZero := c.Have(
							"evaluating the neighborhood equality at p gives the zero fraction",
							"fraction_class(R.carrier, R.carrier ∖ p, a, R.one) = fraction_zero(R.carrier, R.carrier ∖ p)",
							By(
								atPrime,
								agreement,
								StructureRestrictDef.At(
									space, W, c.TermAs[_Section]("«coefficientSection»(R, prime_spectrum(R), a)"), p),
								StructureRestrictDef.At(space, W, c.TermAs[_Section]("structure_zero(R, prime_spectrum(R))"), p),
								StructureZeroDef.At(R, space, p),
								FractionSectionDef.At(R, space, a, one, p)))
						denominators := c.Unfolded(multiplicative, ring_localization.MultiplicativeSetDef)
						c.Show(
							"the zero-fraction criterion supplies the annihilator",
							By(
								valueZero,
								zeroGerm,
								denominators,
								multiplicative,
								ring_localization.FractionZeroIff.Read(ring).AsFact().At(
									c.TermAs[Set[A]]("R.carrier ∖ p"), a, one)))
					})),
			))
		})
	}),
})}

// SpecLocallyRinged — the spectrum with its structure sheaf is a
// locally ringed space: the sections form a sheaf of rings, and the
// stalk at a prime p localizes the ring at the complement of p, so it is
// local.
var SpecLocallyRinged = specLocallyRingedThm{family.Add(registry.ProofEntry{
	Name: "SpecLocallyRinged",
	Key:  "prop_82f90e9bad3227b2",
	Build: comm_ring.CommRingOn.Law("locally_ringed_space(spec_sheaf(R))",
		func(a *Argument, ring comm_ring.CommRingFact[on.R]) {
			a.Do(Unfold(locally_ringed_space.LocallyRingedSpace), SplitConj(
				Case(
					"the structure sheaf is a sheaf of rings",
					By(StructureSheafOfRings.Read(ring))),
				Case(
					"the stalk at every point is a local ring",
					Derive(func(b *Argument) {
						p := b.FixAs[Set[A]]("p")
						inSpace := b.Assume()
						inSpectrum := b.Have(
							"a point of the Zariski space lies in the prime spectrum",
							"p ∈ prime_spectrum(R)",
							By(Normalized, inSpace, prime_spectrum.ZariskiSpace.Read(ring)))
						prime := b.Have(
							"p is a prime ideal",
							"prime_ideal(R, p)",
							BySets(b.Unfolded(inSpectrum, prime_spectrum.PrimeSpectrumDef)))
						baseRing := b.TermAs[RingOps[A]]("R")
						localized := b.Have(
							"the coefficient germs localize the ring at R.carrier ∖ p",
							"is_localization_on(R, R.carrier ∖ p, spec_stalk_ops(R, p), «coefficientGerm»(R, p))",
							By(inSpectrum, StalkAtPrime.Read(ring).At(p)))
						stalkRing := b.TermAs[RingOps[_Germ]]("spec_stalk_ops(R, p)")
						coefficients := b.TermAs[Fun[A, _Germ]]("«coefficientGerm»(R, p)")
						b.Show(
							"a localization at a prime is local",
							Simp(Rev(SpecStalkOps)),
							By(localized, prime, local_ring.LocalizationAtPrimeLocal.At(baseRing, stalkRing, p, coefficients)))
					})),
			))
		}),
})}
