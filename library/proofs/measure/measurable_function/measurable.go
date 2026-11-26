package measurable_function

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/real/real_archimedean"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_topology"
	"github.com/euc-ai/xugo/library/proofs/sets/measurable_space"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/proofs/sets/sigma_algebra"
	"github.com/euc-ai/xugo/library/proofs/topology/borel_space"
	"github.com/euc-ai/xugo/library/registry"
)

// RealMeasurableIffRay — real measurability is determined by strict upper rays:
// complements and countable unions give interval preimages, then all Borel preimages.
var RealMeasurableIffRay = realMeasurableIffRayThm{family.Add(registry.ProofEntry{
	Name: "RealMeasurableIffRay",
	Key:  "prop_6468d83b27bd8395",
	Build: family.Sections(Statement{
		Binders:    "∀Ω:set(A). ∀S:set(set(A)). ∀f:(A → real).",
		Hypotheses: []string{"sigma_algebra_on(Ω, S)"},
		Conclusion: "real_measurable(Ω, S, f) ⇔ ∀c:real. {x:A | x ∈ Ω ∧ c < f(x)} ∈ S",
		Abbrev: Abbrev{
			{Name: "preimages", Text: "{t:set(real) | preimage_on(Ω, f, t) ∈ S}"},
			{Name: "borelCandidates", Text: "{U:set(set(real)) | sigma_algebra_on(𝕌, U) ∧ real_topology ⊆ U}"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		reciprocal := ctx.Lemma("∀x c:real. x < c ⇔ ∃n:num. x ≤ c - real_inv(&n + &1)",
			func(arg *Argument, x, c *Expr[Real]) {
				arg.Iff()
				arg.Forward(
					"a positive gap exceeds some reciprocal",
					func(b *Argument, below Fact) {
						n, small := b.ObtainAs[Nat](
							"choose a reciprocal smaller than the gap",
							"∃n:num. real_inv(&n + &1) < c - x",
							ByArith(below, real_archimedean.ExistsReciprocalBelow.At(b.TermAs[Real]("c - x"))))
						b.Take(n)
						b.Show(
							"the reciprocal leaves x below c",
							ByArith(small))
					})
				arg.Backward(
					"a positive reciprocal gives a strict gap",
					func(b *Argument, some Fact) {
						_, atMost := b.UnpackAs[Nat](some, "n")
						positive := b.Have(
							"the reciprocal is positive",
							"&0 < real_inv(&n + &1)",
							ByArith(real_order_field.InvPos.At(b.TermAs[Real]("&n + &1"))))
						b.Show(
							"the upper bound lies strictly below c",
							ByArith(atMost, positive))
					})
			})

		closedRays := ctx.Lemma(Statement{
			Binders: "∀Ω:set(A). ∀S:set(set(A)). ∀f:(A → real). ∀c:real.",
			Hypotheses: []string{
				"sigma_algebra_on(Ω, S)",
				"∀t:real. {x:A | x ∈ Ω ∧ t < f(x)} ∈ S",
			},
			Conclusion: "{x:A | x ∈ Ω ∧ f(x) ≤ c} ∈ S",
		}, func(
			arg *Argument,
			Ω *Expr[Set[A]],
			S *Expr[Set[Set[A]]],
			f *Arrow[A, Real],
			c *Expr[Real],
			h Fact,
		) {
			complement := arg.Have(
				"a closed lower ray is the relative complement of an upper ray",
				"{x:A | x ∈ Ω ∧ f(x) ≤ c} = Ω ∖ {x:A | x ∈ Ω ∧ c < f(x)}",
				BySets(real_order_ring.NotLessThan))
			arg.Show(
				"relative complements are measurable",
				By(h, complement, At(sigma_algebra.SigmaAlgebraOnDef, Ω, S)))
		})

		lowerRays := ctx.Lemma(Statement{
			Binders: "∀Ω:set(A). ∀S:set(set(A)). ∀f:(A → real). ∀c:real.",
			Hypotheses: []string{
				"sigma_algebra_on(Ω, S)",
				"∀t:real. {x:A | x ∈ Ω ∧ t < f(x)} ∈ S",
			},
			Conclusion: "{x:A | x ∈ Ω ∧ f(x) < c} ∈ S",
		}, func(
			arg *Argument,
			Ω *Expr[Set[A]],
			S *Expr[Set[Set[A]]],
			f *Arrow[A, Real],
			c *Expr[Real],
			h Fact,
		) {
			union := arg.Have(
				"an open lower ray is a countable union of closed lower rays",
				"{x:A | x ∈ Ω ∧ f(x) < c} = ⋃image(λn:num. {x:A | x ∈ Ω ∧ f(x) ≤ c - real_inv(&n + &1)}, 𝕌)",
				BySets(reciprocal))
			laws := arg.Conjuncts(
				arg.Unfolded(h, sigma_algebra.SigmaAlgebraOnDef),
				"sets lie in the carrier",
				"the carrier is measurable",
				"relative complements are measurable",
				"countable unions are measurable",
				"upper rays are measurable")
			terms := arg.Have(
				"each approximating closed ray is measurable",
				"∀n:num. {x:A | x ∈ Ω ∧ f(x) ≤ c - real_inv(&n + &1)} ∈ S",
				Derive(func(b *Argument) {
					b.FixAs[Nat]("n")
					b.Show(
						"apply closed-ray measurability at the shifted threshold",
						By(h, At(closedRays, Ω, S, f, b.TermAs[Real]("c - real_inv(&n + &1)"))))
				}))
			arg.Show(
				"the union is measurable",
				By(
					terms,
					union,
					laws[3].At(arg.TermAs[Fun[Nat, Set[A]]]("λn:num. {x:A | x ∈ Ω ∧ f(x) ≤ c - real_inv(&n + &1)}"))))
		})

		intervals := ctx.Lemma(Statement{
			Binders: "∀Ω:set(A). ∀S:set(set(A)). ∀f:(A → real). ∀a b:real.",
			Hypotheses: []string{
				"sigma_algebra_on(Ω, S)",
				"∀t:real. {x:A | x ∈ Ω ∧ t < f(x)} ∈ S",
			},
			Conclusion: "preimage_on(Ω, f, ⟬a, b⟭) ∈ S",
		}, func(
			arg *Argument,
			Ω *Expr[Set[A]],
			S *Expr[Set[Set[A]]],
			f *Arrow[A, Real],
			a, b *Expr[Real],
			h Fact,
		) {
			meet := arg.Have(
				"an interval preimage is the intersection of two ray preimages",
				"preimage_on(Ω, f, ⟬a, b⟭) = {x:A | x ∈ Ω ∧ a < f(x)} ∩ {x:A | x ∈ Ω ∧ f(x) < b}",
				BySets())
			arg.Show(
				"finite intersections preserve measurability",
				By(h, meet, At(lowerRays, Ω, S, f, b), At(sigma_algebra.SigmaFiniteOperations, Ω, S)))
		})

		opens := ctx.Lemma(Statement{
			Binders: "∀Ω:set(A). ∀S:set(set(A)). ∀f:(A → real). ∀u:set(real).",
			Hypotheses: []string{
				"sigma_algebra_on(Ω, S)",
				"∀t:real. {x:A | x ∈ Ω ∧ t < f(x)} ∈ S",
				"u ∈ real_topology",
			},
			Conclusion: "preimage_on(Ω, f, u) ∈ S",
		}, func(
			arg *Argument,
			Ω *Expr[Set[A]],
			S *Expr[Set[Set[A]]],
			f *Arrow[A, Real],
			u *Expr[Set[Real]],
			h Fact,
		) {
			_, _, cover := arg.Obtain2As[Fun[Nat, Real], Fun[Nat, Real]](
				"write the open set as a countable union of intervals",
				"∃a b:(num → real). ∀y:real. y ∈ u ⇔ ∃n:num. a(n) < y ∧ y < b(n)",
				By(h, real_topology.OpenCountableIntervalUnion.At(u)))
			union := arg.Have(
				"preimages commute with this countable union",
				"preimage_on(Ω, f, u) = ⋃image(λn:num. preimage_on(Ω, f, ⟬a(n), b(n)⟭), 𝕌)",
				BySets(cover))
			terms := arg.Have(
				"each interval preimage is measurable",
				"∀n:num. preimage_on(Ω, f, ⟬a(n), b(n)⟭) ∈ S",
				Derive(func(d *Argument) {
					d.FixAs[Nat]("n")
					d.Show(
						"use the interval criterion",
						By(h, At(intervals, Ω, S, f, d.TermAs[Real]("a(n)"), d.TermAs[Real]("b(n)"))))
				}))
			arg.Show(
				"the open-set preimage is measurable",
				By(h, terms, union, At(sigma_algebra.SigmaAlgebraOnDef, Ω, S)))
		})

		pullbackSigma := ctx.Lemma(Statement{
			Binders:    "∀Ω:set(A). ∀S:set(set(A)). ∀f:(A → real).",
			Hypotheses: []string{"sigma_algebra_on(Ω, S)"},
			Conclusion: "sigma_algebra_on(𝕌, «preimages»)",
		}, func(arg *Argument, Ω *Expr[Set[A]], S *Expr[Set[Set[A]]], f *Arrow[A, Real], h Fact) {
			arg.Do(Simp(Fwd(sigma_algebra.SigmaAlgebraOnDef)))
			arg.Show(
				"preimages preserve the sigma-algebra operations",
				SplitConj(
					Case(
						"carrier and complements",
						SplitConj(
							Case(
								"sets and the whole carrier",
								Derive(func(b *Argument) {
									universe := b.Have(
										"the full preimage is the source carrier",
										"preimage_on(Ω, f, 𝕌) = Ω",
										BySets())
									b.Show(
										"the target carrier is measurable",
										SplitConj(
											Case(
												"every real set lies in the real universe",
												BySets()),
											Case(
												"the full preimage is measurable",
												By(h, universe, At(sigma_algebra.SigmaAlgebraOnDef, Ω, S))),
										))
								})),
							Case(
								"relative complement closure",
								Derive(func(b *Argument) {
									b.FixAs[Set[Real]]("u")
									member := b.Assume()
									complement := b.Have(
										"preimages commute with relative complements",
										"preimage_on(Ω, f, 𝕌 ∖ u) = Ω ∖ preimage_on(Ω, f, u)",
										BySets())
									b.Show(
										"the complement preimage is measurable",
										By(h, member, complement, At(sigma_algebra.SigmaAlgebraOnDef, Ω, S)))
								})),
						)),
					Case(
						"countable union closure",
						Derive(func(b *Argument) {
							b.FixAs[Fun[Nat, Set[Real]]]("a")
							member := b.Assume()
							union := b.Have(
								"preimages commute with countable unions",
								"preimage_on(Ω, f, ⋃image(a, 𝕌)) = ⋃image(λn:num. preimage_on(Ω, f, a(n)), 𝕌)",
								BySets())
							b.Show(
								"the union preimage is measurable",
								By(h, member, union, At(sigma_algebra.SigmaAlgebraOnDef, Ω, S)))
						})),
				))
		})

		return ctx.Theorem(headline, func(
			arg *Argument,
			Ω *Expr[Set[A]],
			S *Expr[Set[Set[A]]],
			f *Arrow[A, Real],
			sigma Fact,
		) {
			arg.Iff()
			arg.Forward(
				"measurability gives measurable upper rays",
				func(b *Argument, measurable Fact) {
					c := b.FixAs[Real]("c")
					borelRay := b.Have(
						"an open upper ray is Borel",
						"{y:real | c < y} ∈ borel_sets(real_topology)",
						Simp(Fwd(borel_space.BorelSetsDef)),
						BySets(real_topology.RayAboveOpen.At(c)))
					ray := b.Have(
						"the relative preimage is the upper level set",
						"preimage_on(Ω, f, {y:real | c < y}) = {x:A | x ∈ Ω ∧ c < f(x)}",
						BySets())
					maps := b.Unfolded(measurable, RealMeasurableDef)
					preimages := b.Unfolded(maps, measurable_space.MeasurableMapDef)
					b.Show(
						"Borel preimages are measurable",
						By(preimages, borelRay, ray))
				})
			arg.Backward(
				"upper rays determine all Borel preimages",
				func(b *Argument, rays Fact) {
					pullback := b.Have(
						"sets with measurable preimages form a sigma algebra",
						"sigma_algebra_on(𝕌, «preimages»)",
						By(sigma, At(pullbackSigma, Ω, S, f)))
					containsOpens := b.Have(
						"this sigma algebra contains every real open set",
						"real_topology ⊆ «preimages»",
						Simp(Fwd(set_basic.SubsetDef)),
						Derive(func(d *Argument) {
							u := d.FixAs[Set[Real]]("u")
							open := d.Assume()
							d.Show(
								"open sets have measurable preimages",
								By(sigma, rays, open, At(opens, Ω, S, f, u)))
						}))
					containsBorel := b.Have(
						"the Borel intersection lies in this sigma algebra",
						"borel_sets(real_topology) ⊆ «preimages»",
						Simp(Fwd(real_topology.RealSpace), Fwd(borel_space.BorelSetsDef)),
						Derive(func(d *Argument) {
							witness := d.Have(
								"the preimage sigma algebra is one of the intersected families",
								"∃T:set(set(real)). T ∈ «borelCandidates» ∧ T ⊆ «preimages»",
								Derive(func(e *Argument) {
									e.Take(e.TermAs[Set[Set[Real]]]("«preimages»"))
									e.Show(
										"it contains the opens and itself",
										BySets(pullback, containsOpens))
								}))
							d.Show(
								"an intersection lies in each of its members",
								By(
									witness,
									At(
										set_order.IntersSubsetStrong.Inst[Set[Real]](),
										d.TermAs[Set[Set[Set[Real]]]]("«borelCandidates»"),
										d.TermAs[Set[Set[Real]]]("«preimages»"))))
						}))
					b.Show(
						"every Borel preimage is measurable",
						Simp(Fwd(RealMeasurableDef), Fwd(measurable_space.MeasurableMapDef)),
						BySets(containsBorel))
				})
		})
	}),
})}

// RealMeasurableIffNonnegRay — a function nonnegative on Ω is measurable
// exactly when it exceeds each level c ≥ 0 on a measurable set: below 0 the
// set where it exceeds the level is Ω itself, so the rays at nonnegative
// levels give every ray.
var RealMeasurableIffNonnegRay = realMeasurableIffNonnegRayThm{family.Add(registry.ProofEntry{
	Name: "RealMeasurableIffNonnegRay",
	Key:  "prop_c365ca59a52bb90",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). ∀S:set(set(A)). ∀f:(A → real).",
		Hypotheses: []string{
			"sigma_algebra_on(Ω, S)",
			"∀x:A. x ∈ Ω ⇒ &0 ≤ f(x)",
		},
		Conclusion: "real_measurable(Ω, S, f) ⇔ ∀c:real. &0 ≤ c ⇒ {x:A | x ∈ Ω ∧ c < f(x)} ∈ S",
	}, func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		f *Arrow[A, Real],
		sigma, nonneg Fact,
	) {
		a.Iff()
		a.Forward(
			"a measurable function exceeds every level on a measurable set",
			func(b *Argument, measurable Fact) {
				b.Show(
					"its rays are measurable",
					By(sigma, measurable, RealMeasurableIffRay.At(Ω, S, f)))
			})
		a.Backward(
			"the rays at nonnegative levels give every ray",
			func(b *Argument, rays Fact) {
				every := b.Have(
					"f exceeds every level on a measurable set",
					"∀c:real. {x:A | x ∈ Ω ∧ c < f(x)} ∈ S",
					Derive(func(d *Argument) {
						c := d.FixAs[Real]("c")
						d.Cases(d.Term("&0 ≤ c"))
						d.When(
							"at a level c ≥ 0",
							func(e *Argument, atLeastZero Fact) {
								e.Show(
									"the ray is one of those given",
									By(atLeastZero, rays.At(c)))
							})
						d.Otherwise(
							"below 0 the ray is Ω",
							func(e *Argument, negative Fact) {
								above := e.Have(
									"f is nonnegative on Ω, so above c there",
									"∀x:A. x ∈ Ω ⇒ c < f(x)",
									ByArith(nonneg, negative))
								whole := e.Have(
									"so the set is Ω",
									"{x:A | x ∈ Ω ∧ c < f(x)} = Ω",
									BySets(above))
								e.Show(
									"which is measurable",
									By(whole, sigma, sigma_algebra.SigmaAlgebraOnDef))
							})
					}))
				b.Show(
					"its rays decide its measurability",
					By(sigma, every, RealMeasurableIffRay.At(Ω, S, f)))
			})
	}),
})}
