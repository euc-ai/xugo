// Points of an algebra counted through its generators and through inverting an element.

package algebra_point_bounds

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/algebra_points"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_away"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_ideal"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_localization"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// AlgebraPointsGeneratedFinite — a ring generated over S by a finite set G has
// finitely many points in a finite ring. Two points agreeing on G agree on a
// subring holding S and G, so everywhere; a point is therefore determined by
// its restriction to G, one of finitely many maps from G into T.
var AlgebraPointsGeneratedFinite = algebraPointsGeneratedFiniteThm{family.Add(registry.ProofEntry{
	Name: "AlgebraPointsGeneratedFinite",
	Key:  "prop_bfed3deff9ef9209",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀T:ring_ops(B). ∀S G:set(A). ∀i:(A → B).",
		Hypotheses: []string{
			"S ⊆ R.carrier",
			"G ⊆ R.carrier",
			"finite(G)",
			"finite(T.carrier)",
			"∀C:set(A). subring(R, C) ∧ S ⊆ C ∧ G ⊆ C ⇒ R.carrier ⊆ C",
		},
		Conclusion: "finite(algebra_points(R, T, S, i))",
		Abbrev: Abbrev{
			{Name: "restriction", Text: "λf:(A → B). λx:A. COND(x ∈ G, f(x), T.zero)"},
			{Name: "mapsOnG", Text: "{h:(A → B) | " +
				"    (∀x:A. x ∈ G ⇒ h(x) ∈ T.carrier) ∧ (∀x:A. x ∉ G ⇒ h(x) = T.zero)}"},
		},
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			T *Expr[RingOps[B]],
			S, G *Expr[Set[A]],
			i *Arrow[A, B],
			sInR, gInR, finiteG, finiteT, generates Fact,
		) {
			points := a.TermAs[Set[Fun[A, B]]]("algebra_points(R, T, S, i)")
			restriction := a.TermAs[Fun[Fun[A, B], Fun[A, B]]]("«restriction»")
			agreement := a.Have(
				"two points agreeing on G are equal",
				Statement{
					Binders: "∀f g:(A → B).",
					Hypotheses: []string{
						"f ∈ algebra_points(R, T, S, i)",
						"g ∈ algebra_points(R, T, S, i)",
						"∀x:A. x ∈ G ⇒ f(x) = g(x)",
					},
					Conclusion: "f = g",
				},
				Derive(func(b *Argument) {
					f := b.FixAs[Fun[A, B]]("f")
					g := b.FixAs[Fun[A, B]]("g")
					assumed := b.Assume()
					data := b.Have(
						"both are ring maps, equal on S and zero off R",
						"ring_homomorphism(R, T, f) ∧ "+
							"ring_homomorphism(R, T, g) ∧ "+
							"(∀x:A. x ∈ S ⇒ f(x) = g(x)) ∧ "+
							"(∀x:A. x ∉ R.carrier ⇒ f(x) = T.zero ∧ g(x) = T.zero)",
						BySets(
							algebra_points.AlgebraPointsMember.At(R, T, S, i, f),
							algebra_points.AlgebraPointsMember.At(R, T, S, i, g),
							assumed))
					agreeing := b.TermAs[Set[A]]("{x:A | x ∈ R.carrier ∧ f(x) = g(x)}")
					equalizer := b.Have(
						"the elements where they agree form a subring",
						"subring(R, {x:A | x ∈ R.carrier ∧ f(x) = g(x)})",
						By(data, ring_homomorphism.RingMapEqualizerSubring.At(R, T, f, g)))
					holds := b.Have(
						"which holds S and G",
						"S ⊆ {x:A | x ∈ R.carrier ∧ f(x) = g(x)} ∧ G ⊆ {x:A | x ∈ R.carrier ∧ f(x) = g(x)}",
						BySets(sInR, gInR, assumed, data))
					cover := b.Have(
						"so it is all of R",
						"R.carrier ⊆ {x:A | x ∈ R.carrier ∧ f(x) = g(x)}",
						By(generates.At(agreeing), equalizer, holds))
					b.Do(Funext())
					b.Show(
						"they agree on R and vanish off it",
						BySets(cover, data))
				}))
			injective := a.Have(
				"so restriction to G is injective on the points",
				"injective_on(algebra_points(R, T, S, i), «restriction»)",
				Simp(Fwd(functions.InjectiveOnDef)),
				By(Normalized, agreement))
			valuesInT := a.Have(
				"a point sends G into T",
				"∀φ:(A → B). φ ∈ algebra_points(R, T, S, i) ⇒ ∀x:A. x ∈ G ⇒ φ(x) ∈ T.carrier",
				Derive(func(b *Argument) {
					φ := b.FixAs[Fun[A, B]]("φ")
					point := b.Assume()
					ringMap := b.Have(
						"it is a ring map",
						"ring_homomorphism(R, T, φ)",
						By(algebra_points.AlgebraPointsMember.At(R, T, S, i, φ), point))
					b.Show(
						"and G lies in R",
						BySets(gInR, ring_homomorphism.MapIn.Read(ringMap)))
				}))
			restricted := a.Have(
				"so the restrictions are maps from G into T",
				"image(«restriction», algebra_points(R, T, S, i)) ⊆ «mapsOnG»",
				BySets(valuesInT))
			a.Show(
				"there are finitely many such maps, and restriction is injective",
				By(
					finiteG,
					finiteT,
					restricted,
					injective,
					cardinality.FiniteFunspace.At(G, a.TermAs[Set[B]]("T.carrier"), a.TermAs[B]("T.zero")),
					finite_set.FiniteSubset.At(
						a.TermAs[Set[Fun[A, B]]]("image(«restriction», algebra_points(R, T, S, i))"),
						a.TermAs[Set[Fun[A, B]]]("«mapsOnG»")),
					finite_set.FiniteImageInjEq.At(restriction, points)))
		}),
})}

// AlgebraPointsAway — when R is S with d inverted, restriction to S is a
// bijection from the points of R onto the points of S at which d is a unit.
// A point of R is determined on S by the localization, and sends the unit d
// to a unit. Conversely a point of S making d a unit makes every power of d a
// unit, so it extends to R by the universal property of the localization, and
// the extension is made a point by sending everything off R to zero.
var AlgebraPointsAway = algebraPointsAwayThm{family.Add(registry.ProofEntry{
	Name: "AlgebraPointsAway",
	Key:  "prop_53adcb59fe39f2c4",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀T:ring_ops(B). ∀S k:set(A). ∀i:(A → B). ∀d:A.",
		Hypotheses: []string{
			"is_localization_on(restrict_ring(R, S), monoid_powers(R.mul, R.one, d), R, λx:A. x)",
			"d ∈ S",
			"k ⊆ S",
		},
		Conclusion: "injective_on(algebra_points(R, T, k, i), «restriction») ∧ " +
			"image(«restriction», algebra_points(R, T, k, i)) = " +
			"{ψ:A → B | ψ ∈ algebra_points(restrict_ring(R, S), T, k, i) ∧ ring_unit(T, ψ(d))}",
		Abbrev: Abbrev{
			{Name: "restriction", Text: "λφ:(A → B). λx:A. COND(x ∈ S, φ(x), T.zero)"},
		},
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			T *Expr[RingOps[B]],
			S, k *Expr[Set[A]],
			i *Arrow[A, B],
			d *Expr[A],
			localization, dInS, kInS Fact,
		) {
			opened := a.Conjuncts(
				a.Unfolded(localization, ring_localization.IsLocalizationOnDef),
				"the powers of d are a multiplicative subset of S",
				"S includes into R",
				"the powers of d are units of R",
				"every element of R is a fraction",
				"an element of S vanishing in R is killed by a power of d")
			inclusion, powerUnits := opened[1], opened[2]
			ring := a.Have(
				"R is a ring",
				"comm_ring_on(R)",
				By(ring_homomorphism.Target.Read(inclusion)))
			sInR := a.Have(
				"S lies in R",
				"S ⊆ R.carrier",
				BySets(ring_homomorphism.MapIn.Read(inclusion)))
			RS := a.TermAs[RingOps[A]]("restrict_ring(R, S)")
			powersOfD := a.TermAs[Set[A]]("monoid_powers(R.mul, R.one, d)")
			inclusionMap := a.TermAs[Fun[A, A]]("λx:A. x")
			firstPower := a.Have(
				"d is its own first power",
				"∃n:num. d = monoid_pow(R.mul, R.one, d, n)",
				Witness(a.TermAs[Nat]("1")),
				By(
					dInS,
					comm_monoid.PowOneOn.Read(comm_ring.MulMonoidOn.Read(ring)).AsFact().At(d),
					ring_homomorphism.MapIn.Read(inclusion).AsFact().At(d)))
			unitD := a.Have(
				"so d is a unit of R",
				"ring_unit(R, d)",
				BySets(powerUnits, firstPower, comm_monoid.MonoidPowersDef))
			restrictedMaps := a.Have(
				"a ring map on R is a ring map on S",
				"∀φ:(A → B). ring_homomorphism(R, T, φ) ⇒ ring_homomorphism(restrict_ring(R, S), T, φ)",
				Derive(func(b *Argument) {
					φ := b.FixAs[Fun[A, B]]("φ")
					ringMap := b.Assume()
					b.Show(
						"compose it with the inclusion",
						By(inclusion, ringMap, ring_homomorphism.RingHomCompose.At(RS, R, T, inclusionMap, φ)))
				}))
			forward := a.Have(
				"the restriction of a point of R is a point of S, and the point makes d a unit",
				Statement{
					Binders:    "∀φ:(A → B).",
					Hypotheses: []string{"φ ∈ algebra_points(R, T, k, i)"},
					Conclusion: "(λx:A. COND(x ∈ S, φ(x), T.zero)) ∈ algebra_points(restrict_ring(R, S), T, k, i) ∧ " +
						"ring_unit(T, φ(d))",
				},
				Derive(func(b *Argument) {
					φ := b.FixAs[Fun[A, B]]("φ")
					point := b.Assume()
					data := b.Conjuncts(
						b.Have(
							"φ is a ring map fixing what i prescribes on k",
							"ring_homomorphism(R, T, φ) ∧ (∀x:A. x ∈ k ⇒ φ(x) = i(x)) ∧ (∀x:A. x ∉ R.carrier ⇒ φ(x) = T.zero)",
							By(algebra_points.AlgebraPointsMember.At(R, T, k, i, φ), point)),
						"φ is a ring map",
						"φ is prescribed on k",
						"φ vanishes off R")
					ringMap, prescribed := data[0], data[1]
					restricted := b.TermAs[Fun[A, B]]("λx:A. COND(x ∈ S, φ(x), T.zero)")
					restrictedMap := b.Have(
						"the restriction is a ring map on S",
						"ring_homomorphism(restrict_ring(R, S), T, λx:A. COND(x ∈ S, φ(x), T.zero))",
						By(restrictedMaps.At(φ), ringMap, ring_homomorphism.RingHomCongruence.At(RS, T, φ, restricted)))
					restrictedPoint := b.Have(
						"so a point of S",
						"(λx:A. COND(x ∈ S, φ(x), T.zero)) ∈ algebra_points(restrict_ring(R, S), T, k, i)",
						BySets(prescribed, kInS, restrictedMap, algebra_points.AlgebraPointsDef.At(RS, T, k, i)))
					b.Show(
						"and ring maps send units to units",
						By(restrictedPoint, unitD, ring_homomorphism.MapUnit.Read(ringMap).AsFact().At(d)))
				}))
			agreement := a.Have(
				"two points of R agreeing on S are equal",
				Statement{
					Binders: "∀φ χ:(A → B).",
					Hypotheses: []string{
						"φ ∈ algebra_points(R, T, k, i)",
						"χ ∈ algebra_points(R, T, k, i)",
						"∀x:A. x ∈ S ⇒ φ(x) = χ(x)",
					},
					Conclusion: "φ = χ",
				},
				Derive(func(b *Argument) {
					φ := b.FixAs[Fun[A, B]]("φ")
					χ := b.FixAs[Fun[A, B]]("χ")
					assumed := b.Assume()
					maps := b.Have(
						"both are ring maps and vanish off R",
						"ring_homomorphism(R, T, φ) ∧ "+
							"ring_homomorphism(R, T, χ) ∧ "+
							"(∀x:A. x ∉ R.carrier ⇒ φ(x) = T.zero ∧ χ(x) = T.zero)",
						By(
							algebra_points.AlgebraPointsMember.At(R, T, k, i, φ),
							algebra_points.AlgebraPointsMember.At(R, T, k, i, χ),
							assumed))
					b.Do(Funext())
					y := b.FixAs[A]("y")
					b.Cases(b.Term("y ∈ R.carrier"))
					b.When(
						"on R they agree, S generating R as a localization",
						func(c *Argument, inR Fact) {
							c.Show(
								"two ring maps out of a localization agreeing on S are equal",
								By(
									inR,
									assumed,
									maps,
									localization,
									ring_localization.LocalizationHomomorphismExtensional.At(
										RS, powersOfD, R, inclusionMap, T, φ, χ, y)))
						})
					b.Otherwise(
						"off R both are zero",
						func(c *Argument, outside Fact) {
							c.Show(
								"both vanish there",
								By(Normalized, outside, maps))
						})
				}))
			powerImages := a.Have(
				"a ring map on S making d a unit makes every power of d a unit",
				Statement{
					Binders: "∀ψ:(A → B).",
					Hypotheses: []string{
						"ring_homomorphism(restrict_ring(R, S), T, ψ)",
						"ring_unit(T, ψ(d))",
					},
					Conclusion: "∀q:A. q ∈ monoid_powers(R.mul, R.one, d) ⇒ ring_unit(T, ψ(q))",
				},
				Derive(func(b *Argument) {
					b.FixAs[Fun[A, B]]("ψ")
					assumed := b.Conjuncts(
						b.Assume(),
						"ψ is a ring map",
						"ψ(d) is a unit")
					ringMap, unit := assumed[0], assumed[1]
					target := b.Have(
						"T is a ring",
						"comm_ring_on(T)",
						By(ring_homomorphism.Target.Read(ringMap)))
					ψd := b.TermAs[B]("ψ(d)")
					unitPowers := b.Have(
						"so each power of d goes to the same power of ψ(d), a unit",
						"∀n:num. ring_unit(T, ψ(monoid_pow(R.mul, R.one, d, n)))",
						Derive(func(c *Argument) {
							n := c.FixAs[Nat]("n")
							c.Show(
								"ψ(dⁿ) = ψ(d)ⁿ, and a power of a unit is a unit",
								By(
									dInS,
									unit,
									ring_homomorphism.RingMapPower.Read(ringMap).AsFact().At(n, d),
									ring_ideal.RingUnitPow.Read(target).At(ψd, n)))
						}))
					b.Show(
						"every member of the powers of d is such a power",
						BySets(unitPowers, comm_monoid.MonoidPowersDef))
				}))
			extension := a.Have(
				"a point of S making d a unit extends to a point of R",
				Statement{
					Binders: "∀ψ:(A → B).",
					Hypotheses: []string{
						"ψ ∈ algebra_points(restrict_ring(R, S), T, k, i)",
						"ring_unit(T, ψ(d))",
					},
					Conclusion: "∃φ:(A → B). φ ∈ algebra_points(R, T, k, i) ∧ (∀x:A. x ∈ S ⇒ φ(x) = ψ(x))",
				},
				Derive(func(b *Argument) {
					ψ := b.FixAs[Fun[A, B]]("ψ")
					assumed := b.Conjuncts(
						b.Assume(),
						"ψ is a point of S",
						"ψ(d) is a unit")
					point, unit := assumed[0], assumed[1]
					clauses := b.Conjuncts(
						b.Have(
							"ψ is a ring map prescribed on k",
							"ring_homomorphism(restrict_ring(R, S), T, ψ) ∧ "+
								"(∀x:A. x ∈ k ⇒ ψ(x) = i(x)) ∧ "+
								"(∀x:A. x ∉ S ⇒ ψ(x) = T.zero)",
							By(algebra_points.AlgebraPointsMember.At(RS, T, k, i, ψ), point)),
						"ψ is a ring map",
						"ψ is prescribed on k",
						"ψ vanishes off S")
					ringMap, prescribed := clauses[0], clauses[1]
					h, lifted := b.ObtainAs[Fun[A, B]](
						"the powers of d going to units, ψ extends to R by the universal property",
						"∃h:(A → B). ring_homomorphism(R, T, h) ∧ (∀x:A. x ∈ S ⇒ h(x) = ψ(x))",
						By(
							localization,
							ringMap,
							unit,
							powerImages.At(ψ),
							ring_localization.LocalizationUniversal.At(RS, powersOfD, R, inclusionMap, T, ψ)))
					lift := b.Conjuncts(
						lifted,
						"h is a ring map on R",
						"h agrees with ψ on S")
					liftMap, agrees := lift[0], lift[1]
					normalized := b.TermAs[Fun[A, B]]("λx:A. COND(x ∈ R.carrier, h(x), T.zero)")
					normalizedMap := b.Have(
						"sending everything off R to zero keeps a ring map",
						"ring_homomorphism(R, T, λx:A. COND(x ∈ R.carrier, h(x), T.zero))",
						By(liftMap, ring_homomorphism.RingHomCongruence.At(R, T, h, normalized)))
					values := b.Have(
						"the normalized map is prescribed on k and zero off R",
						"(∀x:A. x ∈ k ⇒ COND(x ∈ R.carrier, h(x), T.zero) = i(x)) ∧ "+
							"(∀x:A. x ∉ R.carrier ⇒ COND(x ∈ R.carrier, h(x), T.zero) = T.zero)",
						BySets(agrees, prescribed, sInR, kInS))
					normalizedPoint := b.Have(
						"so it is a point of R",
						"(λx:A. COND(x ∈ R.carrier, h(x), T.zero)) ∈ algebra_points(R, T, k, i)",
						By(algebra_points.AlgebraPointsMember.At(R, T, k, i, normalized), values, normalizedMap))
					onS := b.Have(
						"and it agrees with ψ on S",
						"∀x:A. x ∈ S ⇒ COND(x ∈ R.carrier, h(x), T.zero) = ψ(x)",
						BySets(agrees, sInR))
					b.Take(normalized)
					b.Show(
						"take the normalized map",
						By(normalizedPoint, onS))
				}))
			injective := a.Have(
				"points of R agreeing on S being equal, restriction is injective",
				"injective_on(algebra_points(R, T, k, i), «restriction»)",
				Simp(Fwd(functions.InjectiveOnDef)),
				By(Normalized, agreement))
			image := a.Have(
				"the image of restriction is the points of S making d a unit",
				"image(«restriction», algebra_points(R, T, k, i)) = "+
					"{ψ:A → B | ψ ∈ algebra_points(restrict_ring(R, S), T, k, i) ∧ ring_unit(T, ψ(d))}",
				Simp(Fwd(set_basic.Extension)),
				Derive(func(b *Argument) {
					y := b.FixAs[Fun[A, B]]("y")
					b.Iff()
					b.Forward(
						"a restriction is a point of S making d a unit",
						func(c *Argument, inImage Fact) {
							preimage, written := c.UnpackAs[Fun[A, B]](
								c.Simplified(inImage, Fwd(set_basic.InImage)),
								"φ")
							parts := c.Conjuncts(
								written,
								"y is the restriction of φ",
								"φ is a point of R")
							c.Show(
								"the restriction of φ takes the value φ(d) at d",
								parts[0].Rw(),
								BySets(forward.At(preimage), dInS, parts[1]))
						})
					b.Backward(
						"a point of S making d a unit is the restriction of its extension",
						func(c *Argument, inSet Fact) {
							wanted := c.Have(
								"y is a point of S making d a unit",
								"y ∈ algebra_points(restrict_ring(R, S), T, k, i) ∧ ring_unit(T, y(d))",
								BySets(inSet))
							preimage, extended := c.ObtainAs[Fun[A, B]](
								"it extends to a point of R",
								"∃φ:(A → B). φ ∈ algebra_points(R, T, k, i) ∧ (∀x:A. x ∈ S ⇒ φ(x) = y(x))",
								By(extension.At(y), wanted))
							vanishing := c.Have(
								"y vanishes off S",
								"∀x:A. x ∉ S ⇒ y(x) = T.zero",
								By(algebra_points.AlgebraPointsMember.At(RS, T, k, i, y), wanted))
							c.Do(Simp(Fwd(set_basic.InImage)))
							c.Take(preimage)
							c.Do(SplitConj(
								Case(
									"y is the restriction of the extension",
									Funext(),
									BySets(vanishing, extended)),
								Case(
									"which is a point of R",
									By(extended))))
						})
				}))
			a.Show(
				"so restriction is a bijection onto them",
				By(injective, image))
		}),
})}

// AlgebraPointsAwayCardLe — inverting a member d of S with an inverse e in
// the ambient ring adds no points: when S has finitely many points, S[1/d]
// has at most as many. S[1/d] is the localization of S at the powers of d,
// so restriction to S is injective on its points and lands among the points
// of S (AlgebraPointsAway).
var AlgebraPointsAwayCardLe = algebraPointsAwayCardLeThm{family.Add(registry.ProofEntry{
	Name: "AlgebraPointsAwayCardLe",
	Key:  "prop_67aa311fff7294a9",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀T:ring_ops(B). ∀S k:set(A). ∀i:(A → B). ∀d e:A.",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"subring(R, S)",
			"k ⊆ S",
			"d ∈ S",
			"e ∈ R.carrier",
			"d * e = R.one",
			"finite(«pointsOf»(S))",
		},
		Conclusion: "card(«pointsOf»(ring_away(R, S, d))) ≤ card(«pointsOf»(S))",
		Abbrev: Abbrev{
			{Name: "pointsOf", Text: "λX:set(A). algebra_points(restrict_ring(R, X), T, k, i)"},
			{Name: "inverted", Text: "restrict_ring(R, ring_away(R, S, d))"},
			{Name: "restriction", Text: "λφ:(A → B). λx:A. COND(x ∈ S, φ(x), T.zero)"},
		},
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			ring comm_ring.CommRingFact[on.R],
			T *Expr[RingOps[B]],
			S, k *Expr[Set[A]],
			i *Arrow[A, B],
			d, e *Expr[A],
			subringS, kInS, dInS, eInR, product, finitePoints Fact,
		) {
			away := a.TermAs[Set[A]]("ring_away(R, S, d)")
			inverted := a.TermAs[RingOps[A]]("«inverted»")
			points := a.TermAs[Set[Fun[A, B]]]("«pointsOf»(ring_away(R, S, d))")
			pointsOfS := a.TermAs[Set[Fun[A, B]]]("«pointsOf»(S)")
			restriction := a.TermAs[Fun[Fun[A, B], Fun[A, B]]]("«restriction»")
			image := a.TermAs[Set[Fun[A, B]]]("image(«restriction», «pointsOf»(ring_away(R, S, d)))")
			twice := module_record.RestrictRingTwice.At(R, away, S)
			localization := a.Have(
				"S[1/d] is the localization of S at the powers of d",
				"is_localization_on(restrict_ring(«inverted», S), "+
					"    monoid_powers(«inverted».mul, «inverted».one, d), "+
					"    «inverted», "+
					"    λx:A. x)",
				By(
					ring,
					eInR,
					product,
					dInS,
					subringS,
					ring_away.RingAwayIsLocalization.At(R, S, d, e),
					twice,
					module_record.RingMulDef,
					module_record.RingOneDef,
					module_record.RestrictRingDef))
			restricted := a.Conjuncts(
				a.Have(
					"so restriction to S is a bijection from its points onto the points of S making d a unit",
					"injective_on(«pointsOf»(ring_away(R, S, d)), «restriction») ∧ "+
						"image(«restriction», «pointsOf»(ring_away(R, S, d))) = "+
						"{ψ:A → B | ψ ∈ «pointsOf»(S) ∧ ring_unit(T, ψ(d))}",
					By(dInS, kInS, localization, AlgebraPointsAway.At(inverted, T, S, k, i, d), twice)),
				"restriction is injective on the points of S[1/d]",
				"its image is the points of S making d a unit")
			injective, imageEq := restricted[0], restricted[1]
			imageInside := a.Have(
				"the image lies among the points of S",
				"image(«restriction», «pointsOf»(ring_away(R, S, d))) ⊆ «pointsOf»(S)",
				BySets(imageEq))
			finiteSource := a.Have(
				"so S[1/d] has finitely many points",
				"finite(«pointsOf»(ring_away(R, S, d)))",
				By(
					finitePoints,
					injective,
					imageInside,
					finite_set.FiniteSubset.At(image, pointsOfS),
					finite_set.FiniteImageInjEq.At(restriction, points)))
			a.Show(
				"and counting the image counts them",
				By(
					finitePoints,
					finiteSource,
					injective,
					imageInside,
					cardinality.CardSubset.At(image, pointsOfS),
					cardinality.CardImageInj.At(restriction, points)))
		}),
})}
