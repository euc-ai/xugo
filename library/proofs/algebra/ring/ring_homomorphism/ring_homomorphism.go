// ring_homomorphism.go — the chapter: a map between two rings on sets
// that keeps the addition, the multiplication and the one, and with them
// the numerals; its kernel;
// the image of a commutative ring along a map that keeps its operations;
// and the isomorphisms.
//
// The two ring records R and S carry their operations and carriers;
// `ring_homomorphism(R, S, f)` states the map laws between them.

package ring_homomorphism

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/abelian_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_ideal"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/registry"
)

// RingHomomorphism — `ring_homomorphism(R, S, f)`: f carries R.carrier
// into S.carrier, keeping the sum,
// the product and the one. Both rings are the definition's first two
// conjuncts, so the ring chapter's laws apply at `Source` and `Target`.
// Keeping the sum makes f a homomorphism of the two additive groups
// (`AdditiveHomomorphism`), and so f keeps zero and the negation.
var RingHomomorphism = ringHomomorphismThm{family.DefineStructure(registry.DefEntry{
	Name:     "RingHomomorphism",
	Key:      "prop_cba79116630e89f0",
	Const:    "ring_homomorphism",
	Subject:  "f",
	Type:     "ring_ops(A) → ring_ops(B) → (A → B) → bool",
	Implicit: []string{},
	Equations: []string{
		"∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B). " +
			"    ring_homomorphism(R, S, f) ⇔ " +
			"    comm_ring_on(R) ∧ " +
			"    comm_ring_on(S) ∧ " +
			"    (∀x:A. x ∈ R.carrier ⇒ f(x) ∈ S.carrier) ∧ " +
			"    (∀x y:A. x ∈ R.carrier ∧ y ∈ R.carrier ⇒ f(R.add(x, y)) = S.add(f(x), f(y))) ∧ " +
			"    (∀x y:A. x ∈ R.carrier ∧ y ∈ R.carrier ⇒ f(R.mul(x, y)) = S.mul(f(x), f(y))) ∧ " +
			"    f(R.one) = S.one",
	},
	Symbols: map[string]string{},
})}

// Source — the source is a ring on c.
var Source = sourceThm{family.Add(registry.ProofEntry{
	Name:  "Source",
	Key:   "prop_40cca835c13cfa6d",
	Build: RingHomomorphism.Axiom("comm_ring_on(R)"),
})}

// Target — the target is a ring on c'.
var Target = targetThm{family.Add(registry.ProofEntry{
	Name:  "Target",
	Key:   "prop_83a1e9a4fce62ab9",
	Build: RingHomomorphism.Axiom("comm_ring_on(S)"),
})}

// MapIn — f carries c into c'.
var MapIn = mapInThm{family.Add(registry.ProofEntry{
	Name: "MapIn",
	Key:  "prop_cde9c252599e1733",
	Build: RingHomomorphism.Axiom(Statement{
		Binders: "∀x:A.",
		Hypotheses: []string{
			"x ∈ R.carrier",
		},
		Conclusion: "f(x) ∈ S.carrier",
	}),
})}

// MapAdd — f keeps the sum.
var MapAdd = mapAddThm{family.Add(registry.ProofEntry{
	Name: "MapAdd",
	Key:  "prop_1bcfebb2020b86d",
	Build: RingHomomorphism.Axiom(Statement{
		Binders: "∀x y:A.",
		Hypotheses: []string{
			"x ∈ R.carrier",
			"y ∈ R.carrier",
		},
		Conclusion: "f(x + y) = f(x) + f(y)",
	}),
})}

// MapMul — f keeps the product.
var MapMul = mapMulThm{family.Add(registry.ProofEntry{
	Name: "MapMul",
	Key:  "prop_c77d47fdcb065ca4",
	Build: RingHomomorphism.Axiom(Statement{
		Binders: "∀x y:A.",
		Hypotheses: []string{
			"x ∈ R.carrier",
			"y ∈ R.carrier",
		},
		Conclusion: "f(x * y) = f(x) * f(y)",
	}),
})}

// MapOne — f keeps the one.
var MapOne = mapOneThm{family.Add(registry.ProofEntry{
	Name:  "MapOne",
	Key:   "prop_e35039eb8a5e062f",
	Build: RingHomomorphism.Axiom("f(R.one) = S.one"),
})}

// MapUnit — a ring homomorphism carries a unit of the source to a unit of
// the target: the image of an inverse of x is an inverse of φ(x), since φ
// keeps the product and the one, and it lies in c' with φ(x).
var MapUnit = mapUnitThm{family.Add(registry.ProofEntry{
	Name: "MapUnit",
	Key:  "prop_4be670d766cb4b2",
	Build: family.Theorem(Statement{
		Binders: "∀φ:ring_homomorphism(A, B). ∀x:A.",
		Hypotheses: []string{
			"ring_unit(R, x)",
		},
		Conclusion: "ring_unit(S, φ(x))",
	},
		func(a *Argument, φ RingHomomorphismFact[on.R, on.S], x *Expr[A], unit Fact) {
			parts := a.Conjuncts(
				a.Unfolded(unit, ring_ideal.RingUnitDef),
				"x lies in c",
				"and has an inverse y in c")
			xIn, invertible := parts[0], parts[1]
			_, inverse := a.Unpack(invertible, "y")
			product := a.Have(
				"φ(y) inverts φ(x)",
				"φ(x) * φ(y) = S.one",
				CalcEq(
					Leg(
						a.TermAs[B]("φ(x * y)"),
						"φ keeps the product of two members of c",
						By(MapMul.Read(φ), xIn, inverse)),
					Leg(
						a.TermAs[B]("φ(R.one)"),
						"x * y is one",
						By(Normalized, inverse)),
					FinalLeg(
						"φ keeps the one",
						By(MapOne.Read(φ))),
				))
			inverseImage := a.Have(
				"φ(y) lies in c', where it inverts φ(x)",
				"∃w:B. w ∈ S.carrier ∧ φ(x) * w = S.one",
				Witness(a.TermAs[B]("φ(y)")),
				By(MapIn.Read(φ), product, inverse))
			a.Show(
				"φ(x) lies in c' and has an inverse there, so it is a unit of c'",
				By(ring_ideal.RingUnitDef, inverseImage, MapIn.Read(φ), xIn))
		}),
})}

// AdditiveHomomorphism — each ring's sum, zero and negation form an
// abelian group on its carrier, and so a group on it; f carries the
// source's carrier into the target's, and keeping the sum is the group
// homomorphism's operation law. The group homomorphism is unfolded and its
// four conjuncts closed in the definition's order.
var AdditiveHomomorphism = additiveHomomorphismThm{family.Add(registry.ProofEntry{
	Name: "AdditiveHomomorphism",
	Key:  "prop_349c74ac1bb9c38e",
	Build: RingHomomorphism.Law("group_homomorphism(additive_group(R), additive_group(S), f)",
		func(a *Argument, hom RingHomomorphismFact[on.R, on.S]) {
			a.Do(Unfold(group_homomorphism.GroupHomomorphism), SplitConjAll(
				Case(
					"the source's sum, zero and negation form a group on c",
					By(abelian_group.GroupOn.Read(comm_ring.AddGroupOn.Read(Source.Read(hom))))),
				Case(
					"the target's form a group on c'",
					By(abelian_group.GroupOn.Read(comm_ring.AddGroupOn.Read(Target.Read(hom))))),
				Case(
					"f carries c into c'",
					By(MapIn.Read(hom))),
				Case(
					"f carries a sum of two members of c to the sum of the images",
					By(MapAdd.Read(hom))),
			))
		}),
})}

// MapZero — f keeps the zero: the zero is the one of the additive group,
// and f is a homomorphism of the additive groups.
var MapZero = mapZeroThm{family.Add(registry.ProofEntry{
	Name: "MapZero",
	Key:  "prop_35b79171608e0ec",
	Build: RingHomomorphism.Law("f(R.zero) = S.zero",
		func(a *Argument, hom RingHomomorphismFact[on.R, on.S]) {
			a.Show(
				"f keeps the one of the additive groups",
				By(group_homomorphism.MapOne.Read(AdditiveHomomorphism.Read(hom))))
		}),
})}

// ZeroIffImageZero — a ring homomorphism one-to-one on the carrier of its source
// sends a point of that carrier to zero exactly when the point is zero: f keeps
// zero, which lies in the carrier, and identifies no two points of it.
var ZeroIffImageZero = zeroIffImageZeroThm{family.Add(registry.ProofEntry{
	Name: "ZeroIffImageZero",
	Key:  "prop_528cb683d21ed024",
	Build: RingHomomorphism.Law(Statement{
		Binders: "∀x:A.",
		Hypotheses: []string{
			"injective_on(R.carrier, f)",
			"x ∈ R.carrier",
		},
		Conclusion: "x = R.zero ⇔ f(x) = S.zero",
	},
		func(a *Argument, hom RingHomomorphismFact[on.R, on.S], x *Expr[A], injective, xIn Fact) {
			a.Show(
				"f keeps zero, which lies in the carrier, and identifies no two points of it",
				By(
					Normalized,
					a.Unfolded(injective, functions.InjectiveOnDef).At(x, a.TermAs[A]("R.zero")),
					xIn,
					MapZero.Read(hom),
					comm_ring.ZeroIn.Read(Source.Read(hom))))
		}),
})}

// MapNeg — f keeps the negation: the negation is the inverse of the
// additive group, and f is a homomorphism of the additive groups.
var MapNeg = mapNegThm{family.Add(registry.ProofEntry{
	Name: "MapNeg",
	Key:  "prop_30bc244bb167b8e4",
	Build: RingHomomorphism.Law(Statement{
		Binders: "∀x:A.",
		Hypotheses: []string{
			"x ∈ R.carrier",
		},
		Conclusion: "f(-x) = -f(x)",
	},
		func(a *Argument, hom RingHomomorphismFact[on.R, on.S], x *Member[A, on.R]) {
			a.Show(
				"f keeps the inverse of the additive groups",
				By(group_homomorphism.MapInv.Read(AdditiveHomomorphism.Read(hom)).At(x)))
		}),
})}

// MapSub — f keeps the difference: a difference is the sum with the
// negation in both rings, and f keeps the sum and the negation.
var MapSub = mapSubThm{family.Add(registry.ProofEntry{
	Name: "MapSub",
	Key:  "prop_c9a943f819d5dc16",
	Build: RingHomomorphism.Law(Statement{
		Binders: "∀x y:A.",
		Hypotheses: []string{
			"x ∈ R.carrier",
			"y ∈ R.carrier",
		},
		Conclusion: "f(x - y) = f(x) - f(y)",
	},
		func(a *Argument, hom RingHomomorphismFact[on.R, on.S], x, y *Member[A, on.R]) {
			source, target := Source.Read(hom), Target.Read(hom)
			negative := a.Have(
				"the negation of y lies in the source's carrier",
				"-y ∈ R.carrier",
				By(comm_ring.NegIn.Read(source).AsFact().At(y), y))
			a.Show(
				"read the difference on each side as the sum with the negation",
				By(
					comm_ring.SubAddNegOn.Read(source),
					comm_ring.SubAddNegOn.Read(target),
					x,
					y,
					negative,
					MapIn.Read(hom),
					MapAdd.Read(hom),
					MapNeg))
		}),
})}

// MapSum — f keeps a finite sum: it keeps the zero and the sum of two
// members of R, so it carries the fold of R's additive monoid over a
// finite index set to the fold of the images.
var MapSum = mapSumThm{family.Add(registry.ProofEntry{
	Name: "MapSum",
	Key:  "prop_a3543d2915031b51",
	Build: RingHomomorphism.Law(Statement{
		Binders: "∀I:set(D). ∀F:(D → A).",
		Hypotheses: []string{
			"finite(I)",
			"∀p:D. p ∈ I ⇒ F(p) ∈ R.carrier",
		},
		Conclusion: "f(module_sum(R.add, R.zero, I, F)) = module_sum(S.add, S.zero, I, λp:D. f(F(p)))",
	},
		func(
			a *Argument,
			hom RingHomomorphismFact[on.R, on.S],
			I *Expr[Set[D]],
			F *Arrow[D, A],
			finiteIndex, members Fact,
		) {
			a.Show(
				"f keeps the zero and the sum of two members of R, "+
					"so it keeps every finite sum of R's additive monoid",
				By(
					finiteIndex,
					members,
					MapZero.Read(hom),
					MapAdd.Read(hom),
					Read(
						module.ModuleSumMonoidHomomorphism,
						comm_ring.AddMonoidOn.Read(Source.Read(hom))).At(
						a.TermAs[Op[B]]("S.add"),
						a.TermAs[B]("S.zero"),
						a.TermAs[Fun[A, B]]("f"),
						I,
						F)))
		}),
})}

// RingMapNumeral — f keeps the numerals: by induction on n, n ones summed in
// the source go to n ones summed in the target, since f keeps the zero, the one
// and sums on the carrier.
var RingMapNumeral = ringMapNumeralThm{family.Add(registry.ProofEntry{
	Name: "RingMapNumeral",
	Key:  "prop_ef551301e6e1b4ca",
	Build: RingHomomorphism.Law("∀n:num. "+
		"    f(monoid_pow(R.add, R.zero, R.one, n)) = monoid_pow(S.add, S.zero, S.one, n)",
		func(a *Argument, hom RingHomomorphismFact[on.R, on.S], n *Expr[Nat]) {
			source := Source.Read(hom)
			a.Induct(n)
			a.Base(
				"the zeroth additive power is zero",
				Simp(Fwd(comm_monoid.MonoidPowDef)),
				By(MapZero.Read(hom)))
			a.Step(
				"one more summand is preserved",
				func(b *Argument, ih Fact) {
					b.Show(
						"the successor power is the image of the source successor power",
						Simp(Fwd(comm_monoid.MonoidPowDef)),
						By(
							ih,
							comm_ring.OneIn.Read(source),
							MapOne.Read(hom),
							comm_monoid.PowIn.Read(comm_ring.AddMonoidOn.Read(source)).AsFact().At(b.TermAs[A]("R.one"), n),
							MapAdd.Read(hom).AsFact().At(
								b.TermAs[A]("R.one"), b.TermAs[A]("monoid_pow(R.add, R.zero, R.one, n)"))))
				})
		}),
})}

// RingKernelDef — `ring_kernel(zero', c, f)`: the members of c that f
// sends to zero'.
var RingKernelDef = ringKernelDefThm{family.Define(registry.DefEntry{
	Name:     "RingKernelDef",
	Key:      "prop_f701125a55fb4b7",
	Const:    "ring_kernel",
	Type:     "B → set(A) → (A → B) → set(A)",
	Implicit: []string{"zero'"},
	Equations: []string{
		"∀zero':B. ∀c:set(A). ∀f:(A → B). ring_kernel(zero', c, f) = {x:A | x ∈ c ∧ f(x) = zero'}",
	},
})}

// KernelIdeal — the kernel is an ideal of the source, read as the members
// of c that f sends to zero': zero is among them, as f keeps zero (the
// additive groups' identity law, AdditiveHomomorphism); for two
// of them f(x + y) = f(x) + f(y) = zero' + zero' = zero'; and for one of
// them and r in c, f(r * x) = f(r) * f(x) = f(r) * zero' = zero'.
var KernelIdeal = kernelIdealThm{family.Add(registry.ProofEntry{
	Name: "KernelIdeal",
	Key:  "prop_531e7ba7bc32ab8d",
	Build: RingHomomorphism.Law("ring_ideal(R, ring_kernel(S.zero, R.carrier, f))",
		func(a *Argument, hom RingHomomorphismFact[on.R, on.S]) {
			source, target := Source.Read(hom), Target.Read(hom)
			a.Do(Unfold(ring_ideal.RingIdealDef), Unfold(RingKernelDef), SplitConjAll(
				Case(
					"a member of the kernel lies in c",
					BySets()),
				Case(
					"zero lies in c, and f sends it to zero'",
					BySets(comm_ring.ZeroIn.Read(source), MapZero.Read(hom))),
				Case(
					"the kernel is closed under the sum",
					Derive(func(b *Argument) {
						b.FixAs[A]("x")
						b.FixAs[A]("y")
						inKernel := b.Assume()
						members := b.Have(
							"x and y lie in c, and f sends each to zero'",
							"x ∈ R.carrier ∧ f(x) = S.zero ∧ y ∈ R.carrier ∧ f(y) = S.zero",
							BySets(inKernel))
						image := b.Have(
							"so f sends x + y to zero'",
							"f(x + y) = S.zero",
							CalcEq(
								Leg(
									b.TermAs[B]("f(x) + f(y)"),
									"f keeps the sum of two members of c",
									By(MapAdd.Read(hom), members)),
								Leg(
									b.TermAs[B]("S.zero + S.zero"),
									"f sends x and y to zero'",
									By(Normalized, members)),
								FinalLeg(
									"zero' lies in c', where it is the additive identity",
									By(
										comm_monoid.LeftIdentityOn.Read(comm_ring.AddMonoidOn.Read(target)),
										comm_ring.ZeroIn.Read(target))),
							))
						b.Show(
							"and x + y lies in c, which is closed under the sum",
							BySets(image, members, comm_ring.AddIn.Read(source)))
					})),
				Case(
					"the kernel absorbs the product by a member of c",
					Derive(func(b *Argument) {
						b.FixAs[A]("r")
						b.FixAs[A]("x")
						hypotheses := b.Assume()
						member := b.Have(
							"x lies in c, and f sends it to zero'",
							"x ∈ R.carrier ∧ f(x) = S.zero",
							BySets(hypotheses))
						image := b.Have(
							"so f sends r * x to zero'",
							"f(r * x) = S.zero",
							CalcEq(
								Leg(
									b.TermAs[B]("f(r) * f(x)"),
									"f keeps the product of two members of c",
									By(MapMul.Read(hom), hypotheses, member)),
								Leg(
									b.TermAs[B]("f(r) * S.zero"),
									"f sends x to zero'",
									By(Normalized, member)),
								FinalLeg(
									"f(r) lies in c', and a member of c' times zero' is zero'",
									By(comm_ring.MulRightZeroOn.Read(target), MapIn.Read(hom), hypotheses)),
							))
						b.Show(
							"and r * x lies in c, which is closed under the product",
							BySets(image, hypotheses, comm_ring.MulIn.Read(source)))
					})),
			))
		}),
})}

// IdealSpanInKernel — a ring map that kills a set of its source kills the
// ideal the set spans: the kernel is an ideal holding the set, and the span
// is the least ideal that does.
var IdealSpanInKernel = idealSpanInKernelThm{family.Add(registry.ProofEntry{
	Name: "IdealSpanInKernel",
	Key:  "prop_9c1635c867e556d1",
	Build: RingHomomorphism.Law(Statement{
		Binders: "∀E:set(A).",
		Hypotheses: []string{
			"E ⊆ R.carrier",
			"∀x:A. x ∈ E ⇒ f(x) = S.zero",
		},
		Conclusion: "ideal_span(R, E) ⊆ ring_kernel(S.zero, R.carrier, f)",
	},
		func(a *Argument, hom RingHomomorphismFact[on.R, on.S], E *Expr[Set[A]], inside, vanishes Fact) {
			kernel := a.TermAs[Set[A]]("ring_kernel(S.zero, R.carrier, f)")
			generators := a.Have(
				"E lies in the kernel: its members lie in R.carrier, and f sends each to zero'",
				"E ⊆ ring_kernel(S.zero, R.carrier, f)",
				Unfold(RingKernelDef),
				BySets(inside, vanishes))
			a.Show(
				"the kernel is an ideal holding E, and the span of E is the least such ideal",
				By(
					generators,
					KernelIdeal.Read(hom),
					ring_ideal.SpanLeast.At(a.TermAs[RingOps[A]]("R"), E, kernel)))
		}),
})}

// ImageCommRingOn — the homomorphic image of a commutative ring is one: a
// map that carries the carrier of a commutative ring R onto the carrier of
// a ring record S and keeps the six operations makes S a commutative ring.
// Its additive group is the image of R's abelian additive group
// (group_homomorphism.ImageAbelianGroupOn), and its multiplicative monoid
// the image of R's (comm_monoid.ImageCommMonoidOn at
// comm_ring.MulMonoidOn). The two laws joining them, distributivity and
// the difference as the sum with the negation, hold on S.carrier as the
// images of the same laws in R: with the carrier read as the image and
// pulled back along f, each is the law at the values of points of
// R.carrier, where the map's laws turn it into R's own.
var ImageCommRingOn = imageCommRingOnThm{family.Add(registry.ProofEntry{
	Name: "ImageCommRingOn",
	Key:  "prop_43930f8ef47f0299",
	Build: family.Theorem(Statement{
		Binders: "∀R:comm_ring_on(A). ∀S:ring_ops(B). ∀f:(A → B).",
		Hypotheses: []string{
			"image(f, R.carrier) = S.carrier",
			"∀x y:A. x ∈ R.carrier ∧ y ∈ R.carrier ⇒ f(x + y) = f(x) + f(y)",
			"f(R.zero) = S.zero",
			"∀x:A. x ∈ R.carrier ⇒ f(-x) = -f(x)",
			"∀x y:A. x ∈ R.carrier ∧ y ∈ R.carrier ⇒ f(x * y) = f(x) * f(y)",
			"f(R.one) = S.one",
			"∀x y:A. x ∈ R.carrier ∧ y ∈ R.carrier ⇒ f(x - y) = f(x) - f(y)",
		},
		Conclusion: "comm_ring_on(S)",
	},
		func(a *Argument, R comm_ring.CommRingFact[on.R], S *Expr[RingOps[B]], f *Arrow[A, B],
			onto, add, zero, neg, mul, one, sub Fact) {
			additiveS := a.TermAs[group.GroupOps[B]]("additive_group(S)")
			abelian := a.Have(
				"S's sum, zero and negation form an abelian group on S.carrier, the image of R's additive group",
				"abelian_group_on(additive_group(S))",
				By(
					group_homomorphism.ImageAbelianGroupOn.Read(comm_ring.AddGroupOn.Read(R)).At(additiveS, f),
					onto,
					add,
					zero,
					neg))
			multiplicativeMonoid := a.Have(
				"S's product and one form a commutative monoid on S.carrier, the image of R's",
				"comm_monoid_on(S.carrier, S.mul, S.one)",
				By(comm_monoid.ImageCommMonoidOn, comm_ring.MulMonoidOn.Read(R), onto, mul, one))
			distributes := a.Have(
				"the product distributes over the sum on S.carrier, read as the image",
				"∀u v w:B. u ∈ S.carrier ∧ v ∈ S.carrier ∧ w ∈ S.carrier ⇒ u * (v + w) = u * v + u * w",
				onto.RwRev(),
				Simp(Fwd(set_image.ForallInImageTriple)),
				Derive(func(b *Argument) {
					b.FixAs[A]("x")
					b.FixAs[A]("y")
					b.FixAs[A]("z")
					b.Assume()
					b.Show(
						"the two sides are the images of x * (y + z) and x "+
							"* y + x * z, which are equal by distributivity in R",
						Simp(
							Rev(add),
							Rev(mul),
							Fwd(comm_ring.AddIn.Read(R)),
							Fwd(comm_ring.MulIn.Read(R)),
							Fwd(comm_ring.LeftDistribOn.Read(R))),
						Basic())
				}))
			difference := a.Have(
				"the difference is the sum with the negation on S.carrier, read as the image",
				"∀u v:B. u ∈ S.carrier ∧ v ∈ S.carrier ⇒ u - v = u + -v",
				onto.RwRev(),
				Simp(Fwd(set_image.ForallInImagePair)),
				Derive(func(b *Argument) {
					b.FixAs[A]("x")
					b.FixAs[A]("y")
					b.Assume()
					b.Show(
						"f(x) - f(y) and f(x) + -f(y) are the images of x - y and x + -y, which are equal in R",
						Simp(
							Rev(sub),
							Rev(neg),
							Rev(add),
							Fwd(comm_ring.NegIn.Read(R)),
							Fwd(comm_ring.SubAddNegOn.Read(R))),
						Basic())
				}))
			// Unfolding comm_ring_on opens the source's comm_ring_on(R) as
			// well, so the four conditions are had above, before it.
			a.Show(
				"the four facts above are the conditions of a commutative ring on S.carrier",
				Unfold(comm_ring.CommRingOn),
				By(abelian, multiplicativeMonoid, distributes, difference))
		}),
})}

// ImageSubfield — the image of a field under a ring homomorphism into a
// field is a subfield of the target. The image lies in the target's
// carrier; it holds the target's zero and one, the images of the
// source's; and the sum, the negative, the product and the inverse of
// images are the images of the source's, f keeping the inverse because
// it keeps zero, one and products between two fields (field.MapInv).
var ImageSubfield = imageSubfieldThm{family.Add(registry.ProofEntry{
	Name: "ImageSubfield",
	Key:  "prop_4443fe2097cf022e",
	Build: family.Theorem(Statement{
		Binders:    "∀F:field_on(A). ∀G:field_on(B). ∀f:(A → B).",
		Hypotheses: []string{"ring_homomorphism(field_ring(F), field_ring(G), f)"},
		Conclusion: "subfield(G, image(f, F.carrier))",
	}, func(a *Argument, F field.FieldFact[on.F], G field.FieldFact[on.G], f *Arrow[A, B], hom Fact) {
		g := a.TermAs[field.FieldOps[B]]("G")
		fCarrier := a.TermAs[Set[A]]("F.carrier")
		source := field.RingOn.Read(F)
		inverse := a.Have(
			"f carries the inverse of a point of F to the inverse of its image",
			"∀x:A. x ∈ F.carrier ⇒ f(F.inv(x)) = G.inv(f(x))",
			Derive(func(b *Argument) {
				x := b.MemberOf[on.F](b.FixAs[A]("x"), b.Assume())
				b.Show(
					"f keeps zero, one and products between the two fields",
					By(
						G,
						field.MapInv.Read(F).At(g, f, x),
						MapIn.Read(hom),
						MapMul.Read(hom),
						MapZero.Read(hom),
						MapOne.Read(hom)))
			}))
		a.Show(
			"the image meets each condition of a subfield",
			Simp(Fwd(field.SubfieldDef.Inst[B]())),
			SplitConjAll(
				Case(
					"every image lies in the target carrier",
					Derive(func(b *Argument) {
						b.Do(Simp(Fwd(set_image.ImageSubsetIff.Inst(TypeBinder.BindA[A](), TypeBinder.BindB[B]()))))
						x := b.MemberOf[on.F](b.FixAs[A]("x"), b.Assume())
						b.Show(
							"the ring map carries F into G",
							By(x, MapIn.Read(hom).AsFact().At(x)))
					})),
				Case(
					"the target zero is the image of the source zero",
					By(
						Normalized,
						MapZero.Read(hom),
						comm_ring.ZeroIn.Read(source),
						set_image.FunInImage.At(f, fCarrier, a.TermAs[A]("F.zero")))),
				Case(
					"the target one is the image of the source one",
					By(
						Normalized,
						MapOne.Read(hom),
						comm_ring.OneIn.Read(source),
						set_image.FunInImage.At(f, fCarrier, a.TermAs[A]("F.one")))),
				Case(
					"a sum of images is the image of the sum",
					Derive(func(b *Argument) {
						b.Do(Simp(Fwd(set_image.ForallInImagePair.Inst(TypeBinder.BindA[A](), TypeBinder.BindB[B]()))))
						x, y := b.FixAs[A]("x"), b.FixAs[A]("y")
						members := b.Conjuncts(
							b.Assume(),
							"x lies in F",
							"y lies in F")
						xF, yF := b.MemberOf[on.F](x, members[0]), b.MemberOf[on.F](y, members[1])
						sum := comm_ring.AddIn.Read(source).At(xF, yF)
						b.Show(
							"f keeps the sum",
							By(
								Normalized,
								xF,
								yF,
								sum,
								set_image.FunInImage.At(f, fCarrier, sum),
								MapAdd.Read(hom).AsFact().At(xF, yF)))
					})),
				Case(
					"the negative of an image is the image of the negative",
					Derive(func(b *Argument) {
						b.Do(Simp(Fwd(set_image.ForallInImage.Inst(TypeBinder.BindA[A](), TypeBinder.BindB[B]()))))
						x := b.MemberOf[on.F](b.FixAs[A]("x"), b.Assume())
						negative := comm_ring.NegIn.Read(source).At(x)
						b.Show(
							"f keeps the negative, as a homomorphism of the additive groups",
							By(
								Normalized,
								x,
								negative,
								set_image.FunInImage.At(f, fCarrier, negative),
								MapNeg.Read(hom).AsFact().At(x)))
					})),
				Case(
					"a product of images is the image of the product",
					Derive(func(b *Argument) {
						b.Do(Simp(Fwd(set_image.ForallInImagePair.Inst(TypeBinder.BindA[A](), TypeBinder.BindB[B]()))))
						x, y := b.FixAs[A]("x"), b.FixAs[A]("y")
						members := b.Conjuncts(
							b.Assume(),
							"x lies in F",
							"y lies in F")
						xF, yF := b.MemberOf[on.F](x, members[0]), b.MemberOf[on.F](y, members[1])
						product := comm_ring.MulIn.Read(source).At(xF, yF)
						b.Show(
							"f keeps the product",
							By(
								Normalized,
								xF,
								yF,
								product,
								set_image.FunInImage.At(f, fCarrier, product),
								MapMul.Read(hom).AsFact().At(xF, yF)))
					})),
				Case(
					"the inverse of an image is the image of the inverse",
					Derive(func(b *Argument) {
						b.Do(Simp(Fwd(set_image.ForallInImage.Inst(TypeBinder.BindA[A](), TypeBinder.BindB[B]()))))
						x := b.MemberOf[on.F](b.FixAs[A]("x"), b.Assume())
						reciprocal := field.InvIn.Read(F).At(x)
						b.Show(
							"f keeps the inverse",
							By(Normalized, x, reciprocal, inverse.At(x), set_image.FunInImage.At(f, fCarrier, reciprocal)))
					}))))
	}),
})}

// FieldHomomorphismInjective — a ring homomorphism between two fields is
// one-to-one. Were a nonzero x sent to zero, its inverse would carry the
// target's one, the image of x⁻¹·x, to f(x⁻¹)·0 = 0; so only zero maps to
// zero, and a homomorphism of the additive groups whose kernel is {0} is
// one-to-one.
var FieldHomomorphismInjective = fieldHomomorphismInjectiveThm{family.Add(registry.ProofEntry{
	Name: "FieldHomomorphismInjective",
	Key:  "prop_701a6d996df0fd7",
	Build: family.Theorem(Statement{
		Binders:    "∀F:field_on(A). ∀G:field_on(B). ∀f:(A → B).",
		Hypotheses: []string{"ring_homomorphism(field_ring(F), field_ring(G), f)"},
		Conclusion: "injective_on(F.carrier, f)",
	}, func(a *Argument, F field.FieldFact[on.F], G field.FieldFact[on.G], f *Arrow[A, B], hom Fact) {
		onlyZero := a.Have(
			"only zero maps to zero",
			"∀x:A. x ∈ F.carrier ∧ f(x) = G.zero ⇒ x = F.zero",
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				given := b.Conjuncts(
					b.Assume(),
					"x lies in F",
					"f sends x to zero")
				xF := b.MemberOf[on.F](x, given[0])
				invX := field.InvIn.Read(F).At(xF)
				nonzero := b.SupposeNot()
				oneIsZero := b.Have(
					"the one of G would be its zero",
					"G.one = G.zero",
					CalcEq(
						Leg(
							b.TermAs[B]("f(F.one)"),
							"f keeps the one",
							By(MapOne.Read(hom))),
						Leg(
							b.TermAs[B]("f(F.mul(F.inv(x), x))"),
							"the inverse of the nonzero x multiplies it to one",
							By(Normalized, nonzero, xF, field.MulLeftInverseOn.Read(F).At(xF))),
						Leg(
							b.TermAs[B]("G.mul(f(F.inv(x)), f(x))"),
							"f keeps the product",
							By(xF, invX, MapMul.Read(hom).AsFact().At(invX, xF))),
						Leg(
							b.TermAs[B]("G.mul(f(F.inv(x)), G.zero)"),
							"f sends x to zero",
							By(Normalized, given[1])),
						FinalLeg(
							"zero absorbs a product",
							By(
								invX,
								MapIn.Read(hom).AsFact().At(invX),
								comm_ring.MulRightZeroOn.Read(field.RingOn.Read(G)).AsFact().At(b.TermAs[B]("f(F.inv(x))")))),
					))
				b.Show(
					"a field's one is not its zero",
					By(oneIsZero, field.OneNotZeroOn.Read(G)))
			}))
		kernel := a.Have(
			"the kernel of f is {zero}",
			"group_kernel(G.zero, F.carrier, f) = {F.zero}",
			Unfold(group_homomorphism.GroupKernelDef),
			BySets(onlyZero, MapZero.Read(hom), comm_ring.ZeroIn.Read(field.RingOn.Read(F))))
		a.Show(
			"a homomorphism of the additive groups with trivial kernel is one-to-one",
			By(kernel, group_homomorphism.KernelTrivialIffInjective.Read(AdditiveHomomorphism.Read(hom))))
	}),
})}

// SubfieldHomomorphismEmbedding — a ring homomorphism out of a subfield k of
// M into a field L embeds k: σ(k) is a subfield of L and σ is one-to-one on
// k. Under M's operations k is a field, whose ring is M's ring restricted to
// k, and a homomorphism between two fields has a subfield for its image
// (ImageSubfield) and is one-to-one (FieldHomomorphismInjective).
var SubfieldHomomorphismEmbedding = subfieldHomomorphismEmbeddingThm{family.Add(registry.ProofEntry{
	Name: "SubfieldHomomorphismEmbedding",
	Key:  "prop_70d1e18cd9cc67bc",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀L:field_on(B). ∀k:set(A). ∀σ:(A → B).",
		Hypotheses: []string{
			"subfield(M, k)",
			"ring_homomorphism(restrict_ring(field_ring(M), k), field_ring(L), σ)",
		},
		Conclusion: "subfield(L, image(σ, k)) ∧ injective_on(k, σ)",
	}, func(
		a *Argument,
		M field.FieldFact[on.M],
		L field.FieldFact[on.L],
		k *Expr[Set[A]],
		σ *Arrow[A, B],
		subfield, hom Fact,
	) {
		kField := a.TermAs[field.FieldOps[A]]("restrict_field(M, k)")
		l := a.TermAs[field.FieldOps[B]]("L")
		a.Show(
			"k is a field under M's operations and σ a homomorphism of fields "+
				"out of it, which has a subfield for its image and is one-to-one",
			By(
				L,
				subfield,
				hom,
				field.SubfieldFieldOn.Read(M).At(k),
				field.RestrictFieldRing.At(a.TermAs[field.FieldOps[A]]("M"), k),
				ImageSubfield.At(kField, l, σ),
				FieldHomomorphismInjective.At(kField, l, σ),
				field.RestrictFieldDef))
	}),
})}

// RingHomIdentity — the identity of a commutative ring on c is a ring
// homomorphism from the ring to itself. Both ring conditions of the
// definition are the hypothesis, and at λx. x its four map conditions are identities:
// x ∈ c ⇒ x ∈ c, x + y = x + y, x * y = x * y and one = one.
var RingHomIdentity = ringHomIdentityThm{family.Add(registry.ProofEntry{
	Name: "RingHomIdentity",
	Key:  "prop_caf505500be1aacc",
	Reading: "Both ring facts in ring_homomorphism are the hypothesis itself: the source and " +
		"the target are the one commutative ring on c. It discharges the ring-map hypothesis on λx. " +
		"x wherever a statement that takes a ring map is read at the identity, as the cotangent " +
		"complex with coefficients in a module over S itself is, at (R, S, f, S, λx. x, N).",
	Build: comm_ring.CommRingOn.Law("ring_homomorphism(R, R, λx:A. x)",
		func(a *Argument, _ comm_ring.CommRingFact[on.R]) {
			a.Show(
				"unfolded at the identity, the definition closes on the ring on c",
				Unfold(RingHomomorphism))
		}),
})}

// PreimageIdeal — the preimage of an ideal of the target under a ring
// homomorphism is an ideal of the source. The preimage lies in c by its
// definition; φ sends zero to zero', which the ideal holds; φ sends x + y
// to φ(x) + φ(y), a sum of two members of the ideal; and φ sends r * x to
// φ(r) * φ(x), which the ideal absorbs since φ(r) lies in c'.
var PreimageIdeal = preimageIdealThm{family.Add(registry.ProofEntry{
	Name: "PreimageIdeal",
	Key:  "prop_9b8e766619ddda4",
	Build: family.Theorem(Statement{
		Binders: "∀φ:ring_homomorphism(A, B). ∀I:set(B).",
		Hypotheses: []string{
			"ring_ideal(S, I)",
		},
		Conclusion: "ring_ideal(R, preimage_on(R.carrier, φ, I))",
	},
		func(a *Argument, φ RingHomomorphismFact[on.R, on.S], I *Expr[Set[B]], ideal Fact) {
			source := Source.Read(φ)
			inC := a.Have(
				"the preimage lies in c",
				"preimage_on(R.carrier, φ, I) ⊆ R.carrier",
				BySets())
			zeroIn := a.Have(
				"φ sends zero to zero', which I holds",
				"R.zero ∈ preimage_on(R.carrier, φ, I)",
				BySets(comm_ring.ZeroIn.Read(source), MapZero.Read(φ), ring_ideal.IdealZero.Read(ideal)))
			sums := a.Have(
				"φ sends a sum to the sum of the images, which I holds",
				Statement{
					Binders: "∀x y:A.",
					Hypotheses: []string{
						"x ∈ preimage_on(R.carrier, φ, I)",
						"y ∈ preimage_on(R.carrier, φ, I)",
					},
					Conclusion: "x + y ∈ preimage_on(R.carrier, φ, I)",
				},
				Derive(func(b *Argument) {
					x := b.FixAs[A]("x")
					y := b.FixAs[A]("y")
					members := b.Assume()
					b.Show(
						"x + y lies in c, and φ sends it into I",
						BySets(
							members,
							At(comm_ring.AddIn.Read(source), x, y),
							At(MapAdd.Read(φ), x, y),
							At(ring_ideal.IdealAdd.Read(ideal), b.TermAs[B]("φ(x)"), b.TermAs[B]("φ(y)"))))
				}))
			products := a.Have(
				"φ sends r * x to φ(r) * φ(x), which I absorbs since φ(r) lies in c'",
				"∀r x:A. r ∈ R.carrier ∧ x ∈ preimage_on(R.carrier, φ, I) ⇒ r * x ∈ preimage_on(R.carrier, φ, I)",
				Derive(func(b *Argument) {
					r := b.FixAs[A]("r")
					x := b.FixAs[A]("x")
					members := b.Assume()
					b.Show(
						"r * x lies in c, and φ sends it into I",
						BySets(
							members,
							At(comm_ring.MulIn.Read(source), r, x),
							At(MapMul.Read(φ), r, x),
							At(MapIn.Read(φ), r),
							At(ring_ideal.IdealMul.Read(ideal), b.TermAs[B]("φ(r)"), b.TermAs[B]("φ(x)"))))
				}))
			a.Show(
				"these are the conditions defining an ideal of the source",
				By(inC, zeroIn, sums, products, ring_ideal.RingIdealDef))
		}),
})}

// IdealSpanImage — a ring isomorphism takes the ideal a set E spans to the
// ideal the image of E spans. The ideal f(E) spans pulls back along f to an
// ideal of R holding E (PreimageIdeal), so holding the ideal E spans, whose
// image therefore lies in it; and the ideal E spans pulls back along the
// inverse of f to an ideal of T holding f(E), so holding the ideal f(E)
// spans, each member y of which is f of a member of the ideal E spans, as f
// undoes its inverse on T.
var IdealSpanImage = idealSpanImageThm{family.Add(registry.ProofEntry{
	Name: "IdealSpanImage",
	Key:  "prop_17fe32c2a79ceb65",
	Reading: "E ⊆ R.carrier is load-bearing: a set reaching outside R is held by no ideal of R, " +
		"so the ideal it spans is the whole type, while f, unconstrained off R, may carry it into T. " +
		"That f is one to one serves only the proof's route, which pulls the ideal E spans back along " +
		"the inverse of f: a ring homomorphism onto T already carries an ideal of R to an ideal of T.",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀T:ring_ops(B). ∀f:(A → B). ∀E:set(A).",
		Hypotheses: []string{
			"ring_isomorphism(R, T, f)",
			"E ⊆ R.carrier",
		},
		Conclusion: "image(f, ideal_span(R, E)) = ideal_span(T, image(f, E))",
	}, func(
		a *Argument,
		R *Expr[RingOps[A]],
		T *Expr[RingOps[B]],
		f *Arrow[A, B],
		E *Expr[Set[A]],
		iso, inR Fact,
	) {
		parts := a.Conjuncts(
			a.Unfolded(iso, RingIsomorphismDef),
			"f is a ring homomorphism",
			"one to one on R",
			"onto T")
		hom, oneToOne, onto := parts[0], parts[1], parts[2]
		carrierR := a.TermAs[Set[A]]("R.carrier")
		spanR := a.TermAs[Set[A]]("ideal_span(R, E)")
		imageE := a.TermAs[Set[B]]("image(f, E)")
		spanT := a.TermAs[Set[B]]("ideal_span(T, image(f, E))")
		inverseHom := a.Conjuncts(
			a.Unfolded(GroupPremises(iso, IsomorphismInverse.At(R, T, f)), RingIsomorphismDef),
			"the inverse of f on R is a ring homomorphism of T to R",
			"one to one on T",
			"onto R")[0]
		idealR := a.Have(
			"E spans an ideal of R",
			"ring_ideal(R, ideal_span(R, E))",
			By(inR, ring_ideal.SpanIdeal.Read(Source.Read(hom))))
		imageInT := a.Have(
			"f(E) lies in T",
			"image(f, E) ⊆ T.carrier",
			By(inR, MapIn.Read(hom), set_image.ImageSubsetIff, set_basic.SubsetDef))
		idealT := a.Have(
			"f(E) spans an ideal of T",
			"ring_ideal(T, ideal_span(T, image(f, E)))",
			By(imageInT, ring_ideal.SpanIdeal.Read(Target.Read(hom))))
		eInPullback := a.Have(
			"E lies in the pullback along f of the ideal f(E) spans",
			"E ⊆ preimage_on(R.carrier, f, ideal_span(T, image(f, E)))",
			BySets(inR, ring_ideal.SpanContains.At(T, imageE)))
		pulled := a.Have(
			"that pullback is an ideal of R, so it holds the ideal E spans",
			"ideal_span(R, E) ⊆ preimage_on(R.carrier, f, ideal_span(T, image(f, E)))",
			By(
				idealT,
				eInPullback,
				PreimageIdeal.Read(hom).At(spanT),
				ring_ideal.SpanLeast.At(
					R, E, a.TermAs[Set[A]]("preimage_on(R.carrier, f, ideal_span(T, image(f, E)))"))))
		imageInPullback := a.Have(
			"f(E) lies in the pullback along the inverse of the ideal E spans, the inverse undoing f on R",
			"image(f, E) ⊆ preimage_on(T.carrier, inverse_on(R.carrier, f), ideal_span(R, E))",
			BySets(
				inR,
				imageInT,
				oneToOne,
				ring_ideal.SpanContains.At(R, E),
				At(functions.InverseOnLeft, carrierR, f)))
		pushed := a.Have(
			"that pullback is an ideal of T, so it holds the ideal f(E) spans",
			"ideal_span(T, image(f, E)) ⊆ preimage_on(T.carrier, inverse_on(R.carrier, f), ideal_span(R, E))",
			By(
				idealR,
				imageInPullback,
				PreimageIdeal.Read(inverseHom).At(spanR),
				ring_ideal.SpanLeast.At(
					T, imageE, a.TermAs[Set[B]]("preimage_on(T.carrier, inverse_on(R.carrier, f), ideal_span(R, E))"))))
		a.Show(
			"each ideal lies in the other: a member y of the ideal f(E) "+
				"spans is f of its inverse, which lies in the ideal E spans",
			BySets(pulled, pushed, onto, At(functions.InverseOnRight, carrierR, f)))
	}),
})}

// RingHomCompose — the composite of two ring homomorphisms is one. Its
// source is the source ring of the first and its target the target ring
// of the second, each read off its homomorphism; the first carries R
// into S and the second S into Q; and a sum, a product and the one pass
// through φ by φ's law and then through χ by χ's, the images lying in S.
var RingHomCompose = ringHomComposeThm{family.Add(registry.ProofEntry{
	Name: "RingHomCompose",
	Key:  "prop_a3cff188597addfe",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀Q:ring_ops(C). ∀φ:(A → B). ∀χ:(B → C).",
		Hypotheses: []string{
			"ring_homomorphism(R, S, φ)",
			"ring_homomorphism(S, Q, χ)",
		},
		Conclusion: "ring_homomorphism(R, Q, λa:A. χ(φ(a)))",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			S *Expr[RingOps[B]],
			Q *Expr[RingOps[C]],
			φ *Arrow[A, B],
			χ *Arrow[B, C],
			hypotheses Fact,
		) {
			parts := a.Conjuncts(
				hypotheses,
				"φ is a ring homomorphism from R to S",
				"χ is a ring homomorphism from S to Q")
			homφ, homχ := parts[0], parts[1]
			a.Show(
				"χ ∘ φ meets each condition of a ring homomorphism from R to Q",
				Simp(Fwd(RingHomomorphism)),
				SplitConjAll(
					Case(
						"its source is the ring R, φ's source",
						By(Source.Read(homφ))),
					Case(
						"its target is the ring Q, χ's target",
						By(Target.Read(homχ))),
					Case(
						"φ carries R into S, and χ carries S into Q",
						By(MapIn.Read(homφ), MapIn.Read(homχ))),
					Case(
						"φ keeps the sum x + y, and χ the sum of the images, which lie in S",
						Derive(func(b *Argument) {
							b.FixAs[A]("x")
							b.FixAs[A]("y")
							b.Assume()
							b.Show(
								"split the sum by φ's law, then the sum of the images by χ's",
								Simp(Fwd(MapAdd.Read(homφ)), Fwd(MapAdd.Read(homχ)), Fwd(MapIn.Read(homφ))),
								Refl())
						})),
					Case(
						"φ keeps the product x * y, and χ the product of the images, which lie in S",
						Derive(func(b *Argument) {
							b.FixAs[A]("x")
							b.FixAs[A]("y")
							b.Assume()
							b.Show(
								"split the product by φ's law, then the product of the images by χ's",
								Simp(Fwd(MapMul.Read(homφ)), Fwd(MapMul.Read(homχ)), Fwd(MapIn.Read(homφ))),
								Refl())
						})),
					Case(
						"φ sends one to the one of S, and χ sends that to the one of Q",
						By(Normalized, MapOne.Read(homφ), MapOne.Read(homχ))),
				))
		}),
})}

// RingHomRestrictSource — a ring map restricts to a subring of its source: the
// conditions on a smaller carrier are read off those on the whole one.
var RingHomRestrictSource = ringHomRestrictSourceThm{family.Add(registry.ProofEntry{
	Name: "RingHomRestrictSource",
	Key:  "prop_c3b0568c488f403d",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B). ∀T:set(A).",
		Hypotheses: []string{
			"ring_homomorphism(R, S, f)",
			"subring(R, T)",
		},
		Conclusion: "ring_homomorphism(restrict_ring(R, T), S, f)",
	}, func(
		a *Argument,
		R *Expr[RingOps[A]],
		S *Expr[RingOps[B]],
		f *Arrow[A, B],
		T *Expr[Set[A]],
		hom, sub Fact,
	) {
		ring := Source.Read(hom)
		rings := a.Have(
			"T is a commutative ring inside R",
			"comm_ring_on(restrict_ring(R, T)) ∧ T ⊆ R.carrier",
			By(sub, ring, comm_ring.SubringRingOn.At(R, T)))
		a.Show(
			"each condition on T is the condition on R read at elements of T",
			Simp(Fwd(RingHomomorphism)),
			BySets(hom, rings, RingHomomorphism.At(R, S, f)))
	}),
})}

// SubringInclusionHom — a subring includes into its ring as a ring
// homomorphism: the identity of the ring is one, and it restricts to the
// subring.
var SubringInclusionHom = subringInclusionHomThm{family.Add(registry.ProofEntry{
	Name: "SubringInclusionHom",
	Key:  "prop_b23d2d30b04cac34",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀T:set(A).",
		Hypotheses: []string{
			"subring(R, T)",
		},
		Conclusion: "ring_homomorphism(restrict_ring(R, T), R, λa:A. a)",
	},
		func(a *Argument, ring comm_ring.CommRingFact[on.R], T *Expr[Set[A]], subring Fact) {
			R := a.TermAs[RingOps[A]]("R")
			a.Show(
				"the identity of R is a ring homomorphism, and it restricts to the subring T",
				By(
					subring,
					RingHomIdentity.Read(ring),
					RingHomRestrictSource.At(R, R, a.TermAs[Fun[A, A]]("λa:A. a"), T)))
		}),
})}

// RingHomCorestrict — a homomorphism whose values lie in a subring T of S
// is a homomorphism into T, under S's operations: T is then a ring, and a
// sum, a product or the one in T is the one in S.
var RingHomCorestrict = ringHomCorestrictThm{family.Add(registry.ProofEntry{
	Name: "RingHomCorestrict",
	Key:  "prop_8c6caf5a3ec6e18f",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B). ∀T:set(B).",
		Hypotheses: []string{
			"ring_homomorphism(R, S, f)",
			"subring(S, T)",
			"∀x:A. x ∈ R.carrier ⇒ f(x) ∈ T",
		},
		Conclusion: "ring_homomorphism(R, restrict_ring(S, T), f)",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			S *Expr[RingOps[B]],
			f *Arrow[A, B],
			T *Expr[Set[B]],
			given Fact,
		) {
			parts := a.Conjuncts(
				given,
				"f is a homomorphism of R into S",
				"T is a subring of S",
				"f carries R into T")
			hom, subring, into := parts[0], parts[1], parts[2]
			target := a.Have(
				"T under S's operations is a ring",
				"comm_ring_on(restrict_ring(S, T))",
				By(subring, comm_ring.SubringRingOn.Read(Target.Read(hom)).At(T)))
			a.Show(
				"R and T are rings, f carries R into T, and its sums, products and one are S's",
				Simp(Fwd(RingHomomorphism)),
				By(Source.Read(hom), target, into, MapAdd.Read(hom), MapMul.Read(hom), MapOne.Read(hom)))
		}),
})}

// RingHomExtendTarget — a homomorphism into a subset T of a ring S's
// carrier, under S's operations, is a homomorphism into S: its values
// lie in T, so in S.carrier, and T's operations are S's.
var RingHomExtendTarget = ringHomExtendTargetThm{family.Add(registry.ProofEntry{
	Name: "RingHomExtendTarget",
	Key:  "prop_b911666a79d542a5",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B). ∀T:set(B).",
		Hypotheses: []string{
			"ring_homomorphism(R, restrict_ring(S, T), f)",
			"comm_ring_on(S)",
			"T ⊆ S.carrier",
		},
		Conclusion: "ring_homomorphism(R, S, f)",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			S *Expr[RingOps[B]],
			f *Arrow[A, B],
			T *Expr[Set[B]],
			given Fact,
		) {
			parts := a.Conjuncts(
				given,
				"f is a homomorphism of R into T",
				"S is a ring",
				"T lies in S.carrier")
			hom, ring, inside := parts[0], parts[1], parts[2]
			a.Show(
				"R and S are rings, f's values lie in T and so in "+
					"S.carrier, and T's sums, products and one are S's",
				Simp(Fwd(RingHomomorphism)),
				BySets(
					Source.Read(hom),
					ring,
					inside,
					MapIn.Read(hom),
					MapAdd.Read(hom),
					MapMul.Read(hom),
					MapOne.Read(hom)))
		}),
})}

// RingHomCongruence — a homomorphism reads only its values on the carrier:
// a map agreeing with one on R.carrier is one, since R.carrier holds the
// sums, the products and the one that the homomorphism laws evaluate at.
var RingHomCongruence = ringHomCongruenceThm{family.Add(registry.ProofEntry{
	Name: "RingHomCongruence",
	Key:  "prop_e61ed70bfa894def",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀u v:(A → B).",
		Hypotheses: []string{
			"ring_homomorphism(R, S, u)",
			"∀x:A. x ∈ R.carrier ⇒ v(x) = u(x)",
		},
		Conclusion: "ring_homomorphism(R, S, v)",
	},
		func(a *Argument, R *Expr[RingOps[A]], S *Expr[RingOps[B]], u, v *Arrow[A, B], hom, agree Fact) {
			ring := Source.Read(hom)
			a.Show(
				"on R.carrier v has the values of u, whose laws therefore hold of v",
				Simp(Fwd(RingHomomorphism)),
				SplitConjAll(
					Case(
						"R is a ring",
						By(ring)),
					Case(
						"S is a ring",
						By(Target.Read(hom))),
					Case(
						"v carries R into S",
						By(Normalized, agree, MapIn.Read(hom))),
					Case(
						"v keeps the sum",
						By(agree, MapAdd.Read(hom), comm_ring.AddIn.Read(ring))),
					Case(
						"v keeps the product",
						By(agree, MapMul.Read(hom), comm_ring.MulIn.Read(ring))),
					Case(
						"v keeps the one",
						By(Normalized, agree, MapOne.Read(hom), comm_ring.OneIn.Read(ring)))))
		}),
})}

// RingIsomorphismDef — `ring_isomorphism(R, S, f)`: a homomorphism
// that is injective on c and carries c onto c'.
var RingIsomorphismDef = ringIsomorphismDefThm{family.Define(registry.DefEntry{
	Name:     "RingIsomorphismDef",
	Key:      "prop_b8a2d13a5b56b616",
	Const:    "ring_isomorphism",
	Type:     "ring_ops(A) → ring_ops(B) → (A → B) → bool",
	Implicit: []string{},
	Bundles:  []string{},
	Equations: []string{
		"∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B). " +
			"    ring_isomorphism(R, S, f) ⇔ " +
			"    ring_homomorphism(R, S, f) ∧ injective_on(R.carrier, f) ∧ image(f, R.carrier) = S.carrier",
	},
	Deps: []registry.EntryLike{RingHomomorphism},
})}

// IsomorphismInverse — the inverse laws and cancellation transport the
// sum, product and one back to the source ring; both rings are read off
// the isomorphism's homomorphism.
var IsomorphismInverse = isomorphismInverseThm{family.Add(registry.ProofEntry{
	Name: "IsomorphismInverse",
	Key:  "prop_c6cfa635b57fe415",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B).",
		Hypotheses: []string{
			"ring_isomorphism(R, S, f)",
		},
		Conclusion: "ring_isomorphism(S, R, inverse_on(R.carrier, f))",
	},
		func(a *Argument, R *Expr[RingOps[A]], S *Expr[RingOps[B]], f *Arrow[A, B], iso Fact) {
			r, s := a.TermAs[Set[A]]("R.carrier"), a.TermAs[Set[B]]("S.carrier")
			inverse := a.TermAs[Fun[B, A]]("inverse_on(R.carrier, f)")
			isomorphismProperties := a.Have(
				"the isomorphism is a homomorphism and a bijection",
				"ring_homomorphism(R, S, f) ∧ injective_on(R.carrier, f) ∧ image(f, R.carrier) = S.carrier",
				By(iso, RingIsomorphismDef))
			hom := a.Have(
				"f preserves the ring operations",
				"ring_homomorphism(R, S, f)",
				By(isomorphismProperties))
			sourceRing, targetRing := Source.Read(hom), Target.Read(hom)
			inversePreimages := a.Have(
				"the inverse returns a preimage in R for every point of S",
				Statement{
					Binders: "∀y:B.",
					Hypotheses: []string{
						"y ∈ S.carrier",
					},
					Conclusion: "inverse_on(R.carrier, f, y) ∈ R.carrier ∧ f(inverse_on(R.carrier, f, y)) = y",
				},
				Derive(func(b *Argument) {
					y := b.FixAs[B]("y")
					inTarget := b.Assume()
					b.Show(
						"surjectivity supplies the carrier and right inverse laws",
						By(
							Normalized,
							inTarget,
							isomorphismProperties,
							functions.InverseOnIn.At(r, f, y),
							functions.InverseOnRight.At(r, f, y)))
				}))
			leftInverse := a.Have(
				"the inverse undoes f on R",
				"∀x:A. x ∈ R.carrier ⇒ inverse_on(R.carrier, f, f(x)) = x",
				By(isomorphismProperties, Where(functions.InverseOnLeft, "c", r).Where("f", f)))
			preservesAddition := a.Have(
				"the inverse preserves addition",
				Statement{
					Binders: "∀y z:B.",
					Hypotheses: []string{
						"y ∈ S.carrier",
						"z ∈ S.carrier",
					},
					Conclusion: "inverse_on(R.carrier, f, y + z) = " +
						"inverse_on(R.carrier, f, y) + inverse_on(R.carrier, f, z)",
				},
				Derive(func(b *Argument) {
					y, z := b.FixAs[B]("y"), b.FixAs[B]("z")
					members := b.Assume()
					preimages := b.Have(
						"the two preimages lie in R and map to y and z",
						"inverse_on(R.carrier, f, y) ∈ R.carrier ∧ "+
							"inverse_on(R.carrier, f, z) ∈ R.carrier ∧ "+
							"f(inverse_on(R.carrier, f, y)) = y ∧ "+
							"f(inverse_on(R.carrier, f, z)) = z",
						By(members, inversePreimages.At(y), inversePreimages.At(z)))
					closed := b.Have(
						"the sums belong to their respective rings",
						"y + z ∈ S.carrier ∧ inverse_on(R.carrier, f, y) + inverse_on(R.carrier, f, z) ∈ R.carrier",
						By(comm_ring.AddIn.Read(sourceRing), comm_ring.AddIn.Read(targetRing), members, preimages))
					image := b.Have(
						"f sends the sum of the preimages to y + z",
						"f(inverse_on(R.carrier, f, y) + inverse_on(R.carrier, f, z)) = y + z",
						By(
							preimages,
							MapAdd.Read(hom).AsFact().At(
								b.TermAs[A]("inverse_on(R.carrier, f, y)"), b.TermAs[A]("inverse_on(R.carrier, f, z)"))))
					b.Show(
						"injectivity identifies the preimage of the sum",
						By(
							image,
							closed,
							inversePreimages.At(b.TermAs[B]("y + z")),
							isomorphismProperties,
							functions.InjectiveOnDef.At(r, f)))
				}))
			preservesMultiplication := a.Have(
				"the inverse preserves multiplication",
				Statement{
					Binders: "∀y z:B.",
					Hypotheses: []string{
						"y ∈ S.carrier",
						"z ∈ S.carrier",
					},
					Conclusion: "inverse_on(R.carrier, f, y * z) = " +
						"inverse_on(R.carrier, f, y) * inverse_on(R.carrier, f, z)",
				},
				Derive(func(b *Argument) {
					y, z := b.FixAs[B]("y"), b.FixAs[B]("z")
					members := b.Assume()
					preimages := b.Have(
						"the two preimages lie in R and map to y and z",
						"inverse_on(R.carrier, f, y) ∈ R.carrier ∧ "+
							"inverse_on(R.carrier, f, z) ∈ R.carrier ∧ "+
							"f(inverse_on(R.carrier, f, y)) = y ∧ "+
							"f(inverse_on(R.carrier, f, z)) = z",
						By(members, inversePreimages.At(y), inversePreimages.At(z)))
					closed := b.Have(
						"the products belong to their respective rings",
						"y * z ∈ S.carrier ∧ inverse_on(R.carrier, f, y) * inverse_on(R.carrier, f, z) ∈ R.carrier",
						By(comm_ring.MulIn.Read(sourceRing), comm_ring.MulIn.Read(targetRing), members, preimages))
					image := b.Have(
						"f sends the product of the preimages to y * z",
						"f(inverse_on(R.carrier, f, y) * inverse_on(R.carrier, f, z)) = y * z",
						By(
							preimages,
							MapMul.Read(hom).AsFact().At(
								b.TermAs[A]("inverse_on(R.carrier, f, y)"), b.TermAs[A]("inverse_on(R.carrier, f, z)"))))
					b.Show(
						"injectivity identifies the preimage of the product",
						By(
							image,
							closed,
							inversePreimages.At(b.TermAs[B]("y * z")),
							isomorphismProperties,
							functions.InjectiveOnDef.At(r, f)))
				}))
			preservesOne := a.Have(
				"the inverse preserves one",
				"inverse_on(R.carrier, f, S.one) = R.one",
				By(
					Normalized,
					comm_ring.OneIn.Read(sourceRing),
					MapOne.Read(hom),
					leftInverse.At(a.TermAs[A]("R.one"))))
			bijection := a.Have(
				"the two inverse laws make the inverse a bijection from S to R",
				"injective_on(S.carrier, inverse_on(R.carrier, f)) ∧ "+
					"image(inverse_on(R.carrier, f), S.carrier) = R.carrier",
				By(
					MapIn.Read(hom),
					leftInverse,
					inversePreimages,
					functions.TwoSidedInverseBijection.At(s, r, inverse, f)))
			inverseHom := a.Have(
				"the inverse is a ring homomorphism from S to R",
				"ring_homomorphism(S, R, inverse_on(R.carrier, f))",
				Simp(Fwd(RingHomomorphism)),
				By(
					preservesAddition,
					preservesMultiplication,
					inversePreimages,
					preservesOne,
					sourceRing,
					targetRing))
			// The bijection's two conjuncts are taken before the unfolding,
			// whose tidy splits the conjunction.
			laws := a.Conjuncts(
				bijection,
				"the inverse is one-to-one on S.carrier",
				"and carries S.carrier onto R.carrier")
			a.Show(
				"the inverse homomorphism and bijection give the inverse isomorphism",
				Unfold(RingIsomorphismDef),
				By(inverseHom, laws[0], laws[1]))
		}),
})}

// ImageSubring — the image of a ring map is a subring of the target: its sums,
// negatives, products, zero and one are the values at the sums, negatives,
// products, zero and one of the source.
var ImageSubring = imageSubringThm{family.Add(registry.ProofEntry{
	Name: "ImageSubring",
	Key:  "prop_824b081e8f1ad9cb",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀T:ring_ops(B). ∀φ:(A → B).",
		Hypotheses: []string{
			"ring_homomorphism(R, T, φ)",
		},
		Conclusion: "subring(T, image(φ, R.carrier))",
	}, func(a *Argument, R *Expr[RingOps[A]], T *Expr[RingOps[B]], φ *Arrow[A, B], hom Fact) {
		source := Source.Read(hom)
		carrier := a.TermAs[Set[A]]("R.carrier")
		into := a.Have(
			"φ maps into T",
			"image(φ, R.carrier) ⊆ T.carrier",
			BySets(MapIn.Read(hom)))
		zero := a.Have(
			"zero is the value at zero",
			"T.zero ∈ image(φ, R.carrier)",
			By(
				Normalized,
				MapZero.Read(hom),
				comm_ring.ZeroIn.Read(source),
				set_image.FunInImage.At(φ, carrier, a.TermAs[A]("R.zero"))))
		one := a.Have(
			"one is the value at one",
			"T.one ∈ image(φ, R.carrier)",
			By(
				Normalized,
				MapOne.Read(hom),
				comm_ring.OneIn.Read(source),
				set_image.FunInImage.At(φ, carrier, a.TermAs[A]("R.one"))))
		sums := a.Have(
			"a sum of values is the value of the sum",
			"∀x y:A. x ∈ R.carrier ∧ y ∈ R.carrier ⇒ T.add(φ(x), φ(y)) ∈ image(φ, R.carrier)",
			Derive(func(b *Argument) {
				b.FixAs[A]("x")
				b.FixAs[A]("y")
				members := b.Assume()
				b.Show(
					"φ keeps the sum, and the sum lies in R",
					By(
						members,
						MapAdd.Read(hom),
						comm_ring.AddIn.Read(source),
						set_image.FunInImage.At(φ, carrier, b.TermAs[A]("R.add(x, y)"))))
			}))
		negatives := a.Have(
			"a negative of a value is the value of the negative",
			"∀x:A. x ∈ R.carrier ⇒ T.neg(φ(x)) ∈ image(φ, R.carrier)",
			Derive(func(b *Argument) {
				b.FixAs[A]("x")
				member := b.Assume()
				b.Show(
					"φ keeps the negative, and the negative lies in R",
					By(
						Normalized,
						member,
						group_homomorphism.MapInv.Read(AdditiveHomomorphism.Read(hom)),
						comm_ring.NegIn.Read(source),
						set_image.FunInImage.At(φ, carrier, b.TermAs[A]("R.neg(x)"))))
			}))
		products := a.Have(
			"a product of values is the value of the product",
			"∀x y:A. x ∈ R.carrier ∧ y ∈ R.carrier ⇒ T.mul(φ(x), φ(y)) ∈ image(φ, R.carrier)",
			Derive(func(b *Argument) {
				b.FixAs[A]("x")
				b.FixAs[A]("y")
				members := b.Assume()
				b.Show(
					"φ keeps the product, and the product lies in R",
					By(
						members,
						MapMul.Read(hom),
						comm_ring.MulIn.Read(source),
						set_image.FunInImage.At(φ, carrier, b.TermAs[A]("R.mul(x, y)"))))
			}))
		a.Show(
			"read through its values, the image meets every condition of a subring",
			Simp(Fwd(comm_ring.SubringDef), Fwd(set_image.ForallInImagePair), Fwd(set_image.ForallInImage)),
			By(into, zero, one, sums, negatives, products))
	}),
})}

// KernelFactorization — a ring map v killing the kernel of a ring map u factors
// through the image of u: h reads v at a chosen preimage, two preimages of one point
// differing by a point of the kernel of u, which v kills.
var KernelFactorization = kernelFactorizationThm{family.Add(registry.ProofEntry{
	Name: "KernelFactorization",
	Key:  "prop_8455e3beceb2ac99",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀T:ring_ops(C). ∀u:(A → B). ∀v:(A → C).",
		Hypotheses: []string{
			"ring_homomorphism(R, S, u)",
			"ring_homomorphism(R, T, v)",
			"∀x:A. x ∈ R.carrier ∧ u(x) = S.zero ⇒ v(x) = T.zero",
		},
		Conclusion: "∃h:(B → C). " +
			"    ring_homomorphism(restrict_ring(S, image(u, R.carrier)), T, h) ∧ " +
			"    (∀x:A. x ∈ R.carrier ⇒ h(u(x)) = v(x))",
	}, func(
		a *Argument,
		R *Expr[RingOps[A]],
		S *Expr[RingOps[B]],
		T *Expr[RingOps[C]],
		u *Arrow[A, B],
		v *Arrow[A, C],
		uHom RingHomomorphismFact[on.R, on.S],
		vHom RingHomomorphismFact[on.R, on.T],
		kernels Fact,
	) {
		h, hDef := a.LetAs[Fun[B, C]]("h", "λy:B. v(inverse_on(R.carrier, u, y))")
		fibers := a.Have(
			"two points with one image under u have one image under v",
			"∀x y:A. x ∈ R.carrier ∧ y ∈ R.carrier ∧ u(x) = u(y) ⇒ v(x) = v(y)",
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				y := b.FixAs[A]("y")
				given := b.Conjuncts(
					b.Assume(),
					"x lies in R",
					"y lies in R",
					"u agrees at x and y")
				xIn, yIn, agree := given[0], given[1], given[2]
				b.Show(
					"their difference lies in the kernel of u, hence in that of v",
					BySets(
						xIn,
						yIn,
						agree,
						kernels,
						group_homomorphism.EqIffInKernel.Read(AdditiveHomomorphism.Read(uHom)).AsFact().At(x, y),
						group_homomorphism.EqIffInKernel.Read(AdditiveHomomorphism.Read(vHom)).AsFact().At(x, y),
						group_homomorphism.GroupKernelDef.At(b.TermAs[B]("ring_zero(S)"), b.TermAs[Set[A]]("R.carrier"), u),
						group_homomorphism.GroupKernelDef.At(
							b.TermAs[C]("ring_zero(T)"), b.TermAs[Set[A]]("R.carrier"), v)))
			}))
		preimages := a.Have(
			"every point of the image has a chosen preimage",
			Statement{
				Binders: "∀y:B.",
				Hypotheses: []string{
					"y ∈ image(u, R.carrier)",
				},
				Conclusion: "inverse_on(R.carrier, u, y) ∈ R.carrier ∧ u(inverse_on(R.carrier, u, y)) = y",
			},
			By(functions.InverseOnIn, functions.InverseOnRight))
		inImage := a.Have(
			"u sends R into its image",
			"∀x:A. x ∈ R.carrier ⇒ u(x) ∈ image(u, R.carrier)",
			BySets())
		values := a.Have(
			"h has the prescribed values",
			"∀x:A. x ∈ R.carrier ⇒ h(u(x)) = v(x)",
			By(Normalized, inImage, hDef, preimages, fibers))
		intoTarget := a.Have(
			"h maps the image into T",
			"∀y:B. y ∈ image(u, R.carrier) ⇒ h(y) ∈ T.carrier",
			By(Normalized, MapIn.Read(vHom), hDef, preimages))
		sumOnImages := a.Have(
			"h carries a sum of images to the sum of the values",
			"∀x z:A. x ∈ R.carrier ∧ z ∈ R.carrier ⇒ h(S.add(u(x), u(z))) = T.add(v(x), v(z))",
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				z := b.FixAs[A]("z")
				inSource := b.Assume()
				b.Show(
					"u and v are additive, and h reads v off u",
					By(
						Normalized,
						inSource,
						At(values, b.TermAs[A]("R.add(x, z)")),
						MapAdd.Read(uHom).AsFact().At(x, z),
						MapAdd.Read(vHom).AsFact().At(x, z),
						comm_ring.AddIn.Read(Source.Read(uHom)).AsFact().At(x, z)))
			}))
		additive := a.Have(
			"h is additive on the image",
			"∀y z:B. y ∈ image(u, R.carrier) ∧ z ∈ image(u, R.carrier) ⇒ h(S.add(y, z)) = T.add(h(y), h(z))",
			By(Normalized, sumOnImages, values, preimages))
		productOnImages := a.Have(
			"h carries a product of images to the product of the values",
			"∀x z:A. x ∈ R.carrier ∧ z ∈ R.carrier ⇒ h(S.mul(u(x), u(z))) = T.mul(v(x), v(z))",
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				z := b.FixAs[A]("z")
				inSource := b.Assume()
				b.Show(
					"u and v are multiplicative, and h reads v off u",
					By(
						Normalized,
						inSource,
						At(values, b.TermAs[A]("R.mul(x, z)")),
						MapMul.Read(uHom).AsFact().At(x, z),
						MapMul.Read(vHom).AsFact().At(x, z),
						comm_ring.MulIn.Read(Source.Read(uHom)).AsFact().At(x, z)))
			}))
		multiplicative := a.Have(
			"h is multiplicative on the image",
			"∀y z:B. y ∈ image(u, R.carrier) ∧ z ∈ image(u, R.carrier) ⇒ h(S.mul(y, z)) = T.mul(h(y), h(z))",
			Derive(func(b *Argument) {
				y := b.FixAs[B]("y")
				z := b.FixAs[B]("z")
				inImageBoth := b.Assume()
				b.Show(
					"read y and z through their chosen preimages",
					By(
						inImageBoth,
						At(preimages, y),
						At(preimages, z),
						At(
							productOnImages,
							b.TermAs[A]("inverse_on(R.carrier, u, y)"),
							b.TermAs[A]("inverse_on(R.carrier, u, z)")),
						At(values, b.TermAs[A]("inverse_on(R.carrier, u, y)")),
						At(values, b.TermAs[A]("inverse_on(R.carrier, u, z)"))))
			}))
		one := a.Have(
			"h keeps one",
			"h(S.one) = T.one",
			By(
				Normalized,
				comm_ring.OneIn.Read(Source.Read(uHom)),
				MapOne.Read(uHom),
				MapOne.Read(vHom),
				At(values, a.TermAs[A]("R.one"))))
		imageRing := a.Have(
			"the image of u is a ring under the operations of S",
			"comm_ring_on(restrict_ring(S, image(u, R.carrier)))",
			By(
				ImageSubring.Read(uHom),
				comm_ring.SubringRingOn.Read(Target.Read(uHom)).AsFact().At(
					a.TermAs[Set[B]]("image(u, R.carrier)"))))
		homomorphism := a.Have(
			"h is a ring homomorphism from the image into T",
			"ring_homomorphism(restrict_ring(S, image(u, R.carrier)), T, h)",
			By(
				imageRing,
				Target.Read(vHom),
				intoTarget,
				additive,
				multiplicative,
				one,
				RingHomomorphism.At(a.TermAs[RingOps[B]]("restrict_ring(S, image(u, R.carrier))"), T, h)))
		a.Take(h)
		a.Show(
			"h factors v through u",
			By(values, homomorphism))
	}),
})}

// RingMapEqualizerSubring — the elements where two ring maps agree form a
// subring: each map keeps zero, one, sums, negatives and products.
var RingMapEqualizerSubring = ringMapEqualizerSubringThm{family.Add(registry.ProofEntry{
	Name: "RingMapEqualizerSubring",
	Key:  "prop_3cdefa3af3637311",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀T:ring_ops(B). ∀f g:(A → B).",
		Hypotheses: []string{
			"ring_homomorphism(R, T, f)",
			"ring_homomorphism(R, T, g)",
		},
		Conclusion: "subring(R, «agreement»)",
		Abbrev: Abbrev{
			{Name: "agreement", Text: "{x:A | x ∈ R.carrier ∧ f(x) = g(x)}"},
		},
	},
		func(a *Argument, R *Expr[RingOps[A]], T *Expr[RingOps[B]], f, g *Arrow[A, B], fMap, gMap Fact) {
			ring := a.Have(
				"the source is a ring",
				"comm_ring_on(R)",
				By(Source.Read(fMap)))
			inCarrier := a.Have(
				"the agreement set lies in R",
				"«agreement» ⊆ R.carrier",
				BySets())
			zero := a.Have(
				"both maps keep zero",
				"R.zero ∈ «agreement»",
				BySets(comm_ring.ZeroIn.Read(ring), MapZero.Read(fMap), MapZero.Read(gMap)))
			one := a.Have(
				"both maps keep one",
				"R.one ∈ «agreement»",
				BySets(comm_ring.OneIn.Read(ring), MapOne.Read(fMap), MapOne.Read(gMap)))
			sums := a.Have(
				"both maps keep sums",
				"∀u v:A. u ∈ «agreement» ∧ v ∈ «agreement» ⇒ u + v ∈ «agreement»",
				BySets(comm_ring.AddIn.Read(ring), MapAdd.Read(fMap), MapAdd.Read(gMap)))
			negatives := a.Have(
				"both maps keep negatives",
				"∀u:A. u ∈ «agreement» ⇒ -u ∈ «agreement»",
				BySets(
					comm_ring.NegIn.Read(ring),
					group_homomorphism.MapInv.Read(AdditiveHomomorphism.Read(fMap)),
					group_homomorphism.MapInv.Read(AdditiveHomomorphism.Read(gMap))))
			products := a.Have(
				"both maps keep products",
				"∀u v:A. u ∈ «agreement» ∧ v ∈ «agreement» ⇒ u * v ∈ «agreement»",
				BySets(comm_ring.MulIn.Read(ring), MapMul.Read(fMap), MapMul.Read(gMap)))
			a.Show(
				"these are the clauses of a subring",
				Unfold(comm_ring.SubringDef),
				By(inCarrier, zero, one, sums, negatives, products))
		}),
})}

// RingMapPreimageSubring — the elements a ring map sends into a subring of its
// target form a subring: the map keeps zero, one, sums, negatives and products.
var RingMapPreimageSubring = ringMapPreimageSubringThm{family.Add(registry.ProofEntry{
	Name: "RingMapPreimageSubring",
	Key:  "prop_38c55cc226708562",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀T:ring_ops(B). ∀f:(A → B). ∀U:set(B).",
		Hypotheses: []string{
			"ring_homomorphism(R, T, f)",
			"subring(T, U)",
		},
		Conclusion: "subring(R, preimage_on(R.carrier, f, U))",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			T *Expr[RingOps[B]],
			f *Arrow[A, B],
			U *Expr[Set[B]],
			fMap, subringU Fact,
		) {
			ring := a.Have(
				"the source is a ring",
				"comm_ring_on(R)",
				By(Source.Read(fMap)))
			inCarrier := a.Have(
				"the preimage lies in R",
				"preimage_on(R.carrier, f, U) ⊆ R.carrier",
				BySets())
			zero := a.Have(
				"the map keeps zero",
				"R.zero ∈ preimage_on(R.carrier, f, U)",
				BySets(comm_ring.ZeroIn.Read(ring), MapZero.Read(fMap), comm_ring.SubringZero.Read(subringU)))
			one := a.Have(
				"the map keeps one",
				"R.one ∈ preimage_on(R.carrier, f, U)",
				BySets(comm_ring.OneIn.Read(ring), MapOne.Read(fMap), comm_ring.SubringOne.Read(subringU)))
			sums := a.Have(
				"the map keeps sums",
				Statement{
					Binders: "∀u v:A.",
					Hypotheses: []string{
						"u ∈ preimage_on(R.carrier, f, U)",
						"v ∈ preimage_on(R.carrier, f, U)",
					},
					Conclusion: "u + v ∈ preimage_on(R.carrier, f, U)",
				},
				BySets(comm_ring.AddIn.Read(ring), MapAdd.Read(fMap), comm_ring.SubringAdd.Read(subringU)))
			negatives := a.Have(
				"the map keeps negatives",
				"∀u:A. u ∈ preimage_on(R.carrier, f, U) ⇒ -u ∈ preimage_on(R.carrier, f, U)",
				BySets(comm_ring.NegIn.Read(ring), MapNeg.Read(fMap), comm_ring.SubringNeg.Read(subringU)))
			products := a.Have(
				"the map keeps products",
				Statement{
					Binders: "∀u v:A.",
					Hypotheses: []string{
						"u ∈ preimage_on(R.carrier, f, U)",
						"v ∈ preimage_on(R.carrier, f, U)",
					},
					Conclusion: "u * v ∈ preimage_on(R.carrier, f, U)",
				},
				BySets(comm_ring.MulIn.Read(ring), MapMul.Read(fMap), comm_ring.SubringMul.Read(subringU)))
			a.Show(
				"these are the clauses of a subring",
				Unfold(comm_ring.SubringDef),
				By(inCarrier, zero, one, sums, negatives, products))
		}),
})}

// RingMapPower — a ring homomorphism keeps the powers of a member of its source,
// its multiplicativity holding on the source alone: by induction on the exponent,
// the empty power is one, which it keeps, and one more factor is a product of two
// members.
var RingMapPower = ringMapPowerThm{family.Add(registry.ProofEntry{
	Name: "RingMapPower",
	Key:  "prop_658ba8008c2921e2",
	Build: RingHomomorphism.Law(
		Statement{
			Binders: "∀n:num. ∀x:A.",
			Hypotheses: []string{
				"x ∈ R.carrier",
			},
			Conclusion: "f(monoid_pow(R.mul, R.one, x, n)) = monoid_pow(S.mul, S.one, f(x), n)",
		},
		func(a *Argument, hom RingHomomorphismFact[on.R, on.S], n *Expr[Nat], x *Member[A, on.R]) {
			multiplicative := comm_ring.MulMonoidOn.Read(Source.Read(hom))
			a.Induct(n)
			a.Base(
				"the empty power is one, which f keeps",
				Simp(Fwd(comm_monoid.MonoidPowDef)),
				By(MapOne.Read(hom)))
			a.Step(
				"one more factor is a product of two members, which f keeps",
				func(b *Argument, ih Fact) {
					power := b.TermAs[A]("monoid_pow(R.mul, R.one, x, n)")
					inSource := b.Have(
						"the power lies in R",
						"monoid_pow(R.mul, R.one, x, n) ∈ R.carrier",
						By(x, comm_monoid.PowIn.Read(multiplicative).AsFact().At(x, n)))
					b.Do(Simp(Fwd(comm_monoid.MonoidPowDef)))
					b.Show(
						"the power of the image follows the power",
						By(x, inSource, ih, MapMul.Read(hom).AsFact().At(x, power)))
				})
		}),
})}

// RingMapProductSum — a ring homomorphism takes a finite sum of triple products
// of members of its source term by term: it keeps the additive monoid of the
// source, and each term is two products.
var RingMapProductSum = ringMapProductSumThm{family.Add(registry.ProofEntry{
	Name: "RingMapProductSum",
	Key:  "prop_cecfe6dc8a32aa90",
	Build: RingHomomorphism.Law(Statement{
		Binders: "∀I:set(D). ∀c u v:(D → A).",
		Hypotheses: []string{
			"finite(I)",
			"∀p:D. p ∈ I ⇒ c(p) ∈ R.carrier ∧ u(p) ∈ R.carrier ∧ v(p) ∈ R.carrier",
		},
		Conclusion: "f(module_sum(R.add, R.zero, I, λp:D. c(p) * (u(p) * v(p)))) = " +
			"module_sum(S.add, S.zero, I, λp:D. f(c(p)) * (f(u(p)) * f(v(p))))",
	},
		func(
			a *Argument,
			hom RingHomomorphismFact[on.R, on.S],
			I *Expr[Set[D]],
			c, u, v *Arrow[D, A],
			finiteIndex, members Fact,
		) {
			source := Source.Read(hom)
			products := comm_ring.MulIn.Read(source)
			terms := a.Have(
				"each term lies in R, and f splits it",
				Statement{
					Binders:    "∀p:D.",
					Hypotheses: []string{"p ∈ I"},
					Conclusion: "c(p) * (u(p) * v(p)) ∈ R.carrier ∧ " +
						"f(c(p) * (u(p) * v(p))) = f(c(p)) * (f(u(p)) * f(v(p)))",
				},
				Derive(func(b *Argument) {
					p := b.FixAs[D]("p")
					inIndex := b.Assume()
					factors := b.Have(
						"the three factors lie in R",
						"c(p) ∈ R.carrier ∧ u(p) ∈ R.carrier ∧ v(p) ∈ R.carrier",
						By(members.At(p), inIndex))
					first, second, third := c.Apply(p), u.Apply(p), v.Apply(p)
					inner := b.TermAs[A]("u(p) * v(p)")
					b.Show(
						"f keeps both products",
						By(
							factors,
							products.AsFact().At(first, inner),
							products.AsFact().At(second, third),
							MapMul.Read(hom).AsFact().At(first, inner),
							MapMul.Read(hom).AsFact().At(second, third)))
				}))
			add, zero := a.TermAs[Op[B]]("S.add"), a.TermAs[B]("S.zero")
			imaged := a.TermAs[Fun[D, B]]("λp:D. f(c(p) * (u(p) * v(p)))")
			split := a.TermAs[Fun[D, B]]("λp:D. f(c(p)) * (f(u(p)) * f(v(p)))")
			sum := a.Have(
				"f keeps the additive monoid of R, so it takes the sum to the sum of the images",
				"f(module_sum(R.add, R.zero, I, λp:D. c(p) * (u(p) * v(p)))) = "+
					"module_sum(S.add, S.zero, I, λp:D. f(c(p) * (u(p) * v(p))))",
				By(
					finiteIndex,
					terms,
					MapZero.Read(hom),
					MapAdd.Read(hom),
					Read(
						module.ModuleSumMonoidHomomorphism,
						comm_ring.AddMonoidOn.Read(source)).At(
						add,
						zero,
						a.TermAs[Fun[A, B]]("f"),
						I,
						a.TermAs[Fun[D, A]]("λp:D. c(p) * (u(p) * v(p))"))))
			a.Show(
				"and term by term that is the sum of the products of the images",
				sum.Rw(),
				By(terms, module.ModuleSumCongruence.At(add, zero, I, imaged, split)))
		}),
})}

// RestrictionImageKernel — a map cut down to S, vanishing off it, has on S the
// image of the map itself, and its kernel in S is the part of the map's kernel
// that lies in S.
var RestrictionImageKernel = restrictionImageKernelThm{family.Add(registry.ProofEntry{
	Name: "RestrictionImageKernel",
	Key:  "prop_d890d7907e6a73a3",
	Build: family.Theorem(Statement{
		Binders:    "∀S T:set(A). ∀z:B. ∀ψ:(A → B).",
		Hypotheses: []string{"S ⊆ T"},
		Conclusion: "image(«restricted», S) = image(ψ, S) ∧ " +
			"ring_kernel(z, S, «restricted») = ring_kernel(z, T, ψ) ∩ S",
		Abbrev: Abbrev{
			{Name: "restricted", Text: "λx:A. COND(x ∈ S, ψ(x), z)"},
		},
	},
		func(a *Argument, S, T *Expr[Set[A]], z *Expr[B], ψ *Arrow[A, B], inside Fact) {
			restricted := a.TermAs[Fun[A, B]]("«restricted»")
			agree := a.Have(
				"on S the restriction is ψ",
				"∀x:A. x ∈ S ⇒ COND(x ∈ S, ψ(x), z) = ψ(x)",
				Derive(func(b *Argument) {
					b.Fix()
					b.Show(
						"the condition holds",
						By(b.Assume()))
				}))
			sameImage := a.Have(
				"so the two have one image on S",
				"image(«restricted», S) = image(ψ, S)",
				By(agree, set_image.ImageCongruence.At(restricted, ψ, S)))
			sameKernel := a.Have(
				"and the zeros of the restriction in S are those of ψ",
				"ring_kernel(z, S, «restricted») = ring_kernel(z, T, ψ) ∩ S",
				Unfold(RingKernelDef),
				BySets(inside))
			a.Show(
				"both parts stand",
				By(sameImage, sameKernel))
		}),
})}
