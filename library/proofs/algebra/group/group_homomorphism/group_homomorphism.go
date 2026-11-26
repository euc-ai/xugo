// group_homomorphism.go — the chapter: homomorphisms between groups on
// sets, the two subgroups a homomorphism carries — its kernel in the
// source, normal there, and its image in the target, as is the image of
// every subgroup of the source — the converse, that the image of a group
// along a map keeping its operations is a group, and the isomorphisms
// among the homomorphisms.

package group_homomorphism

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/abelian_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The structure and its axioms
// ---------------------------------------------------------------------------

// GroupHomomorphism — f carries G's carrier into H's carrier and
// preserves their products. Its first two conjuncts are the source and
// target group laws, read through Source and Target.
var GroupHomomorphism = groupHomomorphismThm{family.DefineStructure(registry.DefEntry{
	Name: "GroupHomomorphism",
	Key:  "prop_77387a2e28671a25",

	Const: "group_homomorphism",
	Type:  "group_ops(A) → group_ops(B) → (A → B) → bool",
	Equations: []string{
		"∀G:group_ops(A). ∀H:group_ops(B). ∀f:(A → B). " +
			"    group_homomorphism(G, H, f) ⇔ " +
			"    group_on(G) ∧ " +
			"    group_on(H) ∧ " +
			"    (∀x:A. x ∈ G.carrier ⇒ f(x) ∈ H.carrier) ∧ " +
			"    (∀x y:A. x ∈ G.carrier ∧ y ∈ G.carrier ⇒ f(G.mul(x, y)) = H.mul(f(x), f(y)))",
	},
})}

// Source — the map's source is a group on c: the structure at which the
// group chapter's laws apply to the elements f is applied to.
var Source = sourceThm{family.Add(registry.ProofEntry{
	Name: "Source",
	Key:  "prop_9e20549d19c60f1",

	Build: GroupHomomorphism.Axiom("group_on(G)"),
})}

// Target — the map's target is a group on c': the structure at which
// the group chapter's laws apply to the values f takes.
var Target = targetThm{family.Add(registry.ProofEntry{
	Name: "Target",
	Key:  "prop_d52223e34860cdda",

	Build: GroupHomomorphism.Axiom("group_on(H)"),
})}

// MapIn — the map carries the source's carrier into the target's.
var MapIn = mapInThm{family.Add(registry.ProofEntry{
	Name: "MapIn",
	Key:  "prop_fce27ae987517b30",

	Build: GroupHomomorphism.Axiom(Statement{
		Binders: "∀x:A.",
		Hypotheses: []string{
			"x ∈ G.carrier",
		},
		Conclusion: "f(x) ∈ H.carrier",
	}),
})}

// MapMul — the map respects the operation: the image of a product of
// two points of c is the product of the images.
var MapMul = mapMulThm{family.Add(registry.ProofEntry{
	Name: "MapMul",
	Key:  "prop_ab4d6afc66f51804",

	Build: GroupHomomorphism.Axiom(Statement{
		Binders: "∀x y:A.",
		Hypotheses: []string{
			"x ∈ G.carrier",
			"y ∈ G.carrier",
		},
		Conclusion: "f(x * y) = f(x) * f(y)",
	}),
})}

// ---------------------------------------------------------------------------
// What a homomorphism preserves
// ---------------------------------------------------------------------------

// MapOne — the map sends the source's identity to the target's: one is
// one * one in the source, so f(one) is f(one) * f(one) in the target —
// its own square, and the identity is the only element of c' that is.
var MapOne = mapOneThm{family.Add(registry.ProofEntry{
	Name: "MapOne",
	Key:  "prop_8d6f9683dd54f54e",

	Build: GroupHomomorphism.Law("f(G.one) = H.one",
		func(a *Argument, hom GroupHomomorphismFact[on.G, on.H]) {
			source := a.Have(
				"the source is a group on G.carrier",
				"group_on(G)",
				By(Source, hom))
			target := a.Have(
				"the target is a group on H.carrier",
				"group_on(H)",
				By(Target, hom))
			oneIn := a.Have(
				"G.one lies in G.carrier",
				"G.one ∈ G.carrier",
				By(group.OneIn, source))
			imageIn := a.Have(
				"so f(G.one) lies in H.carrier",
				"f(G.one) ∈ H.carrier",
				By(MapIn, hom, oneIn))
			square := a.Have(
				"f(G.one) is its own square in the target",
				"f(G.one) * f(G.one) = f(G.one)",
				CalcEq(
					Leg(
						a.Term("f(G.one * G.one)"),
						"the map carries the product G.one * G.one to the product of the images",
						Simp(Fwd(MapMul)),
						Basic()),
					FinalLeg(
						"and G.one * G.one is G.one, by the source's identity law at G.one",
						Simp(Fwd(group.LeftIdentityOn)),
						Basic()),
				))
			a.Show(
				"the target's identity is the only element of H.carrier that is its own square",
				By(square, group.IdempotentIsOneOn, target, imageIn))
		}),
})}

// MapInv — the map sends the inverse of a point x of c to the inverse of
// f(x): f(inv(x)) times f(x) is the image of inv(x) * x, which is the
// image of one, which is one' — so f(inv(x)) is a left inverse of f(x)
// in the target, and the inverse is the only one.
var MapInv = mapInvThm{family.Add(registry.ProofEntry{
	Name: "MapInv",
	Key:  "prop_bcdeb03c5214fa5b",

	Build: GroupHomomorphism.Law(Statement{
		Binders: "∀x:A.",
		Hypotheses: []string{
			"x ∈ G.carrier",
		},
		Conclusion: "f(G.inv(x)) = H.inv(f(x))",
	},
		func(a *Argument, hom GroupHomomorphismFact[on.G, on.H], x *Member[A, on.G]) {
			source := a.Have(
				"the source is a group on G.carrier",
				"group_on(G)",
				By(Source, hom))
			target := a.Have(
				"the target is a group on H.carrier",
				"group_on(H)",
				By(Target, hom))
			leftInverse := a.Have(
				"f(G.inv(x)) is a left inverse of f(x) in the target",
				"f(G.inv(x)) * f(x) = H.one",
				CalcEq(
					Leg(
						a.Term("f(G.inv(x) * x)"),
						"the map carries the product G.inv(x) * x to the product of the images",
						Simp(Fwd(MapMul), Fwd(group.InvIn)),
						Basic()),
					Leg(
						a.Term("f(G.one)"),
						"and G.inv(x) * x is G.one, by the source's inverse law",
						Simp(Fwd(group.LeftInverseOn)),
						Basic()),
					FinalLeg(
						"and the map sends G.one to H.one",
						Simp(Fwd(MapOne)),
						Basic()),
				))
			a.Show(
				"uniqueness of the inverse in the target: the left factor "+
					"in H.carrier whose product with f(x) is H.one is H.inv(f(x))",
				By(leftInverse, group.InvUniqueOn, target, MapIn, hom, group.InvIn, source, x))
		}),
})}

// MapPow — a homomorphism carries a power of x to the same power of f(x):
// by induction on n, the identity going to the identity and one more
// factor of x to one more factor of f(x).
var MapPow = mapPowThm{family.Add(registry.ProofEntry{
	Name: "MapPow",
	Key:  "prop_9758ed64506814e4",
	Build: GroupHomomorphism.Law(Statement{
		Binders: "∀x:A. ∀n:num.",
		Hypotheses: []string{
			"x ∈ G.carrier",
		},
		Conclusion: "f(monoid_pow(G.mul, G.one, x, n)) = monoid_pow(H.mul, H.one, f(x), n)",
	},
		func(a *Argument, hom GroupHomomorphismFact[on.G, on.H], x *Member[A, on.G], n *Expr[Nat]) {
			a.Induct(n)
			a.Base(
				"x ^ 0 is the identity of G, which f carries to the identity of H",
				Simp(Fwd(comm_monoid.MonoidPowDef)),
				By(MapOne, hom))
			a.Step(
				"f carries x * x ^ n to f(x) * f(x ^ n)",
				func(b *Argument, ih Fact) {
					b.Show(
						"one more factor of x on each side",
						Simp(Fwd(comm_monoid.MonoidPowDef)),
						By(ih, hom, x, MapMul, group.PowIn.Read(Source.Read(hom))))
				})
		}),
})}

// ---------------------------------------------------------------------------
// The kernel
// ---------------------------------------------------------------------------

// GroupKernelDef — `group_kernel(one', c, f)`: the points of c the map
// sends to the target's identity. The kernel reads nothing of either
// group but that identity, so it is defined for any map into a type
// with a distinguished point, and the point is implicit: under a law
// over a homomorphism the arguments are `H.one, G.carrier, f`.
var GroupKernelDef = groupKernelDefThm{family.Define(registry.DefEntry{
	Name:     "GroupKernelDef",
	Key:      "prop_8bf816b3547de155",
	Const:    "group_kernel",
	Type:     "B → set(A) → (A → B) → set(A)",
	Implicit: []string{"one'"},
	Equations: []string{
		"∀one':B. ∀c:set(A). ∀f:(A → B). group_kernel(one', c, f) = {x:A | x ∈ c ∧ f(x) = one'}",
	},
})}

// InKernel — a point lies in the kernel exactly when it lies in c and the
// map sends it to the distinguished point: the definition unfolded and
// membership in the comprehension read off. Every kernel member reads
// the kernel through it.
var InKernel = inKernelThm{family.Add(registry.ProofEntry{
	Name: "InKernel",
	Key:  "prop_2d6d2ead514b1442",
	Build: family.Theorem("∀one':B. ∀c:set(A). ∀f:(A → B). ∀x:A. "+
		"    x ∈ group_kernel(one', c, f) ⇔ x ∈ c ∧ f(x) = one'",
		func(a *Argument, one_ *Expr[B], c *Expr[Set[A]], f *Arrow[A, B], x *Expr[A]) {
			a.Show(
				"a point of the comprehension is a point of c the map sends to one', and conversely",
				Unfold(GroupKernelDef),
				BySets())
		}),
})}

// KernelSubgroup — the kernel is a subgroup of the source: it lies in c
// by definition, the map preserves the three operations, and the
// target's identity is fixed by each of them. The subgroup predicate is
// unfolded, each kernel membership read as its two conditions, and the
// four closure conditions closed in the definition's order.
var KernelSubgroup = kernelSubgroupThm{family.Add(registry.ProofEntry{
	Name: "KernelSubgroup",
	Key:  "prop_b8382ab7f8d237f3",

	Build: GroupHomomorphism.Law("subgroup(G, group_kernel(H.one, G.carrier, f))",
		func(a *Argument, hom GroupHomomorphismFact[on.G, on.H]) {
			source := a.Have(
				"the source is a group on G.carrier",
				"group_on(G)",
				By(Source, hom))
			target := a.Have(
				"the target is a group on H.carrier",
				"group_on(H)",
				By(Target, hom))
			oneIn := a.Have(
				"G.one lies in G.carrier",
				"G.one ∈ G.carrier",
				By(group.OneIn, source))
			oneImageIn := a.Have(
				"H.one lies in H.carrier",
				"H.one ∈ H.carrier",
				By(group.OneIn, target))
			a.Do(Unfold(group.SubgroupDef), Unfold(set_basic.SubsetDef), Simp(Fwd(InKernel)), SplitConjAll(
				Case(
					"the kernel lies in G.carrier: a point of it lies in G.carrier by definition",
					Derive(func(b *Argument) {
						b.FixAs[A]("x")
						given := b.Assume()
						b.Show(
							"the first condition",
							By(given))
					})),
				Case(
					"G.one lies in G.carrier",
					By(oneIn)),
				Case(
					"and the map sends it to H.one",
					By(MapOne, hom)),
				Case(
					"two points of the kernel multiply inside it",
					Derive(func(b *Argument) {
						b.Fix("x")
						b.Fix("y")
						parts := b.Conjuncts(
							b.Assume(),
							"x lies in G.carrier",
							"f(x) is H.one",
							"y lies in G.carrier",
							"f(y) is H.one")
						xParts, yParts := parts[:2], parts[2:]
						b.Do(SplitConj(
							Case(
								"x * y lies in G.carrier",
								By(group.MulIn, source, xParts[0], yParts[0])),
							Case(
								"and the map carries it to a product of two one's",
								CalcEq(
									Leg(
										b.Term("f(x) * f(y)"),
										"the map carries the product x * y to the product of the images",
										Simp(Fwd(MapMul)),
										Basic()),
									Leg(
										b.Term("H.one * H.one"),
										"and both images are H.one",
										xParts[1].Rw(),
										yParts[1].Rw(),
										Basic()),
									FinalLeg(
										"H.one times itself is H.one, by the target's identity law at H.one",
										Simp(Fwd(group.LeftIdentityOn.Read(target))),
										By(oneImageIn)),
								)),
						))
					})),
				Case(
					"a point of the kernel has its inverse inside it",
					Derive(func(b *Argument) {
						b.Fix("x")
						given := b.Assume()
						parts := b.Conjuncts(
							given,
							"x lies in G.carrier",
							"f(x) is H.one")
						b.Do(SplitConj(
							Case(
								"G.inv(x) lies in G.carrier",
								By(group.InvIn, source, parts[0])),
							Case(
								"and the map carries G.inv(x) to the inverse of H.one",
								CalcEq(
									Leg(
										b.Term("H.inv(f(x))"),
										"the map carries the inverse G.inv(x) to the inverse of the image",
										Simp(Fwd(MapInv)),
										Basic()),
									Leg(
										b.Term("H.inv(H.one)"),
										"and the image is H.one",
										parts[1].Rw(),
										Basic()),
									FinalLeg(
										"H.one is its own inverse in the target",
										Simp(Fwd(group.InvOneOn.Read(target))),
										Basic()),
								)),
						))
					})),
			))
		}),
})}

// KernelNormal — the kernel is moreover normal in the source: the map
// carries a conjugate by a point of c of a point it sends to one' to a
// conjugate of one', which is one'. The normal-subgroup predicate is
// unfolded, the kernel memberships read as their conditions, and its
// two conditions closed in the definition's order.
var KernelNormal = kernelNormalThm{family.Add(registry.ProofEntry{
	Name: "KernelNormal",
	Key:  "prop_803202441122432e",

	Build: GroupHomomorphism.Law("normal_subgroup(G, group_kernel(H.one, G.carrier, f))",
		func(a *Argument, hom GroupHomomorphismFact[on.G, on.H]) {
			source := a.Have(
				"the source is a group on G.carrier",
				"group_on(G)",
				By(Source, hom))
			target := a.Have(
				"the target is a group on H.carrier",
				"group_on(H)",
				By(Target, hom))
			a.Do(Unfold(group.NormalSubgroupDef), Simp(Fwd(InKernel)), SplitConj(
				Case(
					"the kernel is a subgroup",
					By(KernelSubgroup, hom)),
				Case(
					"the kernel holds every conjugate by G.carrier of each of its points",
					Derive(func(b *Argument) {
						b.Fix("g")
						b.Fix("x")
						given := b.Assume()
						parts := b.Conjuncts(
							given,
							"g lies in G.carrier",
							"x lies in G.carrier",
							"f(x) is H.one")
						xParts := parts[1:]
						b.Have(
							"f(g) lies in H.carrier",
							"f(g) ∈ H.carrier",
							By(MapIn, hom, parts[0]))
						b.Do(SplitConj(
							Case(
								"the conjugate lies in G.carrier",
								By(group.MulIn, group.InvIn, source, parts[0], xParts[0])),
							Case(
								"and the map carries the conjugate of x by g to the conjugate of H.one by f(g)",
								CalcEq(
									Leg(
										b.Term("(f(g) * f(x)) * H.inv(f(g))"),
										"the map carries the two products and the inverse to the target",
										Simp(Fwd(MapMul), Fwd(MapInv), Fwd(group.MulIn), Fwd(group.InvIn)),
										Basic()),
									Leg(
										b.Term("(f(g) * H.one) * H.inv(f(g))"),
										"and f(x) is H.one",
										xParts[1].Rw(),
										Basic()),
									Leg(
										b.Term("f(g) * H.inv(f(g))"),
										"H.one drops off f(g) * H.one, by the target's identity law",
										Simp(Fwd(group.RightIdentityOn.Read(target))),
										Basic()),
									FinalLeg(
										"and f(g) times its inverse is H.one, by the target's inverse law",
										Simp(Fwd(group.RightInverseOn.Read(target))),
										Basic()),
								)),
						))
					})),
			))
		}),
})}

// EqIffInKernel — two points of c have the same image exactly when
// inv(x) * y lies in the kernel: it lies in c, the map carries it to
// inv'(f(x)) * f(y), and in the target that product is one' exactly when
// f(x) is f(y). The fibres as cosets (`EqIffInLeftCoset`) and the
// kernel's test for injectivity stand on it.
var EqIffInKernel = eqIffInKernelThm{family.Add(registry.ProofEntry{
	Name: "EqIffInKernel",
	Key:  "prop_48eab5d6325b0acc",

	Build: GroupHomomorphism.Law(Statement{
		Binders: "∀x y:A.",
		Hypotheses: []string{
			"x ∈ G.carrier",
			"y ∈ G.carrier",
		},
		Conclusion: "f(x) = f(y) ⇔ G.inv(x) * y ∈ group_kernel(H.one, G.carrier, f)",
	},
		func(a *Argument, hom GroupHomomorphismFact[on.G, on.H], x, y *Member[A, on.G]) {
			source := a.Have(
				"the source is a group on G.carrier",
				"group_on(G)",
				By(Source, hom))
			target := a.Have(
				"the target is a group on H.carrier",
				"group_on(H)",
				By(Target, hom))
			inC := a.Have(
				"G.inv(x) * y lies in G.carrier",
				"G.inv(x) * y ∈ G.carrier",
				By(group.MulIn, group.InvIn, source, x, y))
			image := a.Have(
				"the map carries G.inv(x) * y to H.inv(f(x)) * f(y)",
				"f(G.inv(x) * y) = H.inv(f(x)) * f(y)",
				Simp(Fwd(MapMul), Fwd(MapInv), Fwd(group.InvIn)),
				Basic())
			imagesIn := a.Have(
				"the images lie in H.carrier",
				"f(x) ∈ H.carrier ∧ f(y) ∈ H.carrier",
				By(MapIn, hom, x, y))
			a.Show(
				"in the kernel means in G.carrier, which G.inv(x) * y is, with image "+
					"H.one; and H.inv(f(x)) * f(y) is H.one exactly when f(x) is f(y)",
				Simp(Fwd(InKernel)),
				image.Rw(),
				By(Normalized, inC, imagesIn, group.InvMulEqOneOn.Read(target)))
		}),
})}

// EqIffInLeftCoset — the fibres of a homomorphism are the left cosets of
// its kernel: the points of c sharing x's image are exactly the left
// coset of the kernel at x. The group chapter reads membership in a
// left coset as inv(x) * y lying in the subgroup, and that is the
// kernel's test above.
var EqIffInLeftCoset = eqIffInLeftCosetThm{family.Add(registry.ProofEntry{
	Name: "EqIffInLeftCoset",
	Key:  "prop_81753629bf0bc45d",

	Build: GroupHomomorphism.Law(Statement{
		Binders: "∀x y:A.",
		Hypotheses: []string{
			"x ∈ G.carrier",
			"y ∈ G.carrier",
		},
		Conclusion: "f(x) = f(y) ⇔ y ∈ left_coset(x, group_kernel(H.one, G.carrier, f))",
	},
		func(a *Argument, hom GroupHomomorphismFact[on.G, on.H], x, y *Member[A, on.G]) {
			source := a.Have(
				"the source is a group on G.carrier",
				"group_on(G)",
				By(Source, hom))
			a.Have(
				"the kernel lies in G.carrier",
				"group_kernel(H.one, G.carrier, f) ⊆ G.carrier",
				By(group.SubgroupSubset, KernelSubgroup, hom))
			a.Show(
				"y in the coset at x is G.inv(x) * y in the kernel, which is f(x) = f(y)",
				Simp(Fwd(Read(group.InLeftCosetOn, source)), Fwd(EqIffInKernel)),
				Basic())
		}),
})}

// KernelTrivialIffInjective — a homomorphism is one-to-one on c exactly
// when its kernel is trivial. Forwards, two points of c with the same
// image have inv(x) * y in the kernel, which is {one}, so inv(x) * y =
// one, which makes x and y one point. Backwards, the kernel and {one}
// have the same members: a point of the kernel lies in c and its image
// is one', which is f(one), so a map one-to-one on c makes the point
// one; one itself lies in c and is sent to one'.
var KernelTrivialIffInjective = kernelTrivialIffInjectiveThm{family.Add(registry.ProofEntry{
	Name: "KernelTrivialIffInjective",
	Key:  "prop_4553369e9ca175d6",

	Build: GroupHomomorphism.Law("group_kernel(H.one, G.carrier, f) = {G.one} ⇔ "+
		"injective_on(G.carrier, f)",
		func(a *Argument, hom GroupHomomorphismFact[on.G, on.H]) {
			source := a.Have(
				"the source is a group on G.carrier",
				"group_on(G)",
				By(Source, hom))
			a.Iff()
			a.Forward(
				"two points of G.carrier with the same image differ "+
					"by a kernel element, and the kernel holds G.one alone",
				func(b *Argument, trivial Fact) {
					b.Do(Simp(Fwd(functions.InjectiveOnDef))) // claimed of pairs of points of c
					b.Fix("x")
					b.Fix("y")
					given := b.Assume()
					parts := b.Conjuncts(
						given,
						"x lies in G.carrier",
						"so does y",
						"the images agree")
					inKernel := b.Have(
						"G.inv(x) * y lies in the kernel",
						"G.inv(x) * y ∈ group_kernel(H.one, G.carrier, f)",
						By(parts[2], EqIffInKernel, hom, parts[0], parts[1]))
					b.Show(
						"the kernel is {G.one}, so G.inv(x) * y = G.one, which is x = y",
						By(
							Normalized,
							inKernel,
							trivial,
							set_basic.InSing,
							group.InvMulEqOneOn.Read(source),
							parts[0],
							parts[1]))
				})
			a.Backward(
				"the kernel and {G.one} have the same members: a point of the kernel shares its image with G.one",
				func(b *Argument, injective Fact) {
					injectiveAtPoints := b.Unfolded(injective, functions.InjectiveOnDef)
					oneIn := b.Have(
						"G.one lies in G.carrier",
						"G.one ∈ G.carrier",
						By(group.OneIn, source))
					kernelInSing := b.Have(
						"a point of the kernel is G.one: it lies in G.carrier and shares "+
							"its image with G.one, and the map is one-to-one on G.carrier",
						"∀x:A. x ∈ group_kernel(H.one, G.carrier, f) ⇒ x ∈ {G.one}",
						Derive(func(d *Argument) {
							d.Fix("x")
							inKernel := d.Assume()
							given := d.Conjuncts(
								d.Have(
									"x lies in G.carrier and is sent to H.one",
									"x ∈ G.carrier ∧ f(x) = H.one",
									By(inKernel, InKernel)),
								"x lies in G.carrier",
								"f(x) is H.one")
							d.Show(
								"f(x) = f(G.one), so x = G.one",
								Simp(Fwd(set_basic.InSing)),
								By(Normalized, injectiveAtPoints, given[0], oneIn, given[1], MapOne, hom))
						}))
					singInKernel := b.Have(
						"G.one lies in the kernel: in G.carrier, and sent to H.one",
						"∀x:A. x ∈ {G.one} ⇒ x ∈ group_kernel(H.one, G.carrier, f)",
						Derive(func(d *Argument) {
							d.FixAs[A]("x")
							isOne := d.Have(
								"x is G.one",
								"x = G.one",
								By(d.Assume(), set_basic.InSing))
							d.Do(isOne.Rw(), Simp(Fwd(InKernel)))
							d.Do(SplitConj(Case(
								"G.one lies in G.carrier",
								By(oneIn)), Case(
								"and is sent to H.one",
								By(MapOne, hom))))
						}))
					b.Show(
						"two sets each lying in the other are equal",
						BySets(kernelInSing, singInKernel))
				})
		}),
})}

// ---------------------------------------------------------------------------
// The image
// ---------------------------------------------------------------------------

// ImageSubgroup — the image of G.carrier along a homomorphism is a
// subgroup of H. Each condition of a subgroup that quantifies over image
// points pulls back along f to a condition over points of G.carrier
// (set_image.ForallInImage for one point, ForallInImagePair for two).
// The image lies in H.carrier since f carries G.carrier into H.carrier;
// H.one, f(x) * f(y) and H.inv(f(x)) are the images of G.one, x * y and
// G.inv(x) by the map's laws, each a point of G.carrier by the source's
// closure.
var ImageSubgroup = imageSubgroupThm{family.Add(registry.ProofEntry{
	Name: "ImageSubgroup",
	Key:  "prop_dc1a373e97180945",

	Build: GroupHomomorphism.Law("subgroup(H, image(f, G.carrier))",
		func(a *Argument, hom GroupHomomorphismFact[on.G, on.H]) {
			source := Source.Read(hom)
			a.Do(Unfold(group.SubgroupDef), Unfold(set_basic.SubsetDef), SplitConjAll(
				Case(
					"the image lies in H.carrier: pulled back along f, it is f carrying G.carrier into H.carrier",
					Simp(Fwd(set_image.ForallInImage)),
					By(MapIn.Read(hom))),
				Case(
					"H.one lies in the image: it is the image of G.one, a point of G.carrier",
					Simp(Rev(MapOne.Read(hom))),
					By(set_image.FunInImage, group.OneIn.Read(source))),
				Case(
					"the product of two image points lies in the image",
					Simp(Fwd(set_image.ForallInImagePair)),
					Derive(func(b *Argument) {
						b.FixAs[A]("x")
						b.FixAs[A]("y")
						points := b.Assume()
						b.Show(
							"f(x) * f(y) is the image of x * y, a point of G.carrier",
							Simp(Rev(MapMul.Read(hom))),
							By(set_image.FunInImage, group.MulIn.Read(source), points))
					})),
				Case(
					"the inverse of an image point lies in the image",
					Simp(Fwd(set_image.ForallInImage)),
					Derive(func(b *Argument) {
						b.FixAs[A]("x")
						point := b.Assume()
						b.Show(
							"H.inv(f(x)) is the image of G.inv(x), a point of G.carrier",
							Simp(Rev(MapInv.Read(hom))),
							By(set_image.FunInImage, group.InvIn.Read(source), point))
					})),
			))
		}),
})}

// SubgroupImage — the image of a subgroup N along a homomorphism is a subgroup
// of the target: N is a group of its own, f restricts to a homomorphism on it,
// and ImageSubgroup is that homomorphism's image.
var SubgroupImage = subgroupImageThm{family.Add(registry.ProofEntry{
	Name: "SubgroupImage",
	Key:  "prop_f2f6a79ea189e2f8",
	Build: GroupHomomorphism.Law(Statement{
		Binders: "∀N:set(A).",
		Hypotheses: []string{
			"subgroup(G, N)",
		},
		Conclusion: "subgroup(H, image(f, N))",
	},
		func(a *Argument, hom GroupHomomorphismFact[on.G, on.H], N *Expr[Set[A]], inSource Fact) {
			restricted := a.Conjuncts(
				a.Have(
					"N lies in the carrier and is a group of its own",
					"N ⊆ G.carrier ∧ group_on(restrict_group(G, N))",
					By(inSource, group.SubgroupGroupOn.Read(Source.Read(hom)).At(N))),
				"N lies in the carrier",
				"N is a group of its own")
			target := a.Have(
				"the target is a group on H.carrier",
				"group_on(H)",
				By(Target, hom))
			into := a.Have(
				"f carries G.carrier into H.carrier",
				"∀x:A. x ∈ G.carrier ⇒ f(x) ∈ H.carrier",
				By(MapIn, hom))
			products := a.Have(
				"and keeps its products",
				"∀x y:A. x ∈ G.carrier ∧ y ∈ G.carrier ⇒ f(x * y) = f(x) * f(y)",
				By(MapMul, hom))
			restriction := a.Have(
				"f restricts to a homomorphism on N",
				"group_homomorphism(restrict_group(G, N), H, f)",
				Unfold(GroupHomomorphism),
				BySets(restricted[0], restricted[1], target, into, products))
			a.Show(
				"its image is the image of N",
				By(Normalized, restriction, ImageSubgroup))
		}),
})}

// ImageGroupOn — the homomorphic image of a group is a group: a record
// whose carrier is the image of a group's carrier along a map that keeps
// the product, the identity and the inverse is itself a group on a set.
// With the carrier read as the image, each condition of a group
// quantifies over image points and pulls back along the map to a
// condition over points of G.carrier (set_image.ForallInImage for one
// point, ForallInImagePair for two). There each condition at the images
// is the image of the same condition in the source, the map's laws
// carrying the one to the other.
var ImageGroupOn = imageGroupOnThm{family.Add(registry.ProofEntry{
	Name: "ImageGroupOn",
	Key:  "prop_288252f9761c0677",
	Build: family.Theorem(Statement{
		Binders: "∀G:group_on(A). ∀H:group_ops(B). ∀f:(A → B).",
		Hypotheses: []string{
			"image(f, G.carrier) = H.carrier",
			"∀x y:A. x ∈ G.carrier ∧ y ∈ G.carrier ⇒ f(x * y) = f(x) * f(y)",
			"f(G.one) = H.one",
			"∀x:A. x ∈ G.carrier ⇒ f(G.inv(x)) = H.inv(f(x))",
		},
		Conclusion: "group_on(H)",
	},
		func(
			a *Argument,
			G group.GroupFact[on.G],
			H *Expr[group.GroupOps[B]],
			f *Arrow[A, B],
			onto, mul, one, inv Fact,
		) {
			oneIn := a.Have(
				"H.one lies in the image: it is the image of G.one, a point of G.carrier",
				"H.one ∈ image(f, G.carrier)",
				one.RwRev(),
				By(set_image.FunInImage, group.OneIn.Read(G)))
			mulIn := a.Have(
				"the product of two image points is an image point",
				"∀u v:B. u ∈ image(f, G.carrier) ∧ v ∈ image(f, G.carrier) ⇒ u * v ∈ image(f, G.carrier)",
				Simp(Fwd(set_image.ForallInImagePair)),
				Derive(func(b *Argument) {
					b.FixAs[A]("x")
					b.FixAs[A]("y")
					points := b.Assume()
					b.Show(
						"f(x) * f(y) is the image of x * y, a point of G.carrier",
						Simp(Rev(mul)),
						By(set_image.FunInImage, group.MulIn.Read(G), points))
				}))
			invIn := a.Have(
				"the inverse of an image point is an image point",
				"∀u:B. u ∈ image(f, G.carrier) ⇒ H.inv(u) ∈ image(f, G.carrier)",
				Simp(Fwd(set_image.ForallInImage)),
				Derive(func(b *Argument) {
					b.FixAs[A]("x")
					point := b.Assume()
					b.Show(
						"H.inv(f(x)) is the image of G.inv(x), a point of G.carrier",
						Simp(Rev(inv)),
						By(set_image.FunInImage, group.InvIn.Read(G), point))
				}))
			assoc := a.Have(
				"the product of image points associates",
				Statement{
					Binders: "∀u v w:B.",
					Hypotheses: []string{
						"u ∈ image(f, G.carrier)",
						"v ∈ image(f, G.carrier)",
						"w ∈ image(f, G.carrier)",
					},
					Conclusion: "u * (v * w) = u * v * w",
				},
				Simp(Fwd(set_image.ForallInImageTriple)),
				Derive(func(b *Argument) {
					b.FixAs[A]("x")
					b.FixAs[A]("y")
					b.FixAs[A]("z")
					b.Assume()
					b.Show(
						"the two sides are the images of x * (y * z) and x * y * z, which are equal by associativity in G",
						Simp(Rev(mul), Fwd(group.MulIn.Read(G)), Fwd(group.AssocOn.Read(G))),
						Basic())
				}))
			leftIdentity := a.Have(
				"H.one is a left identity on the image",
				"∀u:B. u ∈ image(f, G.carrier) ⇒ H.one * u = u",
				Simp(Fwd(set_image.ForallInImage)),
				Derive(func(b *Argument) {
					b.FixAs[A]("x")
					b.Assume()
					b.Show(
						"H.one * f(x) is f(G.one) * f(x), the image of G.one * x, that is of x",
						Simp(Rev(one), Rev(mul), Fwd(group.OneIn.Read(G)), Fwd(group.LeftIdentityOn.Read(G))),
						Basic())
				}))
			leftInverse := a.Have(
				"H.inv(u) is a left inverse of u on the image",
				"∀u:B. u ∈ image(f, G.carrier) ⇒ H.inv(u) * u = H.one",
				Simp(Fwd(set_image.ForallInImage)),
				Derive(func(b *Argument) {
					b.FixAs[A]("x")
					b.Assume()
					b.Show(
						"H.inv(f(x)) * f(x) is the image of G.inv(x) * x, which is G.one, and the map sends G.one to H.one",
						Simp(Rev(inv), Rev(mul), Fwd(group.InvIn.Read(G)), Fwd(group.LeftInverseOn.Read(G)), Fwd(one)),
						Basic())
				}))
			// Unfolding group_on opens the source's group_on(G) as well, so the
			// six conditions are had above, before it.
			a.Show(
				"H is a group on its carrier, the image: the six conditions are the six facts above",
				Unfold(group.GroupOn),
				onto.RwRev(),
				By(oneIn, mulIn, invIn, assoc, leftIdentity, leftInverse))
		}),
})}

// ImageAbelianGroupOn — the image of an abelian group along a map that
// keeps its operations is abelian: it is a group by ImageGroupOn, and
// the product commutes at image points as the image of the source's
// commutativity.
var ImageAbelianGroupOn = imageAbelianGroupOnThm{family.Add(registry.ProofEntry{
	Name: "ImageAbelianGroupOn",
	Key:  "prop_e1ce1cae9e27db1d",
	Build: family.Theorem(Statement{
		Binders: "∀G:abelian_group_on(A). ∀H:group_ops(B). ∀f:(A → B).",
		Hypotheses: []string{
			"image(f, G.carrier) = H.carrier",
			"∀x y:A. x ∈ G.carrier ∧ y ∈ G.carrier ⇒ f(x * y) = f(x) * f(y)",
			"f(G.one) = H.one",
			"∀x:A. x ∈ G.carrier ⇒ f(G.inv(x)) = H.inv(f(x))",
		},
		Conclusion: "abelian_group_on(H)",
	},
		func(
			a *Argument,
			G abelian_group.AbelianGroupFact[on.G],
			H *Expr[group.GroupOps[B]],
			f *Arrow[A, B],
			onto, mul, one, inv Fact,
		) {
			isGroup := a.Have(
				"H is a group on its carrier, the image of G's group",
				"group_on(H)",
				By(ImageGroupOn.Read(abelian_group.GroupOn.Read(G)).At(H, f), onto, mul, one, inv))
			commutes := a.Have(
				"the product commutes on H.carrier, read as the image",
				"∀u v:B. u ∈ H.carrier ∧ v ∈ H.carrier ⇒ u * v = v * u",
				onto.RwRev(),
				Simp(Fwd(set_image.ForallInImagePair)),
				Derive(func(b *Argument) {
					b.FixAs[A]("x")
					b.FixAs[A]("y")
					b.Assume()
					b.Show(
						"f(x) * f(y) and f(y) * f(x) are the images of x * y and y * x, which are equal in G",
						Simp(Rev(mul), Fwd(abelian_group.CommOn.Read(G))),
						Basic())
				}))
			a.Show(
				"a group whose product commutes on its carrier is abelian",
				By(abelian_group.AbelianGroupOn, isGroup, commutes))
		}),
})}

// ---------------------------------------------------------------------------
// The identity, composition, and isomorphisms — the chapter's coda
// ---------------------------------------------------------------------------

// IdentityHom — the identity map is a homomorphism of any group on a
// set to itself: both groups are the one in hand, the identity carries
// c into c, and it carries a product to itself. A law of the group on a
// set, stated here because its subject is the homomorphism predicate;
// both arguments name the same group record.
var IdentityHom = identityHomThm{family.Add(registry.ProofEntry{
	Name: "IdentityHom",
	Key:  "prop_66c2b436b26fe41e",

	Build: group.GroupOn.Law("group_homomorphism(G, G, identity_map)",
		Chain(Unfold(GroupHomomorphism), Simp(Fwd(functions.IdentityApply)), Basic())),
})}

// ComposeHom — the composite of two homomorphisms is a homomorphism:
// the source of the first and the target of the second are groups, the
// first map carries c into c' and the second c' into c”, and a product
// is carried to a product by the first map, then by the second.
var ComposeHom = composeHomThm{family.Add(registry.ProofEntry{
	Name: "ComposeHom",
	Key:  "prop_9712d75b5347a21a",

	Build: GroupHomomorphism.Law(Statement{
		Binders: "∀K:group_ops(C). ∀g:(B → C).",
		Hypotheses: []string{
			"group_homomorphism(H, K, g)",
		},
		Conclusion: "group_homomorphism(G, K, g ∘ f)",
	},
		func(
			a *Argument,
			hom GroupHomomorphismFact[on.G, on.H],
			K *Expr[group.GroupOps[C]],
			g *Arrow[B, C],
			homG Fact,
		) {
			source := a.Have(
				"the composite's source is the source of f",
				"group_on(G)",
				By(Source, hom))
			target := a.Have(
				"and its target is the target of g",
				"group_on(K)",
				By(Target, homG))
			// Two homomorphisms are resident, so each map's law is read at its
			// own hypothesis rather than left for the rule to pick.
			carries := a.Have(
				"g after f carries G.carrier into K.carrier: f carries "+
					"G.carrier into H.carrier, and g carries H.carrier into K.carrier",
				"∀x:A. x ∈ G.carrier ⇒ g(f(x)) ∈ K.carrier",
				Derive(func(b *Argument) {
					b.Fix("x")
					member := b.Assume()
					b.Show(
						"f(x) lies in H.carrier, and g carries it into K.carrier",
						By(Read(MapIn, homG), Read(MapIn, hom), member))
				}))
			respects := a.Have(
				"g after f carries a product of two points of G.carrier "+
					"to the product of the images: f does, then g does",
				"∀x y:A. x ∈ G.carrier ∧ y ∈ G.carrier ⇒ g(f(x * y)) = g(f(x)) * g(f(y))",
				Derive(func(b *Argument) {
					b.Fix("x")
					b.Fix("y")
					b.Assume()
					b.Show(
						"the law of f, then the law of g at the images, which lie in H.carrier",
						Simp(Fwd(Read(MapMul, hom)), Fwd(Read(MapMul, homG)), Fwd(Read(MapIn, hom))),
						Basic())
				}))
			a.Show(
				"the two groups and the composite's two laws are the "+
					"facts just shown, once g ∘ f is applied pointwise",
				Unfold(GroupHomomorphism),
				Simp(Fwd(functions.ComposeApply)),
				By(source, target, carries, respects))
		}),
})}

// GroupIsomorphismDef — a homomorphism G → H that is injective on
// G's carrier and carries it onto H's carrier.
var GroupIsomorphismDef = groupIsomorphismDefThm{family.Define(registry.DefEntry{
	Name: "GroupIsomorphismDef",
	Key:  "prop_52cbcca50a09dfc3",

	Const: "group_isomorphism",
	Type:  "group_ops(A) → group_ops(B) → (A → B) → bool",
	Equations: []string{
		"∀G:group_ops(A). ∀H:group_ops(B). ∀f:(A → B). " +
			"    group_isomorphism(G, H, f) ⇔ " +
			"    group_homomorphism(G, H, f) ∧ injective_on(G.carrier, f) ∧ image(f, G.carrier) = H.carrier",
	},
	Deps: []registry.EntryLike{GroupHomomorphism},
})}

// IsomorphismHomomorphism — an isomorphism is a homomorphism.
var IsomorphismHomomorphism = isomorphismHomomorphismThm{family.Add(registry.ProofEntry{
	Name: "IsomorphismHomomorphism",
	Key:  "prop_9a49e1ca34bc3be5",

	Build: GroupIsomorphismDef.Entry().Conjunct("group_homomorphism(G, H, f)"),
})}

// IsomorphismInjective — an isomorphism is injective on the source's
// carrier.
var IsomorphismInjective = isomorphismInjectiveThm{family.Add(registry.ProofEntry{
	Name: "IsomorphismInjective",
	Key:  "prop_516a8d8f28091414",

	Build: GroupIsomorphismDef.Entry().Conjunct("injective_on(G.carrier, f)"),
})}

// IsomorphismSurjective — an isomorphism carries the source's carrier
// onto the target's.
var IsomorphismSurjective = isomorphismSurjectiveThm{family.Add(registry.ProofEntry{
	Name: "IsomorphismSurjective",
	Key:  "prop_efd421f0ac144969",

	Build: GroupIsomorphismDef.Entry().Conjunct("image(f, G.carrier) = H.carrier"),
})}

// InnerAutomorphism — conjugation by a point g of the carrier, x ↦ g x g⁻¹,
// is an automorphism of the group. The isomorphism and homomorphism
// predicates are unfolded and their conditions closed in turn: conjugation
// keeps the carrier by its closure; it respects products, g⁻¹g cancelling
// between g x g⁻¹ and g y g⁻¹; it is one-to-one, g⁻¹ cancelling on the right
// and g on the left; and it is onto, each x being the conjugate of g⁻¹ x g.
var InnerAutomorphism = innerAutomorphismThm{family.Add(registry.ProofEntry{
	Name: "InnerAutomorphism",
	Key:  "prop_98a89813ffa516aa",
	Build: group.GroupOn.Law(Statement{
		Binders: "∀g:A.",
		Hypotheses: []string{
			"g ∈ G.carrier",
		},
		Conclusion: "group_isomorphism(G, G, λx:A. g * x * G.inv(g))",
	},
		func(a *Argument, grp group.GroupFact[on.G], g *Member[A, on.G]) {
			into := a.Have(
				"conjugation by g keeps the carrier, which is closed under products and inverses",
				"∀x:A. x ∈ G.carrier ⇒ g * x * G.inv(g) ∈ G.carrier",
				By(grp, g, group.MulIn, group.InvIn))
			a.Show(
				"conjugation by g is a homomorphism of G to itself, one-to-one on the carrier and onto it",
				Simp(Fwd(GroupIsomorphismDef), Fwd(GroupHomomorphism)),
				SplitConjAll(
					Case(
						"G is a group on its carrier",
						By(grp)),
					Case(
						"conjugation by g carries the carrier into itself",
						By(into)),
					Case(
						"conjugation by g respects products: G.inv(g) * g cancels between the conjugates of x and y",
						Derive(func(b *Argument) {
							b.FixAs[A]("x")
							b.FixAs[A]("y")
							b.Assume()
							b.Show(
								"regrouped to the right, both sides are g * (x * (y * G.inv(g)))",
								Simp(Rev(group.AssocOn), Fwd(group.InvMulCancelLeftOn), Fwd(group.MulIn), Fwd(group.InvIn)),
								Refl())
						})),
					Case(
						"conjugation by g is one-to-one on the carrier",
						Simp(Fwd(functions.InjectiveOnDef)),
						Derive(func(b *Argument) {
							x, y := b.FixAs[A]("x"), b.FixAs[A]("y")
							parts := b.Conjuncts(
								b.Assume(),
								"x lies in the carrier",
								"so does y",
								"their conjugates by g are equal")
							xm, ym := b.MemberOf[on.G](x, parts[0]), b.MemberOf[on.G](y, parts[1])
							b.Show(
								"G.inv(g) cancels on the right, and then g on the left",
								By(
									parts[2],
									group.RightCancelOn.Read(grp).At(
										group.InvIn.Read(grp).At(g),
										group.MulIn.Read(grp).At(g, xm),
										group.MulIn.Read(grp).At(g, ym)),
									group.LeftCancelOn.Read(grp).At(g, xm, ym)))
						})),
					Case(
						"conjugation by g is onto the carrier: each point x is the conjugate of G.inv(g) * x * g",
						Derive(func(b *Argument) {
							preimage := b.Have(
								"G.inv(g) * x * g lies in the carrier, and conjugation by g carries it back to x",
								"∀x:A. x ∈ G.carrier ⇒ G.inv(g) * x * g ∈ G.carrier ∧ g * (G.inv(g) * x * g) * G.inv(g) = x",
								Derive(func(c *Argument) {
									c.FixAs[A]("x")
									inCarrier := c.Assume()
									c.Do(SplitConj(
										Case(
											"the carrier is closed under products and inverses",
											By(grp, g, inCarrier, group.MulIn, group.InvIn)),
										Case(
											"g cancels G.inv(g) on the left, and g * G.inv(g) is G.one",
											Simp(
												Rev(group.AssocOn),
												Fwd(group.MulInvCancelLeftOn),
												Fwd(group.RightInverseOn),
												Fwd(group.RightIdentityOn),
												Fwd(group.MulIn),
												Fwd(group.InvIn)),
											Refl()),
									))
								}))
							b.Show(
								"the image lies in the carrier and holds every point of it",
								BySets(into, preimage))
						})),
				))
		}),
})}
