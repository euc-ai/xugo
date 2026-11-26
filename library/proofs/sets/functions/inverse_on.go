package functions

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// InverseOnDef chooses a preimage in the carrier whenever one exists.
var InverseOnDef = inverseOnDefThm{family.Define(registry.DefEntry{
	Name:  "InverseOnDef",
	Key:   "prop_1e87dde9c2939215",
	Const: "inverse_on",
	Type:  "set(A) → (A → B) → B → A",
	Equations: []string{
		"∀c:set(A). ∀f:(A → B). ∀y:B. inverse_on(c, f, y) = εx:A. x ∈ c ∧ f(x) = y",
	},
})}

// InverseOnRight — image membership inhabits the fibre selected by Hilbert choice.
var InverseOnRight = inverseOnRightThm{family.Add(registry.ProofEntry{
	Name: "InverseOnRight",
	Key:  "prop_e7bf269a90a99773",
	Build: family.Theorem(Statement{
		Binders: "∀c:set(A). ∀f:(A → B). ∀y:B.",
		Hypotheses: []string{
			"y ∈ image(f, c)",
		},
		Conclusion: "f(inverse_on(c, f, y)) = y",
	},
		func(a *Argument, c *Expr[Set[A]], f *Arrow[A, B], y *Expr[B], inImage Fact) {
			a.Do(Unfold(InverseOnDef))
			_, chosen := a.ObtainChosen(
				"image membership supplies a preimage in the carrier",
				"∃x:A. x ∈ c ∧ f(x) = y",
				inImage,
				set_basic.InImage.At(f, c, y))
			a.Show(
				"the chosen preimage maps to y",
				By(chosen))
		}),
})}

// InverseOnIn — image membership puts the chosen preimage in the carrier.
var InverseOnIn = inverseOnInThm{family.Add(registry.ProofEntry{
	Name: "InverseOnIn",
	Key:  "prop_fa5e00e3f4220438",
	Build: family.Theorem(Statement{
		Binders: "∀c:set(A). ∀f:(A → B). ∀y:B.",
		Hypotheses: []string{
			"y ∈ image(f, c)",
		},
		Conclusion: "inverse_on(c, f, y) ∈ c",
	},
		func(a *Argument, c *Expr[Set[A]], f *Arrow[A, B], y *Expr[B], inImage Fact) {
			a.Do(Unfold(InverseOnDef))
			_, chosen := a.ObtainChosen(
				"image membership supplies a preimage in the carrier",
				"∃x:A. x ∈ c ∧ f(x) = y",
				inImage,
				set_basic.InImage.At(f, c, y))
			a.Show(
				"the chosen preimage belongs to the carrier",
				By(chosen))
		}),
})}

// InverseOnLeft — injectivity identifies the chosen preimage with the original point.
var InverseOnLeft = inverseOnLeftThm{family.Add(registry.ProofEntry{
	Name: "InverseOnLeft",
	Key:  "prop_22b7d0f43ba1472e",
	Build: family.Theorem(Statement{
		Binders: "∀c:set(A). ∀f:(A → B). ∀x:A.",
		Hypotheses: []string{
			"injective_on(c, f)",
			"x ∈ c",
		},
		Conclusion: "inverse_on(c, f, f(x)) = x",
	},
		func(a *Argument, c *Expr[Set[A]], f *Arrow[A, B], x *Expr[A], onCarrier Fact) {
			inImage := a.Have(
				"x supplies a preimage of f(x)",
				"f(x) ∈ image(f, c)",
				Derive(func(b *Argument) {
					b.Do(Simp(Fwd(set_basic.InImage)))
					b.Take(x)
					b.Show(
						"x belongs to the carrier",
						By(onCarrier))
				}))
			chosenIn := a.Have(
				"the chosen preimage belongs to the carrier",
				"inverse_on(c, f, f(x)) ∈ c",
				By(inImage, InverseOnIn.At(c, f, f.Apply(x))))
			sameImage := a.Have(
				"the chosen preimage has the same image as x",
				"f(inverse_on(c, f, f(x))) = f(x)",
				By(inImage, InverseOnRight.At(c, f, f.Apply(x))))
			a.Show(
				"injectivity identifies the two preimages",
				By(sameImage, chosenIn, onCarrier, InjectiveOnDef.At(c, f)))
		}),
})}

// TwoSidedInverseBijection — cancel with the left inverse, and use the
// right inverse to choose a preimage in the source carrier.
var TwoSidedInverseBijection = twoSidedInverseBijectionThm{family.Add(registry.ProofEntry{
	Name: "TwoSidedInverseBijection",
	Key:  "prop_b1e5dbf1200d0331",
	Build: family.Theorem(Statement{
		Binders: "∀c:set(A). ∀c':set(B). ∀f:(A → B). ∀g:(B → A).",
		Hypotheses: []string{
			"∀x:A. x ∈ c ⇒ g(f(x)) = x",
			"∀y:B. y ∈ c' ⇒ f(g(y)) = y",
			"∀x:A. x ∈ c ⇒ f(x) ∈ c'",
			"∀y:B. y ∈ c' ⇒ g(y) ∈ c",
		},
		Conclusion: "injective_on(c, f) ∧ image(f, c) = c'",
	},
		func(
			arg *Argument,
			c *Expr[Set[A]],
			cPrime *Expr[Set[B]],
			f *Arrow[A, B],
			g *Arrow[B, A],
			inverses Fact,
		) {
			conditions := arg.Conjuncts(
				inverses,
				"g undoes f on c",
				"f undoes g on c'",
				"f sends c into c'",
				"g sends c' into c")
			leftInverse, rightInverse := conditions[0], conditions[1]
			mapsInto, mapsBack := conditions[2], conditions[3]
			arg.Do(SplitConj(
				Case(
					"the left inverse cancels equal images",
					Unfold(InjectiveOnDef),
					By(leftInverse)),
				Case(
					"the right inverse covers the target carrier",
					Derive(func(a *Argument) {
						preimages := a.Have(
							"each target point has a preimage in c",
							"∀y:B. y ∈ c' ⇒ ∃x:A. x ∈ c ∧ f(x) = y",
							Derive(func(b *Argument) {
								y := b.FixAs[B]()
								inTarget := b.Assume()
								b.Take(g.Apply(y))
								b.Show(
									"the inverse gives a preimage in c",
									By(inTarget, mapsBack.At(y), rightInverse.At(y)))
							}))
						a.Show(
							"membership agrees in the image and target",
							Simp(Fwd(set_basic.Extension)),
							BySets(mapsInto, preimages))
					})),
			))
		}),
})}

// InverseOnInjective — applying f recovers both inputs from their chosen preimages.
var InverseOnInjective = inverseOnInjectiveThm{family.Add(registry.ProofEntry{
	Name: "InverseOnInjective",
	Key:  "prop_925e16ea00d054f2",
	Build: family.Theorem("∀c:set(A). ∀f:(A → B). injective_on(image(f, c), inverse_on(c, f))",
		func(a *Argument, c *Expr[Set[A]], f *Arrow[A, B]) {
			a.Do(Unfold(InjectiveOnDef))
			x := a.FixAs[B]()
			y := a.FixAs[B]()
			equalPreimages := a.Assume()
			recoverX := a.Have(
				"f recovers x from its chosen preimage",
				"f(inverse_on(c, f, x)) = x",
				By(equalPreimages, InverseOnRight.At(c, f, x)))
			recoverY := a.Have(
				"f recovers y from its chosen preimage",
				"f(inverse_on(c, f, y)) = y",
				By(equalPreimages, InverseOnRight.At(c, f, y)))
			a.Show(
				"equal chosen preimages give equal inputs",
				By(recoverX, recoverY, equalPreimages))
		}),
})}

// InverseOnImage — each carrier point is recovered from its image under f.
var InverseOnImage = inverseOnImageThm{family.Add(registry.ProofEntry{
	Name: "InverseOnImage",
	Key:  "prop_a76b0c5479e5b854",
	Build: family.Theorem(Statement{
		Binders: "∀c:set(A). ∀f:(A → B).",
		Hypotheses: []string{
			"injective_on(c, f)",
		},
		Conclusion: "image(inverse_on(c, f), image(f, c)) = c",
	},
		func(a *Argument, c *Expr[Set[A]], f *Arrow[A, B], injective Fact) {
			preimages := a.Have(
				"each carrier point comes from its value under f",
				"∀x:A. x ∈ c ⇒ ∃y:B. y ∈ image(f, c) ∧ inverse_on(c, f, y) = x",
				Derive(func(b *Argument) {
					x := b.FixAs[A]()
					inCarrier := b.Assume()
					b.Take(f.Apply(x))
					b.Do(SplitConj(
						Case(
							"f sends x into its image",
							Derive(func(d *Argument) {
								d.Do(Simp(Fwd(set_basic.InImage)))
								d.Take(x)
								d.Show(
									"x supplies the preimage",
									By(inCarrier))
							})),
						Case(
							"the left inverse recovers x",
							By(injective, inCarrier, InverseOnLeft.At(c, f, x))),
					))
				}))
			a.Show(
				"membership agrees in the image and carrier",
				Simp(Fwd(set_basic.Extension)),
				BySets(preimages, InverseOnIn))
		}),
})}

// InverseOnUnique — recover the chosen preimage with the given left inverse.
var InverseOnUnique = inverseOnUniqueThm{family.Add(registry.ProofEntry{
	Name: "InverseOnUnique",
	Key:  "prop_947add1fcff7b1d5",
	Build: family.Theorem(Statement{
		Binders: "∀c:set(A). ∀f:(A → B). ∀g:(B → A). ∀y:B.",
		Hypotheses: []string{
			"∀x:A. x ∈ c ⇒ g(f(x)) = x",
			"y ∈ image(f, c)",
		},
		Conclusion: "g(y) = inverse_on(c, f, y)",
	},
		func(
			a *Argument,
			c *Expr[Set[A]],
			f *Arrow[A, B],
			g *Arrow[B, A],
			y *Expr[B],
			leftInverseOnImage Fact,
		) {
			chosenIn := a.Have(
				"the chosen preimage belongs to the carrier",
				"inverse_on(c, f, y) ∈ c",
				By(leftInverseOnImage, InverseOnIn.At(c, f, y)))
			recoverImage := a.Have(
				"f recovers y from its chosen preimage",
				"f(inverse_on(c, f, y)) = y",
				By(leftInverseOnImage, InverseOnRight.At(c, f, y)))
			a.Show(
				"the given left inverse recovers the chosen preimage",
				By(Normalized, recoverImage, chosenIn, leftInverseOnImage))
		}),
})}
