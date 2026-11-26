// linear.go — the linear maps on the sequences.
//
// `vec_linear(f)` says of a map on sequences exactly the two
// things a module homomorphism says: it carries a pointwise sum to the
// pointwise sum of the images, and it commutes with the scalar action.
// No dimension appears — linearity is a property of the map on all of
// the sequences, and a statement that needs a dimension carries `vec`
// itself.
//
// The first thing linearity gives is what every homomorphism gives:
// the identity is fixed. The additive half alone settles it, read at
// the one vector that is its own sum, and the cancellation that
// finishes the argument is the additive group's — the chapter's
// identity, inverse and associativity laws, and nothing about the
// scalars at all. It is the fact a fold over vectors needs at its base
// case, where a sum of no summands has to come out as the zero vector
// on both sides of the map.
//
// The fold itself comes second: a linear map carries a finite sum of
// vectors to the sum of the images. No induction is run here — that is
// the fold mechanism's transfer law (`monoidal.Related`), which carries
// a relation along a fold given that the relation survives the
// operation and holds at the element the fold starts from. At
// R x y ⇔ f(x) = y those two obligations ARE the additive half of
// linearity and the fixed identity above, so the member is the law's
// obligation list and one application. Again nothing about the scalars
// is spent.
//
// Third, the map the rest of the corpus reaches for: scaling by a fixed
// scalar is itself linear, so a scalar passes through a sum of
// arbitrarily many vectors, and the fold law above is the whole proof.
// That member is where the ring's multiplication is finally used as a
// COMMUTATIVE one — for the homogeneity half of `vec_linear`, which asks
// the map to commute with every scaling, not for the statement itself.
//
// Last, the linear maps are closed under what a derivative's rules do to
// them: the zero map is linear, and so are a sum, a scalar multiple and a
// composite of linear maps, and a linear map carries a difference to the
// difference of the images. Each is the ring's arithmetic read entry by
// entry, the multiple once more using that the ring is commutative.

package vec_space

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/iterate/monoidal"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/registry"
)

// LinearVecZero — the zero vector is its own sum, so additivity makes its
// image its own sum; adding the negation of that image on the left and
// regrouping cancels one copy, and the inverse pair that remains is the
// zero vector. The scalar half of linearity says nothing this argument
// needs.
var LinearVecZero = linearVecZeroThm{family.Add(registry.ProofEntry{
	Name: "LinearVecZero",
	Key:  "prop_4da51bd9712fda97",
	Build: comm_ring.CommRing.Law(Statement{
		Binders: "∀f:((num → A) → num → A).",
		Hypotheses: []string{
			"vec_linear(f)",
		},
		Conclusion: "f(vec_zero) = vec_zero",
	},
		func(a *Argument, ring Fact, f Term, linear Fact) {
			additive := a.Have(
				"f carries a sum to the sum of the images",
				"∀u v:(num → A). f(u + v) = f(u) + f(v)",
				By(linear, VecLinearDef))
			doubled := a.Have(
				"so the image of the zero vector is its own sum",
				"f(vec_zero) = f(vec_zero) + f(vec_zero)",
				CalcEq(
					Leg(
						a.Term("f(vec_zero + vec_zero)"),
						"the zero vector is its own sum, so f stands on the same argument on both sides",
						Congr(),
						By(AddLeftZero, ring)),
					FinalLeg(
						"and additivity splits the image of that sum",
						By(additive.At(a.Term("vec_zero"), a.Term("vec_zero")))),
				))
			a.Show(
				"cancel one copy: add the negation of the image on the left, regroup, and read off what is left",
				CalcEq(
					Leg(
						a.Term("vec_zero + f(vec_zero)"),
						"the zero vector is a left identity",
						By(AddLeftZero, ring)),
					Leg(
						a.Term("(-f(vec_zero) + f(vec_zero)) + f(vec_zero)"),
						"and it is what the negation of the image adds to, so that summand may be opened up",
						Congr(),
						By(AddLeftNeg, ring)),
					Leg(
						a.Term("-f(vec_zero) + (f(vec_zero) + f(vec_zero))"),
						"regroup, so that the doubled image stands alone",
						By(AddAssoc, ring)),
					Leg(
						a.Term("-f(vec_zero) + f(vec_zero)"),
						"where the doubling collapses it to one copy",
						By(doubled)),
					FinalLeg(
						"leaving an inverse pair, which is the zero vector",
						By(AddLeftNeg, ring)),
				))
		}),
})}

// LinearIterate — a linear map carries a sum of vectors to the sum of
// the images.
//
// The induction is not here. `monoidal.Related` carries a relation
// along two folds at once, and what this chapter owes it is that
// pointwise addition folds at all, plus the relation — "is the image
// under f" — with the three facts the law asks of one: that it relates
// the element the fold starts from to itself, that it survives the
// operation in both arguments, and that it holds between the vectors
// the two summands lay in at each index. The first is the fixed zero
// vector read at the fold's neutral; the second is additivity, the
// half of linearity this argument spends; the third is reflexivity,
// the second summand being the image of the first by construction.
// The scalar half of linearity is never used.
var LinearIterate = linearIterateThm{family.Add(registry.ProofEntry{
	Name: "LinearIterate",
	Key:  "prop_c3787add3052d154",
	Build: comm_ring.CommRing.Law(
		Statement{
			Binders: "∀f:((num → A) → num → A). ∀s:set(num). ∀F:(num → num → A).",
			Hypotheses: []string{
				"vec_linear(f)",
				"finite(s)",
			},
			Conclusion: "f(Σ_{i∈s} F(i)) = Σ_{i∈s} f(F(i))",
		},
		func(a *Argument, ring Fact, f *Arrow[Fun[Nat, A], Fun[Nat, A]], s *Expr[Set[Nat]],
			F *Arrow2[Nat, Nat, A], linear Fact, finite Fact) {
			// The relation the transfer law is applied at. The goal states
			// its β-reduct, so no slot of the goal spells it and it is
			// pinned by name where the law is applied; its obligations are
			// stated below in the law's own words.
			imageUnderF := a.TermAs[Fun2[Fun[Nat, A], Fun[Nat, A], Bool]](
				"λx:(num → A). λy:(num → A). f(x) = y")

			// The fold mechanism at pointwise addition, read off the ring:
			// that it folds at all, and from which element.
			vectors := MonoidalVecAdd.Read(ring)
			startsAtZero := NeutralVecAdd.Read(ring)
			fixesNeutral := a.Have(
				"which f fixes, so the relation holds at the element the fold starts from",
				"f(neutral_elem(vec_add)) = neutral_elem(vec_add)",
				By(startsAtZero, LinearVecZero, ring, linear))
			additive := a.Have(
				"f carries a sum to the sum of the images",
				"∀u v:(num → A). f(u + v) = f(u) + f(v)",
				By(linear, VecLinearDef))
			respectsAddition := a.Have(
				"so the relation survives addition in both arguments",
				"∀x₁ y₁ x₂ y₂:(num → A). f(x₁) = x₂ ∧ f(y₁) = y₂ ⇒ f(x₁ + y₁) = x₂ + y₂",
				// Normalized: substituting the two images leaves additivity
				// itself, so simplification finishes.
				By(Normalized, additive))
			pointwise := a.Have(
				"and it holds at each index between the vector laid in and its image",
				"∀i:num. i ∈ s ⇒ f(F(i)) = f(F(i))",
				Basic())

			a.Show(
				"so the transfer law carries the relation to the two folds, which is the claim",
				By(
					vectors,
					respectsAddition,
					fixesNeutral,
					finite,
					pointwise,
					Where(monoidal.Related, "R", imageUnderF)))
		}),
})}

// SmulIterate — scaling a sum of vectors is scaling each summand.
//
// Scaling by a fixed c is itself a linear map, and a linear map already
// commutes with the fold, so no induction runs here and no fold law is
// reached for: the whole content is the two things `vec_linear` asks of
// that map. Additivity is the chapter's distributive law for the scalar
// action, read at c. Commuting with the scalar action is the one place
// the ring's multiplication is used as a COMMUTATIVE one: `c • (d • u)`
// and `d • (c • u)` are each a single scaling, by the two products of
// the same pair, and those products agree. That second obligation is
// `vec_linear`'s and not the statement's — a scalar passes through a sum
// on distributivity alone — so it is what routing through linearity
// costs.
var SmulIterate = smulIterateThm{family.Add(registry.ProofEntry{
	Name: "SmulIterate",
	Key:  "prop_3613b9cae686a57b",
	Build: comm_ring.CommRing.Law(
		Statement{
			Binders: "∀c:A. ∀s:set(num). ∀F:(num → num → A).",
			Hypotheses: []string{
				"finite(s)",
			},
			Conclusion: "c • (Σ_{i∈s} F(i)) = Σ_{i∈s} c • F(i)",
		},
		func(a *Argument, ring Fact, c *Expr[A], s *Expr[Set[Nat]], F *Arrow2[Nat, Nat, A], finite Fact) {
			// The map: scaling by c, whose linearity is what the two
			// claims below establish. The goal states the fold law's
			// β-reduct, so no slot of the goal spells the map and it is
			// pinned by name where the law is applied.
			scaling := a.TermAs[Fun[Fun[Nat, A], Fun[Nat, A]]]("λu:(num → A). c • u")

			additive := a.Have(
				"scaling carries a sum to the sum of the scalings",
				"∀u v:(num → A). c • (u + v) = c • u + c • v",
				By(SmulAddLeft, ring))
			homogeneous := a.Have(
				"and it commutes with every other scaling",
				"∀d:A. ∀u:(num → A). c • (d • u) = d • (c • u)",
				Derive(func(a *Argument) {
					monoid := a.Have(
						"the ring's multiplication is a commutative monoid",
						"comm_monoid(R.mul, R.one)",
						By(comm_ring.MulMonoid, ring))
					// let the scalar d and the vector u be arbitrary
					a.Fix()
					a.Fix()
					a.Show(
						"each side is one scaling — by c * d on the left, "+
							"by d * c on the right — and the two products agree",
						Simp(Rev(SmulMul)),
						By(comm_monoid.Comm, monoid))
				}))
			linear := a.Have(
				"so scaling by c is a linear map",
				"vec_linear(λu:(num → A). c • u)",
				By(homogeneous, additive, VecLinearDef))

			a.Show(
				"and the fold law applied at that map is the claim",
				By(finite, linear, ring, Where(LinearIterate, "f", scaling)))
		}),
})}

// LinearZeroMap — the zero map is linear: the zero vector is the sum of
// two zero vectors, and every multiple of it.
var LinearZeroMap = linearZeroMapThm{family.Add(registry.ProofEntry{
	Name: "LinearZeroMap",
	Key:  "prop_92ac65f5487b1a39",
	Build: comm_ring.CommRing.Law("vec_linear(λu:(num → A). vec_zero)",
		func(a *Argument, ring Fact) {
			zero := a.TermAs[Fun[Nat, A]]("vec_zero")
			a.Show(
				"the zero vector is its own sum, and every multiple of it is the zero vector",
				Unfold(VecLinearDef),
				By(AddLeftZero.Read(ring).At(zero), SmulZero.Read(ring)))
		}),
})}

// LinearSub — a linear map carries a difference to the difference of the
// images. u is v plus u − v, so additivity makes f(u) the sum of f(v) and
// f(u − v), and taking f(v) away leaves f(u − v), entry by entry.
var LinearSub = linearSubThm{family.Add(registry.ProofEntry{
	Name: "LinearSub",
	Key:  "prop_8a7448ac8ed8877c",
	Build: comm_ring.CommRing.Law(Statement{
		Binders: "∀f:((num → A) → num → A). ∀u v:(num → A).",
		Hypotheses: []string{
			"vec_linear(f)",
		},
		Conclusion: "f(u - v) = f(u) - f(v)",
	},
		func(a *Argument, ring Fact, f *Arrow2[Fun[Nat, A], Nat, A], u, v *Expr[Fun[Nat, A]], linear Fact) {
			image := a.Have(
				"u is v plus the difference u − v, so f(u) is f(v) plus the image of the difference",
				"f(u) = f(v) + f(u - v)",
				By(linear, VecLinearDef, AddSubCancel.Read(ring).At(v, u)))
			a.Show(
				"and f(v) plus the image of the difference, less f(v), is that image, entry by entry",
				image.Rw(),
				Funext(),
				Unfold(VecAddDef),
				Unfold(VecSubDef),
				ByArith(ring))
		}),
})}

// LinearAdd — the sum of two linear maps is linear: at a sum of vectors,
// and at a scaled vector, the four images regroup entry by entry.
var LinearAdd = linearAddThm{family.Add(registry.ProofEntry{
	Name: "LinearAdd",
	Key:  "prop_94dd938f7f2b511b",
	Build: comm_ring.CommRing.Law(Statement{
		Binders: "∀f g:((num → A) → num → A).",
		Hypotheses: []string{
			"vec_linear(f)",
			"vec_linear(g)",
		},
		Conclusion: "vec_linear(λu:(num → A). f(u) + g(u))",
	},
		func(a *Argument, ring Fact, f, g *Arrow2[Fun[Nat, A], Nat, A], linearF, linearG Fact) {
			byF := a.Conjuncts(
				a.Unfolded(linearF, VecLinearDef),
				"f is additive",
				"and homogeneous")
			byG := a.Conjuncts(
				a.Unfolded(linearG, VecLinearDef),
				"g is additive",
				"and homogeneous")
			additive := a.Have(
				"the sum map carries a sum of vectors to the sum of its images",
				"∀u v:(num → A). f(u + v) + g(u + v) = (f(u) + g(u)) + (f(v) + g(v))",
				Derive(func(b *Argument) {
					b.Fix("u")
					b.Fix("v")
					b.Show(
						"each image splits, and the four regroup entry by entry",
						Simp(Fwd(byF[0]), Fwd(byG[0])),
						Funext(),
						Unfold(VecAddDef),
						ByArith(ring))
				}))
			homogeneous := a.Have(
				"and commutes with scaling",
				"∀c:A. ∀u:(num → A). f(c • u) + g(c • u) = c • (f(u) + g(u))",
				Derive(func(b *Argument) {
					b.Fix("c")
					b.Fix("u")
					b.Show(
						"each image is scaled, and the scalar distributes over the sum entry by entry",
						Simp(Fwd(byF[1]), Fwd(byG[1])),
						Funext(),
						Unfold(VecAddDef),
						Unfold(VecScalarMulDef),
						ByArith(ring))
				}))
			a.Show(
				"so the sum map is linear",
				By(additive, homogeneous, VecLinearDef))
		}),
})}

// LinearScale — a scalar multiple of a linear map is linear: the scalar
// distributes over a sum of images and, the ring being commutative,
// commutes with every other scalar, entry by entry.
var LinearScale = linearScaleThm{family.Add(registry.ProofEntry{
	Name: "LinearScale",
	Key:  "prop_a9dcf878340951ff",
	Build: comm_ring.CommRing.Law(Statement{
		Binders: "∀f:((num → A) → num → A). ∀a:A.",
		Hypotheses: []string{
			"vec_linear(f)",
		},
		Conclusion: "vec_linear(λu:(num → A). a • f(u))",
	},
		func(arg *Argument, ring Fact, f *Arrow2[Fun[Nat, A], Nat, A], a *Expr[A], linear Fact) {
			byF := arg.Conjuncts(
				arg.Unfolded(linear, VecLinearDef),
				"f is additive",
				"and homogeneous")
			additive := arg.Have(
				"the scaled map carries a sum of vectors to the sum of its images",
				"∀u v:(num → A). a • f(u + v) = a • f(u) + a • f(v)",
				Derive(func(b *Argument) {
					b.Fix("u")
					b.Fix("v")
					b.Show(
						"the image splits, and the scalar distributes over the two parts",
						Simp(Fwd(byF[0])),
						Funext(),
						Unfold(VecAddDef),
						Unfold(VecScalarMulDef),
						ByArith(ring))
				}))
			homogeneous := arg.Have(
				"and commutes with scaling",
				"∀c:A. ∀u:(num → A). a • f(c • u) = c • (a • f(u))",
				Derive(func(b *Argument) {
					b.Fix("c")
					b.Fix("u")
					b.Show(
						"the image is scaled by c, and the two scalars commute entry by entry",
						Simp(Fwd(byF[1])),
						Funext(),
						Unfold(VecScalarMulDef),
						ByArith(ring))
				}))
			arg.Show(
				"so the scaled map is linear",
				By(additive, homogeneous, VecLinearDef))
		}),
})}

// LinearCompose — a composite of linear maps is linear: f carries a sum
// to a sum and a multiple to a multiple, and g carries those on.
var LinearCompose = linearComposeThm{family.Add(registry.ProofEntry{
	Name: "LinearCompose",
	Key:  "prop_27c752abe382a6bc",
	Build: comm_ring.CommRing.Law(Statement{
		Binders: "∀f g:((num → A) → num → A).",
		Hypotheses: []string{
			"vec_linear(f)",
			"vec_linear(g)",
		},
		Conclusion: "vec_linear(g ∘ f)",
	},
		func(a *Argument, ring Fact, f, g *Arrow2[Fun[Nat, A], Nat, A], linearF, linearG Fact) {
			byF := a.Conjuncts(
				a.Unfolded(linearF, VecLinearDef),
				"f is additive",
				"and homogeneous")
			byG := a.Conjuncts(
				a.Unfolded(linearG, VecLinearDef),
				"g is additive",
				"and homogeneous")
			a.Do(
				Unfold(functions.ComposeApply),
				Unfold(VecLinearDef))
			a.Show(
				"f splits a sum or a multiple, and g splits the result again",
				Simp(Fwd(byF[0]), Fwd(byF[1]), Fwd(byG[0]), Fwd(byG[1])),
				Basic())
		}),
})}
