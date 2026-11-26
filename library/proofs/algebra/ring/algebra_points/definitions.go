package algebra_points

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

var AlgebraPointsDef = algebraPointsDefThm{family.Define(registry.DefEntry{
	Name:  "AlgebraPointsDef",
	Key:   "prop_4054db159aea424b",
	Deps:  []registry.EntryLike{},
	Const: "algebra_points",
	Type:  "ring_ops(A) → ring_ops(B) → set(A) → (A → B) → set(A → B)",
	Equations: []string{
		"∀R:ring_ops(A). ∀T:ring_ops(B). ∀S:set(A). ∀i:(A → B). " +
			"    algebra_points(R, T, S, i) = " +
			"    {f:(A → B) | " +
			"        ring_homomorphism(R, T, f) ∧ " +
			"        (∀x:A. x ∈ S ⇒ f(x) = i(x)) ∧ " +
			"        (∀x:A. x ∉ R.carrier ⇒ f(x) = T.zero)}",
	},
})}

// AlgebraPointsMember — a point is a ring map that agrees with the prescription
// on c and vanishes off the carrier.
var AlgebraPointsMember = algebraPointsMemberThm{family.Add(registry.ProofEntry{
	Name: "AlgebraPointsMember",
	Key:  "prop_945f8c69757f1bf2",
	Build: family.Theorem(
		"∀R:ring_ops(A). ∀T:ring_ops(B). ∀c:set(A). ∀i f:(A → B). "+
			"    f ∈ algebra_points(R, T, c, i) ⇔ "+
			"    ring_homomorphism(R, T, f) ∧ "+
			"    (∀x:A. x ∈ c ⇒ f(x) = i(x)) ∧ "+
			"    (∀x:A. x ∉ R.carrier ⇒ f(x) = T.zero)",
		func(a *Argument, R *Expr[RingOps[A]], T *Expr[RingOps[B]], c *Expr[Set[A]], i, f *Arrow[A, B]) {
			a.Show(
				"the points are this set",
				BySets(AlgebraPointsDef.At(R, T, c, i)))
		}),
})}

// AlgebraPointsOfRingMap — a ring map on R agreeing with the prescription on c ⊆ R is
// a point once it is set to zero off R, which changes nothing on R.
var AlgebraPointsOfRingMap = algebraPointsOfRingMapThm{family.Add(registry.ProofEntry{
	Name: "AlgebraPointsOfRingMap",
	Key:  "prop_ec1e57adf947bb23",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀T:ring_ops(B). ∀c:set(A). ∀i ψ:(A → B).",
		Hypotheses: []string{
			"ring_homomorphism(R, T, ψ)",
			"c ⊆ R.carrier",
			"∀x:A. x ∈ c ⇒ ψ(x) = i(x)",
		},
		Conclusion: "«zeroed» ∈ algebra_points(R, T, c, i) ∧ (∀x:A. x ∈ R.carrier ⇒ «zeroed»(x) = ψ(x))",
		Abbrev: Abbrev{
			{Name: "zeroed", Text: "λx:A. COND(x ∈ R.carrier, ψ(x), T.zero)"},
		},
	}, func(
		a *Argument,
		R *Expr[RingOps[A]],
		T *Expr[RingOps[B]],
		c *Expr[Set[A]],
		i, ψ *Arrow[A, B],
		hom ring_homomorphism.RingHomomorphismFact[on.R, on.T],
		inside, agrees Fact,
	) {
		zeroed := a.TermAs[Fun[A, B]]("«zeroed»")
		onR := a.Have(
			"zeroing off R changes nothing on R",
			"∀x:A. x ∈ R.carrier ⇒ «zeroed»(x) = ψ(x)",
			Derive(func(b *Argument) {
				b.FixAs[A]("x")
				b.Show(
					"on R the condition holds",
					By(b.Assume()))
			}))
		mapped := a.Have(
			"so it keeps a ring map",
			"ring_homomorphism(R, T, «zeroed»)",
			By(hom, onR, ring_homomorphism.RingHomCongruence.At(R, T, ψ, zeroed)))
		onC := a.Have(
			"on c, inside R, it is ψ, which is i",
			"∀x:A. x ∈ c ⇒ «zeroed»(x) = i(x)",
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				xIn := b.Assume()
				b.Show(
					"x lies in R",
					By(xIn, inside, onR.At(x), agrees.At(x), set_basic.SubsetDef))
			}))
		a.Show(
			"a ring map agreeing with i on c and zero off R is a point",
			By(mapped, onC, onR, AlgebraPointsMember.At(R, T, c, i, zeroed)))
	}),
})}

// AlgebraPointsChangeTarget — a point with values in a part of S that lie in a
// subring of S is a point with values in that subring: a ring map into the part
// is a ring map into S, whose image lies in the subring.
var AlgebraPointsChangeTarget = algebraPointsChangeTargetThm{family.Add(registry.ProofEntry{
	Name: "AlgebraPointsChangeTarget",
	Key:  "prop_504d06c9a9965940",
	Build: family.Theorem(Statement{
		Binders: "∀S:comm_ring_on(B). ∀R:ring_ops(A). ∀c:set(A). ∀i f:(A → B). ∀U V:set(B).",
		Hypotheses: []string{
			"U ⊆ S.carrier",
			"subring(S, V)",
			"∀x:A. x ∈ R.carrier ⇒ f(x) ∈ V",
			"f ∈ algebra_points(R, restrict_ring(S, U), c, i)",
		},
		Conclusion: "f ∈ algebra_points(R, restrict_ring(S, V), c, i)",
	}, func(
		a *Argument,
		S comm_ring.CommRingFact[on.S],
		R *Expr[RingOps[A]],
		c *Expr[Set[A]],
		i, f *Arrow[A, B],
		U, V *Expr[Set[B]],
		inside, subring, values, point Fact,
	) {
		ringS := a.TermAs[RingOps[B]]("S")
		parts := a.Conjuncts(
			a.Have(
				"f is a ring map into U, agreeing with i and vanishing off the carrier",
				"ring_homomorphism(R, restrict_ring(S, U), f) ∧ "+
					"(∀x:A. x ∈ c ⇒ f(x) = i(x)) ∧ "+
					"(∀x:A. x ∉ R.carrier ⇒ f(x) = S.zero)",
				By(point, AlgebraPointsMember.At(R, a.TermAs[RingOps[B]]("restrict_ring(S, U)"), c, i, f))),
			"f is a ring map into U",
			"f agrees with i",
			"f vanishes off the carrier")
		intoS := a.Have(
			"so it is a ring map into S",
			"ring_homomorphism(R, S, f)",
			By(parts[0], S, inside, ring_homomorphism.RingHomExtendTarget.At(R, ringS, f, U)))
		intoV := a.Have(
			"and its values lie in the subring V",
			"ring_homomorphism(R, restrict_ring(S, V), f)",
			By(intoS, subring, values, ring_homomorphism.RingHomCorestrict.At(R, ringS, f, V)))
		a.Show(
			"which makes it a point with values in V",
			By(
				intoV,
				parts[1],
				parts[2],
				AlgebraPointsMember.At(R, a.TermAs[RingOps[B]]("restrict_ring(S, V)"), c, i, f)))
	}),
})}

// AlgebraPointsInSubring — a point with values in a subring V of S is a point
// in S taking the carrier into V: a ring map into V is a ring map into S, and a
// ring map into S with values in V is one into V.
var AlgebraPointsInSubring = algebraPointsInSubringThm{family.Add(registry.ProofEntry{
	Name: "AlgebraPointsInSubring",
	Key:  "prop_120438cf1b6a047e",
	Build: family.Theorem(Statement{
		Binders:    "∀S:comm_ring_on(B). ∀R:ring_ops(A). ∀c:set(A). ∀i f:(A → B). ∀V:set(B).",
		Hypotheses: []string{"subring(S, V)"},
		Conclusion: "f ∈ algebra_points(R, restrict_ring(S, V), c, i) ⇔ " +
			"f ∈ algebra_points(R, S, c, i) ∧ (∀x:A. x ∈ R.carrier ⇒ f(x) ∈ V)",
	}, func(
		a *Argument,
		S comm_ring.CommRingFact[on.S],
		R *Expr[RingOps[A]],
		c *Expr[Set[A]],
		i, f *Arrow[A, B],
		V *Expr[Set[B]],
		subring Fact,
	) {
		ringS := a.TermAs[RingOps[B]]("S")
		ringV := a.TermAs[RingOps[B]]("restrict_ring(S, V)")
		a.Iff()
		a.Forward(
			"a point in V is a point in S with values in V",
			func(b *Argument, point Fact) {
				parts := b.Conjuncts(
					b.Have(
						"f is a ring map into V, agreeing with i and vanishing off the carrier",
						"ring_homomorphism(R, restrict_ring(S, V), f) ∧ "+
							"(∀x:A. x ∈ c ⇒ f(x) = i(x)) ∧ "+
							"(∀x:A. x ∉ R.carrier ⇒ f(x) = S.zero)",
						By(point, AlgebraPointsMember.At(R, ringV, c, i, f))),
					"f is a ring map into V",
					"f agrees with i",
					"f vanishes off the carrier")
				intoS := b.Have(
					"so it is a ring map into S",
					"ring_homomorphism(R, S, f)",
					By(
						comm_ring.SubringSubset.Read(subring),
						S,
						parts[0],
						ring_homomorphism.RingHomExtendTarget.At(R, ringS, f, V)))
				values := b.Have(
					"its values lie in V",
					"∀x:A. x ∈ R.carrier ⇒ f(x) ∈ V",
					By(ring_homomorphism.MapIn.Read(parts[0])))
				b.Show(
					"these are the clauses of a point in S",
					By(intoS, parts[1], parts[2], values, AlgebraPointsMember.At(R, ringS, c, i, f)))
			})
		a.Backward(
			"a point in S with values in V is a point in V",
			func(b *Argument, given Fact) {
				held := b.Conjuncts(
					given,
					"f is a point in S",
					"its values lie in V")
				parts := b.Conjuncts(
					b.Have(
						"f is a ring map into S, agreeing with i and vanishing off the carrier",
						"ring_homomorphism(R, S, f) ∧ (∀x:A. x ∈ c ⇒ f(x) = i(x)) ∧ (∀x:A. x ∉ R.carrier ⇒ f(x) = S.zero)",
						By(held[0], AlgebraPointsMember.At(R, ringS, c, i, f))),
					"f is a ring map into S",
					"f agrees with i",
					"f vanishes off the carrier")
				intoV := b.Have(
					"so it is a ring map into V",
					"ring_homomorphism(R, restrict_ring(S, V), f)",
					By(parts[0], subring, held[1], ring_homomorphism.RingHomCorestrict.At(R, ringS, f, V)))
				b.Show(
					"these are the clauses of a point in V",
					By(intoV, parts[1], parts[2], AlgebraPointsMember.At(R, ringV, c, i, f)))
			})
	}),
})}

// PointDeterminedByKernel — two points of a ring over l with values in l and one
// kernel are equal: x - φ(x) lies in the kernel of φ, a point fixing l, so in
// that of ψ, which reads ψ(x) = φ(x). Off the ring both vanish.
var PointDeterminedByKernel = pointDeterminedByKernelThm{family.Add(registry.ProofEntry{
	Name: "PointDeterminedByKernel",
	Key:  "prop_4e2715ea1e4f2225",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀S l:set(A). ∀φ ψ:(A → A).",
		Hypotheses: []string{
			"l ⊆ S",
			"φ ∈ «valuePoints»",
			"ψ ∈ «valuePoints»",
			"{x:A | x ∈ S ∧ φ(x) = R.zero} = {x:A | x ∈ S ∧ ψ(x) = R.zero}",
		},
		Conclusion: "φ = ψ",
		Abbrev: Abbrev{
			{Name: "valuePoints", Text: "algebra_points(restrict_ring(R, S), restrict_ring(R, l), l, λx:A. x)"},
		},
	}, func(
		a *Argument,
		R *Expr[RingOps[A]],
		S, l *Expr[Set[A]],
		φ, ψ *Arrow[A, A],
		inside, pointφ, pointψ, kernels Fact,
	) {
		source := a.TermAs[RingOps[A]]("restrict_ring(R, S)")
		target := a.TermAs[RingOps[A]]("restrict_ring(R, l)")
		identity := a.TermAs[Fun[A, A]]("λx:A. x")
		first := a.Conjuncts(
			a.Have(
				"φ is a ring map fixing l and vanishing off S",
				"ring_homomorphism(restrict_ring(R, S), restrict_ring(R, l), φ) ∧ "+
					"(∀x:A. x ∈ l ⇒ φ(x) = x) ∧ "+
					"(∀x:A. x ∉ S ⇒ φ(x) = R.zero)",
				By(pointφ, AlgebraPointsMember.At(source, target, l, identity, φ))),
			"φ is a ring map",
			"it fixes l",
			"it vanishes off S")
		second := a.Conjuncts(
			a.Have(
				"so is ψ",
				"ring_homomorphism(restrict_ring(R, S), restrict_ring(R, l), ψ) ∧ "+
					"(∀x:A. x ∈ l ⇒ ψ(x) = x) ∧ "+
					"(∀x:A. x ∉ S ⇒ ψ(x) = R.zero)",
				By(pointψ, AlgebraPointsMember.At(source, target, l, identity, ψ))),
			"ψ is a ring map",
			"it fixes l",
			"it vanishes off S")
		mapφ, fixesφ, offφ := first[0], first[1], first[2]
		mapψ, fixesψ, offψ := second[0], second[1], second[2]
		ring := a.Have(
			"S is a ring, the source of φ",
			"comm_ring_on(restrict_ring(R, S))",
			By(mapφ, ring_homomorphism.RingHomomorphism.At(source, target, φ)))
		agree := a.Have(
			"on S the two points agree",
			"∀x:A. x ∈ S ⇒ φ(x) = ψ(x)",
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				inS := b.Assume()
				value := b.TermAs[A]("φ(x)")
				valueInL := b.Have(
					"φ(x) lies in l",
					"φ(x) ∈ l",
					By(inS, ring_homomorphism.MapIn.Read(mapφ).AsFact().At(x)))
				otherInL := b.Have(
					"so does ψ(x)",
					"ψ(x) ∈ l",
					By(inS, ring_homomorphism.MapIn.Read(mapψ).AsFact().At(x)))
				values := b.Conjuncts(
					b.Have(
						"both lie in S, which holds l",
						"φ(x) ∈ S ∧ ψ(x) ∈ S",
						By(valueInL, otherInL, inside, set_basic.SubsetDef)),
					"φ(x) lies in S",
					"ψ(x) lies in S")
				valueInS, otherInS := values[0], values[1]
				differenceIn := b.Have(
					"x - φ(x) lies in S",
					"R.sub(x, φ(x)) ∈ S",
					By(inS, valueInS, comm_ring.SubIn.Read(ring).AsFact().At(x, value)))
				underφ := b.Have(
					"φ fixes φ(x), so it sends x - φ(x) to φ(x) - φ(x)",
					"φ(R.sub(x, φ(x))) = R.sub(φ(x), φ(x))",
					By(
						Normalized,
						fixesφ.At(value),
						valueInL,
						valueInS,
						inS,
						ring_homomorphism.MapSub.Read(mapφ).AsFact().At(x, value)))
				underψ := b.Have(
					"ψ fixes φ(x) too, so it sends x - φ(x) to ψ(x) - φ(x)",
					"ψ(R.sub(x, φ(x))) = R.sub(ψ(x), φ(x))",
					By(
						Normalized,
						fixesψ.At(value),
						valueInL,
						valueInS,
						inS,
						ring_homomorphism.MapSub.Read(mapψ).AsFact().At(x, value)))
				cancel := b.Have(
					"φ(x) - φ(x) is zero",
					"R.sub(φ(x), φ(x)) = R.zero",
					ByArith(ring, valueInS))
				inKernel := b.Have(
					"so x - φ(x) lies in the kernel of φ, which is that of ψ",
					"ψ(R.sub(x, φ(x))) = R.zero",
					BySets(differenceIn, underφ, cancel, kernels))
				b.Show(
					"which reads ψ(x) = φ(x)",
					ByArith(ring, valueInS, otherInS, underψ, inKernel))
			}))
		a.Show(
			"off S both are zero, so they are one function",
			Funext(),
			a.ForEach(func(x *Expr[A]) Action {
				return By(Normalized, offφ.At(x), offψ.At(x), agree.At(x))
			}))
	}),
})}
