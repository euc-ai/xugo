// inverse.go — the inverse's own laws, derived from the field axioms and the
// ring's, and the square roots of an element: z and −z for a square z·z,
// so two to each nonzero square where 2 ≠ 0.

package field

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/abelian_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/registry"
)

// MulRightInverseOn — a nonzero member has an inverse from the right as
// well: the product commutes on the carrier, which holds the inverse,
// and in the other order it is the left-inverse axiom.
var MulRightInverseOn = mulRightInverseOnThm{family.Add(registry.ProofEntry{
	Name: "MulRightInverseOn",
	Key:  "prop_cb9df24ed65fccdd",
	Build: FieldOn.Law(Statement{
		Binders: "∀x:A.",
		Hypotheses: []string{
			"x ∈ F.carrier",
			"x ≠ F.zero",
		},
		Conclusion: "x * F.inv(x) = F.one",
	},
		func(a *Argument, field FieldFact[on.F], x *Member[A, on.F], nonzero Fact) {
			commute := Read(comm_monoid.CommOn, Read(comm_ring.MulMonoidOn, Read(RingOn, field)))
			a.Do(CalcEq(
				Leg(
					a.TermAs[A]("F.inv(x) * x"),
					"the same two factors, in the other order",
					By(commute, x, field, InvIn)),
				FinalLeg(
					"and in that order the product is the left-inverse axiom at x, which x ≠ zero unlocks",
					By(x, nonzero, At(Read(MulLeftInverseOn, field), x))),
			))
		}),
})}

// MulRightInverse — MulRightInverseOn on the whole type.
var MulRightInverse = mulRightInverseThm{family.Add(registry.ProofEntry{
	Name: "MulRightInverse",
	Key:  "prop_f650a82133e1f031",
	Build: FieldAtUniverse.Law(Statement{
		Binders: "∀x:A.",
		Hypotheses: []string{
			"x ≠ F.zero",
		},
		Conclusion: "x * F.inv(x) = F.one",
	}, MulRightInverseOn),
})}

// InvLeftUniqueOn — a factor that multiplies y to one is inv(y) itself.
// y cannot be zero, since x * zero is zero and a field's one is not;
// so y has its left inverse, and inv(y), set against the product
// x * y that is one, trades places with x, meets y and leaves x. The
// monoid laws the chain cites ask only that inv(y) lie in F.carrier beside x
// and y, which the closure under the inverse supplies.
var InvLeftUniqueOn = invLeftUniqueOnThm{family.Add(registry.ProofEntry{
	Name: "InvLeftUniqueOn",
	Key:  "prop_d26fa3382e9c90e7",
	Build: FieldOn.Law(Statement{
		Binders: "∀x y:A.",
		Hypotheses: []string{
			"x ∈ F.carrier",
			"y ∈ F.carrier",
			"x * y = F.one",
		},
		Conclusion: "F.inv(y) = x",
	},
		func(a *Argument, field FieldFact[on.F], x, y *Member[A, on.F], product Fact) {
			ring := Read(RingOn, field)
			monoid := Read(comm_ring.MulMonoidOn, ring)

			nonzero := a.Unless(
				a.Term("y = F.zero"),
				"y = zero would make x * y zero, and the hypothesis would then say one is zero",
				Given(func(b *Argument, isZero Fact) {
					oneIsZero := b.Have(
						"one would be x * zero, which is zero",
						"F.one = F.zero",
						CalcEq(
							Leg(
								b.TermAs[A]("x * y"),
								"the hypothesis",
								By(product)),
							Leg(
								b.TermAs[A]("x * F.zero"),
								"y is zero",
								isZero.Rw(),
								Basic()),
							FinalLeg(
								"zero absorbs a member",
								By(Read(comm_ring.MulRightZeroOn, ring), x, y)),
						))
					b.Show(
						"but one is not zero",
						By(oneIsZero, Read(OneNotZeroOn, field)))
				}))

			leftInverse := a.Have(
				"a nonzero member y has a left inverse",
				"F.inv(y) * y = F.one",
				By(x, y, nonzero, At(Read(MulLeftInverseOn, field), y)))

			a.Show(
				"inv(y) absorbs the product x * y, which is one, and meets its own y beside x",
				CalcEq(
					Leg(
						a.TermAs[A]("F.inv(y) * F.one"),
						"one is the identity",
						By(Read(comm_monoid.RightIdentityOn, monoid), x, y, field, InvIn)),
					Leg(
						a.TermAs[A]("F.inv(y) * (x * y)"),
						"the hypothesis: one is x * y",
						product.Rw(),
						Basic()),
					Leg(
						a.TermAs[A]("x * (F.inv(y) * y)"),
						"inv(y) and x trade places",
						By(Read(comm_monoid.LeftCommOn, monoid), x, y, field, InvIn)),
					Leg(
						a.TermAs[A]("x * F.one"),
						"inv(y) * y is one",
						leftInverse.Rw(),
						Basic()),
					FinalLeg(
						"and one drops off x",
						By(Read(comm_monoid.RightIdentityOn, monoid), x, y)),
				))
		}),
})}

// InvLeftUnique — InvLeftUniqueOn on the whole type.
var InvLeftUnique = invLeftUniqueThm{family.Add(registry.ProofEntry{
	Name: "InvLeftUnique",
	Key:  "prop_943d7e161a125e18",
	Build: FieldAtUniverse.Law(Statement{
		Binders: "∀x y:A.",
		Hypotheses: []string{
			"x * y = F.one",
		},
		Conclusion: "F.inv(y) = x",
	}, InvLeftUniqueOn),
})}

// InvRightUniqueOn — a factor that multiplies x to one from the right is
// inv(x) itself: the product commutes on the carrier, which holds both
// factors, so read in the other order it is y * x = one, and there
// InvLeftUniqueOn names y as the inverse of x.
var InvRightUniqueOn = invRightUniqueOnThm{family.Add(registry.ProofEntry{
	Name: "InvRightUniqueOn",
	Key:  "prop_1d0f9891f99de9ad",
	Build: FieldOn.Law(Statement{
		Binders: "∀x y:A.",
		Hypotheses: []string{
			"x ∈ F.carrier",
			"y ∈ F.carrier",
			"x * y = F.one",
		},
		Conclusion: "F.inv(x) = y",
	},
		func(a *Argument, field FieldFact[on.F], x, y *Member[A, on.F], product Fact) {
			commute := Read(comm_monoid.CommOn, Read(comm_ring.MulMonoidOn, Read(RingOn, field)))
			commuted := a.Have(
				"the hypothesis, its two factors read in the other order",
				"y * x = F.one",
				CalcEq(
					Leg(
						a.TermAs[A]("x * y"),
						"the same two factors, in the other order",
						By(commute, x, y)),
					FinalLeg(
						"and that product is one by hypothesis",
						By(product)),
				))
			a.Show(
				"uniqueness of the left factor, at y * x = one, names y as inv(x)",
				By(commuted, x, y, At(Read(InvLeftUniqueOn, field), y, x)))
		}),
})}

// InvRightUnique — InvRightUniqueOn on the whole type.
var InvRightUnique = invRightUniqueThm{family.Add(registry.ProofEntry{
	Name: "InvRightUnique",
	Key:  "prop_270e9c32da098101",
	Build: FieldAtUniverse.Law(Statement{
		Binders: "∀x y:A.",
		Hypotheses: []string{
			"x * y = F.one",
		},
		Conclusion: "F.inv(x) = y",
	}, InvRightUniqueOn),
})}

// InvInvOn — the inverse is an involution on the carrier. To know the
// inverse of inv(x), exhibit a factor that multiplies inv(x) to one: a
// nonzero x does, x * inv(x) being one by the right-inverse law, and
// such a factor is unique among the members of F.carrier, which hold inv(x)
// beside x — so it is inv(inv(x)).
// At zero there is nothing to exhibit and nothing to prove, the inverse
// of zero being zero.
var InvInvOn = invInvOnThm{family.Add(registry.ProofEntry{
	Name: "InvInvOn",
	Key:  "prop_1831651ecee90639",
	Build: FieldOn.Law(Statement{
		Binders: "∀x:A.",
		Hypotheses: []string{
			"x ∈ F.carrier",
		},
		Conclusion: "F.inv(F.inv(x)) = x",
	},
		func(a *Argument, field FieldFact[on.F], x *Member[A, on.F]) {
			nonzero := a.Unless(
				a.Term("x = F.zero"),
				"at x = zero both sides are zero, the inverse of zero being zero",
				Given(func(b *Argument, isZero Fact) {
					b.Do(isZero.Rw())
					b.Show(
						"the inverse of zero is zero, inside and out",
						Simp(Fwd(Read(InvZeroOn, field))),
						Refl())
				}))

			unit := a.Have(
				"a nonzero member x multiplies its own inverse to one",
				"x * F.inv(x) = F.one",
				By(x, nonzero, At(Read(MulRightInverseOn, field), x)))

			a.Show(
				"so x is the factor that multiplies inv(x) to one, which is inv(inv(x))",
				By(unit, x, field, InvIn, At(Read(InvLeftUniqueOn, field), x, a.TermAs[A]("F.inv(x)"))))
		}),
})}

// InvInv — InvInvOn on the whole type.
var InvInv = invInvThm{family.Add(registry.ProofEntry{
	Name:  "InvInv",
	Key:   "prop_4f3e2a06c6cb1eae",
	Build: FieldAtUniverse.Law("∀x:A. F.inv(F.inv(x)) = x", InvInvOn),
})}

// InvOneOn — one is its own inverse. One times one is one by the identity
// law, and the inverse's uniqueness, at the two members one and one,
// names one as the inverse of one; uniqueness asks no factor to be
// nonzero, so no nonzero hypothesis enters.
var InvOneOn = invOneOnThm{family.Add(registry.ProofEntry{
	Name: "InvOneOn",
	Key:  "prop_8f7c74568c7290d5",
	Build: FieldOn.Law("F.inv(F.one) = F.one",
		func(a *Argument, field FieldFact[on.F]) {
			one := a.TermAs[A]("F.one")
			ring := Read(RingOn, field)
			identity := Read(comm_monoid.LeftIdentityOn, Read(comm_ring.MulMonoidOn, ring))
			a.Show(
				"one is its own square, and a factor that multiplies one to one is its inverse",
				By(At(identity, one), At(Read(InvLeftUniqueOn, field), one, one), Read(comm_ring.OneIn, ring)))
		}),
})}

// InvOne — InvOneOn on the whole type.
var InvOne = invOneThm{family.Add(registry.ProofEntry{
	Name:  "InvOne",
	Key:   "prop_b3f2f5ee954a69e1",
	Build: FieldAtUniverse.Law("F.inv(F.one) = F.one", InvOneOn),
})}

// InvMulOn — the inverse is multiplicative on the carrier, with no
// hypothesis on the factors. When both are nonzero, inv(x) * inv(y)
// multiplies x * y to one: the four factors regroup so that each
// inverse stands beside the factor it inverts, and InvLeftUniqueOn then
// names inv(x) * inv(y) as inv(x * y) — the regrouping asks only that
// the inverses and the product lie in F.carrier, which the closure laws supply.
// When a factor is zero, so is the product, and both sides are zero:
// the inverse of zero is zero, and zero absorbs the other factor, on
// whichever side it stands.
var InvMulOn = invMulOnThm{family.Add(registry.ProofEntry{
	Name: "InvMulOn",
	Key:  "prop_b83f12e4cf4d6df8",
	Build: FieldOn.Law(Statement{
		Binders: "∀x y:A.",
		Hypotheses: []string{
			"x ∈ F.carrier",
			"y ∈ F.carrier",
		},
		Conclusion: "F.inv(x * y) = F.inv(x) * F.inv(y)",
	},
		func(a *Argument, field FieldFact[on.F], x, y *Member[A, on.F]) {
			ring := Read(RingOn, field)
			monoid := Read(comm_ring.MulMonoidOn, ring)

			xNonzero := a.Unless(
				a.Term("x = F.zero"),
				"x = zero: the product is zero as well, and both sides are zero",
				Given(func(b *Argument, isZero Fact) {
					b.Show(
						"inv(zero * y) and inv(zero) * inv(y) both collapse to zero",
						isZero.Rw(),
						Simp(
							Fwd(Read(comm_ring.MulLeftZeroOn, ring)),
							Fwd(Read(InvZeroOn, field)),
							Fwd(Read(InvIn, field))),
						Refl())
				}))
			yNonzero := a.Unless(
				a.Term("y = F.zero"),
				"y = zero: the same collapse, the zero factor on the right",
				Given(func(b *Argument, isZero Fact) {
					b.Show(
						"inv(x * zero) and inv(x) * inv(zero) both collapse to zero",
						isZero.Rw(),
						Simp(
							Fwd(Read(comm_ring.MulRightZeroOn, ring)),
							Fwd(Read(InvZeroOn, field)),
							Fwd(Read(InvIn, field))),
						Refl())
				}))

			passes := a.Have(
				"inv(y) passes x to stand beside y",
				"F.inv(y) * (x * y) = x * (F.inv(y) * y)",
				By(Read(comm_monoid.LeftCommOn, monoid), x, y, field, InvIn))
			inverts := a.Have(
				"inv(x) * inv(y) multiplies x * y to one",
				"(F.inv(x) * F.inv(y)) * (x * y) = F.one",
				CalcEq(
					Leg(
						a.TermAs[A]("F.inv(x) * (F.inv(y) * (x * y))"),
						"regroup, so that inv(y) faces x * y",
						By(Read(comm_monoid.AssocOn, monoid), x, y, field, InvIn, Read(comm_ring.MulIn, ring))),
					Leg(
						a.TermAs[A]("F.inv(x) * (x * (F.inv(y) * y))"),
						"the regrouping above, under inv(x) * ·",
						passes.Rw(),
						Basic()),
					Leg(
						a.TermAs[A]("F.inv(x) * (x * F.one)"),
						"y's left inverse, which y ≠ zero unlocks",
						By(Normalized, x, y, yNonzero, At(Read(MulLeftInverseOn, field), y))),
					Leg(
						a.TermAs[A]("F.inv(x) * x"),
						"one drops off x",
						By(Normalized, x, y, At(Read(comm_monoid.RightIdentityOn, monoid), x))),
					FinalLeg(
						"and x's left inverse, which x ≠ zero unlocks",
						By(xNonzero, x, y, At(Read(MulLeftInverseOn, field), x))),
				))

			a.Show(
				"a factor that multiplies x * y to one is its inverse",
				By(
					inverts,
					x,
					y,
					field,
					InvIn,
					Read(comm_ring.MulIn, ring),
					At(Read(InvLeftUniqueOn, field), a.TermAs[A]("F.inv(x) * F.inv(y)"), a.TermAs[A]("x * y"))))
		}),
})}

// InvMul — InvMulOn on the whole type.
var InvMul = invMulThm{family.Add(registry.ProofEntry{
	Name:  "InvMul",
	Key:   "prop_4ffbc7dbb58b9f3e",
	Build: FieldAtUniverse.Law("∀x y:A. F.inv(x * y) = F.inv(x) * F.inv(y)", InvMulOn),
})}

// InvNegOn — the inverse of a negative is the negative of the inverse.
// Away from zero the two signs of -inv(x) * -x cancel, leaving
// inv(x) * x, which is one; and a factor in F.carrier that multiplies -x to one
// is inv(-x) — both lie in F.carrier, which is closed under negation and under
// the inverse. At zero both sides are zero, since negation and the
// inverse each fix zero.
var InvNegOn = invNegOnThm{family.Add(registry.ProofEntry{
	Name: "InvNegOn",
	Key:  "prop_d68e53af0c1ffe0c",
	Build: FieldOn.Law(Statement{
		Binders: "∀x:A.",
		Hypotheses: []string{
			"x ∈ F.carrier",
		},
		Conclusion: "F.inv(-x) = -F.inv(x)",
	},
		func(a *Argument, field FieldFact[on.F], x *Member[A, on.F]) {
			ring := Read(RingOn, field)

			nonzero := a.Unless(
				a.Term("x = F.zero"),
				"at zero both sides are zero: negation fixes zero, and so does the inverse",
				Given(func(b *Argument, isZero Fact) {
					additive := Read(abelian_group.GroupOn, Read(comm_ring.AddGroupOn, ring))
					b.Show(
						"-zero is zero and inv(zero) is zero",
						isZero.Rw(),
						Simp(Fwd(Read(group.InvOneOn, additive)), Fwd(Read(InvZeroOn, field))),
						Refl())
				}))

			unit := a.Have(
				"-inv(x) is an inverse of -x",
				"-F.inv(x) * -x = F.one",
				CalcEq(
					Leg(
						a.TermAs[A]("F.inv(x) * x"),
						"the two signs cancel",
						By(Read(comm_ring.MulNegNegOn, ring), x, field, InvIn)),
					FinalLeg(
						"and a nonzero x has its left inverse",
						By(x, nonzero, At(Read(MulLeftInverseOn, field), x))),
				))
			a.Show(
				"a factor that multiplies -x to one is inv(-x)",
				By(
					unit,
					x,
					field,
					InvIn,
					Read(comm_ring.NegIn, ring),
					At(Read(InvLeftUniqueOn, field), a.TermAs[A]("-F.inv(x)"), a.TermAs[A]("-x"))))
		}),
})}

// InvNeg — InvNegOn on the whole type.
var InvNeg = invNegThm{family.Add(registry.ProofEntry{
	Name:  "InvNeg",
	Key:   "prop_302ce5e66a9ef9d3",
	Build: FieldAtUniverse.Law("∀x:A. F.inv(-x) = -F.inv(x)", InvNegOn),
})}

// InvEqZeroOn — an inverse vanishes exactly at zero. The inverse of zero
// is zero by the field's convention. Conversely, a nonzero member x has
// inv(x) as its left inverse, so were inv(x) zero, one would be zero * x,
// which is zero — and a field's one is not.
var InvEqZeroOn = invEqZeroOnThm{family.Add(registry.ProofEntry{
	Name: "InvEqZeroOn",
	Key:  "prop_25241fc7f6b2ef03",
	Build: FieldOn.Law(Statement{
		Binders: "∀x:A.",
		Hypotheses: []string{
			"x ∈ F.carrier",
		},
		Conclusion: "F.inv(x) = F.zero ⇔ x = F.zero",
	},
		func(a *Argument, field FieldFact[on.F], x *Member[A, on.F]) {
			a.Iff()
			a.Forward(
				"a nonzero member x would make one zero",
				func(b *Argument, vanishes Fact) {
					nonzero := b.SupposeNot()
					oneIsZero := b.Have(
						"x's left inverse, being zero, would carry one to zero",
						"F.one = F.zero",
						CalcEq(
							Leg(
								b.TermAs[A]("F.inv(x) * x"),
								"x is a nonzero member, so inv(x) is its left inverse",
								By(x, nonzero, At(Read(MulLeftInverseOn, field), x))),
							Leg(
								b.TermAs[A]("F.zero * x"),
								"the hypothesis: inv(x) is zero",
								vanishes.Rw(),
								Basic()),
							FinalLeg(
								"zero absorbs a member on the left",
								By(Read(comm_ring.MulLeftZeroOn, Read(RingOn, field)), x)),
						))
					b.Show(
						"but one is not zero",
						By(oneIsZero, Read(OneNotZeroOn, field)))
				})
			a.Backward(
				"x is zero, and the inverse of zero is zero",
				func(b *Argument, isZero Fact) {
					b.Do(isZero.Rw())
					b.Show(
						"inv(zero) is zero",
						By(Read(InvZeroOn, field)))
				})
		}),
})}

// InvEqZero — InvEqZeroOn on the whole type.
var InvEqZero = invEqZeroThm{family.Add(registry.ProofEntry{
	Name:  "InvEqZero",
	Key:   "prop_d677bacdf35be3b9",
	Build: FieldAtUniverse.Law("∀x:A. F.inv(x) = F.zero ⇔ x = F.zero", InvEqZeroOn),
})}

// MulEqZeroOn — a field has no zero divisors: a product of members is
// zero exactly when one of its factors is. A zero factor absorbs the
// product, on whichever side it stands. Conversely, a left factor that
// is not zero has an inverse, lying in F.carrier beside the two factors, and
// multiplying the vanishing product by it strips that factor off,
// leaving the other factor equal to zero.
var MulEqZeroOn = mulEqZeroOnThm{family.Add(registry.ProofEntry{
	Name: "MulEqZeroOn",
	Key:  "prop_fe78c265d9a2a6eb",
	Build: FieldOn.Law(Statement{
		Binders: "∀x y:A.",
		Hypotheses: []string{
			"x ∈ F.carrier",
			"y ∈ F.carrier",
		},
		Conclusion: "x * y = F.zero ⇔ x = F.zero ∨ y = F.zero",
	},
		func(a *Argument, field FieldFact[on.F], x, y *Member[A, on.F]) {
			ring := Read(RingOn, field)
			monoid := Read(comm_ring.MulMonoidOn, ring)
			a.Iff()
			a.Forward(
				"a nonzero left factor has an inverse, which strips it off the vanishing product",
				func(b *Argument, vanishes Fact) {
					nonzero := b.Unless(
						b.Term("x = F.zero"),
						"if x is zero, the left disjunct holds outright",
						TrivialNormalized())
					inverse := b.Have(
						"x is a nonzero member, so it has an inverse",
						"F.inv(x) * x = F.one",
						By(x, y, nonzero, At(Read(MulLeftInverseOn, field), x)))
					yZero := b.Have(
						"so y is zero",
						"y = F.zero",
						CalcEq(
							Leg(
								b.TermAs[A]("F.one * y"),
								"one is the identity on the member y",
								By(Read(comm_monoid.LeftIdentityOn, monoid), x, y)),
							Leg(
								b.TermAs[A]("(F.inv(x) * x) * y"),
								"and one is inv(x) * x",
								inverse.RwRev(),
								Basic()),
							Leg(
								b.TermAs[A]("F.inv(x) * (x * y)"),
								"regroup, so the inverse faces the product",
								By(Read(comm_monoid.AssocOn, monoid), x, y, field, InvIn)),
							Leg(
								b.TermAs[A]("F.inv(x) * F.zero"),
								"the product vanishes",
								vanishes.Rw(),
								Basic()),
							FinalLeg(
								"and zero absorbs the member inv(x) on the right",
								By(Read(comm_ring.MulRightZeroOn, ring), x, y, field, InvIn)),
						))
					b.Show(
						"the right disjunct holds",
						By(yZero))
				})
			a.Backward(
				"a zero factor absorbs the product, on whichever side it stands",
				func(b *Argument, zeroFactor Fact) {
					b.Do(zeroFactor.SplitDisj(
						LeftHolds(
							"x is zero, and zero absorbs on the left",
							Given(func(d *Argument, xZero Fact) {
								d.Do(xZero.Rw())
								d.Show(
									"zero * y is zero",
									By(Read(comm_ring.MulLeftZeroOn, ring), x, y))
							})),
						RightHolds(
							"y is zero, and zero absorbs on the right",
							Given(func(d *Argument, yZero Fact) {
								d.Do(yZero.Rw())
								d.Show(
									"x * zero is zero",
									By(Read(comm_ring.MulRightZeroOn, ring), x, y))
							})),
					))
				})
		}),
})}

// MulEqZero — MulEqZeroOn on the whole type.
var MulEqZero = mulEqZeroThm{family.Add(registry.ProofEntry{
	Name:  "MulEqZero",
	Key:   "prop_112656b910f350ab",
	Build: FieldAtUniverse.Law("∀x y:A. x * y = F.zero ⇔ x = F.zero ∨ y = F.zero", MulEqZeroOn),
})}

// SquareRootsOfSquare — in a field the elements whose square is z·z are
// exactly z and −z: w·w − z·z factors as (w − z)(w + z), and a field has no
// zero divisors.
var SquareRootsOfSquare = squareRootsOfSquareThm{family.Add(registry.ProofEntry{
	Name: "SquareRootsOfSquare",
	Key:  "prop_b803ac3f0011520",
	Build: family.Theorem(Statement{
		Binders: "∀F:field_on(A). ∀z w:A.",
		Hypotheses: []string{
			"z ∈ F.carrier",
			"w ∈ F.carrier",
		},
		Conclusion: "w * w = z * z ⇔ w = z ∨ w = -z",
	}, func(a *Argument, F FieldFact[on.F], z, w *Member[A, on.F]) {
		ring := RingOn.Read(F)
		a.Iff()
		a.Forward(
			"a square root of z·z is z or −z",
			func(b *Argument, square Fact) {
				product := b.Have(
					"the difference of the squares factors",
					"(w - z) * (w + z) = F.zero",
					ByArith(F, z, w, square))
				factor := b.Have(
					"a field has no zero divisors, so one factor vanishes",
					"w - z = F.zero ∨ w + z = F.zero",
					By(
						product,
						MulEqZeroOn.Read(F).At(comm_ring.SubIn.Read(ring).At(w, z), comm_ring.AddIn.Read(ring).At(w, z))))
				b.Show(
					"w is z or −z by the factor that vanishes",
					factor.SplitDisj(
						LeftHolds(
							"w − z = 0 says w = z",
							Given(func(c *Argument, difference Fact) {
								c.Show(
									"so w = z",
									ByArith(F, z, w, difference))
							})),
						RightHolds(
							"w + z = 0 says w = −z",
							Given(func(c *Argument, sum Fact) {
								c.Show(
									"so w = −z",
									ByArith(F, z, w, sum))
							}))))
			})
		a.Backward(
			"z and −z both square to z·z",
			func(b *Argument, roots Fact) {
				b.Show(
					"(−z)·(−z) = z·z",
					By(Normalized, roots, comm_ring.MulNegNegOn.Read(ring).At(z, z)))
			})
	}),
})}

// FieldSquareRoots — in a field where 2 ≠ 0, zero has the single square
// root zero and every other element has none or exactly two: a square
// vanishes only at zero, and a root r of a nonzero d gives the roots r and −r
// of SquareRootsOfSquare, distinct since 2r ≠ 0.
var FieldSquareRoots = fieldSquareRootsThm{family.Add(registry.ProofEntry{
	Name: "FieldSquareRoots",
	Key:  "prop_c68dc94a9c8c2952",
	Reading: "The hypothesis 2≠0 separates z and −z for a nonzero square. In characteristic two " +
		"z = −z, and a nonzero element has at most one square root, exactly one in a finite field.",

	Build: family.Theorem(Statement{
		Binders:    "∀k:field_on(A). ∀d:A.",
		Hypotheses: []string{"k.one + k.one ≠ k.zero"},
		Conclusion: "(d = k.zero ⇒ has_size(«squareRoots», 1)) ∧ " +
			"(d ≠ k.zero ⇒ has_size(«squareRoots», 0) ∨ has_size(«squareRoots», 2))",
		Abbrev: Abbrev{
			{Name: "squareRoots", Text: "{z:A | z ∈ k.carrier ∧ z * z = d}"},
		},
	}, func(a *Argument, k Fact, d *Expr[A], two Fact) {
		ring := RingOn.Read(k)
		a.Show(
			"zero has one square root, a nonzero element none or two",
			SplitConj(
				Case(
					"at zero the only square root is zero",
					Derive(func(b *Argument) {
						dZero := b.Assume()
						roots := b.Have(
							"a square vanishes only at zero",
							"«squareRoots» = {k.zero}",
							BySets(dZero, MulEqZeroOn.Read(k), comm_ring.ZeroIn.Read(ring)))
						b.Show(
							"a singleton has one element",
							By(roots, cardinality.HasSizeDef, finite_set.FiniteSing, cardinality.CardSing))
					})),
				Case(
					"a nonzero d has no square root or exactly two",
					Derive(func(b *Argument) {
						dNonzero := b.Assume()
						exists := b.Assuming(
							b.TermAs[Bool]("∃r:A. r ∈ k.carrier ∧ r * r = d"),
							"with no square root the set of roots is empty",
							Given(func(c *Argument, none Fact) {
								c.Show(
									"the empty set has size zero",
									BySets(none, cardinality.HasSizeZero))
							}))
						r, root := b.UnpackAs[A](exists, "r")
						parts := b.Conjuncts(
							root,
							"r lies in k",
							"r squares to d")
						rm := b.MemberOf[on.Any](r, parts[0])
						oneM := b.MemberOf[on.Any](b.TermAs[A]("k.one"), comm_ring.OneIn.Read(ring))
						rNonzero := b.Have(
							"r is not zero, since its square d is not",
							"r ≠ k.zero",
							By(Normalized, dNonzero, parts[1], MulEqZeroOn.Read(k).At(rm, rm)))
						twice := b.Have(
							"neither 2 nor r is zero, so 2r is not",
							"(k.one + k.one) * r ≠ k.zero",
							By(two, rNonzero, MulEqZeroOn.Read(k).At(comm_ring.AddIn.Read(ring).At(oneM, oneM), rm)))
						distinct := b.Have(
							"so r and −r differ",
							"r ≠ -r",
							ByArith(k, rm, twice))
						roots := b.Have(
							"the square roots of d = r·r are r and −r",
							"«squareRoots» = {r, -r}",
							BySets(parts[1], rm, SquareRootsOfSquare.Read(k).AsFact().At(r), comm_ring.NegIn.Read(ring).At(rm)))
						b.Show(
							"two distinct points make a set of two",
							By(roots, distinct, cardinality.HasSizePair.At(r, b.TermAs[A]("-r"))))
					}))))
	}),
})}

// MulBijective — multiplying by a nonzero member c is a bijection of the
// carrier. Multiplying by inv(c) is its inverse there: it undoes
// multiplying by c, and multiplying by c undoes it, since inv(c) * c and
// c * inv(c) are one; and both keep the carrier, which is closed under
// products and holds inv(c).
var MulBijective = mulBijectiveThm{family.Add(registry.ProofEntry{
	Name: "MulBijective",
	Key:  "prop_fd8b5a44c4d37a6d",
	Build: FieldOn.Law(Statement{
		Binders: "∀c:A.",
		Hypotheses: []string{
			"c ∈ F.carrier",
			"c ≠ F.zero",
		},
		Conclusion: "injective_on(F.carrier, F.mul(c)) ∧ image(F.mul(c), F.carrier) = F.carrier",
	},
		func(a *Argument, field FieldFact[on.F], c *Member[A, on.F], nonzero Fact) {
			ring := RingOn.Read(field)
			undo := a.Have(
				"multiplying by inv(c) undoes multiplying by c",
				"∀x:A. x ∈ F.carrier ⇒ F.inv(c) * (c * x) = x",
				Derive(func(b *Argument) {
					x := b.FixAs[A]()
					xIn := b.Assume()
					b.Show(
						"inv(c) * c is one, c being nonzero",
						ByArith(
							field,
							xIn,
							c,
							nonzero,
							InvIn.Read(field).At(c),
							Scaled(x, MulLeftInverseOn.Read(field).AsFact().At(c))))
				}))
			redo := a.Have(
				"and multiplying by c undoes multiplying by inv(c)",
				"∀y:A. y ∈ F.carrier ⇒ c * (F.inv(c) * y) = y",
				Derive(func(b *Argument) {
					y := b.FixAs[A]()
					yIn := b.Assume()
					b.Show(
						"c * inv(c) is one, c being nonzero",
						ByArith(
							field,
							yIn,
							c,
							nonzero,
							InvIn.Read(field).At(c),
							Scaled(y, MulRightInverseOn.Read(field).AsFact().At(c))))
				}))
			into := a.Have(
				"multiplying by c keeps the carrier",
				"∀x:A. x ∈ F.carrier ⇒ c * x ∈ F.carrier",
				By(c, comm_ring.MulIn.Read(ring)))
			back := a.Have(
				"and so does multiplying by the member inv(c)",
				"∀y:A. y ∈ F.carrier ⇒ F.inv(c) * y ∈ F.carrier",
				By(c, comm_ring.MulIn.Read(ring), InvIn.Read(field)))
			carrier := a.TermAs[Set[A]]("F.carrier")
			a.Show(
				"a map with an inverse on the carrier is one-to-one there and maps it onto itself",
				By(
					undo,
					redo,
					into,
					back,
					functions.TwoSidedInverseBijection.At(
						carrier, carrier, a.TermAs[Fun[A, A]]("F.mul(c)"), a.TermAs[Fun[A, A]]("F.mul(F.inv(c))"))))
		}),
})}

// PowEqZeroOn — in a field a power of a nonzero element is nonzero: the
// same power of its inverse would invert zero.
var PowEqZeroOn = powEqZeroOnThm{family.Add(registry.ProofEntry{
	Name: "PowEqZeroOn",
	Key:  "prop_a384e160cb8e33bb",
	Build: family.Theorem(Statement{
		Binders: "∀F:field_on(A). ∀x:A. ∀n:num.",
		Hypotheses: []string{
			"x ∈ F.carrier",
			"monoid_pow(F.mul, F.one, x, n) = F.zero",
		},
		Conclusion: "x = F.zero",
	},
		func(a *Argument, F FieldFact[on.F], x *Member[A, on.F], n *Expr[Nat], vanishes Fact) {
			ring := RingOn.Read(F)
			multiplicative := comm_ring.MulMonoidOn.Read(ring)
			inverse := InvIn.Read(F).At(x)
			nonzero := a.SupposeNot()
			a.Show(
				"the n-th power of the inverse of x would invert zero",
				By(
					nonzero,
					vanishes,
					x,
					inverse,
					MulRightInverseOn.Read(F).AsFact().At(x),
					comm_monoid.PowInverseOn.Read(multiplicative).AsFact().At(x, inverse, n),
					comm_monoid.PowIn.Read(multiplicative).AsFact().At(inverse, n),
					comm_ring.MulLeftZeroOn.Read(ring).AsFact().At(
						a.TermAs[A]("monoid_pow(F.mul, F.one, F.inv(x), n)")),
					OneNotZeroOn.Read(F)))
		}),
})}

// PowEqZero — PowEqZeroOn on the whole type.
var PowEqZero = powEqZeroThm{family.Add(registry.ProofEntry{
	Name: "PowEqZero",
	Key:  "prop_b1be90f2b5b53ac5",
	Build: FieldAtUniverse.Law(Statement{
		Binders: "∀x:A. ∀n:num.",
		Hypotheses: []string{
			"monoid_pow(F.mul, F.one, x, n) = F.zero",
		},
		Conclusion: "x = F.zero",
	}, PowEqZeroOn),
})}
