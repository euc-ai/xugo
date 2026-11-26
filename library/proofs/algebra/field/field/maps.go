// maps.go — maps between fields: a map that respects products, one and
// zero carries inverses to inverses.

package field

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

// MapInv — a map f from one field to another that sends zero to zero,
// one to one and products to products sends each inverse to the inverse
// of the image. For a nonzero x, f(inv(x)) · f(x) = f(inv(x) · x) =
// f(one) = one', and in a field a factor that multiplies an element to
// one is that element's inverse; at zero both sides are zero, the
// inverse of zero being zero in each field. Only the multiplicative
// structure is asked for, so the law reads at a map that is not
// additive — the modulus of ℂ.
var MapInv = mapInvThm{family.Add(registry.ProofEntry{
	Name: "MapInv",
	Key:  "prop_ab8cfa52b3bd2d86",
	Build: family.Theorem(Statement{
		Binders: "∀F:field_on(A). ∀G:field_on(B). ∀f:(A → B). ∀x:A.",
		Hypotheses: []string{
			"∀u:A. u ∈ F.carrier ⇒ f(u) ∈ G.carrier",
			"f(F.zero) = G.zero",
			"f(F.one) = G.one",
			"∀u v:A. u ∈ F.carrier ∧ v ∈ F.carrier ⇒ f(F.mul(u, v)) = G.mul(f(u), f(v))",
			"x ∈ F.carrier",
		},
		Conclusion: "f(F.inv(x)) = G.inv(f(x))",
	},
		func(
			a *Argument,
			source FieldFact[on.F],
			target FieldFact[on.G],
			f *Arrow[A, B],
			x *Member[A, on.F],
			mapsInto, zeroMap, oneMap, multiplicative Fact,
		) {
			nonzero := a.Unless(
				a.Term("x = F.zero"),
				"at zero both sides are zero': each field inverts zero to zero, and f sends zero to zero'",
				Given(func(b *Argument, isZero Fact) {
					b.Show(
						"f(inv(zero)) is f(zero), and inv'(f(zero)) is inv'(zero')",
						isZero.Rw(),
						Simp(Fwd(InvZeroOn.Read(source))),
						zeroMap.Rw(),
						Simp(Fwd(InvZeroOn.Read(target))),
						Refl())
				}))
			unit := a.Have(
				"f(inv(x)) multiplies f(x) to one'",
				"G.mul(f(F.inv(x)), f(x)) = G.one",
				CalcEq(
					Leg(
						a.Term("f(F.mul(F.inv(x), x))"),
						"f respects products",
						By(multiplicative, x, InvIn.Read(source))),
					Leg(
						a.Term("f(F.one)"),
						"x has its left inverse",
						By(Normalized, nonzero, x, At(MulLeftInverseOn.Read(source), x))),
					FinalLeg(
						"and f sends one to one'",
						By(oneMap)),
				))
			a.Show(
				"a factor that multiplies f(x) to one' is inv'(f(x))",
				By(
					unit,
					mapsInto,
					x,
					InvIn.Read(source),
					At(InvLeftUniqueOn.Read(target), a.Term("f(F.inv(x))"), a.Term("f(x)"))))
		}),
})}
