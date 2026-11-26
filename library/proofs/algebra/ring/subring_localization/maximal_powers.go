// maximal_powers.go — a member of a subring S off a maximal ideal p is a unit
// modulo every power of p, so a member of the field that a power of p and a
// member of S off p both multiply into S lies in S.

package subring_localization

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/fractional_ideal"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_ideal"
	"github.com/euc-ai/xugo/library/registry"
)

// UnitModuloMaximalPowers — a member b of a subring S off a maximal ideal p is
// a unit modulo each power pⁿ: b·c + y = one for some c in S and y in pⁿ.
// Maximality makes p and b generate S, so one = u·b + t with u in S and t
// in p. Induction on n then carries b·c + y = one to b·(u + c·t) + t·y =
// b·u + t·(b·c + y) = b·u + t = one, and t·y lies in p · pⁿ = pⁿ⁺¹.
var UnitModuloMaximalPowers = unitModuloMaximalPowersThm{family.Add(registry.ProofEntry{
	Name: "UnitModuloMaximalPowers",
	Reading: "Maximality of p, not primality, makes p and b generate S: in " +
		"k[x, y] with p = (x) and b = y, b·c + y′ = one with y′ ∈ (x) fails " +
		"modulo (x, y). n = 0 holds for every b, with c = zero and y = one.",
	Key: "prop_c9502a2e586d0460",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S p:set(A). ∀b:A. ∀n:num.",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"maximal_ideal(«wfScalars», p)",
			"b ∈ S",
			"b ∉ p",
		},
		Conclusion: "∃c y:A. " +
			"    c ∈ S ∧ " +
			"    y ∈ monoid_pow(λX:set(A). λY:set(A). fractional_mul(field_ring(L), S, X, Y), S, p, n) ∧ " +
			"    b * c + y = L.one",
	},
		func(a *Argument, L field.FieldFact[on.L], S, p *Expr[Set[A]], b *Expr[A], h Fact) {
			parts := a.Conjuncts(
				h,
				"S is a subring of the field",
				"p is a maximal ideal of S",
				"b lies in S",
				"and outside p")
			subring, maximal, bInS, outside := parts[0], parts[1], parts[2], parts[3]
			scalars := a.TermAs[RingOps[A]]("«wfScalars»")
			vectors := a.TermAs[module_record.ModuleOps[A, A]]("«wfField»")
			ringS := a.Have(
				"S is a commutative ring under the field's operations",
				"comm_ring_on(«wfScalars»)",
				By(subring, comm_ring.SubringRingOn.Read(field.RingOn.Read(L)).At(S)))
			ideal := a.Have(
				"p is an ideal of S",
				"«wfIdeal»(p)",
				By(maximal, ring_ideal.MaximalIdealIdeal.At(scalars, p)))
			_, t, generated := a.Obtain2As[A, A](
				"p and b generate S, so one is a multiple of b plus a member of p",
				"∃u t:A. u ∈ S ∧ t ∈ p ∧ L.one = u * b + t",
				BySets(
					maximal,
					outside,
					ideal,
					bInS,
					comm_ring.OneIn.Read(ringS),
					ring_ideal.MaximalComplement.Read(ringS).AsFact().At(p, b),
					ring_ideal.SpanInsertIdeal.Read(ringS).AsFact().At(p, b)))
			split := a.Conjuncts(
				generated,
				"u lies in S",
				"t lies in p",
				"one is u times b plus t")
			fractional := a.Have(
				"an ideal of S is a fractional ideal inside S",
				"«wfFractional»(p) ∧ p ⊆ S",
				By(subring, ideal, fractional_ideal.IntegralIdealFractional.Read(L).At(S, p)))
			monoid := a.Have(
				"the fractional ideals form a commutative monoid under the product, with unit S",
				"comm_monoid_on({M:set(A) | «wfFractional»(M)}, "+
					"    λX:set(A). λY:set(A). fractional_mul(field_ring(L), S, X, Y), "+
					"    S)",
				By(subring, fractional_ideal.FractionalIdealsCommMonoid.Read(L).At(S)))
			a.Induct("n")
			a.Base(
				"p⁰ is S, which holds one: c = zero and y = one",
				func(a *Argument) {
					a.Take(a.TermAs[A]("L.zero"))
					a.Take(a.TermAs[A]("L.one"))
					a.Show(
						"zero lies in S, one lies in S = p⁰, and b·zero + one is one",
						ByArith(
							ringS,
							bInS,
							comm_ring.ZeroIn.Read(ringS),
							comm_ring.OneIn.Read(ringS),
							comm_monoid.MonoidPowDef))
				})
			a.Step(
				"multiplying b·c + y = one by t and adding b·u gives "+
					"b·(u + c·t) + t·y = b·u + t = one, with t·y in pⁿ⁺¹",
				func(a *Argument, ih Fact) {
					_, y, previous := a.Unpack2As[A, A](ih, "c", "y")
					known := a.Conjuncts(
						previous,
						"c lies in S",
						"y lies in pⁿ",
						"b·c + y is one")
					n := a.TermAs[Nat]("n")
					power := a.TermAs[Set[A]](
						"monoid_pow(λX:set(A). λY:set(A). fractional_mul(field_ring(L), S, X, Y), S, p, n)")
					powerInField := a.Have(
						"pⁿ is a fractional ideal, so it lies in the field",
						"monoid_pow(λX:set(A). λY:set(A). fractional_mul(field_ring(L), S, X, Y), S, p, n) ⊆ L.carrier",
						By(
							fractional,
							comm_monoid.PowIn.Read(monoid).AsFact().At(p, n),
							submodule.SubmoduleSubset.At(scalars, vectors, power)))
					inField := a.Have(
						"b, c, u and t lie in S and y in pⁿ, all inside the field",
						"b ∈ L.carrier ∧ c ∈ L.carrier ∧ u ∈ L.carrier ∧ t ∈ L.carrier ∧ y ∈ L.carrier",
						BySets(
							comm_ring.SubringSubset.Read(subring),
							bInS,
							known[0],
							split[0],
							split[1],
							known[1],
							fractional,
							powerInField))
					coefficient := a.Have(
						"u + c·t lies in S, closed under sums and products, as t lies in p inside S",
						"u + c * t ∈ S",
						BySets(
							comm_ring.AddIn.Read(ringS),
							comm_ring.MulIn.Read(ringS),
							known[0],
							split[0],
							split[1],
							fractional))
					remainder := a.Have(
						"t·y lies in the product p · pⁿ, which is pⁿ⁺¹",
						"t * y ∈ monoid_pow(λX:set(A). λY:set(A). fractional_mul(field_ring(L), S, X, Y), S, p, suc(n))",
						By(
							known[1],
							split[1],
							fractional_ideal.FractionalMulHolds.Read(L).At(S, p, power, t, y),
							comm_monoid.MonoidPowDef))
					equation := a.Have(
						"b·(u + c·t) + t·y is t·(b·c + y) + b·u, that is t + b·u, which is one",
						"b * (u + c * t) + t * y = L.one",
						ByArith(L, inField, Scaled(t, known[2]), split[2]))
					a.Take(a.TermAs[A]("u + c * t"))
					a.Take(a.TermAs[A]("t * y"))
					a.Show(
						"u + c·t and t·y witness the power n + 1",
						By(coefficient, remainder, equation))
				})
		}),
})}

// ClearedOffMaximalIntegral — a member g of the field lies in a subring S
// when the j-th power of a maximal ideal p of S multiplies it into S and so
// does some b of S off p: b is a unit modulo pʲ (UnitModuloMaximalPowers),
// b·c + y = one with c in S and y in pʲ, and g = (g·b)·c + g·y lies in S.
var ClearedOffMaximalIntegral = clearedOffMaximalIntegralThm{family.Add(registry.ProofEntry{
	Name: "ClearedOffMaximalIntegral",
	Key:  "prop_5969b6d9d6e09bf4",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S p:set(A). ∀g b:A. ∀j:num.",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"maximal_ideal(«wfScalars», p)",
			"g ∈ " +
				"«wfInverse»(monoid_pow(λX:set(A). λY:set(A). fractional_mul(field_ring(L), S, X, Y), S, p, j))",
			"b ∈ S",
			"b ∉ p",
			"g * b ∈ S",
		},
		Conclusion: "g ∈ S",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			S, p *Expr[Set[A]],
			g, b *Expr[A],
			j *Expr[Nat],
			h Fact,
		) {
			parts := a.Conjuncts(
				h,
				"S is a subring of the field",
				"p is a maximal ideal of S",
				"pʲ multiplies g into S",
				"b lies in S",
				"and outside p",
				"and multiplies g into S")
			subring, maximal, inverse, bInS, outside, cleared :=
				parts[0], parts[1], parts[2], parts[3], parts[4], parts[5]
			fieldRing := a.TermAs[RingOps[A]]("field_ring(L)")
			scalars := a.TermAs[RingOps[A]]("«wfScalars»")
			vectors := a.TermAs[module_record.ModuleOps[A, A]]("«wfField»")
			power := a.TermAs[Set[A]](
				"monoid_pow(λX:set(A). λY:set(A). fractional_mul(field_ring(L), S, X, Y), S, p, j)")
			c, _, unit := a.Obtain2As[A, A](
				"b is a unit modulo pʲ",
				"∃c y:A. "+
					"    c ∈ S ∧ "+
					"    y ∈ monoid_pow(λX:set(A). λY:set(A). fractional_mul(field_ring(L), S, X, Y), S, p, j) ∧ "+
					"    b * c + y = L.one",
				By(subring, maximal, bInS, outside, UnitModuloMaximalPowers.Read(L).At(S, p, b, j)))
			unitParts := a.Conjuncts(
				unit,
				"c lies in S",
				"y lies in pʲ",
				"b·c + y is one")
			multiple := a.Have(
				"g lies in the field, and g·y in S",
				"g ∈ L.carrier ∧ g * y ∈ S",
				BySets(inverse, unitParts[1], fractional_ideal.FractionalInverseDef.At(fieldRing, S, power)))
			fractional := a.Have(
				"p is a fractional ideal inside S",
				"«wfFractional»(p) ∧ p ⊆ S",
				By(
					subring,
					maximal,
					ring_ideal.MaximalIdealIdeal.At(scalars, p),
					fractional_ideal.IntegralIdealFractional.Read(L).At(S, p)))
			monoid := a.Have(
				"the fractional ideals form a commutative monoid under the product, with unit S",
				"comm_monoid_on({M:set(A) | «wfFractional»(M)}, "+
					"    λX:set(A). λY:set(A). fractional_mul(field_ring(L), S, X, Y), "+
					"    S)",
				By(subring, fractional_ideal.FractionalIdealsCommMonoid.Read(L).At(S)))
			powerInField := a.Have(
				"pʲ is a fractional ideal, so it lies in the field",
				"monoid_pow(λX:set(A). λY:set(A). fractional_mul(field_ring(L), S, X, Y), S, p, j) ⊆ L.carrier",
				By(
					fractional,
					comm_monoid.PowIn.Read(monoid).AsFact().At(p, j),
					submodule.SubmoduleSubset.At(scalars, vectors, power)))
			members := a.Have(
				"g, b, c and y lie in the field",
				"g ∈ L.carrier ∧ b ∈ L.carrier ∧ c ∈ L.carrier ∧ y ∈ L.carrier",
				BySets(
					multiple,
					bInS,
					unitParts[0],
					unitParts[1],
					powerInField,
					subring,
					comm_ring.SubringSubset.At(fieldRing, S)))
			decomposition := a.Have(
				"g is g·(b·c + y), that is (g·b)·c + g·y",
				"g = g * b * c + g * y",
				ByArith(L, members, Scaled(g, unitParts[2])))
			a.Show(
				"(g·b)·c and g·y lie in S, closed under products and sums",
				By(
					Normalized,
					decomposition,
					cleared,
					unitParts[0],
					multiple,
					subring,
					comm_ring.SubringAdd.At(fieldRing, S, a.TermAs[A]("g * b * c"), a.TermAs[A]("g * y")),
					comm_ring.SubringMul.At(fieldRing, S, a.TermAs[A]("g * b"), c)))
		}),
})}
