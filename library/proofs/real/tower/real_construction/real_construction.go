// real_construction.go — the chapter: the laws of the constructed reals,
// the interface atop the real tower.
//
// Four parts, marked by banners:
//
// - The additive group
// - Multiplicative monoid + inverse
// - The ℕ-embedding as an ordered semiring homomorphism
// - The linear order and its compatibility with the ring operations
//
// Every law transported from the pre-real layer is proved the one way
// a law over a quotient is proved: each real binder inducts to a
// representative (RealDef.Induct — every real is the class of a
// pre-real), the lifted operations compute at the classes (RealAddDef
// and its siblings, the definitions themselves) and class equality
// reads as treal_eq (RealDef.Eq), and what is left IS the nonneg_real_formal_diff law,
// cited. A member spells only its own content: which operations its
// statement mentions, and which nonneg_real_formal_diff law it lands on.

package real_construction

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/real/tower/internal/nonneg_real_formal_diff"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The additive group
// ---------------------------------------------------------------------------
//
// README §"Additive group".

// AddSym — commutativity of real addition.
//
// This law IS nonneg_real_formal_diff.AddSym, transported across the quotient.
var AddSym = addSymThm{family.Add(registry.ProofEntry{
	Name: "AddSym",
	Key:  "prop_401b6b179f66b8f3",
	Build: family.Theorem("∀x y:real. x + y = y + x",
		func(a *Argument) {
			a.Induct("x")
			a.Induct("y")
			a.Show(
				"at representatives the sums are classes of pre-real sums, "+
					"and class equality is treal_eq — pre-real commutativity",
				Simp(Fwd(RealAddDef), Fwd(RealDef.Eq)),
				By(nonneg_real_formal_diff.AddSym))
		}),
})}

// AddAssoc — associativity of real addition.
//
// This law IS nonneg_real_formal_diff.AddAssoc, transported across the quotient.
var AddAssoc = addAssocThm{family.Add(registry.ProofEntry{
	Name: "AddAssoc",
	Key:  "prop_797aff25df375174",
	Build: family.Theorem("∀x y z:real. x + (y + z) = x + y + z",
		func(a *Argument) {
			a.Induct("x")
			a.Induct("y")
			a.Induct("z")
			a.Show(
				"at representatives the nested sums compute to classes, "+
					"and class equality is treal_eq — pre-real associativity",
				Simp(Fwd(RealAddDef), Fwd(RealDef.Eq)),
				By(nonneg_real_formal_diff.AddAssoc))
		}),
})}

// AddLeftId — 0 is a left identity for real addition.
//
// This law IS nonneg_real_formal_diff.AddLeftId, transported across the quotient; the
// numeral unfolds to the class of the embedded pre-real.
var AddLeftId = addLeftIdThm{family.Add(registry.ProofEntry{
	Name: "AddLeftId",
	Key:  "prop_df04f2deca55a6de",
	Build: family.Theorem("∀x:real. &0 + x = x",
		func(a *Argument) {
			a.Induct("x")
			a.Show(
				"the numeral is a class, the sum computes to a class, "+
					"and class equality is treal_eq — the pre-real identity",
				Simp(Fwd(RealOfNumDef), Fwd(RealAddDef), Fwd(RealDef.Eq)),
				By(nonneg_real_formal_diff.AddLeftId))
		}),
})}

// AddLeftInv — real_neg is a left additive inverse for real addition.
//
// This law IS nonneg_real_formal_diff.AddLeftInv, transported across the quotient:
// the negation and the sum compute at the class, the numeral is a
// class, and class equality is treal_eq.
var AddLeftInv = addLeftInvThm{family.Add(registry.ProofEntry{
	Name: "AddLeftInv",
	Key:  "prop_4fe33053fdc4b522",
	Build: family.Theorem("∀x:real. -x + x = &0",
		func(a *Argument) {
			a.Induct("x")
			a.Show(
				"the negation and the sum compute at the class, the numeral is a "+
					"class, and class equality is treal_eq — the pre-real inverse law",
				Simp(Fwd(RealOfNumDef), Fwd(RealNegDef), Fwd(RealAddDef), Fwd(RealDef.Eq)),
				By(nonneg_real_formal_diff.AddLeftInv))
		}),
})}

// ---------------------------------------------------------------------------
// Multiplicative monoid + inverse
// ---------------------------------------------------------------------------
//
// the multiplicative monoid and the inverse, each transported across the
// quotient to the nonneg_real_formal_diff law mirroring it.
//
// README §"Multiplicative monoid + inverse".

// MulSym — commutativity of real multiplication.
//
// This law IS nonneg_real_formal_diff.MulSym, transported across the quotient.
var MulSym = mulSymThm{family.Add(registry.ProofEntry{
	Name: "MulSym",
	Key:  "prop_265109053fc36238",
	Build: family.Theorem("∀x y:real. x * y = y * x",
		func(a *Argument) {
			a.Induct("x")
			a.Induct("y")
			a.Show(
				"at representatives the products are classes of pre-real "+
					"products, and class equality is treal_eq — pre-real commutativity",
				Simp(Fwd(RealMulDef), Fwd(RealDef.Eq)),
				By(nonneg_real_formal_diff.MulSym))
		}),
})}

// MulAssoc — associativity of real multiplication.
//
// This law IS nonneg_real_formal_diff.MulAssoc, transported across the quotient.
var MulAssoc = mulAssocThm{family.Add(registry.ProofEntry{
	Name: "MulAssoc",
	Key:  "prop_78ff54e48227718e",
	Build: family.Theorem("∀x y z:real. x * (y * z) = x * y * z",
		func(a *Argument) {
			a.Induct("x")
			a.Induct("y")
			a.Induct("z")
			a.Show(
				"at representatives the nested products compute to classes, "+
					"and class equality is treal_eq — pre-real associativity",
				Simp(Fwd(RealMulDef), Fwd(RealDef.Eq)),
				By(nonneg_real_formal_diff.MulAssoc))
		}),
})}

// MulLeftId — 1 is a left identity for real multiplication.
//
// This law IS nonneg_real_formal_diff.MulLeftId, transported across the quotient.
var MulLeftId = mulLeftIdThm{family.Add(registry.ProofEntry{
	Name: "MulLeftId",
	Key:  "prop_35d8347a99c4e8bd",
	Build: family.Theorem("∀x:real. &1 * x = x",
		func(a *Argument) {
			a.Induct("x")
			a.Show(
				"the numeral is a class, the product computes to a class, "+
					"and class equality is treal_eq — the pre-real identity",
				Simp(Fwd(RealOfNumDef), Fwd(RealMulDef), Fwd(RealDef.Eq)),
				By(nonneg_real_formal_diff.MulLeftId))
		}),
})}

// MulLeftInverse — every nonzero real has a left multiplicative
// inverse.
//
// This law IS nonneg_real_formal_diff.MulLeftInverse, transported across the quotient:
// at a representative both numerals are classes, the inverse and the
// product compute to classes, and both class equalities — the
// hypothesis's and the goal's — read as treal_eq.
var MulLeftInverse = mulLeftInverseThm{family.Add(registry.ProofEntry{
	Name: "MulLeftInverse",
	Key:  "prop_7472862d82f37c1b",
	Build: family.Theorem(Statement{
		Binders: "∀x:real.",
		Hypotheses: []string{
			"x ≠ &0",
		},
		Conclusion: "real_inv(x) * x = &1",
	},
		func(a *Argument) {
			a.Induct("x")
			a.Show(
				"at a representative everything computes to classes and "+
					"class equality reads as treal_eq — the pre-real inverse law",
				Simp(Fwd(RealOfNumDef), Fwd(RealInvDef), Fwd(RealMulDef), Fwd(RealDef.Eq)),
				By(nonneg_real_formal_diff.MulLeftInverse))
		}),
})}

// InvZero — the real inverse of zero is zero.
//
// This law IS nonneg_real_formal_diff.InvZero, transported across the quotient. It is
// the family's one GROUND law — nothing to induct: the numeral is a
// class, the inverse computes at it, and class equality is treal_eq.
var InvZero = invZeroThm{family.Add(registry.ProofEntry{
	Name: "InvZero",
	Key:  "prop_9a8d45351adaa648",
	Build: family.Theorem("real_inv(&0) = &0",
		func(a *Argument) {
			a.Show(
				"the numeral is a class, the inverse computes at it, "+
					"and class equality is treal_eq — the pre-real law",
				Simp(Fwd(RealOfNumDef), Fwd(RealInvDef), Fwd(RealDef.Eq)),
				By(nonneg_real_formal_diff.InvZero))
		}),
})}

// LeftDistrib — left distributivity of real multiplication over
// real addition.
//
// This law IS nonneg_real_formal_diff.LeftDistrib, transported across the quotient —
// both operations compute at the classes. Structural mirror of
// nonneg_real.LeftDistrib one layer down (hreal_* → real_*, slope.* →
// nonneg_real_formal_diff.*).
var LeftDistrib = leftDistribThm{family.Add(registry.ProofEntry{
	Name: "LeftDistrib",
	Key:  "prop_b686c762d7336bc",
	Build: family.Theorem("∀x y z:real. x * (y + z) = x * y + x * z",
		func(a *Argument) {
			a.Induct("x")
			a.Induct("y")
			a.Induct("z")
			a.Show(
				"at representatives sums and products compute to classes, "+
					"and class equality is treal_eq — pre-real distributivity",
				Simp(Fwd(RealAddDef), Fwd(RealMulDef), Fwd(RealDef.Eq)),
				By(nonneg_real_formal_diff.LeftDistrib))
		}),
})}

// ---------------------------------------------------------------------------
// The ℕ-embedding as an ordered semiring homomorphism
// ---------------------------------------------------------------------------
//
// OfNumEq is the one member here that never descends to the quotient;
// the other three unfold the numerals to classes and compute at them.
//
// README §"ℕ-embedding as an ordered semiring".

// OfNumLessEq — the numeral embedding preserves and reflects order.
//
// Both binders are ℕ, so nothing inducts: the numerals are classes of
// embedded pre-reals, the order at classes is the pre-real order, and
// what remains is nonneg_real_formal_diff.OfNumLessEq, the treal-level order
// embedding, verbatim.
var OfNumLessEq = ofNumLessEqThm{family.Add(registry.ProofEntry{
	Name: "OfNumLessEq",
	Key:  "prop_d536c9e1018bb379",
	Build: family.Theorem("∀m n:num. &m ≤ &n ⇔ m ≤ n",
		func(a *Argument, m, n Term) {
			a.Show(
				"both numerals are classes, and the order at classes "+
					"is the pre-real order — the pre-real order embedding",
				Simp(Fwd(RealOfNumDef), Fwd(RealLeDef)),
				By(nonneg_real_formal_diff.OfNumLessEq))
		}),
})}

// OfNumEq — the numeral embedding is injective, because an order
// embedding into any order is injective whenever the source order is
// antisymmetric. OfNumLessEq is the embedding half; ℕ's half is
// nat_order.LessEqAntisym. The converse arm is congruence and asks
// for nothing.
var OfNumEq = ofNumEqThm{family.Add(registry.ProofEntry{
	Name: "OfNumEq",
	Key:  "prop_ba192bb7260c04f",
	// One premise set covers both arms of the biconditional, so there is
	// nothing to split. Normalized clause-forms it before the close.
	Build: family.Theorem("∀m n:num. &m = &n ⇔ m = n",
		func(a *Argument, m, n Term) {
			a.Do(By(Normalized, OfNumLessEq, nat_order.LessEqAntisym))
		}),
})}

// OfNumAdd — the numeral embedding is additive.
//
// Both binders are numbers, so nothing inducts: the three numerals are
// classes, the sum computes to a class, class equality is treal_eq,
// and nonneg_real_formal_diff.OfNumAdd is that residual with its sides flipped — the
// statement puts the sum on the right where the pre-real law puts it
// on the left, and treal_eq is symmetric by TrealEqSym.
var OfNumAdd = ofNumAddThm{family.Add(registry.ProofEntry{
	Name: "OfNumAdd",
	Key:  "prop_85860fe132d99ba4",
	Build: family.Theorem("∀m n:num. &(m + n) = &m + &n",
		func(a *Argument, m, n Term) {
			a.Show(
				"the numerals are classes, the sum computes to a class, and "+
					"class equality is treal_eq — pre-real additivity, read backwards",
				Simp(Fwd(RealOfNumDef), Fwd(RealAddDef), Fwd(RealDef.Eq)),
				By(nonneg_real_formal_diff.OfNumAdd, nonneg_real_formal_diff.TrealEqSym))
		}),
})}

// OfNumMul — the numeral embedding is multiplicative.
//
// The mirror of OfNumAdd one operation over (and of nonneg_real.OfNumMul
// one layer up), with the same flipped sides.
var OfNumMul = ofNumMulThm{family.Add(registry.ProofEntry{
	Name: "OfNumMul",
	Key:  "prop_ba32843c85e4b8bd",
	Build: family.Theorem("∀m n:num. &(m * n) = &m * &n",
		func(a *Argument, m, n Term) {
			a.Show(
				"the numerals are classes, the product computes to a class, and class "+
					"equality is treal_eq — pre-real multiplicativity, read backwards",
				Simp(Fwd(RealOfNumDef), Fwd(RealMulDef), Fwd(RealDef.Eq)),
				By(nonneg_real_formal_diff.OfNumMul, nonneg_real_formal_diff.TrealEqSym))
		}),
})}

// ---------------------------------------------------------------------------
// The linear order and its compatibility with the ring operations
// ---------------------------------------------------------------------------
//
// the linear order and its compatibility with the ring operations, each
// transported across the quotient to the nonneg_real_formal_diff law mirroring it.
//
// README §"Linear order + order/ring compatibility".

// LessEqAntisym — antisymmetry of the real order.
//
// This law IS nonneg_real_formal_diff.LessEqAntisym, transported across the quotient:
// class equality reads as treal_eq, the order atoms as the pre-real
// order.
var LessEqAntisym = lessEqAntisymThm{family.Add(registry.ProofEntry{
	Name: "LessEqAntisym",
	Key:  "prop_fe5a89ebe23482b2",
	Build: family.Theorem("∀x y:real. x = y ⇔ x ≤ y ∧ y ≤ x",
		func(a *Argument) {
			a.Induct("x")
			a.Induct("y")
			a.Show(
				"class equality is treal_eq and the order at classes is the pre-real order — pre-real antisymmetry",
				Simp(Fwd(RealLeDef), Fwd(RealDef.Eq)),
				By(nonneg_real_formal_diff.LessEqAntisym))
		}),
})}

// LessEqTrans — transitivity of the real order.
//
// This law IS nonneg_real_formal_diff.LessEqTrans, transported across the quotient: the
// statement carries only order atoms, each the pre-real order at
// representatives.
var LessEqTrans = lessEqTransThm{family.Add(registry.ProofEntry{
	Name: "LessEqTrans",
	Key:  "prop_64e888eefe83e60a",
	Build: family.Theorem(Statement{
		Binders: "∀x y z:real.",
		Hypotheses: []string{
			"x ≤ y",
			"y ≤ z",
		},
		Conclusion: "x ≤ z",
	},
		func(a *Argument) {
			a.Induct("x")
			a.Induct("y")
			a.Induct("z")
			a.Show(
				"the three order atoms are the pre-real order at representatives — pre-real transitivity",
				Simp(Fwd(RealLeDef)),
				By(nonneg_real_formal_diff.LessEqTrans))
		}),
})}

// LessEqTotal — totality of the real order.
//
// This law IS nonneg_real_formal_diff.LessEqTotal, transported across the quotient.
var LessEqTotal = lessEqTotalThm{family.Add(registry.ProofEntry{
	Name: "LessEqTotal",
	Key:  "prop_8364940bd9f05fb",
	Build: family.Theorem("∀x y:real. x ≤ y ∨ y ≤ x",
		func(a *Argument) {
			a.Induct("x")
			a.Induct("y")
			a.Show(
				"both disjuncts are the pre-real order at representatives — pre-real totality",
				Simp(Fwd(RealLeDef)),
				By(nonneg_real_formal_diff.LessEqTotal))
		}),
})}

// LessEqAddLeftImp — adding the same real on the left of both sides
// preserves the real order.
//
// This law IS nonneg_real_formal_diff.LessEqAddLeftImp, transported across the
// quotient: the sums compute at the classes and the order atoms are
// the pre-real order.
var LessEqAddLeftImp = lessEqAddLeftImpThm{family.Add(registry.ProofEntry{
	Name: "LessEqAddLeftImp",
	Key:  "prop_5e873e035e1f0513",
	Build: family.Theorem(Statement{
		Binders: "∀x y z:real.",
		Hypotheses: []string{
			"y ≤ z",
		},
		Conclusion: "x + y ≤ x + z",
	},
		func(a *Argument) {
			a.Induct("x")
			a.Induct("y")
			a.Induct("z")
			a.Show(
				"both sums compute to classes and the order at classes "+
					"is the pre-real order — pre-real left-add monotonicity",
				Simp(Fwd(RealAddDef), Fwd(RealLeDef)),
				By(nonneg_real_formal_diff.LessEqAddLeftImp))
		}),
})}

// LessEqMul — the product of two non-negative reals is non-negative.
//
// This law IS nonneg_real_formal_diff.LessEqMul, transported across the quotient: the
// numeral is a class, the product computes at the classes, and every
// order atom is the pre-real order.
var LessEqMul = lessEqMulThm{family.Add(registry.ProofEntry{
	Name: "LessEqMul",
	Key:  "prop_a7761788541c9b2d",
	Build: family.Theorem(Statement{
		Binders: "∀x y:real.",
		Hypotheses: []string{
			"&0 ≤ x",
			"&0 ≤ y",
		},
		Conclusion: "&0 ≤ x * y",
	},
		func(a *Argument) {
			a.Induct("x")
			a.Induct("y")
			a.Show(
				"the numeral is a class, the product computes to a class, and "+
					"the order at classes is the pre-real order — the pre-real law",
				Simp(Fwd(RealOfNumDef), Fwd(RealMulDef), Fwd(RealLeDef)),
				By(nonneg_real_formal_diff.LessEqMul))
		}),
})}
