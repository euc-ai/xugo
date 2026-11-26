// nonneg_real.go — the chapter: nonnegative reals, the real tower's second layer.
//
// Four parts, marked by banners:
//
// - Hreal addition
// - Hreal multiplication
// - The numeral embedding ℕ ↪ hreal and its morphism laws
// - The hreal order
//
// Every law transported from the slope layer is proved the one way a
// law over a quotient is proved: each hreal binder inducts to a
// representative (HrealDef.Induct — every hreal is the class of a
// slope), the lifted operations compute at the classes
// (HrealAddDef and its siblings, the definitions themselves) and
// class equality reads as nadd_eq (HrealDef.Eq), and what is left IS
// the slope law, cited. A member spells only its own content: which
// operations its statement mentions, and which slope law it lands on.

package nonneg_real

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/real/tower/internal/eudoxus_slope"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// Hreal addition
// ---------------------------------------------------------------------------
//
// hreal addition: the monoid laws and cancellation, most of them pushed
// down to representatives and discharged by the slope theorem mirroring
// them. Three members never leave the quotient and are proved from their
// siblings instead: AddRightId (AddSym onto AddLeftId) and the two Eq*
// members, which are cancellation read as a biconditional.
//
// README: "the additive and multiplicative laws (commutative semiring
// with cancellation)".

// AddSym — commutativity of hreal addition:
//
//	⊢ ∀x y : hreal. (x + y) = (y + x)
//
// This law IS eudoxus_slope.AddSym, transported across the quotient.
var AddSym = addSymThm{family.Add(registry.ProofEntry{
	Name: "AddSym",
	Key:  "prop_23ff10d6283c9935",
	Build: family.Theorem("∀x y:hreal. x + y = y + x",
		func(a *Argument) {
			a.Induct("x")
			a.Induct("y")
			a.Show(
				"at representatives the sums are classes of slope sums, "+
					"and class equality is nadd_eq — slope commutativity",
				Simp(Fwd(HrealAddDef), Fwd(HrealDef.Eq)),
				By(eudoxus_slope.AddSym))
		}),
})}

// AddAssoc — associativity of hreal addition:
//
//	⊢ ∀x y z : hreal. (x + (y + z)) = ((x + y) + z)
//
// This law IS eudoxus_slope.AddAssoc, transported across the quotient.
var AddAssoc = addAssocThm{family.Add(registry.ProofEntry{
	Name: "AddAssoc",
	Key:  "prop_8523fcee6c90ed0",
	Build: family.Theorem("∀x y z:hreal. x + (y + z) = x + y + z",
		func(a *Argument) {
			a.Induct("x")
			a.Induct("y")
			a.Induct("z")
			a.Show(
				"at representatives the nested sums compute to classes, "+
					"and class equality is nadd_eq — slope associativity",
				Simp(Fwd(HrealAddDef), Fwd(HrealDef.Eq)),
				By(eudoxus_slope.AddAssoc))
		}),
})}

// AddLeftId — 0 is a left identity for hreal_add:
//
//	⊢ ∀x : hreal. (hreal_of_num(0) + x) = x
//
// This law IS eudoxus_slope.AddLeftId, transported across the quotient; the
// numeral unfolds to the class of the embedded slope.
var AddLeftId = addLeftIdThm{family.Add(registry.ProofEntry{
	Name: "AddLeftId",
	Key:  "prop_5971ff26313d0472",
	Build: family.Theorem("∀x:hreal. hreal_of_num(0) + x = x",
		func(a *Argument) {
			a.Induct("x")
			a.Show(
				"the numeral is a class, the sum computes to a class, "+
					"and class equality is nadd_eq — the slope identity",
				Simp(Fwd(HrealOfNumDef), Fwd(HrealAddDef), Fwd(HrealDef.Eq)),
				By(eudoxus_slope.AddLeftId))
		}),
})}

// AddRightId — 0 is a right identity for hreal_add:
//
//	⊢ ∀n : hreal. (n + hreal_of_num(0)) = n
//
// The mirror of AddLeftId. Commutativity (AddSym) rewrites
// hreal_add(n, 0) onto hreal_add(0, n), reducing the goal to the
// left-form which AddLeftId supplies verbatim; the refute closes.
var AddRightId = addRightIdThm{family.Add(registry.ProofEntry{
	Name: "AddRightId",
	Key:  "prop_fd98d2fc2b389090",
	Build: family.Theorem("∀n:hreal. n + hreal_of_num(0) = n",
		func(a *Argument, n Term) {
			// Commutativity flips (n₀ + 0) → (0 + n₀); AddLeftId then
			// supplies hreal_add(0, n₀) = n₀.
			a.Do(By(Normalized, AddSym, AddLeftId))
		}),
})}

// addLeftCancel — hreal addition cancels on the left:
//
//	⊢ ∀x y z : hreal. (x + y) = (x + z) ⇒ y = z
//
// This law IS eudoxus_slope.AddLeftCancel, transported across the quotient:
// at representatives both sums are classes of slope sums and both
// class equalities read as nadd_eq, so the residual is
//
//	nadd_eq(x + y, x + z) ⇒ nadd_eq(y, z)
//
// which is the cited slope fact.
var addLeftCancel = addLeftCancelThm{family.Add(registry.ProofEntry{
	Name: "addLeftCancel",
	Key:  "prop_6c059bdf449c82b",
	Build: family.Theorem(Statement{
		Binders: "∀x y z:hreal.",
		Hypotheses: []string{
			"x + y = x + z",
		},
		Conclusion: "y = z",
	},
		func(a *Argument) {
			a.Induct("x")
			a.Induct("y")
			a.Induct("z")
			a.Show(
				"at representatives both sums compute to classes and both "+
					"class equalities read as nadd_eq — slope left-cancellation",
				Simp(Fwd(HrealAddDef), Fwd(HrealDef.Eq)),
				By(eudoxus_slope.AddLeftCancel))
		}),
})}

// EqAddLeftCancel — hreal addition on the left is injective as an
// equivalence:
//
//	⊢ ∀m n p : hreal. (p + m) = (p + n) ⇔ m = n
//
// One direction (⇒) is left-cancellation; the other (⇐) is congruence
// under hreal_add. The sibling addLeftCancel is the whole premise: from
// it alone the refuter closes both directions in one step.
var EqAddLeftCancel = eqAddLeftCancelThm{family.Add(registry.ProofEntry{
	Name: "EqAddLeftCancel",
	Key:  "prop_ca5e59d7c359a619",
	Build: family.Theorem("∀m n p:hreal. p + m = p + n ⇔ m = n",
		func(a *Argument, m, n, p Term) {
			// The ⇒ direction is left-cancellation at (p₀, m₀, n₀); the
			// ⇐ direction is congruence under hreal_add.
			a.Show(
				"both directions rest on left-cancellation alone",
				By(Normalized, addLeftCancel))
		}),
})}

// EqAddRightCancel — hreal addition on the right is injective as an
// equivalence:
//
//	⊢ ∀m n p : hreal. (m + p) = (n + p) ⇔ m = n
//
// Commutativity of hreal addition (AddSym) rewrites both sides of the
// right-hand equality onto their left-added twins, reducing the goal
// to left-cancellation (EqAddLeftCancel).
var EqAddRightCancel = eqAddRightCancelThm{family.Add(registry.ProofEntry{
	Name: "EqAddRightCancel",
	Key:  "prop_6c049e38f6ad6098",
	Build: family.Theorem("∀m n p:hreal. m + p = n + p ⇔ m = n",
		func(a *Argument, m, n, p Term) {
			// Commutativity rewrites (m₀ + p₀) → (p₀ + m₀)
			// and the mirror for n₀, reducing the goal to the left-form.
			a.Do(By(AddSym, EqAddLeftCancel))
		}),
})}

// ---------------------------------------------------------------------------
// Hreal multiplication
// ---------------------------------------------------------------------------
//
// hreal multiplication: the monoid laws, distributivity over addition, and
// the multiplicative inverse, each pushed down to representatives and
// discharged by its slope mirror.
//
// MulLeftZero is the exception — no slope fact is needed, because the
// quotient's own additive cancellation already proves it.
//
// README: "the additive and multiplicative laws" and "the
// multiplicative inverse".

// MulSym — commutativity of hreal multiplication:
//
//	⊢ ∀x y : hreal. (x * y) = (y * x)
//
// This law IS eudoxus_slope.MulSym, transported across the quotient.
var MulSym = mulSymThm{family.Add(registry.ProofEntry{
	Name: "MulSym",
	Key:  "prop_ebafdeeadff72e31",
	Build: family.Theorem("∀x y:hreal. x * y = y * x",
		func(a *Argument) {
			a.Induct("x")
			a.Induct("y")
			a.Show(
				"at representatives the products are classes of slope "+
					"products, and class equality is nadd_eq — slope commutativity",
				Simp(Fwd(HrealMulDef), Fwd(HrealDef.Eq)),
				By(eudoxus_slope.MulSym))
		}),
})}

// MulAssoc — associativity of hreal multiplication:
//
//	⊢ ∀x y z : hreal. (x * (y * z)) = ((x * y) * z)
//
// This law IS eudoxus_slope.MulAssoc, transported across the quotient.
var MulAssoc = mulAssocThm{family.Add(registry.ProofEntry{
	Name: "MulAssoc",
	Key:  "prop_6a0ac1d9b5975f83",
	Build: family.Theorem("∀x y z:hreal. x * (y * z) = x * y * z",
		func(a *Argument) {
			a.Induct("x")
			a.Induct("y")
			a.Induct("z")
			a.Show(
				"at representatives the nested products compute to classes, "+
					"and class equality is nadd_eq — slope associativity",
				Simp(Fwd(HrealMulDef), Fwd(HrealDef.Eq)),
				By(eudoxus_slope.MulAssoc))
		}),
})}

// MulLeftId — 1 is a left identity for hreal_mul:
//
//	⊢ ∀x : hreal. (hreal_of_num(1) * x) = x
//
// This law IS eudoxus_slope.MulLeftId, transported across the quotient — the
// exact mirror of AddLeftId one operation over.
var MulLeftId = mulLeftIdThm{family.Add(registry.ProofEntry{
	Name: "MulLeftId",
	Key:  "prop_e6ca157404b54a9a",
	Build: family.Theorem("∀x:hreal. hreal_of_num(1) * x = x",
		func(a *Argument) {
			a.Induct("x")
			a.Show(
				"the numeral is a class, the product computes to a "+
					"class, and class equality is nadd_eq — the slope identity",
				Simp(Fwd(HrealOfNumDef), Fwd(HrealMulDef), Fwd(HrealDef.Eq)),
				By(eudoxus_slope.MulLeftId))
		}),
})}

// MulLeftZero — 0 annihilates hreal multiplication from the left:
//
//	⊢ ∀m : hreal. 0 · m = 0
//
// Additive-cancellation trick. hreal has no subtraction, so 0·m = 0 is
// reached by adding a well-chosen term to both sides and cancelling it
// again. The choice IS the proof: with p := 1·m₀, EqAddRightCancel
// turns the goal into
//
//	0·m₀ + 1·m₀ = 0 + 1·m₀
//
// and both sides are 1·m₀. The right is AddLeftId at 1·m₀. The left is
// the distributive collapse: MulSym flips the two products to m₀·0 and
// m₀·1, LeftDistrib folds them into m₀·(0+1), AddLeftId turns the
// numeric sum into 1, and MulSym flips m₀·1 back to 1·m₀.
//
// Every instantiation above is spelled ground below. p := 1·m₀ in
// particular is a choice no unground install can record — it is the
// one step of this proof that is not forced.
var MulLeftZero = mulLeftZeroThm{family.Add(registry.ProofEntry{
	Name: "MulLeftZero",
	Key:  "prop_10c9babd23f5a014",
	Build: family.Theorem("∀m:hreal. hreal_of_num(0) * m = hreal_of_num(0)",
		func(a *Argument, m Term) {
			ctx := a.Ctx()
			v := ops(ctx)

			// The waypoints, named so the cancellation witness and the
			// distributive collapse are terms the checker sees.
			zero := v.HrealOfNum.Apply(ctx.Numeral(0)) // 0
			one := v.HrealOfNum.Apply(ctx.Numeral(1))  // 1
			zeroM := v.HrealMul.Apply(zero, m)         // 0·m₀ — the goal's RHS
			oneM := v.HrealMul.Apply(one, m)           // 1·m₀ — the cancellation witness

			a.Do(By(
				// EqAddRightCancel @ (0, 0·m₀, 1·m₀): (a+p = b+p) ⇔ (a = b).
				// The third witness is the whole trick — adding 1·m₀ is what
				// makes the product side distribute.
				At(EqAddRightCancel, zero, zeroM, oneM),

				// MulSym @ (0, m₀) and @ (1, m₀): re-orient both products so
				// they share the left factor LeftDistrib needs.
				At(MulSym, zero, m),
				At(MulSym, one, m),

				// LeftDistrib @ (m₀, 0, 1): m₀·0 + m₀·1 = m₀·(0+1) — the
				// collapse the whole shift was arranged to expose.
				At(LeftDistrib, m, zero, one),

				// AddLeftId @ 1 and @ 1·m₀: the first turns m₀·(0+1) into
				// m₀·1, the second reduces the goal's right side 0 + 1·m₀ to
				// 1·m₀. Both sides are now 1·m₀.
				At(AddLeftId, one),
				At(AddLeftId, oneM),
			))
		}),
})}

// LeftDistrib — left distributivity of hreal multiplication over
// hreal addition:
//
//	⊢ ∀x y z : hreal. (x * (y + z)) = ((x * y) + (x * z))
//
// This law IS eudoxus_slope.LeftDistrib, transported across the quotient —
// both operations compute at the classes.
var LeftDistrib = leftDistribThm{family.Add(registry.ProofEntry{
	Name: "LeftDistrib",
	Key:  "prop_2568ec6910328251",
	Build: family.Theorem("∀x y z:hreal. x * (y + z) = x * y + x * z",
		func(a *Argument) {
			a.Induct("x")
			a.Induct("y")
			a.Induct("z")
			a.Show(
				"at representatives sums and products compute to classes, "+
					"and class equality is nadd_eq — slope distributivity",
				Simp(Fwd(HrealAddDef), Fwd(HrealMulDef), Fwd(HrealDef.Eq)),
				By(eudoxus_slope.LeftDistrib))
		}),
})}

// MulLeftInverse — every nonzero hreal has a left multiplicative
// inverse:
//
//	⊢ ∀x : hreal. x ≠ 0 ⇒ (hreal_inv(x) * x) = 1
//
// This law IS eudoxus_slope.MulLeftInverse, transported across the quotient:
// at a representative both numerals are classes, the reciprocal and
// the product compute to classes, and both class equalities — the
// hypothesis's and the goal's — read as nadd_eq.
var MulLeftInverse = mulLeftInverseThm{family.Add(registry.ProofEntry{
	Name: "MulLeftInverse",
	Key:  "prop_d5909276984ada0c",
	Build: family.Theorem(
		Statement{
			Binders: "∀x:hreal.",
			Hypotheses: []string{
				"x ≠ hreal_of_num(0)",
			},
			Conclusion: "hreal_inv(x) * x = hreal_of_num(1)",
		},
		func(a *Argument) {
			a.Induct("x")
			a.Show(
				"at a representative everything computes to classes and "+
					"class equality reads as nadd_eq — the slope inverse law",
				Simp(Fwd(HrealOfNumDef), Fwd(HrealInvDef), Fwd(HrealMulDef), Fwd(HrealDef.Eq)),
				By(eudoxus_slope.MulLeftInverse))
		}),
})}

// ---------------------------------------------------------------------------
// The numeral embedding ℕ ↪ hreal and its morphism laws
// ---------------------------------------------------------------------------
//
// the numeral embedding ℕ ↪ hreal and its morphism laws: both binders
// are numbers, so nothing inducts — the numerals unfold to classes,
// the operations compute at them, and the slope law mirroring the
// member is the residual.
//
// README: "the ℕ-embedding morphism laws".

// OfNumEq — the numeral embedding is injective:
//
//	⊢ ∀m n : num. hreal_of_num(m) = hreal_of_num(n) ⇔ m = n
//
// This law IS eudoxus_slope.OfNumEq, read through the class equality.
var OfNumEq = ofNumEqThm{family.Add(registry.ProofEntry{
	Name: "OfNumEq",
	Key:  "prop_495cdbf9f4b1dbee",
	Build: family.Theorem(
		"∀m n:num. hreal_of_num(m) = hreal_of_num(n) ⇔ m = n",
		func(a *Argument, m, n Term) {
			a.Show(
				"both numerals are classes of embedded slopes, and class equality is nadd_eq — slope injectivity",
				Simp(Fwd(HrealOfNumDef), Fwd(HrealDef.Eq)),
				By(eudoxus_slope.OfNumEq))
		}),
})}

// OfNumLessEq — the numeral embedding preserves and reflects order:
//
//	⊢ ∀m n : num. (hreal_of_num(m) ≤ hreal_of_num(n)) ⇔ (m ≤ n)
//
// This law IS eudoxus_slope.OfNumLessEq, read through the order at classes.
var OfNumLessEq = ofNumLessEqThm{family.Add(registry.ProofEntry{
	Name: "OfNumLessEq",
	Key:  "prop_66bf86593928ab7f",
	Build: family.Theorem(
		"∀m n:num. hreal_of_num(m) ≤ hreal_of_num(n) ⇔ m ≤ n",
		func(a *Argument, m, n Term) {
			a.Show(
				"both numerals are classes of embedded slopes, and the order "+
					"at classes is the slope order — the slope order embedding",
				Simp(Fwd(HrealOfNumDef), Fwd(HrealLeDef)),
				By(eudoxus_slope.OfNumLessEq))
		}),
})}

// OfNumAdd — the numeral embedding is additive:
//
//	⊢ ∀m n : num. (hreal_of_num(m) + hreal_of_num(n)) = hreal_of_num(m + n)
//
// This law IS eudoxus_slope.OfNumAdd: the three numerals are classes, the sum
// computes to a class, and class equality is nadd_eq.
var OfNumAdd = ofNumAddThm{family.Add(registry.ProofEntry{
	Name: "OfNumAdd",
	Key:  "prop_6fbe1d8452f7ee64",
	Build: family.Theorem(
		"∀m n:num. hreal_of_num(m) + hreal_of_num(n) = hreal_of_num(m + n)",
		func(a *Argument, m, n Term) {
			a.Show(
				"the numerals are classes, the sum computes to a "+
					"class, and class equality is nadd_eq — slope additivity",
				Simp(Fwd(HrealOfNumDef), Fwd(HrealAddDef), Fwd(HrealDef.Eq)),
				By(eudoxus_slope.OfNumAdd))
		}),
})}

// OfNumMul — multiplicativity of the ℕ-embedding:
//
//	⊢ ∀m n : num. (hreal_of_num(m) * hreal_of_num(n)) = hreal_of_num(m * n)
//
// This law IS eudoxus_slope.OfNumMul — the exact mirror of OfNumAdd one
// operation over.
var OfNumMul = ofNumMulThm{family.Add(registry.ProofEntry{
	Name: "OfNumMul",
	Key:  "prop_65828cabe46361e9",
	Build: family.Theorem(
		"∀m n:num. hreal_of_num(m) * hreal_of_num(n) = hreal_of_num(m * n)",
		func(a *Argument, m, n Term) {
			a.Show(
				"the numerals are classes, the product computes to a class, "+
					"and class equality is nadd_eq — slope multiplicativity",
				Simp(Fwd(HrealOfNumDef), Fwd(HrealMulDef), Fwd(HrealDef.Eq)),
				By(eudoxus_slope.OfNumMul))
		}),
})}

// ---------------------------------------------------------------------------
// The hreal order
// ---------------------------------------------------------------------------
//
// the hreal order: the linear-order laws, the order's defining
// subtraction, and compatibility with addition and multiplication. Most
// are transports of the slope order; LessEqAdd2 is proved at the
// quotient level from its siblings.
//
// README: "the total order".

// LessEqRefl — the hreal order is reflexive:
//
//	⊢ ∀x : hreal. (x ≤ x)
//
// At a representative the order at classes is the slope order, which
// absorbs its equivalence — eudoxus_slope.NaddEqImpliesLessEq gives
// nadd_eq(x, x) ⇒ (x ≤ x) — and slope equivalence is reflexive.
var LessEqRefl = lessEqReflThm{family.Add(registry.ProofEntry{
	Name: "LessEqRefl",
	Key:  "prop_f15b81833a892faf",
	Build: family.Theorem("∀x:hreal. x ≤ x",
		func(a *Argument) {
			a.Induct("x")
			a.Show(
				"the order at classes is the slope order; a slope "+
					"is below itself because it is equivalent to itself",
				Simp(Fwd(HrealLeDef)),
				By(eudoxus_slope.NaddEqImpliesLessEq, eudoxus_slope.NaddEqRefl))
		}),
})}

// lessEqTrans — the hreal order is transitive:
//
//	⊢ ∀x y z : hreal. (x ≤ y) ∧ (y ≤ z) ⇒ (x ≤ z)
//
// This law IS eudoxus_slope.LessEqTrans, transported across the quotient: the
// goal carries only order atoms, each the slope order at
// representatives.
var lessEqTrans = lessEqTransThm{family.Add(registry.ProofEntry{
	Name: "lessEqTrans",
	Key:  "prop_60942fb1b3740f6f",
	Build: family.Theorem(Statement{
		Binders: "∀x y z:hreal.",
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
				"the three order atoms are the slope order at representatives — slope transitivity",
				Simp(Fwd(HrealLeDef)),
				By(eudoxus_slope.LessEqTrans))
		}),
})}

// LessEqAntisym — antisymmetry (as an equivalence) of the hreal order:
//
//	⊢ ∀x y : hreal. x = y ⇔ (x ≤ y) ∧ (y ≤ x)
//
// This law IS eudoxus_slope.LessEqAntisym, transported across the quotient:
// class equality reads as nadd_eq, the order atoms as the slope order.
var LessEqAntisym = lessEqAntisymThm{family.Add(registry.ProofEntry{
	Name: "LessEqAntisym",
	Key:  "prop_5aa8c4dc4fa49519",
	Build: family.Theorem("∀x y:hreal. x = y ⇔ x ≤ y ∧ y ≤ x",
		func(a *Argument) {
			a.Induct("x")
			a.Induct("y")
			a.Show(
				"class equality is nadd_eq and the order at classes is the slope order — slope antisymmetry",
				Simp(Fwd(HrealLeDef), Fwd(HrealDef.Eq)),
				By(eudoxus_slope.LessEqAntisym))
		}),
})}

// LessEqTotal — the hreal order is total:
//
//	⊢ ∀x y : hreal. (x ≤ y) ∨ (y ≤ x)
//
// This law IS eudoxus_slope.LessEqTotal, transported across the quotient.
var LessEqTotal = lessEqTotalThm{family.Add(registry.ProofEntry{
	Name: "LessEqTotal",
	Key:  "prop_f72234556f6cf78b",
	Build: family.Theorem("∀x y:hreal. x ≤ y ∨ y ≤ x",
		func(a *Argument) {
			a.Induct("x")
			a.Induct("y")
			a.Show(
				"both disjuncts are the slope order at representatives — slope totality",
				Simp(Fwd(HrealLeDef)),
				By(eudoxus_slope.LessEqTotal))
		}),
})}

// LessEqExists — whenever x ≤ y in the quotient order, the gap is
// realized by an actual hreal difference:
//
//	⊢ ∀x y : hreal. (x ≤ y) ⇒ ∃d. y = (x + d)
//
// This is the quotient's substitute for subtraction, and the only
// place the order's defining content crosses the bridge: at
// representatives the hypothesis is the slope order, eudoxus_slope.LessEqExists
// realizes the gap as a slope d, and the class of d witnesses the hreal
// gap — the sum computes to a class and class equality is nadd_eq, so
// the residual is the slope fact itself.
var LessEqExists = lessEqExistsThm{family.Add(registry.ProofEntry{
	Name: "LessEqExists",
	Key:  "prop_70d7ef93bb54dac1",
	Build: family.Theorem(Statement{
		Binders: "∀x y:hreal.",
		Hypotheses: []string{
			"x ≤ y",
		},
		Conclusion: "∃d:hreal. y = x + d",
	},
		func(a *Argument) {
			v := ops(a.Ctx())
			a.Induct("x")
			a.StepArgs("xr")
			a.Induct("y")
			a.StepArgs("yr")
			a.Do(Simp(Fwd(HrealLeDef)))
			le := a.Assume()
			d, gap := a.Obtain(
				"the slope order realizes the gap: a slope d with yr equivalent to xr + d",
				"∃d:nadd. nadd_eq(yr, xr + d)",
				By(le, eudoxus_slope.LessEqExists))
			a.Take(v.HrealOfNadd.Apply(d))
			a.Show(
				"the class of the gap is the hreal gap: the sum computes to a class and class equality is nadd_eq",
				Simp(Fwd(HrealAddDef), Fwd(HrealDef.Eq)),
				By(gap))
		}),
})}

// LessEqSelfAdd — a hreal is below itself plus anything:
//
//	⊢ ∀x y : hreal. (x ≤ (x + y))
//
// This law IS eudoxus_slope.LessEqSelfAdd, transported across the quotient.
var LessEqSelfAdd = lessEqSelfAddThm{family.Add(registry.ProofEntry{
	Name: "LessEqSelfAdd",
	Key:  "prop_141eba7a55b7370a",
	Build: family.Theorem("∀x y:hreal. x ≤ x + y",
		func(a *Argument) {
			a.Induct("x")
			a.Induct("y")
			a.Show(
				"the sum computes to a class and the order at classes is the slope order — slope monotonicity",
				Simp(Fwd(HrealAddDef), Fwd(HrealLeDef)),
				By(eudoxus_slope.LessEqSelfAdd))
		}),
})}

// LessEqAddRight — adding the same hreal on the right of both sides
// preserves AND reflects the hreal order (the ⇔ form of
// right-cancellation):
//
//	⊢ ∀m n p : hreal. ((m + p) ≤ (n + p)) ⇔ (m ≤ n)
//
// This law IS eudoxus_slope.LessEqAddRight, transported across the quotient.
//
// The left-cancellation twin is one breath from this law + AddSym at
// any consumer, so no separate entry is minted.
var LessEqAddRight = lessEqAddRightThm{family.Add(registry.ProofEntry{
	Name: "LessEqAddRight",
	Key:  "prop_53397ac23e17b0ff",
	Build: family.Theorem("∀m n p:hreal. m + p ≤ n + p ⇔ m ≤ n",
		func(a *Argument) {
			a.Induct("m")
			a.Induct("n")
			a.Induct("p")
			a.Show(
				"both sums compute to classes and the order at classes "+
					"is the slope order — slope right-add invariance",
				Simp(Fwd(HrealAddDef), Fwd(HrealLeDef)),
				By(eudoxus_slope.LessEqAddRight))
		}),
})}

// LessEqAdd2 — inequalities add: if a ≤ b and c ≤ d then a + c ≤ b + d.
//
//	⊢ ∀a b c d : hreal. (a ≤ b) ∧ (c ≤ d)
//	 ⇒ ((a + c) ≤ (b + d))
//
// Direct hreal-level chain — no transport needed, everything stays on
// the quotient. The two hypotheses are shifted by DIFFERENT summands so
// that their conclusions meet at a common midpoint b₀ + c₀:
//
// - LessEqAddRight @ (a₀, b₀, c₀) shifts a ≤ b on the right by c₀,
// giving a₀+c₀ ≤ b₀+c₀.
// - LessEqAddRight @ (c₀, d₀, b₀) shifts c ≤ d on the right by b₀,
// giving c₀+b₀ ≤ d₀+b₀; AddSym re-orients both sums, giving
// b₀+c₀ ≤ b₀+d₀.
// - lessEqTrans @ (a₀+c₀, b₀+c₀, b₀+d₀) chains the two through that
// midpoint.
//
// The midpoint is the content of the proof: it is what forces the two
// shifts to use different summands, and it is spelled ground below.
var LessEqAdd2 = lessEqAdd2Thm{family.Add(registry.ProofEntry{
	Name: "LessEqAdd2",
	Key:  "prop_5baaac105f760ad2",
	Build: family.Theorem(Statement{
		Binders: "∀a b c d:hreal.",
		Hypotheses: []string{
			"a ≤ b",
			"c ≤ d",
		},
		Conclusion: "a + c ≤ b + d",
	},
		func(arg *Argument, a, b, c, d Term, bounds Fact) {
			v := ops(arg.Ctx())

			// The three points of the chain, named — the middle one is the
			// waypoint the whole argument is arranged around.
			aPlusC := v.HrealAdd.Apply(a, c) // a₀ + c₀
			bPlusC := v.HrealAdd.Apply(b, c) // b₀ + c₀ — the midpoint
			bPlusD := v.HrealAdd.Apply(b, d) // b₀ + d₀

			arg.Show(
				"chain the two shifted bounds through the midpoint b₀+c₀",
				By(
					bounds,
					// Shift each hypothesis on the right by the OTHER pair's
					// summand, so both land on the midpoint b₀+c₀.
					At(LessEqAddRight, a, b, c),
					At(LessEqAddRight, c, d, b),

					// AddSym @ (c₀, b₀) and @ (d₀, b₀): re-orient the second
					// shift's sums from c₀+b₀ / d₀+b₀ to b₀+c₀ / b₀+d₀.
					At(AddSym, c, b),
					At(AddSym, d, b),

					// lessEqTrans @ (a₀+c₀, b₀+c₀, b₀+d₀): chain the two
					// bounds through the midpoint.
					At(lessEqTrans, aPlusC, bPlusC, bPlusD),
				))
		}),
})}

// lessEqMulRight — transport slope multiplication's order law through
// representatives; the lifted products and order compute at classes.
var lessEqMulRight = lessEqMulRightThm{family.Add(registry.ProofEntry{
	Name: "lessEqMulRight",
	Key:  "prop_fd44ba761b93ef9a",
	Build: family.Theorem(Statement{
		Binders: "∀a b c:hreal.",
		Hypotheses: []string{
			"a ≤ b",
		},
		Conclusion: "a * c ≤ b * c",
	},
		func(arg *Argument) {
			arg.Induct("a")
			arg.Induct("b")
			arg.Induct("c")
			arg.Show(
				"the products and order at classes give the slope law",
				Simp(Fwd(HrealMulDef), Fwd(HrealLeDef)),
				By(eudoxus_slope.LessEqMulRight))
		}),
})}
