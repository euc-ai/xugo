// arithmetic.go — addition and multiplication on ⟦0, ∞⟧: a commutative
// semiring with 0 · ∞ = 0, whose operations extend those of the
// nonnegative reals and are monotone in the order. A finite summand
// cancels from an inequality, and a bound that holds up to every e > 0,
// or at every scale below 1, holds.
//
// A law is argued in two halves: when its two sides are ∞ (a sum is ∞
// when a summand is, a product when a factor is ∞ and neither is 0), and
// what their finite values are (the finite value of a product is the
// product of the finite values; of a sum of finite values, the sum).
// ExtendedEq joins the two halves into an equation.
//
// In the labels, tx is the finite value extended_to_real(x) of an
// extended value x, and ty, tz those of y and z.

package extended_nonneg_real

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/real/real_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/registry"
)

// AddEqInfinity — a sum is ∞ exactly when a summand is: otherwise it is
// the image of a real, which is never ∞.
var AddEqInfinity = addEqInfinityThm{family.Add(registry.ProofEntry{
	Name: "AddEqInfinity",
	Key:  "prop_3ea8799cd8ffbd28",
	Build: family.Theorem("∀x y:extended_nonneg_real. "+
		"    x + y = extended_infinity ⇔ x = extended_infinity ∨ y = extended_infinity",
		func(a *Argument, x, y *Expr[ExtendedNonnegReal]) {
			a.Show(
				"a sum of finite values is the image of a real",
				By(
					Normalized,
					ExtendedAddDef.At(x, y),
					OfRealNotInfinity.At(a.TermAs[Real]("extended_to_real(x) + extended_to_real(y)"))))
		}),
})}

// ToRealAdd — the finite value of a sum of finite values is the sum of
// their finite values, a sum of nonnegative reals being read back by its
// image.
var ToRealAdd = toRealAddThm{family.Add(registry.ProofEntry{
	Name: "ToRealAdd",
	Key:  "prop_ed605d9d078ca929",
	Build: family.Theorem(Statement{
		Binders: "∀x y:extended_nonneg_real.",
		Hypotheses: []string{
			"x ≠ extended_infinity",
			"y ≠ extended_infinity",
		},
		Conclusion: "extended_to_real(x + y) = extended_to_real(x) + extended_to_real(y)",
	}, func(a *Argument, x, y *Expr[ExtendedNonnegReal], finite Fact) {
		a.Show(
			"x + y is the image of the nonnegative real tx + ty",
			ByArith(
				finite,
				ExtendedAddDef.At(x, y),
				ToRealOfReal.At(a.TermAs[Real]("extended_to_real(x) + extended_to_real(y)")),
				ToRealNonneg.At(x),
				ToRealNonneg.At(y)))
	}),
})}

// AddInfinity — ∞ absorbs every summand.
var AddInfinity = addInfinityThm{family.Add(registry.ProofEntry{
	Name: "AddInfinity",
	Key:  "prop_e0872db610a5251d",
	Build: family.Theorem("∀x:extended_nonneg_real. x + extended_infinity = extended_infinity",
		func(a *Argument, x *Expr[ExtendedNonnegReal]) {
			a.Show(
				"a summand is ∞",
				By(ExtendedAddDef.At(x, a.TermAs[ExtendedNonnegReal]("extended_infinity"))))
		}),
})}

// AddComm — addition is commutative, as addition of the finite values
// is.
var AddComm = addCommThm{family.Add(registry.ProofEntry{
	Name: "AddComm",
	Key:  "prop_1a98bfd8aa8265a3",
	Build: family.Theorem("∀x y:extended_nonneg_real. x + y = y + x",
		func(a *Argument, x, y *Expr[ExtendedNonnegReal]) {
			a.Show(
				"both sides test the same summands for ∞ and add the same values",
				By(
					ExtendedAddDef.At(x, y),
					ExtendedAddDef.At(y, x),
					real_construction.AddSym.At(
						a.TermAs[Real]("extended_to_real(x)"), a.TermAs[Real]("extended_to_real(y)"))))
		}),
})}

// AddZero — 0 is neutral for addition.
var AddZero = addZeroThm{family.Add(registry.ProofEntry{
	Name: "AddZero",
	Key:  "prop_471a777cf4b3567d",
	Build: family.Theorem("∀x:extended_nonneg_real. x + &0 = x",
		func(a *Argument, x *Expr[ExtendedNonnegReal]) {
			zero := a.TermAs[ExtendedNonnegReal]("&0")
			a.Cases(a.Term("x = extended_infinity"))
			a.When(
				"∞ absorbs 0",
				func(b *Argument, atInfinity Fact) {
					b.Show(
						"x + 0 is ∞",
						By(Normalized, atInfinity, ExtendedAddDef.At(x, zero)))
				})
			a.Otherwise(
				"a finite x adds the value 0 to its own",
				func(b *Argument, finite Fact) {
					sum := b.Have(
						"adding 0 to the finite value of x changes nothing",
						"extended_to_real(x) + &0 = extended_to_real(x)",
						ByArith())
					b.Show(
						"x + 0 is the image of the finite value of x",
						By(
							Normalized,
							finite,
							sum,
							ExtendedAddDef.At(x, zero),
							ZeroNotInfinity,
							ToRealZero,
							OfRealToReal.At(x)))
				})
		}),
})}

// OfRealAdd — on the nonnegative reals the embedding carries addition
// to addition: both images are finite with values r and s.
var OfRealAdd = ofRealAddThm{family.Add(registry.ProofEntry{
	Name: "OfRealAdd",
	Key:  "prop_a9e35ea955b5cec1",
	Build: family.Theorem(Statement{
		Binders: "∀r s:real.",
		Hypotheses: []string{
			"&0 ≤ r",
			"&0 ≤ s",
		},
		Conclusion: "extended_of_real(r) + extended_of_real(s) = extended_of_real(r + s)",
	}, func(a *Argument, r, s *Expr[Real], nonneg Fact) {
		a.Show(
			"the images of r and s are finite with values r and s",
			By(
				Normalized,
				nonneg,
				ExtendedAddDef.At(
					a.TermAs[ExtendedNonnegReal]("extended_of_real(r)"),
					a.TermAs[ExtendedNonnegReal]("extended_of_real(s)")),
				OfRealNotInfinity.At(r),
				OfRealNotInfinity.At(s),
				ToRealOfReal.At(r),
				ToRealOfReal.At(s)))
	}),
})}

// AddAssoc — addition is associative: both sides are ∞ when a summand
// is, and otherwise both have the finite value tx + ty + tz.
var AddAssoc = addAssocThm{family.Add(registry.ProofEntry{
	Name: "AddAssoc",
	Key:  "prop_9676ab454bbd7477",
	Build: family.Theorem("∀x y z:extended_nonneg_real. x + y + z = x + (y + z)",
		func(a *Argument, x, y, z *Expr[ExtendedNonnegReal]) {
			xy := a.TermAs[ExtendedNonnegReal]("x + y")
			yz := a.TermAs[ExtendedNonnegReal]("y + z")
			a.Cases(a.Term("x + y + z = extended_infinity"))
			a.When(
				"a summand is ∞, and both sides are ∞",
				func(b *Argument, infinite Fact) {
					b.Show(
						"x + (y + z) is ∞ too",
						By(
							Normalized,
							infinite,
							AddEqInfinity.At(xy, z),
							AddEqInfinity.At(x, y),
							AddEqInfinity.At(x, yz),
							AddEqInfinity.At(y, z)))
				})
			a.Otherwise(
				"every summand is finite",
				func(b *Argument, finite Fact) {
					parts := b.Have(
						"x, y, z and the partial sums are finite",
						"x ≠ extended_infinity ∧ "+
							"y ≠ extended_infinity ∧ "+
							"z ≠ extended_infinity ∧ "+
							"x + y ≠ extended_infinity ∧ "+
							"y + z ≠ extended_infinity",
						By(finite, AddEqInfinity.At(xy, z), AddEqInfinity.At(x, y), AddEqInfinity.At(y, z)))
					b.Show(
						"both sides are finite with value tx + ty + tz",
						ByArith(
							finite,
							parts,
							ExtendedEq.At(
								b.TermAs[ExtendedNonnegReal]("x + y + z"), b.TermAs[ExtendedNonnegReal]("x + (y + z)")),
							AddEqInfinity.At(x, yz),
							ToRealAdd.At(xy, z),
							ToRealAdd.At(x, y),
							ToRealAdd.At(x, yz),
							ToRealAdd.At(y, z)))
				})
		}),
})}

// AddLeMono — adding the same value preserves the order.
var AddLeMono = addLeMonoThm{family.Add(registry.ProofEntry{
	Name: "AddLeMono",
	Key:  "prop_b5c16a54819ae81e",
	Build: family.Theorem(Statement{
		Binders:    "∀x y z:extended_nonneg_real.",
		Hypotheses: []string{"x ≤ y"},
		Conclusion: "x + z ≤ y + z",
	}, func(a *Argument, x, y, z *Expr[ExtendedNonnegReal], below Fact) {
		a.Cases(a.Term("y + z = extended_infinity"))
		a.When(
			"y + z is ∞, above everything",
			func(b *Argument, infinite Fact) {
				b.Show(
					"x + z lies below ∞",
					By(Normalized, infinite, LeInfinity.At(b.TermAs[ExtendedNonnegReal]("x + z"))))
			})
		a.Otherwise(
			"y + z is finite",
			func(b *Argument, finiteSum Fact) {
				finite := b.Have(
					"y and z are finite",
					"y ≠ extended_infinity ∧ z ≠ extended_infinity",
					By(finiteSum, AddEqInfinity.At(y, z)))
				values := b.Have(
					"x lies below the finite y, so x is finite with the smaller value",
					"x ≠ extended_infinity ∧ extended_to_real(x) ≤ extended_to_real(y)",
					By(below, finite, ExtendedLeDef.At(x, y)))
				b.Show(
					"x + z is finite with value tx + tz, at most ty + tz",
					ByArith(
						values,
						finite,
						ExtendedLeDef.At(b.TermAs[ExtendedNonnegReal]("x + z"), b.TermAs[ExtendedNonnegReal]("y + z")),
						AddEqInfinity.At(x, z),
						ToRealAdd.At(x, z),
						ToRealAdd.At(y, z)))
			})
	}),
})}

// AddLeAdd — two inequalities add: raise the first summand, then the
// second.
var AddLeAdd = addLeAddThm{family.Add(registry.ProofEntry{
	Name: "AddLeAdd",
	Key:  "prop_884063f33f37f871",
	Build: family.Theorem(Statement{
		Binders: "∀x₁ y₁ x₂ y₂:extended_nonneg_real.",
		Hypotheses: []string{
			"x₁ ≤ x₂",
			"y₁ ≤ y₂",
		},
		Conclusion: "x₁ + y₁ ≤ x₂ + y₂",
	},
		func(a *Argument, x1, y1, x2, y2 *Expr[ExtendedNonnegReal], below Fact) {
			a.Show(
				"x₁ + y₁ lies below x₂ + y₁, which lies below x₂ + y₂",
				By(
					below,
					AddLeMono.At(x1, x2, y1),
					AddLeMono.At(y1, y2, x2),
					AddComm.At(x2, y1),
					AddComm.At(x2, y2),
					LeTrans.At(
						a.TermAs[ExtendedNonnegReal]("x₁ + y₁"),
						a.TermAs[ExtendedNonnegReal]("x₂ + y₁"),
						a.TermAs[ExtendedNonnegReal]("x₂ + y₂"))))
		}),
})}

// LeAddRight — adding a value never decreases: the added finite value is
// nonnegative.
var LeAddRight = leAddRightThm{family.Add(registry.ProofEntry{
	Name: "LeAddRight",
	Key:  "prop_ac31d33fb5b9b124",
	Build: family.Theorem("∀x y:extended_nonneg_real. x ≤ x + y",
		func(a *Argument, x, y *Expr[ExtendedNonnegReal]) {
			a.Cases(a.Term("x + y = extended_infinity"))
			a.When(
				"x + y is ∞, above everything",
				func(b *Argument, infinite Fact) {
					b.Show(
						"x lies below ∞",
						By(Normalized, infinite, LeInfinity.At(x)))
				})
			a.Otherwise(
				"x + y is finite",
				func(b *Argument, finiteSum Fact) {
					finite := b.Have(
						"x and y are finite",
						"x ≠ extended_infinity ∧ y ≠ extended_infinity",
						By(finiteSum, AddEqInfinity.At(x, y)))
					b.Show(
						"the value of x + y is tx + ty, at least tx",
						ByArith(
							finiteSum,
							finite,
							ExtendedLeDef.At(x, b.TermAs[ExtendedNonnegReal]("x + y")),
							ToRealAdd.At(x, y),
							ToRealNonneg.At(y)))
				})
		}),
})}

// AddLeCancel — a finite summand cancels from an inequality in ⟦0, ∞⟧:
// x + z ≤ y + z with z finite gives x ≤ y. At y = ∞ there is nothing to
// prove. Otherwise y + z is finite, so x + z is too, and on the finite
// values tx + tz ≤ ty + tz.
var AddLeCancel = addLeCancelThm{family.Add(registry.ProofEntry{
	Name: "AddLeCancel",
	Key:  "prop_4f2ba59af0314c78",
	Build: family.Theorem(Statement{
		Binders: "∀x y z:extended_nonneg_real.",
		Hypotheses: []string{
			"x + z ≤ y + z",
			"z ≠ extended_infinity",
		},
		Conclusion: "x ≤ y",
	}, func(a *Argument, x, y, z *Expr[ExtendedNonnegReal], bound, zFinite Fact) {
		finiteY := a.Unless(
			a.Term("y = extended_infinity"),
			"everything lies below ∞",
			Given(func(b *Argument, top Fact) {
				b.Show(
					"x lies below ∞",
					top.Rw(),
					Cite(LeInfinity))
			}))
		values := a.Have(
			"y + z is finite, so x + z is too, and their finite values obey the bound",
			"x ≠ extended_infinity ∧ extended_to_real(x + z) ≤ extended_to_real(y + z)",
			By(finiteY, bound, zFinite, ExtendedLeDef, AddEqInfinity))
		a.Show(
			"the finite value of z cancels",
			ByArith(finiteY, values, zFinite, ExtendedLeDef.At(x, y), ToRealAdd.At(x, z), ToRealAdd.At(y, z)))
	}),
})}

// LeOfLeAddPositive — in ⟦0, ∞⟧, x ≤ y as soon as x ≤ y + e for every
// real e > 0. At y = ∞ there is nothing to prove. Otherwise x lies below
// the finite y + 1, so x is finite too, and the bound reads on the finite
// values as tx ≤ ty + e for every e > 0; were tx above ty, the bound would
// fail at half the gap.
var LeOfLeAddPositive = leOfLeAddPositiveThm{family.Add(registry.ProofEntry{
	Name: "LeOfLeAddPositive",
	Key:  "prop_cf4119256e0a7fb7",
	Build: family.Theorem(Statement{
		Binders:    "∀x y:extended_nonneg_real.",
		Hypotheses: []string{"∀e:real. &0 < e ⇒ x ≤ y + extended_of_real(e)"},
		Conclusion: "x ≤ y",
	}, func(a *Argument, x, y *Expr[ExtendedNonnegReal], near Fact) {
		finite := a.Unless(
			a.Term("y = extended_infinity"),
			"everything lies below ∞",
			Given(func(b *Argument, top Fact) {
				b.Show(
					"x lies below ∞",
					top.Rw(),
					Cite(LeInfinity))
			}))
		finiteX := a.Have(
			"x lies below the finite y + 1, so x is finite",
			"x ≠ extended_infinity",
			By(
				near.At(a.TermAs[Real]("&1")),
				real_order_ring.ZeroLessThanOne,
				finite,
				AddEqInfinity,
				OfRealNotInfinity,
				ExtendedLeDef))
		values := a.Have(
			"the finite values obey the bound",
			"∀e:real. &0 < e ⇒ extended_to_real(x) ≤ extended_to_real(y) + e",
			Derive(func(b *Argument) {
				e := b.FixAs[Real]()
				positive := b.Assume()
				sum := b.Have(
					"the finite value of y + e is ty + e",
					"extended_to_real(y + extended_of_real(e)) = extended_to_real(y) + e",
					ByArith(
						finite,
						positive,
						ToRealAdd.At(y, b.TermAs[ExtendedNonnegReal]("extended_of_real(e)")),
						OfRealNotInfinity.At(e),
						ToRealOfReal.At(e)))
				b.Show(
					"x lies below the finite y + e",
					By(Normalized, near.At(e), positive, finite, sum, AddEqInfinity, OfRealNotInfinity, ExtendedLeDef))
			}))
		below := a.Have(
			"tx ≤ ty, the bound failing at half of any gap",
			"extended_to_real(x) ≤ extended_to_real(y)",
			ByArith(values.At(a.TermAs[Real]("(extended_to_real(x) - extended_to_real(y)) / &2"))))
		a.Show(
			"so x ≤ y",
			By(finiteX, below, ExtendedLeDef))
	}),
})}

// AddEqZero — a sum is 0 exactly when both summands are: a sum of two
// nonnegative values is 0 only when both are.
var AddEqZero = addEqZeroThm{family.Add(registry.ProofEntry{
	Name: "AddEqZero",
	Key:  "prop_36a737b69ebffa48",
	Build: family.Theorem("∀x y:extended_nonneg_real. x + y = &0 ⇔ x = &0 ∧ y = &0",
		func(a *Argument, x, y *Expr[ExtendedNonnegReal]) {
			a.Iff()
			a.Backward(
				"0 + 0 is 0",
				func(b *Argument, zeros Fact) {
					b.Show(
						"x + y is 0 + 0",
						By(Normalized, zeros, AddZero.At(b.TermAs[ExtendedNonnegReal]("&0"))))
				})
			a.Forward(
				"a zero sum has finite summands of value 0",
				func(b *Argument, zeroSum Fact) {
					finite := b.Have(
						"a sum equal to 0 is finite, and so are its summands",
						"x ≠ extended_infinity ∧ y ≠ extended_infinity",
						By(zeroSum, AddEqInfinity.At(x, y), ZeroNotInfinity))
					sumValue := b.Have(
						"the sum has value 0",
						"extended_to_real(x + y) = &0",
						By(zeroSum, ToRealZero))
					values := b.Have(
						"two nonnegative values summing to 0 are both 0",
						"extended_to_real(x) = &0 ∧ extended_to_real(y) = &0",
						ByArith(sumValue, finite, ToRealAdd.At(x, y), ToRealNonneg.At(x), ToRealNonneg.At(y)))
					b.Show(
						"x and y are the images of their values, 0",
						By(Normalized, finite, values, OfRealToReal.At(x), OfRealToReal.At(y)))
				})
		}),
})}

// MulEqInfinity — a product is ∞ exactly when one factor is ∞ and the
// other is not 0.
var MulEqInfinity = mulEqInfinityThm{family.Add(registry.ProofEntry{
	Name: "MulEqInfinity",
	Key:  "prop_46430d45ae01ba70",
	Build: family.Theorem("∀x y:extended_nonneg_real. "+
		"    x * y = extended_infinity ⇔ x = extended_infinity ∧ y ≠ &0 ∨ y = extended_infinity ∧ x ≠ &0",
		func(a *Argument, x, y *Expr[ExtendedNonnegReal]) {
			a.Show(
				"0 and the image of a product of values are not ∞",
				By(
					ExtendedMulDef.At(x, y),
					ZeroNotInfinity,
					OfRealNotInfinity.At(a.TermAs[Real]("extended_to_real(x) * extended_to_real(y)"))))
		}),
})}

// ToRealMul — the finite value of a product is the product of the finite
// values, ∞ included: a product that is 0 or ∞ has value 0, and so has
// one of its factors.
var ToRealMul = toRealMulThm{family.Add(registry.ProofEntry{
	Name: "ToRealMul",
	Key:  "prop_6dd82956d1571859",
	Build: family.Theorem("∀x y:extended_nonneg_real. "+
		"    extended_to_real(x * y) = extended_to_real(x) * extended_to_real(y)",
		func(a *Argument, x, y *Expr[ExtendedNonnegReal]) {
			tx := a.TermAs[Real]("extended_to_real(x)")
			ty := a.TermAs[Real]("extended_to_real(y)")
			a.Cases(a.Term("x = &0 ∨ y = &0"))
			a.When(
				"a factor is 0: the product is 0, and a factor has value 0",
				func(b *Argument, zero Fact) {
					values := b.Have(
						"the product and one factor have value 0",
						"extended_to_real(x * y) = &0 ∧ (extended_to_real(x) = &0 ∨ extended_to_real(y) = &0)",
						By(zero, ExtendedMulDef.At(x, y), ToRealZero))
					b.Show(
						"both sides are 0",
						By(values, real_ring.MulEqZero.At(tx, ty)))
				})
			a.Otherwise(
				"no factor is 0",
				func(b *Argument, nonzero Fact) {
					b.Cases(b.Term("x = extended_infinity ∨ y = extended_infinity"))
					b.When(
						"a factor is ∞: the product is ∞, of value 0, as is that factor",
						func(c *Argument, infinite Fact) {
							values := c.Have(
								"the product and one factor have value 0",
								"extended_to_real(x * y) = &0 ∧ (extended_to_real(x) = &0 ∨ extended_to_real(y) = &0)",
								By(nonzero, infinite, ExtendedMulDef.At(x, y), ToRealInfinity))
							c.Show(
								"both sides are 0",
								By(values, real_ring.MulEqZero.At(tx, ty)))
						})
					b.Otherwise(
						"both factors are finite: the product is the image of tx · ty",
						func(c *Argument, finite Fact) {
							nonneg := c.Have(
								"the product of the values is nonnegative",
								"&0 ≤ extended_to_real(x) * extended_to_real(y)",
								ByArith(ToRealNonneg.At(x), ToRealNonneg.At(y)))
							c.Show(
								"the image of tx · ty reads back as tx · ty",
								By(
									finite,
									nonzero,
									nonneg,
									ExtendedMulDef.At(x, y),
									ToRealOfReal.At(c.TermAs[Real]("extended_to_real(x) * extended_to_real(y)"))))
						})
				})
		}),
})}

// MulEqZero — a product is 0 exactly when a factor is: a nonzero product
// of values has nonzero factors, and a factor of value 0 that is not ∞ is
// 0.
var MulEqZero = mulEqZeroThm{family.Add(registry.ProofEntry{
	Name: "MulEqZero",
	Key:  "prop_4146e7a056a8a666",
	Build: family.Theorem("∀x y:extended_nonneg_real. x * y = &0 ⇔ x = &0 ∨ y = &0",
		func(a *Argument, x, y *Expr[ExtendedNonnegReal]) {
			a.Iff()
			a.Backward(
				"a factor 0 makes the product 0",
				func(b *Argument, zero Fact) {
					b.Show(
						"the definition's first case",
						By(zero, ExtendedMulDef.At(x, y)))
				})
			a.Forward(
				"a zero product has a factor of value 0",
				func(b *Argument, zeroProduct Fact) {
					values := b.Have(
						"tx · ty is the value of the product, 0, so a factor has value 0",
						"extended_to_real(x) = &0 ∨ extended_to_real(y) = &0",
						By(
							Normalized,
							zeroProduct,
							ToRealMul.At(x, y),
							ToRealZero,
							real_ring.MulEqZero.At(
								b.TermAs[Real]("extended_to_real(x)"), b.TermAs[Real]("extended_to_real(y)"))))
					b.Show(
						"that factor is 0, being finite since the product is not ∞, or the other factor is 0",
						By(
							zeroProduct,
							values,
							MulEqInfinity.At(x, y),
							ZeroNotInfinity,
							OfRealToReal.At(x),
							OfRealToReal.At(y)))
				})
		}),
})}

// MulComm — multiplication is commutative, as multiplication of the
// finite values is.
var MulComm = mulCommThm{family.Add(registry.ProofEntry{
	Name: "MulComm",
	Key:  "prop_9fb7a55b90f3e4bb",
	Build: family.Theorem("∀x y:extended_nonneg_real. x * y = y * x",
		func(a *Argument, x, y *Expr[ExtendedNonnegReal]) {
			a.Show(
				"both sides test the same factors for 0 and ∞ and multiply the same values",
				By(
					ExtendedMulDef.At(x, y),
					ExtendedMulDef.At(y, x),
					real_construction.MulSym.At(
						a.TermAs[Real]("extended_to_real(x)"), a.TermAs[Real]("extended_to_real(y)"))))
		}),
})}

// MulZero — a product with 0 is 0, ∞ included.
var MulZero = mulZeroThm{family.Add(registry.ProofEntry{
	Name: "MulZero",
	Key:  "prop_528445570cd4714b",
	Build: family.Theorem("∀x:extended_nonneg_real. x * &0 = &0",
		func(a *Argument, x *Expr[ExtendedNonnegReal]) {
			a.Show(
				"a factor is 0",
				By(ExtendedMulDef.At(x, a.TermAs[ExtendedNonnegReal]("&0"))))
		}),
})}

// MulInfinity — a nonzero value times ∞ is ∞.
var MulInfinity = mulInfinityThm{family.Add(registry.ProofEntry{
	Name: "MulInfinity",
	Key:  "prop_ba32f2fb6f51cb",
	Build: family.Theorem(Statement{
		Binders:    "∀x:extended_nonneg_real.",
		Hypotheses: []string{"x ≠ &0"},
		Conclusion: "x * extended_infinity = extended_infinity",
	}, func(a *Argument, x *Expr[ExtendedNonnegReal], nonzero Fact) {
		a.Show(
			"neither factor is 0, and one is ∞",
			By(
				nonzero,
				ExtendedMulDef.At(x, a.TermAs[ExtendedNonnegReal]("extended_infinity")),
				ZeroNotInfinity))
	}),
})}

// OfRealMul — for a nonnegative r the embedding carries multiplication by r
// to multiplication: with s ≥ 0 both sides are finite with value r · s, and
// with s < 0 the factor s and the product r · s both embed as 0.
var OfRealMul = ofRealMulThm{family.Add(registry.ProofEntry{
	Name: "OfRealMul",
	Key:  "prop_ba76584979179579",
	Build: family.Theorem(Statement{
		Binders:    "∀r s:real.",
		Hypotheses: []string{"&0 ≤ r"},
		Conclusion: "extended_of_real(r) * extended_of_real(s) = extended_of_real(r * s)",
	}, func(a *Argument, r, s *Expr[Real], nonneg Fact) {
		imageR := a.TermAs[ExtendedNonnegReal]("extended_of_real(r)")
		imageS := a.TermAs[ExtendedNonnegReal]("extended_of_real(s)")
		rs := a.TermAs[Real]("r * s")
		a.Cases(a.Term("&0 ≤ s"))
		a.When(
			"a nonnegative second factor",
			func(b *Argument, nonnegS Fact) {
				b.Show(
					"neither side is ∞, and both have value r · s",
					ByArith(
						nonneg,
						nonnegS,
						ExtendedEq.At(
							b.TermAs[ExtendedNonnegReal]("extended_of_real(r) * extended_of_real(s)"),
							b.TermAs[ExtendedNonnegReal]("extended_of_real(r * s)")),
						MulEqInfinity.At(imageR, imageS),
						OfRealNotInfinity.At(r),
						OfRealNotInfinity.At(s),
						OfRealNotInfinity.At(rs),
						ToRealMul.At(imageR, imageS),
						ToRealOfReal.At(r),
						ToRealOfReal.At(s),
						ToRealOfReal.At(rs)))
			})
		a.Otherwise(
			"a negative second factor",
			func(b *Argument, negative Fact) {
				nonpositive := b.Have(
					"s and the product r · s are at most 0",
					"s ≤ &0 ∧ r * s ≤ &0",
					ByArith(nonneg, negative))
				b.Show(
					"both embed as 0, and so does the product of the images",
					By(Normalized, nonpositive, OfRealNeg.At(s), OfRealNeg.At(rs), MulZero.At(imageR)))
			})
	}),
})}

// MulOne — 1 is neutral for multiplication: x · 1 is ∞ exactly when x
// is, 1 being neither 0 nor ∞, and its value is tx · 1.
var MulOne = mulOneThm{family.Add(registry.ProofEntry{
	Name: "MulOne",
	Key:  "prop_ea106d79abd72ec8",
	Build: family.Theorem("∀x:extended_nonneg_real. x * &1 = x",
		func(a *Argument, x *Expr[ExtendedNonnegReal]) {
			one := a.TermAs[ExtendedNonnegReal]("&1")
			a.Show(
				"x · 1 and x are ∞ together and have the same value",
				ByArith(
					ExtendedEq.At(a.TermAs[ExtendedNonnegReal]("x * &1"), x),
					MulEqInfinity.At(x, one),
					OfRealNotInfinity.At(a.TermAs[Real]("&1")),
					OfRealInjective.At(a.TermAs[Real]("&1"), a.TermAs[Real]("&0")),
					ToRealMul.At(x, one),
					ToRealOfReal.At(a.TermAs[Real]("&1"))))
		}),
})}

// MulAssoc — multiplication is associative: both sides are ∞ exactly
// when no factor is 0 and some factor is ∞, and both have value
// tx · ty · tz.
var MulAssoc = mulAssocThm{family.Add(registry.ProofEntry{
	Name: "MulAssoc",
	Key:  "prop_453ffb931714d01e",
	Build: family.Theorem("∀x y z:extended_nonneg_real. x * y * z = x * (y * z)",
		func(a *Argument, x, y, z *Expr[ExtendedNonnegReal]) {
			xy := a.TermAs[ExtendedNonnegReal]("x * y")
			yz := a.TermAs[ExtendedNonnegReal]("y * z")
			infinite := a.Have(
				"both sides are ∞ exactly when no factor is 0 and some factor is ∞",
				"x * y * z = extended_infinity ⇔ x * (y * z) = extended_infinity",
				By(
					MulEqInfinity.At(xy, z),
					MulEqInfinity.At(x, y),
					MulEqInfinity.At(x, yz),
					MulEqInfinity.At(y, z),
					MulEqZero.At(x, y),
					MulEqZero.At(y, z),
					ZeroNotInfinity))
			values := a.Have(
				"both sides have value tx · ty · tz",
				"extended_to_real(x * y * z) = extended_to_real(x * (y * z))",
				Simp(Fwd(ToRealMul)),
				ByArith())
			a.Show(
				"so the two sides are equal",
				By(
					infinite,
					values,
					ExtendedEq.At(
						a.TermAs[ExtendedNonnegReal]("x * y * z"), a.TermAs[ExtendedNonnegReal]("x * (y * z)"))))
		}),
})}

// MulAddDistrib — multiplication distributes over addition. Both sides
// are ∞ together; when they are finite and y + z is ∞, x is 0 and both
// sides are 0, and otherwise both have value tx · (ty + tz).
var MulAddDistrib = mulAddDistribThm{family.Add(registry.ProofEntry{
	Name: "MulAddDistrib",
	Key:  "prop_3a4d75cd1d99294b",
	Build: family.Theorem("∀x y z:extended_nonneg_real. x * (y + z) = x * y + x * z",
		func(a *Argument, x, y, z *Expr[ExtendedNonnegReal]) {
			yz := a.TermAs[ExtendedNonnegReal]("y + z")
			xy := a.TermAs[ExtendedNonnegReal]("x * y")
			xz := a.TermAs[ExtendedNonnegReal]("x * z")
			infinite := a.Have(
				"both sides are ∞ exactly when x is ∞ and y or z is not 0, or x is not 0 and y or z is ∞",
				"x * (y + z) = extended_infinity ⇔ x * y + x * z = extended_infinity",
				By(
					MulEqInfinity.At(x, yz),
					AddEqInfinity.At(y, z),
					AddEqZero.At(y, z),
					AddEqInfinity.At(xy, xz),
					MulEqInfinity.At(x, y),
					MulEqInfinity.At(x, z)))
			a.Cases(a.Term("x * (y + z) = extended_infinity"))
			a.When(
				"both sides are ∞",
				func(b *Argument, atInfinity Fact) {
					b.Show(
						"x · y + x · z is ∞ as well",
						By(Normalized, infinite, atInfinity))
				})
			a.Otherwise(
				"both sides are finite",
				func(b *Argument, finiteProduct Fact) {
					b.Cases(b.Term("y + z = extended_infinity"))
					b.When(
						"y + z is ∞, so the finite x · (y + z) forces x = 0",
						func(c *Argument, infiniteSum Fact) {
							zero := c.TermAs[ExtendedNonnegReal]("&0")
							c.Show(
								"both sides are 0",
								By(
									Normalized,
									finiteProduct,
									infiniteSum,
									MulEqInfinity.At(x, yz),
									MulEqZero.At(x, yz),
									MulEqZero.At(x, y),
									MulEqZero.At(x, z),
									AddZero.At(zero)))
						})
					b.Otherwise(
						"y + z is finite",
						func(c *Argument, finiteSum Fact) {
							finite := c.Have(
								"y, z, x · y and x · z are finite",
								"y ≠ extended_infinity ∧ "+
									"z ≠ extended_infinity ∧ "+
									"x * y ≠ extended_infinity ∧ "+
									"x * z ≠ extended_infinity",
								By(finiteSum, finiteProduct, infinite, AddEqInfinity.At(y, z), AddEqInfinity.At(xy, xz)))
							values := c.Have(
								"both sides have value tx · ty + tx · tz",
								"extended_to_real(x * (y + z)) = extended_to_real(x * y + x * z)",
								ByArith(
									finite,
									ToRealMul.At(x, yz),
									Scaled(c.TermAs[Real]("extended_to_real(x)"), ToRealAdd.At(y, z)),
									ToRealAdd.At(xy, xz),
									ToRealMul.At(x, y),
									ToRealMul.At(x, z)))
							c.Show(
								"so the two sides are equal",
								By(
									infinite,
									values,
									ExtendedEq.At(
										c.TermAs[ExtendedNonnegReal]("x * (y + z)"), c.TermAs[ExtendedNonnegReal]("x * y + x * z"))))
						})
				})
		}),
})}

// MulLeMono — multiplying by the same value preserves the order.
var MulLeMono = mulLeMonoThm{family.Add(registry.ProofEntry{
	Name: "MulLeMono",
	Key:  "prop_fae458461f8023bf",
	Build: family.Theorem(Statement{
		Binders:    "∀x y z:extended_nonneg_real.",
		Hypotheses: []string{"x ≤ y"},
		Conclusion: "z * x ≤ z * y",
	}, func(a *Argument, x, y, z *Expr[ExtendedNonnegReal], below Fact) {
		zx := a.TermAs[ExtendedNonnegReal]("z * x")
		zy := a.TermAs[ExtendedNonnegReal]("z * y")
		a.Cases(a.Term("z = &0"))
		a.When(
			"z is 0: z · x is 0, the least value",
			func(b *Argument, zero Fact) {
				b.Show(
					"0 lies below z · y",
					By(Normalized, zero, MulEqZero.At(z, x), ZeroLe.At(zy)))
			})
		a.Otherwise(
			"z is not 0",
			func(b *Argument, nonzero Fact) {
				b.Cases(b.Term("z * y = extended_infinity"))
				b.When(
					"z · y is ∞, above everything",
					func(c *Argument, infinite Fact) {
						c.Show(
							"z · x lies below ∞",
							By(Normalized, infinite, LeInfinity.At(zx)))
					})
				b.Otherwise(
					"z · y is finite",
					func(c *Argument, finiteProduct Fact) {
						c.Cases(c.Term("y = &0"))
						c.When(
							"y is 0, so x lies below 0 and is 0",
							func(d *Argument, yZero Fact) {
								d.Show(
									"z · x is z · y",
									By(Normalized, yZero, below, ZeroLe.At(x), LeAntisym.At(x, y), LeRefl.At(zy)))
							})
						c.Otherwise(
							"y is not 0",
							func(d *Argument, yNonzero Fact) {
								values := d.Have(
									"z and y are finite, as z · y is, so x is finite with value at most ty",
									"z ≠ extended_infinity ∧ x ≠ extended_infinity ∧ extended_to_real(x) ≤ extended_to_real(y)",
									By(yNonzero, nonzero, finiteProduct, below, MulEqInfinity.At(z, y), ExtendedLeDef.At(x, y)))
								d.Show(
									"z · x is finite with value tz · tx, at most tz · ty",
									ByArith(
										values,
										ExtendedLeDef.At(zx, zy),
										MulEqInfinity.At(z, x),
										ToRealMul.At(z, x),
										ToRealMul.At(z, y),
										ToRealNonneg.At(z)))
							})
					})
			})
	}),
})}

// LeOfScaledLe — x ≤ y as soon as c·x ≤ y for every real
// c strictly between 0 and 1. At y = ∞ there is nothing to prove. Otherwise x
// is finite, since half of ∞ is ∞, which lies below no finite y; and on the
// finite values c·tx ≤ ty for every such c, so were tx above ty, the bound would
// fail at c = (tx + ty)/(2tx).
var LeOfScaledLe = leOfScaledLeThm{family.Add(registry.ProofEntry{
	Name: "LeOfScaledLe",
	Key:  "prop_43b14706eb2f7bab",
	Build: family.Theorem(Statement{
		Binders:    "∀x y:extended_nonneg_real.",
		Hypotheses: []string{"∀c:real. &0 < c ∧ c < &1 ⇒ extended_of_real(c) * x ≤ y"},
		Conclusion: "x ≤ y",
	}, func(a *Argument, x, y *Expr[ExtendedNonnegReal], scaled Fact) {
		finite := a.Unless(
			a.Term("y = extended_infinity"),
			"everything lies below ∞",
			Given(func(b *Argument, top Fact) {
				b.Show(
					"x lies below ∞",
					top.Rw(),
					Cite(LeInfinity))
			}))
		half := a.TermAs[Real]("&1 / &2")
		halfBetween := a.Have(
			"a half lies strictly between 0 and 1",
			"&0 < &1 / &2 ∧ &1 / &2 < &1",
			ByArith())
		halfOfInfinity := a.Have(
			"half of ∞ is ∞, a half not being 0",
			"extended_of_real(&1 / &2) * extended_infinity = extended_infinity",
			By(
				halfBetween,
				MulInfinity.At(a.TermAs[ExtendedNonnegReal]("extended_of_real(&1 / &2)")),
				OfRealInjective.At(half, a.TermAs[Real]("&0"))))
		finiteX := a.Have(
			"x is finite: half of it lies below the finite y",
			"x ≠ extended_infinity",
			By(
				finite,
				halfBetween,
				halfOfInfinity,
				scaled.At(half),
				ExtendedLeDef.At(a.TermAs[ExtendedNonnegReal]("extended_of_real(&1 / &2) * x"), y)))
		values := a.Have(
			"on the finite values, c·tx ≤ ty for every c strictly between 0 and 1",
			"∀c:real. &0 < c ∧ c < &1 ⇒ c * extended_to_real(x) ≤ extended_to_real(y)",
			Derive(func(b *Argument) {
				c := b.FixAs[Real]("c")
				between := b.Assume()
				b.Show(
					"the finite value of c·x is c·tx",
					ByArith(
						finite,
						between,
						scaled.At(c),
						ExtendedLeDef.At(b.TermAs[ExtendedNonnegReal]("extended_of_real(c) * x"), y),
						ToRealMul.At(b.TermAs[ExtendedNonnegReal]("extended_of_real(c)"), x),
						ToRealOfReal.At(c)))
			}))
		below := a.Have(
			"tx ≤ ty: were tx above ty, the bound would fail at c = (tx + ty)/(2tx)",
			"extended_to_real(x) ≤ extended_to_real(y)",
			Derive(func(b *Argument) {
				above := b.SupposeNot()
				b.Show(
					"that c lies strictly between 0 and 1, and c·tx = (tx + ty)/2 lies above ty",
					ByArith(
						above,
						values.At(
							b.TermAs[Real]("(extended_to_real(x) + extended_to_real(y)) / (&2 * extended_to_real(x))")),
						field.DivRightMul.Read(real_field.Field).At(
							b.TermAs[Real]("extended_to_real(x) + extended_to_real(y)"),
							b.TermAs[Real]("&2 * extended_to_real(x)")),
						ToRealNonneg.At(y)))
			}))
		a.Show(
			"so x ≤ y",
			By(finiteX, below, ExtendedLeDef.At(x, y)))
	}),
})}
