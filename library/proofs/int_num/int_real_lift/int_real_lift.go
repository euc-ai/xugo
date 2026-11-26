// int_real_lift.go — the chapter: ℤ inherits its algebra from ℝ.
//
// Three parts, marked by banners:
//
// - ℤ's order
// - ℤ's ring laws, inherited
// - An integer's size and its sign, inherited from ℝ's

package int_real_lift

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// ℤ's order
// ---------------------------------------------------------------------------
//
// ℤ's order: the order's own laws, the strict companion, and where the
// order meets negation and the unit. All of it is inherited:
//
// ℤ is carved out of ℝ and its order IS ℝ's restricted, so each law
// here is the image of its ℝ twin under the embedding.

// LessEqRefl — the chapter's floor: every integer bounds itself.
//
// It is what a remainder bound's lower half comes off. The division
// algorithm asks its remainder to be nonnegative, so every `int_div_rem`
// member that exhibits a remainder of &0 discharges that half by citing
// this at &0.
var LessEqRefl = lessEqReflThm{family.Add(registry.ProofEntry{
	Name:  "LessEqRefl",
	Key:   "prop_53f8c713472b4e36",
	Build: family.Lifted("∀x:int. x ≤ x", real_order_ring.LessEqRefl),
})}

// LessEqTrans — transitivity: two bounds in a row are one bound. With
// LessEqRefl above and LessEqAntisym below, this is what makes ℤ's `≤`
// an order at all rather than an arbitrary relation.
var LessEqTrans = lessEqTransThm{family.Add(registry.ProofEntry{
	Name: "LessEqTrans",
	Key:  "prop_1e5ed4b68901b541",
	Build: family.Lifted(Statement{
		Binders: "∀x y z:int.",
		Hypotheses: []string{
			"x ≤ y",
			"y ≤ z",
		},
		Conclusion: "x ≤ z",
	}, real_construction.LessEqTrans),
})}

// LessEqAntisym — antisymmetry, in the form that also gives the
// converse: two integers bounding each other are the same integer, and
// equal ones bound each other.
var LessEqAntisym = lessEqAntisymThm{family.Add(registry.ProofEntry{
	Name:  "LessEqAntisym",
	Key:   "prop_8b757903062fb35a",
	Build: family.Lifted("∀x y:int. x = y ⇔ x ≤ y ∧ y ≤ x", real_construction.LessEqAntisym),
})}

// LessEqTotal — the order is total: of any two integers, one is at or
// below the other. With LessEqRefl above and LessEqTrans and
// LessEqAntisym beside it, this is the last of the four laws that make
// ≤ a total order rather than a partial one.
var LessEqTotal = lessEqTotalThm{family.Add(registry.ProofEntry{
	Name:  "LessEqTotal",
	Key:   "prop_33d6bc879764a380",
	Build: family.Lifted("∀x y:int. x ≤ y ∨ y ≤ x", real_construction.LessEqTotal),
})}

// LessEqOfEq — an equation is a bound: the one shard of
// LessEqAntisym's converse a chain wants when it holds an equation and
// needs a bound.
var LessEqOfEq = lessEqOfEqThm{family.Add(registry.ProofEntry{
	Name: "LessEqOfEq",
	Key:  "prop_b8985050ee42f34",
	Build: family.Lifted(Statement{
		Binders: "∀x y:int.",
		Hypotheses: []string{
			"x = y",
		},
		Conclusion: "x ≤ y",
	}, real_order_ring.LessEqOfEq),
})}

// NotLessThan — the two relations deny each other: x fails to be below
// y exactly when y is at or below x. At ℝ this is not an order theorem
// but the DEFINITION of `<`, and ℤ takes both of its relations from ℝ,
// so it takes the definition along with them.
var NotLessThan = notLessThanThm{family.Add(registry.ProofEntry{
	Name:  "NotLessThan",
	Key:   "prop_869232fafda8fdac",
	Build: family.Lifted("∀x y:int. ¬(x < y) ⇔ y ≤ x", real_order_ring.NotLessThan),
})}

// NotLessEq — the negation of ≤ is the flipped strict order: NotLessThan's twin.
var NotLessEq = notLessEqThm{family.Add(registry.ProofEntry{
	Name:  "NotLessEq",
	Key:   "prop_446fb15e6966e96f",
	Build: family.Lifted("∀x y:int. ¬(x ≤ y) ⇔ y < x", real_order_ring.NotLessEq),
})}

// LessThanTrichotomy — the order is total: two integers are equal, or
// one lies strictly below the other.
var LessThanTrichotomy = lessThanTrichotomyThm{family.Add(registry.ProofEntry{
	Name:  "LessThanTrichotomy",
	Key:   "prop_9ea8646947ad1678",
	Build: family.Lifted("∀x y:int. x = y ∨ x < y ∨ y < x", real_order_ring.LessThanTrichotomy),
})}

// LessThanIrrefl — nothing lies strictly below itself.
// LessThanTrichotomy above offers three cases; this is what keeps the
// first from overlapping the other two, and it is the fact a proof by
// contradiction closes on once it has driven a quantity below its own
// value.
var LessThanIrrefl = lessThanIrreflThm{family.Add(registry.ProofEntry{
	Name:  "LessThanIrrefl",
	Key:   "prop_de5eabebf84cb187",
	Build: family.Lifted("∀x:int. ¬(x < x)", real_order_ring.LessThanIrrefl),
})}

// LessThanSplit — the strict comparison taken apart: below means at or
// below, and not at.
var LessThanSplit = lessThanSplitThm{family.Add(registry.ProofEntry{
	Name:  "LessThanSplit",
	Key:   "prop_3cf93b862bbd6ef4",
	Build: family.Lifted("∀x y:int. x < y ⇔ x ≤ y ∧ x ≠ y", real_order_ring.LessThanSplit),
})}

// LessEqSplit — the non-strict comparison taken apart, which is
// LessThanSplit above read from the other side: at or below means below
// or at. The two carry the same content in the two shapes an argument
// wants it in — one to sharpen a bound into a strict one and a
// disequation, this one to case-split a bound already in hand.
var LessEqSplit = lessEqSplitThm{family.Add(registry.ProofEntry{
	Name:  "LessEqSplit",
	Key:   "prop_73f123c98d4ee372",
	Build: family.Lifted("∀x y:int. x ≤ y ⇔ x < y ∨ x = y", real_order_ring.LessEqSplit),
})}

// NotEqualOfLessThan — one of LessThanSplit's two shards on its own: a
// strict bound separates.
var NotEqualOfLessThan = notEqualOfLessThanThm{family.Add(registry.ProofEntry{
	Name: "NotEqualOfLessThan",
	Key:  "prop_43b62c46ea9ddb3d",
	Build: family.Lifted(Statement{
		Binders: "∀x y:int.",
		Hypotheses: []string{
			"x < y",
		},
		Conclusion: "x ≠ y",
	}, real_order_ring.NotEqualOfLessThan),
})}

// LessEqOfLessThan — a strict bound is in particular a bound.
var LessEqOfLessThan = lessEqOfLessThanThm{family.Add(registry.ProofEntry{
	Name: "LessEqOfLessThan",
	Key:  "prop_ef880d66a3ef9815",
	Build: family.Lifted(Statement{
		Binders: "∀x y:int.",
		Hypotheses: []string{
			"x < y",
		},
		Conclusion: "x ≤ y",
	}, real_order_ring.LessEqOfLessThan),
})}

// LessEqLessThanTrans — mixed transitivity: a non-strict step followed
// by a strict one composes to a strict one.
var LessEqLessThanTrans = lessEqLessThanTransThm{family.Add(registry.ProofEntry{
	Name: "LessEqLessThanTrans",
	Key:  "prop_1978aaff0b369570",
	Build: family.Lifted(Statement{
		Binders: "∀x y z:int.",
		Hypotheses: []string{
			"x ≤ y",
			"y < z",
		},
		Conclusion: "x < z",
	}, real_order_ring.LessEqLessThanTrans),
})}

// LessThanLessEqTrans — the mixed transitivity the other way round, and
// the same content read from the other end: a chain carrying one strict
// step is strict, wherever in it that step sits.
var LessThanLessEqTrans = lessThanLessEqTransThm{family.Add(registry.ProofEntry{
	Name: "LessThanLessEqTrans",
	Key:  "prop_2b2a806693196547",
	Build: family.Lifted(Statement{
		Binders: "∀x y z:int.",
		Hypotheses: []string{
			"x < y",
			"y ≤ z",
		},
		Conclusion: "x < z",
	}, real_order_ring.LessThanLessEqTrans),
})}

// LessThanTrans — two strict steps in a row are one strict step. It is
// the last corner of the transitivity square: with LessEqTrans and the
// two mixed readings above it, every way of composing a ≤ with a < has
// a law, and a chain never has to weaken a link to knit it.
var LessThanTrans = lessThanTransThm{family.Add(registry.ProofEntry{
	Name: "LessThanTrans",
	Key:  "prop_d3f3b8629a43d6a7",
	Build: family.Lifted(Statement{
		Binders: "∀x y z:int.",
		Hypotheses: []string{
			"x < y",
			"y < z",
		},
		Conclusion: "x < z",
	}, real_order_ring.LessThanTrans),
})}

// LessEqAddRight — translation leaves a comparison alone: adding the
// same integer to both sides neither creates nor destroys a bound.
var LessEqAddRight = lessEqAddRightThm{family.Add(registry.ProofEntry{
	Name:  "LessEqAddRight",
	Key:   "prop_91fd637b119fdbbf",
	Build: family.Lifted("∀x y z:int. x + z ≤ y + z ⇔ x ≤ y", real_order_ring.LessEqAddRight),
})}

// LessThanAddRight — LessEqAddRight's strict reading: a common summand
// on the right leaves a strict comparison alone as well.
var LessThanAddRight = lessThanAddRightThm{family.Add(registry.ProofEntry{
	Name:  "LessThanAddRight",
	Key:   "prop_3180576ed9f68e4f",
	Build: family.Lifted("∀x y z:int. x + z < y + z ⇔ x < y", real_order_ring.LessThanAddRight),
})}

// LessEqAddLeft — the same with the common summand on the left.
var LessEqAddLeft = lessEqAddLeftThm{family.Add(registry.ProofEntry{
	Name:  "LessEqAddLeft",
	Key:   "prop_8de1039a979fdcb4",
	Build: family.Lifted("∀x y z:int. x + y ≤ x + z ⇔ y ≤ z", real_order_ring.LessEqAddLeft),
})}

// LessThanAddLeft — the strict comparison is translation-invariant too,
// here with the common summand on the left.
var LessThanAddLeft = lessThanAddLeftThm{family.Add(registry.ProofEntry{
	Name:  "LessThanAddLeft",
	Key:   "prop_9191506fdc49eb36",
	Build: family.Lifted("∀x y z:int. x + y < x + z ⇔ y < z", real_order_ring.LessThanAddLeft),
})}

// LessThanAddLeftImp — LessThanAddLeft's one-way reading: the
// direction a chain actually consumes, stated without the return trip.
var LessThanAddLeftImp = lessThanAddLeftImpThm{family.Add(registry.ProofEntry{
	Name: "LessThanAddLeftImp",
	Key:  "prop_cdb95a0332a91562",
	Build: family.Lifted(Statement{
		Binders: "∀x y z:int.",
		Hypotheses: []string{
			"y < z",
		},
		Conclusion: "x + y < x + z",
	}, real_order_ring.LessThanAddLeftImp),
})}

// LessEqAddLeftImp — LessThanAddLeftImp's non-strict companion, and
// LessEqAddLeft's one-way reading: the direction a chain uses when it is
// translating a bound it already holds rather than recovering one from a
// translated pair.
var LessEqAddLeftImp = lessEqAddLeftImpThm{family.Add(registry.ProofEntry{
	Name: "LessEqAddLeftImp",
	Key:  "prop_690b4c4c265becf6",
	Build: family.Lifted(Statement{
		Binders: "∀x y z:int.",
		Hypotheses: []string{
			"y ≤ z",
		},
		Conclusion: "x + y ≤ x + z",
	}, real_construction.LessEqAddLeftImp),
})}

// LessEqSelfAddRight — a sum stays at or above its first summand
// exactly when the other summand is nonnegative.
var LessEqSelfAddRight = lessEqSelfAddRightThm{family.Add(registry.ProofEntry{
	Name:  "LessEqSelfAddRight",
	Key:   "prop_66a7d5df4a77f26b",
	Build: family.Lifted("∀x y:int. x ≤ x + y ⇔ &0 ≤ y", real_order_ring.LessEqSelfAddRight),
})}

// LessEqSelfAddLeft — the same with the summands exchanged.
var LessEqSelfAddLeft = lessEqSelfAddLeftThm{family.Add(registry.ProofEntry{
	Name:  "LessEqSelfAddLeft",
	Key:   "prop_a8b59b6f89fef56a",
	Build: family.Lifted("∀x y:int. y ≤ x + y ⇔ &0 ≤ x", real_order_ring.LessEqSelfAddLeft),
})}

// LessThanSelfAddRight — a sum strictly beats its first summand exactly
// when the other summand is strictly positive.
var LessThanSelfAddRight = lessThanSelfAddRightThm{family.Add(registry.ProofEntry{
	Name:  "LessThanSelfAddRight",
	Key:   "prop_58cf0a3952af2b74",
	Build: family.Lifted("∀x y:int. x < x + y ⇔ &0 < y", real_order_ring.LessThanSelfAddRight),
})}

// LessEqAdd2 — two bounds add: sums compare as their summands do.
var LessEqAdd2 = lessEqAdd2Thm{family.Add(registry.ProofEntry{
	Name: "LessEqAdd2",
	Key:  "prop_3760215ec31a2472",
	Build: family.Lifted(Statement{
		Binders: "∀w x y z:int.",
		Hypotheses: []string{
			"w ≤ x",
			"y ≤ z",
		},
		Conclusion: "w + y ≤ x + z",
	}, real_order_ring.LessEqAdd2),
})}

// LessThanAdd2 — two strict bounds add to a strict one.
var LessThanAdd2 = lessThanAdd2Thm{family.Add(registry.ProofEntry{
	Name: "LessThanAdd2",
	Key:  "prop_6a786ae8a88e2fc4",
	Build: family.Lifted(Statement{
		Binders: "∀w x y z:int.",
		Hypotheses: []string{
			"w < x",
			"y < z",
		},
		Conclusion: "w + y < x + z",
	}, real_order_ring.LessThanAdd2),
})}

// LessEqLessThanAdd2 — a bound and a strict bound add to a strict one:
// a single strict summand makes the sum strict.
var LessEqLessThanAdd2 = lessEqLessThanAdd2Thm{family.Add(registry.ProofEntry{
	Name: "LessEqLessThanAdd2",
	Key:  "prop_64e5dfe370c2fd07",
	Build: family.Lifted(Statement{
		Binders: "∀w x y z:int.",
		Hypotheses: []string{
			"w ≤ x",
			"y < z",
		},
		Conclusion: "w + y < x + z",
	}, real_order_ring.LessEqLessThanAdd2),
})}

// LessThanLessEqAdd2 — the same with the strict summand first.
var LessThanLessEqAdd2 = lessThanLessEqAdd2Thm{family.Add(registry.ProofEntry{
	Name: "LessThanLessEqAdd2",
	Key:  "prop_8e16428db4872674",
	Build: family.Lifted(Statement{
		Binders: "∀w x y z:int.",
		Hypotheses: []string{
			"w < x",
			"y ≤ z",
		},
		Conclusion: "w + y < x + z",
	}, real_order_ring.LessThanLessEqAdd2),
})}

// AddNonneg — nonnegative integers add to a nonnegative one: LessEqAdd2
// with both lower bounds at zero.
var AddNonneg = addNonnegThm{family.Add(registry.ProofEntry{
	Name: "AddNonneg",
	Key:  "prop_6a2a6dd6fe2241ba",
	Build: family.Lifted(Statement{
		Binders: "∀x y:int.",
		Hypotheses: []string{
			"&0 ≤ x",
			"&0 ≤ y",
		},
		Conclusion: "&0 ≤ x + y",
	}, real_order_ring.AddNonneg),
})}

// NegNonneg — negation exchanges the two halves of ℤ: an integer is
// nonpositive exactly when its negation is nonnegative.
var NegNonneg = negNonnegThm{family.Add(registry.ProofEntry{
	Name: "NegNonneg",
	Key:  "prop_d2b8aadb2ff44d29",
	Build: family.Lifted(
		"∀x:int. x ≤ &0 ⇔ &0 ≤ int_neg(x)", real_order_ring.NegNonnegativeIffNonpositive),
})}

// NegNonpos — NegNonneg read the other way round: an integer is
// nonnegative exactly when its negation is nonpositive. The pair is what
// lets an argument carry a bound across a sign change in whichever
// direction it happens to be holding it.
var NegNonpos = negNonposThm{family.Add(registry.ProofEntry{
	Name: "NegNonpos",
	Key:  "prop_8321ba44dff32e64",
	Build: family.Lifted(
		"∀x:int. &0 ≤ x ⇔ int_neg(x) ≤ &0", real_order_ring.NegNonpositiveIffNonnegative),
})}

// NegPositiveIffNegative — NegNonneg's strict companion: a negation is
// positive exactly when the integer is negative.
var NegPositiveIffNegative = negPositiveIffNegativeThm{family.Add(registry.ProofEntry{
	Name:  "NegPositiveIffNegative",
	Key:   "prop_5b228c57f84fa34",
	Build: family.Lifted("∀x:int. &0 < int_neg(x) ⇔ x < &0", real_order_ring.NegPositiveIffNegative),
})}

// NegNegativeIffPositive — NegPositiveIffNegative's mirror, and the
// strict companion of NegNonpos above: a negation is negative exactly
// when the integer is positive.
var NegNegativeIffPositive = negNegativeIffPositiveThm{family.Add(registry.ProofEntry{
	Name:  "NegNegativeIffPositive",
	Key:   "prop_7dc2d07bbea62c1e",
	Build: family.Lifted("∀x:int. int_neg(x) < &0 ⇔ &0 < x", real_order_ring.NegNegativeIffPositive),
})}

// LessEqNeg2 — negation reverses the order, and reversibly: two
// integers compare exactly as their negations compare backwards.
// NegNonneg above is its instance at x = &0, once NegZero has turned
// `int_neg(&0)` back into `&0`.
var LessEqNeg2 = lessEqNeg2Thm{family.Add(registry.ProofEntry{
	Name:  "LessEqNeg2",
	Key:   "prop_2ca8e1cb4f191eea",
	Build: family.Lifted("∀x y:int. int_neg(x) ≤ int_neg(y) ⇔ y ≤ x", real_order_ring.LessEqNeg2),
})}

// LessThanNeg2 — LessEqNeg2's strict twin: negation reverses the strict
// order too, and reversibly.
var LessThanNeg2 = lessThanNeg2Thm{family.Add(registry.ProofEntry{
	Name:  "LessThanNeg2",
	Key:   "prop_a5e3650e86d2d6e0",
	Build: family.Lifted("∀x y:int. int_neg(x) < int_neg(y) ⇔ y < x", real_order_ring.LessThanNeg2),
})}

// LessThanNegTotal — trichotomy through negation: an integer is zero,
// positive, or positive after a sign change.
var LessThanNegTotal = lessThanNegTotalThm{family.Add(registry.ProofEntry{
	Name:  "LessThanNegTotal",
	Key:   "prop_d1b4b0d37e716631",
	Build: family.Lifted("∀x:int. x = &0 ∨ &0 < x ∨ &0 < int_neg(x)", real_order_ring.LessThanNegTotal),
})}

// LessEqNegTotal — every integer has a nonnegative side: either it is
// nonnegative or its negation is. LessThanNegTotal above says the same
// with the zero case named separately, which the non-strict reading
// absorbs into both alternatives.
var LessEqNegTotal = lessEqNegTotalThm{family.Add(registry.ProofEntry{
	Name:  "LessEqNegTotal",
	Key:   "prop_672d387c05761d36",
	Build: family.Lifted("∀x:int. &0 ≤ x ∨ &0 ≤ int_neg(x)", real_order_ring.LessEqNegTotal),
})}

// LessEqMul — nonnegative integers multiply to a nonnegative one: the
// order's compatibility with the product, in its most basic form.
var LessEqMul = lessEqMulThm{family.Add(registry.ProofEntry{
	Name: "LessEqMul",
	Key:  "prop_cd53751639545d34",
	Build: family.Lifted(Statement{
		Binders: "∀x y:int.",
		Hypotheses: []string{
			"&0 ≤ x",
			"&0 ≤ y",
		},
		Conclusion: "&0 ≤ x * y",
	}, real_construction.LessEqMul),
})}

// MulPos — and positive ones to a positive one.
var MulPos = mulPosThm{family.Add(registry.ProofEntry{
	Name: "MulPos",
	Key:  "prop_a5db914c6dd69895",
	Build: family.Lifted(Statement{
		Binders: "∀x y:int.",
		Hypotheses: []string{
			"&0 < x",
			"&0 < y",
		},
		Conclusion: "&0 < x * y",
	}, real_order_ring.MulPos),
})}

// LessEqMulLeft — a nonnegative factor preserves a comparison. This is
// how a bound on a factor becomes a bound on a product, and the
// nonnegativity of the scaling factor is what the hypothesis is for:
// scaling by a negative one would reverse the comparison instead.
var LessEqMulLeft = lessEqMulLeftThm{family.Add(registry.ProofEntry{
	Name: "LessEqMulLeft",
	Key:  "prop_21c8e29e62cb71b5",
	Build: family.Lifted(Statement{
		Binders: "∀x y z:int.",
		Hypotheses: []string{
			"&0 ≤ x",
			"y ≤ z",
		},
		Conclusion: "x * y ≤ x * z",
	}, real_order_ring.LessEqMulLeft),
})}

// LessEqMulRight — LessEqMulLeft's mirror: the nonnegative factor
// scales from the right.
var LessEqMulRight = lessEqMulRightThm{family.Add(registry.ProofEntry{
	Name: "LessEqMulRight",
	Key:  "prop_2665e5c85c6d568f",
	Build: family.Lifted(Statement{
		Binders: "∀x y z:int.",
		Hypotheses: []string{
			"x ≤ y",
			"&0 ≤ z",
		},
		Conclusion: "x * z ≤ y * z",
	}, real_order_ring.LessEqMulRight),
})}

// LessThanMulLeft — a positive factor preserves a strict comparison:
// LessEqMulLeft's strict form, and strictness is what asks the factor
// to be positive rather than merely nonnegative.
var LessThanMulLeft = lessThanMulLeftThm{family.Add(registry.ProofEntry{
	Name: "LessThanMulLeft",
	Key:  "prop_f63805dd49924447",
	Build: family.Lifted(Statement{
		Binders: "∀x y z:int.",
		Hypotheses: []string{
			"&0 < x",
			"y < z",
		},
		Conclusion: "x * y < x * z",
	}, real_order_ring.LessThanMulLeft),
})}

// LessThanMulRight — LessThanMulLeft's mirror, with the positive factor
// on the right, and the fourth corner of the group LessEqMulLeft,
// LessEqMulRight and LessThanMulLeft above already hold: monotonicity
// of the product in either slot, strictly and weakly. Stated on both
// sides for MulRightZero's reason — a scaling step reached through the
// other side would carry a commutation premise every time.
var LessThanMulRight = lessThanMulRightThm{family.Add(registry.ProofEntry{
	Name: "LessThanMulRight",
	Key:  "prop_c1dd19584bf53b95",
	Build: family.Lifted(Statement{
		Binders: "∀x y z:int.",
		Hypotheses: []string{
			"x < y",
			"&0 < z",
		},
		Conclusion: "x * z < y * z",
	}, real_order_ring.LessThanMulRight),
})}

// LessThanMulRightEq — a positive right factor can be put on or taken
// off both sides of a strict comparison: scaling by it changes nothing
// either way.
var LessThanMulRightEq = lessThanMulRightEqThm{family.Add(registry.ProofEntry{
	Name: "LessThanMulRightEq",
	Key:  "prop_aa4572783e9789a1",
	Build: family.Lifted(Statement{
		Binders: "∀x y z:int.",
		Hypotheses: []string{
			"&0 < z",
		},
		Conclusion: "x * z < y * z ⇔ x < y",
	}, real_order_ring.LessThanMulRightEq),
})}

// LessEqMulRightEq — LessThanMulRightEq's non-strict twin: a positive
// right factor goes onto a bound and comes off it freely. The ⇔ is what
// makes it a cancellation law as well as a scaling one, which is why the
// chapter states it rather than the implication it is usually used in.
var LessEqMulRightEq = lessEqMulRightEqThm{family.Add(registry.ProofEntry{
	Name: "LessEqMulRightEq",
	Key:  "prop_b8e2c680d1371543",
	Build: family.Lifted(Statement{
		Binders: "∀x y z:int.",
		Hypotheses: []string{
			"&0 < z",
		},
		Conclusion: "x * z ≤ y * z ⇔ x ≤ y",
	}, real_order_ring.LessEqMulRightEq),
})}

// LessEqSubAddLeft — the order half of the add/subtract adjunction: a
// subtrahend crosses the bound and becomes a summand on the other side.
var LessEqSubAddLeft = lessEqSubAddLeftThm{family.Add(registry.ProofEntry{
	Name:  "LessEqSubAddLeft",
	Key:   "prop_8dce419c058be71b",
	Build: family.Lifted("∀x y z:int. x ≤ y - z ⇔ x + z ≤ y", real_order_ring.LessEqSubAddLeft),
})}

// LessEqSubAddRight — the same adjunction read from the difference's
// side: the subtrahend crosses over to become a summand of the bound.
var LessEqSubAddRight = lessEqSubAddRightThm{family.Add(registry.ProofEntry{
	Name:  "LessEqSubAddRight",
	Key:   "prop_c9aafb9d86b8c54e",
	Build: family.Lifted("∀x y z:int. x - y ≤ z ⇔ x ≤ z + y", real_order_ring.LessEqSubAddRight),
})}

// LessThanSubAddRight — the strict adjunction, read from the
// difference's side.
var LessThanSubAddRight = lessThanSubAddRightThm{family.Add(registry.ProofEntry{
	Name:  "LessThanSubAddRight",
	Key:   "prop_fb1faa7a2a37e9a1",
	Build: family.Lifted("∀x y z:int. x - y < z ⇔ x < z + y", real_order_ring.LessThanSubAddRight),
})}

// LessThanSubAddLeft — the strict adjunction the other way round: a
// summand crosses the bound and becomes a subtrahend.
var LessThanSubAddLeft = lessThanSubAddLeftThm{family.Add(registry.ProofEntry{
	Name:  "LessThanSubAddLeft",
	Key:   "prop_796422d4e35666db",
	Build: family.Lifted("∀x y z:int. x + z < y ⇔ x < y - z", real_order_ring.LessThanSubAddLeft),
})}

// SubNonneg — a difference is nonnegative exactly when it is taken in
// the order the two integers stand: asking how x and y compare IS
// asking x - y its sign.
var SubNonneg = subNonnegThm{family.Add(registry.ProofEntry{
	Name:  "SubNonneg",
	Key:   "prop_54ee884a02ae81c",
	Build: family.Lifted("∀x y:int. &0 ≤ x - y ⇔ y ≤ x", real_order_ring.SubNonneg),
})}

// SubPos — SubNonneg's strict twin: a difference is positive exactly
// when it is taken in the increasing direction.
var SubPos = subPosThm{family.Add(registry.ProofEntry{
	Name:  "SubPos",
	Key:   "prop_698b13515db26da9",
	Build: family.Lifted("∀x y:int. &0 < x - y ⇔ y < x", real_order_ring.SubPos),
})}

// The two facts about the unit spell the coercion out where the rest of
// the chapter writes `&`. `&` takes its target type from the term
// around it, and a comparison of two literals supplies none: left as
// `&0 < &1` these would be statements about ℝ.

// ZeroLessEqOne — the unit is nonnegative. The non-strict companion of
// ZeroLessThanOne below, and a separate member because a bound wanted
// non-strictly is a different premise from a strict one.
var ZeroLessEqOne = zeroLessEqOneThm{family.Add(registry.ProofEntry{
	Name:  "ZeroLessEqOne",
	Key:   "prop_8ea56da548cbd386",
	Build: family.Lifted("0 ≤ int_of_num(1)", real_order_ring.ZeroLessEqOne),
})}

// ZeroLessThanOne — the unit is strictly positive: &0 and &1 are
// different integers, and this says which way round they stand.
var ZeroLessThanOne = zeroLessThanOneThm{family.Add(registry.ProofEntry{
	Name:  "ZeroLessThanOne",
	Key:   "prop_56f0f7cda96d4ab",
	Build: family.Lifted("0 < int_of_num(1)", real_order_ring.ZeroLessThanOne),
})}

// ---------------------------------------------------------------------------
// ℤ's ring laws, inherited
// ---------------------------------------------------------------------------
//
// ℤ's ring laws, inherited: each is the image of its ℝ twin under the
// embedding, one IntOfRealDerive step.

// AddLeftIdentity — zero is a left identity for +.
var AddLeftIdentity = addLeftIdentityThm{family.Add(registry.ProofEntry{
	Name:  "AddLeftIdentity",
	Key:   "prop_d1f22169b908f179",
	Build: family.Lifted("∀x:int. &0 + x = x", real_construction.AddLeftId),
})}

// AddRightIdentity — zero is a right identity for +.
var AddRightIdentity = addRightIdentityThm{family.Add(registry.ProofEntry{
	Name:  "AddRightIdentity",
	Key:   "prop_c1509cc36354ecd8",
	Build: family.Lifted("∀x:int. x + &0 = x", real_ring.AddRightId),
})}

// AddLeftInverse — every integer is cancelled by its negation on the
// left.
var AddLeftInverse = addLeftInverseThm{family.Add(registry.ProofEntry{
	Name:  "AddLeftInverse",
	Key:   "prop_3792ed79f57e29f",
	Build: family.Lifted("∀x:int. int_neg(x) + x = &0", real_construction.AddLeftInv),
})}

// SubAddNeg — subtraction is addition of the negation: ℝ's definition
// of its subtraction, lifted. It is the ring's subtraction axiom at ℤ.
var SubAddNeg = subAddNegThm{family.Add(registry.ProofEntry{
	Name:  "SubAddNeg",
	Key:   "prop_50328baadcefa16a",
	Build: family.Lifted("∀x y:int. int_sub(x, y) = x + int_neg(y)", real_ring.RealSubDef),
})}

// AddRightInverse — and on the right.
var AddRightInverse = addRightInverseThm{family.Add(registry.ProofEntry{
	Name:  "AddRightInverse",
	Key:   "prop_f1e6b1aad4c8c26e",
	Build: family.Lifted("∀x:int. x + int_neg(x) = &0", real_ring.AddRightInv),
})}

// AddSym — addition is commutative.
var AddSym = addSymThm{family.Add(registry.ProofEntry{
	Name:  "AddSym",
	Key:   "prop_103c48fef8645821",
	Build: family.Lifted("∀x y:int. x + y = y + x", real_construction.AddSym),
})}

// AddAssoc — addition is associative.
var AddAssoc = addAssocThm{family.Add(registry.ProofEntry{
	Name:  "AddAssoc",
	Key:   "prop_64f1ef89f2049fbd",
	Build: family.Lifted("∀x y z:int. x + (y + z) = x + y + z", real_construction.AddAssoc),
})}

// MulLeftZero — zero annihilates on the left.
var MulLeftZero = mulLeftZeroThm{family.Add(registry.ProofEntry{
	Name:  "MulLeftZero",
	Key:   "prop_705f9832684537e6",
	Build: family.Lifted("∀x:int. &0 * x = &0", real_ring.MulLeftZero),
})}

// MulRightZero — and on the right. The two are separate members rather
// than one plus commutativity because a consumer that has the product
// the wrong way round otherwise pays for the flip: reaching this fact
// through MulLeftZero costs a commutation premise at every site, and
// the sites that want it are zero-divisor branches, where the whole
// argument is one line.
var MulRightZero = mulRightZeroThm{family.Add(registry.ProofEntry{
	Name:  "MulRightZero",
	Key:   "prop_af37d65569dbc6ef",
	Build: family.Lifted("∀x:int. x * &0 = &0", real_ring.MulRightZero),
})}

// MulLeftIdentity — one is a left identity for ·.
var MulLeftIdentity = mulLeftIdentityThm{family.Add(registry.ProofEntry{
	Name:  "MulLeftIdentity",
	Key:   "prop_ce8d05d5166bf5b5",
	Build: family.Lifted("∀x:int. &1 * x = x", real_construction.MulLeftId),
})}

// MulRightIdentity — one is a right identity for ·.
var MulRightIdentity = mulRightIdentityThm{family.Add(registry.ProofEntry{
	Name:  "MulRightIdentity",
	Key:   "prop_2e01ce69795cdc9d",
	Build: family.Lifted("∀x:int. x * &1 = x", real_ring.MulRightId),
})}

// MulEqZero — ℤ has no zero divisors: a product vanishes only when one
// of its factors does. Right to left it is the pair of zero laws above;
// left to right it is the direction that carries information, a
// nonvanishing product telling you both its factors are nonzero.
var MulEqZero = mulEqZeroThm{family.Add(registry.ProofEntry{
	Name:  "MulEqZero",
	Key:   "prop_bb8365e5ca388960",
	Build: family.Lifted("∀x y:int. x * y = &0 ⇔ x = &0 ∨ y = &0", real_ring.MulEqZero),
})}

// MulLeftCancel — a common factor can be cancelled off both sides of an
// equation, and the disjunct is what makes that unconditional: at x = &0
// the two products agree whatever stands beside them, so cancellation
// is the OTHER case rather than a law with a side condition.
var MulLeftCancel = mulLeftCancelThm{family.Add(registry.ProofEntry{
	Name:  "MulLeftCancel",
	Key:   "prop_b5854f48f605fd5b",
	Build: family.Lifted("∀x y z:int. x * y = x * z ⇔ x = &0 ∨ y = z", real_ring.MulLeftCancel),
})}

// MulRightCancel — MulLeftCancel's mirror: a common factor cancels off
// the right of an equation exactly as it does off the left, and in both
// the factor's own vanishing is the one alternative.
var MulRightCancel = mulRightCancelThm{family.Add(registry.ProofEntry{
	Name:  "MulRightCancel",
	Key:   "prop_eac942bd7c6ba13e",
	Build: family.Lifted("∀x y z:int. y * x = z * x ⇔ x = &0 ∨ y = z", real_ring.MulRightCancel),
})}

// MulSym — multiplication is commutative.
var MulSym = mulSymThm{family.Add(registry.ProofEntry{
	Name:  "MulSym",
	Key:   "prop_a99872d586118b6b",
	Build: family.Lifted("∀x y:int. x * y = y * x", real_construction.MulSym),
})}

// MulAssoc — multiplication is associative.
var MulAssoc = mulAssocThm{family.Add(registry.ProofEntry{
	Name:  "MulAssoc",
	Key:   "prop_5ad5ed2c448db7dc",
	Build: family.Lifted("∀x y z:int. x * (y * z) = x * y * z", real_construction.MulAssoc),
})}

// LeftDistrib — multiplication distributes over addition from the left.
// With MulAssoc, this is the pair that carries the Bézout combination
// step for both gcd chapters.
var LeftDistrib = leftDistribThm{family.Add(registry.ProofEntry{
	Name:  "LeftDistrib",
	Key:   "prop_ac36fa87996c3882",
	Build: family.Lifted("∀x y z:int. x * (y + z) = x * y + x * z", real_construction.LeftDistrib),
})}

// RightDistrib — multiplication distributes over addition from the
// right.
var RightDistrib = rightDistribThm{family.Add(registry.ProofEntry{
	Name:  "RightDistrib",
	Key:   "prop_2491f8c0720e906b",
	Build: family.Lifted("∀x y z:int. (x + y) * z = x * z + y * z", real_ring.RightDistrib),
})}

// SubLeftDistrib — multiplication distributes over subtraction from the
// left.
var SubLeftDistrib = subLeftDistribThm{family.Add(registry.ProofEntry{
	Name:  "SubLeftDistrib",
	Key:   "prop_dc18c753330ba042",
	Build: family.Lifted("∀x y z:int. x * (y - z) = x * y - x * z", real_ring.SubLeftDistrib),
})}

// SubRightDistrib — and from the right.
var SubRightDistrib = subRightDistribThm{family.Add(registry.ProofEntry{
	Name:  "SubRightDistrib",
	Key:   "prop_eb9ee4b2c12944c5",
	Build: family.Lifted("∀x y z:int. (x - y) * z = x * z - y * z", real_ring.SubRightDistrib),
})}

// SubRefl — an integer differs from itself by nothing.
var SubRefl = subReflThm{family.Add(registry.ProofEntry{
	Name:  "SubRefl",
	Key:   "prop_e4a74d10f634dbc9",
	Build: family.Lifted("∀x:int. x - x = &0", real_ring.SubRefl),
})}

// SubEqZero — and only from itself, so a vanishing difference is
// equality. This is what lets an equation between integers be handled
// as a statement about one quantity.
var SubEqZero = subEqZeroThm{family.Add(registry.ProofEntry{
	Name:  "SubEqZero",
	Key:   "prop_140057796c3485b0",
	Build: family.Lifted("∀x y:int. x - y = &0 ⇔ x = y", real_ring.SubEqZero),
})}

// SubTriangle — consecutive differences telescope: the point they meet
// at cancels itself.
var SubTriangle = subTriangleThm{family.Add(registry.ProofEntry{
	Name:  "SubTriangle",
	Key:   "prop_1092f8260e27c991",
	Build: family.Lifted("∀a b c:int. (a - b) + (b - c) = a - c", real_ring.SubTriangle),
})}

// SubAddPairwise — a difference of sums is the sum of the differences,
// each minuend paired with its own subtrahend.
var SubAddPairwise = subAddPairwiseThm{family.Add(registry.ProofEntry{
	Name: "SubAddPairwise",
	Key:  "prop_6b422e044d14845e",
	Build: family.Lifted(
		"∀a b c d:int. (a + b) - (c + d) = (a - c) + (b - d)", real_ring.SubAddPairwise),
})}

// SubAddRight — subtracting an integer and adding it back is the
// identity: the two translations undo each other. Named for the side
// the restored summand takes: here `+ y` stands on the RIGHT.
var SubAddRight = subAddRightThm{family.Add(registry.ProofEntry{
	Name:  "SubAddRight",
	Key:   "prop_d1e2636f09c8797b",
	Build: family.Lifted("∀x y:int. x - y + y = x", real_ring.SubAddRight),
})}

// SubAddLeft — the same cancellation with the restored summand on the
// LEFT (`y + …`), the difference moving to the right of the sum.
var SubAddLeft = subAddLeftThm{family.Add(registry.ProofEntry{
	Name:  "SubAddLeft",
	Key:   "prop_aac006b1b6baacdc",
	Build: family.Lifted("∀x y:int. y + (x - y) = x", real_ring.SubAddLeft),
})}

// SubRightZero — subtracting nothing changes nothing: zero is a right
// identity for the difference. Its mirror SubLeftZero below is not an
// identity at all — zero on the LEFT reflects its argument rather than
// fixing it — and the pair is where the difference stops behaving
// symmetrically in its two slots.
var SubRightZero = subRightZeroThm{family.Add(registry.ProofEntry{
	Name:  "SubRightZero",
	Key:   "prop_e01b15192084c1c6",
	Build: family.Lifted("∀x:int. x - &0 = x", real_ring.SubRightZero),
})}

// SubLeftZero — subtracting from zero is negation.
var SubLeftZero = subLeftZeroThm{family.Add(registry.ProofEntry{
	Name:  "SubLeftZero",
	Key:   "prop_fcd9f93cb5ca1ad0",
	Build: family.Lifted("∀x:int. &0 - x = int_neg(x)", real_ring.SubLeftZero),
})}

// SubRightNeg — subtracting a negation is adding.
var SubRightNeg = subRightNegThm{family.Add(registry.ProofEntry{
	Name:  "SubRightNeg",
	Key:   "prop_42cd103442e591df",
	Build: family.Lifted("∀x y:int. x - int_neg(y) = x + y", real_ring.SubRightNeg),
})}

// NegSub — negating a difference turns it around.
var NegSub = negSubThm{family.Add(registry.ProofEntry{
	Name:  "NegSub",
	Key:   "prop_485097985d106104",
	Build: family.Lifted("∀x y:int. int_neg(x - y) = y - x", real_ring.NegSub),
})}

// SubLeftNeg — subtracting from a negation is negating the sum.
var SubLeftNeg = subLeftNegThm{family.Add(registry.ProofEntry{
	Name:  "SubLeftNeg",
	Key:   "prop_a4464d2dbac58bcf",
	Build: family.Lifted("∀x y:int. int_neg(x) - y = int_neg(x + y)", real_ring.SubLeftNeg),
})}

// EqSubRightAdd — half of the add/subtract adjunction: a difference may
// be moved across an equation and become a sum. ℤ is where that holds
// unconditionally, which is what a ℕ statement about truncated
// subtraction crosses the embedding to borrow.
var EqSubRightAdd = eqSubRightAddThm{family.Add(registry.ProofEntry{
	Name:  "EqSubRightAdd",
	Key:   "prop_8fbd0a72359a704a",
	Build: family.Lifted("∀x y z:int. x - y = z ⇔ x = z + y", real_ring.EqSubRightAdd),
})}

// NegZero — zero is its own negation, so it is the one integer lying in
// both halves NegNonneg exchanges.
var NegZero = negZeroThm{family.Add(registry.ProofEntry{
	Name:  "NegZero",
	Key:   "prop_34dfc93fe4bd2ff4",
	Build: family.Lifted("int_neg(&0) = &0", real_ring.NegZero),
})}

// NegNeg — negation is an involution: an integer is the negation of its
// own negation. That is additive inverses being unique — x is an
// inverse of int_neg(x), and so is int_neg(int_neg(x)).
var NegNeg = negNegThm{family.Add(registry.ProofEntry{
	Name:  "NegNeg",
	Key:   "prop_3a7a9f8c8abdc379",
	Build: family.Lifted("∀x:int. int_neg(int_neg(x)) = x", real_ring.NegNeg),
})}

// NegAdd — negation distributes over a sum. With NegNeg above and NegSub
// among the subtraction laws, it is what lets a sign be pushed through an
// expression rather than carried alongside it.
var NegAdd = negAddThm{family.Add(registry.ProofEntry{
	Name:  "NegAdd",
	Key:   "prop_e34c8c43568bbc77",
	Build: family.Lifted("∀x y:int. int_neg(x + y) = int_neg(x) + int_neg(y)", real_ring.NegAdd),
})}

// NegLeftUnique — additive inverses are unique: the one integer that
// cancels y is its negation.
var NegLeftUnique = negLeftUniqueThm{family.Add(registry.ProofEntry{
	Name:  "NegLeftUnique",
	Key:   "prop_e222a296902ffa82",
	Build: family.Lifted("∀x y:int. x + y = &0 ⇔ x = int_neg(y)", real_ring.NegLeftUnique),
})}

// MulLeftNeg — a sign on a factor is a sign on the product: negation
// slides out through multiplication.
var MulLeftNeg = mulLeftNegThm{family.Add(registry.ProofEntry{
	Name:  "MulLeftNeg",
	Key:   "prop_c6a1bb5dd7475f2a",
	Build: family.Lifted("∀x y:int. int_neg(x) * y = int_neg(x * y)", real_ring.MulLeftNeg),
})}

// MulRightNeg — MulLeftNeg's mirror: the sign slides out of the right
// factor too.
var MulRightNeg = mulRightNegThm{family.Add(registry.ProofEntry{
	Name:  "MulRightNeg",
	Key:   "prop_39e17f0ccc72b66d",
	Build: family.Lifted("∀x y:int. x * int_neg(y) = int_neg(x * y)", real_ring.MulRightNeg),
})}

// MulNegNeg — two signs in one product cancel: the sign slides out of
// each factor in turn, and the double negation left outside is no sign
// at all.
var MulNegNeg = mulNegNegThm{family.Add(registry.ProofEntry{
	Name:  "MulNegNeg",
	Key:   "prop_7b9cf496679ff6a5",
	Build: family.Lifted("∀x y:int. int_neg(x) * int_neg(y) = x * y", real_ring.MulNegNeg),
})}

// ---------------------------------------------------------------------------
// An integer's size and its sign, inherited from ℝ's
// ---------------------------------------------------------------------------
//
// int_abs and int_sgn are both defined by transport along real_of_int,
// so each law here is the image of its ℝ twin, one IntOfRealDerive step.
//
// Size and sign share a file because they are the two things an
// integer splits into, and SgnMulSelfIsAbs at the end is where the
// split is stated: multiplying by the direction is exactly what turns
// a value into its size.
//
// The size laws come first — the unconditional bounds, then
// multiplicativity, then the criteria for when the size vanishes,
// leaves its argument alone, or forgets a sign, then the two
// equivalences that read a bound on a size back as a bracket around
// the value. The sign closes the file.

// AbsNonneg — absolute values are nonnegative.
var AbsNonneg = absNonnegThm{family.Add(registry.ProofEntry{
	Name:  "AbsNonneg",
	Key:   "prop_b30a689b83e4b91",
	Build: family.Lifted("∀x:int. &0 ≤ |x|", real_sgn_abs.AbsNonneg),
})}

// AbsDominates — no integer exceeds its own size. This and AbsNonneg
// above it are the two lower bounds the absolute value carries
// unconditionally, one against &0 and one against the argument itself,
// and it is the second that closes an argument by contradiction: a
// quantity that would have to be strictly larger than its own size has
// nowhere to be.
var AbsDominates = absDominatesThm{family.Add(registry.ProofEntry{
	Name:  "AbsDominates",
	Key:   "prop_53fcfa0bd6451228",
	Build: family.Lifted("∀x:int. x ≤ |x|", real_sgn_abs.AbsDominates),
})}

// AbsMul — the absolute value is multiplicative.
var AbsMul = absMulThm{family.Add(registry.ProofEntry{
	Name:  "AbsMul",
	Key:   "prop_21b81ac93a183150",
	Build: family.Lifted("∀x y:int. |x * y| = |x| * |y|", real_sgn_abs.AbsMul),
})}

// AbsTriangle — the absolute value is subadditive: the size of a sum
// is at most the sum of the sizes. The estimate every bound on a sum
// of integers goes through.
var AbsTriangle = absTriangleThm{family.Add(registry.ProofEntry{
	Name:  "AbsTriangle",
	Key:   "prop_4849d2084658acf5",
	Build: family.Lifted("∀x y:int. |x + y| ≤ |x| + |y|", real_sgn_abs.AbsTriangle),
})}

// AbsPosIffNonzero — being nonzero and having a size at all are the same
// condition. This is the chapter's bridge from "nonzero" to "has a size
// for something to fall below", which is the hypothesis every
// division-algorithm remainder bound opens with.
//
// Not `AbsPositive`: `AbsNonneg` above it is the unconditional size
// bound, so the two names would read as the nonstrict/strict pair of one
// fact rather than as an unconditional law and this conditional one —
// which is the reading `AbsNonneg` was itself renamed away from.
var AbsPosIffNonzero = absPosIffNonzeroThm{family.Add(registry.ProofEntry{
	Name:  "AbsPosIffNonzero",
	Key:   "prop_39e931df8d77969e",
	Build: family.Lifted("∀x:int. x ≠ &0 ⇔ &0 < |x|", real_sgn_abs.AbsPosIffNonzero),
})}

// AbsEven — the absolute value forgets the sign: an integer and its
// negation have the same size.
var AbsEven = absEvenThm{family.Add(registry.ProofEntry{
	Name:  "AbsEven",
	Key:   "prop_3c2529974d818fc5",
	Build: family.Lifted("∀x:int. |int_neg(x)| = |x|", real_sgn_abs.AbsEven),
})}

// AbsIdempotent — a size has no sign left to forget: taking the
// absolute value twice is taking it once.
var AbsIdempotent = absIdempotentThm{family.Add(registry.ProofEntry{
	Name:  "AbsIdempotent",
	Key:   "prop_bb38c8cc2d8cc2e5",
	Build: family.Lifted("∀x:int. ||x|| = |x|", real_sgn_abs.AbsIdempotent),
})}

// AbsFixedIffNonneg — the absolute value leaves its argument alone
// exactly when there is no sign to forget.
var AbsFixedIffNonneg = absFixedIffNonnegThm{family.Add(registry.ProofEntry{
	Name:  "AbsFixedIffNonneg",
	Key:   "prop_8dc3f6eda0192f04",
	Build: family.Lifted("∀x:int. |x| = x ⇔ &0 ≤ x", real_sgn_abs.AbsFixedIffNonneg),
})}

// AbsOfZero — zero has no size. The forward half of AbsVanishes below,
// as an equation ready to rewrite with.
var AbsOfZero = absOfZeroThm{family.Add(registry.ProofEntry{
	Name:  "AbsOfZero",
	Key:   "prop_7b12141244d68707",
	Build: family.Lifted("int_abs(&0) = &0", real_sgn_abs.AbsOfZero),
})}

// AbsOfOne — the unit is its own size, AbsOfZero's companion at the
// other numeral the chapter states things at.
var AbsOfOne = absOfOneThm{family.Add(registry.ProofEntry{
	Name:  "AbsOfOne",
	Key:   "prop_cc0f178fb5e96aec",
	Build: family.Lifted("int_abs(&1) = &1", real_sgn_abs.AbsOfOne),
})}

// AbsVanishes — and zero is the only integer with no size: the absolute
// value vanishes nowhere else.
var AbsVanishes = absVanishesThm{family.Add(registry.ProofEntry{
	Name:  "AbsVanishes",
	Key:   "prop_3e4d5ed4d423c7db",
	Build: family.Lifted("∀x:int. |x| = &0 ⇔ x = &0", real_sgn_abs.AbsVanishes),
})}

// AbsBounds — a bound on an integer's size is a bracket around the
// integer, and back again. ℤ's consumer for it is the division
// algorithm's size theory: `int_div_rem.DivNoLarger` converts a bound
// on a quotient's SIZE into the pair of bounds the adjunction actually
// argues with, and travels back the same way.
var AbsBounds = absBoundsThm{family.Add(registry.ProofEntry{
	Name:  "AbsBounds",
	Key:   "prop_11baf2285cc2a675",
	Build: family.Lifted("∀x k:int. |x| ≤ k ⇔ -k ≤ x ∧ x ≤ k", real_sgn_abs.AbsBounds),
})}

// AbsBetween — AbsBounds one order relation over and applied to a
// difference. ℤ wants it where two quantities are known to come from a
// common window: `int_div_rem.DivModUnique` has two remainders drawn
// from ⟦&0, |n|⟭ and needs them less than |n| apart, which is this
// statement read right to left.
//
// Its ground cites PERMUTE. The generated twin installs at
// (d, x, y) where this text binds (x, y, d), so a tuple carried over
// from a string cite has to be re-read rather than copied.
var AbsBetween = absBetweenThm{family.Add(registry.ProofEntry{
	Name: "AbsBetween",
	Key:  "prop_7baadb28d183b5b2",
	Build: family.Lifted(
		"∀x y d:int. |y - x| < d ⇔ x - d < y ∧ y < x + d ∧ &0 < d", real_sgn_abs.AbsBetween),
})}

// SgnOfZero — zero is the one integer with no direction, and the sign
// records that as a third value of its own rather than by being
// undefined there. It is the degenerate branch every argument that
// splits on sign has to dispose of, here as an equation ready to
// rewrite with.
var SgnOfZero = sgnOfZeroThm{family.Add(registry.ProofEntry{
	Name:  "SgnOfZero",
	Key:   "prop_76935b155855bef",
	Build: family.Lifted("int_sgn(&0) = &0", real_sgn_abs.SgnOfZero),
})}

// SgnTrichotomy — a direction is one of exactly three things: backwards,
// nowhere, or forwards. The members around it say what the sign DOES —
// its value at zero, that negation reverses it, that it is multiplicative,
// that multiplying by it recovers the magnitude — and none of them says
// what it IS; without this one `int_sgn(x)` stays an opaque factor and
// SgnMulSelfIsAbs's split of an integer into direction times magnitude
// cannot be consumed. It is where an argument that case-splits on a sign
// starts.
var SgnTrichotomy = sgnTrichotomyThm{family.Add(registry.ProofEntry{
	Name: "SgnTrichotomy",
	Key:  "prop_239e866ca3f61e8b",
	Build: family.Lifted(
		"∀x:int. sgn(x) = -&1 ∨ sgn(x) = &0 ∨ sgn(x) = &1", real_sgn_abs.SgnTrichotomy),
})}

// SgnOdd — negation reverses the direction: the sign of -x is minus
// the sign of x. With SgnOfZero it is what lets a sign argument be
// made on one side of zero and reflected to the other.
var SgnOdd = sgnOddThm{family.Add(registry.ProofEntry{
	Name:  "SgnOdd",
	Key:   "prop_2bcb193d44699148",
	Build: family.Lifted("∀x:int. sgn(-x) = -sgn(x)", real_sgn_abs.SgnOdd),
})}

// SgnMul — the direction of a product is the product of the
// directions: the sign is multiplicative, exactly as the size is
// (AbsMul), and the two together are the split of a product into
// direction and magnitude.
var SgnMul = sgnMulThm{family.Add(registry.ProofEntry{
	Name:  "SgnMul",
	Key:   "prop_b3ec81230a8d6e96",
	Build: family.Lifted("∀x y:int. sgn(x * y) = sgn(x) * sgn(y)", real_sgn_abs.SgnMul),
})}

// SgnMulSelfIsAbs — the split of an integer into direction and
// magnitude, `x = int_sgn(x)·|x|`, solved for the magnitude. ℤ spends
// it in `int_div_rem`'s negation members, where reflecting a division
// across zero costs exactly one step of int_sgn(n)·n and this is what
// says that step is |n| — so the correction is priced without a case
// split on the divisor's sign.
var SgnMulSelfIsAbs = sgnMulSelfIsAbsThm{family.Add(registry.ProofEntry{
	Name:  "SgnMulSelfIsAbs",
	Key:   "prop_e01bdf5638a9a2c9",
	Build: family.Lifted("∀x:int. sgn(x) * x = |x|", real_sgn_abs.SgnMulSelfIsAbs),
})}
