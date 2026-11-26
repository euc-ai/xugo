// quotient.go — the quotient of a set by a relation: the readings of
// quotient_on — a member is the class, inside the set, of a point of it;
// a statement about every member is one about every point — and, under
// an equivalence on the set, its classes covering the set and pairwise
// equal or disjoint, and the quotient of a set closed under the relation
// as the image of the set under the class map.

package equivalence

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// Reading the quotient set
// ---------------------------------------------------------------------------
//
// The quotient is the image of c under the class map of the restricted
// relation, so each reading is the image chapter's law at that map. They
// hold for any relation.

// InQuotientOn — a member of the quotient is the class, inside c, of a
// point of c.
var InQuotientOn = inQuotientOnThm{family.Add(registry.ProofEntry{
	Name: "InQuotientOn",
	Key:  "prop_e2d75b521d4af476",
	Build: family.Theorem("∀c:set(A). ∀R:(A → A → bool). ∀s:set(A). "+
		"    s ∈ quotient_on(c, R) ⇔ ∃x:A. s = equivalence_class(relation_on(c, R), x) ∧ x ∈ c",
		func(a *Argument, c *Expr[Set[A]], R *Arrow2[A, A, Bool], s *Expr[Set[A]]) {
			a.Show(
				"the quotient is the image of c under the class map, and "+
					"a member of an image is the value at a point of its source",
				Unfold(QuotientOnDef),
				By(set_basic.InImage))
		}),
})}

// ClassInQuotientOn — the class of a point of c is a member of the
// quotient.
var ClassInQuotientOn = classInQuotientOnThm{family.Add(registry.ProofEntry{
	Name: "ClassInQuotientOn",
	Key:  "prop_e4a4eb13230994b3",
	Build: family.Theorem(Statement{
		Binders: "∀c:set(A). ∀R:(A → A → bool). ∀x:A.",
		Hypotheses: []string{
			"x ∈ c",
		},
		Conclusion: "equivalence_class(relation_on(c, R), x) ∈ quotient_on(c, R)",
	},
		func(a *Argument, c *Expr[Set[A]], R *Arrow2[A, A, Bool], x *Expr[A], inC Fact) {
			a.Show(
				"the quotient is the image of c under the class "+
					"map, and the value at a point of c lies in the image",
				Unfold(QuotientOnDef),
				By(inC, set_image.FunInImage))
		}),
})}

// ForallInQuotientOn — a statement about every member of the quotient
// is one about the class of every point of c.
var ForallInQuotientOn = forallInQuotientOnThm{family.Add(registry.ProofEntry{
	Name: "ForallInQuotientOn",
	Key:  "prop_f6b0dc6eb62692e",
	Build: family.Theorem("∀c:set(A). ∀R:(A → A → bool). ∀P:(set(A) → bool). "+
		"    (∀s:set(A). s ∈ quotient_on(c, R) ⇒ P(s)) ⇔ "+
		"    ∀x:A. x ∈ c ⇒ P(equivalence_class(relation_on(c, R), x))",
		func(a *Argument, c *Expr[Set[A]], R *Arrow2[A, A, Bool], P *Arrow[Set[A], Bool]) {
			a.Show(
				"the quotient is the image of c under the class map, "+
					"and a quantifier over an image is one over its source",
				Unfold(QuotientOnDef),
				By(set_image.ForallInImage))
		}),
})}

// ForallInQuotientOnPair — and about every two members, one about the
// classes of every two points.
var ForallInQuotientOnPair = forallInQuotientOnPairThm{family.Add(registry.ProofEntry{
	Name: "ForallInQuotientOnPair",
	Key:  "prop_70159dbaf2a50794",
	Build: family.Theorem("∀c:set(A). ∀R:(A → A → bool). ∀P:(set(A) → set(A) → bool). "+
		"    (∀s t:set(A). s ∈ quotient_on(c, R) ∧ t ∈ quotient_on(c, R) ⇒ P(s, t)) ⇔ "+
		"    ∀x y:A. "+
		"        x ∈ c ∧ y ∈ c ⇒ "+
		"        P(equivalence_class(relation_on(c, R), x), equivalence_class(relation_on(c, R), y))",
		func(a *Argument, c *Expr[Set[A]], R *Arrow2[A, A, Bool], P *Arrow2[Set[A], Set[A], Bool]) {
			a.Show(
				"the quotient is the image of c under the class map, and a quantifier "+
					"over two points of an image is one over two points of its source",
				Unfold(QuotientOnDef),
				By(set_image.ForallInImagePair))
		}),
})}

// ExistsInQuotientOn — some member of the quotient has a property
// exactly when the class of some point of c has it.
var ExistsInQuotientOn = existsInQuotientOnThm{family.Add(registry.ProofEntry{
	Name: "ExistsInQuotientOn",
	Key:  "prop_32d596f78c755162",
	Build: family.Theorem("∀c:set(A). ∀R:(A → A → bool). ∀P:(set(A) → bool). "+
		"    (∃s:set(A). s ∈ quotient_on(c, R) ∧ P(s)) ⇔ "+
		"    ∃x:A. x ∈ c ∧ P(equivalence_class(relation_on(c, R), x))",
		func(a *Argument, c *Expr[Set[A]], R *Arrow2[A, A, Bool], P *Arrow[Set[A], Bool]) {
			a.Show(
				"the quotient is the image of c under the class map, "+
					"and an existential over an image is one over its source",
				Unfold(QuotientOnDef),
				By(set_image.ExistsInImage))
		}),
})}

// QuotientOnFinite — a finite set has finitely many classes: its quotient
// is an image of it.
var QuotientOnFinite = quotientOnFiniteThm{family.Add(registry.ProofEntry{
	Name: "QuotientOnFinite",
	Key:  "prop_bf5ab20f048f4b99",
	Build: family.Theorem(Statement{
		Binders: "∀c:set(A). ∀R:(A → A → bool).",
		Hypotheses: []string{
			"finite(c)",
		},
		Conclusion: "finite(quotient_on(c, R))",
	},
		func(a *Argument, c *Expr[Set[A]], R *Arrow2[A, A, Bool], finite Fact) {
			a.Show(
				"the quotient is the image of the finite c under the class map",
				Unfold(QuotientOnDef),
				By(finite, finite_set.FiniteImage))
		}),
})}

// ---------------------------------------------------------------------------
// The quotient under an equivalence
// ---------------------------------------------------------------------------

// QuotientOnClosed — when c is closed under the relation, its quotient
// is the image of c under the class map itself.
var QuotientOnClosed = quotientOnClosedThm{family.Add(registry.ProofEntry{
	Name: "QuotientOnClosed",
	Key:  "prop_392aab17b5e1f33e",
	Build: family.Theorem(Statement{
		Binders: "∀c:set(A). ∀R:(A → A → bool).",
		Hypotheses: []string{
			"∀x y:A. x ∈ c ∧ R(x, y) ⇒ y ∈ c",
		},
		Conclusion: "quotient_on(c, R) = image(equivalence_class(R), c)",
	},
		func(a *Argument, c *Expr[Set[A]], R *Arrow2[A, A, Bool], closed Fact) {
			sameClass := a.Have(
				"at a point of c the class inside c is the class",
				"∀x:A. x ∈ c ⇒ equivalence_class(relation_on(c, R), x) = equivalence_class(R, x)",
				By(closed, ClassOnClosed))
			a.Show(
				"two maps that agree on c have one image of c",
				Unfold(QuotientOnDef),
				By(sameClass, set_image.ImageCongruence))
		}),
})}

// InQuotientOnClosed — when c is closed under the relation, a member of
// its quotient is the class of a point of c: QuotientOnClosed, then the
// image read off.
var InQuotientOnClosed = inQuotientOnClosedThm{family.Add(registry.ProofEntry{
	Name: "InQuotientOnClosed",
	Key:  "prop_5fa0573161374bda",
	Build: family.Theorem(Statement{
		Binders: "∀c:set(A). ∀R:(A → A → bool). ∀s:set(A).",
		Hypotheses: []string{
			"∀x y:A. x ∈ c ∧ R(x, y) ⇒ y ∈ c",
		},
		Conclusion: "s ∈ quotient_on(c, R) ⇔ ∃x:A. s = equivalence_class(R, x) ∧ x ∈ c",
	},
		func(a *Argument, c *Expr[Set[A]], R *Arrow2[A, A, Bool], s *Expr[Set[A]], closed Fact) {
			image := a.Have(
				"c being closed, the quotient is the image of c under the class map",
				"quotient_on(c, R) = image(equivalence_class(R), c)",
				By(closed, QuotientOnClosed))
			// InImage is read at the class map, A → set(A): a Simp rule is not
			// instantiated at a type on its own.
			a.Show(
				"a member of the image of c under the class map is the class of a point of c",
				image.Rw(),
				Simp(Fwd(set_basic.InImage.Inst(TypeBinder.BindA[A](), TypeBinder.BindB[Set[A]]()))),
				Basic())
		}),
})}

// ClassInQuotientOnClosed — when c is closed under the relation, the class
// of a point of c is a member of its quotient.
var ClassInQuotientOnClosed = classInQuotientOnClosedThm{family.Add(registry.ProofEntry{
	Name: "ClassInQuotientOnClosed",
	Key:  "prop_d63c2c2417610582",
	Build: family.Theorem(Statement{
		Binders: "∀c:set(A). ∀R:(A → A → bool). ∀x:A.",
		Hypotheses: []string{
			"x ∈ c",
			"∀u v:A. u ∈ c ∧ R(u, v) ⇒ v ∈ c",
		},
		Conclusion: "equivalence_class(R, x) ∈ quotient_on(c, R)",
	},
		func(a *Argument, c *Expr[Set[A]], R *Arrow2[A, A, Bool], x *Expr[A], inC Fact, closed Fact) {
			image := a.Have(
				"c being closed, the quotient is the image of c under the class map",
				"quotient_on(c, R) = image(equivalence_class(R), c)",
				By(closed, QuotientOnClosed))
			a.Show(
				"the value of the class map at a point of c lies in the image",
				image.Rw(),
				By(inC, set_image.FunInImage))
		}),
})}

// QuotientOnCovers — the classes cover c: each lies in c, and each point
// of c lies in its own.
var QuotientOnCovers = quotientOnCoversThm{family.Add(registry.ProofEntry{
	Name: "QuotientOnCovers",
	Key:  "prop_ccdedc024079200d",
	Build: EquivalenceOn.Law("⋃quotient_on(c, R) = c",
		func(a *Argument, c *Expr[Set[A]], R *Arrow2[A, A, Bool], equiv EquivalenceFact[on.C]) {
			a.Do(Simp(Fwd(set_order.SubsetAntisymEq)), SplitConj(
				Case(
					"every class lies in c",
					Simp(Fwd(set_order.UnionsSubset), Fwd(ForallInQuotientOn)),
					By(ClassOnSubset)),
				Case(
					"every point of c lies in a class: its own",
					Simp(Fwd(set_basic.SubsetDef)),
					a.ForEach(func(x *Expr[A]) Action {
						return Derive(func(b *Argument) {
							inC := b.Assume()
							b.Do(Simp(Fwd(set_basic.InUnions)))
							b.Take(b.TermAs[Set[A]]("equivalence_class(relation_on(c, R), x)"))
							b.Show(
								"the class of x is a member of the quotient, and x lies in it",
								By(inC, ClassInQuotientOn, ClassOwnOn, equiv))
						})
					})),
			))
		}),
})}

// QuotientOnDisjointOrEqual — two members of the quotient are equal or
// disjoint, as the classes of any two points of c are.
var QuotientOnDisjointOrEqual = quotientOnDisjointOrEqualThm{family.Add(registry.ProofEntry{
	Name: "QuotientOnDisjointOrEqual",
	Key:  "prop_c85c59409f218cfe",
	Build: EquivalenceOn.Law(Statement{
		Binders: "∀s t:set(A).",
		Hypotheses: []string{
			"s ∈ quotient_on(c, R)",
			"t ∈ quotient_on(c, R)",
		},
		Conclusion: "s = t ∨ disjoint(s, t)",
	},
		func(a *Argument, c *Expr[Set[A]], R *Arrow2[A, A, Bool], equiv EquivalenceFact[on.C]) {
			a.Show(
				"a statement about two members of the quotient is one about the classes of two points of c",
				Simp(Fwd(ForallInQuotientOnPair)),
				By(ClassOnDisjointOrEqual, equiv))
		}),
})}
