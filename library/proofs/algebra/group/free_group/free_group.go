// free_group.go — the free group over A is a group. The equivalence of
// words is a congruence for the two operations on words, concatenation
// and the inverse, which is exactly what lets them descend to the
// classes; the descended operations then satisfy the group axioms, each
// read at representatives.
//
// Four parts, marked by banners: the congruence for concatenation; the
// inverse of a word and its congruence; the operations at classes; the
// group.

package free_group

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/datatypes/list"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The congruence for concatenation
// ---------------------------------------------------------------------------

// Appending a word on either side of an equivalent pair keeps it
// equivalent, and so does appending equivalent pairs side by side.
//
// Each one-sided law is a rule induction along the equivalence,
// carrying the property "the pair with the fixed word appended is
// equivalent". The three equivalence rules carry it for free — the
// appended pair is reflexive, symmetric and transitive by the same
// rule — and the one piece of content is the cancellation: a deleted
// pair `x, x⁻¹` stays adjacent once the fixed word is appended, so it
// is the same cancellation at a re-associated word. The two-sided law
// composes the one-sided ones through the common word u₂ ++ v₁; it is
// the respectfulness the lift of concatenation to classes cites.

// AppendCongruenceLeft — appending w after both words of an equivalent
// pair keeps them equivalent. Rule induction on the pair, carrying the
// property that the pair with w appended is equivalent: the first three
// rules re-apply to the appended pair, and at the cancellation
// (u ++ (x :: x⁻¹ :: v)) ++ w re-associates to u ++ (x :: x⁻¹ :: (v ++ w))
// — the pair deleted from the word is the same pair, in front of v ++ w.
var AppendCongruenceLeft = appendCongruenceLeftThm{family.Add(registry.ProofEntry{
	Name: "AppendCongruenceLeft",
	Key:  "prop_b6f5fa77c1f84470",
	Build: family.Theorem(Statement{
		Binders: "∀u v w:list(prod(A, bool)).",
		Hypotheses: []string{
			"word_equiv(u, v)",
		},
		Conclusion: "word_equiv(list_append(u, w), list_append(v, w))",
	},
		func(a *Argument, u, v, w *Expr[List[Prod[A, Bool]]], equiv Fact) {
			a.Show(
				"rule induction along the equivalence, carrying the "+
					"property that the pair with w appended is equivalent",
				ByInduction(wordEquivInduct, equiv,
					Case(
						"a word with w appended is equivalent to itself, by the first rule",
						By(Normalized, wordEquivRules)),
					Case(
						"the appended pair read backwards is equivalent, by the second rule",
						By(wordEquivRules)),
					Case(
						"two appended pairs through a common word compose, by the third rule",
						By(wordEquivRules)),
					Case(
						"the cancellation: re-associated to the right with w "+
							"pushed through the cons, the deleted pair stays adjacent",
						Simp(Rev(list.AppendAssoc.Inst[Prod[A, Bool]]()), Fwd(list.ListAppendDef.Inst[Prod[A, Bool]]())),
						By(wordEquivRules))))
		}),
})}

// AppendCongruenceRight — appending u before both words of an
// equivalent pair keeps them equivalent. Rule induction on the pair,
// carrying the property that the pair behind u is equivalent: the first
// three rules re-apply, and at the cancellation
// u ++ (u' ++ (x :: x⁻¹ :: v)) re-associates to (u ++ u') ++ (x :: x⁻¹ :: v)
// — the same cancellation, behind the longer prefix u ++ u'.
var AppendCongruenceRight = appendCongruenceRightThm{family.Add(registry.ProofEntry{
	Name: "AppendCongruenceRight",
	Key:  "prop_f8e3662e93785e4b",
	Build: family.Theorem(Statement{
		Binders: "∀u v w:list(prod(A, bool)).",
		Hypotheses: []string{
			"word_equiv(v, w)",
		},
		Conclusion: "word_equiv(list_append(u, v), list_append(u, w))",
	},
		func(a *Argument, u, v, w *Expr[List[Prod[A, Bool]]], equiv Fact) {
			a.Show(
				"rule induction along the equivalence, carrying the property that the pair behind u is equivalent",
				ByInduction(wordEquivInduct, equiv,
					Case(
						"a word behind u is equivalent to itself, by the first rule",
						By(Normalized, wordEquivRules)),
					Case(
						"the pair behind u read backwards is equivalent, by the second rule",
						By(wordEquivRules)),
					Case(
						"two pairs behind u through a common word compose, by the third rule",
						By(wordEquivRules)),
					Case(
						"the cancellation: re-associated to the left, the deleted pair sits behind the longer prefix",
						Simp(Fwd(list.AppendAssoc.Inst[Prod[A, Bool]]())),
						By(wordEquivRules))))
		}),
})}

// AppendCongruence — the equivalence of words is a congruence for
// concatenation: the respectfulness law the lift of concatenation to
// the free group cites. The left congruence replaces the first word,
// the right one the second, and transitivity composes the two steps
// through u₂ ++ v₁.
var AppendCongruence = appendCongruenceThm{family.Add(registry.ProofEntry{
	Name: "AppendCongruence",
	Key:  "prop_29e79ea67a71d956",
	Build: family.Theorem(Statement{
		Binders: "∀u₁ u₂ v₁ v₂:list(prod(A, bool)).",
		Hypotheses: []string{
			"word_equiv(u₁, u₂)",
			"word_equiv(v₁, v₂)",
		},
		Conclusion: "word_equiv(list_append(u₁, v₁), list_append(u₂, v₂))",
	},
		func(a *Argument, u1, u2, v1, v2 *Expr[List[Prod[A, Bool]]], both Fact) {
			a.Show(
				"u₁ ++ v₁ ~ u₂ ++ v₁ by the left congruence, u₂ ++ v₁ ~ "+
					"u₂ ++ v₂ by the right one, and the third rule chains them",
				By(both, AppendCongruenceLeft.At(u1, u2, v1), AppendCongruenceRight.At(u2, v1, v2), wordEquivRules))
		}),
})}

// ---------------------------------------------------------------------------
// The inverse of a word and its congruence
// ---------------------------------------------------------------------------

// Inverting a letter twice gives the letter back, the inverse of a
// concatenation is the concatenation of the inverses in the other
// order, the inverse of an inverse is the word itself, and the
// equivalence of words is a congruence for the inverse. The congruence
// is the respectfulness the lift door asks for before the inverse
// descends to the free group; the letter law and the concatenation law
// are what the computation inside its cancellation case rests on.
//
// The three laws are computations with the definitions and the list
// chapter's laws — no induction on words is run for them, the list
// chapter having run each one once; the congruence is a rule induction
// along the equivalence, as the two one-sided laws above are.

// LetterInverseInverse — inverting a letter twice gives the letter back.
// Unfolded twice, the doubly inverted letter is the pair of its own
// generator and its sign negated twice; the projections of a pair are its
// components, a negation negated is itself, and a pair is the pair of its
// components.
var LetterInverseInverse = letterInverseInverseThm{family.Add(registry.ProofEntry{
	Name: "LetterInverseInverse",
	Key:  "prop_78672b2a5dc2726f",
	Build: family.Theorem("∀x:prod(A, bool). letter_inverse(letter_inverse(x)) = x",
		func(a *Argument, x *Expr[Prod[A, Bool]]) {
			// The pair laws read at a letter: a generator beside a sign.
			generator := TypeBinder.BindA[A]()
			sign := TypeBinder.BindB[Bool]()
			a.Show(
				"unfolded twice, the letter is the pair of its generator and "+
					"its sign negated twice, which is the pair of its components",
				Simp(
					Fwd(letterInverseDef),
					Fwd(pairs.Fst.Inst(generator, sign)),
					Fwd(pairs.Snd.Inst(generator, sign)),
					Fwd(pairs.PairEta.Inst(generator, sign))),
				Refl())
		}),
})}

// InverseAppend — the inverse of a concatenation is the concatenation of
// the inverses, in the other order. Unfolded, an inverse is a reversed
// image: the image of a concatenation is the concatenation of the images,
// and reversing a concatenation reverses each part and swaps them.
var InverseAppend = inverseAppendThm{family.Add(registry.ProofEntry{
	Name: "InverseAppend",
	Key:  "prop_e421edffab9f4e15",
	Build: family.Theorem("∀u v:list(prod(A, bool)). "+
		"    word_inverse(list_append(u, v)) = list_append(word_inverse(v), word_inverse(u))",
		func(a *Argument, u, v *Expr[List[Prod[A, Bool]]]) {
			// The list laws read at letters, on the source side and the image side alike.
			letters := TypeBinder.BindA[Prod[A, Bool]]()
			images := TypeBinder.BindB[Prod[A, Bool]]()
			a.Show(
				"the image of the concatenation is the concatenation of "+
					"the images, and reversing it swaps the two reversed parts",
				Simp(
					Fwd(wordInverseDef),
					Fwd(list.MapAppend.Inst(letters, images)),
					Fwd(list.ReverseAppend.Inst[Prod[A, Bool]]())),
				Refl())
		}),
})}

// InverseInverse — the inverse of an inverse is the word itself.
// Unfolded twice, the word is read backwards twice with every letter
// inverted twice: reversing commutes with the image, two reversals
// cancel, the two images compose into one image under the doubly
// inverting letter map, which LetterInverseInverse makes the identity,
// and the image under the identity is the word.
var InverseInverse = inverseInverseThm{family.Add(registry.ProofEntry{
	Name: "InverseInverse",
	Key:  "prop_c99c40a3b07893c9",
	Build: family.Theorem("∀w:list(prod(A, bool)). word_inverse(word_inverse(w)) = w",
		func(a *Argument, w *Expr[List[Prod[A, Bool]]]) {
			// The list laws read at letters at every stage: both images and the composite are words.
			letters := TypeBinder.BindA[Prod[A, Bool]]()
			images := TypeBinder.BindB[Prod[A, Bool]]()
			composite := TypeBinder.BindC[Prod[A, Bool]]()
			a.Show(
				"the reversals meet and cancel, the two letter maps compose, and a letter inverted twice is itself",
				Simp(
					Fwd(wordInverseDef),
					Fwd(list.MapReverse.Inst(letters, images)),
					Fwd(list.ReverseReverse.Inst[Prod[A, Bool]]()),
					Rev(list.MapMap.Inst(letters, images, composite)),
					Fwd(LetterInverseInverse),
					Fwd(list.MapId.Inst[Prod[A, Bool]]())),
				Refl())
		}),
})}

// InverseCongruence — the equivalence of words is a congruence for the
// inverse: equivalent words have equivalent inverses. Rule induction
// along the equivalence, carrying "the inverted pair is equivalent".
// Each of the first three rules is undone by the same rule on the
// inverted pair. The cancellation rule, at a front word, a deleted pair
// x, x⁻¹ and a back word, needs one computation: the inverse of x, x⁻¹,
// back is the inverse of back followed by x, x⁻¹ — every letter
// inverted, x twice, and the whole read backwards — so the inverse of the
// whole word is the inverse of back, then x, x⁻¹, then the inverse of
// front, and deleting that adjacent pair leaves the inverse of front,
// back.
var InverseCongruence = inverseCongruenceThm{family.Add(registry.ProofEntry{
	Name: "InverseCongruence",
	Key:  "prop_3b6ab8720fd4f74f",
	Build: family.Theorem(Statement{
		Binders: "∀u v:list(prod(A, bool)).",
		Hypotheses: []string{
			"word_equiv(u, v)",
		},
		Conclusion: "word_equiv(word_inverse(u), word_inverse(v))",
	},
		func(a *Argument, u, v *Expr[List[Prod[A, Bool]]], equivalent Fact) {
			a.Show(
				"rule induction along the equivalence, carrying the property that the inverted pair is equivalent",
				ByInduction(wordEquivInduct, equivalent,
					Case(
						"a word's inverse is equivalent to itself, the first rule",
						By(Normalized, wordEquivRules)),
					Case(
						"an equivalence of inverses runs the other way, the second rule",
						By(wordEquivRules)),
					Case(
						"two equivalences of inverses through a common inverse compose, the third rule",
						By(wordEquivRules)),
					Case(
						"a deleted pair x, x⁻¹ is a deleted pair in the inverse, "+
							"between the inverted back and the inverted front",
						Derive(func(c *Argument) {
							// The list laws read at letters, the clauses of the map on both sides.
							letters := TypeBinder.BindA[Prod[A, Bool]]()
							images := TypeBinder.BindB[Prod[A, Bool]]()
							c.FixAs[List[Prod[A, Bool]]]("front")
							c.FixAs[List[Prod[A, Bool]]]("back")
							c.FixAs[Prod[A, Bool]]("x")
							invertedTriple := c.Have(
								"the inverse of x, x⁻¹, back is the inverse of back followed "+
									"by x, x⁻¹: every letter inverted, x twice, read backwards",
								"word_inverse(cons(x, cons(letter_inverse(x), back))) = "+
									"list_append(word_inverse(back), cons(x, cons(letter_inverse(x), nil)))",
								Simp(
									Fwd(wordInverseDef),
									Fwd(list.ListMapDef.Inst(letters, images)),
									Fwd(list.ListReverseDef.Inst[Prod[A, Bool]]()),
									Fwd(LetterInverseInverse),
									Rev(list.AppendAssoc.Inst[Prod[A, Bool]]()),
									Fwd(list.ListAppendDef.Inst[Prod[A, Bool]]())),
								Refl())
							c.Show(
								"both inverses split at the concatenation, leaving x, x⁻¹ between "+
									"the inverses of back and front, which the fourth rule deletes",
								Simp(Fwd(InverseAppend)),
								invertedTriple.Rw(),
								Simp(Rev(list.AppendAssoc.Inst[Prod[A, Bool]]()), Fwd(list.ListAppendDef.Inst[Prod[A, Bool]]())),
								By(wordEquivRules))
						}))))
		}),
})}

// ---------------------------------------------------------------------------
// The operations at classes
// ---------------------------------------------------------------------------

// The product is the class of the concatenation, the inverse the class
// of the inverse word. Each is one lift of the quotient door, whose
// obligation — that the rule respects the equivalence in every class
// argument — is the congruence law proved above, cited; nothing else
// is asked, and the door derives the definition's existence from the
// quotient's own Sound and Exact.

// FreeMulDef — the product of two classes is the class of the
// concatenation of representatives; AppendCongruence is the
// respectfulness. It is written `x * y` — the group chapter's symbol,
// declared here as this constant's notation (a notation's holes are
// named by the equation's binders, which for a lift are the
// representatives: the class of u times the class of v).
var FreeMulDef = freeMulDefThm{family.Define(registry.DefEntry{
	Name:      "FreeMulDef",
	Key:       "prop_bd2f73b6385a7b8d",
	Const:     "free_mul",
	Type:      "free_group(A) → free_group(A) → free_group(A)",
	Notation:  "u * v",
	Equations: []string{"∀u v:list(prod(A, bool)). free_mul(⁅u⁆, ⁅v⁆) = ⁅list_append(u, v)⁆"},
	Respects:  []Action{Cite(AppendCongruence)},
	Deps:      []registry.EntryLike{FreeGroupDef.Surjectivity, AppendCongruence},
})}

// FreeInvDef — the inverse of a class is the class of the inverse of
// a representative; InverseCongruence is the respectfulness.
var FreeInvDef = freeInvDefThm{family.Define(registry.DefEntry{
	Name:      "FreeInvDef",
	Key:       "prop_d00e1342eb64fe2",
	Const:     "free_inv",
	Type:      "free_group(A) → free_group(A)",
	Equations: []string{"∀u:list(prod(A, bool)). free_inv(⁅u⁆) = ⁅word_inverse(u)⁆"},
	Respects:  []Action{Cite(InverseCongruence)},
	Deps:      []registry.EntryLike{FreeGroupDef.Surjectivity, InverseCongruence},
})}

// ---------------------------------------------------------------------------
// The group
// ---------------------------------------------------------------------------

// The operations are defined at classes, so each axiom inducts its
// class binders to representatives, computes the operations as words
// and reads the resulting class equation: associativity and the left
// identity are then the list chapter's concatenation laws, two words
// being one word, and the left inverse is the one piece of group
// mathematics the chapter proves about words — the inverse of a word
// followed by the word reduces to the empty word, by deleting the
// adjacent pairs from the middle outward.

// InverseCancel — the inverse of a word, followed by the word, is
// equivalent to the empty word. Induction on the word: the empty word
// has the empty inverse, and the empty word is equivalent to itself.
// At a word x :: t, the inverse is the inverse of t followed by x⁻¹, so
// the concatenation re-associates to the inverse of t, then the
// adjacent pair x⁻¹, x, then t; deleting the pair leaves the inverse of
// t followed by t, which the induction hypothesis reduces to the empty
// word.
var InverseCancel = inverseCancelThm{family.Add(registry.ProofEntry{
	Name: "InverseCancel",
	Key:  "prop_43f1cbdc29b1098a",
	Build: family.Theorem("∀w:list(prod(A, bool)). word_equiv(list_append(word_inverse(w), w), nil)",
		func(a *Argument) {
			// The list laws read at letters, the clauses of the map on both sides.
			letters := TypeBinder.BindA[Prod[A, Bool]]()
			images := TypeBinder.BindB[Prod[A, Bool]]()
			a.Induct("w")
			a.Base(
				"the empty word's inverse is empty, and the empty word is equivalent to itself, the first rule",
				Simp(
					Fwd(wordInverseDef),
					Fwd(list.ListMapDef.Inst(letters, images)),
					Fwd(list.ListReverseDef.Inst[Prod[A, Bool]]()),
					Fwd(list.ListAppendDef.Inst[Prod[A, Bool]]())),
				Cite(wordEquivRules))
			a.Step(
				"at x :: t: the inverse of t, then x⁻¹, x, then t — the pair deleted, the hypothesis finishes",
				func(b *Argument, ih Fact) {
					b.StepArgs("x", "t")
					inverted := b.Have(
						"the inverse of x :: t is the inverse of t followed by x⁻¹: every letter inverted, read backwards",
						"word_inverse(cons(x, t)) = list_append(word_inverse(t), cons(letter_inverse(x), nil))",
						Simp(
							Fwd(wordInverseDef),
							Fwd(list.ListMapDef.Inst(letters, images)),
							Fwd(list.ListReverseDef.Inst[Prod[A, Bool]]())),
						Refl())
					b.Show(
						"re-associated, x⁻¹, x sits between the inverse of t and t: the fourth "+
							"rule deletes the pair, the hypothesis finishes, the third rule chains",
						inverted.Rw(),
						Simp(Rev(list.AppendAssoc.Inst[Prod[A, Bool]]()), Fwd(list.ListAppendDef.Inst[Prod[A, Bool]]())),
						By(ih, wordEquivRules, LetterInverseInverse))
				})
		}),
})}

// Group — the free group over A is a group under the product, with
// the class of the empty word as identity and the inverse. Each axiom
// is read at representatives: the product of classes is the class of
// the concatenation, so associativity and the left identity are the
// concatenation laws, and the left inverse is InverseCancel read as a
// class equation.
var Group = groupThm{family.Add(registry.ProofEntry{
	Name: "Group",
	Key:  "prop_f3a2da60e6a328bf",
	Build: family.Instance(group.Group, "group(mk_group(free_mul⟨A:A⟩, free_one, free_inv, 𝕌))",
		Case(
			"the product associates: at representatives both "+
				"sides are the class of the three words concatenated",
			Derive(func(b *Argument) {
				b.Induct("x")
				b.Induct("y")
				b.Induct("z")
				b.Show(
					"the products compute to classes of concatenations, and concatenation associates",
					Simp(Fwd(FreeMulDef), Fwd(list.AppendAssoc.Inst[Prod[A, Bool]]())),
					Refl())
			})),
		Case(
			"the class of the empty word is a left identity: the empty "+
				"word prepended to a representative is the representative",
			Derive(func(b *Argument) {
				b.Induct("x")
				b.Show(
					"the product computes to the class of nil ++ u, which is the class of u",
					Simp(Fwd(FreeOneDef), Fwd(FreeMulDef), Fwd(list.ListAppendDef.Inst[Prod[A, Bool]]())),
					Refl())
			})),
		Case(
			"the inverse is a left inverse: at a representative u the product "+
				"is the class of the inverse of u followed by u, which cancels",
			Derive(func(b *Argument) {
				b.Induct("x")
				b.Show(
					"the product computes to a class, class equality is "+
						"the equivalence of words, and the inverse cancels",
					Simp(Fwd(FreeInvDef), Fwd(FreeMulDef), Fwd(FreeOneDef), Fwd(FreeGroupDef.Eq)),
					Cite(InverseCancel))
			}))),
})}
