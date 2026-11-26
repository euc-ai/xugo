// map.go — list_map, and the algebra of applying a function along a list.
//
// list_map changes what a list holds and nothing else, so every law here
// says that some other operation does not notice: concatenation, the
// order, the length, and the identity function; and two maps have one
// image of a list exactly when they agree on its members. Two element types meet
// in this file and nowhere else in the chapter — a statement over
// `f : A → B` reads the list operations at BOTH, which is why several
// of these proofs cite one definition twice, once per letter.

package list

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

// MapAppend — list_map distributes over list_append. By induction on the first
// list, with f and the second list fixed. With nil in front, nil in
// front of m is m and the image of nil is nil, so both sides are the
// image of m. With a head in front, f(h) comes out in front on both
// sides — on the left once list_append has moved h out and list_map has applied
// f to it, on the right once list_map has put f(h) in front and list_append has
// moved it out — and the induction hypothesis identifies the tails.
var MapAppend = mapAppendThm{family.Add(registry.ProofEntry{
	Name: "MapAppend",
	Key:  "prop_d8ad69a390394910",
	Build: family.Theorem("∀f:(A → B). ∀l m:list(A). "+
		"    list_map(f, list_append(l, m)) = list_append(list_map(f, l), list_map(f, m))",
		func(a *Argument, f *Arrow[A, B], l, m *Expr[List[A]]) {
			a.Induct(l)
			a.Base(
				"l = nil: nil in front of m is m and the image of nil is nil, so both sides are list_map(f, m)",
				Simp(Fwd(ListAppendDef), Fwd(ListAppendDef.Inst[B]()), Fwd(ListMapDef)),
				Refl())
			a.Step(
				"l = cons(h, t): f(h) comes out in front on both sides, and the hypothesis identifies the tails",
				func(b *Argument, ih Fact) {
					b.Show(
						"both sides are f(h) in front of a tail, and the tails agree by the hypothesis",
						Simp(Fwd(ListAppendDef), Fwd(ListAppendDef.Inst[B]()), Fwd(ListMapDef)),
						By(Normalized, ih))
				})
		}),
})}

// MapId — mapping the identity over a list changes nothing. By induction
// on l: at nil the first clause of list_map reads list_map(λx. x, nil) = nil
// outright; at cons(h, t) the second clause puts (λx. x)(h), which is h,
// in front of list_map(λx. x, t), and the hypothesis folds that tail back to
// t. list_map is read at the identity's own type, A → A.
var MapId = mapIdThm{family.Add(registry.ProofEntry{
	Name: "MapId",
	Key:  "prop_614d24b711f6f45e",
	Build: family.Theorem("∀l:list(A). list_map(λx:A. x, l) = l",
		func(a *Argument, l *Expr[List[A]]) {
			mapAtIdentity := ListMapDef.Inst(TypeBinder.BindA[A](), TypeBinder.BindB[A]())
			a.Induct(l)
			a.Base(
				"at nil: the first clause of list_map leaves nil = nil",
				Simp(Fwd(mapAtIdentity)),
				Refl())
			a.Step(
				"at cons(h, t): the second clause puts h out front, "+
					"and the hypothesis folds list_map(λx. x, t) to t",
				func(b *Argument, ih Fact) {
					b.Show(
						"both sides now read cons(h, t)",
						Simp(Fwd(mapAtIdentity)),
						ih.Rw(),
						TrivialNormalized())
				})
		}),
})}

// MapMap — mapping g after f is mapping their composite. By induction
// on l with f and g fixed. Every list_map of the empty list is empty, so at
// nil both sides are nil. At cons(h, t) each side puts g(f(h)) in front
// — the left in one step, the right through f(h) — and the hypothesis
// identifies the tails. list_map is read at the three element types the
// statement uses it at: A → B and B → C for the two stages, A → C for
// the composite.
var MapMap = mapMapThm{family.Add(registry.ProofEntry{
	Name: "MapMap",
	Key:  "prop_1dee3f69219dfb00",
	Build: family.Theorem("∀f:(A → B). ∀g:(B → C). ∀l:list(A). "+
		"    list_map(λx:A. g(f(x)), l) = list_map(g, list_map(f, l))",
		func(a *Argument, f *Arrow[A, B], g *Arrow[B, C], l *Expr[List[A]]) {
			// The clauses of list_map at the three element types.
			firstStage := Fwd(ListMapDef)
			secondStage := Fwd(ListMapDef.Inst(TypeBinder.BindA[B](), TypeBinder.BindB[C]()))
			composite := Fwd(ListMapDef.Inst(TypeBinder.BindA[A](), TypeBinder.BindB[C]()))

			a.Induct(l)
			a.Base(
				"l = nil: every list_map of the empty list is empty, so both sides are nil",
				Simp(firstStage, secondStage, composite),
				Refl())
			a.Step(
				"l = cons(h, t): both sides put g(f(h)) in front, and the hypothesis identifies the tails",
				func(b *Argument, ih Fact) {
					b.Show(
						"both sides are g(f(h)) in front of list_map(g, list_map(f, t))",
						Simp(firstStage, secondStage, composite),
						ih.Rw(),
						TrivialNormalized())
				})
		}),
})}

// MapReverse — reversing an image is the image of the reverse. By
// induction on l with f fixed. At nil both sides are the empty list,
// which is its own reverse at the source type and at the image type
// alike. At cons(h, t) the head travels to the far end on both sides:
// on the left list_map puts f(h) in front and list_reverse sends it behind the
// reversed image of t; on the right list_reverse sends h behind the reversed
// t, and MapAppend carries f across that concatenation, leaving f(h)
// behind the image of the reversed t. The hypothesis identifies the two
// front segments.
var MapReverse = mapReverseThm{family.Add(registry.ProofEntry{
	Name: "MapReverse",
	Key:  "prop_1c4b16bbb58da2ae",
	Build: family.Theorem("∀f:(A → B). ∀l:list(A). "+
		"    list_reverse(list_map(f, l)) = list_map(f, list_reverse(l))",
		func(a *Argument, f *Arrow[A, B], l *Expr[List[A]]) {
			reverseOfImage := ListReverseDef.Inst[B]()
			a.Induct(l)
			a.Base(
				"l = nil: the empty list is its own reverse, at the source type and at the image type alike",
				Simp(Fwd(ListMapDef), Fwd(ListReverseDef), Fwd(reverseOfImage)),
				Refl())
			a.Step(
				"l = cons(h, t): the head travels to the far end on both sides, "+
					"MapAppend carrying f across the concatenation list_reverse leaves",
				func(b *Argument, ih Fact) {
					b.Show(
						"both sides are a reversed tail with f(h) behind it, and the hypothesis identifies the tails",
						Simp(Fwd(ListMapDef), Fwd(ListReverseDef), Fwd(reverseOfImage), Fwd(MapAppend)),
						ih.Rw(),
						TrivialNormalized())
				})
		}),
})}

// LengthMap — applying f to every element leaves the length alone. By
// induction on l with f fixed: list_map and list_length both recurse on the list,
// so each side unfolds one constructor at a time — both sides are 0 at
// nil, and at cons both are suc of a tail's length, the mapped tail's
// on the left and the tail's on the right, which the hypothesis
// identifies.
var LengthMap = lengthMapThm{family.Add(registry.ProofEntry{
	Name: "LengthMap",
	Key:  "prop_cc3c260a3b1e8243",
	Build: family.Theorem("∀f:(A → B). ∀l:list(A). list_length(list_map(f, l)) = list_length(l)",
		func(a *Argument, f *Arrow[A, B], l *Expr[List[A]]) {
			a.Induct(l)
			a.Base(
				"f maps the empty list to the empty list, and the empty list has length 0 at either element type",
				Simp(Fwd(ListMapDef), Fwd(ListLengthDef), Fwd(ListLengthDef.Inst[B]())),
				Refl())
			a.Step(
				"a head in front maps to f(h) in front of the mapped tail; both "+
					"lengths are suc of a tail's length, and the hypothesis identifies them",
				func(b *Argument, ih Fact) {
					b.Show(
						"both sides are suc of a tail's length",
						Simp(Fwd(ListMapDef), Fwd(ListLengthDef), Fwd(ListLengthDef.Inst[B]())),
						ih.Rw(),
						TrivialNormalized())
				})
		}),
})}

// MapEqNil — the image of a list is empty exactly when the list is.
// Emptiness through length, read at B for the image and at A for the
// source, and mapping leaves the length alone, so the two sides become
// one and the same condition.
//
// The statement carries an annotation, `nil⟨A:B⟩`. The empty list on
// the left is the image's, so its element type is B; written bare it
// resolves at A and the statement does not parse — "equality type
// mismatch: left is list(var:B), right is list(var:A)". ⟨A:B⟩ pins the
// letter at that occurrence and leaves the one on the right at A.
var MapEqNil = mapEqNilThm{family.Add(registry.ProofEntry{
	Name: "MapEqNil",
	Key:  "prop_527b9481a8d3eae3",
	Build: family.Theorem("∀f:(A → B). ∀l:list(A). list_map(f, l) = nil⟨A:B⟩ ⇔ l = nil",
		func(a *Argument, f *Arrow[A, B], l *Expr[List[A]]) {
			a.Show(
				"emptiness read backwards as length 0 on both sides, "+
					"and the image's length folded back to the source's",
				Simp(Rev(LengthEqNil), Rev(LengthEqNil.Inst[B]()), Fwd(LengthMap)),
				TrivialNormalized())
		}),
})}

// MapAgreesOnMembers — Two maps with the same image list agree on every member of the list: by
// induction on the list, since the image lists of cons(h, t) are equal exactly when the images of
// the head and the image lists of the tail are.
var MapAgreesOnMembers = mapAgreesOnMembersThm{family.Add(registry.ProofEntry{
	Name: "MapAgreesOnMembers",
	Key:  "prop_3c0aa66168169e86",
	Build: family.Theorem(Statement{
		Binders: "∀f g:(A → B). ∀l:list(A). ∀x:A.",
		Hypotheses: []string{
			"list_map(f, l) = list_map(g, l)",
			"list_member(x, l)",
		},
		Conclusion: "f(x) = g(x)",
	}, func(a *Argument, f, g *Arrow[A, B], l *Expr[List[A]]) {
		a.Induct(l)
		a.Base(
			"the empty list has no member",
			Simp(Fwd(ListMemberDef)),
			Basic())
		a.Step(
			"the image lists of cons(h, t) agree when the images of h and the image lists of t do",
			func(b *Argument, ih Fact) {
				b.Show(
					"a member of cons(h, t) is h, or a member of t, where the induction hypothesis applies",
					Simp(Fwd(ListMapDef), Fwd(ListMemberDef), Fwd(ConsInjective)),
					By(Normalized, ih))
			})
	}),
})}

// MapCongruence — two functions that agree on the members of a list have one image of it, the
// converse of MapAgreesOnMembers: by induction on the list, the images of nil being nil, and at
// cons(h, t) the heads agreeing and the tails mapping alike.
var MapCongruence = mapCongruenceThm{family.Add(registry.ProofEntry{
	Name: "MapCongruence",
	Key:  "prop_fcea071df0775249",
	Build: family.Theorem(Statement{
		Binders: "∀f g:(A → B). ∀l:list(A).",
		Hypotheses: []string{
			"∀x:A. list_member(x, l) ⇒ f(x) = g(x)",
		},
		Conclusion: "list_map(f, l) = list_map(g, l)",
	}, func(a *Argument, f, g *Arrow[A, B]) {
		a.Induct("l")
		a.Base(
			"both maps of nil are nil",
			By(ListMapDef))
		a.Step(
			"at cons(h, t) the heads agree and the tails map alike",
			func(c *Argument, ih Fact) {
				args := c.StepArgs("h", "t")
				agree := c.Assume()
				tail := c.Have(
					"f and g agree on the members of t",
					"∀x:A. list_member(x, t) ⇒ f(x) = g(x)",
					By(agree, ListMemberDef))
				c.Show(
					"cons the agreeing heads onto the equal tails",
					Simp(Fwd(ListMapDef)),
					By(ih, tail, agree.At(args[0]), ListMemberDef))
			})
	}),
})}
