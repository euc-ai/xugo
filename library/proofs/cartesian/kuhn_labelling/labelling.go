// labelling.go — the count and the lemma: the reduced label turns a labelling
// of the grid into vertex labels 0, …, n; doors and rooms
// (nat_sum.DoorsAndRoomsParity), read at the Kuhn simplices, make a face
// count that is odd on the boundary odd inside; induction on the
// dimension makes the number of fully labelled simplices odd; and one of
// them is the cell the lemma asks for.

package kuhn_labelling

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/cartesian/carrier"
	"github.com/euc-ai/xugo/library/proofs/cartesian/kuhn"
	"github.com/euc-ai/xugo/library/proofs/iterate/nat/nat_sum"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The reduced label
// ---------------------------------------------------------------------------

// KuhnReducedIff — the reduced label is k exactly when k ≤ n, the labels
// below k are ⊥, and k is n or its label is ⊤. Such an r cuts the counted
// set down to the segment {i | i < r}, so the count is r; and one exists,
// the least coordinate that is n or labelled ⊤. The count is that r, so
// k is the count exactly when k has the three properties.
var KuhnReducedIff = kuhnReducedIffThm{family.Add(registry.ProofEntry{
	Name: "KuhnReducedIff",
	Key:  "prop_f8fbc28b643f662f",
	Reading: "No hypothesis: the counted set is the segment {k | k < r}, so card is read " +
		"only at a finite set. At n = 0 both sides say k = 0, and for k > n both are false.",
	Build: family.Theorem(Statement{
		Binders:    "∀n k:num. ∀l:((num → num) → num → bool). ∀x:(num → num).",
		Conclusion: "kuhn_reduced(n, l, x) = k ⇔ k ≤ n ∧ (∀j:num. j < k ⇒ ¬l(x, j)) ∧ (k = n ∨ l(x, k))",
		Abbrev: Abbrev{
			{Name: "stopsAt", Text: "λr:num. r ≤ n ∧ (∀j:num. j < r ⇒ ¬l(x, j)) ∧ (r = n ∨ l(x, r))"},
		},
	},
		func(a *Argument, n, k *Expr[Nat], l *Arrow2[Fun[Nat, Nat], Nat, Bool], x *Arrow[Nat, Nat]) {
			segment := a.Have(
				"a run of ⊥ labels cut at r makes the counted set the coordinates below r",
				"∀r:num. «stopsAt»(r) ⇒ {i:num | i < n ∧ (∀j:num. j ≤ i ⇒ ¬l(x, j))} = {i:num | i < r}",
				Derive(func(b *Argument) {
					b.FixAs[Nat]("r")
					run := b.Conjuncts(
						b.Assume(),
						"r is at most n",
						"the labels below r are ⊥",
						"r is n or its label is ⊤")
					reaches := b.Have(
						"a coordinate below r lies below n, and the labels up to it are ⊥",
						"∀i:num. i < r ⇒ i < n ∧ ∀j:num. j ≤ i ⇒ ¬l(x, j)",
						ByArith(run[0], run[1]))
					stops := b.Have(
						"a coordinate below n whose labels up to it are ⊥ lies below r",
						"∀i:num. i < n ∧ (∀j:num. j ≤ i ⇒ ¬l(x, j)) ⇒ i < r",
						Derive(func(c *Argument) {
							c.FixAs[Nat]("i")
							upTo := c.Assume()
							c.Do(run[2].SplitDisj(
								LeftHolds(
									"r is n, and i lies below n",
									Given(func(d *Argument, atN Fact) {
										d.Show(
											"so i lies below r",
											ByArith(atN, upTo))
									})),
								RightHolds(
									"the label at r is ⊤, so r is not among the coordinates up to i",
									Given(func(d *Argument, top Fact) {
										d.Show(
											"so i lies below r",
											ByArith(top, upTo))
									}))))
						}))
					b.Show(
						"so the two sets have the same points",
						BySets(reaches, stops))
				}))
			count := a.Have(
				"such an r is the count, the coordinates below r being r in number",
				"∀r:num. «stopsAt»(r) ⇒ kuhn_reduced(n, l, x) = r",
				Derive(func(b *Argument) {
					r := b.FixAs[Nat]("r")
					b.Show(
						"the count of the coordinates below r",
						By(
							segment.At(r),
							kuhnReducedDef.At(n, l, x),
							num_segment.HasSizeBelowStrict.At(r),
							cardinality.CardOfSized.At(b.TermAs[Set[Nat]]("{i:num | i < r}"), r)))
				}))
			r, first := a.ObtainAs[Nat](
				"the least coordinate that is n or labelled ⊤ is such an r",
				"∃r:num. «stopsAt»(r)",
				By(nat_order.WellOrdering.At(a.TermAs[Set[Nat]]("λi:num. i = n ∨ l(x, i)")), nat_order.NotLessThan))
			a.Iff()
			a.Forward(
				"the count is r, so k is r and has its three properties",
				func(b *Argument, reduced Fact) {
					same := b.Have(
						"k is r",
						"k = r",
						By(count.At(r), reduced, first))
					b.Show(
						"r has them",
						same.Rw(),
						By(first))
				})
			a.Backward(
				"a k with the three properties is the count",
				func(b *Argument, cut Fact) {
					b.Show(
						"by the count at k",
						By(count.At(k), cut))
				})
		}),
})}

// ---------------------------------------------------------------------------
// The parity induction
// ---------------------------------------------------------------------------

// KuhnSimplexLemma — vertex labels in 0, …, n + 1 on the (n + 1)-simplices:
// an odd number of boundary faces carrying 0, …, n makes an odd number of
// simplices carrying 0, …, n + 1. Doors and rooms, with the faces as doors
// and the simplices as rooms: a face lies in one simplex on the cube's
// boundary and in two inside it; a fully labelled simplex has one face
// carrying 0, …, n, the one opposite its vertex labelled n + 1, and any
// other simplex none or two, the faces opposite the two vertices that share
// a label. Faces of one simplex are counted by their opposite vertices.
var KuhnSimplexLemma = kuhnSimplexLemmaThm{family.Add(registry.ProofEntry{
	Name: "KuhnSimplexLemma",
	Key:  "prop_976d657f7821fde1",
	Reading: "The bound on the labels is load-bearing: a vertex labelled above n + 1 could give " +
		"a simplex one door without its being full. The dimension is n + 1, so KuhnFaceInterior " +
		"applies to every inner face; at p = 0 there is no face and the statement is vacuous.",
	Build: family.Sections(Statement{
		Binders: "∀p n:num. ∀label:((num → num) → num).",
		Hypotheses: []string{
			"∀s:set(num → num). kuhn_simplex(p, n + 1, s) ⇒ image(label, s) ⊆ {k:num | k ≤ n + 1}",
			"nat_odd(card(«boundaryDoors»))",
		},
		Conclusion: "nat_odd( " +
			"    card({s:set(num → num) | kuhn_simplex(p, n + 1, s) ∧ image(label, s) = {k:num | k ≤ n + 1}}))",
		Abbrev: Abbrev{
			{Name: "boundaryDoors", Text: "{f:set(num → num) | " +
				"    (∃s:set(num → num). ∃a:(num → num). kuhn_simplex(p, n + 1, s) ∧ a ∈ s ∧ f = delete(s, a)) ∧ " +
				"    image(label, f) = {k:num | k ≤ n} ∧ " +
				"    ∃j:num. " +
				"        j < n + 1 ∧ ((∀x:(num → num). x ∈ f ⇒ x(j) = 0) ∨ (∀x:(num → num). x ∈ f ⇒ x(j) = p))}"},
			{Name: "faces", Text: "{f:set(num → num) | " +
				"    ∃s:set(num → num). ∃a:(num → num). kuhn_simplex(p, n + 1, s) ∧ a ∈ s ∧ f = delete(s, a)}"},
		},
	},
		func(ctx *Script, headline string) *GoalStackNode {
			// The faces of a finite set s are the sets delete(s, b), b ∈ s, and
			// b ↦ delete(s, b) is one-to-one: the faces with a property are as
			// many as the vertices whose opposite face has it.
			faceCount := ctx.Lemma(Statement{
				Binders: "∀faces:set(set(A)). ∀P:(set(A) → bool). ∀s:set(A).",
				Hypotheses: []string{
					"finite(s)",
					"∀b:A. b ∈ s ⇒ delete(s, b) ∈ faces",
				},
				Conclusion: "card({f:set(A) | f ∈ faces ∧ (∃b:A. b ∈ s ∧ delete(s, b) = f) ∧ P(f)}) = " +
					"card({b:A | b ∈ s ∧ P(delete(s, b))})",
			},
				func(
					a *Argument,
					faces *Expr[Set[Set[A]]],
					P *Expr[Set[Set[A]]],
					s *Expr[Set[A]],
					finite, inFamily Fact,
				) {
					opposite := a.Have(
						"a face of s in the family with P is the face opposite a vertex whose face has P",
						"∀f:set(A). "+
							"    f ∈ faces ∧ (∃b:A. b ∈ s ∧ delete(s, b) = f) ∧ P(f) ⇔ "+
							"    ∃b:A. (b ∈ s ∧ P(delete(s, b))) ∧ f = delete(s, b)",
						By(Normalized, Broadcast, inFamily))
					asImage := a.Have(
						"so those faces are the image of those vertices under b ↦ delete(s, b)",
						"{f:set(A) | f ∈ faces ∧ (∃b:A. b ∈ s ∧ delete(s, b) = f) ∧ P(f)} = "+
							"image(λb:A. delete(s, b), {b:A | b ∈ s ∧ P(delete(s, b))})",
						BySets(opposite))
					oneToOne := a.Have(
						"distinct vertices leave distinct faces",
						"injective_on({b:A | b ∈ s ∧ P(delete(s, b))}, λb:A. delete(s, b))",
						Simp(Fwd(functions.InjectiveOnDef)),
						BySets())
					a.Show(
						"and a one-to-one image has as many points as its source",
						asImage.Rw(),
						By(finite, oneToOne, cardinality.CardImageInj, finite_set.FiniteRestrict))
				})

			// The labels up to n are those up to n + 1 short of n + 1.
			belowTop := ctx.Lemma(
				"∀n k:num. k ≤ n ⇔ k ≤ n + 1 ∧ ¬(k = n + 1)",
				func(a *Argument, n, k *Expr[Nat]) {
					a.Show(
						"k ≤ n exactly when k ≤ n + 1 and k is not n + 1",
						ByArith())
				})

			// m + 1 vertices carrying all of the m + 1 labels 0, …, m carry each
			// label once.
			ontoOnce := ctx.Lemma(Statement{
				Binders: "∀m:num. ∀label:(A → num). ∀t:set(A).",
				Hypotheses: []string{
					"has_size(t, m + 1)",
					"image(label, t) = {k:num | k ≤ m}",
				},
				Conclusion: "injective_on(t, label)",
			},
				func(a *Argument, m *Expr[Nat], label *Arrow[A, Nat], t *Expr[Set[A]], size, onto Fact) {
					labels := a.TermAs[Set[Nat]]("{k:num | k ≤ m}")
					count := a.TermAs[Nat]("m + 1")
					a.Show(
						"a map of m + 1 points onto m + 1 values is one-to-one",
						ByArith(
							size,
							onto,
							cardinality.ImageImpInjectiveGen.At(t, labels, label),
							num_segment.HasSizeBelow.At(m),
							cardinality.HasSizeDef.At(t, count),
							cardinality.HasSizeDef.At(labels, count)))
				})

			// A fully labelled simplex has one face carrying 0, …, n.
			oneDoor := ctx.Lemma(Statement{
				Binders: "∀n:num. ∀label:(A → num). ∀s:set(A).",
				Hypotheses: []string{
					"has_size(s, n + 2)",
					"image(label, s) = {k:num | k ≤ n + 1}",
				},
				Conclusion: "card({b:A | b ∈ s ∧ image(label, delete(s, b)) = {k:num | k ≤ n}}) = 1",
			},
				func(arg *Argument, n *Expr[Nat], label *Arrow[A, Nat], s *Expr[Set[A]], size, onto Fact) {
					top := arg.TermAs[Nat]("n + 1")
					oneToOne := arg.Have(
						"n + 2 vertices onto n + 2 labels: no label is carried twice",
						"injective_on(s, label)",
						ByArith(
							size,
							onto,
							cardinality.HasSizeDef.At(s, arg.TermAs[Nat]("n + 2")),
							cardinality.HasSizeDef.At(s, arg.TermAs[Nat]("n + 1 + 1")),
							At(ontoOnce, top, label, s)))
					v, carries := arg.ObtainAs[A](
						"some vertex v carries the label n + 1",
						"∃v:A. v ∈ s ∧ label(v) = n + 1",
						BySets(onto, nat_order.LessEqRefl.At(top)))
					vertex := arg.Conjuncts(
						carries,
						"v lies in s",
						"v carries n + 1")
					only := arg.Have(
						"no other vertex carries v's label",
						"∀x:A. x ∈ s ∧ label(x) = label(v) ⇒ x = v",
						By(oneToOne, vertex[0], functions.InjectiveOnDef))
					door := arg.Have(
						"the face opposite v carries 0, …, n",
						"image(label, delete(s, v)) = {k:num | k ≤ n}",
						CalcEq(
							Leg(
								arg.TermAs[Set[Nat]]("delete(image(label, s), label(v))"),
								"deleting v deletes its label, which no other vertex carries",
								By(only, set_image.ImageDeleteInj.At(label, s, v))),
							Leg(
								arg.TermAs[Set[Nat]]("delete({k:num | k ≤ n + 1}, n + 1)"),
								"the labels of s are 0, …, n + 1, and v carries n + 1",
								onto.Rw(),
								vertex[1].Rw(),
								Basic()),
							FinalLeg(
								"and 0, …, n + 1 less n + 1 is 0, …, n",
								BySets(At(belowTop, n)))))
					doorVertex := arg.Have(
						"the face opposite a vertex b carries 0, …, n exactly when b is v",
						"∀b:A. b ∈ s ∧ image(label, delete(s, b)) = {k:num | k ≤ n} ⇔ b = v",
						Derive(func(c *Argument) {
							c.FixAs[A]("b")
							c.Iff()
							c.Forward(
								"the face opposite any other vertex keeps v, and n + 1 is not among 0, …, n",
								func(d *Argument, isDoor Fact) {
									d.Show(
										"so b is v",
										BySets(isDoor, vertex[1], vertex[0], At(belowTop, n, top)))
								})
							c.Backward(
								"the face opposite v is the door found above",
								func(d *Argument, isV Fact) {
									d.Show(
										"v lies in s and its face carries 0, …, n",
										By(isV, door, vertex[0]))
								})
						}))
					doors := arg.Have(
						"so v is the one vertex whose opposite face carries 0, …, n",
						"{b:A | b ∈ s ∧ image(label, delete(s, b)) = {k:num | k ≤ n}} = {v}",
						BySets(doorVertex))
					arg.Show(
						"one vertex, one door",
						By(doors, cardinality.CardSing))
				})

			// Any other simplex has none or two.
			noneOrTwo := ctx.Lemma(Statement{
				Binders: "∀n:num. ∀label:(A → num). ∀s:set(A).",
				Hypotheses: []string{
					"has_size(s, n + 2)",
					"image(label, s) ⊆ {k:num | k ≤ n + 1}",
					"¬(image(label, s) = {k:num | k ≤ n + 1})",
				},
				Conclusion: "card({b:A | b ∈ s ∧ image(label, delete(s, b)) = {k:num | k ≤ n}}) = 0 ∨ " +
					"card({b:A | b ∈ s ∧ image(label, delete(s, b)) = {k:num | k ≤ n}}) = 2",
			},
				func(
					arg *Argument,
					n *Expr[Nat],
					label *Arrow[A, Nat],
					s *Expr[Set[A]],
					size, bounded, notFull Fact,
				) {
					someDoor := arg.Assuming(
						arg.Term("∃c:A. c ∈ s ∧ image(label, delete(s, c)) = {k:num | k ≤ n}"),
						"with no face carrying 0, …, n there is no vertex to count",
						Given(func(b *Argument, none Fact) {
							noDoor := b.Have(
								"no face of s carries 0, …, n",
								"∀c:A. ¬(c ∈ s ∧ image(label, delete(s, c)) = {k:num | k ≤ n})",
								By(Normalized, none))
							empty := b.Have(
								"so no vertex is counted",
								"{b:A | b ∈ s ∧ image(label, delete(s, b)) = {k:num | k ≤ n}} = ∅",
								BySets(noDoor))
							b.Show(
								"and the count is 0",
								By(empty, cardinality.CardClauses))
						}))
					c, cDoor := arg.UnpackAs[A](someDoor, "c")
					first := arg.Conjuncts(
						cDoor,
						"c lies in s",
						"the face opposite c carries 0, …, n")
					cLabel := arg.Have(
						"c carries a label up to n: were it n + 1, s would carry every label 0, …, n + 1",
						"label(c) ≤ n",
						BySets(notFull, At(belowTop, n), first[1], first[0], bounded))
					d, twin := arg.ObtainAs[A](
						"so another vertex d carries the label of c",
						"∃d:A. d ∈ delete(s, c) ∧ label(d) = label(c)",
						BySets(cLabel, first[1]))
					second := arg.Conjuncts(
						twin,
						"d lies in s and is not c",
						"d carries the label of c")
					dDoor := arg.Have(
						"the face opposite d carries the same labels as the face opposite c",
						"image(label, delete(s, d)) = {k:num | k ≤ n}",
						BySets(first[1], second[1], first[0], second[0]))
					oneToOne := arg.Have(
						"the n + 1 vertices of a face carrying 0, …, n carry each label once",
						"∀e:A. e ∈ s ∧ image(label, delete(s, e)) = {k:num | k ≤ n} ⇒ injective_on(delete(s, e), label)",
						Derive(func(b *Argument) {
							e := b.FixAs[A]("e")
							isDoor := b.Assume()
							face := b.TermAs[Set[A]]("delete(s, e)")
							b.Show(
								"the face has n + 1 vertices, onto its n + 1 labels",
								ByArith(
									size,
									isDoor,
									cardinality.HasSizeDef.At(s, b.TermAs[Nat]("n + 2")),
									cardinality.HasSizeDef.At(face, b.TermAs[Nat]("n + 1")),
									cardinality.CardDelete.At(s, e),
									finite_set.FiniteDeleteImp.At(s, e),
									At(ontoOnce, n, label, face)))
						}))
					doorVertex := arg.Have(
						"the face opposite a vertex e carries 0, …, n exactly when e is c or d",
						"∀e:A. e ∈ s ∧ image(label, delete(s, e)) = {k:num | k ≤ n} ⇔ e = c ∨ e = d",
						Derive(func(b *Argument) {
							e := b.FixAs[A]("e")
							b.Iff()
							b.Forward(
								"the face opposite any other vertex keeps c and d, two vertices with one label",
								func(f *Argument, isDoor Fact) {
									other := f.SupposeNot()
									both := f.Have(
										"then c and d lie in the face opposite e",
										"c ∈ delete(s, e) ∧ d ∈ delete(s, e)",
										BySets(other, first[0], second[0]))
									same := f.Have(
										"where each label is carried once, so c is d",
										"c = d",
										By(
											both,
											isDoor,
											oneToOne.At(e),
											second[1],
											functions.InjectiveOnDef.At(f.TermAs[Set[A]]("delete(s, e)"), label)))
									f.Show(
										"but d is not c",
										BySets(same, second[0]))
								})
							b.Backward(
								"the faces opposite c and opposite d are the two found above",
								func(f *Argument, isCOrD Fact) {
									f.Show(
										"e lies in s and its face carries 0, …, n",
										BySets(isCOrD, first[1], dDoor, first[0], second[0]))
								})
						}))
					pair := arg.Have(
						"so c and d are the vertices whose opposite faces carry 0, …, n",
						"{b:A | b ∈ s ∧ image(label, delete(s, b)) = {k:num | k ≤ n}} = {d, c}",
						BySets(doorVertex))
					arg.Show(
						"two distinct vertices, two doors",
						By(
							pair,
							second[0],
							cardinality.HasSizePair.At(d, c),
							cardinality.CardOfSized.At(arg.TermAs[Set[A]]("{d, c}"), arg.TermAs[Nat]("2")),
							set_basic.InDelete.At(s, d, c)))
				})

			return ctx.Theorem(headline,
				func(a *Argument, p, n *Expr[Nat], label *Arrow[Fun[Nat, Nat], Nat], bounded, oddBoundary Fact) {
					dim := a.TermAs[Nat]("n + 1")
					faces := a.TermAs[Set[Set[Fun[Nat, Nat]]]]("«faces»")
					simplices := a.TermAs[Set[Set[Fun[Nat, Nat]]]]("{s:set(num → num) | kuhn_simplex(p, n + 1, s)}")
					incidence := a.TermAs[Fun2[Set[Fun[Nat, Nat]], Set[Fun[Nat, Nat]], Bool]](
						"λf:set(num → num). λt:set(num → num). ∃b:(num → num). b ∈ t ∧ delete(t, b) = f")
					boundary := a.TermAs[Set[Set[Fun[Nat, Nat]]]](
						"λf:set(num → num). ∃j:num. " +
							"    j < n + 1 ∧ ((∀x:(num → num). x ∈ f ⇒ x(j) = 0) ∨ (∀x:(num → num). x ∈ f ⇒ x(j) = p))")
					full := a.TermAs[Set[Set[Fun[Nat, Nat]]]](
						"λs:set(num → num). image(label, s) = {k:num | k ≤ n + 1}")
					door := a.TermAs[Set[Set[Fun[Nat, Nat]]]]("λf:set(num → num). image(label, f) = {k:num | k ≤ n}")
					vertices := a.Have(
						"an (n + 1)-simplex has n + 2 vertices",
						"∀s:set(num → num). kuhn_simplex(p, n + 1, s) ⇒ has_size(s, n + 2)",
						Derive(func(b *Argument) {
							b.FixAs[Set[Fun[Nat, Nat]]]("s")
							simplex := b.Unfolded(b.Assume(), kuhn.KuhnSimplexDef)
							b.Show(
								"n + 1 + 1 points are n + 2",
								RingNf(),
								By(simplex))
						}))
					finiteSimplex := a.Have(
						"an (n + 1)-simplex is finite",
						"∀s:set(num → num). kuhn_simplex(p, n + 1, s) ⇒ finite(s)",
						Derive(func(b *Argument) {
							s := b.FixAs[Set[Fun[Nat, Nat]]]("s")
							simplex := b.Assume()
							b.Show(
								"it has n + 2 points",
								By(simplex, vertices.At(s), cardinality.HasSizeDef.At(s, b.TermAs[Nat]("n + 2"))))
						}))
					ownFaces := a.Have(
						"the faces of a simplex are faces",
						"∀s:set(num → num). kuhn_simplex(p, n + 1, s) ⇒ ∀b:(num → num). b ∈ s ⇒ delete(s, b) ∈ «faces»",
						Derive(func(b *Argument) {
							b.FixAs[Set[Fun[Nat, Nat]]]("s")
							simplex := b.Assume()
							b.Show(
								"each delete(s, b) is a face of the simplex s",
								By(simplex))
						}))

					finiteFaces := a.Have(
						"the faces are finitely many",
						"finite(«faces»)",
						Derive(func(b *Argument) {
							points := b.Have(
								"the simplices hold finitely many points, finitely many finite sets",
								"finite(⋃{s:set(num → num) | kuhn_simplex(p, n + 1, s)})",
								By(finiteSimplex, kuhn.KuhnSimplicesFinite.At(p, dim), finite_set.FiniteUnions))
							within := b.Have(
								"a face is a set of those points",
								"«faces» ⊆ {t:set(num → num) | t ⊆ ⋃{s:set(num → num) | kuhn_simplex(p, n + 1, s)}}",
								BySets())
							b.Show(
								"so the faces lie in the finite powerset of those points",
								By(points, within, finite_set.FinitePowerset, finite_set.FiniteSubset))
						}))

					// A face in a boundary plane lies in one simplex, a face in
					// none in two: the face counts at dimension n + 1, read at
					// the simplex the face comes from.
					boundaryOne := a.Have(
						"a face in a boundary plane lies in one simplex",
						Statement{
							Binders: "∀f:set(num → num).",
							Hypotheses: []string{
								"f ∈ «faces»",
								"∃j:num. j < n + 1 ∧ ((∀x:(num → num). x ∈ f ⇒ x(j) = 0) ∨ (∀x:(num → num). x ∈ f ⇒ x(j) = p))",
							},
							Conclusion: "card({t:set(num → num) | " +
								"        kuhn_simplex(p, n + 1, t) ∧ ∃b:(num → num). b ∈ t ∧ delete(t, b) = f}) = " +
								"1",
						},
						Derive(func(b *Argument) {
							b.FixAs[Set[Fun[Nat, Nat]]]("f")
							given := b.Conjuncts(
								b.Assume(),
								"f is a face",
								"f lies in a boundary plane")
							s, v, opposite := b.Unpack2As[Set[Fun[Nat, Nat]], Fun[Nat, Nat]](given[0], "s", "v")
							face := b.Conjuncts(
								opposite,
								"s is a simplex",
								"v lies in s",
								"f is the face of s opposite v")
							j, plane := b.UnpackAs[Nat](given[1], "j")
							b.Do(face[2].Rw())
							inPlane := b.Conjuncts(
								plane,
								"j is a coordinate",
								"the face lies in x(j) = 0 or in x(j) = p")
							b.Do(inPlane[1].SplitDisj(
								LeftHolds(
									"in x(j) = 0 only s holds it",
									Given(func(c *Argument, zero Fact) {
										c.Show(
											"one simplex",
											By(zero, inPlane[0], face[0], face[1], kuhn.KuhnFaceZeroPlane.At(p, dim, j, s, v)))
									})),
								RightHolds(
									"in x(j) = p only s holds it",
									Given(func(c *Argument, top Fact) {
										c.Show(
											"one simplex",
											By(top, inPlane[0], face[0], face[1], kuhn.KuhnFaceTopPlane.At(p, dim, j, s, v)))
									}))))
						}))
					innerTwo := a.Have(
						"a face in no boundary plane lies in two simplices",
						Statement{
							Binders: "∀f:set(num → num).",
							Hypotheses: []string{
								"f ∈ «faces»",
								"¬∃j:num. j < n + 1 ∧ ((∀x:(num → num). x ∈ f ⇒ x(j) = 0) ∨ (∀x:(num → num). x ∈ f ⇒ x(j) = p))",
							},
							Conclusion: "card({t:set(num → num) | " +
								"        kuhn_simplex(p, n + 1, t) ∧ ∃b:(num → num). b ∈ t ∧ delete(t, b) = f}) = " +
								"2",
						},
						Derive(func(b *Argument) {
							b.FixAs[Set[Fun[Nat, Nat]]]("f")
							given := b.Conjuncts(
								b.Assume(),
								"f is a face",
								"f lies in no boundary plane")
							s, v, opposite := b.Unpack2As[Set[Fun[Nat, Nat]], Fun[Nat, Nat]](given[0], "s", "v")
							face := b.Conjuncts(
								opposite,
								"s is a simplex",
								"v lies in s",
								"f is the face of s opposite v")
							b.Do(face[2].Rw())
							inside := b.Have(
								"off every boundary plane, the face has points off x(j) = 0 and off x(j) = p",
								Statement{
									Binders: "∀j:num.",
									Hypotheses: []string{
										"j < n + 1",
									},
									Conclusion: "(∃x:(num → num). x ∈ delete(s, v) ∧ ¬(x(j) = 0)) ∧ " +
										"(∃x:(num → num). x ∈ delete(s, v) ∧ ¬(x(j) = p))",
								},
								By(Normalized, given[1]))
							b.Show(
								"two simplices, the dimension n + 1 being positive",
								ByArith(inside, face[0], face[1], kuhn.KuhnFaceInterior.At(p, dim, s, v)))
						}))

					// Doors are counted per simplex by their opposite vertices.
					fullOne := a.Have(
						"a fully labelled simplex has one door",
						Statement{
							Binders: "∀s:set(num → num).",
							Hypotheses: []string{
								"kuhn_simplex(p, n + 1, s)",
								"image(label, s) = {k:num | k ≤ n + 1}",
							},
							Conclusion: "card({f:set(num → num) | " +
								"        f ∈ «faces» ∧ " +
								"        (∃b:(num → num). b ∈ s ∧ delete(s, b) = f) ∧ " +
								"        image(label, f) = {k:num | k ≤ n}}) = " +
								"1",
						},
						Derive(func(b *Argument) {
							s := b.FixAs[Set[Fun[Nat, Nat]]]("s")
							given := b.Conjuncts(
								b.Assume(),
								"s is a simplex",
								"s is fully labelled")
							b.Show(
								"its doors are counted by its vertices, and one vertex opens one",
								By(
									finiteSimplex.At(s),
									given[0],
									given[1],
									vertices.At(s),
									ownFaces.At(s),
									At(ctx.AtTypeVars(faceCount, TypeBinder.BindA[Fun[Nat, Nat]]()),
										faces,
										door,
										s),
									At(ctx.AtTypeVars(oneDoor, TypeBinder.BindA[Fun[Nat, Nat]]()), n, label, s)))
						}))
					otherNoneOrTwo := a.Have(
						"any other simplex has none or two",
						Statement{
							Binders: "∀s:set(num → num).",
							Hypotheses: []string{
								"kuhn_simplex(p, n + 1, s)",
								"¬(image(label, s) = {k:num | k ≤ n + 1})",
							},
							Conclusion: "card({f:set(num → num) | " +
								"        f ∈ «faces» ∧ " +
								"        (∃b:(num → num). b ∈ s ∧ delete(s, b) = f) ∧ " +
								"        image(label, f) = {k:num | k ≤ n}}) = " +
								"0 ∨ " +
								"card({f:set(num → num) | " +
								"        f ∈ «faces» ∧ " +
								"        (∃b:(num → num). b ∈ s ∧ delete(s, b) = f) ∧ " +
								"        image(label, f) = {k:num | k ≤ n}}) = " +
								"2",
						},
						Derive(func(b *Argument) {
							s := b.FixAs[Set[Fun[Nat, Nat]]]("s")
							given := b.Conjuncts(
								b.Assume(),
								"s is a simplex",
								"s is not fully labelled")
							b.Show(
								"its doors are counted by its vertices, and none or two vertices open one",
								By(
									finiteSimplex.At(s),
									given[0],
									given[1],
									vertices.At(s),
									ownFaces.At(s),
									bounded.At(s),
									At(ctx.AtTypeVars(faceCount, TypeBinder.BindA[Fun[Nat, Nat]]()),
										faces,
										door,
										s),
									At(ctx.AtTypeVars(noneOrTwo, TypeBinder.BindA[Fun[Nat, Nat]]()), n, label, s)))
						}))

					a.Show(
						"doors and rooms: the full simplices are as odd in number as the boundary doors",
						By(
							finiteFaces,
							kuhn.KuhnSimplicesFinite.At(p, dim),
							boundaryOne,
							innerTwo,
							fullOne,
							otherNoneOrTwo,
							oddBoundary,
							nat_sum.DoorsAndRoomsParity.At(incidence, faces, simplices, boundary, full, door)))
				})
		}),
})}

// KuhnInduction — the step in the dimension: if the labelling read on the
// top face x(n) = p has an odd number of fully labelled n-simplices, the
// labelling has an odd number of fully labelled (n + 1)-simplices. Every
// boundary door labelled 0, …, n lies in the plane x(n) = p, where setting
// coordinate n to p and truncating match the doors one for one with the
// fully labelled n-simplices; KuhnSimplexLemma then counts.
var KuhnInduction = kuhnInductionThm{family.Add(registry.ProofEntry{
	Name: "KuhnInduction",
	Key:  "prop_5a8f6baa0eecee91",
	Reading: "All three boundary readings enter: the conditions at 0 and at p below n keep every " +
		"boundary door in the plane x(n) = p, and the condition at p at coordinate n makes the reduced " +
		"labels at n and n + 1 agree there. At p = 0 the two conditions contradict at the zero point.",
	Build: family.Theorem(Statement{
		Binders: "∀p n:num. ∀l:((num → num) → num → bool).",
		Hypotheses: []string{
			"∀x:(num → num). ∀i:num. x ∈ kuhn_grid(p, n + 1) ∧ i < n + 1 ∧ x(i) = 0 ⇒ ¬l(x, i)",
			"∀x:(num → num). ∀i:num. x ∈ kuhn_grid(p, n + 1) ∧ i < n + 1 ∧ x(i) = p ⇒ l(x, i)",
			"nat_odd(card({f:set(num → num) | " +
				"            kuhn_simplex(p, n, f) ∧ " +
				"            image(λx:(num → num). kuhn_reduced(n, l, λi:num. COND(i = n, p, x(i))), f) = " +
				"            {k:num | k ≤ n}}))",
		},
		Conclusion: "nat_odd(card({s:set(num → num) | " +
			"            kuhn_simplex(p, n + 1, s) ∧ image(kuhn_reduced(n + 1, l), s) = {k:num | k ≤ n + 1}}))",
		Abbrev: Abbrev{
			{Name: "onTop", Text: "λx:(num → num). λi:num. COND(i = n, p, x(i))"},
			{Name: "full", Text: "{f:set(num → num) | " +
				"    kuhn_simplex(p, n, f) ∧ " +
				"    image(λx:(num → num). kuhn_reduced(n, l, «onTop»(x)), f) = {k:num | k ≤ n}}"},
			{Name: "boundaryDoors", Text: "{f:set(num → num) | " +
				"    (∃s:set(num → num). ∃a:(num → num). kuhn_simplex(p, n + 1, s) ∧ a ∈ s ∧ f = delete(s, a)) ∧ " +
				"    image(kuhn_reduced(n + 1, l), f) = {k:num | k ≤ n} ∧ " +
				"    ∃j:num. " +
				"        j < n + 1 ∧ ((∀x:(num → num). x ∈ f ⇒ x(j) = 0) ∨ (∀x:(num → num). x ∈ f ⇒ x(j) = p))}"},
		},
	}, func(
		a *Argument,
		p, n *Expr[Nat],
		l *Arrow2[Fun[Nat, Nat], Nat, Bool],
		zeroSide, topSide, oddFull Fact,
	) {
		succ := a.TermAs[Nat]("n + 1")
		zero := a.TermAs[Nat]("0")
		flat := a.TermAs[Fun[Nat, Nat]]("λi:num. 0")
		origin := a.TermAs[Fun[Nat, Nat]]("tuple_take(n + 1, λi:num. 0)")
		originIn := a.Have(
			"the origin lies in the grid",
			"tuple_take(n + 1, λi:num. 0) ∈ kuhn_grid(p, n + 1)",
			Unfold(kuhn.KuhnGridDef),
			ByArith(carrier.TakeClosed.At(succ, flat), carrier.TupleTakeDef))
		positive := a.Have(
			"p is positive: at p = 0 the two boundary conditions disagree at the origin",
			"0 < p",
			ByArith(
				zeroSide.At(origin, zero),
				topSide.At(origin, zero),
				originIn,
				carrier.TupleTakeDef.At(succ, flat, zero)))

		onTop := a.Have(
			"a grid point set to p at coordinate n lies in the "+
				"grid one dimension up, and truncation gives it back",
			Statement{
				Binders: "∀x:(num → num).",
				Hypotheses: []string{
					"x ∈ kuhn_grid(p, n)",
				},
				Conclusion: "«onTop»(x) ∈ kuhn_grid(p, n + 1) ∧ tuple_take(n, «onTop»(x)) = x",
			},
			Derive(func(b *Argument) {
				x := b.FixAs[Fun[Nat, Nat]]("x")
				xIn := b.Assume()
				b.Show(
					"p ≤ p, so x set to p at coordinate n is a grid point one dimension up, truncating back to x",
					By(xIn, At(kuhn.KuhnGridExtend, p, n, x, p), nat_order.LessEqRefl.At(p)))
			}))
		agree := a.Have(
			"on the plane x(n) = p the reduced labels at n + 1 and at n agree, the label at n being ⊤ there",
			Statement{
				Binders: "∀x:(num → num).",
				Hypotheses: []string{
					"x ∈ kuhn_grid(p, n)",
				},
				Conclusion: "kuhn_reduced(n + 1, l, «onTop»(x)) = kuhn_reduced(n, l, «onTop»(x))",
			},
			Derive(func(b *Argument) {
				x := b.FixAs[Fun[Nat, Nat]]("x")
				xIn := b.Assume()
				up := b.TermAs[Fun[Nat, Nat]]("«onTop»(x)")
				label := b.TermAs[Nat]("kuhn_reduced(n, l, «onTop»(x))")
				b.Show(
					"the run of ⊥ stops at n at the latest either way",
					ByArith(
						onTop.At(x),
						xIn,
						topSide.At(up, n),
						KuhnReducedIff.At(n, label, l, up),
						KuhnReducedIff.At(succ, label, l, up)))
			}))
		labels := a.Have(
			"so on an n-simplex set to p at coordinate n the labels at n + 1 are the ones the hypothesis reads",
			Statement{
				Binders: "∀f:set(num → num).",
				Hypotheses: []string{
					"f ⊆ kuhn_grid(p, n)",
				},
				Conclusion: "image(kuhn_reduced(n + 1, l), image(«onTop», f)) = " +
					"image(λx:(num → num). kuhn_reduced(n, l, «onTop»(x)), f)",
			},
			Derive(func(b *Argument) {
				b.FixAs[Set[Fun[Nat, Nat]]]("f")
				inGrid := b.Assume()
				b.Show(
					"point by point, by the agreement",
					BySets(agree, inGrid))
			}))

		zeroLabel := a.Have(
			"in a plane x(j) = 0 no point has reduced label j, its label at j being ⊥",
			Statement{
				Binders: "∀x:(num → num). ∀j:num.",
				Hypotheses: []string{
					"x ∈ kuhn_grid(p, n + 1)",
					"j < n + 1",
					"x(j) = 0",
				},
				Conclusion: "¬(kuhn_reduced(n + 1, l, x) = j)",
			},
			Derive(func(b *Argument) {
				x := b.FixAs[Fun[Nat, Nat]]("x")
				j := b.FixAs[Nat]("j")
				inPlane := b.Assume()
				b.Show(
					"a reduced label j below n + 1 needs the label at j to be ⊤",
					ByArith(zeroSide.At(x, j), inPlane, KuhnReducedIff.At(succ, j, l, x)))
			}))
		topLabel := a.Have(
			"in a plane x(j) = p no reduced label exceeds j, its label at j being ⊤",
			Statement{
				Binders: "∀x:(num → num). ∀j:num.",
				Hypotheses: []string{
					"x ∈ kuhn_grid(p, n + 1)",
					"j < n + 1",
					"x(j) = p",
				},
				Conclusion: "kuhn_reduced(n + 1, l, x) ≤ j",
			},
			Derive(func(b *Argument) {
				x := b.FixAs[Fun[Nat, Nat]]("x")
				j := b.FixAs[Nat]("j")
				inPlane := b.Assume()
				label := b.TermAs[Nat]("kuhn_reduced(n + 1, l, x)")
				b.Show(
					"a reduced label above j needs the label at j to be ⊥",
					ByArith(topSide.At(x, j), inPlane, KuhnReducedIff.At(succ, label, l, x)))
			}))

		doorsTruncated := a.Have(
			"truncating a boundary door gives a fully labelled "+
				"n-simplex, which set to p at coordinate n is the door",
			Statement{
				Binders: "∀g:set(num → num).",
				Hypotheses: []string{
					"g ∈ «boundaryDoors»",
				},
				Conclusion: "image(tuple_take(n), g) ∈ «full» ∧ image(«onTop», image(tuple_take(n), g)) = g",
			},
			Derive(func(b *Argument) {
				b.FixAs[Set[Fun[Nat, Nat]]]("g")
				door := b.Conjuncts(
					b.Assume(),
					"g is a face of an (n + 1)-simplex",
					"g is labelled 0, …, n",
					"g lies in a boundary plane")
				s, removed, isFace := b.Unpack2As[Set[Fun[Nat, Nat]], Fun[Nat, Nat]](door[0], "s", "a")
				face := b.Conjuncts(
					isFace,
					"s is an (n + 1)-simplex",
					"a lies in s",
					"g is s without a")
				top := b.Have(
					"g lies in the plane x(n) = p",
					"∀x:(num → num). x ∈ g ⇒ x(n) = p",
					Derive(func(c *Argument) {
						simplexUp := c.Conjuncts(
							c.Unfolded(face[0], kuhn.KuhnSimplexDef),
							"s lies in the grid",
							"s has n + 2 points",
							"any two points of s are comparable")
						j, inPlane := c.UnpackAs[Nat](door[2], "j")
						plane := c.Conjuncts(
							inPlane,
							"j is a coordinate",
							"g lies in x(j) = 0 or in x(j) = p")
						onGrid := c.Have(
							"g lies in the grid",
							"∀x:(num → num). x ∈ g ⇒ x ∈ kuhn_grid(p, n + 1)",
							BySets(face[2], simplexUp[0]))
						attained := c.Have(
							"every label 0, …, n is taken on g",
							"∀k:num. k ≤ n ⇒ ∃x:(num → num). x ∈ g ∧ kuhn_reduced(n + 1, l, x) = k",
							BySets(door[1]))
						c.Cases(c.Term("∀x:(num → num). x ∈ g ⇒ x(j) = 0"))
						c.When(
							"in a plane x(j) = 0 the label j taken on g is impossible",
							func(d *Argument, zeroPlane Fact) {
								z, labelled := d.ObtainAs[Fun[Nat, Nat]](
									"some point of g has reduced label j",
									"∃z:(num → num). z ∈ g ∧ kuhn_reduced(n + 1, l, z) = j",
									ByArith(attained.At(j), plane[0]))
								d.Show(
									"which its plane forbids",
									By(zeroLabel.At(z, j), zeroPlane.At(z), onGrid.At(z), plane[0], labelled))
							})
						c.Otherwise(
							"so g lies in a plane x(j) = p, and the label n taken on g forces j = n",
							func(d *Argument, notZero Fact) {
								topPlane := d.Have(
									"g lies in the plane x(j) = p",
									"∀x:(num → num). x ∈ g ⇒ x(j) = p",
									By(plane[1], notZero))
								z, labelled := d.ObtainAs[Fun[Nat, Nat]](
									"some point of g has reduced label n",
									"∃z:(num → num). z ∈ g ∧ kuhn_reduced(n + 1, l, z) = n",
									ByArith(attained.At(n)))
								atN := d.Have(
									"so j = n",
									"j = n",
									ByArith(topLabel.At(z, j), topPlane.At(z), onGrid.At(z), plane[0], labelled))
								d.Show(
									"the plane is x(n) = p",
									By(Normalized, topPlane, atN))
							})
					}))
				topFace := b.Have(
					"so does s without a",
					"∀x:(num → num). x ∈ delete(s, a) ⇒ x(n) = p",
					By(Normalized, top, face[2]))
				truncated := b.Have(
					"so the truncation of g is an n-simplex, which set to p at coordinate n is g",
					"kuhn_simplex(p, n, image(tuple_take(n), g)) ∧ image(«onTop», image(tuple_take(n), g)) = g",
					By(
						Normalized,
						face[0],
						face[1],
						topFace,
						face[2],
						At(kuhn.KuhnTopFaceTruncation, p, n, s, removed)))
				truncatedIn := b.Have(
					"the truncation lies in the grid",
					"image(tuple_take(n), g) ⊆ kuhn_grid(p, n)",
					By(truncated, kuhn.KuhnSimplexDef))
				truncatedSet := b.TermAs[Set[Fun[Nat, Nat]]]("image(tuple_take(n), g)")
				b.Show(
					"its labels, read on the top face, are g's: 0, …, n",
					By(labels.At(truncatedSet), truncatedIn, door[1], truncated))
			}))

		fullOnTop := a.Have(
			"a fully labelled n-simplex set to p at coordinate "+
				"n is a boundary door, and truncation gives it back",
			Statement{
				Binders: "∀f:set(num → num).",
				Hypotheses: []string{
					"f ∈ «full»",
				},
				Conclusion: "image(«onTop», f) ∈ «boundaryDoors» ∧ image(tuple_take(n), image(«onTop», f)) = f",
			},
			Derive(func(b *Argument) {
				f := b.FixAs[Set[Fun[Nat, Nat]]]("f")
				full := b.Conjuncts(
					b.Assume(),
					"f is an n-simplex",
					"f is fully labelled")
				inGrid := b.Have(
					"f lies in the grid",
					"f ⊆ kuhn_grid(p, n)",
					By(full[0], kuhn.KuhnSimplexDef))
				back := b.Have(
					"truncating f on the top face gives f back",
					"image(tuple_take(n), image(«onTop», f)) = f",
					BySets(onTop, inGrid))
				isFace := b.Have(
					"on the top face it is a face of an (n + 1)-simplex",
					"∃s:set(num → num). ∃a:(num → num). "+
						"    kuhn_simplex(p, n + 1, s) ∧ a ∈ s ∧ image(«onTop», f) = delete(s, a)",
					By(positive, full[0], At(kuhn.KuhnRaisedSimplexFace, p, n, f)))
				topPlane := b.Have(
					"lying in the plane x(n) = p",
					"∀x:(num → num). x ∈ image(«onTop», f) ⇒ x(n) = p",
					BySets())
				labelsUp := b.Have(
					"labelled 0, …, n",
					"image(kuhn_reduced(n + 1, l), image(«onTop», f)) = {k:num | k ≤ n}",
					By(labels.At(f), inGrid, full[1]))
				nBelow := b.Have(
					"n is a coordinate",
					"n < n + 1",
					ByArith())
				inPlane := b.Have(
					"so it lies in a boundary plane, x(n) = p",
					"∃j:num. "+
						"    j < n + 1 ∧ "+
						"    ((∀x:(num → num). x ∈ image(«onTop», f) ⇒ x(j) = 0) ∨ "+
						"        (∀x:(num → num). x ∈ image(«onTop», f) ⇒ x(j) = p))",
					Derive(func(c *Argument) {
						c.Take(n)
						c.Show(
							"at j = n",
							By(topPlane, nBelow))
					}))
				b.Show(
					"so on the top face it is a boundary door",
					By(isFace, inPlane, labelsUp, back))
			}))

		fullSet := a.TermAs[Set[Set[Fun[Nat, Nat]]]]("«full»")
		simplices := a.TermAs[Set[Set[Fun[Nat, Nat]]]]("{f:set(num → num) | kuhn_simplex(p, n, f)}")
		fullSimplices := a.Have(
			"the fully labelled n-simplices are n-simplices",
			"«full» ⊆ {f:set(num → num) | kuhn_simplex(p, n, f)}",
			BySets())
		fullFinite := a.Have(
			"there are finitely many of them",
			"finite(«full»)",
			By(
				fullSimplices,
				kuhn.KuhnSimplicesFinite.At(p, n),
				finite_set.FiniteSubset.At(fullSet, simplices)))
		doorSet := a.TermAs[Set[Set[Fun[Nat, Nat]]]]("«boundaryDoors»")
		onTopSets := a.TermAs[Fun[Set[Fun[Nat, Nat]], Set[Fun[Nat, Nat]]]]("image(«onTop»)")
		takeSets := a.TermAs[Fun[Set[Fun[Nat, Nat]], Set[Fun[Nat, Nat]]]]("image(tuple_take(n))")
		doorsCount := a.Have(
			"setting coordinate n to p and truncating match the boundary "+
				"doors one for one with the fully labelled n-simplices",
			"card(«boundaryDoors») = card(«full»)",
			By(
				fullFinite,
				fullOnTop,
				doorsTruncated,
				cardinality.MutualInversesCard.At(fullSet, doorSet, onTopSets, takeSets)))
		oddDoors := a.Have(
			"so the boundary doors are odd in number",
			"nat_odd(card(«boundaryDoors»))",
			By(oddFull, doorsCount))
		bounded := a.Have(
			"the reduced labels lie in 0, …, n + 1",
			"∀x:(num → num). kuhn_reduced(n + 1, l, x) ≤ n + 1",
			Derive(func(b *Argument) {
				x := b.FixAs[Fun[Nat, Nat]]("x")
				label := b.TermAs[Nat]("kuhn_reduced(n + 1, l, x)")
				b.Show(
					"a reduced label is at most its dimension",
					By(KuhnReducedIff.At(succ, label, l, x)))
			}))
		labelsBounded := a.Have(
			"so do the labels of every (n + 1)-simplex",
			Statement{
				Binders: "∀s:set(num → num).",
				Hypotheses: []string{
					"kuhn_simplex(p, n + 1, s)",
				},
				Conclusion: "image(kuhn_reduced(n + 1, l), s) ⊆ {k:num | k ≤ n + 1}",
			},
			By(bounded, set_image.ImageSubsetIff))
		label := a.TermAs[Fun[Fun[Nat, Nat], Nat]]("kuhn_reduced(n + 1, l)")
		a.Show(
			"the boundary doors are odd in number and the reduced labels lie "+
				"in 0, …, n + 1, so the fully labelled simplices are odd in number",
			By(oddDoors, labelsBounded, KuhnSimplexLemma.At(p, n, label)))
	}),
})}

// KuhnCombinatorial — under the boundary conditions, the fully labelled
// Kuhn simplices are odd in number. By induction on the dimension, the
// labelling left general. In dimension 0 the grid is the one tuple that
// is junk everywhere, its singleton is the one simplex, and every reduced
// label is 0, so exactly one simplex is fully labelled. A step is
// KuhnInduction, whose count one dimension down is the induction
// hypothesis at the labelling read on the top face x(n) = p: a point of
// the n-grid set to p at coordinate n lies in the (n + 1)-grid and keeps
// its coordinates below n (KuhnGridExtend), so that labelling meets the
// boundary conditions in dimension n.
var KuhnCombinatorial = kuhnCombinatorialThm{family.Add(registry.ProofEntry{
	Name: "KuhnCombinatorial",
	Key:  "prop_513da64c1ebb61f5",
	Reading: "At n = 0 it holds for every p, the count being 1. At p = 0 and n > " +
		"0 the two boundary conditions contradict, which is why no 0 < p is assumed.",
	Build: family.Theorem(Statement{
		Binders: "∀p n:num. ∀l:((num → num) → num → bool).",
		Hypotheses: []string{
			"∀x:(num → num). ∀i:num. x ∈ kuhn_grid(p, n) ∧ i < n ∧ x(i) = 0 ⇒ ¬l(x, i)",
			"∀x:(num → num). ∀i:num. x ∈ kuhn_grid(p, n) ∧ i < n ∧ x(i) = p ⇒ l(x, i)",
		},
		Conclusion: "nat_odd(card({s:set(num → num) | " +
			"            kuhn_simplex(p, n, s) ∧ image(kuhn_reduced(n, l), s) = {k:num | k ≤ n}}))",
		Abbrev: Abbrev{
			{Name: "junkTuple", Text: "λi:num. junk⟨A:num⟩"},
			{Name: "onTop", Text: "λx:(num → num). λi:num. COND(i = n, p, x(i))"},
			{Name: "topLabels", Text: "λx:(num → num). λi:num. l(«onTop»(x), i)"},
		},
	},
		func(a *Argument, p *Expr[Nat]) {
			a.Induct("n")
			a.Base(
				"in dimension 0 the one simplex is the singleton of the junk tuple, fully labelled",
				func(b *Argument) {
					l := b.FixAs[Fun2[Fun[Nat, Nat], Nat, Bool]]("l")
					point := b.TermAs[Fun[Nat, Nat]]("«junkTuple»")
					single := b.TermAs[Set[Fun[Nat, Nat]]]("{«junkTuple»}")
					junkOnly := b.Have(
						"a point of the 0-grid is junk at every coordinate, none lying below 0",
						"∀x:(num → num). x ∈ kuhn_grid(p, 0) ⇔ x = «junkTuple»",
						Derive(func(c *Argument) {
							c.FixAs[Fun[Nat, Nat]]("x")
							c.Iff()
							c.Forward(
								"a 0-tuple is junk from coordinate 0 on",
								func(d *Argument, inGrid Fact) {
									entries := d.Conjuncts(
										d.Unfolded(d.Unfolded(inGrid, kuhn.KuhnGridDef), carrier.TupleDef),
										"x is junk at every coordinate not below 0",
										"x is at most p below 0")
									d.Show(
										"so x is the junk tuple",
										Funext(),
										By(entries[0], nat_order.LessThanZeroClause))
								})
							c.Backward(
								"the junk tuple is a 0-tuple, with no coordinate below 0 to bound",
								func(d *Argument, isJunk Fact) {
									d.Show(
										"so it lies in the 0-grid",
										isJunk.Rw(),
										Unfold(kuhn.KuhnGridDef),
										Unfold(carrier.TupleDef),
										BySets(nat_order.LessThanZeroClause))
								})
						}))
					grid := b.Have(
						"so the 0-grid is that one point",
						"kuhn_grid(p, 0) = {«junkTuple»}",
						BySets(junkOnly))
					zero := b.TermAs[Nat]("0")
					one := b.TermAs[Nat]("0 + 1")
					simplices := b.Have(
						"a 0-simplex is the singleton of the junk tuple",
						"∀s:set(num → num). kuhn_simplex(p, 0, s) ⇔ s = {«junkTuple»}",
						Derive(func(c *Argument) {
							s := c.FixAs[Set[Fun[Nat, Nat]]]("s")
							c.Iff()
							c.Forward(
								"a 0-simplex has one point and lies in the one-point grid",
								func(d *Argument, simplex Fact) {
									parts := d.Conjuncts(
										d.Unfolded(simplex, kuhn.KuhnSimplexDef),
										"s lies in the grid",
										"s has one point",
										"any two points of s are comparable")
									d.Show(
										"so s is the whole grid",
										ByArith(
											grid,
											parts[1],
											parts[0],
											cardinality.CardSubsetEq.At(s, single),
											finite_set.FiniteSing.At(point),
											cardinality.CardSing.At(point),
											cardinality.HasSizeDef.At(s, one)))
								})
							c.Backward(
								"the singleton lies in the grid, has one point, and that point lies below itself",
								func(d *Argument, isSingle Fact) {
									inGrid := d.Have(
										"the singleton lies in the grid",
										"{«junkTuple»} ⊆ kuhn_grid(p, 0)",
										BySets(grid))
									sized := d.Have(
										"it has one point",
										"has_size({«junkTuple»}, 0 + 1)",
										By(
											cardinality.HasSizeDef.At(single, one),
											finite_set.FiniteSing.At(point),
											cardinality.CardSing.At(point)))
									comparable := d.Have(
										"its one point is comparable with itself",
										"∀x y:(num → num). x ∈ {«junkTuple»} ∧ y ∈ {«junkTuple»} ⇒ kuhn_le(0, x, y) ∨ kuhn_le(0, y, x)",
										BySets(At(kuhn.KuhnLeRefl, zero)))
									d.Show(
										"so the singleton is a 0-simplex",
										isSingle.Rw(),
										Unfold(kuhn.KuhnSimplexDef),
										By(inGrid, sized, comparable))
								})
						}))
					labels := b.Have(
						"every reduced label in dimension 0 is 0",
						"∀x:(num → num). kuhn_reduced(0, l, x) = 0",
						b.ForEach(func(x *Expr[Fun[Nat, Nat]]) Action {
							return ByArith(KuhnReducedIff.At(zero, zero, l, x))
						}))
					singleLabels := b.Have(
						"so the singleton carries the labels 0, …, 0",
						"image(kuhn_reduced(0, l), {«junkTuple»}) = {k:num | k ≤ 0}",
						BySets(labels.At(point), nat_order.LessEqZeroClause))
					full := b.Have(
						"a 0-simplex is fully labelled exactly when it is the singleton",
						"∀s:set(num → num). "+
							"    kuhn_simplex(p, 0, s) ∧ image(kuhn_reduced(0, l), s) = {k:num | k ≤ 0} ⇔ s = {«junkTuple»}",
						b.ForEach(func(s *Expr[Set[Fun[Nat, Nat]]]) Action {
							return By(simplices.At(s), singleLabels)
						}))
					counted := b.Have(
						"so the fully labelled 0-simplices are that one",
						"{s:set(num → num) | kuhn_simplex(p, 0, s) ∧ image(kuhn_reduced(0, l), s) = {k:num | k ≤ 0}} = "+
							"{{«junkTuple»}}",
						BySets(full))
					b.Show(
						"and one is odd",
						ByArith(counted, cardinality.CardSing.At(single)))
				})
			a.Step(
				"KuhnInduction carries the count up from the labelling read on the top face x(n) = p",
				func(b *Argument, ih Fact) {
					// The step's dimension suc(n), written n + 1 as KuhnInduction states it.
					b.Do(Simp(Fwd(nat_arith.Add1)))
					n := b.TermAs[Nat]("n")
					l := b.FixAs[Fun2[Fun[Nat, Nat], Nat, Bool]]("l")
					bounds := b.Conjuncts(
						b.Assume(),
						"l is ⊥ where a coordinate below n + 1 is 0",
						"l is ⊤ where a coordinate below n + 1 is p")
					onTop := b.Have(
						"a point of the n-grid set to p at coordinate n lies in the (n + 1)-grid",
						"∀x:(num → num). x ∈ kuhn_grid(p, n) ⇒ «onTop»(x) ∈ kuhn_grid(p, n + 1)",
						Derive(func(c *Argument) {
							x := c.FixAs[Fun[Nat, Nat]]("x")
							xIn := c.Assume()
							c.Show(
								"p ≤ p, so x set to p at coordinate n is a grid point one dimension up",
								By(xIn, kuhn.KuhnGridExtend.At(p, n, x, p), nat_order.LessEqRefl.At(p)))
						}))
					zeroFace := b.Have(
						"so the labelling read on the top face is ⊥ where a coordinate below n is 0",
						"∀x:(num → num). ∀i:num. x ∈ kuhn_grid(p, n) ∧ i < n ∧ x(i) = 0 ⇒ ¬l(«onTop»(x), i)",
						Derive(func(c *Argument) {
							x := c.FixAs[Fun[Nat, Nat]]("x")
							i := c.FixAs[Nat]("i")
							c.Show(
								"the point on the top face is 0 at i, below n + 1",
								ByArith(bounds[0].At(c.TermAs[Fun[Nat, Nat]]("«onTop»(x)"), i), onTop.At(x)))
						}))
					topFace := b.Have(
						"and ⊤ where a coordinate below n is p",
						"∀x:(num → num). ∀i:num. x ∈ kuhn_grid(p, n) ∧ i < n ∧ x(i) = p ⇒ l(«onTop»(x), i)",
						Derive(func(c *Argument) {
							x := c.FixAs[Fun[Nat, Nat]]("x")
							i := c.FixAs[Nat]("i")
							c.Show(
								"the point on the top face is p at i, below n + 1",
								ByArith(bounds[1].At(c.TermAs[Fun[Nat, Nat]]("«onTop»(x)"), i), onTop.At(x)))
						}))
					relabel := b.Have(
						"its reduced label at a point is the reduced label of the point on the top face",
						"kuhn_reduced(n, «topLabels») = (λx:(num → num). kuhn_reduced(n, l, «onTop»(x)))",
						Simp(Fwd(kuhnReducedDef)),
						Refl())
					odd := b.Have(
						"so by the induction hypothesis the n-simplices it labels fully are odd in number",
						"nat_odd(card({f:set(num → num) | "+
							"            kuhn_simplex(p, n, f) ∧ "+
							"            image(λx:(num → num). kuhn_reduced(n, l, «onTop»(x)), f) = {k:num | k ≤ n}}))",
						By(ih.At(b.TermAs[Fun2[Fun[Nat, Nat], Nat, Bool]]("«topLabels»")), zeroFace, topFace, relabel))
					b.Show(
						"so the fully labelled (n + 1)-simplices are odd in number too",
						By(KuhnInduction.At(p, n, l), odd, bounds[0], bounds[1]))
				})
		}),
})}

// ---------------------------------------------------------------------------
// The lemma
// ---------------------------------------------------------------------------

// KuhnLemma — a labelling of the grid {0, …, p}ⁿ that is ⊥ where a
// coordinate is 0 and ⊤ where it is p has a cell ⟦q, q + (1, …, 1)⟧ in
// which every coordinate's label takes both values (Kuhn, 1960). The
// fully labelled simplices are odd in number, so there is one, t. Its
// least point q is the corner: its greatest point is q raised by one
// below n and lies in the grid, so q stays below p there, and every point
// of t lies within one of q. For i < n, t holds a point r of reduced
// label i and a point s of reduced label i + 1, and the reduced label
// reads l(r, i) as ⊤ and l(s, i) as ⊥.
var KuhnLemma = kuhnLemmaThm{family.Add(registry.ProofEntry{
	Name: "KuhnLemma",
	Key:  "prop_db5bf4204065c120",
	Reading: "The boundary conditions as in KuhnCombinatorial, and no 0 < " +
		"p for the same reason. At n = 0 the conclusion asks only a grid point.",
	Build: family.Theorem(Statement{
		Binders: "∀p n:num. ∀l:((num → num) → num → bool).",
		Hypotheses: []string{
			"∀x:(num → num). ∀i:num. x ∈ kuhn_grid(p, n) ∧ i < n ∧ x(i) = 0 ⇒ ¬l(x, i)",
			"∀x:(num → num). ∀i:num. x ∈ kuhn_grid(p, n) ∧ i < n ∧ x(i) = p ⇒ l(x, i)",
		},
		Conclusion: "∃q:(num → num). " +
			"    q ∈ kuhn_grid(p, n) ∧ " +
			"    (∀i:num. i < n ⇒ q(i) < p) ∧ " +
			"    ∀i:num. " +
			"        i < n ⇒ " +
			"        ∃r s:(num → num). " +
			"            r ∈ kuhn_grid(p, n) ∧ " +
			"            s ∈ kuhn_grid(p, n) ∧ " +
			"            (∀j:num. j < n ⇒ q(j) ≤ r(j) ∧ r(j) ≤ q(j) + 1 ∧ q(j) ≤ s(j) ∧ s(j) ≤ q(j) + 1) ∧ " +
			"            ¬(l(r, i) ⇔ l(s, i))",
		Abbrev: Abbrev{
			{Name: "fullSimplices", Text: "{s:set(num → num) | " +
				"    kuhn_simplex(p, n, s) ∧ image(kuhn_reduced(n, l), s) = {k:num | k ≤ n}}"},
		},
	},
		func(a *Argument, p, n *Expr[Nat], l *Arrow2[Fun[Nat, Nat], Nat, Bool], bounds Fact) {
			odd := a.Have(
				"the fully labelled simplices are odd in number",
				"nat_odd(card(«fullSimplices»))",
				By(KuhnCombinatorial.At(p, n, l), bounds))
			some := a.Have(
				"so there are some, an odd count not being 0",
				"«fullSimplices» ≠ ∅",
				ByArith(odd, cardinality.CardClauses))
			full := a.TermAs[Set[Set[Fun[Nat, Nat]]]]("«fullSimplices»")
			t, fullT := a.ObtainAs[Set[Fun[Nat, Nat]]](
				"take a fully labelled simplex t",
				"∃t:set(num → num). kuhn_simplex(p, n, t) ∧ image(kuhn_reduced(n, l), t) = {k:num | k ≤ n}",
				By(some, set_basic.MemberNotEmpty.At(full)))
			tParts := a.Conjuncts(
				fullT,
				"t is a simplex",
				"t carries every label 0, …, n")
			simplex, labels := tParts[0], tParts[1]
			points := a.Have(
				"the points of t are grid points",
				"∀x:(num → num). x ∈ t ⇒ x ∈ kuhn_grid(p, n)",
				BySets(simplex, kuhn.KuhnSimplexDef.At(p, n, t)))
			q, b, extrema := a.Unpack2As[Fun[Nat, Nat], Fun[Nat, Nat]](
				GroupPremises(simplex, kuhn.KuhnSimplexExtrema.At(p, n, t)),
				"q",
				"b")
			ends := a.Conjuncts(
				extrema,
				"q lies in t",
				"b lies in t",
				"every point of t lies between q and b",
				"b is q raised by one below n")
			qIn, bIn, between, raised := ends[0], ends[1], ends[2], ends[3]
			top := a.Conjuncts(
				a.Unfolded(GroupPremises(bIn, points.At(b)), kuhn.KuhnGridDef),
				"b is an n-tuple",
				"the entries of b below n are at most p")
			belowP := a.Have(
				"q is below p in every coordinate below n, q raised by one being at most p there",
				"∀i:num. i < n ⇒ q(i) < p",
				Derive(func(c *Argument) {
					i := c.FixAs[Nat]("i")
					below := c.Assume()
					c.Show(
						"q(i) + 1 = b(i) ≤ p",
						ByArith(top[1].At(i), raised.At(i), below))
				}))
			within := a.Have(
				"every point of t lies above q, within one of it in each coordinate below n",
				"∀x:(num → num). x ∈ t ⇒ ∀j:num. j < n ⇒ q(j) ≤ x(j) ∧ x(j) ≤ q(j) + 1",
				Derive(func(c *Argument) {
					x := c.FixAs[Fun[Nat, Nat]]("x")
					xIn := c.Assume()
					c.Show(
						"x lies above q in kuhn_le's order, which bounds each coordinate below n",
						By(between.At(x), xIn, kuhn.KuhnLeDef.At(n, q, x)))
				}))
			cells := a.Have(
				"for each coordinate i below n the cell ⟦q, b⟧ holds a point labelled ⊤ at i and one labelled ⊥",
				Statement{
					Binders: "∀i:num.",
					Hypotheses: []string{
						"i < n",
					},
					Conclusion: "∃r s:(num → num). " +
						"    r ∈ kuhn_grid(p, n) ∧ " +
						"    s ∈ kuhn_grid(p, n) ∧ " +
						"    (∀j:num. j < n ⇒ q(j) ≤ r(j) ∧ r(j) ≤ q(j) + 1 ∧ q(j) ≤ s(j) ∧ s(j) ≤ q(j) + 1) ∧ " +
						"    ¬(l(r, i) ⇔ l(s, i))",
				},
				Derive(func(c *Argument) {
					i := c.FixAs[Nat]("i")
					below := c.Assume()
					r, atI := c.ObtainAs[Fun[Nat, Nat]](
						"t holds a point r of reduced label i, as i ≤ n",
						"∃r:(num → num). r ∈ t ∧ kuhn_reduced(n, l, r) = i",
						BySets(below, labels, nat_order.LessEqOfLessThan.At(i, n)))
					next := c.Have(
						"i + 1 is at most n too",
						"i + 1 ≤ n",
						ByArith(below))
					s, atNext := c.ObtainAs[Fun[Nat, Nat]](
						"and a point s of reduced label i + 1",
						"∃s:(num → num). s ∈ t ∧ kuhn_reduced(n, l, s) = i + 1",
						BySets(next, labels))
					rParts := c.Conjuncts(
						atI,
						"r lies in t",
						"the reduced label of r is i")
					sParts := c.Conjuncts(
						atNext,
						"s lies in t",
						"the reduced label of s is i + 1")
					on := c.Have(
						"the run of ⊥ at r stops at i, short of n: l(r, i) is ⊤",
						"l(r, i)",
						ByArith(rParts[1], below, KuhnReducedIff.At(n, i, l, r)))
					off := c.Have(
						"the run of ⊥ at s reaches past i: l(s, i) is ⊥",
						"¬l(s, i)",
						ByArith(sParts[1], KuhnReducedIff.At(n, c.TermAs[Nat]("i + 1"), l, s)))
					c.Take(r)
					c.Take(s)
					c.Show(
						"r and s are grid points of t, within one of q, whose labels at i differ",
						By(points.At(r), points.At(s), within.At(r), within.At(s), rParts[0], sParts[0], on, off))
				}))
			a.Take(q)
			a.Show(
				"q is the corner of the cell",
				By(points.At(q), qIn, belowP, cells))
		}),
})}
