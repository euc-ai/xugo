// orthogonal.go — orthogonality: the projection along a direction, and
// what orthogonality to a family says about everything it spans.
//
// Two vectors are orthogonal when the form pairs them to `&0`. Fix a
// direction g: every x splits into the multiple of g that the form
// prescribes — `⟪x, g⟫_n * real_inv(⟪g, g⟫_n) • g`, the component of x
// along g — and the residual left over, and the residual is orthogonal
// to g. That splitting is the projection, and the coefficient is
// chosen for exactly one reason: it is what makes the residual
// orthogonal.
//
// The coefficient is written with the inverse, and the chapter asks
// nothing of g. `real_inv` is total, and where g is null for the form x
// is orthogonal to g already, so the statements here carry no nonzero
// hypothesis at all. A caller splitting a vector against a whole list
// of directions therefore never has to decide, direction by direction,
// whether that direction vanishes.
//
// Against a family the question is finite: a member of the span is a
// combination of the family, and the form is linear in the argument it
// is checked against, so a vector checked against the k directions is
// orthogonal to every vector they span. That is what lets a
// decomposition speak of a vector orthogonal to a subspace without
// ever checking it against infinitely many vectors.

package euclidean

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/abelian_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/real/real_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/vector/dot"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// ResidualOrthogonal — subtracting from x its component along g leaves a
// vector orthogonal to g.
//
// Linearity in the first argument reduces the whole claim to one
// equation between two reals: the coefficient, multiplied back by
// ⟪g, g⟫_n, is ⟪x, g⟫_n again. Where ⟪g, g⟫_n is invertible the
// coefficient is the quotient by it and the two cancel. Where it
// vanishes x is orthogonal to g already, and the coefficient carries
// ⟪x, g⟫_n as a factor, so both sides are &0 — the value real_inv takes
// at &0 never enters the argument, which is why g needs no hypothesis.
var ResidualOrthogonal = residualOrthogonalThm{family.Add(registry.ProofEntry{
	Name: "ResidualOrthogonal",
	Key:  "prop_cb84a0bccac67aef",
	Build: family.Theorem("∀n:num. ∀x g:(num → real). "+
		"    ⟪x - ⟪x, g⟫_n * real_inv(⟪g, g⟫_n) • g, g⟫_n = &0",
		func(a *Argument, n *Expr[Nat], x, g *Vec[Real, DimN]) {
			// Linearity in the first argument, at the head: the form
			// of the residual against g is the difference of the form
			// at x and the coefficient times the form at g.
			a.Do(Simp(Fwd(dot.SubLeft.Read(real_ring.CommRing)), Fwd(dot.SmulLeft.Read(real_ring.CommRing))))
			recovered := a.Have(
				"the coefficient, multiplied back by ⟪g, g⟫_n, is ⟪x, g⟫_n",
				"⟪x, g⟫_n * real_inv(⟪g, g⟫_n) * ⟪g, g⟫_n = ⟪x, g⟫_n",
				ByCaseStep(a.Term("⟪g, g⟫_n = &0"),
					Case(
						"g is null for the form, so x is orthogonal to g already and ⟪x, g⟫_n is a factor of the left side",
						Given(func(b *Argument, null Fact) {
							orthogonal := b.Have(
								"a vector null for the form is orthogonal to every vector, and the form is symmetric",
								"⟪x, g⟫_n = &0",
								By(null, NullVectorOrthogonal.At(g, x), dot.Sym.Read(real_ring.CommRing)))
							b.Show(
								"so the left side vanishes with its factor, and both sides are &0",
								By(orthogonal, real_ring.MulLeftZero))
						})),
					Case(
						"⟪g, g⟫_n ≠ &0, so the coefficient is the quotient of ⟪x, g⟫_n by it",
						Given(func(b *Argument, nonzero Fact) {
							b.Show(
								"and a quotient multiplied back by its divisor is its numerator",
								Simp(Rev(real_field.RealDivDef)),
								By(nonzero, field.DivRightMul.Read(real_field.Field)))
						})),
				))
			a.Show(
				"so the residual pairs to &0 against g",
				ByArith(recovered))
		}),
})}

// DecompositionUnique — a vector splits in at most one way into a part
// inside a subspace and a part orthogonal to it.
//
// One vector settles it: the difference of the two candidate subspace
// parts. It lies in the subspace, which is closed under differences,
// and it is an n-vector, the subspace lying inside them. Pair the one
// sum against that difference: each orthogonal part pairs to zero
// against it, the difference being a member of the subspace, so the two
// subspace parts pair against it alike and the difference pairs to zero
// against itself. On n-vectors the form is definite, so the difference
// is the zero vector and the two subspace parts agree; cancelling the
// part they share in the sum settles the orthogonal ones.
//
// The hypothesis confining the subspace to the n-vectors is where
// uniqueness parts company with existence, which asks for no such
// thing. The form only ever looks below n, so without the confinement
// two decompositions differing past n would pair identically and the
// statement would be false. Nothing more is asked of the subspace: it
// is any subspace rather than a span, so a consumer holding some other
// subspace uses this as it stands.
var DecompositionUnique = decompositionUniqueThm{family.Add(registry.ProofEntry{
	Name: "DecompositionUnique",
	Key:  "prop_b0fb5685ef96a497",
	Build: family.Theorem(
		Statement{
			Binders: "∀n:num. ∀s:set(num → real). ∀y z y' z':(num → real).",
			Hypotheses: []string{
				"vec_subspace(s)",
				"∀w:(num → real). w ∈ s ⇒ vec⟨n⟩(w)",
				"y ∈ s",
				"y' ∈ s",
				"∀w:(num → real). w ∈ s ⇒ ⟪z, w⟫_n = &0",
				"∀w:(num → real). w ∈ s ⇒ ⟪z', w⟫_n = &0",
				"y + z = y' + z'",
			},
			Conclusion: "y = y' ∧ z = z'",
		},
		func(a *Argument, n *Expr[Nat], s *Expr[Set[Fun[Nat, Real]]], y, z, yPrime, zPrime *Vec[Real, DimN],
			subspace, confined, yIn, yPrimeIn, zOrth, zPrimeOrth, split Fact) {
			difference := a.VecAs[Real, DimN]("y - y'")

			inSubspace := a.Have(
				"the difference of the two subspace parts lies in the subspace",
				"y - y' ∈ s",
				By(subspace, yIn, yPrimeIn, vec_space.SubspaceSub, real_ring.CommRing))
			isVector := a.Have(
				"and the subspace lies inside the n-vectors, so the difference is one",
				"vec⟨n⟩(y - y')",
				By(confined.At(difference), inSubspace))

			zNull := a.Have(
				"the first decomposition's orthogonal part pairs to zero against the difference",
				"⟪z, y - y'⟫_n = &0",
				By(zOrth.At(difference), inSubspace))
			zPrimeNull := a.Have(
				"and so does the second's",
				"⟪z', y - y'⟫_n = &0",
				By(zPrimeOrth.At(difference), inSubspace))

			pairing := a.Have(
				"pairing the one sum against the difference splits it along either decomposition",
				"⟪y, y - y'⟫_n + ⟪z, y - y'⟫_n = ⟪y', y - y'⟫_n + ⟪z', y - y'⟫_n",
				Simp(Rev(dot.AddLeft.Read(real_ring.CommRing))),
				By(Normalized, split))
			null := a.Have(
				"the orthogonal parts contribute nothing there, so the subspace parts "+
					"pair alike against the difference and it pairs to zero against itself",
				"⟪y - y', y - y'⟫_n = &0",
				Simp(Fwd(dot.SubLeft.Read(real_ring.CommRing))),
				ByArith(pairing, zNull, zPrimeNull))

			// Definiteness is spent here and nowhere else, and it is what
			// the confinement hypothesis was carried for.
			vanishes := a.Have(
				"the form is definite on n-vectors, so the difference is the zero vector",
				"y - y' = vec_zero",
				By(null, DotEqZero.At(proof.Inhabit(difference, isVector))))

			// A vanishing difference IS an equality, at the vectors' own
			// additive group.
			samePart := a.Have(
				"so the two subspace parts are the same vector",
				"y = y'",
				By(vanishes, vec_space.SubEqZero.Read(real_ring.CommRing)))

			vectors := abelian_group.Group.Read(vec_space.AbelianGroup.Read(real_ring.CommRing))
			vectorGroup := a.TermAs[group.GroupOps[Fun[Nat, Real]]]("mk_group(vec_add, vec_zero, vec_neg, 𝕌)")

			a.Show(
				"and cancelling that common part on the left of the sum identifies the orthogonal parts too",
				By(samePart, split, vectors, group.LeftCancel.At(vectorGroup, y, z, zPrime)))
		}),
})}

// ProjectionExists — every sequence splits against the first k members
// of a family: a part inside their span, and a remainder the form sends
// to &0 against each of those members.
//
// The induction is on k, and the property it carries keeps the sequence
// universally quantified, because the step reads the hypothesis TWICE:
// once at x, which supplies y inside the span with x - y orthogonal to
// the first k members, and once at the new member e(k), which supplies
// p inside the span with e(k) - p orthogonal to them. The step then
// corrects y by the component of x - y along e(k) - p. Nothing is built
// member by member — no orthogonal family is constructed — which is why
// the family is asked for nothing at all.
//
// That the correction lands inside the larger span is subspace
// bookkeeping: the span at suc k holds y and p because it extends the
// span at k, and it holds e(k) because e(k) is one of its own members;
// hence it holds e(k) - p, every multiple of it, and every sum.
//
// That the new remainder is orthogonal splits in two. Against a member
// below k both shares of the splitting identity vanish, by the two
// readings of the hypothesis. Against e(k) the remainder is orthogonal
// to p — p lies in the span of members it is already orthogonal to —
// and orthogonal to e(k) - p, which is precisely what the coefficient
// was chosen for; since e(k) and p differ by e(k) - p, the pairing
// against e(k) is the sum of those two. The coefficient asks nothing of
// e(k) - p, so no branch of this proof decides whether that direction
// vanishes — which it does exactly when e(k) already lies in the span of
// the earlier members.
var ProjectionExists = projectionExistsThm{family.Add(registry.ProofEntry{
	Name: "ProjectionExists",
	Key:  "prop_35a1229866370e80",
	Build: family.Theorem(
		Statement{
			Binders:    "∀n k:num. ∀e:(num → num → real). ∀x:(num → real).",
			Conclusion: "∃y:(num → real). y ∈ vec_span(k, e) ∧ (∀i:num. i < k ⇒ ⟪x - y, e(i)⟫_n = &0)",
			Abbrev: Abbrev{
				{Name: "projectionCoefficient", Text: "⟪x - y, e(k) - p⟫_n * real_inv(⟪e(k) - p, e(k) - p⟫_n)"},
				{Name: "projectionCorrected", Text: "y + «projectionCoefficient» • (e(k) - p)"},
				{Name: "projectionResidual", Text: "x - («projectionCorrected»)"},
			},
		},
		func(a *Argument) {
			// The induction runs on k alone: the dimension, the family and
			// the sequence stay inside the property — the sequence because
			// the step reads the hypothesis at two different sequences.
			k := a.Binder("k")
			a.Induct(k)
			a.Base(
				"below 0 there is nothing to be orthogonal to, and the zero vector is already in the span",
				func(a *Argument) {
					// The dimension, the family and the sequence.
					a.Fix()
					a.Fix()
					a.Fix()
					a.Take(a.Term("vec_zero"))

					subspace := a.Have(
						"the span of no members is a subspace",
						"vec_subspace(vec_span(0, e))",
						By(Normalized, vec_space.SpanSubspace, real_ring.CommRing))
					a.Show(
						"so it holds the zero vector, and the orthogonality condition asks nothing, no index lying below 0",
						By(subspace, vec_space.VecSubspaceDef, nat_order.LessThanZeroClause))
				})
			a.Step(
				"one more member: correct the projection by the component along what that member adds",
				func(a *Argument, projects Fact) {
					n := a.Fix()
					e := a.Fix()
					x := a.Fix()
					newMember := e.Apply(k)
					members := a.TermAs[Fun2[Nat, Nat, Real]]("e")
					upTo := a.TermAs[Nat]("k")
					upToNext := a.TermAs[Nat]("suc(k)")

					// The two readings of the hypothesis, at x and at the
					// new member. This is the whole device of the proof.
					y, forX := a.ObtainAs[Fun[Nat, Real]](
						"the first k members carry a projection of x",
						"∃y:(num → real). y ∈ vec_span(k, e) ∧ (∀i:num. i < k ⇒ ⟪x - y, e(i)⟫_n = &0)",
						By(projects.At(n, e, x)))
					p, forNew := a.ObtainAs[Fun[Nat, Real]](
						"and one of the new member e(k)",
						"∃p:(num → real). p ∈ vec_span(k, e) ∧ (∀i:num. i < k ⇒ ⟪e(k) - p, e(i)⟫_n = &0)",
						By(projects.At(n, e, newMember)))

					strictly := a.Have(
						"k lies below its successor",
						"k < suc(k)",
						By(nat_order.LessThanSucIffLessEq, nat_order.LessEqRefl))
					weakly := a.Have(
						"and so at most it",
						"k ≤ suc(k)",
						By(strictly, nat_order.LessEqOfLessThan))

					wider := a.Have(
						"the span of the first suc k members is a subspace",
						"vec_subspace(vec_span(suc(k), e))",
						By(Normalized, vec_space.SpanSubspace, real_ring.CommRing))
					yIn := a.Have(
						"it holds y",
						"y ∈ vec_span(suc(k), e)",
						By(weakly, forX, vec_space.SpanMono.Read(real_ring.CommRing).At(upTo, upToNext, members, y)))
					pIn := a.Have(
						"and p",
						"p ∈ vec_span(suc(k), e)",
						By(weakly, forNew, vec_space.SpanMono.Read(real_ring.CommRing).At(upTo, upToNext, members, p)))
					newIn := a.Have(
						"and the new member itself",
						"e(k) ∈ vec_span(suc(k), e)",
						By(strictly, vec_space.SpanMember.Read(real_ring.CommRing).At(upToNext, upTo, members)))
					directionIn := a.Have(
						"hence the direction e(k) - p the correction runs along",
						"e(k) - p ∈ vec_span(suc(k), e)",
						By(
							pIn,
							newIn,
							wider,
							vec_space.SubspaceSub.Read(real_ring.CommRing).At(
								a.TermAs[Set[Fun[Nat, Real]]]("vec_span(suc(k), e)"), a.TermAs[Fun[Nat, Real]]("e(k)"), p)))

					// The witness: y plus the component of x - y along
					// e(k) - p.
					a.Take(a.Term("«projectionCorrected»"))

					correctionIn := a.Have(
						"a multiple of that direction stays in the span",
						"«projectionCoefficient» • (e(k) - p) ∈ vec_span(suc(k), e)",
						By(directionIn, wider, vec_space.VecSubspaceDef))
					corrected := a.Have(
						"and so does y plus it",
						"«projectionCorrected» ∈ vec_span(suc(k), e)",
						By(yIn, correctionIn, wider, vec_space.VecSubspaceDef))

					// Stated for every second argument, because it is wanted
					// twice: at the members below k, and at e(k) - p itself.
					splits := a.Have(
						"the new remainder pairs as x - y does, less the correction's share",
						"∀w:(num → real). "+
							"    ⟪«projectionResidual», w⟫_n = ⟪x - y, w⟫_n - «projectionCoefficient» * ⟪e(k) - p, w⟫_n",
						Derive(func(b *Argument) {
							b.Fix()
							b.Show(
								"linearity in the first argument brings both sides to the same combination of the three pairings",
								Simp(
									Fwd(dot.SubLeft.Read(real_ring.CommRing)),
									Fwd(dot.AddLeft.Read(real_ring.CommRing)),
									Fwd(dot.SmulLeft.Read(real_ring.CommRing))),
								ByArith(real_ring.RealSubDef))
						}))

					below := a.Have(
						"against a member below k both shares vanish, by the two readings of the hypothesis",
						"∀i:num. i < k ⇒ ⟪«projectionResidual», e(i)⟫_n = &0",
						Derive(func(b *Argument) {
							i := b.Fix()
							early := b.Assume()
							b.Show(
								"x - y and e(k) - p are each orthogonal to e(i), and a multiple of &0 is &0",
								By(splits.At(e.Apply(i)), early, forX, forNew, real_ring.MulRightZero, real_ring.SubRightZero))
						}))

					againstP := a.Have(
						"p is a combination of the members below k, so the new "+
							"remainder is orthogonal to it, being orthogonal to all of them",
						"⟪«projectionResidual», p⟫_n = &0",
						By(below, forNew, dot.OrthogonalToSpan.Read(real_ring.CommRing)))

					annihilates := a.Have(
						"the coefficient is the one that cancels the pairing along e(k) - p",
						"⟪x - y, e(k) - p⟫_n - «projectionCoefficient» * ⟪e(k) - p, e(k) - p⟫_n = &0",
						Simp(Rev(dot.SmulLeft.Read(real_ring.CommRing)), Rev(dot.SubLeft.Read(real_ring.CommRing))),
						By(ResidualOrthogonal))
					againstDirection := a.Have(
						"so the new remainder is orthogonal to e(k) - p",
						"⟪«projectionResidual», e(k) - p⟫_n = &0",
						By(splits.At(a.Term("e(k) - p")), annihilates))

					againstNew := a.Have(
						"the form is linear in its second argument, and e(k) and p differ by "+
							"that direction, so the new remainder is orthogonal to e(k) as well",
						"⟪«projectionResidual», e(k)⟫_n = &0",
						By(againstP, againstDirection, dot.SubRight.Read(real_ring.CommRing), real_ring.SubRightZero))

					orthogonal := a.Have(
						"that is every member below suc k",
						"∀i:num. i < suc(k) ⇒ ⟪«projectionResidual», e(i)⟫_n = &0",
						Derive(func(b *Argument) {
							i := b.Fix()
							reaches := b.Assume()
							b.Cases(b.Term("i < k"))
							b.When(
								"i is below k, where the remainder's orthogonality is what the hypothesis at x supplies",
								func(b *Argument, early Fact) {
									b.Show(
										"the remainder was already orthogonal there",
										By(below.At(i), early))
								})
							b.Otherwise(
								"or i is k, the one member the correction was built against",
								func(b *Argument, notEarly Fact) {
									b.Show(
										"below suc k and not below k leaves i = k",
										By(notEarly, reaches, againstNew, nat_order.LessThanSucClause))
								})
						}))

					a.Show(
						"so the corrected vector realizes the split at suc k",
						By(corrected, orthogonal))
				})
		}),
})}

// OrthogonalDecomposition — every sequence splits against the span of a
// family's first k members: a part lying in that span, and a part the
// form sends to &0 against every vector of it.
//
// The projection supplies the first part and the remainder left over is
// the second. Two facts make that a decomposition. The remainder is
// orthogonal to each of the k members, and orthogonality to a family
// reaches everything the family spans, so the second part is orthogonal
// to the span as a whole — the form a reader wants, since it speaks of
// the subspace and not of the family that happens to present it. And
// the two parts add back to the sequence, which entry by entry is the
// real line's own add-back law.
//
// Nothing is asked of the family, of the sequence, or of the dimension:
// a projection exists against any family whatever, so this half of the
// decomposition carries no hypothesis at all. Uniqueness is where one
// enters: the form only ever looks below n, so DecompositionUnique
// above confines the subspace to the n-vectors, without which two
// splittings differing past n would pair alike.
var OrthogonalDecomposition = orthogonalDecompositionThm{family.Add(registry.ProofEntry{
	Name: "OrthogonalDecomposition",
	Key:  "prop_1ae786ea29581c28",
	Build: family.Theorem(
		"∀n k:num. ∀e:(num → num → real). ∀x:(num → real). ∃y z:(num → real). "+
			"    y ∈ vec_span(k, e) ∧ (∀w:(num → real). w ∈ vec_span(k, e) ⇒ ⟪z, w⟫_n = &0) ∧ x = y + z",
		func(a *Argument, n, k *Expr[Nat], e *Arrow2[Nat, Nat, Real], x *Expr[Fun[Nat, Real]]) {
			y, projects := a.Obtain(
				"the first k members carry a projection of x",
				"∃y:(num → real). y ∈ vec_span(k, e) ∧ (∀i:num. i < k ⇒ ⟪x - y, e(i)⟫_n = &0)",
				By(ProjectionExists.At(n, k, e, x)))
			// The two parts: the projection, and what it leaves behind.
			a.Take(y)
			a.Take(a.Term("x - y"))

			reaches := a.Have(
				"the remainder is orthogonal to everything the family spans, not only to the k members",
				"∀w:(num → real). w ∈ vec_span(k, e) ⇒ ⟪x - y, w⟫_n = &0",
				By(projects, dot.OrthogonalToSpan.Read(real_ring.CommRing)))
			adds := a.Have(
				"and the remainder added back to the projection is x again",
				"y + (x - y) = x",
				By(vec_space.AddSubCancel.Read(real_ring.CommRing)))

			a.Show(
				"so the projection and the remainder are the two parts the split asks for",
				By(Normalized, projects, reaches, adds))
		}),
})}

// SpanDecomposition — the chapter's two halves in one statement: against
// the span of a family of n-vectors, every sequence splits into a part
// lying in that span and a part orthogonal to it, and it splits in
// exactly one way.
//
// Both halves are theorems above, and what is left is to read the
// uniqueness one at the span. That reading asks two things of the span
// and nothing else: that it be a subspace, which every span is, and
// that it lie inside the n-vectors, which is where this member's
// hypothesis goes and the only place it goes — a span borrows its
// dimension from the family it is combined from. The remaining premise
// is the two splittings' own equations for x set side by side: both add
// back to x, so both have the same sum.
//
// The asymmetry a reader meets here is the chapter's. Existence asks
// nothing at all — of the family, of the sequence, or of the dimension —
// while uniqueness must confine the span to the n-vectors, the form
// looking only below n. So a splitting exists against any family
// whatever, and is the only one as soon as that family is made of
// n-vectors.
var SpanDecomposition = spanDecompositionThm{family.Add(registry.ProofEntry{
	Name: "SpanDecomposition",
	Key:  "prop_2ee3a5364b896d74",
	Build: family.Theorem(
		Statement{
			Binders: "∀n k:num. ∀e:(num → num → real). ∀x:(num → real).",
			Hypotheses: []string{
				"∀i:num. i < k ⇒ vec⟨n⟩(e(i))",
			},
			Conclusion: "∃y z:(num → real). " +
				"    y ∈ vec_span(k, e) ∧ " +
				"    (∀w:(num → real). w ∈ vec_span(k, e) ⇒ ⟪z, w⟫_n = &0) ∧ " +
				"    x = y + z ∧ " +
				"    (∀y' z':(num → real). " +
				"        y' ∈ vec_span(k, e) ∧ " +
				"        (∀w:(num → real). w ∈ vec_span(k, e) ⇒ ⟪z', w⟫_n = &0) ∧ " +
				"        x = y' + z' ⇒ " +
				"        y' = y ∧ z' = z)",
		},
		func(a *Argument, n, k *Expr[Nat], e *Arrow2[Nat, Nat, Real], x *Expr[Fun[Nat, Real]],
			familyVecs Fact) {
			y, z, splits := a.Obtain2(
				"the projection of x against the family, and the remainder it leaves",
				"∃y z:(num → real). "+
					"    y ∈ vec_span(k, e) ∧ (∀w:(num → real). w ∈ vec_span(k, e) ⇒ ⟪z, w⟫_n = &0) ∧ x = y + z",
				By(OrthogonalDecomposition.At(n, k, e, x)))
			a.Take(y)
			a.Take(z)

			a.Do(SplitConj(
				Case(
					"the projection and the remainder split x against the span",
					By(splits)),
				Case(
					"and a pair splitting it that way is that pair",
					Derive(func(b *Argument) {
						yPrime := b.Fix("y'")
						zPrime := b.Fix("z'")
						other := b.Assume()

						subspace := b.Have(
							"the span is a subspace",
							"vec_subspace(vec_span(k, e))",
							By(Normalized, vec_space.SpanSubspace, real_ring.CommRing))
						confined := b.Have(
							"and it lies inside the n-vectors, the family's first k members being n-vectors",
							"∀w:(num → real). w ∈ vec_span(k, e) ⇒ vec⟨n⟩(w)",
							Derive(func(c *Argument) {
								c.Fix()
								inSpan := c.Assume()
								c.Show(
									"an element of the span is combined from vectors the hypothesis gives dimension n",
									By(familyVecs, inSpan, vec_space.SpanVec, real_ring.CommRing))
							}))

						sums := b.Have(
							"both splittings add back to x, so the two have one sum",
							"y' + z' = y + z",
							By(other, splits))

						b.Show(
							"and against one subspace a sum splits in at most one way",
							By(
								subspace,
								confined,
								other,
								splits,
								sums,
								At(DecompositionUnique, n, b.Term("vec_span(k, e)"), yPrime, zPrime, y, z)))
					})),
			))
		}),
})}
