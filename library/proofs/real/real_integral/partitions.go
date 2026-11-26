// partitions.go — tagged partitions and what the definition asks of
// them. Every interval has partitions as fine as we like, cut into equal
// pieces when it is not a point. The points of a partition rise, so its
// pieces and its tags lie in the interval and each point of the interval
// lies in some piece; moving one tag moves one term of the Riemann sum.
// An interval over which a function has an integral is ordered, two
// integrals over one interval share a mesh, and so a function has at most
// one integral, which the oriented integral then reads off.

package real_integral

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/real/real_archimedean"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/proofs/relations/equivalence"
	"github.com/euc-ai/xugo/library/proofs/relations/order"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/registry"
)

// UniformFinePartition — a nondegenerate interval has partitions into
// equal pieces as fine as we like: some N copies of δ exceed b − a, and
// the N + 1 pieces of length h = (b − a)/(N + 1), each tagged at its left
// end, are shorter than δ.
var UniformFinePartition = uniformFinePartitionThm{family.Add(registry.ProofEntry{
	Name: "UniformFinePartition",
	Key:  "prop_952f28d2a6118e2f",
	Build: family.Theorem(Statement{
		Binders: "∀a b δ:real.",
		Hypotheses: []string{
			"a < b",
			"&0 < δ",
		},
		Conclusion: "∃n:num. ∃p:(num → real). ∃h:real. " +
			"    &0 < h ∧ «finePartition»(a, b, δ, n, p, p) ∧ (∀i:num. i ≤ n ⇒ p(i + 1) - p(i) = h)",
	},
		func(arg *Argument, a, b, δ *Expr[Real], wide, pos Fact) {
			N, room := arg.ObtainAs[Nat](
				"by Archimedes some N copies of δ exceed the length b − a",
				"∃N:num. b - a < &N * δ",
				By(pos, real_archimedean.Archimedean.At(δ, arg.TermAs[Real]("b - a"))))
			h, hDef := arg.LetAs[Real]("h", "(b - a) / (&N + &1)")
			count := arg.Have(
				"N + 1 pieces are a positive count",
				"&0 < &N + &1",
				ByArith())
			piece := arg.Have(
				"N + 1 pieces of length h fill ⟦a, b⟧, and h lies strictly between 0 and δ",
				"(&N + &1) * h = b - a ∧ &0 < h ∧ h < δ",
				ByArith(hDef, wide, pos, count, room))
			arg.Take(N)
			arg.Take(arg.TermAs[Fun[Nat, Real]]("λi:num. a + &i * h"))
			arg.Take(h)
			arg.Show(
				"the points a + i·h run from a to b in steps of h, each piece tagged at its left end",
				Simp(Fwd(real_construction.OfNumAdd)),
				ByArith(piece))
		}),
})}

// FinePartitionExists — an interval has tagged partitions as fine as we
// like. A nondegenerate one is cut into pieces of one length shorter than
// δ, each tagged at its left end (UniformFinePartition); a one-point
// interval is one piece of length 0.
var FinePartitionExists = finePartitionExistsThm{family.Add(registry.ProofEntry{
	Name: "FinePartitionExists",
	Key:  "prop_4cb47fdc7626366b",
	Build: family.Theorem(Statement{
		Binders: "∀a b δ:real.",
		Hypotheses: []string{
			"a ≤ b",
			"&0 < δ",
		},
		Conclusion: "∃n:num. ∃p t:(num → real). «finePartition»(a, b, δ, n, p, t)",
	},
		func(arg *Argument, a, b, δ *Expr[Real], ordered, pos Fact) {
			arg.Cases(arg.Term("a < b"))
			arg.When(
				"a nondegenerate interval is cut into equal pieces shorter than δ",
				func(c *Argument, wide Fact) {
					n, p, _, uniform := c.Obtain3As[Nat, Fun[Nat, Real], Real](
						"⟦a, b⟧ has a partition into n + 1 pieces of one "+
							"length h shorter than δ, tagged at their left ends",
						"∃n:num. ∃p:(num → real). ∃h:real. "+
							"    &0 < h ∧ «finePartition»(a, b, δ, n, p, p) ∧ (∀i:num. i ≤ n ⇒ p(i + 1) - p(i) = h)",
						By(UniformFinePartition, wide, pos))
					c.Take(n)
					c.Take(p)
					c.Take(p)
					c.Show(
						"that partition, tagged at the left ends, serves",
						By(uniform))
				})
			arg.Otherwise(
				"a one-point interval is one piece of length 0",
				func(c *Argument, flat Fact) {
					point := c.TermAs[Fun[Nat, Real]]("λk:num. a")
					c.Take(c.TermAs[Nat]("0"))
					c.Take(point)
					c.Take(point)
					c.Show(
						"the piece from a to b = a, tagged at a, is shorter than δ",
						ByArith(flat, ordered, pos))
				})
		}),
})}

// FinePartitionMono — a partition finer than δ₁ is finer than any δ₂ at
// least δ₁: each piece shorter than δ₁ is shorter than δ₂.
var FinePartitionMono = finePartitionMonoThm{family.Add(registry.ProofEntry{
	Name: "FinePartitionMono",
	Key:  "prop_261d31c107dd9b4c",
	Build: family.Theorem(Statement{
		Binders: "∀a b δ₁ δ₂:real. ∀n:num. ∀p t:(num → real).",
		Hypotheses: []string{
			"«finePartition»(a, b, δ₁, n, p, t)",
			"δ₁ ≤ δ₂",
		},
		Conclusion: "«finePartition»(a, b, δ₂, n, p, t)",
	},
		func(
			arg *Argument,
			a, b, δ1, δ2 *Expr[Real],
			n *Expr[Nat],
			p, t *Arrow[Nat, Real],
			start, end, pieces, coarser Fact,
		) {
			arg.Show(
				"each piece shorter than δ₁ is shorter than δ₂",
				ByArith(start, end, pieces, coarser))
		}),
})}

// FinePartitionIsPartition — the points of a tagged partition of ⟦a, b⟧
// rise from a to b: each piece holds its tag between its two ends.
var FinePartitionIsPartition = finePartitionIsPartitionThm{family.Add(registry.ProofEntry{
	Name: "FinePartitionIsPartition",
	Key:  "prop_8f9954dca81ca881",
	Build: family.Theorem(Statement{
		Binders: "∀a b δ:real. ∀n:num. ∀p t:(num → real).",
		Hypotheses: []string{
			"«finePartition»(a, b, δ, n, p, t)",
		},
		Conclusion: "«partition»(a, b, n, p)",
	},
		func(
			arg *Argument,
			a, b, δ *Expr[Real],
			n *Expr[Nat],
			p, t *Arrow[Nat, Real],
			start, end, pieces Fact,
		) {
			arg.Show(
				"each piece holds its tag between its two ends, so the points rise from a to b",
				ByArith(start, end, pieces))
		}),
})}

// PartitionPiecesInInterval — each piece of a partition of ⟦a, b⟧ lies in
// ⟦a, b⟧. The preorder interval law composes the adjacent rises from
// p(0) = a to each piece and from that piece to p(n + 1) = b.
var PartitionPiecesInInterval = partitionPiecesInIntervalThm{family.Add(registry.ProofEntry{
	Name: "PartitionPiecesInInterval",
	Key:  "prop_6142bba1afe7eeec",
	Build: family.Theorem(Statement{
		Binders: "∀a b:real. ∀n:num. ∀p:(num → real). ∀k:num.",
		Hypotheses: []string{
			"«partition»(a, b, n, p)",
			"k ≤ n",
		},
		Conclusion: "a ≤ p(k) ∧ p(k) ≤ p(k + 1) ∧ p(k + 1) ≤ b",
	},
		func(arg *Argument, a, b *Expr[Real], n *Expr[Nat], p *Arrow[Nat, Real], k *Expr[Nat],
			start, end, rising, inside Fact) {
			preorder := arg.Have(
				"the real order is reflexive and transitive",
				"preorder(λx:real. λy:real. x ≤ y)",
				order.Preorder.Intro(
					Case(
						"each real is below itself",
						Unfold(equivalence.ReflexiveDef),
						Cite(real_order_ring.LessEqRefl)),
					Case(
						"two comparisons compose",
						Unfold(equivalence.TransitiveDef),
						Cite(real_construction.LessEqTrans))))
			bounds := arg.Have(
				"the piece lies above the first point and below the last point",
				"p(0) ≤ p(k) ∧ p(k + 1) ≤ p(n + 1)",
				ByArith(
					rising,
					inside,
					order.MonotoneOnNatInterval.Read(preorder).At(p, arg.TermAs[Nat]("0"), k),
					order.MonotoneOnNatInterval.Read(preorder).At(
						p, arg.TermAs[Nat]("k + 1"), arg.TermAs[Nat]("n + 1"))))
			arg.Show(
				"a = p(0) ≤ p(k) ≤ p(k + 1) ≤ p(n + 1) = b",
				ByArith(bounds, rising.At(k), inside, start, end))
		}),
})}

// PartitionTagsInInterval — the tags of a tagged partition of ⟦a, b⟧ lie
// in ⟦a, b⟧. Each point is at most the next, the tag lying between them,
// so the points are a partition of ⟦a, b⟧, whose pieces lie in ⟦a, b⟧
// (PartitionPiecesInInterval); a tag t(k) lies in piece k.
var PartitionTagsInInterval = partitionTagsInIntervalThm{family.Add(registry.ProofEntry{
	Name: "PartitionTagsInInterval",
	Key:  "prop_3b73c3b3d2b7886b",
	Build: family.Theorem(Statement{
		Binders: "∀a b:real. ∀n:num. ∀p t:(num → real). ∀k:num.",
		Hypotheses: []string{
			"p(0) = a",
			"p(n + 1) = b",
			"∀j:num. j ≤ n ⇒ p(j) ≤ t(j) ∧ t(j) ≤ p(j + 1)",
			"k ≤ n",
		},
		Conclusion: "a ≤ t(k) ∧ t(k) ≤ b",
	},
		func(arg *Argument, a, b *Expr[Real], n *Expr[Nat], p, t *Arrow[Nat, Real], k *Expr[Nat],
			start, end, tagged, inside Fact) {
			rising := arg.Have(
				"each point is at most the next, the tag lying between them",
				"«partition»(a, b, n, p)",
				ByArith(start, end, tagged))
			arg.Show(
				"a ≤ p(k) ≤ t(k) ≤ p(k + 1) ≤ b, piece k lying in ⟦a, b⟧",
				ByArith(PartitionPiecesInInterval.At(a, b, n, p, k), rising, inside, tagged.At(k)))
		}),
})}

// PartitionPieceContains — a point between the first and the last point of
// a run of points lies in one of the pieces between consecutive points. By
// induction on the number of pieces: one piece further, the point lies
// below p(n + 1), in an earlier piece, or above it, in the last one.
var PartitionPieceContains = partitionPieceContainsThm{family.Add(registry.ProofEntry{
	Name: "PartitionPieceContains",
	Key:  "prop_3b28f7ab6afd20db",
	Build: family.Theorem(Statement{
		Binders: "∀p:(num → real). ∀x:real. ∀n:num.",
		Hypotheses: []string{
			"p(0) ≤ x",
			"x ≤ p(n + 1)",
		},
		Conclusion: "∃k:num. k ≤ n ∧ p(k) ≤ x ∧ x ≤ p(k + 1)",
	},
		func(arg *Argument, p *Arrow[Nat, Real], x *Expr[Real]) {
			arg.Induct("n")
			arg.Base(
				"between p(0) and p(1) the point lies in the first piece",
				func(c *Argument) {
					within := c.Assume()
					c.Take(c.TermAs[Nat]("0"))
					c.Show(
						"piece 0 holds x",
						By(within))
				})
			arg.Step(
				"one piece further, x lies below p(n + 1), in an earlier piece, or above it, in the last one",
				func(c *Argument, ih Fact) {
					within := c.Simplified(c.Assume(), Fwd(nat_arith.Add1))
					c.Cases(c.Term("x ≤ p(n + 1)"))
					c.When(
						"below p(n + 1) an earlier piece holds x",
						func(d *Argument, below Fact) {
							k, piece := d.ObtainAs[Nat](
								"some piece k up to n holds x",
								"∃k:num. k ≤ n ∧ p(k) ≤ x ∧ x ≤ p(k + 1)",
								By(ih, below, within))
							d.Take(k)
							d.Show(
								"and k is a piece of the longer run too",
								ByArith(piece))
						})
					c.Otherwise(
						"above p(n + 1) the last piece holds x",
						func(d *Argument, above Fact) {
							d.Take(d.TermAs[Nat]("n + 1"))
							d.Show(
								"x lies between p(n + 1) and p(n + 2)",
								ByArith(above, within))
						})
				})
		}),
})}

// RiemannSumRetag — moving one tag moves one term: tagging piece k at x
// instead of t(k) changes the Riemann sum by f(x) − f(t(k)) times the
// length of the piece. Term by term the new sum is the old one plus that
// change at index k and 0 elsewhere, and the changes sum to the one at k.
var RiemannSumRetag = riemannSumRetagThm{family.Add(registry.ProofEntry{
	Name: "RiemannSumRetag",
	Key:  "prop_69ca91b2a8ce348d",
	Build: family.Theorem(Statement{
		Binders: "∀f:(real → real). ∀n:num. ∀p t:(num → real). ∀k:num. ∀x:real.",
		Hypotheses: []string{
			"k ≤ n",
		},
		Conclusion: "«riemannSum»(f, n, p, λi:num. COND(i = k, x, t(i))) = " +
			"«riemannSum»(f, n, p, t) + «change»",
		Abbrev: Abbrev{
			{Name: "change", Text: "(f(x) - f(t(k))) * (p(k + 1) - p(k))"},
		},
	},
		func(
			arg *Argument,
			f *Arrow[Real, Real],
			n *Expr[Nat],
			p, t *Arrow[Nat, Real],
			k *Expr[Nat],
			x *Expr[Real],
			inside Fact,
		) {
			termwise := arg.Have(
				"term by term the new sum is the old one plus the change at index k",
				"∀i:num. "+
					"    f(COND(i = k, x, t(i))) * (p(i + 1) - p(i)) = "+
					"    f(t(i)) * (p(i + 1) - p(i)) + COND(i = k, «change», &0)",
				Derive(func(c *Argument) {
					c.FixAs[Nat]()
					c.Cases(c.Term("i = k"))
					c.When(
						"at index k the tag is x",
						func(d *Argument, at Fact) {
							d.Show(
								"f(x) times the piece is f(t(k)) times it plus the change",
								ByArith(at))
						})
					c.Otherwise(
						"elsewhere the tag stays",
						func(d *Argument, other Fact) {
							d.Show(
								"and the term is unchanged",
								ByArith(other))
						})
				}))
			spread := arg.Have(
				"so the new sum is the sum of the old terms plus the changes",
				"«riemannSum»(f, n, p, λi:num. COND(i = k, x, t(i))) = "+
					"Σ_{i∈0 .. n} (f(t(i)) * (p(i + 1) - p(i)) + COND(i = k, «change», &0))",
				By(termwise, real_sum.IntervalCongruence))
			single := arg.Have(
				"and the changes sum to the one at k, an index among 0 .. n",
				"Σ_{i∈0 .. n} COND(i = k, «change», &0) = «change»",
				By(inside, real_sum.Delta, num_segment.MembershipFromZero))
			arg.Show(
				"adding the old sum and the change",
				ByArith(
					spread,
					single,
					real_sum.IntervalAdd.At(
						arg.TermAs[Nat]("0"),
						n,
						arg.TermAs[Fun[Nat, Real]]("λi:num. f(t(i)) * (p(i + 1) - p(i))"),
						arg.TermAs[Fun[Nat, Real]]("λi:num. COND(i = k, «change», &0)"))))
		}),
})}

// HasIntegralOrdered — an interval over which a function has an integral
// is ordered: a ≤ b is the first clause of the definition.
var HasIntegralOrdered = hasIntegralOrderedThm{family.Add(registry.ProofEntry{
	Name: "HasIntegralOrdered",
	Key:  "prop_3feafe8aaedbc50",
	Build: family.Theorem(Statement{
		Binders: "∀f:(real → real). ∀a b I:real.",
		Hypotheses: []string{
			"real_has_integral(f, a, b, I)",
		},
		Conclusion: "a ≤ b",
	},
		func(arg *Argument, f *Arrow[Real, Real], a, b, I *Expr[Real], toI Fact) {
			arg.Show(
				"the definition of the integral asks a ≤ b first",
				By(toI, RealHasIntegralDef))
		}),
})}

// CommonMesh — two integrals over one interval share, for every ε, one
// mesh below which the Riemann sums of both functions are within ε of
// their integrals: the smaller of the two meshes the integrals hand over.
var CommonMesh = commonMeshThm{family.Add(registry.ProofEntry{
	Name: "CommonMesh",
	Key:  "prop_e7bf32e3a6144bc8",
	Build: family.Theorem(Statement{
		Binders: "∀f g:(real → real). ∀a b I J ε:real.",
		Hypotheses: []string{
			"real_has_integral(f, a, b, I)",
			"real_has_integral(g, a, b, J)",
			"&0 < ε",
		},
		Conclusion: "∃δ:real. " +
			"    &0 < δ ∧ " +
			"    (∀n:num. ∀p t:(num → real). " +
			"        «finePartition»(a, b, δ, n, p, t) ⇒ " +
			"        |«riemannSum»(f, n, p, t) - I| < ε ∧ |«riemannSum»(g, n, p, t) - J| < ε)",
	},
		func(arg *Argument, f, g *Arrow[Real, Real], a, b, I, J, ε *Expr[Real], toI, toJ, pos Fact) {
			nearI := arg.Unfolded(toI, RealHasIntegralDef)
			nearJ := arg.Unfolded(toJ, RealHasIntegralDef)
			_, fineI := arg.Obtain(
				"at ε the integral of f hands over a mesh δ₁ below which f's Riemann sums are within ε of I",
				"∃δ₁:real. "+
					"    &0 < δ₁ ∧ "+
					"    (∀n:num. ∀p t:(num → real). "+
					"        «finePartition»(a, b, δ₁, n, p, t) ⇒ |«riemannSum»(f, n, p, t) - I| < ε)",
				By(nearI, pos))
			_, fineJ := arg.Obtain(
				"and the integral of g a mesh δ₂ below which g's Riemann sums are within ε of J",
				"∃δ₂:real. "+
					"    &0 < δ₂ ∧ "+
					"    (∀n:num. ∀p t:(num → real). "+
					"        «finePartition»(a, b, δ₂, n, p, t) ⇒ |«riemannSum»(g, n, p, t) - J| < ε)",
				By(nearJ, pos))
			meshI := arg.Conjuncts(
				fineI,
				"δ₁ is positive",
				"below δ₁ the Riemann sums of f are within ε of I")
			meshJ := arg.Conjuncts(
				fineJ,
				"δ₂ is positive",
				"below δ₂ the Riemann sums of g are within ε of J")
			arg.Take(arg.TermAs[Real]("min(δ₁, δ₂)"))
			arg.Show(
				"the smaller of the two meshes serves both integrals",
				SplitConj(
					Case(
						"the smaller of two positive meshes is positive",
						ByArith(meshI[0], meshJ[0])),
					Case(
						"a partition finer than min(δ₁, δ₂) is finer than δ₁ and than δ₂",
						Derive(func(c *Argument) {
							n := c.FixAs[Nat]()
							p := c.FixAs[Fun[Nat, Real]]()
							t := c.FixAs[Fun[Nat, Real]]()
							partition := c.Conjuncts(
								c.Assume(),
								"the points start at a",
								"and end at b",
								"each tag lies in its piece, and each piece is shorter than min(δ₁, δ₂)")
							finerI := c.Have(
								"so each piece is shorter than δ₁",
								"∀k:num. k ≤ n ⇒ p(k) ≤ t(k) ∧ t(k) ≤ p(k + 1) ∧ p(k + 1) - p(k) < δ₁",
								c.ForEach(func(k *Expr[Nat]) Action { return ByArith(partition[2].At(k)) }))
							finerJ := c.Have(
								"and shorter than δ₂",
								"∀k:num. k ≤ n ⇒ p(k) ≤ t(k) ∧ t(k) ≤ p(k + 1) ∧ p(k + 1) - p(k) < δ₂",
								c.ForEach(func(k *Expr[Nat]) Action { return ByArith(partition[2].At(k)) }))
							c.Show(
								"so f's Riemann sum is within ε of I and g's within ε of J",
								By(meshI[1].At(n, p, t), meshJ[1].At(n, p, t), partition[0], partition[1], finerI, finerJ))
						}))))
		}),
})}

// HasIntegralUnique — a function has at most one integral over an
// interval. Were I ≠ J, the two integrals would share a mesh at
// ε = |I − J|/2, and a partition finer than it would have a Riemann sum
// within ε of both I and J, which lie 2ε apart.
var HasIntegralUnique = hasIntegralUniqueThm{family.Add(registry.ProofEntry{
	Name: "HasIntegralUnique",
	Key:  "prop_eb474a5db9c1f5c2",
	Build: family.Theorem(Statement{
		Binders: "∀f:(real → real). ∀a b I J:real.",
		Hypotheses: []string{
			"real_has_integral(f, a, b, I)",
			"real_has_integral(f, a, b, J)",
		},
		Conclusion: "I = J",
	},
		func(arg *Argument, f *Arrow[Real, Real], a, b, I, J *Expr[Real], toI, toJ Fact) {
			apart := arg.SupposeNot()
			pos := arg.Have(
				"half the distance from I to J is positive",
				"&0 < |I - J| / &2",
				ByArith(apart))
			_, shared := arg.Obtain(
				"the two integrals share a mesh δ at ε = |I − J|/2",
				"∃δ:real. "+
					"    &0 < δ ∧ "+
					"    (∀n:num. ∀p t:(num → real). "+
					"        «finePartition»(a, b, δ, n, p, t) ⇒ "+
					"        |«riemannSum»(f, n, p, t) - I| < |I - J| / &2 ∧ "+
					"        |«riemannSum»(f, n, p, t) - J| < |I - J| / &2)",
				By(CommonMesh, toI, toJ, pos))
			mesh := arg.Conjuncts(
				shared,
				"δ is positive",
				"below δ every Riemann sum of f is within |I − J|/2 of I and of J")
			n, p, t, fine := arg.Obtain3(
				"⟦a, b⟧ has a tagged partition finer than δ",
				"∃n:num. ∃p t:(num → real). «finePartition»(a, b, δ, n, p, t)",
				By(FinePartitionExists, HasIntegralOrdered.At(f, a, b, I), toI, mesh[0]))
			arg.Show(
				"its Riemann sum is within |I − J|/2 of both I and J, so |I − J| < |I − J|",
				ByArith(mesh[1].At(n, p, t), fine))
		}),
})}

// HasIntegralValue — the oriented integral of a function over an interval
// on which it has integral I is I: the interval is ordered, so the value
// is the integral the definition chooses, and f has only one.
var HasIntegralValue = hasIntegralValueThm{family.Add(registry.ProofEntry{
	Name: "HasIntegralValue",
	Key:  "prop_4287d9e8574a3065",
	Build: family.Theorem(Statement{
		Binders: "∀f:(real → real). ∀a b I:real.",
		Hypotheses: []string{
			"real_has_integral(f, a, b, I)",
		},
		Conclusion: "real_integral(f, a, b) = I",
	},
		func(arg *Argument, f *Arrow[Real, Real], a, b, I *Expr[Real], toI Fact) {
			_, chosen := arg.ObtainChosen(
				"so the definition chooses an integral of f over ⟦a, b⟧",
				"∃J:real. real_has_integral(f, a, b, J)",
				toI)
			arg.Show(
				"on an ordered interval the value is the chosen integral, which is I since f has only one",
				Unfold(RealIntegralDef),
				By(HasIntegralOrdered.At(f, a, b, I), toI, chosen, HasIntegralUnique))
		}),
})}
