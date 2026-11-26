// additivity.go — the integral is additive over intervals: integrals over
// two adjacent intervals add up to the integral over their union, and the
// oriented integral of a continuous function adds over any three points.

package real_integral

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	"github.com/euc-ai/xugo/library/proofs/real/real_continuous"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/registry"
)

// HasIntegralSplit — integrals over adjacent intervals add: f has integral
// I on ⟦a, c⟧ and J on ⟦c, b⟧, so it has integral I + J on ⟦a, b⟧.
//
// f is bounded on ⟦a, b⟧, by M say. Clamp a partition of ⟦a, b⟧ finer than δ
// to ⟦a, c⟧ — points and tags taken min(c, ·) — and to ⟦c, b⟧ — max(c, ·):
// both are partitions no coarser than the original. Their two Riemann
// sums add up to that of the original but on the piece across c, where
// the tag moves to c on one side: the error there is f(t) − f(c), at most
// 2M in size, times the part of the piece on the other side of c, which
// lies within δ of c. Clamping the points into ⟦c, c + δ⟧ and into
// ⟦c − δ, c⟧ measures those parts; the clamped points rise by at most δ in
// all, so the error is at most 4Mδ.
var HasIntegralSplit = hasIntegralSplitThm{family.Add(registry.ProofEntry{
	Name: "HasIntegralSplit",
	Key:  "prop_7f0e0768ad8b8818",
	Build: family.Theorem(Statement{
		Binders: "∀f:(real → real). ∀a c b I J:real.",
		Hypotheses: []string{
			"a ≤ c",
			"c ≤ b",
			"real_has_integral(f, a, c, I)",
			"real_has_integral(f, c, b, J)",
		},
		Conclusion: "real_has_integral(f, a, b, I + J)",
		Abbrev: Abbrev{
			{Name: "splitError", Text: "λp:real. λq:real. λt:real. " +
				"    f(t) * (q - p) - " +
				"    f(min(c, t)) * (min(c, q) - min(c, p)) - " +
				"    f(max(c, t)) * (max(c, q) - max(c, p))"},
			{Name: "above", Text: "λδ:real. λz:real. max(c, min(c + δ, z))"},
			{Name: "below", Text: "λδ:real. λz:real. min(c, max(c - δ, z))"},
		},
	},
		func(arg *Argument, f *Arrow[Real, Real], a, c, b, I, J *Expr[Real], ac, cb, toI, toJ Fact) {
			_, left := arg.ObtainAs[Real](
				"f is bounded on ⟦a, c⟧",
				"∃B₁:real. ∀x:real. a ≤ x ∧ x ≤ c ⇒ |f(x)| ≤ B₁",
				By(IntegrableBounded, toI))
			_, right := arg.ObtainAs[Real](
				"and on ⟦c, b⟧",
				"∃B₂:real. ∀x:real. c ≤ x ∧ x ≤ b ⇒ |f(x)| ≤ B₂",
				By(IntegrableBounded, toJ))
			_, bound := arg.ObtainAs[Real](
				"so it is bounded on ⟦a, b⟧, by M say",
				"∃M:real. &0 ≤ M ∧ (∀x:real. a ≤ x ∧ x ≤ b ⇒ |f(x)| ≤ M)",
				Derive(func(d *Argument) {
					covers := d.Have(
						"|B₁| + |B₂| bounds f on either side of c",
						"∀x:real. a ≤ x ∧ x ≤ b ⇒ |f(x)| ≤ |B₁| + |B₂|",
						Derive(func(e *Argument) {
							x := e.FixAs[Real]()
							within := e.Assume()
							e.Cases(e.Term("x ≤ c"))
							e.When(
								"left of c, B₁ bounds f",
								func(g *Argument, onLeft Fact) {
									g.Show(
										"and B₁ is at most |B₁| + |B₂|",
										ByArith(left.At(x), within, onLeft))
								})
							e.Otherwise(
								"right of c, B₂ bounds f",
								func(g *Argument, onRight Fact) {
									g.Show(
										"and B₂ is at most |B₁| + |B₂|",
										ByArith(right.At(x), within, onRight))
								})
						}))
					d.Take(d.TermAs[Real]("|B₁| + |B₂|"))
					d.Show(
						"a sum of sizes is not negative",
						ByArith(covers))
				}))
			sizes := arg.Conjuncts(
				bound,
				"M is not negative",
				"M bounds |f| on ⟦a, b⟧")
			clamp := arg.Have(
				"splitting one term at c costs at most 2M times the parts of its piece within δ of c",
				Statement{
					Binders: "∀δ p q t:real.",
					Hypotheses: []string{
						"a ≤ p ∧ p ≤ t ∧ t ≤ q ∧ q ≤ b ∧ q - p < δ",
					},
					Conclusion: "|«splitError»(p, q, t)| ≤ " +
						"&2 * M * ((«above»(δ, q) - «above»(δ, p)) + («below»(δ, q) - «below»(δ, p)))",
				},
				Derive(func(d *Argument) {
					d.FixAs[Real]()
					d.FixAs[Real]()
					d.FixAs[Real]()
					t := d.FixAs[Real]()
					piece := d.Assume()
					rises := d.Have(
						"the clamped points do not fall",
						"&0 ≤ «above»(δ, q) - «above»(δ, p) ∧ &0 ≤ «below»(δ, q) - «below»(δ, p)",
						ByArith(piece))
					values := d.Have(
						"|f| is at most M at the tag and at c",
						"|f(t)| ≤ M ∧ |f(c)| ≤ M",
						ByArith(sizes[1].At(t), sizes[1].At(c), piece, ac, cb))
					d.Cases(d.Term("t ≤ c"))
					d.When(
						"tagged left of c, the term moves only on the part of the piece right of c",
						func(e *Argument, tagLeft Fact) {
							e.Cases(e.Term("q ≤ c"))
							e.When(
								"a piece left of c is not split at all",
								func(g *Argument, pieceLeft Fact) {
									ends := g.Have(
										"each point lies left of c",
										"min(c, t) = t ∧ max(c, t) = c ∧ min(c, p) = p ∧ max(c, p) = c ∧ min(c, q) = q ∧ max(c, q) = c",
										ByArith(piece, tagLeft, pieceLeft))
									g.Show(
										"so nothing is lost",
										ByArith(
											ends,
											rises,
											sizes[0],
											real_order_ring.LessEqMulLeft.At(
												g.TermAs[Real]("&2 * M"),
												g.TermAs[Real]("&0"),
												g.TermAs[Real]("(«above»(δ, q) - «above»(δ, p)) + («below»(δ, q) - «below»(δ, p))"))))
								})
							e.Otherwise(
								"a piece across c loses f(t) − f(c) times its part right of c, which is within δ of c",
								func(g *Argument, across Fact) {
									ends := g.Have(
										"the points left of c and right of it, clamped",
										"min(c, t) = t ∧ "+
											"max(c, t) = c ∧ "+
											"min(c, p) = p ∧ "+
											"max(c, p) = c ∧ "+
											"min(c, q) = c ∧ "+
											"max(c, q) = q ∧ "+
											"«above»(δ, q) = q ∧ "+
											"«above»(δ, p) = c",
										ByArith(piece, tagLeft, across))
									g.Show(
										"f(t) − f(c) is at most 2M in size",
										ByArith(
											ends,
											rises,
											values,
											piece,
											real_order_ring.LessEqMulRight.At(
												g.TermAs[Real]("f(t) - f(c)"),
												g.TermAs[Real]("&2 * M"),
												g.TermAs[Real]("q - c")),
											real_order_ring.LessEqMulRight.At(
												g.TermAs[Real]("f(c) - f(t)"),
												g.TermAs[Real]("&2 * M"),
												g.TermAs[Real]("q - c")),
											real_order_ring.LessEqMulLeft.At(
												g.TermAs[Real]("&2 * M"),
												g.TermAs[Real]("&0"),
												g.TermAs[Real]("«below»(δ, q) - «below»(δ, p)"))))
								})
						})
					d.Otherwise(
						"tagged right of c, the term moves only on the part of the piece left of c",
						func(e *Argument, tagRight Fact) {
							e.Cases(e.Term("c ≤ p"))
							e.When(
								"a piece right of c is not split at all",
								func(g *Argument, pieceRight Fact) {
									ends := g.Have(
										"each point lies right of c",
										"min(c, t) = c ∧ max(c, t) = t ∧ min(c, p) = c ∧ max(c, p) = p ∧ min(c, q) = c ∧ max(c, q) = q",
										ByArith(piece, tagRight, pieceRight))
									g.Show(
										"so nothing is lost",
										ByArith(
											ends,
											rises,
											sizes[0],
											real_order_ring.LessEqMulLeft.At(
												g.TermAs[Real]("&2 * M"),
												g.TermAs[Real]("&0"),
												g.TermAs[Real]("(«above»(δ, q) - «above»(δ, p)) + («below»(δ, q) - «below»(δ, p))"))))
								})
							e.Otherwise(
								"a piece across c loses f(t) − f(c) times its part left of c, which is within δ of c",
								func(g *Argument, across Fact) {
									ends := g.Have(
										"the points left of c and right of it, clamped",
										"min(c, t) = c ∧ "+
											"max(c, t) = t ∧ "+
											"min(c, p) = p ∧ "+
											"max(c, p) = c ∧ "+
											"min(c, q) = c ∧ "+
											"max(c, q) = q ∧ "+
											"«below»(δ, q) = c ∧ "+
											"«below»(δ, p) = p",
										ByArith(piece, tagRight, across))
									g.Show(
										"f(t) − f(c) is at most 2M in size",
										ByArith(
											ends,
											rises,
											values,
											piece,
											real_order_ring.LessEqMulRight.At(
												g.TermAs[Real]("f(t) - f(c)"),
												g.TermAs[Real]("&2 * M"),
												g.TermAs[Real]("c - p")),
											real_order_ring.LessEqMulRight.At(
												g.TermAs[Real]("f(c) - f(t)"),
												g.TermAs[Real]("&2 * M"),
												g.TermAs[Real]("c - p")),
											real_order_ring.LessEqMulLeft.At(
												g.TermAs[Real]("&2 * M"),
												g.TermAs[Real]("&0"),
												g.TermAs[Real]("«above»(δ, q) - «above»(δ, p)"))))
								})
						})
				}))
			nearI := arg.Conjuncts(
				arg.Unfolded(toI, RealHasIntegralDef),
				"⟦a, c⟧ is ordered",
				"for every ε some mesh brings the Riemann sums of f on ⟦a, c⟧ within ε of I")
			nearJ := arg.Conjuncts(
				arg.Unfolded(toJ, RealHasIntegralDef),
				"⟦c, b⟧ is ordered",
				"for every ε some mesh brings the Riemann sums of f on ⟦c, b⟧ within ε of J")
			approach := arg.Have(
				"for every ε some mesh brings the Riemann sums of f on ⟦a, b⟧ within ε of I + J",
				Statement{
					Binders: "∀ε:real.",
					Hypotheses: []string{
						"&0 < ε",
					},
					Conclusion: "∃δ:real. " +
						"    &0 < δ ∧ " +
						"    (∀n:num. ∀p t:(num → real). " +
						"        «finePartition»(a, b, δ, n, p, t) ⇒ |«riemannSum»(f, n, p, t) - (I + J)| < ε)",
				},
				Derive(func(d *Argument) {
					d.FixAs[Real]()
					pos := d.Assume()
					third := d.Have(
						"ε/3 is positive",
						"&0 < ε / &3",
						ByArith(pos))
					_, meshI := d.ObtainAs[Real](
						"the integral on ⟦a, c⟧ gives a mesh δ₁ at ε/3",
						"∃δ₁:real. "+
							"    &0 < δ₁ ∧ "+
							"    (∀n:num. ∀p t:(num → real). "+
							"        «finePartition»(a, c, δ₁, n, p, t) ⇒ |«riemannSum»(f, n, p, t) - I| < ε / &3)",
						By(nearI[1].At(d.TermAs[Real]("ε / &3")), third))
					_, meshJ := d.ObtainAs[Real](
						"and the integral on ⟦c, b⟧ a mesh δ₂",
						"∃δ₂:real. "+
							"    &0 < δ₂ ∧ "+
							"    (∀n:num. ∀p t:(num → real). "+
							"        «finePartition»(c, b, δ₂, n, p, t) ⇒ |«riemannSum»(f, n, p, t) - J| < ε / &3)",
						By(nearJ[1].At(d.TermAs[Real]("ε / &3")), third))
					fineI := d.Conjuncts(
						meshI,
						"δ₁ is positive",
						"below δ₁ the Riemann sums on ⟦a, c⟧ are within ε/3 of I")
					fineJ := d.Conjuncts(
						meshJ,
						"δ₂ is positive",
						"below δ₂ the Riemann sums on ⟦c, b⟧ are within ε/3 of J")
					small := d.Have(
						"the mesh δ₃ = ε/(12(M + 1)) is positive, and 4M·δ₃ is below ε/3",
						"&0 < ε / (&12 * (M + &1)) ∧ &4 * M * (ε / (&12 * (M + &1))) < ε / &3",
						ByArith(pos, sizes[0]))
					μ, μDef := d.LetAs[Real]("μ", "min(δ₁, min(δ₂, ε / (&12 * (M + &1))))")
					d.Take(μ)
					fineSum := d.Have(
						"below μ, the smallest of δ₁, δ₂ and δ₃, every Riemann sum on ⟦a, b⟧ is within ε of I + J",
						Statement{
							Binders: "∀n:num. ∀p t:(num → real).",
							Hypotheses: []string{
								"«finePartition»(a, b, μ, n, p, t)",
							},
							Conclusion: "|«riemannSum»(f, n, p, t) - (I + J)| < ε",
						},
						Derive(func(g *Argument) {
							n := g.FixAs[Nat]()
							p := g.FixAs[Fun[Nat, Real]]()
							t := g.FixAs[Fun[Nat, Real]]()
							fine := g.Assume()
							parts := g.Conjuncts(
								fine,
								"p starts at a",
								"and ends at b",
								"each piece holds its tag and is shorter than μ")
							rising := g.Have(
								"the points rise from a to b",
								"«partition»(a, b, n, p)",
								By(FinePartitionIsPartition.At(a, b, μ, n, p, t), fine))
							toLeft := g.Have(
								"clamped to ⟦a, c⟧, p is a partition of ⟦a, c⟧ finer than δ₁",
								"«finePartition»(a, c, δ₁, n, λk:num. min(c, p(k)), λk:num. min(c, t(k)))",
								ByArith(parts[0], parts[1], parts[2], ac, cb, μDef))
							toRight := g.Have(
								"clamped to ⟦c, b⟧, p is a partition of ⟦c, b⟧ finer than δ₂",
								"«finePartition»(c, b, δ₂, n, λk:num. max(c, p(k)), λk:num. max(c, t(k)))",
								ByArith(parts[0], parts[1], parts[2], ac, cb, μDef))
							nearLeft := g.Have(
								"so the Riemann sum of the clamp to ⟦a, c⟧ is within ε/3 of I",
								"|«riemannSum»(f, n, λk:num. min(c, p(k)), λk:num. min(c, t(k))) - I| < ε / &3",
								By(
									fineI[1].At(
										n,
										g.TermAs[Fun[Nat, Real]]("λk:num. min(c, p(k))"),
										g.TermAs[Fun[Nat, Real]]("λk:num. min(c, t(k))")),
									toLeft))
							nearRight := g.Have(
								"and that of the clamp to ⟦c, b⟧ within ε/3 of J",
								"|«riemannSum»(f, n, λk:num. max(c, p(k)), λk:num. max(c, t(k))) - J| < ε / &3",
								By(
									fineJ[1].At(
										n,
										g.TermAs[Fun[Nat, Real]]("λk:num. max(c, p(k))"),
										g.TermAs[Fun[Nat, Real]]("λk:num. max(c, t(k))")),
									toRight))
							termwise := g.Have(
								"term by term, splitting at c costs at most 2M times the parts of the piece within μ of c",
								Statement{
									Binders: "∀k:num.",
									Hypotheses: []string{
										"0 ≤ k ∧ k ≤ n",
									},
									Conclusion: "|«splitError»(p(k), p(k + 1), t(k))| ≤ " +
										"&2 * M * ((«above»(μ, p(k + 1)) - «above»(μ, p(k))) + («below»(μ, p(k + 1)) - «below»(μ, p(k))))",
								},
								Derive(func(h *Argument) {
									k := h.FixAs[Nat]("k")
									inside := h.Assume()
									h.Show(
										"piece k lies in ⟦a, b⟧, holds its tag and is shorter than μ",
										By(
											clamp.At(μ, h.TermAs[Real]("p(k)"), h.TermAs[Real]("p(k + 1)"), h.TermAs[Real]("t(k)")),
											PartitionPiecesInInterval.At(a, b, n, p, k),
											rising,
											inside,
											parts[2].At(k)))
								}))
							total := g.Have(
								"so the whole splitting error is at most 2M times the rises of the clamped points",
								"|Σ_{k∈0 .. n} «splitError»(p(k), p(k + 1), t(k))| ≤ "+
									"Σ_{k∈0 .. n} &2 * "+
									"M * "+
									"((«above»(μ, p(k + 1)) - «above»(μ, p(k))) + («below»(μ, p(k + 1)) - «below»(μ, p(k))))",
								By(termwise, real_sum.IntervalDominated))
							rises := g.Have(
								"the rises of the clamped points telescope from a to b, to their total rise w",
								"Σ_{k∈0 .. n} &2 * "+
									"M * "+
									"((«above»(μ, p(k + 1)) - «above»(μ, p(k))) + («below»(μ, p(k + 1)) - «below»(μ, p(k)))) = "+
									"&2 * M * ((«above»(μ, b) - «above»(μ, a)) + («below»(μ, b) - «below»(μ, a)))",
								ByArith(
									parts[0],
									parts[1],
									real_sum.ScalarLeft.At(
										g.TermAs[Real]("&2 * M"),
										g.TermAs[Fun[Nat, Real]](
											"λk:num. («above»(μ, p(k + 1)) - «above»(μ, p(k))) + («below»(μ, p(k + 1)) - «below»(μ, p(k)))"),
										g.TermAs[Set[Nat]]("0 .. n")),
									real_sum.IntervalAdd.At(
										g.TermAs[Nat]("0"),
										n,
										g.TermAs[Fun[Nat, Real]]("λk:num. «above»(μ, p(k + 1)) - «above»(μ, p(k))"),
										g.TermAs[Fun[Nat, Real]]("λk:num. «below»(μ, p(k + 1)) - «below»(μ, p(k))")),
									real_sum.TelescopeUp.At(
										g.TermAs[Nat]("0"), n, g.TermAs[Fun[Nat, Real]]("λk:num. «above»(μ, p(k))")),
									real_sum.TelescopeUp.At(
										g.TermAs[Nat]("0"), n, g.TermAs[Fun[Nat, Real]]("λk:num. «below»(μ, p(k))"))))
							w, wDef := g.LetAs[Real]("w", "(«above»(μ, b) - «above»(μ, a)) + («below»(μ, b) - «below»(μ, a))")
							reach := g.Have(
								"between a and b the clamped points rise by at most δ₃ each way",
								"w ≤ &2 * (ε / (&12 * (M + &1)))",
								ByArith(wDef, ac, cb, μDef, small, fineI[0], fineJ[0]))
							err := g.Have(
								"so the splitting error is at most 4Mδ₃",
								"|Σ_{k∈0 .. n} «splitError»(p(k), p(k + 1), t(k))| ≤ &4 * M * (ε / (&12 * (M + &1)))",
								ByArith(
									total,
									rises,
									reach,
									sizes[0],
									real_order_ring.LessEqMulLeft.At(
										g.TermAs[Real]("M"),
										w,
										g.TermAs[Real]("&2 * (ε / (&12 * (M + &1)))"))))
							g.Show(
								"the clamped sums are within ε/3 of I and of J, and they "+
									"add up to the Riemann sum but for the splitting error",
								ByArith(
									nearLeft,
									nearRight,
									err,
									small,
									real_sum.IntervalSub.At(
										g.TermAs[Nat]("0"),
										n,
										g.TermAs[Fun[Nat, Real]](
											"λk:num. f(t(k)) * (p(k + 1) - p(k)) - f(min(c, t(k))) * (min(c, p(k + 1)) - min(c, p(k)))"),
										g.TermAs[Fun[Nat, Real]]("λk:num. f(max(c, t(k))) * (max(c, p(k + 1)) - max(c, p(k)))")),
									real_sum.IntervalSub.At(
										g.TermAs[Nat]("0"),
										n,
										g.TermAs[Fun[Nat, Real]]("λk:num. f(t(k)) * (p(k + 1) - p(k))"),
										g.TermAs[Fun[Nat, Real]]("λk:num. f(min(c, t(k))) * (min(c, p(k + 1)) - min(c, p(k)))"))))
						}))
					d.Show(
						"so μ serves",
						ByArith(fineSum, fineI[0], fineJ[0], small, μDef))
				}))
			ordered := arg.Have(
				"⟦a, b⟧ is ordered",
				"a ≤ b",
				ByArith(ac, cb))
			arg.Show(
				"the Riemann sums of f on ⟦a, b⟧ tend to I + J",
				Unfold(RealHasIntegralDef),
				By(ordered, approach))
		}),
})}

// IntegrableSubinterval — a function with an integral over ⟦a, b⟧ has one
// over every interval ⟦c, d⟧ inside it, by the Cauchy criterion on both
// intervals. Given ε, the criterion on ⟦a, b⟧ hands over a mesh δ below
// which any two Riemann sums over ⟦a, b⟧ lie within ε. Two partitions of
// ⟦c, d⟧ finer than δ, each joined to the same partitions of ⟦a, c⟧ and of
// ⟦d, b⟧ finer than δ (PartitionJoin, twice), become partitions of ⟦a, b⟧
// finer than δ whose Riemann sums differ exactly as theirs do, so theirs
// lie within ε too.
var IntegrableSubinterval = integrableSubintervalThm{family.Add(registry.ProofEntry{
	Name: "IntegrableSubinterval",
	Key:  "prop_490d10c21d7e7fff",
	Build: family.Theorem(Statement{
		Binders: "∀f:(real → real). ∀a b c d I:real.",
		Hypotheses: []string{
			"real_has_integral(f, a, b, I)",
			"a ≤ c",
			"c ≤ d",
			"d ≤ b",
		},
		Conclusion: "∃J:real. real_has_integral(f, c, d, J)",
	},
		func(arg *Argument, f *Arrow[Real, Real], a, b, c, d, I *Expr[Real], toI, ac, cd, db Fact) {
			integrable := arg.Have(
				"f has an integral over ⟦a, b⟧",
				"∃J:real. real_has_integral(f, a, b, J)",
				By(Normalized, toI))
			near := arg.Have(
				"for every ε some mesh brings any two Riemann sums over ⟦c, d⟧ within ε of each other",
				"∀ε:real. &0 < ε ⇒ ∃δ:real. &0 < δ ∧ «sumsWithin»(f, c, d, δ, ε)",
				Derive(func(g *Argument) {
					g.FixAs[Real]()
					pos := g.Assume()
					δ, mesh := g.ObtainAs[Real](
						"by the Cauchy criterion over ⟦a, b⟧ a mesh δ brings any two Riemann sums within ε of each other",
						"∃δ:real. &0 < δ ∧ «sumsWithin»(f, a, b, δ, ε)",
						By(integrable, pos, IntegrableCauchy))
					fine := g.Conjuncts(
						mesh,
						"δ is positive",
						"below δ any two Riemann sums over ⟦a, b⟧ lie within ε of each other")
					within := g.Have(
						"two partitions of ⟦c, d⟧ finer than δ have Riemann sums within ε of each other",
						"«sumsWithin»(f, c, d, δ, ε)",
						Derive(func(h *Argument) {
							n := h.FixAs[Nat]()
							p := h.FixAs[Fun[Nat, Real]]()
							t := h.FixAs[Fun[Nat, Real]]()
							m := h.FixAs[Nat]()
							q := h.FixAs[Fun[Nat, Real]]()
							s := h.FixAs[Fun[Nat, Real]]()
							both := h.Assume()
							n1, p1, t1, left := h.Obtain3As[Nat, Fun[Nat, Real], Fun[Nat, Real]](
								"⟦a, c⟧ has a partition finer than δ",
								"∃n₁:num. ∃p₁ t₁:(num → real). «finePartition»(a, c, δ, n₁, p₁, t₁)",
								By(FinePartitionExists, ac, fine[0]))
							n2, p2, t2, right := h.Obtain3As[Nat, Fun[Nat, Real], Fun[Nat, Real]](
								"and so has ⟦d, b⟧",
								"∃n₂:num. ∃p₂ t₂:(num → real). «finePartition»(d, b, δ, n₂, p₂, t₂)",
								By(FinePartitionExists, db, fine[0]))
							n3, p3, t3, leftFirst := h.Obtain3As[Nat, Fun[Nat, Real], Fun[Nat, Real]](
								"the partition of ⟦a, c⟧ and the first of ⟦c, d⟧ join "+
									"into one of ⟦a, d⟧, whose sum is the sum of theirs",
								"∃n₃:num. ∃p₃ t₃:(num → real). "+
									"    «finePartition»(a, d, δ, n₃, p₃, t₃) ∧ "+
									"    «riemannSum»(f, n₃, p₃, t₃) = «riemannSum»(f, n₁, p₁, t₁) + «riemannSum»(f, n, p, t)",
								By(PartitionJoin.At(f, a, c, d, δ, n1, p1, t1, n, p, t), left, both))
							n4, p4, t4, first := h.Obtain3As[Nat, Fun[Nat, Real], Fun[Nat, Real]](
								"and that one and the partition of ⟦d, b⟧ into one of ⟦a, b⟧",
								"∃n₄:num. ∃p₄ t₄:(num → real). "+
									"    «finePartition»(a, b, δ, n₄, p₄, t₄) ∧ "+
									"    «riemannSum»(f, n₄, p₄, t₄) = «riemannSum»(f, n₃, p₃, t₃) + «riemannSum»(f, n₂, p₂, t₂)",
								By(PartitionJoin.At(f, a, d, b, δ, n3, p3, t3, n2, p2, t2), leftFirst, right))
							n5, p5, t5, leftSecond := h.Obtain3As[Nat, Fun[Nat, Real], Fun[Nat, Real]](
								"likewise the partition of ⟦a, c⟧ and the second of ⟦c, d⟧ join into one of ⟦a, d⟧",
								"∃n₅:num. ∃p₅ t₅:(num → real). "+
									"    «finePartition»(a, d, δ, n₅, p₅, t₅) ∧ "+
									"    «riemannSum»(f, n₅, p₅, t₅) = «riemannSum»(f, n₁, p₁, t₁) + «riemannSum»(f, m, q, s)",
								By(PartitionJoin.At(f, a, c, d, δ, n1, p1, t1, m, q, s), left, both))
							n6, p6, t6, second := h.Obtain3As[Nat, Fun[Nat, Real], Fun[Nat, Real]](
								"and that one and the partition of ⟦d, b⟧ into one of ⟦a, b⟧",
								"∃n₆:num. ∃p₆ t₆:(num → real). "+
									"    «finePartition»(a, b, δ, n₆, p₆, t₆) ∧ "+
									"    «riemannSum»(f, n₆, p₆, t₆) = «riemannSum»(f, n₅, p₅, t₅) + «riemannSum»(f, n₂, p₂, t₂)",
								By(PartitionJoin.At(f, a, d, b, δ, n5, p5, t5, n2, p2, t2), leftSecond, right))
							h.Show(
								"the two joined sums lie within ε, and they differ as the two sums over ⟦c, d⟧ do",
								ByArith(fine[1].At(n4, p4, t4, n6, p6, t6), leftFirst, first, leftSecond, second))
						}))
					g.Take(δ)
					g.Show(
						"so δ serves",
						By(fine[0], within))
				}))
			arg.Show(
				"so by the Cauchy criterion f has an integral over ⟦c, d⟧",
				By(near, cd, IntegrableCauchy))
		}),
})}

// IntegralAdditiveOrdered — for a ≤ b ≤ c, the integral over ⟦a, b⟧ and the
// integral over ⟦b, c⟧ add up to the integral over ⟦a, c⟧, once f has an
// integral on each part: the two integrals add up to one over ⟦a, c⟧
// (HasIntegralSplit), and each value is the integral it reads off.
var IntegralAdditiveOrdered = integralAdditiveOrderedThm{family.Add(registry.ProofEntry{
	Name: "IntegralAdditiveOrdered",
	Key:  "prop_207902616a9e51a5",
	Build: family.Theorem(Statement{
		Binders: "∀f:(real → real). ∀a b c I J:real.",
		Hypotheses: []string{
			"a ≤ b",
			"b ≤ c",
			"real_has_integral(f, a, b, I)",
			"real_has_integral(f, b, c, J)",
		},
		Conclusion: "real_integral(f, a, b) + real_integral(f, b, c) = real_integral(f, a, c)",
	},
		func(arg *Argument, f *Arrow[Real, Real], a, b, c, I, J *Expr[Real], ab, bc, toI, toJ Fact) {
			whole := arg.Have(
				"f has integral I + J over ⟦a, c⟧",
				"real_has_integral(f, a, c, I + J)",
				By(HasIntegralSplit.At(f, a, b, c, I, J), ab, bc, toI, toJ))
			arg.Show(
				"each oriented integral is the integral it reads off",
				ByArith(
					HasIntegralValue.At(f, a, b, I),
					HasIntegralValue.At(f, b, c, J),
					HasIntegralValue.At(f, a, c, arg.TermAs[Real]("I + J")),
					toI,
					toJ,
					whole))
		}),
})}

// IntegralReverse — reversing the bounds negates the oriented integral of a
// function with an integral. When b < a reverses an interval this is the
// definition; when a = b both integrals are over a point, where every
// integral is 0 (HasIntegralBound with the bound |f(a)|).
var IntegralReverse = integralReverseThm{family.Add(registry.ProofEntry{
	Name: "IntegralReverse",
	Key:  "prop_da9a9119697f9161",
	Build: family.Theorem(Statement{
		Binders: "∀f:(real → real). ∀a b I:real.",
		Hypotheses: []string{
			"real_has_integral(f, a, b, I)",
		},
		Conclusion: "real_integral(f, b, a) = -real_integral(f, a, b)",
	},
		func(arg *Argument, f *Arrow[Real, Real], a, b, I *Expr[Real], toI Fact) {
			ordered := arg.Have(
				"an interval over which f has an integral is ordered",
				"a ≤ b",
				By(HasIntegralOrdered.At(f, a, b, I), toI))
			value := arg.Have(
				"the integral over ⟦a, b⟧ is I",
				"real_integral(f, a, b) = I",
				By(HasIntegralValue, toI))
			arg.Cases(arg.Term("b ≤ a"))
			arg.When(
				"when b ≤ a the interval is one point, over which every integral is 0",
				func(c *Argument, flat Fact) {
					same := c.Have(
						"b is a",
						"b = a",
						ByArith(ordered, flat))
					bounded := c.Have(
						"on ⟦a, b⟧ the function is f(a)",
						"∀x:real. a ≤ x ∧ x ≤ b ⇒ |f(x)| ≤ |f(a)|",
						Derive(func(d *Argument) {
							d.FixAs[Real]()
							within := d.Assume()
							at := d.Have(
								"x is a",
								"x = a",
								ByArith(within, same))
							d.Show(
								"so |f(x)| is |f(a)|",
								at.Rw(),
								ByArith())
						}))
					small := c.Have(
						"so I is at most |f(a)|·(b − a) in size",
						"|I| ≤ |f(a)| * (b - a)",
						By(HasIntegralBound.At(f, a, b, I, c.TermAs[Real]("|f(a)|")), bounded, toI))
					zero := c.Have(
						"which is 0",
						"I = &0",
						same.Rw(),
						ByArith(small))
					c.Show(
						"both integrals are over ⟦a, a⟧, and are 0",
						same.Rw(),
						ByArith(value, zero))
				})
			arg.Otherwise(
				"when a < b the reversed integral is by definition the negative of the integral",
				func(c *Argument, wide Fact) {
					c.Show(
						"the definition reads the two bounds in either order",
						Unfold(RealIntegralDef),
						By(wide, ordered))
				})
		}),
})}

// IntegralAdditive — the oriented integral adds over any three points of an
// interval on which f is continuous: real_integral(f, a, b) +
// real_integral(f, b, c) = real_integral(f, a, c). f has an integral over
// every interval inside ⟦l, r⟧ (ContinuousIntegrable), so the integrals add
// over three ordered points (IntegralAdditiveOrdered) and change sign when
// the bounds are reversed (IntegralReverse); each of the six orders of a, b
// and c is one of these identities read off another.
var IntegralAdditive = integralAdditiveThm{family.Add(registry.ProofEntry{
	Name: "IntegralAdditive",
	Key:  "prop_f1d1e03b969f2bc1",
	Build: family.Theorem(Statement{
		Binders: "∀f:(real → real). ∀l r a b c:real.",
		Hypotheses: []string{
			"real_continuous_on(⟦l, r⟧, f)",
			"l ≤ a",
			"a ≤ r",
			"l ≤ b",
			"b ≤ r",
			"l ≤ c",
			"c ≤ r",
		},
		Conclusion: "real_integral(f, a, b) + real_integral(f, b, c) = real_integral(f, a, c)",
	},
		func(
			arg *Argument,
			f *Arrow[Real, Real],
			l, r, a, b, c *Expr[Real],
			continuous, la, ar, lb, br, lc, cr Fact,
		) {
			integrable := arg.Have(
				"f has an integral over every interval inside ⟦l, r⟧",
				"∀x y:real. l ≤ x ∧ x ≤ y ∧ y ≤ r ⇒ ∃I:real. real_has_integral(f, x, y, I)",
				Derive(func(d *Argument) {
					d.FixAs[Real]()
					d.FixAs[Real]()
					within := d.Assume()
					pointwise := d.Have(
						"each point of ⟦x, y⟧ lies in ⟦l, r⟧",
						"∀z:real. x ≤ z ∧ z ≤ y ⇒ l ≤ z ∧ z ≤ r",
						ByArith(within))
					inside := d.Have(
						"so ⟦x, y⟧ lies inside ⟦l, r⟧",
						"⟦x, y⟧ ⊆ ⟦l, r⟧",
						BySets(pointwise))
					d.Show(
						"f is continuous on ⟦x, y⟧, so has an integral there",
						By(ContinuousIntegrable, continuous, inside, within, real_continuous.ContinuousOnSubset))
				}))
			ordered := arg.Have(
				"over three ordered points of ⟦l, r⟧ the integrals add",
				Statement{
					Binders: "∀x y z:real.",
					Hypotheses: []string{
						"l ≤ x",
						"x ≤ y",
						"y ≤ z",
						"z ≤ r",
					},
					Conclusion: "real_integral(f, x, y) + real_integral(f, y, z) = real_integral(f, x, z)",
				},
				Derive(func(d *Argument) {
					x := d.FixAs[Real]()
					y := d.FixAs[Real]()
					z := d.FixAs[Real]()
					within := d.Assume()
					first := d.Have(
						"⟦x, y⟧ lies inside ⟦l, r⟧",
						"l ≤ x ∧ x ≤ y ∧ y ≤ r",
						ByArith(within))
					second := d.Have(
						"and so does ⟦y, z⟧",
						"l ≤ y ∧ y ≤ z ∧ z ≤ r",
						ByArith(within))
					I, toI := d.ObtainAs[Real](
						"f has an integral I over ⟦x, y⟧",
						"∃I:real. real_has_integral(f, x, y, I)",
						By(integrable.At(x, y), first))
					J, toJ := d.ObtainAs[Real](
						"and an integral J over ⟦y, z⟧",
						"∃J:real. real_has_integral(f, y, z, J)",
						By(integrable.At(y, z), second))
					d.Show(
						"so the integrals add",
						By(IntegralAdditiveOrdered.At(f, x, y, z, I, J), within, toI, toJ))
				}))
			reversed := arg.Have(
				"and reversing two points of ⟦l, r⟧ negates the integral",
				"∀x y:real. l ≤ x ∧ x ≤ y ∧ y ≤ r ⇒ real_integral(f, y, x) = -real_integral(f, x, y)",
				Derive(func(d *Argument) {
					x := d.FixAs[Real]()
					y := d.FixAs[Real]()
					within := d.Assume()
					I, toI := d.ObtainAs[Real](
						"f has an integral I over ⟦x, y⟧",
						"∃I:real. real_has_integral(f, x, y, I)",
						By(integrable.At(x, y), within))
					d.Show(
						"so reversing it negates the integral",
						By(IntegralReverse.At(f, x, y, I), toI))
				}))
			arg.Cases(arg.Term("a ≤ b"))
			arg.When(
				"when a ≤ b",
				func(d *Argument, ab Fact) {
					d.Cases(d.Term("b ≤ c"))
					d.When(
						"and b ≤ c, the points are in order",
						func(e *Argument, bc Fact) {
							e.Show(
								"the integrals over ⟦a, b⟧ and ⟦b, c⟧ add up to that over ⟦a, c⟧",
								ByArith(ordered.At(a, b, c), la, ab, bc, cr))
						})
					d.Otherwise(
						"and c < b",
						func(e *Argument, cb Fact) {
							e.Cases(e.Term("a ≤ c"))
							e.When(
								"with a ≤ c < b, the integral over ⟦a, b⟧ splits at c",
								func(g *Argument, ac Fact) {
									g.Show(
										"and the integral from b back to c is minus that from c to b",
										ByArith(ordered.At(a, c, b), reversed.At(c, b), la, ac, cb, br, lc))
								})
							e.Otherwise(
								"with c < a ≤ b, the integral over ⟦c, b⟧ splits at a",
								func(g *Argument, ca Fact) {
									g.Show(
										"and the integrals from b to c and from a to c are minus those from c",
										ByArith(ordered.At(c, a, b), reversed.At(c, b), reversed.At(c, a), lc, ca, ab, br, ar))
								})
						})
				})
			arg.Otherwise(
				"when b < a",
				func(d *Argument, ba Fact) {
					d.Cases(d.Term("a ≤ c"))
					d.When(
						"and a ≤ c, the integral over ⟦b, c⟧ splits at a",
						func(e *Argument, ac Fact) {
							e.Show(
								"and the integral from a to b is minus that from b to a",
								ByArith(ordered.At(b, a, c), reversed.At(b, a), lb, ba, ac, cr, ar))
						})
					d.Otherwise(
						"and c < a",
						func(e *Argument, ca Fact) {
							e.Cases(e.Term("b ≤ c"))
							e.When(
								"with b ≤ c < a, the integral over ⟦b, a⟧ splits at c",
								func(g *Argument, bc Fact) {
									g.Show(
										"and the integrals from a to b and from a to c are minus those to a",
										ByArith(ordered.At(b, c, a), reversed.At(b, a), reversed.At(c, a), lb, bc, ca, ar, cr))
								})
							e.Otherwise(
								"with c < b < a, the integral over ⟦c, a⟧ splits at b",
								func(g *Argument, cb Fact) {
									g.Show(
										"and every integral read downwards is minus the one read upwards",
										ByArith(
											ordered.At(c, b, a),
											reversed.At(b, a),
											reversed.At(c, b),
											reversed.At(c, a),
											lc,
											cb,
											ba,
											ar,
											br))
								})
						})
				})
		}),
})}

// NonnegIntegralZeroVanishes — a continuous function, nonnegative on ⟦a, b⟧
// with a < b, whose integral over ⟦a, b⟧ is 0 vanishes at every point of
// ⟦a, b⟧. Were f(x) positive, continuity at x would keep f above f(x)/2 on a
// stretch ⟦c, d⟧ of ⟦a, b⟧ of positive length around x. The integral over
// ⟦a, b⟧ is the sum of those over ⟦a, c⟧, ⟦c, d⟧ and ⟦d, b⟧; the outer two
// are nonnegative and the middle one is at least f(x)/2·(d − c) > 0, so the
// sum is not 0.
var NonnegIntegralZeroVanishes = nonnegIntegralZeroVanishesThm{family.Add(registry.ProofEntry{
	Name: "NonnegIntegralZeroVanishes",
	Key:  "prop_b8fbff4a4d723d71",
	Build: family.Theorem(Statement{
		Binders: "∀f:(real → real). ∀a b x:real.",
		Hypotheses: []string{
			"a < b",
			"real_continuous_on(⟦a, b⟧, f)",
			"∀t:real. a ≤ t ∧ t ≤ b ⇒ &0 ≤ f(t)",
			"real_integral(f, a, b) = &0",
			"a ≤ x",
			"x ≤ b",
		},
		Conclusion: "f(x) = &0",
	},
		func(
			arg *Argument,
			f *Arrow[Real, Real],
			a, b, x *Expr[Real],
			proper, continuous, nonneg, zero, ax, xb Fact,
		) {
			I, toI := arg.ObtainAs[Real](
				"f has an integral I over ⟦a, b⟧",
				"∃I:real. real_has_integral(f, a, b, I)",
				ByArith(proper, continuous, ContinuousIntegrable.At(f, a, b)))
			notZero := arg.SupposeNot()
			half := arg.Have(
				"then f(x) is positive, and so is half of it",
				"&0 < f(x) / &2",
				ByArith(notZero, nonneg.At(x), ax, xb))
			pointwise := arg.Unfolded(continuous, real_continuous.RealContinuousOnDef)
			_, near := arg.ObtainAs[Real](
				"by continuity at x, f is within f(x)/2 of f(x) at the points of ⟦a, b⟧ within some δ of x",
				"∃δ:real. &0 < δ ∧ ∀y:real. y ∈ ⟦a, b⟧ ∧ |y - x| < δ ⇒ |f(y) - f(x)| < f(x) / &2",
				By(pointwise.At(x, arg.TermAs[Real]("f(x) / &2")), ax, xb, half))
			radius := arg.Conjuncts(
				near,
				"δ is positive",
				"and f is within f(x)/2 of f(x) on those points")
			c, cDef := arg.LetAs[Real]("c", "max(a, x - δ / &2)")
			d, dDef := arg.LetAs[Real]("d", "min(b, x + δ / &2)")
			order := arg.Have(
				"the points a ≤ c ≤ d ≤ b lie in order",
				"a ≤ c ∧ c ≤ d ∧ d ≤ b",
				ByArith(cDef, dDef, proper, ax, xb, radius[0]))
			stretch := arg.Have(
				"⟦c, d⟧ has positive length and lies within δ of x",
				"c < d ∧ x - δ < c ∧ d < x + δ",
				ByArith(cDef, dDef, proper, ax, xb, radius[0]))
			above := arg.Have(
				"so on ⟦c, d⟧, f is at least f(x)/2",
				"∀y:real. c ≤ y ∧ y ≤ d ⇒ f(x) / &2 ≤ f(y)",
				arg.ForEach(func(y *Expr[Real]) Action {
					return ByArith(radius[1].At(y), order, stretch)
				}))
			J1, toJ1 := arg.ObtainAs[Real](
				"f has an integral J₁ over ⟦a, c⟧",
				"∃J₁:real. real_has_integral(f, a, c, J₁)",
				ByArith(toI, order, IntegrableSubinterval.At(f, a, b, a, c, I)))
			J2, toJ2 := arg.ObtainAs[Real](
				"an integral J₂ over ⟦c, d⟧",
				"∃J₂:real. real_has_integral(f, c, d, J₂)",
				ByArith(toI, order, IntegrableSubinterval.At(f, a, b, c, d, I)))
			J3, toJ3 := arg.ObtainAs[Real](
				"and an integral J₃ over ⟦d, b⟧",
				"∃J₃:real. real_has_integral(f, d, b, J₃)",
				ByArith(toI, order, IntegrableSubinterval.At(f, a, b, d, b, I)))
			total := arg.Have(
				"the three add up to the integral over ⟦a, b⟧, which is 0",
				"J₁ + J₂ + J₃ = &0",
				ByArith(
					zero,
					order,
					toI,
					toJ1,
					toJ2,
					toJ3,
					HasIntegralValue.At(f, a, b, I),
					HasIntegralSplit.At(f, a, c, d, J1, J2),
					HasIntegralSplit.At(f, a, d, b, arg.TermAs[Real]("J₁ + J₂"), J3),
					HasIntegralUnique.At(f, a, b, arg.TermAs[Real]("J₁ + J₂ + J₃"), I)))
			nothing := arg.TermAs[Fun[Real, Real]]("λt:real. &0")
			naught := arg.TermAs[Real]("&0")
			outerNonnegative := arg.Have(
				"f is nonnegative on ⟦a, c⟧ and on ⟦d, b⟧",
				"(∀t:real. a ≤ t ∧ t ≤ c ⇒ &0 ≤ f(t)) ∧ (∀t:real. d ≤ t ∧ t ≤ b ⇒ &0 ≤ f(t))",
				ByArith(nonneg, order))
			outer := arg.Have(
				"so J₁ and J₃ are nonnegative",
				"&0 ≤ J₁ ∧ &0 ≤ J₃",
				ByArith(
					outerNonnegative,
					order,
					toJ1,
					toJ3,
					HasIntegralConst.At(a, c, naught),
					HasIntegralConst.At(d, b, naught),
					HasIntegralLessEq.At(nothing, f, a, c, arg.TermAs[Real]("&0 * (c - a)"), J1),
					HasIntegralLessEq.At(nothing, f, d, b, arg.TermAs[Real]("&0 * (b - d)"), J3)))
			middle := arg.Have(
				"and J₂ is at least f(x)/2 times the length of ⟦c, d⟧",
				"f(x) / &2 * (d - c) ≤ J₂",
				ByArith(
					above,
					order,
					toJ2,
					HasIntegralConst.At(c, d, arg.TermAs[Real]("f(x) / &2")),
					HasIntegralLessEq.At(
						arg.TermAs[Fun[Real, Real]]("λt:real. f(x) / &2"),
						f,
						c,
						d,
						arg.TermAs[Real]("f(x) / &2 * (d - c)"),
						J2)))
			arg.Show(
				"which is positive, so the three cannot add up to 0",
				ByArith(total, outer, middle, half, stretch))
		}),
})}
