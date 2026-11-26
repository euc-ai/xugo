// integrability.go — which functions have an integral. A function with an
// integral is bounded; a function has an integral exactly when its Riemann
// sums over fine partitions are close to one another (the Cauchy
// criterion); and so continuous and monotone functions on a closed
// interval have integrals. A bounded function has one as soon as it has
// one on every closed interval inside, the end strips counting little in
// a Riemann sum, and so a bounded function continuous off finitely many
// points has one.

package real_integral

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/real/real_archimedean"
	"github.com/euc-ai/xugo/library/proofs/real/real_continuous"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sequences"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_algebra"
	"github.com/euc-ai/xugo/library/registry"
)

// IntegrableBounded — a function with an integral over ⟦a, b⟧ is bounded
// there. On a one-point interval |f(a)| bounds it. Otherwise take the mesh
// δ the integral gives at ε = 1 and a partition of ⟦a, b⟧ into n + 1 equal
// pieces of length h < δ, tagged at their left ends. A point x of ⟦a, b⟧
// lies in some piece k; tagging that piece at x instead is again a
// partition finer than δ, and moves the Riemann sum by (f(x) − f(p(k)))·h.
// Both sums lie within 1 of I, so |f(x) − f(p(k))| < 2/h, and |f(x)| is at
// most the sum of the |f(p(i))| plus 2/h.
var IntegrableBounded = integrableBoundedThm{family.Add(registry.ProofEntry{
	Name: "IntegrableBounded",
	Key:  "prop_eb6e05e9e6b3741e",
	Build: family.Theorem(Statement{
		Binders: "∀f:(real → real). ∀a b I:real.",
		Hypotheses: []string{
			"real_has_integral(f, a, b, I)",
		},
		Conclusion: "∃B:real. ∀x:real. a ≤ x ∧ x ≤ b ⇒ |f(x)| ≤ B",
	},
		func(arg *Argument, f *Arrow[Real, Real], a, b, I *Expr[Real], toI Fact) {
			integral := arg.Conjuncts(
				arg.Unfolded(toI, RealHasIntegralDef),
				"the interval is ordered",
				"for every ε some mesh brings the Riemann sums of f within ε of I")
			arg.Cases(arg.Term("a < b"))
			arg.Otherwise(
				"when a = b the interval is the point a, where |f(a)| bounds f",
				func(c *Argument, flat Fact) {
					c.Take(c.TermAs[Real]("|f(a)|"))
					c.FixAs[Real]()
					inside := c.Assume()
					point := c.Have(
						"x is a",
						"x = a",
						ByArith(flat, integral[0], inside))
					c.Show(
						"so |f(x)| is |f(a)|",
						point.Rw(),
						ByArith())
				})
			arg.When(
				"when a < b a partition into equal pieces controls f at every point",
				func(c *Argument, wide Fact) {
					_, mesh := c.ObtainAs[Real](
						"at ε = 1 the integral gives a mesh δ",
						"∃δ:real. "+
							"    &0 < δ ∧ "+
							"    (∀n:num. ∀p t:(num → real). "+
							"        «finePartition»(a, b, δ, n, p, t) ⇒ |«riemannSum»(f, n, p, t) - I| < &1)",
						By(integral[1].At(c.TermAs[Real]("&1"))))
					fine := c.Conjuncts(
						mesh,
						"δ is positive",
						"below δ every Riemann sum of f is within 1 of I")
					n, p, h, uniform := c.Obtain3As[Nat, Fun[Nat, Real], Real](
						"⟦a, b⟧ has a partition into n + 1 pieces of one length h < δ, tagged at their left ends",
						"∃n:num. ∃p:(num → real). ∃h:real. "+
							"    &0 < h ∧ «finePartition»(a, b, δ, n, p, p) ∧ (∀i:num. i ≤ n ⇒ p(i + 1) - p(i) = h)",
						By(UniformFinePartition, wide, fine[0]))
					parts := c.Conjuncts(
						uniform,
						"h is positive",
						"p starts at a",
						"and ends at b",
						"each piece is tagged in itself and shorter than δ",
						"each piece has length h")
					near := c.Have(
						"its Riemann sum is within 1 of I",
						"|«riemannSum»(f, n, p, p) - I| < &1",
						By(fine[1].At(n, p, p), parts[1], parts[2], parts[3]))
					sizes := c.Have(
						"the sizes |f(p(i))| are not negative",
						"∀i:num. i ∈ 0 .. n ⇒ &0 ≤ |f(p(i))|",
						ByArith())
					length := c.Have(
						"h is its own size",
						"|h| = h",
						ByArith(parts[0]))
					c.Take(c.TermAs[Real]("Σ_{i∈0 .. n} |f(p(i))| + &2 / h"))
					x := c.FixAs[Real]()
					inside := c.Assume()
					between := c.Have(
						"x lies between the first point a and the last point b",
						"p(0) ≤ x ∧ x ≤ p(n + 1)",
						ByArith(parts[1], parts[2], inside))
					k, piece := c.ObtainAs[Nat](
						"so x lies in some piece k",
						"∃k:num. k ≤ n ∧ p(k) ≤ x ∧ x ≤ p(k + 1)",
						By(PartitionPieceContains, between))
					where := c.Conjuncts(
						piece,
						"k is a piece",
						"x lies above its left end",
						"and below its right end")
					tags := c.Have(
						"tagging piece k at x instead tags every piece in itself",
						Statement{
							Binders: "∀i:num.",
							Hypotheses: []string{
								"i ≤ n",
							},
							Conclusion: "p(i) ≤ COND(i = k, x, p(i)) ∧ COND(i = k, x, p(i)) ≤ p(i + 1) ∧ p(i + 1) - p(i) < δ",
						},
						Derive(func(d *Argument) {
							i := d.FixAs[Nat]()
							within := d.Assume()
							d.Cases(d.Term("i = k"))
							d.When(
								"piece k is tagged at x, which it holds",
								func(e *Argument, at Fact) {
									e.Show(
										"and it is shorter than δ",
										ByArith(parts[3].At(i), within, where[1], where[2], at))
								})
							d.Otherwise(
								"every other piece keeps its tag",
								func(e *Argument, other Fact) {
									e.Show(
										"which it holds",
										ByArith(parts[3].At(i), within, other))
								})
						}))
					nearAgain := c.Have(
						"so the retagged Riemann sum is within 1 of I too",
						"|«riemannSum»(f, n, p, λi:num. COND(i = k, x, p(i))) - I| < &1",
						By(
							fine[1].At(n, p, c.TermAs[Fun[Nat, Real]]("λi:num. COND(i = k, x, p(i))")),
							parts[1],
							parts[2],
							tags))
					moved := c.Have(
						"the two sums differ by (f(x) − f(p(k)))·h, which is therefore less than 2 in size",
						"|(f(x) - f(p(k))) * h| < &2",
						ByArith(near, nearAgain, parts[4].At(k), where[0], RiemannSumRetag.At(f, n, p, p, k, x)))
					nearTag := c.Have(
						"so f(x) lies within 2/h of f(p(k))",
						"|f(x) - f(p(k))| < &2 / h",
						ByArith(moved, parts[0], length, real_sgn_abs.AbsMul.At(c.TermAs[Real]("f(x) - f(p(k))"), h)))
					term := c.Have(
						"and |f(p(k))| is one of the terms of the sum of the sizes",
						"|f(p(k))| ≤ Σ_{i∈0 .. n} |f(p(i))|",
						ByArith(
							where[0],
							sizes,
							num_segment.Finite.At(c.TermAs[Nat]("0"), n),
							real_sum.TermBound.At(
								c.TermAs[Set[Nat]]("0 .. n"),
								c.TermAs[Fun[Nat, Real]]("λi:num. |f(p(i))|"),
								c.TermAs[Real]("Σ_{i∈0 .. n} |f(p(i))|"),
								k)))
					c.Show(
						"so |f(x)| is at most the sum of the sizes plus 2/h",
						ByArith(nearTag, term))
				})
		}),
})}

// IntegrableCauchy — the Cauchy criterion: a function has an integral over
// ⟦a, b⟧ exactly when, for every ε, any two of its Riemann sums over
// partitions fine enough lie within ε of each other.
//
// Two sums near the integral are near each other. Conversely, choose for
// every k a mesh d(k) below which any two sums lie within 1/(k + 1); the
// first k meshes have a positive lower bound, so some partition is finer
// than d(0), …, d(k) at once, and its sum x(k) is chosen. For K ≤ m, n the
// sums x(m) and x(n) come from partitions finer than d(K), so they lie
// within 1/(K + 1): the x(k) are a Cauchy sequence, with a limit l. A
// partition finer than d(K) has its sum within 1/(K + 1) of x(K + J), and
// x(K + J) is as near l as we like for J large: l is the integral.
var IntegrableCauchy = integrableCauchyThm{family.Add(registry.ProofEntry{
	Name: "IntegrableCauchy",
	Key:  "prop_287084ad7833d105",
	Build: family.Theorem(Statement{
		Binders: "∀f:(real → real). ∀a b:real.",
		Conclusion: "(∃I:real. real_has_integral(f, a, b, I)) ⇔ " +
			"a ≤ b ∧ (∀ε:real. &0 < ε ⇒ ∃δ:real. &0 < δ ∧ «sumsWithin»(f, a, b, δ, ε))",
	},
		func(arg *Argument, f *Arrow[Real, Real], a, b *Expr[Real]) {
			arg.Iff()
			arg.Forward(
				"Riemann sums near the integral are near one another",
				func(c *Argument, has Fact) {
					_, toI := c.UnpackAs[Real](has)
					integral := c.Conjuncts(
						c.Unfolded(toI, RealHasIntegralDef),
						"the interval is ordered",
						"for every ε some mesh brings the Riemann sums of f within ε of I")
					within := c.Have(
						"for every ε some mesh brings any two Riemann sums within ε of each other",
						"∀ε:real. &0 < ε ⇒ ∃δ:real. &0 < δ ∧ «sumsWithin»(f, a, b, δ, ε)",
						Derive(func(d *Argument) {
							d.FixAs[Real]()
							pos := d.Assume()
							half := d.Have(
								"ε/2 is positive",
								"&0 < ε / &2",
								ByArith(pos))
							δ, mesh := d.ObtainAs[Real](
								"the integral gives a mesh δ at ε/2",
								"∃δ:real. "+
									"    &0 < δ ∧ "+
									"    (∀n:num. ∀p t:(num → real). "+
									"        «finePartition»(a, b, δ, n, p, t) ⇒ |«riemannSum»(f, n, p, t) - I| < ε / &2)",
								By(integral[1].At(d.TermAs[Real]("ε / &2")), half))
							fine := d.Conjuncts(
								mesh,
								"δ is positive",
								"below δ every Riemann sum of f is within ε/2 of I")
							pairs := d.Have(
								"two Riemann sums below δ, each within ε/2 of I, are within ε of each other",
								"«sumsWithin»(f, a, b, δ, ε)",
								Derive(func(e *Argument) {
									n := e.FixAs[Nat]()
									p := e.FixAs[Fun[Nat, Real]]()
									t := e.FixAs[Fun[Nat, Real]]()
									m := e.FixAs[Nat]()
									q := e.FixAs[Fun[Nat, Real]]()
									s := e.FixAs[Fun[Nat, Real]]()
									both := e.Assume()
									e.Show(
										"each lies within ε/2 of I",
										ByArith(fine[1].At(n, p, t), fine[1].At(m, q, s), both))
								}))
							d.Take(δ)
							d.Show(
								"so δ serves",
								By(fine[0], pairs))
						}))
					c.Show(
						"the interval is ordered, and the Riemann sums are close to one another",
						By(integral[0], within))
				})
			arg.Backward(
				"Riemann sums close to one another converge along partitions finer and finer",
				func(c *Argument, cauchy Fact) {
					given := c.Conjuncts(
						cauchy,
						"the interval is ordered",
						"for every ε some mesh brings any two Riemann sums within ε of each other")
					perK := c.Have(
						"for every k some mesh brings any two Riemann sums within 1/(k + 1) of each other",
						"∀k:num. ∃δ:real. &0 < δ ∧ «sumsWithin»(f, a, b, δ, &1 / (&k + &1))",
						Derive(func(d *Argument) {
							d.FixAs[Nat]()
							pos := d.Have(
								"1/(k + 1) is positive",
								"&0 < &1 / (&k + &1)",
								ByArith())
							d.Show(
								"the criterion at ε = 1/(k + 1)",
								By(given[1].At(d.TermAs[Real]("&1 / (&k + &1)")), pos))
						}))
					_, meshes := c.ObtainAs[Fun[Nat, Real]](
						"choose one such mesh d(k) for every k",
						"∃d:(num → real). ∀k:num. &0 < d(k) ∧ «sumsWithin»(f, a, b, d(k), &1 / (&k + &1))",
						Derive(func(d *Argument) {
							d.Take(
								d.TermAs[Fun[Nat, Real]]("λk:num. εδ:real. &0 < δ ∧ «sumsWithin»(f, a, b, δ, &1 / (&k + &1))"))
							d.Show(
								"the chosen mesh has the property some mesh has",
								By(Normalized, perK))
						}))
					lower := c.Have(
						"the meshes below any index have a positive lower bound",
						"∀k:num. ∃e:real. &0 < e ∧ (∀i:num. i < k ⇒ e ≤ d(i))",
						Derive(func(d *Argument) {
							d.Induct("k")
							d.Base(
								"below index 0 there is no mesh, and 1 is positive",
								func(g *Argument) {
									g.Take(g.TermAs[Real]("&1"))
									g.Show(
										"1 bounds no mesh at all",
										ByArith())
								})
							d.Step(
								"one index further the smaller of the bound and the next mesh serves",
								func(g *Argument, ih Fact) {
									k := g.TermAs[Nat]("k")
									_, bound := g.UnpackAs[Real](ih)
									parts := g.Conjuncts(
										bound,
										"e is positive",
										"e is at most each mesh below k")
									g.Take(g.TermAs[Real]("min(e, d(k))"))
									below := g.Have(
										"min(e, d(k)) is at most each mesh up to k",
										"∀i:num. i < suc(k) ⇒ min(e, d(k)) ≤ d(i)",
										Derive(func(h *Argument) {
											i := h.FixAs[Nat]()
											within := h.Assume()
											h.Cases(h.Term("i < k"))
											h.When(
												"below k, e is at most d(i)",
												func(j *Argument, earlier Fact) {
													j.Show(
														"and min(e, d(k)) is at most e",
														ByArith(parts[1].At(i), earlier))
												})
											h.Otherwise(
												"otherwise i is k itself",
												func(j *Argument, last Fact) {
													at := j.Have(
														"i is k",
														"i = k",
														ByArith(last, within))
													j.Show(
														"and min(e, d(k)) is at most d(k)",
														at.Rw(),
														ByArith())
												})
										}))
									g.Show(
										"min(e, d(k)) is positive, both being positive",
										ByArith(parts[0], meshes.At(k), below))
								})
						}))
					sums := c.Have(
						"for every k some partition is finer than d(0), …, d(k) at once",
						"∀k:num. ∃s:real. ∃n:num. ∃p t:(num → real). "+
							"    (∀i:num. i ≤ k ⇒ «finePartition»(a, b, d(i), n, p, t)) ∧ s = «riemannSum»(f, n, p, t)",
						Derive(func(d *Argument) {
							d.FixAs[Nat]()
							e, bound := d.UnpackAs[Real](lower.At(d.TermAs[Nat]("k + 1")))
							parts := d.Conjuncts(
								bound,
								"e is positive",
								"e is at most each mesh up to k")
							n, p, t, fine := d.Obtain3As[Nat, Fun[Nat, Real], Fun[Nat, Real]](
								"⟦a, b⟧ has a partition finer than e",
								"∃n:num. ∃p t:(num → real). «finePartition»(a, b, e, n, p, t)",
								By(FinePartitionExists, given[0], parts[0]))
							coarser := d.Have(
								"so it is finer than each of d(0), …, d(k)",
								"∀i:num. i ≤ k ⇒ «finePartition»(a, b, d(i), n, p, t)",
								Derive(func(g *Argument) {
									i := g.FixAs[Nat]()
									within := g.Assume()
									below := g.Have(
										"e is at most d(i)",
										"e ≤ d(i)",
										ByArith(parts[1].At(i), within))
									g.Show(
										"a partition finer than e is finer than d(i)",
										By(FinePartitionMono.At(a, b, e, g.TermAs[Real]("d(i)"), n, p, t), fine, below))
								}))
							d.Take(d.TermAs[Real]("«riemannSum»(f, n, p, t)"))
							d.Take(n)
							d.Take(p)
							d.Take(t)
							d.Show(
								"its Riemann sum is such a sum",
								By(Normalized, coarser))
						}))
					_, sampled := c.ObtainAs[Fun[Nat, Real]](
						"choose one such sum x(k) for every k",
						"∃x:(num → real). ∀k:num. ∃N:num. ∃P T:(num → real). "+
							"    (∀i:num. i ≤ k ⇒ «finePartition»(a, b, d(i), N, P, T)) ∧ x(k) = «riemannSum»(f, N, P, T)",
						Derive(func(d *Argument) {
							d.Take(d.TermAs[Fun[Nat, Real]](
								"λk:num. εs:real. ∃n:num. ∃p t:(num → real). " +
									"    (∀i:num. i ≤ k ⇒ «finePartition»(a, b, d(i), n, p, t)) ∧ s = «riemannSum»(f, n, p, t)"))
							d.Show(
								"the chosen sum has the property some sum has",
								By(Normalized, sums))
						}))
					reciprocal := c.Have(
						"by Archimedes some 1/(K + 1) is below any positive ε",
						"∀ε:real. &0 < ε ⇒ ∃K:num. &1 / (&K + &1) < ε",
						Derive(func(d *Argument) {
							ε := d.FixAs[Real]()
							pos := d.Assume()
							K, room := d.ObtainAs[Nat](
								"some K copies of ε exceed 1",
								"∃K:num. &1 < &K * ε",
								By(pos, real_archimedean.Archimedean.At(ε, d.TermAs[Real]("&1"))))
							d.Take(K)
							d.Show(
								"so 1/(K + 1) is below ε",
								ByArith(room, pos))
						}))
					cauchySums := c.Have(
						"the sums x(k) are eventually within any ε of one another",
						"∀ε:real. &0 < ε ⇒ ∃K:num. ∀j k:num. K ≤ j ∧ K ≤ k ⇒ |x(j) - x(k)| < ε",
						Derive(func(d *Argument) {
							ε := d.FixAs[Real]()
							pos := d.Assume()
							K, tolerance := d.ObtainAs[Nat](
								"some 1/(K + 1) is below ε",
								"∃K:num. &1 / (&K + &1) < ε",
								By(reciprocal.At(ε), pos))
							meshK := d.Conjuncts(
								meshes.At(K),
								"d(K) is positive",
								"below d(K) any two Riemann sums lie within 1/(K + 1)")
							d.Take(K)
							j := d.FixAs[Nat]()
							k := d.FixAs[Nat]()
							late := d.Conjuncts(
								d.Assume(),
								"K is at most j",
								"and at most k")
							N, P, T, atJ := d.Obtain3As[Nat, Fun[Nat, Real], Fun[Nat, Real]](
								"x(j) is the Riemann sum of a partition N, P, T finer than d(0), …, d(j)",
								"∃N:num. ∃P T:(num → real). "+
									"    (∀i:num. i ≤ j ⇒ «finePartition»(a, b, d(i), N, P, T)) ∧ x(j) = «riemannSum»(f, N, P, T)",
								By(sampled.At(j)))
							fromJ := d.Conjuncts(
								atJ,
								"N, P, T is finer than d(0), …, d(j)",
								"and is its Riemann sum")
							M, Q, S, atK := d.Obtain3As[Nat, Fun[Nat, Real], Fun[Nat, Real]](
								"and x(k) that of a partition M, Q, S finer than d(0), …, d(k)",
								"∃M:num. ∃Q S:(num → real). "+
									"    (∀i:num. i ≤ k ⇒ «finePartition»(a, b, d(i), M, Q, S)) ∧ x(k) = «riemannSum»(f, M, Q, S)",
								By(sampled.At(k)))
							fromK := d.Conjuncts(
								atK,
								"M, Q, S is finer than d(0), …, d(k)",
								"and is its Riemann sum")
							near := d.Have(
								"both partitions are finer than d(K), so their sums lie within 1/(K + 1)",
								"|«riemannSum»(f, N, P, T) - «riemannSum»(f, M, Q, S)| < &1 / (&K + &1)",
								By(meshK[1].At(N, P, T, M, Q, S), fromJ[0].At(K), fromK[0].At(K), late[0], late[1]))
							d.Show(
								"so x(j) and x(k) lie within ε of each other",
								ByArith(near, fromJ[1], fromK[1], tolerance))
						}))
					l, limit := c.ObtainAs[Real](
						"so they converge, to l say",
						"∃l:real. x ⟶ l",
						By(real_sequences.CauchyIffConvergent, real_sequences.RealCauchyDef, cauchySums))
					tail := c.Unfolded(limit, real_sequences.RealConvergesToDef)
					approach := c.Have(
						"for every ε some mesh brings every Riemann sum within ε of l",
						Statement{
							Binders: "∀ε:real.",
							Hypotheses: []string{
								"&0 < ε",
							},
							Conclusion: "∃δ:real. " +
								"    &0 < δ ∧ " +
								"    (∀n:num. ∀p t:(num → real). " +
								"        «finePartition»(a, b, δ, n, p, t) ⇒ |«riemannSum»(f, n, p, t) - l| < ε)",
						},
						Derive(func(d *Argument) {
							ε := d.FixAs[Real]()
							pos := d.Assume()
							K, tolerance := d.ObtainAs[Nat](
								"some 1/(K + 1) is below ε",
								"∃K:num. &1 / (&K + &1) < ε",
								By(reciprocal.At(ε), pos))
							gap := d.Have(
								"and ε − 1/(K + 1) is positive",
								"&0 < ε - &1 / (&K + &1)",
								ByArith(tolerance))
							J, late := d.ObtainAs[Nat](
								"from some index J on the sums x lie within ε − 1/(K + 1) of l",
								"∃J:num. ∀j:num. J ≤ j ⇒ |x(j) - l| < ε - &1 / (&K + &1)",
								By(tail.At(d.TermAs[Real]("ε - &1 / (&K + &1)")), gap))
							meshK := d.Conjuncts(
								meshes.At(K),
								"d(K) is positive",
								"below d(K) any two Riemann sums lie within 1/(K + 1)")
							d.Take(d.TermAs[Real]("d(K)"))
							fineSum := d.Have(
								"below d(K) every Riemann sum lies within ε of l",
								Statement{
									Binders: "∀n:num. ∀p t:(num → real).",
									Hypotheses: []string{
										"«finePartition»(a, b, d(K), n, p, t)",
									},
									Conclusion: "|«riemannSum»(f, n, p, t) - l| < ε",
								},
								Derive(func(g *Argument) {
									n := g.FixAs[Nat]()
									p := g.FixAs[Fun[Nat, Real]]()
									t := g.FixAs[Fun[Nat, Real]]()
									fine := g.Assume()
									M, Q, S, atKN := g.Obtain3As[Nat, Fun[Nat, Real], Fun[Nat, Real]](
										"x(K + J) is the Riemann sum of a partition M, Q, S finer than d(0), …, d(K + J)",
										"∃M:num. ∃Q S:(num → real). "+
											"    (∀i:num. i ≤ K + J ⇒ «finePartition»(a, b, d(i), M, Q, S)) ∧ "+
											"    x(K + J) = «riemannSum»(f, M, Q, S)",
										By(sampled.At(g.TermAs[Nat]("K + J"))))
									fromKN := g.Conjuncts(
										atKN,
										"that partition is finer than d(0), …, d(K + J)",
										"and is its Riemann sum")
									near := g.Have(
										"that partition is finer than d(K) too, so the two sums lie within 1/(K + 1)",
										"|«riemannSum»(f, n, p, t) - «riemannSum»(f, M, Q, S)| < &1 / (&K + &1)",
										By(meshK[1].At(n, p, t, M, Q, S), fine, fromKN[0].At(K), nat_order.LessEqAdd.At(K, J)))
									g.Show(
										"and x(K + J) lies within ε − 1/(K + 1) of l",
										ByArith(near, fromKN[1], late.At(g.TermAs[Nat]("K + J"))))
								}))
							d.Show(
								"so d(K) serves",
								By(meshK[0], fineSum))
						}))
					c.Take(l)
					c.Show(
						"the Riemann sums of f tend to l",
						Unfold(RealHasIntegralDef),
						By(given[0], approach))
				})
		}),
})}

// ContinuousIntegrable — a function continuous on a closed interval has an
// integral there. It is uniformly continuous on ⟦a, b⟧: one radius δ₀
// brings the values at any two points within η = ε/(b − a + 1). Where a
// piece of one partition finer than δ₀/2 meets a piece of another, their
// tags lie within δ₀, so the values of f at the tags lie within η, and the
// two Riemann sums within η·(b − a) < ε (PartitionSumsClose): the Cauchy
// criterion holds.
var ContinuousIntegrable = continuousIntegrableThm{family.Add(registry.ProofEntry{
	Name: "ContinuousIntegrable",
	Key:  "prop_9e4e90a42af4d7f",
	Build: family.Theorem(Statement{
		Binders: "∀f:(real → real). ∀a b:real.",
		Hypotheses: []string{
			"a ≤ b",
			"real_continuous_on(⟦a, b⟧, f)",
		},
		Conclusion: "∃I:real. real_has_integral(f, a, b, I)",
	},
		func(arg *Argument, f *Arrow[Real, Real], a, b *Expr[Real], ordered, continuous Fact) {
			uniform := arg.Unfolded(
				GroupPremises(
					ordered, continuous, real_continuous.ContinuousClosedIntervalUniformlyContinuous.At(f, a, b)),
				real_continuous.RealUniformlyContinuousOnDef)
			cauchy := arg.Have(
				"for every ε, any two Riemann sums over partitions fine enough lie within ε of each other",
				"∀ε:real. &0 < ε ⇒ ∃δ:real. &0 < δ ∧ «sumsWithin»(f, a, b, δ, ε)",
				Derive(func(c *Argument) {
					c.FixAs[Real]()
					pos := c.Assume()
					tolerance := c.Have(
						"the tolerance η = ε/(b − a + 1) is positive",
						"&0 < ε / (b - a + &1)",
						ByArith(pos, ordered))
					small := c.Have(
						"and η·(b − a) is below ε",
						"ε / (b - a + &1) * (b - a) < ε",
						ByArith(pos, ordered, tolerance))
					_, radius := c.ObtainAs[Real](
						"uniform continuity answers η with one radius δ₀",
						"∃δ₀:real. "+
							"    &0 < δ₀ ∧ "+
							"    (∀x y:real. x ∈ ⟦a, b⟧ ∧ y ∈ ⟦a, b⟧ ∧ |x - y| < δ₀ ⇒ |f(x) - f(y)| < ε / (b - a + &1))",
						By(uniform.At(c.TermAs[Real]("ε / (b - a + &1)")), tolerance))
					near := c.Conjuncts(
						radius,
						"δ₀ is positive",
						"points of ⟦a, b⟧ within δ₀ have values within η")
					δ := c.TermAs[Real]("δ₀ / &2")
					c.Take(δ)
					pairs := c.Have(
						"two partitions finer than δ₀/2 have Riemann sums within ε of each other",
						"«sumsWithin»(f, a, b, δ₀ / &2, ε)",
						Derive(func(d *Argument) {
							n := d.FixAs[Nat]()
							p := d.FixAs[Fun[Nat, Real]]()
							t := d.FixAs[Fun[Nat, Real]]()
							m := d.FixAs[Nat]()
							q := d.FixAs[Fun[Nat, Real]]()
							s := d.FixAs[Fun[Nat, Real]]()
							both := d.Conjuncts(
								d.Assume(),
								"p starts at a",
								"and ends at b",
								"each piece of p holds its tag and is shorter than δ₀/2",
								"q starts at a",
								"and ends at b",
								"each piece of q holds its tag and is shorter than δ₀/2")
							risingP := d.Have(
								"the points of p rise from a to b",
								"«partition»(a, b, n, p)",
								By(FinePartitionIsPartition.At(a, b, δ, n, p, t), both[0], both[1], both[2]))
							risingQ := d.Have(
								"and so do those of q",
								"«partition»(a, b, m, q)",
								By(FinePartitionIsPartition.At(a, b, δ, m, q, s), both[3], both[4], both[5]))
							valuesNear := d.Have(
								"where pieces meet, their tags lie within δ₀, so the values there lie within η",
								Statement{
									Binders: "∀k j:num.",
									Hypotheses: []string{
										"k ≤ n ∧ j ≤ m ∧ p(k) < q(j + 1) ∧ q(j) < p(k + 1)",
									},
									Conclusion: "|f(t(k)) - f(s(j))| ≤ ε / (b - a + &1)",
								},
								Derive(func(e *Argument) {
									k := e.FixAs[Nat]()
									j := e.FixAs[Nat]()
									meet := e.Assume()
									inP := e.Have(
										"the tag t(k) lies in ⟦a, b⟧",
										"a ≤ t(k) ∧ t(k) ≤ b",
										By(PartitionTagsInInterval, both[0], both[1], both[2], meet))
									inQ := e.Have(
										"and so does s(j)",
										"a ≤ s(j) ∧ s(j) ≤ b",
										By(PartitionTagsInInterval, both[3], both[4], both[5], meet))
									tk := e.TermAs[Real]("t(k)")
									sj := e.TermAs[Real]("s(j)")
									e.Show(
										"each tag lies within its piece, shorter than δ₀/2, and the pieces meet",
										ByArith(near[1].At(tk, sj), inP, inQ, both[2].At(k), both[5].At(j), meet))
								}))
							d.Show(
								"so the Riemann sums lie within η·(b − a) of each other, which is below ε",
								ByArith(
									valuesNear,
									small,
									risingP,
									risingQ,
									PartitionSumsClose.At(a, b, n, m, p, q,
										d.TermAs[Fun[Nat, Real]]("λk:num. f(t(k))"),
										d.TermAs[Fun[Nat, Real]]("λj:num. f(s(j))"),
										d.TermAs[Real]("ε / (b - a + &1)"))))
						}))
					c.Show(
						"so δ₀/2 serves",
						ByArith(pairs, near[0]))
				}))
			arg.Show(
				"by the Cauchy criterion f has an integral",
				By(IntegrableCauchy, ordered, cauchy))
		}),
})}

// ContinuousHasIntegral — a function continuous on ⟦a, b⟧ has its integral
// there: it has some integral I (ContinuousIntegrable), and the value
// real_integral(f, a, b) is that I (HasIntegralValue).
var ContinuousHasIntegral = continuousHasIntegralThm{family.Add(registry.ProofEntry{
	Name: "ContinuousHasIntegral",
	Key:  "prop_bbd4dad5b477584e",
	Build: family.Theorem(Statement{
		Binders: "∀f:(real → real). ∀a b:real.",
		Hypotheses: []string{
			"a ≤ b",
			"real_continuous_on(⟦a, b⟧, f)",
		},
		Conclusion: "real_has_integral(f, a, b, real_integral(f, a, b))",
	},
		func(arg *Argument, f *Arrow[Real, Real], a, b *Expr[Real], ordered, continuous Fact) {
			I, integral := arg.ObtainAs[Real](
				"f has some integral I over ⟦a, b⟧",
				"∃I:real. real_has_integral(f, a, b, I)",
				By(ordered, continuous, ContinuousIntegrable.At(f, a, b)))
			arg.Show(
				"and the value real_integral(f, a, b) is that I",
				By(Normalized, integral, HasIntegralValue.At(f, a, b, I)))
		}),
})}

// IncreasingSumBracket — for an increasing function the Riemann sum of a
// partition lies between the sums tagged at the left and at the right ends
// of the pieces, and these differ by at most δ·(f(b) − f(a)) when every
// piece is shorter than δ: on each piece the rise of f times the length is
// at most the rise times δ, and the rises add up to f(b) − f(a).
var IncreasingSumBracket = increasingSumBracketThm{family.Add(registry.ProofEntry{
	Name: "IncreasingSumBracket",
	Key:  "prop_14c76323a7d5484",
	Build: family.Theorem(Statement{
		Binders: "∀f:(real → real). ∀a b δ:real. ∀n:num. ∀p t:(num → real).",
		Hypotheses: []string{
			"real_increasing_on(⟦a, b⟧, f)",
			"«finePartition»(a, b, δ, n, p, t)",
		},
		Conclusion: "«riemannSum»(f, n, p, p) ≤ «riemannSum»(f, n, p, t) ∧ " +
			"«riemannSum»(f, n, p, t) ≤ «riemannSum»(f, n, p, λi:num. p(i + 1)) ∧ " +
			"«riemannSum»(f, n, p, λi:num. p(i + 1)) - «riemannSum»(f, n, p, p) ≤ δ * (f(b) - f(a))",
	},
		func(
			arg *Argument,
			f *Arrow[Real, Real],
			a, b, δ *Expr[Real],
			n *Expr[Nat],
			p, t *Arrow[Nat, Real],
			increasingOn, fine Fact,
		) {
			increasing := arg.Unfolded(increasingOn, real_continuous.RealIncreasingOnDef)
			parts := arg.Conjuncts(
				fine,
				"p starts at a",
				"and ends at b",
				"each piece holds its tag and is shorter than δ")
			rising := arg.Have(
				"the points rise from a to b",
				"«partition»(a, b, n, p)",
				By(FinePartitionIsPartition.At(a, b, δ, n, p, t), fine))
			termwise := arg.Have(
				"on each piece f rises from the left end through the tag to the right end",
				Statement{
					Binders: "∀k:num.",
					Hypotheses: []string{
						"k ≤ n",
					},
					Conclusion: "f(p(k)) * (p(k + 1) - p(k)) ≤ f(t(k)) * (p(k + 1) - p(k)) ∧ " +
						"f(t(k)) * (p(k + 1) - p(k)) ≤ f(p(k + 1)) * (p(k + 1) - p(k)) ∧ " +
						"f(p(k + 1)) * (p(k + 1) - p(k)) ≤ f(p(k)) * (p(k + 1) - p(k)) + (f(p(k + 1)) - f(p(k))) * δ",
				},
				Derive(func(c *Argument) {
					k := c.FixAs[Nat]()
					inside := c.Assume()
					values := c.Have(
						"piece k lies in ⟦a, b⟧, so f rises across it through its tag",
						"f(p(k)) ≤ f(t(k)) ∧ f(t(k)) ≤ f(p(k + 1))",
						ByArith(
							rising,
							inside,
							PartitionPiecesInInterval.At(a, b, n, p, k),
							parts[2].At(k),
							increasing.At(c.TermAs[Real]("p(k)"), c.TermAs[Real]("t(k)")),
							increasing.At(c.TermAs[Real]("t(k)"), c.TermAs[Real]("p(k + 1)"))))
					c.Show(
						"multiplying by the length of the piece, which is below δ",
						ByArith(
							values,
							parts[2].At(k),
							inside,
							real_order_ring.LessEqMulLeft.At(
								c.TermAs[Real]("f(p(k + 1)) - f(p(k))"),
								c.TermAs[Real]("p(k + 1) - p(k)"),
								δ)))
				}))
			lower := arg.Have(
				"the sum tagged at the left ends is at most the Riemann sum",
				"«riemannSum»(f, n, p, p) ≤ «riemannSum»(f, n, p, t)",
				By(termwise, real_sum.IntervalMonotone))
			upper := arg.Have(
				"which is at most the sum tagged at the right ends",
				"«riemannSum»(f, n, p, t) ≤ «riemannSum»(f, n, p, λi:num. p(i + 1))",
				By(termwise, real_sum.IntervalMonotone))
			gap := arg.Have(
				"which is at most the sum at the left ends plus δ times the rises of f",
				"«riemannSum»(f, n, p, λi:num. p(i + 1)) ≤ "+
					"Σ_{k∈0 .. n} (f(p(k)) * (p(k + 1) - p(k)) + (f(p(k + 1)) - f(p(k))) * δ)",
				By(termwise, real_sum.IntervalMonotone))
			arg.Show(
				"and the rises of f across the pieces add up to f(b) − f(a)",
				ByArith(
					lower,
					upper,
					gap,
					parts[0],
					parts[1],
					real_sum.IntervalAdd.At(
						arg.TermAs[Nat]("0"),
						n,
						arg.TermAs[Fun[Nat, Real]]("λk:num. f(p(k)) * (p(k + 1) - p(k))"),
						arg.TermAs[Fun[Nat, Real]]("λk:num. (f(p(k + 1)) - f(p(k))) * δ")),
					real_sum.ScalarRight.At(
						δ,
						arg.TermAs[Fun[Nat, Real]]("λk:num. f(p(k + 1)) - f(p(k))"),
						arg.TermAs[Set[Nat]]("0 .. n")),
					real_sum.TelescopeUp.At(
						arg.TermAs[Nat]("0"),
						n,
						arg.TermAs[Fun[Nat, Real]]("λk:num. f(p(k))"))))
		}),
})}

// IncreasingIntegrable — an increasing function has an integral over a
// closed interval. Take δ = ε/(2(f(b) − f(a)) + 1). For partitions P and Q
// finer than δ, the sum of P tagged at the left ends is at most that of Q
// tagged at the right ends, since where a piece of P meets a piece of Q
// its left end lies below the right end of the other (PartitionSumsCompare);
// so the Riemann sum of P exceeds that of Q by at most the two gaps between
// the sums tagged at the two ends, each at most δ·(f(b) − f(a))
// (IncreasingSumBracket), and so is below ε: the Cauchy criterion holds.
var IncreasingIntegrable = increasingIntegrableThm{family.Add(registry.ProofEntry{
	Name: "IncreasingIntegrable",
	Key:  "prop_1931b769d6e961e2",
	Build: family.Theorem(Statement{
		Binders: "∀f:(real → real). ∀a b:real.",
		Hypotheses: []string{
			"a ≤ b",
			"real_increasing_on(⟦a, b⟧, f)",
		},
		Conclusion: "∃I:real. real_has_integral(f, a, b, I)",
	},
		func(arg *Argument, f *Arrow[Real, Real], a, b *Expr[Real], ordered, increasingOn Fact) {
			increasing := arg.Unfolded(increasingOn, real_continuous.RealIncreasingOnDef)
			rise := arg.Have(
				"f rises from a to b",
				"f(a) ≤ f(b)",
				ByArith(increasing.At(a, b), ordered))
			leftBelowRight := arg.Have(
				"the sum of one partition of ⟦a, b⟧ tagged at its left "+
					"ends is at most the sum of another tagged at its right ends",
				Statement{
					Binders: "∀n m:num. ∀p q:(num → real).",
					Hypotheses: []string{
						"«partition»(a, b, n, p)",
						"«partition»(a, b, m, q)",
					},
					Conclusion: "«riemannSum»(f, n, p, p) ≤ «riemannSum»(f, m, q, λj:num. q(j + 1))",
				},
				Derive(func(c *Argument) {
					n := c.FixAs[Nat]()
					m := c.FixAs[Nat]()
					p := c.FixAs[Fun[Nat, Real]]()
					q := c.FixAs[Fun[Nat, Real]]()
					rising := c.Assume()
					meets := c.Have(
						"where piece k of p meets piece j of q, f at the left "+
							"end of the one is at most f at the right end of the other",
						"∀k j:num. k ≤ n ∧ j ≤ m ∧ p(k) < q(j + 1) ∧ q(j) < p(k + 1) ⇒ f(p(k)) ≤ f(q(j + 1))",
						Derive(func(e *Argument) {
							k := e.FixAs[Nat]()
							j := e.FixAs[Nat]()
							meet := e.Assume()
							e.Show(
								"both ends lie in ⟦a, b⟧ and the one is below the other",
								ByArith(
									rising,
									meet,
									PartitionPiecesInInterval.At(a, b, n, p, k),
									PartitionPiecesInInterval.At(a, b, m, q, j),
									increasing.At(e.TermAs[Real]("p(k)"), e.TermAs[Real]("q(j + 1)"))))
						}))
					c.Show(
						"so the two sums compare piece by piece where the pieces meet",
						By(
							PartitionSumsCompare.At(a, b, n, m, p, q,
								c.TermAs[Fun[Nat, Real]]("λk:num. f(p(k))"),
								c.TermAs[Fun[Nat, Real]]("λj:num. f(q(j + 1))")),
							rising,
							meets))
				}))
			cauchy := arg.Have(
				"for every ε, any two Riemann sums over partitions fine enough lie within ε of each other",
				"∀ε:real. &0 < ε ⇒ ∃δ:real. &0 < δ ∧ «sumsWithin»(f, a, b, δ, ε)",
				Derive(func(c *Argument) {
					c.FixAs[Real]()
					pos := c.Assume()
					mesh := c.Have(
						"the mesh δ = ε/(2(f(b) − f(a)) + 1) is positive",
						"&0 < ε / (&2 * (f(b) - f(a)) + &1)",
						ByArith(pos, rise))
					small := c.Have(
						"and twice δ·(f(b) − f(a)) is below ε",
						"&2 * (ε / (&2 * (f(b) - f(a)) + &1) * (f(b) - f(a))) < ε",
						ByArith(pos, rise, mesh))
					δ := c.TermAs[Real]("ε / (&2 * (f(b) - f(a)) + &1)")
					c.Take(δ)
					pairs := c.Have(
						"two partitions finer than δ have Riemann sums within ε of each other",
						"«sumsWithin»(f, a, b, ε / (&2 * (f(b) - f(a)) + &1), ε)",
						Derive(func(d *Argument) {
							n := d.FixAs[Nat]()
							p := d.FixAs[Fun[Nat, Real]]()
							t := d.FixAs[Fun[Nat, Real]]()
							m := d.FixAs[Nat]()
							q := d.FixAs[Fun[Nat, Real]]()
							s := d.FixAs[Fun[Nat, Real]]()
							both := d.Conjuncts(
								d.Assume(),
								"p starts at a",
								"and ends at b",
								"each piece of p holds its tag and is shorter than δ",
								"q starts at a",
								"and ends at b",
								"each piece of q holds its tag and is shorter than δ")
							risingP := d.Have(
								"the points of p rise from a to b",
								"«partition»(a, b, n, p)",
								By(FinePartitionIsPartition.At(a, b, δ, n, p, t), both[0], both[1], both[2]))
							risingQ := d.Have(
								"and so do those of q",
								"«partition»(a, b, m, q)",
								By(FinePartitionIsPartition.At(a, b, δ, m, q, s), both[3], both[4], both[5]))
							bracketP := GroupPremises(
								increasingOn,
								both[0],
								both[1],
								both[2],
								IncreasingSumBracket.At(f, a, b, δ, n, p, t))
							bracketQ := GroupPremises(
								increasingOn,
								both[3],
								both[4],
								both[5],
								IncreasingSumBracket.At(f, a, b, δ, m, q, s))
							d.Show(
								"each Riemann sum lies between its sums at the two "+
									"ends, which are within δ·(f(b) − f(a)) of each other",
								ByArith(
									leftBelowRight.At(n, m, p, q),
									leftBelowRight.At(m, n, q, p),
									risingP,
									risingQ,
									bracketP,
									bracketQ,
									small))
						}))
					c.Show(
						"so δ serves",
						By(mesh, pairs))
				}))
			arg.Show(
				"by the Cauchy criterion f has an integral",
				By(IntegrableCauchy, ordered, cauchy))
		}),
})}

// DecreasingIntegrable — a decreasing function has an integral over a
// closed interval: its negative is increasing, and has an integral I, so
// the function has the integral −I.
var DecreasingIntegrable = decreasingIntegrableThm{family.Add(registry.ProofEntry{
	Name: "DecreasingIntegrable",
	Key:  "prop_73757ec8ab207fe1",
	Build: family.Theorem(Statement{
		Binders: "∀f:(real → real). ∀a b:real.",
		Hypotheses: []string{
			"a ≤ b",
			"real_decreasing_on(⟦a, b⟧, f)",
		},
		Conclusion: "∃I:real. real_has_integral(f, a, b, I)",
	},
		func(arg *Argument, f *Arrow[Real, Real], a, b *Expr[Real], ordered, decreasingOn Fact) {
			decreasing := arg.Unfolded(decreasingOn, real_continuous.RealDecreasingOnDef)
			negated := arg.Have(
				"−f is increasing on ⟦a, b⟧",
				"real_increasing_on(⟦a, b⟧, λx:real. -f(x))",
				Unfold(real_continuous.RealIncreasingOnDef),
				Derive(func(c *Argument) {
					x := c.FixAs[Real]()
					y := c.FixAs[Real]()
					within := c.Assume()
					c.Show(
						"negating reverses the order",
						ByArith(decreasing.At(x, y), within))
				}))
			I, toI := arg.ObtainAs[Real](
				"so −f has an integral I",
				"∃I:real. real_has_integral(λx:real. -f(x), a, b, I)",
				By(IncreasingIntegrable.At(arg.TermAs[Fun[Real, Real]]("λx:real. -f(x)"), a, b), ordered, negated))
			back := arg.Simplified(
				GroupPremises(toI, HasIntegralNeg.At(arg.TermAs[Fun[Real, Real]]("λx:real. -f(x)"), a, b, I)),
				Fwd(real_ring.NegNeg))
			arg.Take(arg.TermAs[Real]("-I"))
			arg.Show(
				"f is the negative of −f, so it has integral −I",
				By(back))
		}),
})}

// IntegrableFromInterior — a function bounded on ⟦a, b⟧ with an integral
// over every closed interval inside ⟬a, b⟭ has one over ⟦a, b⟧: of f near
// the ends nothing is known but its bound, and the end strips count in a
// Riemann sum by at most their length times twice the bound.
//
// Given ε, take η with 32(B + 1)·η = ε. On an interval no longer than 2η
// two Riemann sums lie within 2B·(b − a) < ε of each other. Otherwise f
// has an integral J over ⟦c, d⟧ = ⟦a + η, b − η⟧; g, f frozen at f(c) left
// of c and at f(d) right of d, has an integral over ⟦a, b⟧, constant on
// the strips, and its Riemann sums meet the Cauchy criterion at ε/2 below
// some mesh δ₀. Below min(δ₀, η) the Riemann sums of f and of g differ
// only on the strips, by at most 2B·(2η + 2η)
// (RiemannSumsAgreeInside), so two sums of f lie within ε/2 + 16Bη < ε.
var IntegrableFromInterior = integrableFromInteriorThm{family.Add(registry.ProofEntry{
	Name: "IntegrableFromInterior",
	Key:  "prop_5263d5d8f2423443",
	Build: family.Theorem(Statement{
		Binders: "∀f:(real → real). ∀a b B:real.",
		Hypotheses: []string{
			"a ≤ b",
			"∀t:real. a ≤ t ∧ t ≤ b ⇒ |f(t)| ≤ B",
			"∀c d:real. a < c ∧ c ≤ d ∧ d < b ⇒ ∃I:real. real_has_integral(f, c, d, I)",
		},
		Conclusion: "∃I:real. real_has_integral(f, a, b, I)",
	},
		func(arg *Argument, f *Arrow[Real, Real], a, b, B *Expr[Real], ordered, bounded, inside Fact) {
			nonneg := arg.Have(
				"B is not negative, bounding |f(a)|",
				"&0 ≤ B",
				ByArith(bounded.At(a), ordered))
			cauchy := arg.Have(
				"for every ε, any two Riemann sums over partitions fine enough lie within ε of each other",
				"∀ε:real. &0 < ε ⇒ ∃δ:real. &0 < δ ∧ «sumsWithin»(f, a, b, δ, ε)",
				Derive(func(e *Argument) {
					e.FixAs[Real]()
					pos := e.Assume()
					η, scale := e.ObtainAs[Real](
						"take η with 32(B + 1)·η = ε: then 16Bη < ε/2, and B + 1 is positive even at B = 0",
						"∃η:real. &0 < η ∧ &32 * (B + &1) * η = ε",
						Derive(func(h *Argument) {
							h.Take(h.TermAs[Real]("ε / (&32 * (B + &1))"))
							h.Show(
								"32(B + 1) is positive",
								ByArith(pos, nonneg))
						}))
					sized := e.Conjuncts(
						scale,
						"η is positive",
						"and 32(B + 1)·η is ε")
					e.Cases(e.Term("b - a ≤ &2 * η"))
					e.When(
						"on an interval no longer than 2η, any two Riemann sums lie within 2B·(b − a) < ε",
						func(h *Argument, short Fact) {
							h.Take(η)
							within := h.Have(
								"two Riemann sums differ by at most twice the bound times b − a",
								"«sumsWithin»(f, a, b, η, ε)",
								Derive(func(i *Argument) {
									n := i.FixAs[Nat]()
									p := i.FixAs[Fun[Nat, Real]]()
									t := i.FixAs[Fun[Nat, Real]]()
									m := i.FixAs[Nat]()
									q := i.FixAs[Fun[Nat, Real]]()
									s := i.FixAs[Fun[Nat, Real]]()
									both := i.Conjuncts(
										i.Assume(),
										"p starts at a",
										"and ends at b",
										"each piece of p holds its tag and is shorter than η",
										"q starts at a",
										"and ends at b",
										"each piece of q holds its tag and is shorter than η")
									risingP := i.Have(
										"the points of p rise from a to b",
										"«partition»(a, b, n, p)",
										By(FinePartitionIsPartition.At(a, b, η, n, p, t), both[0], both[1], both[2]))
									risingQ := i.Have(
										"and so do those of q",
										"«partition»(a, b, m, q)",
										By(FinePartitionIsPartition.At(a, b, η, m, q, s), both[3], both[4], both[5]))
									valuesNear := i.Have(
										"the tags lie in ⟦a, b⟧, where the values of f lie within 2B of each other",
										"∀k j:num. k ≤ n ∧ j ≤ m ∧ p(k) < q(j + 1) ∧ q(j) < p(k + 1) ⇒ |f(t(k)) - f(s(j))| ≤ &2 * B",
										Derive(func(o *Argument) {
											o.FixAs[Nat]()
											o.FixAs[Nat]()
											meet := o.Assume()
											inP := o.Have(
												"the tag t(k) lies in ⟦a, b⟧",
												"a ≤ t(k) ∧ t(k) ≤ b",
												By(PartitionTagsInInterval, both[0], both[1], both[2], meet))
											inQ := o.Have(
												"and so does s(j)",
												"a ≤ s(j) ∧ s(j) ≤ b",
												By(PartitionTagsInInterval, both[3], both[4], both[5], meet))
											o.Show(
												"B bounds |f| at both",
												ByArith(bounded.At(o.TermAs[Real]("t(k)")), bounded.At(o.TermAs[Real]("s(j)")), inP, inQ))
										}))
									close := i.Have(
										"so the two sums lie within 2B·(b − a) of each other",
										"|«riemannSum»(f, n, p, t) - «riemannSum»(f, m, q, s)| ≤ &2 * B * (b - a)",
										By(
											valuesNear,
											risingP,
											risingQ,
											PartitionSumsClose.At(a, b, n, m, p, q,
												i.TermAs[Fun[Nat, Real]]("λk:num. f(t(k))"),
												i.TermAs[Fun[Nat, Real]]("λj:num. f(s(j))"),
												i.TermAs[Real]("&2 * B"))))
									i.Show(
										"and 2B·(b − a) is at most 4Bη, below ε",
										ByArith(
											close,
											sized[0],
											sized[1],
											nonneg,
											real_order_ring.LessEqMulLeft.At(B, i.TermAs[Real]("b - a"), i.TermAs[Real]("&2 * η")),
											short))
								}))
							h.Show(
								"so η serves",
								By(sized[0], within))
						})
					e.Otherwise(
						"on a longer interval, f has an integral J over the middle ⟦a + η, b − η⟧",
						func(h *Argument, long Fact) {
							c, cDef := h.LetAs[Real]("c", "a + η")
							d, dDef := h.LetAs[Real]("d", "b - η")
							strictly := h.Have(
								"⟦c, d⟧ lies strictly inside ⟦a, b⟧",
								"a < c ∧ c ≤ d ∧ d < b",
								ByArith(cDef, dDef, sized[0], long))
							order := h.Have(
								"so a, c, d, b come in order",
								"a ≤ c ∧ c ≤ d ∧ a ≤ d ∧ d ≤ b",
								ByArith(strictly))
							J, onMiddleF := h.ObtainAs[Real](
								"f has an integral J over ⟦c, d⟧",
								"∃J:real. real_has_integral(f, c, d, J)",
								By(inside.At(c, d), strictly))
							// g is f frozen at f(c) left of c and at f(d) right of d.
							g, gDef := h.LetAs[Fun[Real, Real]]("g", "λx:real. f(max(c, min(d, x)))")
							agreeMiddle := h.Have(
								"on ⟦c, d⟧, g is f",
								"∀x:real. c ≤ x ∧ x ≤ d ⇒ f(x) = g(x)",
								Derive(func(i *Argument) {
									i.FixAs[Real]()
									within := i.Assume()
									clamp := i.Have(
										"x is its own clamp",
										"max(c, min(d, x)) = x",
										ByArith(within))
									i.Show(
										"so the values agree",
										gDef.Rw(),
										By(Normalized, clamp))
								}))
							agreeLeft := h.Have(
								"left of c it is f(c)",
								"∀x:real. a ≤ x ∧ x ≤ c ⇒ f(c) = g(x)",
								Derive(func(i *Argument) {
									i.FixAs[Real]()
									within := i.Assume()
									clamp := i.Have(
										"x clamps to c",
										"max(c, min(d, x)) = c",
										ByArith(within, order))
									i.Show(
										"so the values agree",
										gDef.Rw(),
										By(Normalized, clamp))
								}))
							agreeRight := h.Have(
								"right of d it is f(d)",
								"∀x:real. d ≤ x ∧ x ≤ b ⇒ f(d) = g(x)",
								Derive(func(i *Argument) {
									i.FixAs[Real]()
									within := i.Assume()
									clamp := i.Have(
										"x clamps to d",
										"max(c, min(d, x)) = d",
										ByArith(within, order))
									i.Show(
										"so the values agree",
										gDef.Rw(),
										By(Normalized, clamp))
								}))
							onLeft := h.Have(
								"so g has integral f(c)·(c − a) over ⟦a, c⟧, where it is constant",
								"real_has_integral(g, a, c, f(c) * (c - a))",
								By(
									agreeLeft,
									order,
									HasIntegralConst.At(a, c, f.Apply(c)),
									HasIntegralCongruence.At(h.TermAs[Fun[Real, Real]]("λx:real. f(c)"), g, a, c,
										h.TermAs[Real]("f(c) * (c - a)"))))
							onMiddle := h.Have(
								"integral J over ⟦c, d⟧, where it is f",
								"real_has_integral(g, c, d, J)",
								By(onMiddleF, agreeMiddle, HasIntegralCongruence.At(f, g, c, d, J)))
							onRight := h.Have(
								"and integral f(d)·(b − d) over ⟦d, b⟧",
								"real_has_integral(g, d, b, f(d) * (b - d))",
								By(
									agreeRight,
									order,
									HasIntegralConst.At(d, b, f.Apply(d)),
									HasIntegralCongruence.At(h.TermAs[Fun[Real, Real]]("λx:real. f(d)"), g, d, b,
										h.TermAs[Real]("f(d) * (b - d)"))))
							integrable := h.Have(
								"so g has an integral over ⟦a, b⟧",
								"∃K:real. real_has_integral(g, a, b, K)",
								Derive(func(i *Argument) {
									i.Take(i.TermAs[Real]("f(c) * (c - a) + J + f(d) * (b - d)"))
									i.Show(
										"the three integrals add over ⟦a, c⟧, ⟦c, d⟧ and ⟦d, b⟧",
										By(
											onLeft,
											onMiddle,
											onRight,
											order,
											HasIntegralSplit.At(g, a, c, d, i.TermAs[Real]("f(c) * (c - a)"), J),
											HasIntegralSplit.At(g, a, d, b, i.TermAs[Real]("f(c) * (c - a) + J"),
												i.TermAs[Real]("f(d) * (b - d)"))))
								}))
							half := h.Have(
								"ε/2 is positive",
								"&0 < ε / &2",
								ByArith(pos))
							δ0, mesh := h.ObtainAs[Real](
								"by the Cauchy criterion, below some mesh δ₀ two Riemann sums of g lie within ε/2",
								"∃δ₀:real. &0 < δ₀ ∧ «sumsWithin»(g, a, b, δ₀, ε / &2)",
								By(integrable, half, IntegrableCauchy))
							coarse := h.Conjuncts(
								mesh,
								"δ₀ is positive",
								"below δ₀ two sums of g lie within ε/2")
							δ := h.TermAs[Real]("min(δ₀, η)")
							h.Take(δ)
							below := h.Have(
								"min(δ₀, η) is positive, and at most δ₀ and η",
								"&0 < min(δ₀, η) ∧ min(δ₀, η) ≤ δ₀ ∧ min(δ₀, η) ≤ η",
								ByArith(coarse[0], sized[0]))
							bounds := h.Conjuncts(
								below,
								"min(δ₀, η) is positive",
								"it is at most δ₀",
								"and at most η")
							apart := h.Have(
								"f and g differ by at most 2B on ⟦a, b⟧",
								"∀x:real. a ≤ x ∧ x ≤ b ⇒ |f(x) - g(x)| ≤ &2 * B",
								Derive(func(i *Argument) {
									x := i.FixAs[Real]()
									within := i.Assume()
									i.Show(
										"B bounds |f| at x and at its clamp, both in ⟦a, b⟧",
										gDef.Rw(),
										ByArith(within, order, bounded.At(x), bounded.At(i.TermAs[Real]("max(c, min(d, x))"))))
								}))
							strips := h.Have(
								"each end strip is η long, so the strips cost at most 2B·(2η + 2η)",
								"&2 * B * ((c - a) + (b - d) + &2 * min(δ₀, η)) ≤ &8 * B * η",
								ByArith(
									Scaled(B, cDef),
									Scaled(B, dDef),
									nonneg,
									bounds[2],
									real_order_ring.LessEqMulLeft.At(B, δ, η)))
							within := h.Have(
								"two Riemann sums of f below min(δ₀, η) lie within ε of each other",
								"«sumsWithin»(f, a, b, min(δ₀, η), ε)",
								Derive(func(i *Argument) {
									n := i.FixAs[Nat]()
									p := i.FixAs[Fun[Nat, Real]]()
									t := i.FixAs[Fun[Nat, Real]]()
									m := i.FixAs[Nat]()
									q := i.FixAs[Fun[Nat, Real]]()
									s := i.FixAs[Fun[Nat, Real]]()
									fine := i.Assume()
									gNear := i.Have(
										"the two sums of g lie within ε/2",
										"|«riemannSum»(g, n, p, t) - «riemannSum»(g, m, q, s)| < ε / &2",
										By(
											fine,
											bounds[1],
											FinePartitionMono.At(a, b, δ, δ0, n, p, t),
											FinePartitionMono.At(a, b, δ, δ0, m, q, s),
											coarse[1].At(n, p, t, m, q, s)))
									onP := i.Have(
										"on p, f and g differ only on the strips",
										"|«riemannSum»(f, n, p, t) - «riemannSum»(g, n, p, t)| ≤ "+
											"&2 * B * ((c - a) + (b - d) + &2 * min(δ₀, η))",
										By(
											apart,
											agreeMiddle,
											order,
											fine,
											RiemannSumsAgreeInside.At(f, g, a, b, c, d, i.TermAs[Real]("&2 * B"), δ, n, p, t)))
									onQ := i.Have(
										"and so on q",
										"|«riemannSum»(f, m, q, s) - «riemannSum»(g, m, q, s)| ≤ "+
											"&2 * B * ((c - a) + (b - d) + &2 * min(δ₀, η))",
										By(
											apart,
											agreeMiddle,
											order,
											fine,
											RiemannSumsAgreeInside.At(f, g, a, b, c, d, i.TermAs[Real]("&2 * B"), δ, m, q, s)))
									i.Show(
										"so the two sums of f lie within ε/2 + 16Bη of each other, below ε",
										ByArith(gNear, onP, onQ, strips, sized[0], sized[1]))
								}))
							h.Show(
								"so min(δ₀, η) serves",
								By(bounds[0], within))
						})
				}))
			arg.Show(
				"by the Cauchy criterion f has an integral",
				By(IntegrableCauchy, ordered, cauchy))
		}),
})}

// IntegrableOffFinite — a function bounded on ⟦a, b⟧ and continuous there
// off finitely many points has an integral over ⟦a, b⟧.
//
// By induction on the exceptional set, for every interval at once. With
// no exceptional point f is continuous on the interval. With one more,
// c: on an interval whose interior misses c, every closed interval inside
// it misses c, so f is continuous there off the rest and has an integral
// by the induction hypothesis — and IntegrableFromInterior carries that to
// the whole interval; an interval with c inside is split at c into two
// such intervals.
var IntegrableOffFinite = integrableOffFiniteThm{family.Add(registry.ProofEntry{
	Name: "IntegrableOffFinite",
	Key:  "prop_ee77f7abfde8ccdc",
	Build: family.Theorem(Statement{
		Binders: "∀f:(real → real). ∀a b B:real. ∀k:set(real).",
		Hypotheses: []string{
			"a ≤ b",
			"finite(k)",
			"∀t:real. a ≤ t ∧ t ≤ b ⇒ |f(t)| ≤ B",
			"real_continuous_on(⟦a, b⟧ ∖ k, f)",
		},
		Conclusion: "∃I:real. real_has_integral(f, a, b, I)",
	},
		func(
			arg *Argument,
			f *Arrow[Real, Real],
			a, b, B *Expr[Real],
			k *Expr[Set[Real]],
			ordered, finite, bounded, continuous Fact,
		) {
			// The property the induction carries: on every interval where f
			// is bounded by B and continuous off s, f has an integral.
			integrableOff := arg.TermAs[Set[Set[Real]]](
				"λs:set(real). ∀u v:real. " +
					"    u ≤ v ∧ (∀t:real. u ≤ t ∧ t ≤ v ⇒ |f(t)| ≤ B) ∧ real_continuous_on(⟦u, v⟧ ∖ s, f) ⇒ " +
					"    ∃I:real. real_has_integral(f, u, v, I)")
			arg.Show(
				"the induction carries the property to k, which is finite",
				ByInduction(finite_set.FiniteInduct.At(integrableOff, k), finite, ordered, bounded, continuous,
					Case(
						"with no exceptional point f is continuous on the interval",
						Derive(func(h *Argument) {
							h.FixAs[Real]("u")
							h.FixAs[Real]("v")
							given := h.Conjuncts(
								h.Assume(),
								"u ≤ v",
								"B bounds |f| on ⟦u, v⟧",
								"f is continuous on ⟦u, v⟧ ∖ ∅")
							whole := h.Simplified(given[2], Fwd(set_algebra.DiffEmpty))
							h.Show(
								"so it has an integral",
								By(given[0], whole, ContinuousIntegrable))
						})),
					Case(
						"one more exceptional point c: integrate from inside up to c, splitting at c when it is inside",
						Derive(func(h *Argument) {
							c := h.FixAs[Real]("c")
							h.FixAs[Set[Real]]("s")
							carried := h.Assume()
							u := h.FixAs[Real]("u")
							v := h.FixAs[Real]("v")
							given := h.Conjuncts(
								h.Assume(),
								"u ≤ v",
								"B bounds |f| on ⟦u, v⟧",
								"f is continuous on ⟦u, v⟧ off insert(c, s)")
							missesC := h.Have(
								"on an interval ⟦x, y⟧ in ⟦u, v⟧ whose interior misses c, f has an integral",
								"∀x y:real. u ≤ x ∧ x ≤ y ∧ y ≤ v ∧ (c ≤ x ∨ y ≤ c) ⇒ ∃I:real. real_has_integral(f, x, y, I)",
								Derive(func(i *Argument) {
									x := i.FixAs[Real]()
									y := i.FixAs[Real]()
									within := i.Assume()
									boundedXY := i.Have(
										"B bounds |f| on ⟦x, y⟧",
										"∀t:real. x ≤ t ∧ t ≤ y ⇒ |f(t)| ≤ B",
										i.ForEach(func(t *Expr[Real]) Action {
											return ByArith(within, given[1].At(t))
										}))
									interior := i.Have(
										"on every closed interval ⟦p, q⟧ inside ⟬x, y⟭, which "+
											"misses c, the induction hypothesis gives an integral",
										"∀p q:real. x < p ∧ p ≤ q ∧ q < y ⇒ ∃I:real. real_has_integral(f, p, q, I)",
										Derive(func(o *Argument) {
											p := o.FixAs[Real]()
											q := o.FixAs[Real]()
											inside := o.Assume()
											pointwise := o.Have(
												"each point of ⟦p, q⟧ lies in ⟦u, v⟧ and is not c",
												"∀z:real. p ≤ z ∧ z ≤ q ⇒ u ≤ z ∧ z ≤ v ∧ z ≠ c",
												ByArith(within, inside))
											misses := o.Have(
												"so ⟦p, q⟧ off s lies in ⟦u, v⟧ off insert(c, s)",
												"⟦p, q⟧ ∖ s ⊆ ⟦u, v⟧ ∖ insert(c, s)",
												BySets(pointwise))
											boundedPQ := o.Have(
												"B bounds |f| on ⟦p, q⟧",
												"∀t:real. p ≤ t ∧ t ≤ q ⇒ |f(t)| ≤ B",
												o.ForEach(func(t *Expr[Real]) Action {
													return ByArith(within, inside, given[1].At(t))
												}))
											continuousPQ := o.Have(
												"f is continuous on ⟦p, q⟧ off s",
												"real_continuous_on(⟦p, q⟧ ∖ s, f)",
												By(given[2], misses, real_continuous.ContinuousOnSubset))
											o.Show(
												"the induction hypothesis at ⟦p, q⟧",
												By(carried.At(p, q), inside, boundedPQ, continuousPQ))
										}))
									i.Show(
										"so f has an integral over ⟦x, y⟧",
										By(IntegrableFromInterior.At(f, x, y, B), within, boundedXY, interior))
								}))
							h.Cases(h.Term("u < c ∧ c < v"))
							h.When(
								"c lies inside ⟬u, v⟭: split ⟦u, v⟧ at c",
								func(i *Argument, inside Fact) {
									order := i.Have(
										"u ≤ c ≤ v, the ends of ⟦u, c⟧ and of ⟦c, v⟧ each at most itself",
										"u ≤ u ∧ u ≤ c ∧ c ≤ c ∧ c ≤ v ∧ v ≤ v",
										ByArith(inside))
									// Normalized reads c ≤ c as true, which settles the guard
									// c ≤ x ∨ y ≤ c of missesC on either half.
									I1, left := i.ObtainAs[Real](
										"f has an integral I₁ over ⟦u, c⟧, c being its right end",
										"∃I₁:real. real_has_integral(f, u, c, I₁)",
										By(Normalized, missesC.At(u, c), order))
									I2, right := i.ObtainAs[Real](
										"and an integral I₂ over ⟦c, v⟧, c being its left end",
										"∃I₂:real. real_has_integral(f, c, v, I₂)",
										By(Normalized, missesC.At(c, v), order))
									i.Take(i.TermAs[Real]("I₁ + I₂"))
									i.Show(
										"the two integrals add over ⟦u, v⟧",
										By(left, right, order, HasIntegralSplit.At(f, u, c, v, I1, I2)))
								})
							h.Otherwise(
								"c lies outside ⟬u, v⟭, so the interior of ⟦u, v⟧ misses it",
								func(i *Argument, outside Fact) {
									beside := i.Have(
										"c is at most u or at least v, and the ends of ⟦u, v⟧ are each at most itself",
										"(c ≤ u ∨ v ≤ c) ∧ u ≤ u ∧ v ≤ v",
										ByArith(outside))
									i.Show(
										"so f has an integral over ⟦u, v⟧",
										By(missesC.At(u, v), given[0], beside))
								})
						}))))
		}),
})}
