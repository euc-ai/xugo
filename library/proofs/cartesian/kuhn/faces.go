// faces.go — a face of a Kuhn simplex and the simplices through it: each
// is the face with one point added, its apex; the apex over the face of a
// chain opposite one of its vertices is that vertex or one other point,
// read off the chain; a vertex replaced by a grid point comparable with
// the rest gives a simplex; and so a face on the boundary of the cube lies
// in one simplex and any other face in two.

package kuhn

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/cartesian/carrier"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_algebra"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// KuhnCofaceApex — a Kuhn simplex through the face of s opposite a is the
// face with one point added that the face does not hold, and every such
// simplex is one.
var KuhnCofaceApex = kuhnCofaceApexThm{family.Add(registry.ProofEntry{
	Name: "KuhnCofaceApex",
	Key:  "prop_51e1640d7eae2f0b",
	Build: family.Theorem(
		"∀p n:num. ∀s:set(num → num). ∀a:(num → num). ∀u:set(num → num). "+
			"    u ∈ «cofaces» ⇔ "+
			"    (∃b:(num → num). "+
			"        b ∉ delete(s, a) ∧ "+
			"        kuhn_simplex(p, n, insert(b, delete(s, a))) ∧ "+
			"        u = insert(b, delete(s, a)))",
		func(
			arg *Argument,
			p, n *Expr[Nat],
			s *Expr[Set[Fun[Nat, Nat]]],
			a *Expr[Fun[Nat, Nat]],
			u *Expr[Set[Fun[Nat, Nat]]],
		) {
			arg.Iff()
			arg.Forward(
				"a simplex through the face is the face with the removed point put back",
				func(c *Argument, through Fact) {
					parts := c.Conjuncts(
						through,
						"u is a Kuhn simplex",
						"removing a point of u leaves the face")
					apex, removed := c.UnpackAs[Fun[Nat, Nat]](parts[1], "b")
					c.Show(
						"u is the face with b inserted, and b is not on the face",
						By(removed, parts[0], set_algebra.InsertDelete.At(u, apex), set_basic.InDelete))
				})
			arg.Backward(
				"the face with a new point added holds the face opposite that point",
				func(c *Argument, added Fact) {
					apex, given := c.UnpackAs[Fun[Nat, Nat]](added, "b")
					parts := c.Conjuncts(
						given,
						"b is not on the face",
						"the face with b is a Kuhn simplex",
						"u is the face with b")
					face := c.TermAs[Set[Fun[Nat, Nat]]]("delete(s, a)")
					removal := c.Have(
						"b lies in the face with b, and removing it leaves the face",
						"b ∈ insert(b, delete(s, a)) ∧ delete(insert(b, delete(s, a)), b) = delete(s, a)",
						By(
							parts[0],
							set_algebra.DeleteInsert.At(face, apex, apex),
							set_algebra.DeleteNonElement.At(face, apex),
							set_basic.InInsert))
					c.Show(
						"u is a simplex through the face",
						By(parts[2], removal, parts[1]))
				})
		}),
})}

// KuhnSingleCoface — a face whose only apex is the vertex it was cut from
// lies in one Kuhn simplex: a simplex through the face is the face with its
// apex put back (KuhnCofaceApex), and with the apex a that is s.
var KuhnSingleCoface = kuhnSingleCofaceThm{family.Add(registry.ProofEntry{
	Name: "KuhnSingleCoface",
	Key:  "prop_1b4281a42cd5ab40",
	Build: family.Theorem(Statement{
		Binders: "∀p n:num. ∀s:set(num → num). ∀a:(num → num).",
		Hypotheses: []string{
			"kuhn_simplex(p, n, s)",
			"a ∈ s",
			"∀b:(num → num). b ∉ delete(s, a) ∧ kuhn_simplex(p, n, insert(b, delete(s, a))) ⇒ b = a",
		},
		Conclusion: "card(«cofaces») = 1",
	}, func(
		arg *Argument,
		p, n *Expr[Nat],
		s *Expr[Set[Fun[Nat, Nat]]],
		a *Expr[Fun[Nat, Nat]],
		h Fact,
	) {
		given := arg.Conjuncts(
			h,
			"s is a Kuhn simplex",
			"a is a vertex of s",
			"every apex of the face is a")
		pointwise := arg.Have(
			"a Kuhn simplex lies through the face exactly when it is s",
			"∀u:set(num → num). u ∈ «cofaces» ⇔ u ∈ {s}",
			Derive(func(c *Argument) {
				u := c.FixAs[Set[Fun[Nat, Nat]]]("u")
				c.Iff()
				c.Forward(
					"a simplex through the face is the face with its apex put back, and the apex is a",
					func(d *Argument, through Fact) {
						apex, putBack := d.UnpackAs[Fun[Nat, Nat]](
							d.Simplified(through, Fwd(KuhnCofaceApex)),
							"b")
						d.Show(
							"u is the face with a put back, which is s",
							By(
								putBack,
								given[2].At(apex),
								given[1],
								set_algebra.InsertDelete.At(s, a),
								set_basic.InSing.At(u, s)))
					})
				c.Backward(
					"s lies through the face, a being the point removed",
					func(d *Argument, listed Fact) {
						d.Show(
							"s is a Kuhn simplex holding the face",
							By(listed, given[1], given[0], set_basic.InSing))
					})
			}))
		single := arg.Have(
			"the simplices through the face are s alone",
			"«cofaces» = {s}",
			By(
				pointwise,
				set_basic.Extension.At(
					arg.TermAs[Set[Set[Fun[Nat, Nat]]]]("«cofaces»"),
					arg.TermAs[Set[Set[Fun[Nat, Nat]]]]("{s}"))))
		arg.Do(single.Rw())
		arg.Show(
			"one set",
			Cite(cardinality.CardSing))
	}),
})}

// KuhnApexOppositeLeast — through the face of a chain opposite its least
// vertex there are at most two Kuhn simplices: the chain itself, and the
// chain one step further on, whose greatest point is the greatest vertex
// raised once more in the coordinate the chain raises first.
var KuhnApexOppositeLeast = kuhnApexOppositeLeastThm{family.Add(registry.ProofEntry{
	Name: "KuhnApexOppositeLeast",
	Key:  "prop_ca76007aaac07765",
	Build: family.Theorem(Statement{
		Binders: "∀p n:num. ∀v τ:(num → num). ∀s:set(num → num). ∀b:(num → num).",
		Hypotheses: []string{
			"0 < n",
			"∀i:num. i < n ⇒ τ(i) < n",
			"injective_on({i:num | i < n}, τ)",
			"s = {«vertex»(v, τ, j) | j:num | j ≤ n}",
			"kuhn_simplex(p, n, «withApex»)",
		},
		Conclusion: "b = «vertex»(v, τ, 0) ∨ b = «lifted»(v, τ)",
		Abbrev: Abbrev{
			{Name: "withApex", Text: "insert(b, delete(s, «vertex»(v, τ, 0)))"},
		},
	},
		func(
			a *Argument,
			p, n *Expr[Nat],
			v, τ *Expr[Fun[Nat, Nat]],
			s *Expr[Set[Fun[Nat, Nat]]],
			b *Expr[Fun[Nat, Nat]],
			h Fact,
		) {
			given := a.Conjuncts(
				h,
				"n is positive",
				"τ gives each coordinate below n a step below n",
				"τ is one-to-one below n",
				"s is the chain",
				"the face with b is a Kuhn simplex")
			pos, steps, oneToOne, chain, simplex := given[0], given[1], given[2], given[3], given[4]
			zero := a.TermAs[Nat]("0")
			one := a.TermAs[Nat]("1")
			k, first := a.ObtainAs[Nat](
				"some coordinate k is raised at the first step",
				"∃k:num. k < n ∧ τ(k) = 0",
				By(
					steps,
					pos,
					oneToOne,
					functions.InjectiveOnDef,
					num_segment.BelowStrictInjectiveOnto.At(n, τ, zero)))
			c, d, extremes := a.Unpack2As[Fun[Nat, Nat], Fun[Nat, Nat]](
				GroupPremises(simplex, KuhnSimplexExtrema.At(p, n, a.TermAs[Set[Fun[Nat, Nat]]]("«withApex»"))),
				"c",
				"d")
			ext := a.Conjuncts(
				extremes,
				"c is a point of the face with b",
				"d is a point of the face with b",
				"every point of the face with b lies between c and d",
				"d is c raised in every coordinate below n")
			cIn, dIn, between, raisedAll := ext[0], ext[1], ext[2], ext[3]
			levels := a.Have(
				"1 and n are vertices other than vertex 0",
				"1 ≤ n ∧ ¬(1 = 0) ∧ n ≤ n ∧ ¬(n = 0) ∧ 0 ≤ n",
				ByArith(pos))
			second := a.TermAs[Fun[Nat, Nat]]("«vertex»(v, τ, 1)")
			greatest := a.TermAs[Fun[Nat, Nat]]("«vertex»(v, τ, n)")
			onFace := a.Have(
				"vertices 1 and n lie on the face",
				"«vertex»(v, τ, 1) ∈ delete(s, «vertex»(v, τ, 0)) ∧ "+
					"«vertex»(v, τ, n) ∈ delete(s, «vertex»(v, τ, 0))",
				By(
					steps,
					chain,
					oneToOne,
					levels,
					At(KuhnChainFaceVertices, n, v, τ, s, one, zero),
					At(KuhnChainFaceVertices, n, v, τ, s, n, zero)))
			bounds := a.Conjuncts(
				a.Have(
					"c lies below vertex 1 and vertex n below d",
					"kuhn_le(n, c, «vertex»(v, τ, 1)) ∧ kuhn_le(n, «vertex»(v, τ, n), d)",
					By(onFace, between.At(second), between.At(greatest), set_basic.InInsert)),
				"c lies below vertex 1",
				"vertex n lies below d")
			aboveLeast := a.Have(
				"c lies above vertex 0, since d = c + 1 lies above v + 1",
				"kuhn_le(n, «vertex»(v, τ, 0), c)",
				Derive(func(e *Argument) {
					belowSecond := e.Unfolded(bounds[0], KuhnLeDef)
					aboveGreatest := e.Unfolded(bounds[1], KuhnLeDef)
					e.Do(Unfold(KuhnLeDef))
					i := e.FixAs[Nat]("i")
					e.Show(
						"coordinate by coordinate",
						ByArith(steps.At(i), raisedAll.At(i), belowSecond.At(i), aboveGreatest.At(i)))
				}))
			a.Cases(a.Term("c = «vertex»(v, τ, 0)"))
			a.When(
				"the least point of the face with b is vertex 0, off the face, so it is b",
				func(e *Argument, cLeast Fact) {
					e.Show(
						"b is vertex 0",
						By(cLeast, cIn, set_basic.InInsert, set_basic.InDelete))
				})
			a.Otherwise(
				"the least point is vertex 1, and the greatest point d is then the other apex",
				func(e *Argument, notLeast Fact) {
					cSecond := e.Have(
						"c lies between consecutive vertices 0 and 1, so it is vertex 1",
						"c = «vertex»(v, τ, 1)",
						By(notLeast, oneToOne, bounds[0], aboveLeast, At(KuhnChainSqueeze, n, v, τ, zero, one, c)))
					cd := e.Have(
						"c lies below d",
						"kuhn_le(n, c, d)",
						By(dIn, between.At(d)))
					dApex := e.Have(
						"d is vertex n raised once more in the first coordinate",
						"d = «lifted»(v, τ)",
						Derive(func(f *Argument) {
							cdAt := f.Unfolded(cd, KuhnLeDef)
							f.Do(Funext())
							i := f.FixAs[Nat]("i")
							cAt := f.Have(
								"c(i) is vertex 1 at i",
								"c(i) = «vertex»(v, τ, 1, i)",
								By(Normalized, cSecond))
							f.Cases(f.Term("i < n"))
							f.When(
								"below n, d(i) = c(i) + 1",
								func(g *Argument, below Fact) {
									g.Cases(g.Term("τ(i) = 0"))
									g.When(
										"i is raised at the first step",
										func(u *Argument, firstStep Fact) {
											u.Show(
												"both read v(i) + 2",
												ByArith(below, cAt, firstStep, steps.At(i), raisedAll.At(i)))
										})
									g.Otherwise(
										"i is raised later",
										func(u *Argument, laterStep Fact) {
											u.Show(
												"both read v(i) + 1",
												ByArith(laterStep, below, cAt, steps.At(i), raisedAll.At(i)))
										})
								})
							f.Otherwise(
								"from n on, d(i) = c(i) = v(i)",
								func(g *Argument, beyond Fact) {
									g.Show(
										"both read v(i)",
										ByArith(beyond, cAt, cdAt.At(i)))
								})
						}))
					offVertices := e.Have(
						"at the first coordinate d exceeds every vertex",
						"∀j:num. ¬(d(k) = «vertex»(v, τ, j, k))",
						Derive(func(f *Argument) {
							dAt := f.Have(
								"d(k) is v(k) + 2",
								"d(k) = «lifted»(v, τ, k)",
								By(Normalized, dApex))
							f.FixAs[Nat]("j")
							f.Show(
								"a vertex is at most v(k) + 1 there",
								ByArith(dAt, first, steps.At(k)))
						}))
					offChain := e.Have(
						"so d is no point of s",
						"¬(d ∈ s)",
						Derive(func(f *Argument) {
							f.Do(chain.Rw())
							f.Show(
								"no vertex is d",
								By(offVertices))
						}))
					dIsB := e.Have(
						"d lies in the face with b but off the face, so it is b",
						"d = b",
						By(offChain, dIn, set_basic.InInsert, set_basic.InDelete))
					e.Show(
						"b is the other apex",
						By(dIsB, dApex))
				})
		}),
})}

// KuhnApexOppositeGreatest — through the face of a chain opposite its
// greatest vertex there are at most two Kuhn simplices: the chain itself,
// and the chain one step back, whose least point is v lowered in the
// coordinate the chain raises last.
var KuhnApexOppositeGreatest = kuhnApexOppositeGreatestThm{family.Add(registry.ProofEntry{
	Name: "KuhnApexOppositeGreatest",
	Key:  "prop_537257a667429a3b",
	Build: family.Theorem(Statement{
		Binders: "∀p n:num. ∀v τ:(num → num). ∀s:set(num → num). ∀b:(num → num).",
		Hypotheses: []string{
			"0 < n",
			"∀i:num. i < n ⇒ τ(i) < n",
			"injective_on({i:num | i < n}, τ)",
			"s = {«vertex»(v, τ, j) | j:num | j ≤ n}",
			"kuhn_simplex(p, n, «withApex»)",
		},
		Conclusion: "b = «vertex»(v, τ, n) ∨ b = «lowered»(v, τ)",
		Abbrev: Abbrev{
			{Name: "withApex", Text: "insert(b, delete(s, «vertex»(v, τ, n)))"},
		},
	},
		func(
			a *Argument,
			p, n *Expr[Nat],
			v, τ *Expr[Fun[Nat, Nat]],
			s *Expr[Set[Fun[Nat, Nat]]],
			b *Expr[Fun[Nat, Nat]],
			h Fact,
		) {
			given := a.Conjuncts(
				h,
				"n is positive",
				"τ gives each coordinate below n a step below n",
				"τ is one-to-one below n",
				"s is the chain",
				"the face with b is a Kuhn simplex")
			pos, steps, oneToOne, chain, simplex := given[0], given[1], given[2], given[3], given[4]
			zero := a.TermAs[Nat]("0")
			previous := a.TermAs[Nat]("n - 1")
			levels := a.Have(
				"0 and n - 1 are vertices other than vertex n, vertex "+
					"n follows vertex n - 1, and n - 1 is the last step",
				"0 ≤ n ∧ ¬(0 = n) ∧ n - 1 ≤ n ∧ ¬(n - 1 = n) ∧ n ≤ n ∧ n - 1 < n ∧ n = n - 1 + 1",
				ByArith(pos))
			k, last := a.ObtainAs[Nat](
				"some coordinate k is raised at the last step",
				"∃k:num. k < n ∧ τ(k) = n - 1",
				By(
					steps,
					levels,
					oneToOne,
					functions.InjectiveOnDef,
					num_segment.BelowStrictInjectiveOnto.At(n, τ, previous)))
			c, d, extremes := a.Unpack2As[Fun[Nat, Nat], Fun[Nat, Nat]](
				GroupPremises(simplex, KuhnSimplexExtrema.At(p, n, a.TermAs[Set[Fun[Nat, Nat]]]("«withApex»"))),
				"c",
				"d")
			ext := a.Conjuncts(
				extremes,
				"c is a point of the face with b",
				"d is a point of the face with b",
				"every point of the face with b lies between c and d",
				"d is c raised in every coordinate below n")
			cIn, dIn, between, raisedAll := ext[0], ext[1], ext[2], ext[3]
			least := a.TermAs[Fun[Nat, Nat]]("«vertex»(v, τ, 0)")
			beforeLast := a.TermAs[Fun[Nat, Nat]]("«vertex»(v, τ, n - 1)")
			onFace := a.Have(
				"vertices 0 and n - 1 lie on the face",
				"«vertex»(v, τ, 0) ∈ delete(s, «vertex»(v, τ, n)) ∧ "+
					"«vertex»(v, τ, n - 1) ∈ delete(s, «vertex»(v, τ, n))",
				By(
					steps,
					chain,
					oneToOne,
					levels,
					At(KuhnChainFaceVertices, n, v, τ, s, zero, n),
					At(KuhnChainFaceVertices, n, v, τ, s, previous, n)))
			bounds := a.Conjuncts(
				a.Have(
					"c lies below vertex 0 and vertex n - 1 below d",
					"kuhn_le(n, c, «vertex»(v, τ, 0)) ∧ kuhn_le(n, «vertex»(v, τ, n - 1), d)",
					By(onFace, between.At(least), between.At(beforeLast), set_basic.InInsert)),
				"c lies below vertex 0",
				"vertex n - 1 lies below d")
			belowGreatest := a.Have(
				"d lies below vertex n, since c lies below v",
				"kuhn_le(n, d, «vertex»(v, τ, n))",
				Derive(func(e *Argument) {
					belowLeast := e.Unfolded(bounds[0], KuhnLeDef)
					aboveBefore := e.Unfolded(bounds[1], KuhnLeDef)
					e.Do(Unfold(KuhnLeDef))
					i := e.FixAs[Nat]("i")
					e.Show(
						"coordinate by coordinate",
						ByArith(steps.At(i), raisedAll.At(i), belowLeast.At(i), aboveBefore.At(i)))
				}))
			a.Cases(a.Term("d = «vertex»(v, τ, n)"))
			a.When(
				"the greatest point of the face with b is vertex n, off the face, so it is b",
				func(e *Argument, dGreatest Fact) {
					e.Show(
						"b is vertex n",
						By(dGreatest, dIn, set_basic.InInsert, set_basic.InDelete))
				})
			a.Otherwise(
				"the greatest point is vertex n - 1, and the least point c is then the other apex",
				func(e *Argument, notGreatest Fact) {
					dBefore := e.Have(
						"d lies between consecutive vertices n - 1 and n, so it is vertex n - 1",
						"d = «vertex»(v, τ, n - 1)",
						By(
							notGreatest,
							levels,
							oneToOne,
							bounds[1],
							belowGreatest,
							At(KuhnChainSqueeze, n, v, τ, previous, n, d)))
					cd := e.Have(
						"c lies below d",
						"kuhn_le(n, c, d)",
						By(cIn, between.At(c)))
					cApex := e.Have(
						"c is v lowered in the last coordinate",
						"c = «lowered»(v, τ)",
						Derive(func(f *Argument) {
							cdAt := f.Unfolded(cd, KuhnLeDef)
							f.Do(Funext())
							i := f.FixAs[Nat]("i")
							dAt := f.Have(
								"d(i) is vertex n - 1 at i",
								"d(i) = «vertex»(v, τ, n - 1, i)",
								By(Normalized, dBefore))
							f.Cases(f.Term("i < n"))
							f.When(
								"below n, c(i) + 1 = d(i)",
								func(g *Argument, below Fact) {
									g.Cases(g.Term("τ(i) = n - 1"))
									g.When(
										"i is raised at the last step",
										func(u *Argument, lastStep Fact) {
											u.Show(
												"both read v(i) - 1",
												ByArith(below, dAt, lastStep, steps.At(i), raisedAll.At(i)))
										})
									g.Otherwise(
										"i is raised earlier",
										func(u *Argument, earlierStep Fact) {
											u.Show(
												"both read v(i)",
												ByArith(earlierStep, below, dAt, steps.At(i), raisedAll.At(i)))
										})
								})
							f.Otherwise(
								"from n on, c(i) = d(i) = v(i)",
								func(g *Argument, beyond Fact) {
									g.Show(
										"both read v(i)",
										ByArith(beyond, dAt, cdAt.At(i)))
								})
						}))
					dAtK := e.Have(
						"d(k) is vertex n - 1 at k",
						"d(k) = «vertex»(v, τ, n - 1, k)",
						By(Normalized, dBefore))
					lowered := e.Have(
						"c(k) + 1 = v(k)",
						"c(k) + 1 = v(k)",
						ByArith(last, raisedAll.At(k), dAtK))
					offVertices := e.Have(
						"at the last coordinate c lies below every vertex",
						"∀j:num. ¬(c(k) = «vertex»(v, τ, j, k))",
						Derive(func(f *Argument) {
							f.FixAs[Nat]("j")
							f.Show(
								"a vertex is at least v(k) there",
								ByArith(lowered))
						}))
					offChain := e.Have(
						"so c is no point of s",
						"¬(c ∈ s)",
						Derive(func(f *Argument) {
							f.Do(chain.Rw())
							f.Show(
								"no vertex is c",
								By(offVertices))
						}))
					cIsB := e.Have(
						"c lies in the face with b but off the face, so it is b",
						"c = b",
						By(offChain, cIn, set_basic.InInsert, set_basic.InDelete))
					e.Show(
						"b is the other apex",
						By(cIsB, cApex))
				})
		}),
})}

// KuhnApexOppositeInner — through the face of a chain opposite an inner
// vertex there are at most two Kuhn simplices: the chain itself, and the
// chain with the steps on either side of that vertex exchanged. Every
// simplex through the face is a chain from vertex 0 to vertex n, so its
// apex lies above the vertices before m and below those after, by
// induction along the chain, and between vertices m - 1 and m + 1 only
// the two raises of steps m - 1 and m are free.
var KuhnApexOppositeInner = kuhnApexOppositeInnerThm{family.Add(registry.ProofEntry{
	Name: "KuhnApexOppositeInner",
	Key:  "prop_85fa090bc8804a08",
	Build: family.Theorem(Statement{
		Binders: "∀p n:num. ∀v τ:(num → num). ∀s:set(num → num). ∀m:num. ∀b:(num → num).",
		Hypotheses: []string{
			"0 < m",
			"m < n",
			"∀i:num. i < n ⇒ τ(i) < n",
			"injective_on({i:num | i < n}, τ)",
			"s = {«vertex»(v, τ, j) | j:num | j ≤ n}",
			"b ∉ delete(s, «vertex»(v, τ, m))",
			"kuhn_simplex(p, n, «withApex»)",
		},
		Conclusion: "b = «vertex»(v, τ, m) ∨ b = «swapped»(v, τ, m)",
		Abbrev: Abbrev{
			{Name: "withApex", Text: "insert(b, delete(s, «vertex»(v, τ, m)))"},
		},
	},
		func(
			a *Argument,
			p, n *Expr[Nat],
			v, τ *Expr[Fun[Nat, Nat]],
			s *Expr[Set[Fun[Nat, Nat]]],
			m *Expr[Nat],
			b *Expr[Fun[Nat, Nat]],
			h Fact,
		) {
			given := a.Conjuncts(
				h,
				"m is positive",
				"m is below n",
				"τ gives each coordinate below n a step below n",
				"τ is one-to-one below n",
				"s is the chain",
				"b is not on the face",
				"the face with b is a Kuhn simplex")
			pos, below, steps, oneToOne, chain, apexOff, simplex :=
				given[0], given[1], given[2], given[3], given[4], given[5], given[6]
			zero := a.TermAs[Nat]("0")
			before := a.TermAs[Nat]("m - 1")
			after := a.TermAs[Nat]("m + 1")
			neighbours := a.Have(
				"0, n, m - 1 and m + 1 are vertices other than vertex "+
					"m, and vertices m - 1, m and m + 1 are consecutive",
				"0 ≤ n ∧ "+
					"¬(0 = m) ∧ "+
					"n ≤ n ∧ "+
					"¬(n = m) ∧ "+
					"m ≤ n ∧ "+
					"m - 1 < m ∧ "+
					"m - 1 ≤ n ∧ "+
					"¬(m - 1 = m) ∧ "+
					"m + 1 ≤ n ∧ "+
					"¬(m + 1 = m) ∧ "+
					"m = m - 1 + 1 ∧ "+
					"m + 1 = m + 1",
				ByArith(pos, below))
			_, _, extremes := a.Unpack2As[Fun[Nat, Nat], Fun[Nat, Nat]](
				GroupPremises(simplex, KuhnSimplexExtrema.At(p, n, a.TermAs[Set[Fun[Nat, Nat]]]("«withApex»"))),
				"c",
				"d")
			ext := a.Conjuncts(
				extremes,
				"c is a point of the face with b",
				"d is a point of the face with b",
				"every point of the face with b lies between c and d",
				"d is c raised in every coordinate below n")
			between, raisedAll := ext[2], ext[3]
			comparable := a.Conjuncts(
				a.Unfolded(simplex, KuhnSimplexDef),
				"the face with b lies in the grid",
				"the face with b has n + 1 points",
				"any two points of the face with b are comparable")[2]
			apexIn := a.Have(
				"b is a point of the face with b",
				"b ∈ «withApex»",
				By(set_basic.InInsert))
			least := a.TermAs[Fun[Nat, Nat]]("«vertex»(v, τ, 0)")
			greatest := a.TermAs[Fun[Nat, Nat]]("«vertex»(v, τ, n)")
			onFace := a.Have(
				"vertices 0, n, m - 1 and m + 1 lie on the face",
				"«vertex»(v, τ, 0) ∈ delete(s, «vertex»(v, τ, m)) ∧ "+
					"«vertex»(v, τ, n) ∈ delete(s, «vertex»(v, τ, m)) ∧ "+
					"«vertex»(v, τ, m - 1) ∈ delete(s, «vertex»(v, τ, m)) ∧ "+
					"«vertex»(v, τ, m + 1) ∈ delete(s, «vertex»(v, τ, m))",
				By(
					steps,
					chain,
					oneToOne,
					neighbours,
					At(KuhnChainFaceVertices, n, v, τ, s, zero, m),
					At(KuhnChainFaceVertices, n, v, τ, s, n, m),
					At(KuhnChainFaceVertices, n, v, τ, s, before, m),
					At(KuhnChainFaceVertices, n, v, τ, s, after, m)))
			bounds := a.Conjuncts(
				a.Have(
					"c lies below vertex 0 and b, and vertex n and b below d",
					"kuhn_le(n, c, «vertex»(v, τ, 0)) ∧ "+
						"kuhn_le(n, «vertex»(v, τ, n), d) ∧ "+
						"kuhn_le(n, c, b) ∧ "+
						"kuhn_le(n, b, d)",
					By(onFace, apexIn, between.At(least), between.At(greatest), between.At(b), set_basic.InInsert)),
				"c lies below vertex 0",
				"vertex n lies below d",
				"c lies below b",
				"b lies below d")
			cLeast := a.Unfolded(bounds[0], KuhnLeDef)
			dGreatest := a.Unfolded(bounds[1], KuhnLeDef)
			cApex := a.Unfolded(bounds[2], KuhnLeDef)
			dApex := a.Unfolded(bounds[3], KuhnLeDef)
			aboveLeast := a.Have(
				"b lies above vertex 0: b lies above c, and c + 1 = d lies above vertex n, which is v + 1",
				"kuhn_le(n, «vertex»(v, τ, 0), b)",
				Derive(func(e *Argument) {
					e.Do(Unfold(KuhnLeDef))
					i := e.FixAs[Nat]("i")
					e.Show(
						"coordinate by coordinate",
						ByArith(steps.At(i), raisedAll.At(i), cLeast.At(i), dGreatest.At(i), cApex.At(i), dApex.At(i)))
				}))
			belowGreatest := a.Have(
				"b lies below vertex n: b lies below d = c + 1, and c below vertex 0, which is v",
				"kuhn_le(n, b, «vertex»(v, τ, n))",
				Derive(func(e *Argument) {
					e.Do(Unfold(KuhnLeDef))
					i := e.FixAs[Nat]("i")
					e.Show(
						"coordinate by coordinate",
						ByArith(steps.At(i), raisedAll.At(i), cLeast.At(i), dGreatest.At(i), cApex.At(i), dApex.At(i)))
				}))
			upward := a.Have(
				"b lies above every vertex before m",
				"∀j:num. j < m ⇒ kuhn_le(n, «vertex»(v, τ, j), b)",
				Derive(func(e *Argument) {
					e.Induct("j")
					e.Base(
						"vertex 0 lies below b",
						func(f *Argument) {
							f.Show(
								"shown above",
								By(aboveLeast))
						})
					e.Step(
						"a vertex on the face comparable with b and next above one below b lies below b",
						func(f *Argument, lower Fact) {
							early := f.Assume()
							stepsHere := f.Have(
								"j and suc(j) are consecutive vertices other than vertex m",
								"j < m ∧ j ≤ n ∧ ¬(j = m) ∧ suc(j) ≤ n ∧ ¬(suc(j) = m) ∧ suc(j) = j + 1",
								ByArith(early, below))
							j := f.TermAs[Nat]("j")
							next := f.TermAs[Nat]("suc(j)")
							nextVertex := f.TermAs[Fun[Nat, Nat]]("«vertex»(v, τ, suc(j))")
							onFaceHere := f.Have(
								"vertices j and suc(j) lie on the face",
								"«vertex»(v, τ, j) ∈ delete(s, «vertex»(v, τ, m)) ∧ "+
									"«vertex»(v, τ, suc(j)) ∈ delete(s, «vertex»(v, τ, m))",
								By(
									steps,
									chain,
									oneToOne,
									neighbours,
									stepsHere,
									At(KuhnChainFaceVertices, n, v, τ, s, j, m),
									At(KuhnChainFaceVertices, n, v, τ, s, next, m)))
							lowerHere := f.Have(
								"vertex j lies below b",
								"kuhn_le(n, «vertex»(v, τ, j), b)",
								By(lower, stepsHere))
							notUp := f.SupposeNot()
							down := f.Have(
								"b lies below vertex suc(j)",
								"kuhn_le(n, b, «vertex»(v, τ, suc(j)))",
								By(notUp, onFaceHere, apexIn, comparable.At(b, nextVertex), set_basic.InInsert))
							squeezed := f.Have(
								"b is vertex j or vertex suc(j)",
								"b = «vertex»(v, τ, j) ∨ b = «vertex»(v, τ, suc(j))",
								By(stepsHere, oneToOne, lowerHere, down, At(KuhnChainSqueeze, n, v, τ, j, next, b)))
							f.Show(
								"but b is off the face",
								By(squeezed, onFaceHere, apexOff))
						})
				}))
			downward := a.Have(
				"b lies below every vertex after m",
				"∀k:num. k < n - m ⇒ kuhn_le(n, b, «vertex»(v, τ, n - k))",
				Derive(func(e *Argument) {
					e.Induct("k")
					e.Base(
						"b lies below vertex n",
						func(f *Argument) {
							f.Assume()
							top := f.Have(
								"n - 0 = n",
								"n - 0 = n",
								ByArith())
							f.Do(top.Rw())
							f.Show(
								"shown above",
								By(belowGreatest))
						})
					e.Step(
						"a vertex on the face comparable with b and next below one above b lies above b",
						func(f *Argument, upper Fact) {
							late := f.Assume()
							stepsHere := f.Have(
								"n - suc(k) and n - k are consecutive vertices other than vertex m",
								"k < n - m ∧ "+
									"n - suc(k) ≤ n ∧ "+
									"¬(n - suc(k) = m) ∧ "+
									"n - k ≤ n ∧ "+
									"¬(n - k = m) ∧ "+
									"n - k = n - suc(k) + 1",
								ByArith(late, below))
							prev := f.TermAs[Nat]("n - suc(k)")
							here := f.TermAs[Nat]("n - k")
							prevVertex := f.TermAs[Fun[Nat, Nat]]("«vertex»(v, τ, n - suc(k))")
							onFaceHere := f.Have(
								"vertices n - suc(k) and n - k lie on the face",
								"«vertex»(v, τ, n - suc(k)) ∈ delete(s, «vertex»(v, τ, m)) ∧ "+
									"«vertex»(v, τ, n - k) ∈ delete(s, «vertex»(v, τ, m))",
								By(
									steps,
									chain,
									oneToOne,
									neighbours,
									stepsHere,
									At(KuhnChainFaceVertices, n, v, τ, s, prev, m),
									At(KuhnChainFaceVertices, n, v, τ, s, here, m)))
							upperHere := f.Have(
								"b lies below vertex n - k",
								"kuhn_le(n, b, «vertex»(v, τ, n - k))",
								By(upper, stepsHere))
							notDown := f.SupposeNot()
							up := f.Have(
								"vertex n - suc(k) lies below b",
								"kuhn_le(n, «vertex»(v, τ, n - suc(k)), b)",
								By(notDown, onFaceHere, apexIn, comparable.At(prevVertex, b), set_basic.InInsert))
							squeezed := f.Have(
								"b is vertex n - suc(k) or vertex n - k",
								"b = «vertex»(v, τ, n - suc(k)) ∨ b = «vertex»(v, τ, n - k)",
								By(stepsHere, oneToOne, up, upperHere, At(KuhnChainSqueeze, n, v, τ, prev, here, b)))
							f.Show(
								"but b is off the face",
								By(squeezed, onFaceHere, apexOff))
						})
				}))
			aboveBefore := a.Have(
				"vertex m - 1 lies below b",
				"kuhn_le(n, «vertex»(v, τ, m - 1), b)",
				By(neighbours, upward.At(before)))
			belowAfter := a.Have(
				"b lies below vertex m + 1",
				"kuhn_le(n, b, «vertex»(v, τ, m + 1))",
				Derive(func(e *Argument) {
					back := e.Conjuncts(
						e.Have(
							"m + 1 is n less n - (m + 1)",
							"n - (n - (m + 1)) = m + 1 ∧ n - (m + 1) < n - m",
							ByArith(below)),
						"n - (n - (m + 1)) = m + 1",
						"n - (m + 1) lies below n - m")
					farBelow := e.Unfolded(GroupPremises(back[1], downward.At(e.TermAs[Nat]("n - (m + 1)"))), KuhnLeDef)
					e.Do(Unfold(KuhnLeDef))
					i := e.FixAs[Nat]("i")
					e.Show(
						"downward, at n - (m + 1)",
						ByArith(back[0], farBelow.At(i)))
				}))
			lowAt := a.Unfolded(aboveBefore, KuhnLeDef)
			highAt := a.Unfolded(belowAfter, KuhnLeDef)
			a.Cases(a.Term("∀i:num. i < n ∧ τ(i) = m ⇒ b(i) = v(i)"))
			a.When(
				"b leaves the coordinate of step m low, so it lies between vertices m - 1 and m",
				func(e *Argument, lowAtM Fact) {
					belowM := e.Have(
						"b lies below vertex m",
						"kuhn_le(n, b, «vertex»(v, τ, m))",
						Derive(func(f *Argument) {
							f.Do(Unfold(KuhnLeDef))
							i := f.FixAs[Nat]("i")
							inRange := f.Assuming(
								f.Term("i < n"),
								"from n on b is v",
								Given(func(g *Argument, beyond Fact) {
									g.Show(
										"b(i) = v(i)",
										ByArith(beyond, lowAt.At(i), highAt.At(i)))
								}))
							f.Cases(f.Term("τ(i) = m"))
							f.When(
								"at step m b is v",
								func(g *Argument, atM Fact) {
									g.Show(
										"b(i) = v(i)",
										ByArith(inRange, atM, lowAtM.At(i), lowAt.At(i), highAt.At(i)))
								})
							f.Otherwise(
								"off step m vertices m and m + 1 agree",
								func(g *Argument, offM Fact) {
									g.Show(
										"b(i) lies between them",
										ByArith(inRange, offM, lowAt.At(i), highAt.At(i)))
								})
						}))
					squeezed := e.Have(
						"b is vertex m - 1 or vertex m",
						"b = «vertex»(v, τ, m - 1) ∨ b = «vertex»(v, τ, m)",
						By(neighbours, oneToOne, aboveBefore, belowM, At(KuhnChainSqueeze, n, v, τ, before, m, b)))
					e.Show(
						"vertex m - 1 is on the face, so b is vertex m",
						By(squeezed, onFace, apexOff))
				})
			a.Otherwise(
				"b raises the coordinate of step m",
				func(e *Argument, notLowAtM Fact) {
					k2, raisedM := e.ObtainAs[Nat](
						"the coordinate k₂ of step m is raised in b",
						"∃k₂:num. k₂ < n ∧ τ(k₂) = m ∧ ¬(b(k₂) = v(k₂))",
						By(notLowAtM))
					upM := e.Have(
						"b(k₂) = v(k₂) + 1",
						"b(k₂) = v(k₂) + 1",
						ByArith(raisedM, neighbours, lowAt.At(k2)))
					e.Cases(e.Term("∀i:num. i < n ∧ τ(i) = m - 1 ⇒ b(i) = v(i)"))
					e.When(
						"b leaves the coordinate of step m - 1 low, so it is the chain with the two steps exchanged",
						func(f *Argument, lowBefore Fact) {
							swapped := f.TermAs[Fun[Nat, Nat]]("«swapped»(v, τ, m)")
							agreement := f.Have(
								"b agrees with the exchanged point at steps m - 1 and m",
								"∀i:num. i < n ∧ m - 1 ≤ τ(i) ∧ τ(i) < m + 1 ⇒ b(i) = «swapped»(v, τ, m, i)",
								Derive(func(g *Argument) {
									i := g.FixAs[Nat]("i")
									atSteps := g.Assume()
									g.Cases(g.Term("τ(i) = m"))
									g.When(
										"at step m the coordinate is k₂, raised",
										func(u *Argument, atM Fact) {
											same := u.Have(
												"τ is one-to-one, so i is k₂",
												"i = k₂",
												ByArith(atSteps, atM, raisedM, oneToOne, functions.InjectiveOnDef))
											u.Show(
												"b(i) = v(i) + 1",
												ByArith(same, upM, atSteps, atM))
										})
									g.Otherwise(
										"at step m - 1 the coordinate is low",
										func(u *Argument, offM Fact) {
											u.Show(
												"b(i) = v(i)",
												ByArith(atSteps, offM, lowBefore.At(i)))
										})
								}))
							isSwapped := f.Have(
								"b and the exchanged point lie between vertices m - 1 and "+
									"m + 1 and agree at the steps between, so they are equal",
								"b = «swapped»(v, τ, m)",
								ByArith(
									pos,
									agreement,
									aboveBefore,
									belowAfter,
									KuhnEarlierBelowExchanged.At(n, v, τ, before, m),
									KuhnExchangedBelowLater.At(n, v, τ, after, m),
									At(KuhnChainAgree, n, v, τ, before, after, b, swapped)))
							f.Show(
								"b is the second apex",
								By(isSwapped))
						})
					e.Otherwise(
						"b raises the coordinate of step m - 1 too, so it lies between vertices m and m + 1",
						func(f *Argument, notLowBefore Fact) {
							k1, raisedBefore := f.ObtainAs[Nat](
								"the coordinate k₁ of step m - 1 is raised in b",
								"∃k₁:num. k₁ < n ∧ τ(k₁) = m - 1 ∧ ¬(b(k₁) = v(k₁))",
								By(notLowBefore))
							atStepBefore := f.Conjuncts(
								raisedBefore,
								"k₁ is below n",
								"k₁ is raised at step m - 1",
								"b moves k₁")
							upBefore := f.Have(
								"b(k₁) = v(k₁) + 1",
								"b(k₁) = v(k₁) + 1",
								ByArith(raisedBefore, lowAt.At(k1)))
							aboveM := f.Have(
								"vertex m lies below b",
								"kuhn_le(n, «vertex»(v, τ, m), b)",
								Derive(func(g *Argument) {
									g.Do(Unfold(KuhnLeDef))
									i := g.FixAs[Nat]("i")
									inRange := g.Assuming(
										g.Term("i < n"),
										"from n on b is v",
										Given(func(u *Argument, beyond Fact) {
											u.Show(
												"b(i) = v(i)",
												ByArith(beyond, lowAt.At(i), highAt.At(i)))
										}))
									g.Cases(g.Term("τ(i) = m - 1"))
									g.When(
										"at step m - 1 the coordinate is k₁, raised",
										func(u *Argument, atBefore Fact) {
											same := u.Have(
												"τ is one-to-one, so i is k₁",
												"i = k₁",
												ByArith(inRange, atBefore, atStepBefore[0], atStepBefore[1], oneToOne, functions.InjectiveOnDef))
											u.Show(
												"b(i) = v(i) + 1",
												ByArith(same, upBefore, inRange, atBefore, highAt.At(i)))
										})
									g.Otherwise(
										"off step m - 1 vertices m - 1 and m agree",
										func(u *Argument, offBefore Fact) {
											u.Show(
												"b(i) lies between them",
												ByArith(inRange, offBefore, lowAt.At(i), highAt.At(i)))
										})
								}))
							squeezed := f.Have(
								"b is vertex m or vertex m + 1",
								"b = «vertex»(v, τ, m) ∨ b = «vertex»(v, τ, m + 1)",
								By(neighbours, oneToOne, aboveM, belowAfter, At(KuhnChainSqueeze, n, v, τ, m, after, b)))
							f.Show(
								"vertex m + 1 is on the face, so b is vertex m",
								By(squeezed, onFace, apexOff))
						})
				})
		}),
})}

// KuhnSimplexReplace — replacing a vertex of a Kuhn simplex by a grid
// point outside it that is comparable with every remaining vertex gives a
// Kuhn simplex: the count is kept, the grid is kept, and every pair is
// comparable.
var KuhnSimplexReplace = kuhnSimplexReplaceThm{family.Add(registry.ProofEntry{
	Name: "KuhnSimplexReplace",
	Key:  "prop_f7d21f58eaf6020b",
	Build: family.Theorem(Statement{
		Binders: "∀p n:num. ∀s:set(num → num). ∀a b:(num → num).",
		Hypotheses: []string{
			"kuhn_simplex(p, n, s)",
			"a ∈ s",
			"b ∈ kuhn_grid(p, n)",
			"b ∉ s",
			"∀x:(num → num). x ∈ delete(s, a) ⇒ kuhn_le(n, x, b) ∨ kuhn_le(n, b, x)",
		},
		Conclusion: "kuhn_simplex(p, n, insert(b, delete(s, a)))",
	},
		func(
			arg *Argument,
			p, n *Expr[Nat],
			s *Expr[Set[Fun[Nat, Nat]]],
			a, b *Expr[Fun[Nat, Nat]],
			h Fact,
		) {
			given := arg.Conjuncts(
				h,
				"s is a Kuhn simplex",
				"a is a vertex of s",
				"b is a grid point",
				"b is not in s",
				"b is comparable with every point of the face")
			simplex := arg.Conjuncts(
				arg.Unfolded(given[0], KuhnSimplexDef),
				"s lies in the grid",
				"s has n + 1 points",
				"any two points of s are comparable")
			face := arg.TermAs[Set[Fun[Nat, Nat]]]("delete(s, a)")
			replaced := arg.TermAs[Set[Fun[Nat, Nat]]]("insert(b, delete(s, a))")
			size := arg.TermAs[Nat]("n + 1")
			inGrid := arg.Have(
				"the face and b lie in the grid",
				"insert(b, delete(s, a)) ⊆ kuhn_grid(p, n)",
				BySets(simplex[0], given[2]))
			counted := arg.Have(
				"the face has n points, b is a new one, so n + 1 in all",
				"has_size(insert(b, delete(s, a)), n + 1)",
				ByArith(
					simplex[1],
					given[1],
					given[3],
					cardinality.HasSizeDef.At(s, size),
					cardinality.HasSizeDef.At(replaced, size),
					cardinality.CardDelete.At(s, a),
					finite_set.FiniteDeleteImp.At(s, a),
					finite_set.FiniteInsert.At(b, face),
					cardinality.InsertCountsOneMore.At(face, b),
					set_basic.InDelete))
			pairs := arg.Have(
				"any two points of the face with b are comparable",
				Statement{
					Binders: "∀x y:(num → num).",
					Hypotheses: []string{
						"x ∈ insert(b, delete(s, a))",
						"y ∈ insert(b, delete(s, a))",
					},
					Conclusion: "kuhn_le(n, x, y) ∨ kuhn_le(n, y, x)",
				},
				Derive(func(c *Argument) {
					x := c.FixAs[Fun[Nat, Nat]]("x")
					y := c.FixAs[Fun[Nat, Nat]]("y")
					both := c.Assume()
					c.Show(
						"each is b or a point of s other than a",
						By(
							both,
							simplex[2].At(x, y),
							given[4].At(x),
							given[4].At(y),
							KuhnLeRefl.At(n, b),
							set_basic.InInsert,
							set_basic.InDelete))
				}))
			arg.Do(Unfold(KuhnSimplexDef))
			arg.Show(
				"the three conditions",
				By(inGrid, counted, pairs))
		}),
})}

// KuhnFaceZeroPlane — a face of a Kuhn simplex lying in a coordinate
// plane x(j) = 0 is a face of that simplex only. Write s as the chain from
// v in the order τ (KuhnSimplexChain) and a as its vertex m. Every other
// vertex lies on the face, so in the plane: vertex n is v(j) + 1 at j, so a
// is vertex n, and vertices 0 and n - 1 give v(j) = 0 and τ(j) = n - 1. The
// face opposite the greatest vertex has one apex besides a, v lowered in the
// coordinate of the last step (KuhnApexOppositeGreatest); that coordinate is
// j alone, where v is 0 and 0 - 1 = 0 in ℕ, so the lowered point is v
// itself, a point of the face, and s is the only simplex through it
// (KuhnSingleCoface).
var KuhnFaceZeroPlane = kuhnFaceZeroPlaneThm{family.Add(registry.ProofEntry{
	Name: "KuhnFaceZeroPlane",
	Key:  "prop_a077f1c3654a5ec",
	Reading: "j < n carries it and makes the statement vacuous at n = 0. Only the " +
		"face opposite the greatest point holds a coordinate constant at 0, the one the " +
		"last step raises; a face of a Kuhn simplex lies in at most one coordinate plane.",
	Build: family.Theorem(Statement{
		Binders: "∀p n j:num. ∀s:set(num → num). ∀a:(num → num).",
		Hypotheses: []string{
			"kuhn_simplex(p, n, s)",
			"a ∈ s",
			"j < n",
			"∀x:(num → num). x ∈ delete(s, a) ⇒ x(j) = 0",
		},
		Conclusion: "card(«cofaces») = 1",
	},
		func(
			arg *Argument,
			p, n, j *Expr[Nat],
			s *Expr[Set[Fun[Nat, Nat]]],
			a *Expr[Fun[Nat, Nat]],
			h Fact,
		) {
			given := arg.Conjuncts(
				h,
				"s is a Kuhn simplex",
				"a is a vertex of s",
				"j is a coordinate",
				"the face opposite a lies in the plane x(j) = 0")
			simplex, aIn, coordinate, inPlane := given[0], given[1], given[2], given[3]
			v, τ, presented := arg.Unpack2As[Fun[Nat, Nat], Fun[Nat, Nat]](
				GroupPremises(simplex, KuhnSimplexChain.At(p, n, s)), "v", "τ")
			chainParts := arg.Conjuncts(
				presented,
				"τ gives each coordinate below n a step below n",
				"τ is one-to-one below n",
				"s is the chain from v in the order τ")
			steps, oneToOne, chain := chainParts[0], chainParts[1], chainParts[2]
			zero := arg.TermAs[Nat]("0")
			previous := arg.TermAs[Nat]("n - 1")
			onChain := arg.Have(
				"a is a vertex of the chain",
				"a ∈ {«vertex»(v, τ, m) | m:num | m ≤ n}",
				Derive(func(b *Argument) {
					b.Do(chain.RwRev())
					b.Show(
						"a lies in s",
						By(aIn))
				}))
			m, aAt := arg.UnpackAs[Nat](onChain, "m")
			aParts := arg.Conjuncts(
				aAt,
				"m is at most n",
				"a is vertex m")
			level := arg.Have(
				"every vertex but a lies on the face, so in the plane x(j) = 0",
				"∀k:num. k ≤ n ∧ ¬(k = m) ⇒ «vertex»(v, τ, k, j) = 0",
				Derive(func(b *Argument) {
					k := b.FixAs[Nat]("k")
					other := b.Assume()
					b.Show(
						"vertex k lies on the face",
						By(
							inPlane.At(b.TermAs[Fun[Nat, Nat]]("«vertex»(v, τ, k)")),
							other,
							steps,
							oneToOne,
							chain,
							aParts[0],
							aParts[1],
							KuhnChainFaceVertices.At(n, v, τ, s, k, m)))
				}))
			greatest := arg.Have(
				"a is the greatest vertex: vertex n is v(j) + 1 at j",
				"m = n",
				ByArith(level.At(n), coordinate, steps.At(j)))
			reading := arg.Have(
				"vertices 0 and n - 1 lie in the plane: v(j) = 0, and j is raised at the last step",
				"v(j) = 0 ∧ τ(j) = n - 1",
				ByArith(level.At(zero), level.At(previous), greatest, coordinate, steps.At(j)))
			isGreatest := arg.Have(
				"a is vertex n",
				"a = «vertex»(v, τ, n)",
				By(Normalized, aParts[1], greatest))
			ends := arg.Have(
				"n is positive, j lying below it, so vertices 0 and n are distinct",
				"0 < n ∧ 0 ≤ n ∧ ¬(0 = n) ∧ n ≤ n",
				ByArith(coordinate))
			leastOnFace := arg.Have(
				"the least vertex lies on the face",
				"«vertex»(v, τ, 0) ∈ delete(s, a)",
				By(steps, oneToOne, chain, isGreatest, ends, KuhnChainFaceVertices.At(n, v, τ, s, zero, n)))
			collapse := arg.Have(
				"lowering v in the coordinate of the last step leaves v: that coordinate is j, where 0 - 1 = 0",
				"«lowered»(v, τ) = «vertex»(v, τ, 0)",
				Funext(),
				Derive(func(b *Argument) {
					b.FixAs[Nat]("i")
					b.Cases(b.Term("i < n ∧ τ(i) = n - 1"))
					b.When(
						"i is raised at the last step, so i is j",
						func(c *Argument, last Fact) {
							same := c.Have(
								"τ is one-to-one below n and takes j to n - 1",
								"i = j",
								ByArith(last, reading, oneToOne, coordinate, functions.InjectiveOnDef))
							c.Show(
								"v(j) - 1 = 0 = v(j)",
								ByArith(same, last, reading))
						})
					b.Otherwise(
						"i is not lowered",
						func(c *Argument, notLast Fact) {
							c.Show(
								"both are v(i)",
								ByArith(Normalized, notLast))
						})
				}))
			unique := arg.Have(
				"every apex of the face is a",
				"∀b:(num → num). b ∉ delete(s, a) ∧ kuhn_simplex(p, n, insert(b, delete(s, a))) ⇒ b = a",
				Derive(func(c *Argument) {
					b := c.FixAs[Fun[Nat, Nat]]("b")
					apex := c.Conjuncts(
						c.Assume(),
						"b is off the face",
						"the face with b is a Kuhn simplex")
					simplexAt := c.Have(
						"the face opposite vertex n with b is a Kuhn simplex",
						"kuhn_simplex(p, n, insert(b, delete(s, «vertex»(v, τ, n))))",
						By(apex[1], isGreatest))
					either := c.Have(
						"the two apexes of the face opposite the greatest vertex",
						"b = «vertex»(v, τ, n) ∨ b = «lowered»(v, τ)",
						By(simplexAt, ends, steps, oneToOne, chain, KuhnApexOppositeGreatest.At(p, n, v, τ, s, b)))
					c.Do(either.SplitDisj(
						LeftHolds(
							"vertex n is a",
							Given(func(d *Argument, top Fact) {
								d.Show(
									"b is a",
									By(top, isGreatest))
							})),
						RightHolds(
							"the lowered point is the least vertex, on the face, where b is not",
							Given(func(d *Argument, low Fact) {
								d.Show(
									"b would then lie on the face",
									By(low, collapse, leastOnFace, apex[0]))
							}))))
				}))
			arg.Show(
				"one apex, one simplex",
				By(simplex, aIn, unique, KuhnSingleCoface.At(p, n, s, a)))
		}),
})}

// KuhnFaceTopPlane — a face of a Kuhn simplex lying in a coordinate
// plane x(j) = p is a face of that simplex only. Write s as the chain from
// v in the order τ (KuhnSimplexChain) and a as its vertex m. Every vertex
// other than a lies on the face, so in the plane, while vertex n, a grid
// point, is v(j) + 1 ≤ p at j; vertex 0 is v(j) there, so it is a, and
// vertices n and 1 give v(j) + 1 = p and τ(j) = 0. The face opposite the
// least vertex has one apex besides a, vertex n raised once more in the
// coordinate of the first step (KuhnApexOppositeLeast); that coordinate is
// j, where the point is p + 1, off the grid, so s is the only simplex
// through the face (KuhnSingleCoface).
var KuhnFaceTopPlane = kuhnFaceTopPlaneThm{family.Add(registry.ProofEntry{
	Name: "KuhnFaceTopPlane",
	Key:  "prop_53cd01e29df5deae",
	Reading: "The mirror of KuhnFaceZeroPlane: since the greatest point lies in the grid, only the " +
		"face opposite the least point holds a coordinate constant at p, the one the first step raises.",
	Build: family.Theorem(Statement{
		Binders: "∀p n j:num. ∀s:set(num → num). ∀a:(num → num).",
		Hypotheses: []string{
			"kuhn_simplex(p, n, s)",
			"a ∈ s",
			"j < n",
			"∀x:(num → num). x ∈ delete(s, a) ⇒ x(j) = p",
		},
		Conclusion: "card(«cofaces») = 1",
	},
		func(
			arg *Argument,
			p, n, j *Expr[Nat],
			s *Expr[Set[Fun[Nat, Nat]]],
			a *Expr[Fun[Nat, Nat]],
			h Fact,
		) {
			given := arg.Conjuncts(
				h,
				"s is a Kuhn simplex",
				"a is a vertex of s",
				"j is a coordinate",
				"the face opposite a lies in the plane x(j) = p")
			simplex, aIn, coordinate, inPlane := given[0], given[1], given[2], given[3]
			bounded := arg.Have(
				"a point of a Kuhn simplex is a grid point, at most p at j",
				"∀t:set(num → num). ∀x:(num → num). kuhn_simplex(p, n, t) ∧ x ∈ t ⇒ x(j) ≤ p",
				Derive(func(b *Argument) {
					b.FixAs[Set[Fun[Nat, Nat]]]("t")
					b.FixAs[Fun[Nat, Nat]]("x")
					point := b.Conjuncts(
						b.Assume(),
						"t is a Kuhn simplex",
						"x is a point of t")
					grid := b.Conjuncts(
						b.Unfolded(point[0], KuhnSimplexDef),
						"t lies in the grid",
						"t has n + 1 points",
						"any two points of t are comparable")[0]
					onGrid := b.Have(
						"x is a grid point",
						"x ∈ kuhn_grid(p, n)",
						BySets(point[1], grid))
					b.Show(
						"a grid point is at most p below n",
						By(b.Unfolded(onGrid, KuhnGridDef), coordinate))
				}))
			v, τ, presented := arg.Unpack2As[Fun[Nat, Nat], Fun[Nat, Nat]](
				GroupPremises(simplex, KuhnSimplexChain.At(p, n, s)), "v", "τ")
			chainParts := arg.Conjuncts(
				presented,
				"τ gives each coordinate below n a step below n",
				"τ is one-to-one below n",
				"s is the chain from v in the order τ")
			steps, oneToOne, chain := chainParts[0], chainParts[1], chainParts[2]
			zero := arg.TermAs[Nat]("0")
			one := arg.TermAs[Nat]("1")
			onChain := arg.Have(
				"a is a vertex of the chain",
				"a ∈ {«vertex»(v, τ, m) | m:num | m ≤ n}",
				Derive(func(b *Argument) {
					b.Do(chain.RwRev())
					b.Show(
						"a lies in s",
						By(aIn))
				}))
			m, aAt := arg.UnpackAs[Nat](onChain, "m")
			aParts := arg.Conjuncts(
				aAt,
				"m is at most n",
				"a is vertex m")
			level := arg.Have(
				"every vertex but a lies on the face, so in the plane x(j) = p",
				"∀k:num. k ≤ n ∧ ¬(k = m) ⇒ «vertex»(v, τ, k, j) = p",
				Derive(func(b *Argument) {
					k := b.FixAs[Nat]("k")
					other := b.Assume()
					b.Show(
						"vertex k lies on the face",
						By(
							inPlane.At(b.TermAs[Fun[Nat, Nat]]("«vertex»(v, τ, k)")),
							other,
							steps,
							oneToOne,
							chain,
							aParts[0],
							aParts[1],
							KuhnChainFaceVertices.At(n, v, τ, s, k, m)))
				}))
			room := arg.Have(
				"vertex n, a point of s, is a grid point: v(j) + 1 ≤ p",
				"«vertex»(v, τ, n, j) ≤ p",
				Derive(func(b *Argument) {
					onS := b.Have(
						"vertex n is a point of s",
						"«vertex»(v, τ, n) ∈ s",
						Derive(func(c *Argument) {
							c.Do(chain.Rw())
							c.Show(
								"vertex n is on the chain",
								By(nat_order.LessEqRefl.At(n)))
						}))
					b.Show(
						"s lies in the grid",
						By(bounded.At(s, b.TermAs[Fun[Nat, Nat]]("«vertex»(v, τ, n)")), simplex, onS))
				}))
			least := arg.Have(
				"a is the least vertex: vertex 0 is v(j) < p at j",
				"m = 0",
				ByArith(level.At(zero), room, coordinate, steps.At(j)))
			reading := arg.Have(
				"vertices n and 1 lie in the plane: v(j) + 1 = p, and j is raised at the first step",
				"v(j) + 1 = p ∧ τ(j) = 0",
				ByArith(level.At(n), level.At(one), least, coordinate, steps.At(j)))
			isLeast := arg.Have(
				"a is vertex 0",
				"a = «vertex»(v, τ, 0)",
				By(Normalized, aParts[1], least))
			pos := arg.Have(
				"n is positive, j lying below it",
				"0 < n",
				ByArith(coordinate))
			unique := arg.Have(
				"every apex of the face is a",
				"∀b:(num → num). b ∉ delete(s, a) ∧ kuhn_simplex(p, n, insert(b, delete(s, a))) ⇒ b = a",
				Derive(func(c *Argument) {
					b := c.FixAs[Fun[Nat, Nat]]("b")
					apex := c.Conjuncts(
						c.Assume(),
						"b is off the face",
						"the face with b is a Kuhn simplex")
					below := c.Have(
						"b is a point of the face with b, a Kuhn simplex, so b(j) ≤ p",
						"b(j) ≤ p",
						By(
							bounded.At(c.TermAs[Set[Fun[Nat, Nat]]]("insert(b, delete(s, a))"), b),
							apex[1],
							set_basic.InInsert.At(c.TermAs[Set[Fun[Nat, Nat]]]("delete(s, a)"), b, b)))
					simplexAt := c.Have(
						"the face opposite vertex 0 with b is a Kuhn simplex",
						"kuhn_simplex(p, n, insert(b, delete(s, «vertex»(v, τ, 0))))",
						By(apex[1], isLeast))
					either := c.Have(
						"the two apexes of the face opposite the least vertex",
						"b = «vertex»(v, τ, 0) ∨ b = «lifted»(v, τ)",
						By(simplexAt, pos, steps, oneToOne, chain, KuhnApexOppositeLeast.At(p, n, v, τ, s, b)))
					c.Do(either.SplitDisj(
						LeftHolds(
							"vertex 0 is a",
							Given(func(d *Argument, start Fact) {
								d.Show(
									"b is a",
									By(start, isLeast))
							})),
						RightHolds(
							"the lifted point is p + 1 at j, off the grid",
							Given(func(d *Argument, lifted Fact) {
								atJ := d.Have(
									"b is the lifted point, v(j) + 2 at j",
									"b(j) = «lifted»(v, τ, j)",
									By(Normalized, lifted))
								d.Show(
									"v(j) + 2 = p + 1 exceeds p",
									ByArith(atJ, below, reading, coordinate))
							}))))
				}))
			arg.Show(
				"one apex, one simplex",
				By(simplex, aIn, unique, KuhnSingleCoface.At(p, n, s, a)))
		}),
})}

// KuhnFaceInterior — a face of a Kuhn simplex lying in no boundary plane
// of the cube is a face of exactly two simplices. Write s as the chain
// from v in the order τ (KuhnSimplexChain) and a as its vertex m. A
// simplex through the face is the face with one point put back, and that
// point is a or one other (KuhnApexOppositeLeast, KuhnApexOppositeGreatest,
// KuhnApexOppositeInner): for m = 0 the chain's end raised once more in
// the coordinate of the first step, for m = n its start lowered in the
// coordinate of the last step, and for 0 < m < n vertex m with steps m - 1
// and m exchanged. The interior hypothesis keeps the first in the grid and
// the second off s; the third reads none of it. The other point is off s
// and comparable with every vertex of the face — for an inner vertex by
// KuhnEarlierBelowExchanged and KuhnExchangedBelowLater — so the face with
// it put back is a simplex (KuhnSimplexReplace), the second of the two.
var KuhnFaceInterior = kuhnFaceInteriorThm{family.Add(registry.ProofEntry{
	Name: "KuhnFaceInterior",
	Key:  "prop_4ed6123987a5239d",
	Reading: "0 < n is load-bearing: at n = 0 the face is ∅ and lies in the one " +
		"simplex, so the count is 1. The interior hypothesis is read only for the two end " +
		"vertices: at the least it keeps the other apex in the grid, at the greatest off s.",
	Build: family.Sections(Statement{
		Binders: "∀p n:num. ∀s:set(num → num). ∀a:(num → num).",
		Hypotheses: []string{
			"0 < n",
			"kuhn_simplex(p, n, s)",
			"a ∈ s",
			"∀j:num. " +
				"    j < n ⇒ " +
				"    (∃x:(num → num). x ∈ delete(s, a) ∧ ¬(x(j) = 0)) ∧ " +
				"    (∃x:(num → num). x ∈ delete(s, a) ∧ ¬(x(j) = p))",
		},
		Conclusion: "card(«cofaces») = 2",
	},
		func(ctx *Script, headline string) *GoalStackNode {
			twoApexes := ctx.Lemma(Statement{
				Binders: "∀p n:num. ∀s:set(num → num). ∀a c:(num → num).",
				Hypotheses: []string{
					"kuhn_simplex(p, n, s)",
					"a ∈ s",
					"c ∉ s",
					"kuhn_simplex(p, n, insert(c, delete(s, a)))",
					"∀b:(num → num). b ∉ delete(s, a) ∧ kuhn_simplex(p, n, insert(b, delete(s, a))) ⇒ b = a ∨ b = c",
				},
				Conclusion: "card(«cofaces») = 2",
			}, func(
				arg *Argument,
				p, n *Expr[Nat],
				s *Expr[Set[Fun[Nat, Nat]]],
				a, c *Expr[Fun[Nat, Nat]],
				h Fact,
			) {
				given := arg.Conjuncts(
					h,
					"s is a Kuhn simplex",
					"a is a vertex of s",
					"c is not in s",
					"the face with c is a Kuhn simplex",
					"every apex of the face is a or c")
				other := arg.TermAs[Set[Fun[Nat, Nat]]]("insert(c, delete(s, a))")
				listedSet := arg.TermAs[Set[Set[Fun[Nat, Nat]]]]("{s, insert(c, delete(s, a))}")
				pointwise := arg.Have(
					"a Kuhn simplex lies through the face exactly when it is s or the face with c",
					"∀u:set(num → num). u ∈ «cofaces» ⇔ u ∈ {s, insert(c, delete(s, a))}",
					Derive(func(d *Argument) {
						u := d.FixAs[Set[Fun[Nat, Nat]]]("u")
						d.Iff()
						d.Forward(
							"a simplex through the face is the face with its apex put back, and the apex is a or c",
							func(e *Argument, through Fact) {
								apex, putBack := e.UnpackAs[Fun[Nat, Nat]](
									e.Simplified(through, Fwd(KuhnCofaceApex)),
									"b")
								read := e.Conjuncts(
									putBack,
									"b is off the face",
									"the face with b is a Kuhn simplex",
									"u is the face with b")
								e.Cases(e.Term("b = a"))
								e.When(
									"the apex a puts back s",
									func(f *Argument, isA Fact) {
										f.Show(
											"u is s",
											By(isA, read[2], given[1], set_algebra.InsertDelete.At(s, a), set_basic.InInsert))
									})
								e.Otherwise(
									"the apex c gives the other simplex",
									func(f *Argument, notA Fact) {
										isC := f.Have(
											"the apex is c",
											"b = c",
											By(notA, read[0], read[1], given[4].At(apex)))
										f.Do(read[2].Rw())
										f.Do(isC.Rw())
										f.Show(
											"the face with c is listed",
											BySets())
									})
							})
						d.Backward(
							"s and the face with c are simplices through the face",
							func(e *Argument, listed Fact) {
								e.Cases(e.Term("u = s"))
								e.When(
									"s, with apex a",
									func(f *Argument, isS Fact) {
										withA := f.Have(
											"s is the face with a",
											"a ∉ delete(s, a) ∧ kuhn_simplex(p, n, insert(a, delete(s, a))) ∧ u = insert(a, delete(s, a))",
											By(Normalized, isS, given[0], given[1], set_algebra.InsertDelete.At(s, a), set_basic.InDelete))
										f.Do(Simp(Fwd(KuhnCofaceApex)))
										f.Show(
											"u lies in the cofaces",
											By(withA))
									})
								e.Otherwise(
									"the face with c, with apex c",
									func(f *Argument, notS Fact) {
										single := f.TermAs[Set[Set[Fun[Nat, Nat]]]]("{insert(c, delete(s, a))}")
										isOther := f.Have(
											"u is the other listed set",
											"u = insert(c, delete(s, a))",
											By(notS, listed, set_basic.InInsert.At(single, s, u), set_basic.InSing.At(u, other)))
										withC := f.Have(
											"u is the face with c",
											"c ∉ delete(s, a) ∧ kuhn_simplex(p, n, insert(c, delete(s, a))) ∧ u = insert(c, delete(s, a))",
											By(isOther, given[2], given[3], set_basic.InDelete))
										f.Do(Simp(Fwd(KuhnCofaceApex)))
										f.Show(
											"u lies in the cofaces",
											By(withC))
									})
							})
					}))
				both := arg.Have(
					"the simplices through the face are s and the face with c",
					"«cofaces» = {s, insert(c, delete(s, a))}",
					By(pointwise, set_basic.Extension.At(arg.TermAs[Set[Set[Fun[Nat, Nat]]]]("«cofaces»"), listedSet)))
				differ := arg.Have(
					"s is not the face with c, which holds c",
					"¬(s = insert(c, delete(s, a)))",
					By(Normalized, given[2], set_basic.InInsert))
				arg.Do(both.Rw())
				arg.Show(
					"two distinct sets",
					By(
						differ,
						cardinality.HasSizePair.At(s, other),
						cardinality.CardOfSized.At(listedSet, arg.TermAs[Nat]("2"))))
			})
			laterBelowLifted := ctx.Lemma(Statement{
				Binders: "∀n:num. ∀v τ:(num → num). ∀j:num.",
				Hypotheses: []string{
					"0 < j",
					"j ≤ n",
				},
				Conclusion: "kuhn_le(n, «vertex»(v, τ, j), «lifted»(v, τ))",
			}, func(arg *Argument, n *Expr[Nat], v, τ *Expr[Fun[Nat, Nat]], j *Expr[Nat], h Fact) {
				given := arg.Conjuncts(
					h,
					"j is positive",
					"j is at most n")
				positive, upTo := given[0], given[1]
				arg.Do(Unfold(KuhnLeDef))
				arg.FixAs[Nat]("i")
				inRange := arg.Assuming(
					arg.Term("i < n"),
					"from n on both are v",
					Given(func(b *Argument, beyond Fact) {
						b.Show(
							"nothing is raised there",
							ByArith(beyond))
					}))
				arg.Cases(arg.Term("τ(i) = 0"))
				arg.When(
					"i is the coordinate of the first step, which vertex j raises and the lifted point raises twice",
					func(b *Argument, firstStep Fact) {
						b.Show(
							"vertex j is v(i) + 1 and the lifted point v(i) + 2",
							ByArith(inRange, firstStep, positive))
					})
				arg.Otherwise(
					"elsewhere the lifted point is vertex n",
					func(b *Argument, elsewhere Fact) {
						b.Show(
							"a coordinate vertex j raises, vertex n raises too, j being at most n",
							ByArith(inRange, elsewhere, upTo))
					})
			})
			loweredBelowEarlier := ctx.Lemma(Statement{
				Binders: "∀n:num. ∀v τ:(num → num). ∀j:num.",
				Hypotheses: []string{
					"j < n",
				},
				Conclusion: "kuhn_le(n, «lowered»(v, τ), «vertex»(v, τ, j))",
			}, func(arg *Argument, n *Expr[Nat], v, τ *Expr[Fun[Nat, Nat]], j *Expr[Nat], beforeEnd Fact) {
				arg.Do(Unfold(KuhnLeDef))
				arg.FixAs[Nat]("i")
				inRange := arg.Assuming(
					arg.Term("i < n"),
					"from n on both are v",
					Given(func(b *Argument, beyond Fact) {
						b.Show(
							"nothing is raised or lowered there",
							ByArith(beyond))
					}))
				arg.Cases(arg.Term("τ(i) = n - 1"))
				arg.When(
					"i is the coordinate of the last step, which the lowered "+
						"point lowers and vertex j, before n, does not raise",
					func(b *Argument, lastStep Fact) {
						b.Show(
							"vertex j is v(i), and the lowered point v(i) - 1, which is 0 where v(i) is 0",
							ByArith(inRange, lastStep, beforeEnd))
					})
				arg.Otherwise(
					"elsewhere the lowered point is v",
					func(b *Argument, elsewhere Fact) {
						b.Show(
							"vertex j is v(i) or v(i) + 1",
							ByArith(inRange, elsewhere))
					})
			})
			return ctx.Theorem(headline,
				func(arg *Argument, p, n *Expr[Nat], s *Expr[Set[Fun[Nat, Nat]]], a *Expr[Fun[Nat, Nat]], h Fact) {
					given := arg.Conjuncts(
						h,
						"n is positive",
						"s is a Kuhn simplex",
						"a is a vertex of s",
						"the face opposite a lies in no boundary plane")
					pos, simplex, aIn, interior := given[0], given[1], given[2], given[3]
					v, τ, presented := arg.Unpack2As[Fun[Nat, Nat], Fun[Nat, Nat]](
						GroupPremises(simplex, At(KuhnSimplexChain, p, n, s)), "v", "τ")
					chainParts := arg.Conjuncts(
						presented,
						"τ gives each coordinate below n a step below n",
						"τ is one-to-one below n",
						"s is the chain from v in the order τ")
					steps, oneToOne, chain := chainParts[0], chainParts[1], chainParts[2]
					zero := arg.TermAs[Nat]("0")
					onChain := arg.Have(
						"a is a vertex of the chain",
						"a ∈ {«vertex»(v, τ, j) | j:num | j ≤ n}",
						Derive(func(b *Argument) {
							b.Do(chain.RwRev())
							b.Show(
								"a lies in s",
								By(aIn))
						}))
					m, aAt := arg.UnpackAs[Nat](onChain, "m")
					aParts := arg.Conjuncts(
						aAt,
						"m is at most n",
						"a is vertex m")
					grid := arg.Conjuncts(
						arg.Unfolded(simplex, KuhnSimplexDef),
						"s lies in the grid",
						"s has n + 1 points",
						"any two points of s are comparable")[0]
					corners := arg.Have(
						"v is junk from n on and leaves room for one raise below n",
						"∀i:num. (¬(i < n) ⇒ v(i) = junk) ∧ (i < n ⇒ v(i) + 1 ≤ p)",
						Derive(func(b *Argument) {
							ends := b.Have(
								"vertices 0 and n are grid points",
								"«vertex»(v, τ, 0) ∈ kuhn_grid(p, n) ∧ «vertex»(v, τ, n) ∈ kuhn_grid(p, n)",
								Derive(func(c *Argument) {
									onS := c.Have(
										"vertices 0 and n are points of s",
										"«vertex»(v, τ, 0) ∈ s ∧ «vertex»(v, τ, n) ∈ s",
										Derive(func(d *Argument) {
											d.Do(chain.Rw())
											d.Show(
												"vertices 0 and n are on the chain",
												By(nat_order.ZeroLessEq.At(n), nat_order.LessEqRefl.At(n)))
										}))
									c.Show(
										"s lies in the grid",
										BySets(onS, grid))
								}))
							read := b.Conjuncts(
								ends,
								"vertex 0 is a grid point",
								"vertex n is a grid point")
							least := b.Unfolded(b.Unfolded(read[0], KuhnGridDef), carrier.TupleDef)
							greatest := b.Unfolded(read[1], KuhnGridDef)
							i := b.FixAs[Nat]("i")
							b.Show(
								"vertices 0 and n read at i",
								ByArith(least, greatest, steps.At(i)))
						}))
					arg.Cases(arg.Term("m = 0"))
					arg.When(
						"a is the least vertex: the other simplex is the chain one step on",
						func(b *Argument, atStart Fact) {
							lifted := b.TermAs[Fun[Nat, Nat]]("«lifted»(v, τ)")
							isLeast := b.Have(
								"a is vertex 0",
								"a = «vertex»(v, τ, 0)",
								By(Normalized, aParts[1], atStart))
							face := b.Have(
								"the face is the face opposite vertex 0",
								"delete(s, a) = delete(s, «vertex»(v, τ, 0))",
								By(isLeast))
							k, raisedFirst := b.ObtainAs[Nat](
								"some coordinate k is raised at the first step",
								"∃k:num. k < n ∧ τ(k) = 0",
								By(
									steps,
									pos,
									oneToOne,
									functions.InjectiveOnDef,
									num_segment.BelowStrictInjectiveOnto.At(n, τ, zero)))
							first := b.Conjuncts(
								raisedFirst,
								"k is a coordinate",
								"k is raised at the first step")
							room := b.Have(
								"the face leaves the plane x(k) = p, so v(k) + 2 ≤ p",
								"v(k) + 2 ≤ p",
								Derive(func(c *Argument) {
									leaves := c.Conjuncts(
										GroupPremises(first[0], interior.At(k)),
										"the face leaves x(k) = 0",
										"the face leaves x(k) = p")
									x, off := c.UnpackAs[Fun[Nat, Nat]](leaves[1], "x")
									offParts := c.Conjuncts(
										off,
										"x lies on the face",
										"x(k) is not p")
									onFace := c.Have(
										"x lies on the face opposite vertex 0",
										"x ∈ delete(s, «vertex»(v, τ, 0))",
										By(offParts[0], face))
									_, xAt := c.UnpackAs[Nat](
										GroupPremises(chain, onFace, At(KuhnChainFacePoints, n, v, τ, s, zero, x)), "j")
									xParts := c.Conjuncts(
										xAt,
										"j is at most n",
										"j is not 0",
										"x is vertex j")
									xk := c.Have(
										"x(k) is vertex j at k",
										"x(k) = «vertex»(v, τ, j, k)",
										By(Normalized, xParts[2]))
									c.Show(
										"x(k) = v(k) + 1 is below p",
										ByArith(xk, xParts[1], offParts[1], first[0], first[1], corners.At(k)))
								}))
							inGrid := b.Have(
								"the lifted point is a grid point",
								"«lifted»(v, τ) ∈ kuhn_grid(p, n)",
								Derive(func(c *Argument) {
									c.Do(Unfold(KuhnGridDef))
									c.Show(
										"junk from n on, at most p below n",
										By(
											c.Have(
												"the lifted point is junk from n on",
												"tuple(n, «lifted»(v, τ))",
												Derive(func(d *Argument) {
													d.Do(Unfold(carrier.TupleDef))
													i := d.FixAs[Nat]("i")
													d.Show(
														"it is v there",
														ByArith(corners.At(i)))
												})),
											c.Have(
												"the lifted point is at most p below n",
												"∀i:num. i < n ⇒ «lifted»(v, τ)(i) ≤ p",
												Derive(func(d *Argument) {
													i := d.FixAs[Nat]("i")
													inRange := d.Assume()
													d.Cases(d.Term("τ(i) = 0"))
													d.When(
														"at the first coordinate, v(k) + 2",
														func(e *Argument, firstStep Fact) {
															same := e.Have(
																"i is k",
																"i = k",
																ByArith(inRange, firstStep, first[0], first[1], oneToOne, functions.InjectiveOnDef))
															e.Show(
																"v(k) + 2 ≤ p",
																ByArith(same, room, inRange, firstStep, steps.At(i)))
														})
													d.Otherwise(
														"elsewhere, v(i) + 1",
														func(e *Argument, laterStep Fact) {
															e.Show(
																"v(i) + 1 ≤ p",
																ByArith(inRange, laterStep, steps.At(i), corners.At(i)))
														})
												}))))
								}))
							offS := b.Have(
								"the lifted point is not in s: at k it is v(k) + 2",
								"¬(«lifted»(v, τ) ∈ s)",
								Derive(func(c *Argument) {
									above := c.Have(
										"the lifted point is no vertex: at k it exceeds them all",
										"∀j:num. ¬(«lifted»(v, τ) = «vertex»(v, τ, j))",
										Derive(func(d *Argument) {
											d.FixAs[Nat]("j")
											atK := d.Have(
												"a vertex is at most v(k) + 1 at k",
												"¬(«lifted»(v, τ, k) = «vertex»(v, τ, j, k))",
												ByArith(first[0], first[1], steps.At(k)))
											d.Show(
												"the two differ at k",
												By(Normalized, atK))
										}))
									c.Do(chain.Rw())
									c.Show(
										"no vertex is the lifted point",
										By(above))
								}))
							comparable := b.Have(
								"the lifted point lies above every point of the face",
								"∀x:(num → num). x ∈ delete(s, a) ⇒ kuhn_le(n, x, «lifted»(v, τ)) ∨ kuhn_le(n, «lifted»(v, τ), x)",
								Derive(func(c *Argument) {
									x := c.FixAs[Fun[Nat, Nat]]("x")
									xIn := c.Assume()
									onFace := c.Have(
										"x lies on the face opposite vertex 0",
										"x ∈ delete(s, «vertex»(v, τ, 0))",
										By(xIn, face))
									j, xAt := c.UnpackAs[Nat](
										GroupPremises(chain, onFace, At(KuhnChainFacePoints, n, v, τ, s, zero, x)), "j")
									xParts := c.Conjuncts(
										xAt,
										"j is at most n",
										"j is not 0",
										"x is vertex j")
									c.Show(
										"comparable, x lying below the lifted point",
										ByArith(xParts[2], xParts[0], xParts[1], At(laterBelowLifted, n, v, τ, j)))
								}))
							unique := b.Have(
								"every apex of the face is a or the lifted point",
								Statement{
									Binders: "∀b:(num → num).",
									Hypotheses: []string{
										"b ∉ delete(s, a)",
										"kuhn_simplex(p, n, insert(b, delete(s, a)))",
									},
									Conclusion: "b = a ∨ b = «lifted»(v, τ)",
								},
								Derive(func(c *Argument) {
									other := c.FixAs[Fun[Nat, Nat]]("b")
									apex := c.Conjuncts(
										c.Assume(),
										"b is off the face",
										"the face with b is a Kuhn simplex")
									simplexAt := c.Have(
										"the face opposite vertex 0 with b is a Kuhn simplex",
										"kuhn_simplex(p, n, insert(b, delete(s, «vertex»(v, τ, 0))))",
										Derive(func(d *Argument) {
											d.Do(face.RwRev())
											d.Show(
												"the face with b is a Kuhn simplex, as assumed",
												By(apex[1]))
										}))
									c.Do(isLeast.Rw())
									c.Show(
										"the two apexes of the face opposite the least vertex",
										By(simplexAt, pos, steps, oneToOne, chain, At(KuhnApexOppositeLeast, p, n, v, τ, s, other)))
								}))
							b.Show(
								"two apexes, two simplices",
								By(
									simplex,
									aIn,
									offS,
									unique,
									At(twoApexes, p, n, s, a, lifted),
									b.Have(
										"the face with the lifted point is a Kuhn simplex",
										"kuhn_simplex(p, n, insert(«lifted»(v, τ), delete(s, a)))",
										By(simplex, aIn, inGrid, offS, comparable, At(KuhnSimplexReplace, p, n, s, a, lifted)))))
						})
					arg.Otherwise(
						"a is not the least vertex",
						func(b *Argument, notStart Fact) {
							b.Cases(b.Term("m = n"))
							b.When(
								"a is the greatest vertex: the other simplex is the chain one step back",
								func(c *Argument, atEnd Fact) {
									lowered := c.TermAs[Fun[Nat, Nat]]("«lowered»(v, τ)")
									previous := c.TermAs[Nat]("n - 1")
									isGreatest := c.Have(
										"a is vertex n",
										"a = «vertex»(v, τ, n)",
										By(Normalized, aParts[1], atEnd))
									face := c.Have(
										"the face is the face opposite vertex n",
										"delete(s, a) = delete(s, «vertex»(v, τ, n))",
										By(isGreatest))
									lastStep := c.Have(
										"n - 1 is the last step below n",
										"n - 1 < n",
										ByArith(pos))
									k, raisedLast := c.ObtainAs[Nat](
										"some coordinate k is raised at the last step",
										"∃k:num. k < n ∧ τ(k) = n - 1",
										By(
											steps,
											lastStep,
											oneToOne,
											functions.InjectiveOnDef,
											num_segment.BelowStrictInjectiveOnto.At(n, τ, previous)))
									last := c.Conjuncts(
										raisedLast,
										"k is a coordinate",
										"k is raised at the last step")
									positive := c.Have(
										"the face leaves the plane x(k) = 0, so v(k) is positive",
										"1 ≤ v(k)",
										Derive(func(d *Argument) {
											leaves := d.Conjuncts(
												GroupPremises(last[0], interior.At(k)),
												"the face leaves x(k) = 0",
												"the face leaves x(k) = p")
											x, off := d.UnpackAs[Fun[Nat, Nat]](leaves[0], "x")
											offParts := d.Conjuncts(
												off,
												"x lies on the face",
												"x(k) is not 0")
											onFace := d.Have(
												"x lies on the face opposite vertex n",
												"x ∈ delete(s, «vertex»(v, τ, n))",
												By(offParts[0], face))
											_, xAt := d.UnpackAs[Nat](
												GroupPremises(chain, onFace, At(KuhnChainFacePoints, n, v, τ, s, n, x)), "j")
											xParts := d.Conjuncts(
												xAt,
												"j is at most n",
												"j is not n",
												"x is vertex j")
											xk := d.Have(
												"x(k) is vertex j at k",
												"x(k) = «vertex»(v, τ, j, k)",
												By(Normalized, xParts[2]))
											d.Show(
												"x(k) = v(k) is not 0",
												ByArith(xk, xParts[0], xParts[1], offParts[1], last[0], last[1]))
										}))
									inGrid := c.Have(
										"the lowered point is a grid point",
										"«lowered»(v, τ) ∈ kuhn_grid(p, n)",
										Derive(func(d *Argument) {
											d.Do(Unfold(KuhnGridDef))
											d.Show(
												"junk from n on, at most p below n",
												By(
													d.Have(
														"the lowered point is junk from n on",
														"tuple(n, «lowered»(v, τ))",
														Derive(func(e *Argument) {
															e.Do(Unfold(carrier.TupleDef))
															i := e.FixAs[Nat]("i")
															e.Show(
																"it is v there",
																ByArith(corners.At(i)))
														})),
													d.Have(
														"the lowered point is at most p below n",
														"∀i:num. i < n ⇒ «lowered»(v, τ)(i) ≤ p",
														Derive(func(e *Argument) {
															i := e.FixAs[Nat]("i")
															inRange := e.Assume()
															e.Cases(e.Term("τ(i) = n - 1"))
															e.When(
																"at the last coordinate, v(i) - 1",
																func(f *Argument, lastCoordinate Fact) {
																	f.Show(
																		"at most v(i)",
																		ByArith(inRange, lastCoordinate, corners.At(i)))
																})
															e.Otherwise(
																"elsewhere, v(i)",
																func(f *Argument, elsewhere Fact) {
																	f.Show(
																		"at most v(i)",
																		ByArith(inRange, elsewhere, corners.At(i)))
																})
														}))))
										}))
									offS := c.Have(
										"the lowered point is not in s: at k it is v(k) - 1",
										"¬(«lowered»(v, τ) ∈ s)",
										Derive(func(d *Argument) {
											below := d.Have(
												"the lowered point is no vertex: at k it lies below them all",
												"∀j:num. ¬(«lowered»(v, τ) = «vertex»(v, τ, j))",
												Derive(func(e *Argument) {
													e.FixAs[Nat]("j")
													atK := e.Have(
														"a vertex is at least v(k) at k",
														"¬(«lowered»(v, τ, k) = «vertex»(v, τ, j, k))",
														ByArith(positive, last[0], last[1]))
													e.Show(
														"the two differ at k",
														By(Normalized, atK))
												}))
											d.Do(chain.Rw())
											d.Show(
												"no vertex is the lowered point",
												By(below))
										}))
									comparable := c.Have(
										"the lowered point lies below every point of the face",
										Statement{
											Binders: "∀x:(num → num).",
											Hypotheses: []string{
												"x ∈ delete(s, a)",
											},
											Conclusion: "kuhn_le(n, x, «lowered»(v, τ)) ∨ kuhn_le(n, «lowered»(v, τ), x)",
										},
										Derive(func(d *Argument) {
											x := d.FixAs[Fun[Nat, Nat]]("x")
											xIn := d.Assume()
											onFace := d.Have(
												"x lies on the face opposite vertex n",
												"x ∈ delete(s, «vertex»(v, τ, n))",
												By(xIn, face))
											j, xAt := d.UnpackAs[Nat](
												GroupPremises(chain, onFace, At(KuhnChainFacePoints, n, v, τ, s, n, x)), "j")
											xParts := d.Conjuncts(
												xAt,
												"j is at most n",
												"j is not n",
												"x is vertex j")
											d.Show(
												"comparable, the lowered point lying below x",
												ByArith(xParts[2], xParts[0], xParts[1], At(loweredBelowEarlier, n, v, τ, j)))
										}))
									unique := c.Have(
										"every apex of the face is a or the lowered point",
										Statement{
											Binders: "∀b:(num → num).",
											Hypotheses: []string{
												"b ∉ delete(s, a)",
												"kuhn_simplex(p, n, insert(b, delete(s, a)))",
											},
											Conclusion: "b = a ∨ b = «lowered»(v, τ)",
										},
										Derive(func(d *Argument) {
											other := d.FixAs[Fun[Nat, Nat]]("b")
											apex := d.Conjuncts(
												d.Assume(),
												"b is off the face",
												"the face with b is a Kuhn simplex")
											simplexAt := d.Have(
												"the face opposite vertex n with b is a Kuhn simplex",
												"kuhn_simplex(p, n, insert(b, delete(s, «vertex»(v, τ, n))))",
												Derive(func(e *Argument) {
													e.Do(face.RwRev())
													e.Show(
														"the face with b is a Kuhn simplex, as assumed",
														By(apex[1]))
												}))
											d.Do(isGreatest.Rw())
											d.Show(
												"the two apexes of the face opposite the greatest vertex",
												By(simplexAt, pos, steps, oneToOne, chain, At(KuhnApexOppositeGreatest, p, n, v, τ, s, other)))
										}))
									c.Show(
										"two apexes, two simplices",
										By(
											simplex,
											aIn,
											offS,
											unique,
											At(twoApexes, p, n, s, a, lowered),
											c.Have(
												"the face with the lowered point is a Kuhn simplex",
												"kuhn_simplex(p, n, insert(«lowered»(v, τ), delete(s, a)))",
												By(simplex, aIn, inGrid, offS, comparable, At(KuhnSimplexReplace, p, n, s, a, lowered)))))
								})
							b.Otherwise(
								"a is an inner vertex: the other simplex exchanges the steps around it",
								func(c *Argument, notEnd Fact) {
									swapped := c.TermAs[Fun[Nat, Nat]]("«swapped»(v, τ, m)")
									face := c.Have(
										"the face is the face opposite vertex m",
										"delete(s, a) = delete(s, «vertex»(v, τ, m))",
										By(aParts[1]))
									before := c.TermAs[Nat]("m - 1")
									inner := c.Have(
										"m lies strictly between 0 and n",
										"0 < m ∧ m < n ∧ m - 1 < n",
										ByArith(notStart, notEnd, aParts[0]))
									innerParts := c.Conjuncts(
										inner,
										"m is positive",
										"m is below n",
										"m - 1 is below n")
									_, atBefore := c.ObtainAs[Nat](
										"some coordinate k₁ is raised at step m - 1",
										"∃k₁:num. k₁ < n ∧ τ(k₁) = m - 1",
										By(
											steps,
											innerParts[2],
											oneToOne,
											functions.InjectiveOnDef,
											num_segment.BelowStrictInjectiveOnto.At(n, τ, before)))
									_, atM := c.ObtainAs[Nat](
										"some coordinate k₂ is raised at step m",
										"∃k₂:num. k₂ < n ∧ τ(k₂) = m",
										By(
											steps,
											innerParts[1],
											oneToOne,
											functions.InjectiveOnDef,
											num_segment.BelowStrictInjectiveOnto.At(n, τ, m)))
									inGrid := c.Have(
										"the exchanged point is a grid point",
										"«swapped»(v, τ, m) ∈ kuhn_grid(p, n)",
										Derive(func(d *Argument) {
											d.Do(Unfold(KuhnGridDef))
											d.Show(
												"junk from n on, at most p below n",
												By(
													d.Have(
														"the exchanged point is junk from n on",
														"tuple(n, «swapped»(v, τ, m))",
														Derive(func(e *Argument) {
															e.Do(Unfold(carrier.TupleDef))
															i := e.FixAs[Nat]("i")
															e.Show(
																"it is v there",
																ByArith(corners.At(i)))
														})),
													d.Have(
														"the exchanged point is at most p below n",
														"∀i:num. i < n ⇒ «swapped»(v, τ, m)(i) ≤ p",
														Derive(func(e *Argument) {
															i := e.FixAs[Nat]("i")
															inRange := e.Assume()
															e.Cases(e.Term("τ(i) < m - 1 ∨ τ(i) = m"))
															e.When(
																"raised, v(i) + 1",
																func(f *Argument, raised Fact) {
																	f.Show(
																		"at most p",
																		ByArith(inRange, raised, corners.At(i)))
																})
															e.Otherwise(
																"not raised, v(i)",
																func(f *Argument, notRaised Fact) {
																	f.Show(
																		"at most p",
																		ByArith(inRange, notRaised, corners.At(i)))
																})
														}))))
										}))
									offS := c.Have(
										"the exchanged point is not in s: it raises k₂ but not k₁",
										"¬(«swapped»(v, τ, m) ∈ s)",
										Derive(func(d *Argument) {
											mismatch := d.Have(
												"the exchanged point is no vertex: no vertex raises k₂ without k₁",
												"∀j:num. ¬(«swapped»(v, τ, m) = «vertex»(v, τ, j))",
												Derive(func(e *Argument) {
													e.FixAs[Nat]("j")
													atBoth := e.Have(
														"vertex j raises k₁ by step m - 1 before k₂",
														"¬(«swapped»(v, τ, m, k₁) = «vertex»(v, τ, j, k₁) ∧ "+
															"    «swapped»(v, τ, m, k₂) = «vertex»(v, τ, j, k₂))",
														ByArith(atBefore, atM, innerParts[0]))
													e.Show(
														"the two differ at k₁ or at k₂",
														By(Normalized, atBoth))
												}))
											d.Do(chain.Rw())
											d.Show(
												"no vertex is the exchanged point",
												By(mismatch))
										}))
									comparable := c.Have(
										"the exchanged point is comparable with every point of the face",
										Statement{
											Binders: "∀x:(num → num).",
											Hypotheses: []string{
												"x ∈ delete(s, a)",
											},
											Conclusion: "kuhn_le(n, x, «swapped»(v, τ, m)) ∨ kuhn_le(n, «swapped»(v, τ, m), x)",
										},
										Derive(func(d *Argument) {
											x := d.FixAs[Fun[Nat, Nat]]("x")
											xIn := d.Assume()
											onFace := d.Have(
												"x lies on the face opposite vertex m",
												"x ∈ delete(s, «vertex»(v, τ, m))",
												By(xIn, face))
											j, xAt := d.UnpackAs[Nat](
												GroupPremises(chain, onFace, At(KuhnChainFacePoints, n, v, τ, s, m, x)), "j")
											xParts := d.Conjuncts(
												xAt,
												"j is at most n",
												"j is not m",
												"x is vertex j")
											d.Cases(d.Term("j < m"))
											d.When(
												"an earlier vertex lies below the exchanged point",
												func(e *Argument, earlier Fact) {
													e.Show(
														"comparable, x lying below the exchanged point",
														By(xParts[2], earlier, KuhnEarlierBelowExchanged.At(n, v, τ, j, m)))
												})
											d.Otherwise(
												"a later vertex lies above the exchanged point",
												func(e *Argument, notEarlier Fact) {
													e.Show(
														"comparable, the exchanged point lying below x",
														ByArith(xParts[2], notEarlier, xParts[1], KuhnExchangedBelowLater.At(n, v, τ, j, m)))
												})
										}))
									unique := c.Have(
										"every apex of the face is a or the exchanged point",
										Statement{
											Binders: "∀b:(num → num).",
											Hypotheses: []string{
												"b ∉ delete(s, a)",
												"kuhn_simplex(p, n, insert(b, delete(s, a)))",
											},
											Conclusion: "b = a ∨ b = «swapped»(v, τ, m)",
										},
										Derive(func(d *Argument) {
											other := d.FixAs[Fun[Nat, Nat]]("b")
											apex := d.Conjuncts(
												d.Assume(),
												"b is off the face",
												"the face with b is a Kuhn simplex")
											offAt := d.Have(
												"b is off the face opposite vertex m",
												"b ∉ delete(s, «vertex»(v, τ, m))",
												Derive(func(e *Argument) {
													e.Do(face.RwRev())
													e.Show(
														"b is off the face, as assumed",
														By(apex[0]))
												}))
											simplexAt := d.Have(
												"the face opposite vertex m with b is a Kuhn simplex",
												"kuhn_simplex(p, n, insert(b, delete(s, «vertex»(v, τ, m))))",
												Derive(func(e *Argument) {
													e.Do(face.RwRev())
													e.Show(
														"the face with b is a Kuhn simplex, as assumed",
														By(apex[1]))
												}))
											d.Do(aParts[1].Rw())
											d.Show(
												"the two apexes of the face opposite an inner vertex",
												By(
													offAt,
													simplexAt,
													innerParts[0],
													innerParts[1],
													steps,
													oneToOne,
													chain,
													At(KuhnApexOppositeInner, p, n, v, τ, s, m, other)))
										}))
									c.Show(
										"two apexes, two simplices",
										By(
											simplex,
											aIn,
											offS,
											unique,
											At(twoApexes, p, n, s, a, swapped),
											c.Have(
												"the face with the exchanged point is a Kuhn simplex",
												"kuhn_simplex(p, n, insert(«swapped»(v, τ, m), delete(s, a)))",
												By(simplex, aIn, inGrid, offS, comparable, At(KuhnSimplexReplace, p, n, s, a, swapped)))))
								})
						})
				})
		}),
})}
