// chain.go — the shape of one Kuhn simplex: the grid holds finitely many;
// each has a least and a greatest point, the greatest the least raised in
// every coordinate below n; and each is the chain between them, raising
// one coordinate at a time in an order of the coordinates. Along a chain
// the vertices rise in Kuhn's order, are distinct, and fill the face
// opposite any one of them, and a point between two consecutive vertices
// is one of them. The exchanged point «swapped»(v, τ, m), vertex m with
// the steps on either side of it exchanged, lies above the vertices
// before m and below those after.

package kuhn

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/cartesian/carrier"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// KuhnSimplicesFinite — the grid holds finitely many Kuhn simplices. A
// grid point maps the n coordinates into {0, …, p} and is junk past them,
// and there are finitely many such maps; a simplex is a set of grid
// points, so the simplices lie among the finitely many subsets of the
// grid.
var KuhnSimplicesFinite = kuhnSimplicesFiniteThm{family.Add(registry.ProofEntry{
	Name: "KuhnSimplicesFinite",
	Key:  "prop_a74285d23ef80966",
	Reading: "No hypothesis: the grid is finite whatever p and n, since tuple pins every " +
		"coordinate from n on to the one junk value; at n = 0 or p = 0 it is a single point.",
	Build: family.Theorem("∀p n:num. finite({s:set(num → num) | kuhn_simplex(p, n, s)})",
		func(a *Argument, p, n *Expr[Nat]) {
			maps := a.Have(
				"a grid point maps the coordinates below n into {0, …, p} and is junk past them",
				"kuhn_grid(p, n) ⊆ "+
					"{h:(num → num) | "+
					"    (∀x:num. x ∈ {i:num | i < n} ⇒ h(x) ∈ {k:num | k ≤ p}) ∧ "+
					"    (∀x:num. x ∉ {i:num | i < n} ⇒ h(x) = junk)}",
				BySets(KuhnGridDef, carrier.TupleDef))
			grid := a.TermAs[Set[Fun[Nat, Nat]]]("kuhn_grid(p, n)")
			finiteGrid := a.Have(
				"so the grid is finite, such maps between finite sets being finitely many",
				"finite(kuhn_grid(p, n))",
				By(
					maps,
					num_segment.FiniteBelowStrict.At(n),
					num_segment.FiniteBelow.At(p),
					cardinality.FiniteFunspace.At(
						a.TermAs[Set[Nat]]("{i:num | i < n}"),
						a.TermAs[Set[Nat]]("{k:num | k ≤ p}"),
						a.TermAs[Nat]("junk")),
					finite_set.FiniteSubset))
			inGrid := a.Have(
				"a simplex is a set of grid points",
				"∀s:set(num → num). kuhn_simplex(p, n, s) ⇒ s ⊆ kuhn_grid(p, n)",
				By(KuhnSimplexDef))
			simplices := a.TermAs[Set[Set[Fun[Nat, Nat]]]]("{s:set(num → num) | kuhn_simplex(p, n, s)}")
			subsets := a.TermAs[Set[Set[Fun[Nat, Nat]]]]("{t:set(num → num) | t ⊆ kuhn_grid(p, n)}")
			inPowerset := a.Have(
				"so the simplices lie among the subsets of the grid",
				"{s:set(num → num) | kuhn_simplex(p, n, s)} ⊆ {t:set(num → num) | t ⊆ kuhn_grid(p, n)}",
				BySets(inGrid))
			a.Show(
				"and a finite set has finitely many subsets",
				By(
					finiteGrid,
					inPowerset,
					finite_set.FinitePowerset.At(grid),
					finite_set.FiniteSubset.At(simplices, subsets)))
		}),
})}

// KuhnSimplexExtrema — a Kuhn simplex has a least and a greatest point,
// and the greatest is the least raised by one in each of the n
// coordinates. A point a of the finite set s with no point of s strictly
// below it coordinatewise is least, since every point is comparable with
// it. Each point exceeds a by one in some of the first n coordinates, and
// those coordinates determine it; along kuhn_le they only grow, so two
// points of s exceeding a in equally many coordinates coincide. The n + 1
// counts are then n + 1 distinct values in 0, …, n, all of them, and the
// point b whose count is n is a raised everywhere, above every point of s.
var KuhnSimplexExtrema = kuhnSimplexExtremaThm{family.Add(registry.ProofEntry{
	Name: "KuhnSimplexExtrema",
	Key:  "prop_3eeab0f50745a270",
	Reading: "Pairwise comparability carries it: with antisymmetry it makes " +
		"kuhn_le transitive on s, which kuhn_le is not in general. At n = 0 the " +
		"simplex is a singleton and a = b; at p = 0 and n > 0 there is no simplex.",
	Build: family.Theorem(Statement{
		Binders: "∀p n:num. ∀s:set(num → num).",
		Hypotheses: []string{
			"kuhn_simplex(p, n, s)",
		},
		Conclusion: "∃a b:(num → num). " +
			"    a ∈ s ∧ " +
			"    b ∈ s ∧ " +
			"    (∀x:(num → num). x ∈ s ⇒ kuhn_le(n, a, x) ∧ kuhn_le(n, x, b)) ∧ " +
			"    ∀i:num. i < n ⇒ b(i) = a(i) + 1",
		Abbrev: Abbrev{
			{Name: "above", Text: "λx:(num → num). λy:(num → num). " +
				"    (∀i:num. y(i) ≤ x(i)) ∧ ¬(∀i:num. x(i) ≤ y(i))"},
		},
	}, func(arg *Argument, _, n *Expr[Nat], s *Expr[Set[Fun[Nat, Nat]]], simplex Fact) {
		parts := arg.Conjuncts(
			arg.Unfolded(simplex, KuhnSimplexDef),
			"s lies in the grid",
			"s has n + 1 points",
			"any two points of s are comparable")
		size, comparable := parts[1], parts[2]
		occupied := arg.Have(
			"s has n + 1 points, so it is finite and not empty",
			"finite(s) ∧ s ≠ ∅",
			ByArith(size, cardinality.HasSizeZero.At(s), cardinality.HasSizeDef))
		steps := arg.Have(
			"along kuhn_le each coordinate rises by at most one",
			"∀x y:(num → num). kuhn_le(n, x, y) ⇒ ∀i:num. x(i) ≤ y(i) ∧ y(i) ≤ x(i) + 1",
			Derive(func(c *Argument) {
				x := c.FixAs[Fun[Nat, Nat]]("x")
				y := c.FixAs[Fun[Nat, Nat]]("y")
				xy := c.Assume()
				c.Show(
					"below n by the definition, and from n on not at all",
					ByArith(xy, KuhnLeDef.At(n, x, y)))
			}))

		// The least point: a point with nothing of s strictly below it,
		// which a finite set has since lying strictly above is a strict
		// order on num → num.
		irreflexive := arg.Have(
			"no point lies strictly above itself",
			"∀x:(num → num). ¬«above»(x, x)",
			By(nat_order.LessEqRefl))
		transitive := arg.Have(
			"lying strictly above is transitive",
			"∀x y z:(num → num). «above»(x, y) ∧ «above»(y, z) ⇒ «above»(x, z)",
			By(nat_order.LessEqTrans))
		above := arg.TermAs[Fun2[Fun[Nat, Nat], Fun[Nat, Nat], Bool]]("«above»")
		a, minimal := arg.ObtainAs[Fun[Nat, Nat]](
			"some point a of s lies strictly above no point of s",
			"∃a:(num → num). a ∈ s ∧ ∀y:(num → num). y ∈ s ⇒ ¬«above»(a, y)",
			Derive(func(c *Argument) {
				none := c.SupposeNot()
				descent := c.Have(
					"otherwise every point of s lies strictly above another point of s",
					"∀x:(num → num). x ∈ s ⇒ ∃y:(num → num). y ∈ s ∧ «above»(x, y)",
					By(Normalized, none))
				c.Show(
					"and a finite set along which a strict order descends forever is empty",
					By(irreflexive, transitive, descent, occupied, finite_set.FiniteTransitivityChain.At(above, s)))
			}))
		bottom := arg.Conjuncts(
			minimal,
			"a lies in s",
			"no point of s lies strictly below a")
		aIn := bottom[0]
		least := arg.Have(
			"a lies below every point of s",
			"∀x:(num → num). x ∈ s ⇒ kuhn_le(n, a, x)",
			Derive(func(c *Argument) {
				x := c.FixAs[Fun[Nat, Nat]]("x")
				xIn := c.Assume()
				underA := c.Assuming(
					c.Term("kuhn_le(n, x, a)"),
					"unless x lies below a, comparability puts a below x",
					Given(func(d *Argument, notBelow Fact) {
						d.Show(
							"a lies below x",
							By(notBelow, comparable.At(a, x), aIn, xIn))
					}))
				up := c.Have(
					"x lies below a coordinatewise and not strictly, so a lies below x coordinatewise",
					"∀i:num. a(i) ≤ x(i)",
					By(steps.At(x, a), bottom[1].At(x), xIn, underA))
				c.Show(
					"so x and a agree, and a lies below x",
					Simp(Fwd(KuhnLeDef)),
					ByArith(up, steps.At(x, a), underA))
			}))

		// A point of s is a raised by one in the coordinates «raised»(a, x)
		// and agrees with a elsewhere, so those coordinates determine it.
		beyond := arg.Have(
			"a point of s exceeds a only in coordinates below n",
			"∀x:(num → num). ∀i:num. x ∈ s ∧ a(i) < x(i) ⇒ i < n",
			Derive(func(c *Argument) {
				x := c.FixAs[Fun[Nat, Nat]]("x")
				c.FixAs[Nat]("i")
				exceeds := c.Assume()
				c.Show(
					"from n on, x agrees with a",
					ByArith(exceeds, least.At(x), KuhnLeDef.At(n, a, x)))
			}))
		inside := arg.Have(
			"only coordinates below n are raised",
			"∀x:(num → num). «raised»(a, x) ⊆ {i:num | i < n}",
			BySets())
		determined := arg.Have(
			"a point of s is determined by the coordinates in which it exceeds a",
			"∀x y:(num → num). x ∈ s ∧ y ∈ s ∧ «raised»(a, x) = «raised»(a, y) ⇒ x = y",
			Derive(func(c *Argument) {
				x := c.FixAs[Fun[Nat, Nat]]("x")
				y := c.FixAs[Fun[Nat, Nat]]("y")
				given := c.Conjuncts(
					c.Assume(),
					"x lies in s",
					"y lies in s",
					"x and y exceed a in the same coordinates")
				xIn, yIn, same := given[0], given[1], given[2]
				agree := c.Have(
					"x and y agree in every coordinate",
					"∀i:num. x(i) = y(i)",
					Derive(func(d *Argument) {
						i := d.FixAs[Nat]("i")
						together := d.Have(
							"x exceeds a at i exactly when y does: below n their raised sets agree, from n on neither does",
							"a(i) < x(i) ⇔ a(i) < y(i)",
							BySets(same, beyond.At(x, i), beyond.At(y, i), xIn, yIn))
						d.Cases(d.Term("a(i) < x(i)"))
						d.When(
							"both exceed a(i), by at most one: both are a(i) + 1",
							func(e *Argument, raisedAt Fact) {
								e.Show(
									"so x and y agree at i",
									ByArith(
										raisedAt,
										together,
										xIn,
										yIn,
										least.At(x),
										least.At(y),
										steps.At(a, x, i),
										steps.At(a, y, i)))
							})
						d.Otherwise(
							"neither exceeds a(i): both are a(i)",
							func(e *Argument, flatAt Fact) {
								e.Show(
									"so x and y agree at i",
									ByArith(flatAt, together, xIn, yIn, least.At(x), least.At(y), steps.At(a, x, i), steps.At(a, y, i)))
							})
					}))
				c.Show(
					"so x = y",
					By(Normalized, agree))
			}))

		// The count of those coordinates tells the points of s apart.
		grows := arg.Have(
			"moving up along kuhn_le, a point keeps every coordinate in which it exceeds a",
			"∀x y:(num → num). kuhn_le(n, x, y) ⇒ «raised»(a, x) ⊆ «raised»(a, y)",
			Derive(func(c *Argument) {
				x := c.FixAs[Fun[Nat, Nat]]("x")
				y := c.FixAs[Fun[Nat, Nat]]("y")
				xy := c.Assume()
				c.Show(
					"a(i) < x(i) ≤ y(i)",
					BySets(steps.At(x, y), xy, nat_order.LessThanLessEqTrans))
			}))
		below := arg.TermAs[Set[Nat]]("{i:num | i < n}")
		bounded := arg.Have(
			"a point of s exceeds a in at most n coordinates",
			"∀x:(num → num). x ∈ s ⇒ finite(«raised»(a, x)) ∧ card(«raised»(a, x)) ≤ n",
			Derive(func(c *Argument) {
				x := c.FixAs[Fun[Nat, Nat]]("x")
				xIn := c.Assume()
				raisedX := c.TermAs[Set[Nat]]("«raised»(a, x)")
				c.Show(
					"those coordinates lie among the n below n",
					By(
						xIn,
						inside.At(x),
						num_segment.HasSizeBelowStrict.At(n),
						cardinality.HasSizeDef.At(below, n),
						finite_set.FiniteSubset.At(raisedX, below),
						cardinality.CardSubset.At(raisedX, below)))
			}))
		counts := arg.Have(
			"points of s exceeding a in equally many coordinates coincide",
			"injective_on(s, λx:(num → num). card(«raised»(a, x)))",
			Simp(Fwd(functions.InjectiveOnDef)),
			Derive(func(c *Argument) {
				x := c.FixAs[Fun[Nat, Nat]]("x")
				y := c.FixAs[Fun[Nat, Nat]]("y")
				given := c.Conjuncts(
					c.Assume(),
					"x lies in s",
					"y lies in s",
					"x and y exceed a in equally many coordinates")
				xIn, yIn, sameCount := given[0], given[1], given[2]
				raisedX := c.TermAs[Set[Nat]]("«raised»(a, x)")
				raisedY := c.TermAs[Set[Nat]]("«raised»(a, y)")
				same := c.Have(
					"x and y exceed a in the same coordinates",
					"«raised»(a, x) = «raised»(a, y)",
					Derive(func(d *Argument) {
						d.Cases(d.Term("kuhn_le(n, x, y)"))
						d.When(
							"x below y: the coordinates of x are among those of y, and as many",
							func(e *Argument, xy Fact) {
								e.Show(
									"so the two sets are one",
									By(
										sameCount,
										xy,
										grows.At(x, y),
										yIn,
										bounded.At(y),
										cardinality.CardSubsetEq.At(raisedX, raisedY)))
							})
						d.Otherwise(
							"y below x, as any two points of s are comparable: the same the other way round",
							func(e *Argument, notXY Fact) {
								e.Show(
									"so the two sets are one",
									By(
										notXY,
										sameCount,
										comparable.At(x, y),
										xIn,
										yIn,
										grows.At(y, x),
										bounded.At(x),
										cardinality.CardSubsetEq.At(raisedY, raisedX)))
							})
					}))
				c.Show(
					"so x = y",
					By(determined.At(x, y), same, xIn, yIn))
			}))

		// The n + 1 counts fill 0, …, n; the point whose count is n is b.
		values := arg.TermAs[Set[Nat]]("{k:num | k ≤ n}")
		count := arg.TermAs[Fun[Fun[Nat, Nat], Nat]]("λx:(num → num). card(«raised»(a, x))")
		within := arg.Have(
			"every count is at most n",
			"image(λx:(num → num). card(«raised»(a, x)), s) ⊆ {k:num | k ≤ n}",
			By(bounded, set_image.ImageSubsetIff.At(count, s, values)))
		points := arg.TermAs[Nat]("n + 1")
		matched := arg.Have(
			"s has as many points as there are counts 0, …, n",
			"card(s) = card({k:num | k ≤ n})",
			By(
				size,
				num_segment.HasSizeBelow.At(n),
				cardinality.CardOfSized.At(s, points),
				cardinality.CardOfSized.At(values, points)))
		b, top := arg.ObtainAs[Fun[Nat, Nat]](
			"one-to-one from s into 0, …, n, the count is onto: some point b of s exceeds a in n coordinates",
			"∃b:(num → num). b ∈ s ∧ card(«raised»(a, b)) = n",
			By(
				occupied,
				matched,
				within,
				counts,
				num_segment.FiniteBelow.At(n),
				cardinality.SurjectiveIffInjectiveGen.At(s, values, count),
				nat_order.LessEqRefl.At(n)))
		topParts := arg.Conjuncts(
			top,
			"b lies in s",
			"b exceeds a in n coordinates")
		bIn := topParts[0]
		raisedB := arg.TermAs[Set[Nat]]("«raised»(a, b)")
		full := arg.Have(
			"n coordinates below n are all of them: b exceeds a in every coordinate below n",
			"«raised»(a, b) = {i:num | i < n}",
			By(
				topParts[1],
				bIn,
				inside.At(b),
				num_segment.HasSizeBelowStrict.At(n),
				cardinality.HasSizeDef.At(below, n),
				cardinality.SubsetEqIffSameCount.At(raisedB, below)))
		coords := arg.Have(
			"b is a raised by one in each of the n coordinates",
			"∀i:num. i < n ⇒ b(i) = a(i) + 1",
			Derive(func(c *Argument) {
				i := c.FixAs[Nat]("i")
				iBelow := c.Assume()
				exceeds := c.Have(
					"b exceeds a at i",
					"a(i) < b(i)",
					BySets(iBelow, full))
				c.Show(
					"and by at most one",
					ByArith(exceeds, bIn, least.At(b), steps.At(a, b, i)))
			}))
		greatest := arg.Have(
			"every point of s lies below b",
			"∀x:(num → num). x ∈ s ⇒ kuhn_le(n, x, b)",
			Derive(func(c *Argument) {
				x := c.FixAs[Fun[Nat, Nat]]("x")
				xIn := c.Assume()
				c.Show(
					"x lies between a and a raised everywhere, which is b",
					Simp(Fwd(KuhnLeDef)),
					ByArith(coords, bIn, xIn, least.At(x), least.At(b), KuhnLeDef.At(n, a, x), KuhnLeDef.At(n, a, b)))
			}))
		arg.Take(a)
		arg.Take(b)
		arg.Show(
			"a and b are the least and the greatest point of s",
			By(least, greatest, coords, aIn, bIn))
	}),
})}

// KuhnSimplexChain — a Kuhn simplex is the chain from its least point v to
// v raised in every coordinate below n, raising one coordinate at each step:
// coordinate i is raised at step τ(i), for an order τ of the coordinates
// below n, and the points are «vertex»(v, τ, j) for j ≤ n. The proof reads
// each point through the coordinates it raises above v. Comparable points
// raise nested sets, so a point is fixed by how many it raises; n + 1 points
// with counts in 0, …, n take every count once, and τ(i) is the count at
// which coordinate i switches on.
var KuhnSimplexChain = kuhnSimplexChainThm{family.Add(registry.ProofEntry{
	Name: "KuhnSimplexChain",
	Key:  "prop_70cac8bbe12305a8",
	Build: family.Sections(Statement{
		Binders: "∀p n:num. ∀s:set(num → num).",
		Hypotheses: []string{
			"kuhn_simplex(p, n, s)",
		},
		Conclusion: "∃v τ:(num → num). " +
			"    (∀i:num. i < n ⇒ τ(i) < n) ∧ " +
			"    injective_on({i:num | i < n}, τ) ∧ " +
			"    s = {«vertex»(v, τ, j) | j:num | j ≤ n}",
	},
		func(ctx *Script, headline string) *GoalStackNode {
			switchesOn := ctx.Lemma(Statement{
				Binders: "∀P:(num → bool). ∀n:num.",
				Hypotheses: []string{
					"¬P(0)",
					"P(n)",
				},
				Conclusion: "∃k:num. k < n ∧ ¬P(k) ∧ P(k + 1)",
			}, func(a *Argument, P *Expr[Set[Nat]]) {
				a.Induct("n")
				a.Base(
					"no property is both false and true at 0",
					func(b *Argument) {
						both := b.Assume()
						b.Show(
							"the hypotheses contradict",
							By(both))
					})
				a.Step(
					"the switch below n stays below suc(n), or else it is at n itself",
					func(b *Argument, below Fact) {
						ends := b.Assume()
						b.Cases(b.Term("P(n)"))
						b.When(
							"P already holds at n, so it switches on below n",
							func(c *Argument, atN Fact) {
								c.Show(
									"a step below n is below suc(n)",
									By(atN, below, ends, nat_order.LessThanSucClause))
							})
						b.Otherwise(
							"P fails at n and holds at suc(n), so it switches on at n",
							func(c *Argument, notAtN Fact) {
								c.Take(c.Term("n"))
								c.Show(
									"n is below suc(n)",
									By(Normalized, notAtN, ends, nat_arith.Add1, nat_order.LessThanSucClause))
							})
					})
			})
			return ctx.Theorem(headline,
				func(a *Argument, p, n *Expr[Nat], s *Expr[Set[Fun[Nat, Nat]]], simplex Fact) {
					v, _, extremes := a.Unpack2As[Fun[Nat, Nat], Fun[Nat, Nat]](
						GroupPremises(simplex, KuhnSimplexExtrema.At(p, n, s)), "v", "w")
					least := a.Conjuncts(
						extremes,
						"v lies in s",
						"w lies in s",
						"every point lies between v and w",
						"w is v raised in every coordinate below n")
					parts := a.Conjuncts(
						a.Unfolded(simplex, KuhnSimplexDef),
						"s lies in the grid",
						"s has n + 1 points",
						"any two points of s are comparable")
					size, comparable := parts[1], parts[2]
					between := a.Have(
						"a point of s is v raised by at most one below n and v from n on",
						"∀x:(num → num). x ∈ s ⇒ ∀i:num. (i < n ⇒ v(i) ≤ x(i) ∧ x(i) ≤ v(i) + 1) ∧ (n ≤ i ⇒ x(i) = v(i))",
						Derive(func(b *Argument) {
							x := b.FixAs[Fun[Nat, Nat]]("x")
							b.Show(
								"kuhn_le(n, v, x), read coordinate by coordinate",
								By(least[2].At(x), KuhnLeDef.At(n, v, x)))
						}))
					reading := a.Have(
						"a point of s is v raised by one exactly on its raised coordinates",
						Statement{
							Binders: "∀x:(num → num).",
							Hypotheses: []string{
								"x ∈ s",
							},
							Conclusion: "∀i:num. (i ∈ «raised»(v, x) ⇒ x(i) = v(i) + 1) ∧ (i ∉ «raised»(v, x) ⇒ x(i) = v(i))",
						},
						Derive(func(b *Argument) {
							x := b.FixAs[Fun[Nat, Nat]]("x")
							in := b.Assume()
							i := b.FixAs[Nat]("i")
							b.Show(
								"x(i) is v(i) or v(i) + 1",
								ByArith(in, between.At(x, i)))
						}))
					monotone := a.Have(
						"raising a point of s keeps every raised coordinate raised",
						"∀x y:(num → num). x ∈ s ∧ kuhn_le(n, x, y) ⇒ «raised»(v, x) ⊆ «raised»(v, y)",
						Derive(func(b *Argument) {
							x := b.FixAs[Fun[Nat, Nat]]("x")
							b.FixAs[Fun[Nat, Nat]]("y")
							given := b.Conjuncts(
								b.Assume(),
								"x lies in s",
								"y is x raised")
							raise := b.Unfolded(given[1], KuhnLeDef)
							b.Do(Unfold(set_basic.SubsetDef))
							i := b.FixAs[Nat]("i")
							raisedAtX := b.Assume()
							b.Show(
								"y(i) is at least x(i), which is above v(i)",
								ByArith(raisedAtX, raise.At(i), between.At(x, i), given[0]))
						}))
					below := a.TermAs[Set[Nat]]("{i:num | i < n}")
					bounded := a.Have(
						"the raised coordinates of any point are finitely many, at most n",
						"∀x:(num → num). finite(«raised»(v, x)) ∧ card(«raised»(v, x)) ≤ n",
						Derive(func(b *Argument) {
							b.FixAs[Fun[Nat, Nat]]("x")
							raisedX := b.TermAs[Set[Nat]]("«raised»(v, x)")
							inside := b.Have(
								"only coordinates below n are raised",
								"«raised»(v, x) ⊆ {i:num | i < n}",
								BySets())
							b.Show(
								"a subset of the n coordinates below n",
								By(
									inside,
									cardinality.BoundedCountOfSubset.At(raisedX, below, n),
									num_segment.HasSizeBelowStrict.At(n),
									cardinality.HasSizeDef,
									nat_order.LessEqRefl))
						}))
					determined := a.Have(
						"a point of s is determined by its raised coordinates",
						"∀x y:(num → num). x ∈ s ∧ y ∈ s ∧ «raised»(v, x) = «raised»(v, y) ⇒ x = y",
						Derive(func(b *Argument) {
							x := b.FixAs[Fun[Nat, Nat]]("x")
							y := b.FixAs[Fun[Nat, Nat]]("y")
							same := b.Assume()
							b.Do(Funext())
							i := b.FixAs[Nat]("i")
							b.Show(
								"both read the same raise at i",
								BySets(same, reading.At(x, i), reading.At(y, i)))
						}))
					orderedLevels := a.Have(
						"of two comparable points of s raising equally many coordinates, the lower is the higher",
						Statement{
							Binders: "∀x y:(num → num).",
							Hypotheses: []string{
								"x ∈ s",
								"y ∈ s",
								"kuhn_le(n, x, y)",
								"card(«raised»(v, x)) = card(«raised»(v, y))",
							},
							Conclusion: "x = y",
						},
						Derive(func(b *Argument) {
							b.FixAs[Fun[Nat, Nat]]("x")
							b.FixAs[Fun[Nat, Nat]]("y")
							given := b.Conjuncts(
								b.Assume(),
								"x lies in s",
								"y lies in s",
								"y is x raised",
								"they count alike")
							same := b.Have(
								"a raised set inside another of the same count is that set",
								"«raised»(v, x) = «raised»(v, y)",
								By(given[3], given[0], given[2], monotone, bounded, cardinality.CardSubsetEq))
							b.Show(
								"the raised set fixes the point",
								By(same, given[0], given[1], determined))
						}))
					levelsSeparate := a.Have(
						"two points of s raising equally many coordinates are equal",
						"∀x y:(num → num). x ∈ s ∧ y ∈ s ∧ card(«raised»(v, x)) = card(«raised»(v, y)) ⇒ x = y",
						Derive(func(b *Argument) {
							x := b.FixAs[Fun[Nat, Nat]]("x")
							y := b.FixAs[Fun[Nat, Nat]]("y")
							given := b.Assume()
							b.Show(
								"one of the two lies below the other",
								By(given, comparable.At(x, y), orderedLevels.At(x, y), orderedLevels.At(y, x)))
						}))
					level := a.TermAs[Fun[Fun[Nat, Nat], Nat]]("λx:(num → num). card(«raised»(v, x))")
					upToN := a.TermAs[Set[Nat]]("{j:num | j ≤ n}")
					oneToOne := a.Have(
						"the level, the number of raised coordinates, is one-to-one on s",
						"injective_on(s, λx:(num → num). card(«raised»(v, x)))",
						By(levelsSeparate, functions.InjectiveOnDef))
					levels := a.Have(
						"every level lies in 0, …, n",
						"image(λx:(num → num). card(«raised»(v, x)), s) ⊆ {j:num | j ≤ n}",
						By(bounded, set_image.ImageSubsetIff))
					counts := a.Have(
						"s and 0, …, n both have n + 1 elements",
						"finite(s) ∧ finite({j:num | j ≤ n}) ∧ card(s) = card({j:num | j ≤ n})",
						By(
							size,
							num_segment.HasSizeBelow.At(n),
							cardinality.CardOfSized.At(s, a.TermAs[Nat]("n + 1")),
							cardinality.CardOfSized.At(upToN, a.TermAs[Nat]("n + 1")),
							num_segment.FiniteBelow.At(n),
							cardinality.HasSizeDef.At(s, a.TermAs[Nat]("n + 1"))))
					occupied := a.Have(
						"so every level 0, …, n is taken by a point of s",
						"∀j:num. j ≤ n ⇒ ∃x:(num → num). x ∈ s ∧ card(«raised»(v, x)) = j",
						By(oneToOne, levels, counts, cardinality.SurjectiveIffInjectiveGen.At(s, upToN, level)))
					_, chosen := a.ObtainAs[Fun[Nat, Fun[Nat, Nat]]](
						"choose the point X(j) of level j",
						"∃X:(num → num → num). ∀j:num. j ≤ n ⇒ X(j) ∈ s ∧ card(«raised»(v, X(j))) = j",
						By(occupied))
					grows := a.Have(
						"the raised set grows with the level",
						"∀j l:num. j ≤ l ∧ l ≤ n ⇒ «raised»(v, X(j)) ⊆ «raised»(v, X(l))",
						Derive(func(b *Argument) {
							j := b.FixAs[Nat]("j")
							l := b.FixAs[Nat]("l")
							order := b.Assume()
							points := b.Conjuncts(
								b.Have(
									"X(j) and X(l) are the chosen points of levels j and l",
									"(X(j) ∈ s ∧ card(«raised»(v, X(j))) = j) ∧ X(l) ∈ s ∧ card(«raised»(v, X(l))) = l",
									ByArith(order, chosen.At(j), chosen.At(l))),
								"X(j) lies in s",
								"X(j) has level j",
								"X(l) lies in s",
								"X(l) has level l")
							lower := b.TermAs[Fun[Nat, Nat]]("X(j)")
							upper := b.TermAs[Fun[Nat, Nat]]("X(l)")
							b.Cases(b.Term("kuhn_le(n, X(j), X(l))"))
							b.When(
								"X(j) lies below X(l)",
								func(c *Argument, up Fact) {
									c.Show(
										"raising keeps the raised coordinates",
										By(up, points[0], monotone))
								})
							b.Otherwise(
								"X(l) lies below X(j), and then the two raise the same coordinates",
								func(c *Argument, notUp Fact) {
									down := c.Have(
										"X(l) lies below X(j)",
										"kuhn_le(n, X(l), X(j))",
										By(notUp, points[0], points[2], comparable.At(lower, upper)))
									fewer := c.Have(
										"X(j) raises no more coordinates than X(l)",
										"card(«raised»(v, X(j))) ≤ card(«raised»(v, X(l)))",
										ByArith(points[1], points[3], order))
									equal := c.Have(
										"a raised set inside another with no fewer elements is that set",
										"«raised»(v, X(l)) = «raised»(v, X(j))",
										By(fewer, points[2], down, monotone, bounded, cardinality.CardSubsetLe))
									c.Show(
										"equal sets lie inside each other",
										By(equal, set_order.SubsetRefl))
								})
						}))
					zero := a.TermAs[Nat]("0")
					atZero := a.Have(
						"level 0 raises nothing",
						"«raised»(v, X(0)) = ∅",
						By(
							chosen.At(zero),
							bounded.At(a.TermAs[Fun[Nat, Nat]]("X(0)")),
							cardinality.CardEqZero.At(a.TermAs[Set[Nat]]("«raised»(v, X(0))")),
							nat_order.ZeroLessEq.At(n)))
					insideAtN := a.Have(
						"level n raises only coordinates below n",
						"«raised»(v, X(n)) ⊆ {i:num | i < n}",
						BySets())
					atN := a.Have(
						"level n raises every coordinate below n",
						"«raised»(v, X(n)) = {i:num | i < n}",
						By(
							insideAtN,
							chosen.At(n),
							cardinality.CardSubsetEq.At(a.TermAs[Set[Nat]]("«raised»(v, X(n))"), below),
							nat_order.LessEqRefl.At(n),
							num_segment.FiniteBelowStrict.At(n),
							cardinality.CardOfSized.At(below, n),
							num_segment.HasSizeBelowStrict.At(n)))
					switches := a.Have(
						"each coordinate below n switches on at some step below n",
						"∀i:num. i < n ⇒ ∃k:num. k < n ∧ i ∉ «raised»(v, X(k)) ∧ i ∈ «raised»(v, X(k + 1))",
						Derive(func(b *Argument) {
							b.FixAs[Nat]("i")
							inRange := b.Assume()
							ends := b.Have(
								"i is off at level 0 and on at level n",
								"i ∉ «raised»(v, X(0)) ∧ i ∈ «raised»(v, X(n))",
								BySets(inRange, atZero, atN))
							b.Show(
								"a property off at 0 and on at n switches on at a step below n",
								By(ends, At(switchesOn, b.Term("λk:num. i ∈ «raised»(v, X(k))"), n)))
						}))
					tau, steps := a.ObtainAs[Fun[Nat, Nat]](
						"τ(i) is the step at which coordinate i switches on",
						"∃τ:(num → num). ∀i:num. "+
							"    i < n ⇒ τ(i) < n ∧ i ∉ «raised»(v, X(τ(i))) ∧ i ∈ «raised»(v, X(τ(i) + 1))",
						By(switches))
					raisedAt := a.Have(
						"coordinate i is raised at level j exactly when its step comes before j",
						"∀i j:num. i < n ∧ j ≤ n ⇒ (i ∈ «raised»(v, X(j)) ⇔ τ(i) < j)",
						Derive(func(b *Argument) {
							i := b.FixAs[Nat]("i")
							j := b.FixAs[Nat]("j")
							ranges := b.Assume()
							step := b.TermAs[Nat]("τ(i)")
							b.Cases(b.Term("τ(i) < j"))
							b.When(
								"the step comes before j",
								func(c *Argument, before Fact) {
									bounds := c.Have(
										"τ(i) + 1 ≤ j ≤ n",
										"τ(i) + 1 ≤ j ∧ j ≤ n",
										ByArith(before, ranges))
									c.Show(
										"i is on from level τ(i) + 1 on",
										BySets(before, ranges, bounds, grows.At(c.TermAs[Nat]("τ(i) + 1"), j), steps.At(i)))
								})
							b.Otherwise(
								"the step comes at j or later",
								func(c *Argument, notBefore Fact) {
									bounds := c.Have(
										"j ≤ τ(i) ≤ n",
										"j ≤ τ(i) ∧ τ(i) ≤ n",
										ByArith(notBefore, ranges, steps.At(i)))
									c.Show(
										"i is still off up to level τ(i)",
										BySets(notBefore, bounds, grows.At(j, step), steps.At(i)))
								})
						}))
					vertices := a.Have(
						"the chosen points are the vertices of the chain from v in the order τ",
						"∀j:num. j ≤ n ⇒ X(j) = «vertex»(v, τ, j)",
						Derive(func(b *Argument) {
							j := b.FixAs[Nat]("j")
							upTo := b.Assume()
							point := b.TermAs[Fun[Nat, Nat]]("X(j)")
							b.Do(Funext())
							i := b.FixAs[Nat]("i")
							b.Cases(b.Term("i < n ∧ τ(i) < j"))
							b.When(
								"coordinate i is raised at level j",
								func(c *Argument, on Fact) {
									c.Show(
										"both read v(i) + 1",
										ByArith(on, upTo, chosen.At(j), reading.At(point, i), raisedAt.At(i, j)))
								})
							b.Otherwise(
								"coordinate i is not raised at level j",
								func(c *Argument, off Fact) {
									c.Cases(c.Term("i < n"))
									c.When(
										"below n its step is j or later",
										func(d *Argument, inRange Fact) {
											d.Show(
												"both read v(i)",
												ByArith(off, inRange, upTo, chosen.At(j), reading.At(point, i), raisedAt.At(i, j)))
										})
									c.Otherwise(
										"from n on no coordinate is raised",
										func(d *Argument, outOfRange Fact) {
											d.Show(
												"both read v(i)",
												ByArith(outOfRange, upTo, chosen.At(j), reading.At(point, i)))
										})
								})
						}))
					injective := a.Have(
						"no two coordinates switch on at the same step",
						"∀i i₁:num. i < n ∧ i₁ < n ∧ τ(i) = τ(i₁) ⇒ i = i₁",
						Derive(func(b *Argument) {
							i := b.FixAs[Nat]("i")
							i1 := b.FixAs[Nat]("i₁")
							given := b.Assume()
							step := b.TermAs[Nat]("τ(i)")
							next := b.TermAs[Nat]("τ(i) + 1")
							newlyRaised := b.Have(
								"both switch on at step τ(i)",
								"i ∈ «raised»(v, X(τ(i) + 1)) ∖ «raised»(v, X(τ(i))) ∧ "+
									"i₁ ∈ «raised»(v, X(τ(i) + 1)) ∖ «raised»(v, X(τ(i)))",
								BySets(given, steps.At(i), steps.At(i1)))
							bounds := b.Have(
								"τ(i) and τ(i) + 1 are levels",
								"τ(i) ≤ τ(i) + 1 ∧ τ(i) ≤ n ∧ τ(i) + 1 ≤ n",
								ByArith(given, steps.At(i)))
							consecutive := b.Have(
								"consecutive levels raise nested sets of j and j + 1 coordinates",
								"«raised»(v, X(τ(i))) ⊆ «raised»(v, X(τ(i) + 1)) ∧ "+
									"card(«raised»(v, X(τ(i)))) = τ(i) ∧ "+
									"card(«raised»(v, X(τ(i) + 1))) = τ(i) + 1",
								By(bounds, grows.At(step, next), chosen.At(step), chosen.At(next)))
							upper := b.TermAs[Set[Nat]]("«raised»(v, X(τ(i) + 1))")
							lower := b.TermAs[Set[Nat]]("«raised»(v, X(τ(i)))")
							single := b.Have(
								"exactly one coordinate switches on per step",
								"finite(«raised»(v, X(τ(i) + 1)) ∖ «raised»(v, X(τ(i)))) ∧ "+
									"card(«raised»(v, X(τ(i) + 1)) ∖ «raised»(v, X(τ(i)))) ≤ 1",
								ByArith(
									consecutive,
									bounded.At(b.TermAs[Fun[Nat, Nat]]("X(τ(i) + 1)")),
									cardinality.CardDiff.At(upper, lower),
									finite_set.FiniteDiff.At(upper, lower)))
							_, inside := b.ObtainAs[Nat](
								"the coordinates switching on at step τ(i) lie in one singleton",
								"∃a:num. «raised»(v, X(τ(i) + 1)) ∖ «raised»(v, X(τ(i))) ⊆ {a}",
								By(single, cardinality.AtMostOneIffInSingleton))
							b.Show(
								"so i and i₁ are that one coordinate",
								BySets(inside, newlyRaised))
						}))
					onLevel := a.Have(
						"each point of s is the chosen point of its level",
						"∀x:(num → num). x ∈ s ⇒ card(«raised»(v, x)) ≤ n ∧ x = X(card(«raised»(v, x)))",
						Derive(func(b *Argument) {
							x := b.FixAs[Fun[Nat, Nat]]("x")
							in := b.Assume()
							count := b.TermAs[Nat]("card(«raised»(v, x))")
							b.Show(
								"X of that level lies on the same level",
								By(
									in,
									bounded.At(x),
									chosen.At(count),
									levelsSeparate.At(x, b.TermAs[Fun[Nat, Nat]]("X(card(«raised»(v, x)))"))))
						}))
					chain := a.Have(
						"s is the chain of vertices",
						"s = {«vertex»(v, τ, j) | j:num | j ≤ n}",
						Derive(func(b *Argument) {
							b.Do(Simp(Fwd(set_basic.Extension)))
							x := b.FixAs[Fun[Nat, Nat]]("x")
							b.Iff()
							b.Forward(
								"a point of s is the vertex of its level",
								func(c *Argument, in Fact) {
									c.Show(
										"its level is at most n",
										By(in, onLevel.At(x), vertices.At(c.TermAs[Nat]("card(«raised»(v, x))"))))
								})
							b.Backward(
								"a vertex is a chosen point, which lies in s",
								func(c *Argument, onChain Fact) {
									j, at := c.UnpackAs[Nat](onChain, "j")
									c.Show(
										"X(j) lies in s",
										By(at, vertices.At(j), chosen.At(j)))
								})
						}))
					a.Take(v)
					a.Take(tau)
					a.Show(
						"v and τ present s as a chain",
						By(steps, injective, chain, functions.InjectiveOnDef))
				})
		}),
})}

// KuhnLeRefl — every point lies below itself in Kuhn's order, raised in no
// coordinate.
var KuhnLeRefl = kuhnLeReflThm{family.Add(registry.ProofEntry{
	Name: "KuhnLeRefl",
	Key:  "prop_bcdf3f5104996f74",
	Build: family.Theorem("∀n:num. ∀x:(num → num). kuhn_le(n, x, x)",
		func(a *Argument, n *Expr[Nat], x *Expr[Fun[Nat, Nat]]) {
			a.Do(Unfold(KuhnLeDef))
			a.Show(
				"coordinate by coordinate, x(i) ≤ x(i) ≤ x(i) + 1",
				ByArith())
		}),
})}

// KuhnChainOrdered — along a chain the vertices rise: an earlier vertex
// lies below a later one, coordinate by coordinate raised by at most one.
var KuhnChainOrdered = kuhnChainOrderedThm{family.Add(registry.ProofEntry{
	Name: "KuhnChainOrdered",
	Key:  "prop_b18d59bdc96fed96",
	Build: family.Theorem(Statement{
		Binders: "∀n:num. ∀v τ:(num → num). ∀j l:num.",
		Hypotheses: []string{
			"j ≤ l",
		},
		Conclusion: "kuhn_le(n, «vertex»(v, τ, j), «vertex»(v, τ, l))",
	},
		func(a *Argument, n *Expr[Nat], v, τ *Expr[Fun[Nat, Nat]], j, l *Expr[Nat], earlier Fact) {
			a.Do(Unfold(KuhnLeDef))
			a.Show(
				"a coordinate vertex j raises, vertex l raises too",
				ByArith(earlier))
		}),
})}

// KuhnChainDistinct — the vertices of a chain whose order τ gives the
// coordinates below n distinct steps below n are distinct: vertex l raises
// the coordinate of step j, which vertex j leaves low.
var KuhnChainDistinct = kuhnChainDistinctThm{family.Add(registry.ProofEntry{
	Name: "KuhnChainDistinct",
	Key:  "prop_5ad5a83c5e94a8d3",
	Build: family.Theorem(Statement{
		Binders: "∀n:num. ∀v τ:(num → num). ∀j l:num.",
		Hypotheses: []string{
			"∀i:num. i < n ⇒ τ(i) < n",
			"injective_on({i:num | i < n}, τ)",
			"j < l",
			"l ≤ n",
		},
		Conclusion: "¬(«vertex»(v, τ, j) = «vertex»(v, τ, l))",
	},
		func(a *Argument, n *Expr[Nat], v, τ *Expr[Fun[Nat, Nat]], j, l *Expr[Nat], given Fact) {
			_, raisedAtJ := a.ObtainAs[Nat](
				"τ, one-to-one from the coordinates below n into the "+
					"steps below n, gives some coordinate k the step j",
				"∃k:num. k < n ∧ τ(k) = j",
				By(
					given,
					functions.InjectiveOnDef,
					num_segment.BelowStrictInjectiveOnto.At(n, τ, j),
					nat_order.LessThanLessEqTrans.At(j, l, n)))
			differ := a.Have(
				"vertex j has v(k) at k, vertex l has v(k) + 1",
				"¬(«vertex»(v, τ, j, k) = «vertex»(v, τ, l, k))",
				ByArith(raisedAtJ, given))
			a.Show(
				"two maps differing at k differ",
				By(Normalized, differ))
		}),
})}

// KuhnChainFaceVertices — every vertex of a chain other than the one
// removed lies on the face opposite it.
var KuhnChainFaceVertices = kuhnChainFaceVerticesThm{family.Add(registry.ProofEntry{
	Name: "KuhnChainFaceVertices",
	Key:  "prop_e8ed79c92980ce16",
	Build: family.Theorem(Statement{
		Binders: "∀n:num. ∀v τ:(num → num). ∀s:set(num → num). ∀j m:num.",
		Hypotheses: []string{
			"∀i:num. i < n ⇒ τ(i) < n",
			"injective_on({i:num | i < n}, τ)",
			"s = {«vertex»(v, τ, k) | k:num | k ≤ n}",
			"j ≤ n",
			"m ≤ n",
			"¬(j = m)",
		},
		Conclusion: "«vertex»(v, τ, j) ∈ delete(s, «vertex»(v, τ, m))",
	},
		func(
			a *Argument,
			n *Expr[Nat],
			v, τ *Expr[Fun[Nat, Nat]],
			s *Expr[Set[Fun[Nat, Nat]]],
			j, m *Expr[Nat],
			h Fact,
		) {
			given := a.Conjuncts(
				h,
				"τ gives each coordinate below n a step below n",
				"τ is one-to-one below n",
				"s is the chain",
				"j is at most n",
				"m is at most n",
				"j is not m")
			onChain := a.Have(
				"vertex j is a point of s",
				"«vertex»(v, τ, j) ∈ s",
				Derive(func(b *Argument) {
					b.Do(given[2].Rw())
					b.Show(
						"vertex j is on the chain, j being at most n",
						By(given[3]))
				}))
			differ := a.Have(
				"vertex j is not vertex m",
				"¬(«vertex»(v, τ, j) = «vertex»(v, τ, m))",
				Derive(func(b *Argument) {
					b.Cases(b.Term("j < m"))
					b.When(
						"j comes before m",
						func(c *Argument, before Fact) {
							c.Show(
								"the chain's vertices at distinct indices differ",
								By(given[0], before, given[4], given[1], At(KuhnChainDistinct, n, v, τ, j, m)))
						})
					b.Otherwise(
						"m comes before j",
						func(c *Argument, notBefore Fact) {
							after := c.Have(
								"m < j",
								"m < j",
								ByArith(notBefore, given[5]))
							c.Show(
								"the chain's vertices at distinct indices differ",
								By(given[0], after, given[3], given[1], At(KuhnChainDistinct, n, v, τ, m, j)))
						})
				}))
			a.Show(
				"a point of s other than vertex m",
				By(differ, onChain, set_basic.InDelete))
		}),
})}

// KuhnChainFacePoints — every point of the face of a chain opposite a
// vertex is another vertex of the chain.
var KuhnChainFacePoints = kuhnChainFacePointsThm{family.Add(registry.ProofEntry{
	Name: "KuhnChainFacePoints",
	Key:  "prop_a15974241b8f532",
	Build: family.Theorem(Statement{
		Binders: "∀n:num. ∀v τ:(num → num). ∀s:set(num → num). ∀m:num. ∀x:(num → num).",
		Hypotheses: []string{
			"s = {«vertex»(v, τ, k) | k:num | k ≤ n}",
			"x ∈ delete(s, «vertex»(v, τ, m))",
		},
		Conclusion: "∃j:num. j ≤ n ∧ ¬(j = m) ∧ x = «vertex»(v, τ, j)",
	},
		func(
			a *Argument,
			n *Expr[Nat],
			v, τ *Expr[Fun[Nat, Nat]],
			s *Expr[Set[Fun[Nat, Nat]]],
			m *Expr[Nat],
			x *Expr[Fun[Nat, Nat]],
			h Fact,
		) {
			given := a.Conjuncts(
				h,
				"s is the chain",
				"x lies on the face opposite vertex m")
			parts := a.Conjuncts(
				a.Have(
					"x is a vertex of the chain other than vertex m",
					"x ∈ {«vertex»(v, τ, k) | k:num | k ≤ n} ∧ ¬(x = «vertex»(v, τ, m))",
					By(given[0], given[1], set_basic.InDelete)),
				"x is a vertex of the chain",
				"x is not vertex m")
			_, at := a.UnpackAs[Nat](parts[0], "j")
			a.Show(
				"x is vertex j for some j other than m",
				By(parts[1], at))
		}),
})}

// KuhnChainAgree — two points lying between the same two vertices of a
// chain, in Kuhn's order, are equal when they agree at the coordinates
// raised in between: elsewhere the two vertices agree and pin both points.
var KuhnChainAgree = kuhnChainAgreeThm{family.Add(registry.ProofEntry{
	Name: "KuhnChainAgree",
	Key:  "prop_15e9cf840eb5e570",
	Build: family.Theorem(Statement{
		Binders: "∀n:num. ∀v τ:(num → num). ∀j l:num. ∀b c:(num → num).",
		Hypotheses: []string{
			"kuhn_le(n, «vertex»(v, τ, j), b)",
			"kuhn_le(n, b, «vertex»(v, τ, l))",
			"kuhn_le(n, «vertex»(v, τ, j), c)",
			"kuhn_le(n, c, «vertex»(v, τ, l))",
			"∀i:num. i < n ∧ j ≤ τ(i) ∧ τ(i) < l ⇒ b(i) = c(i)",
		},
		Conclusion: "b = c",
	},
		func(
			a *Argument,
			n *Expr[Nat],
			v, τ *Expr[Fun[Nat, Nat]],
			j, l *Expr[Nat],
			b, c *Expr[Fun[Nat, Nat]],
			h Fact,
		) {
			given := a.Conjuncts(
				h,
				"b lies above vertex j",
				"b lies below vertex l",
				"c lies above vertex j",
				"c lies below vertex l",
				"b and c agree at the steps from j to l")
			bLow := a.Unfolded(given[0], KuhnLeDef)
			bHigh := a.Unfolded(given[1], KuhnLeDef)
			cLow := a.Unfolded(given[2], KuhnLeDef)
			cHigh := a.Unfolded(given[3], KuhnLeDef)
			a.Do(Funext())
			i := a.FixAs[Nat]("i")
			a.Cases(a.Term("i < n"))
			a.When(
				"below n both lie between the two vertices, which agree off the steps from j to l",
				func(d *Argument, below Fact) {
					d.Show(
						"b(i) and c(i) are pinned",
						ByArith(below, given[4].At(i), bHigh.At(i), cHigh.At(i), bLow.At(i), cLow.At(i)))
				})
			a.Otherwise(
				"from n on both equal vertex j",
				func(d *Argument, beyond Fact) {
					d.Show(
						"b(i) and c(i) are v(i)",
						ByArith(beyond, bLow.At(i), cLow.At(i)))
				})
		}),
})}

// KuhnChainSqueeze — a point between two consecutive vertices of a chain,
// in Kuhn's order, is one of them: the two differ only at the coordinate
// raised at step j, where the point is either still low or already
// raised. The upper vertex is a binder l with l = j + 1, not the term
// j + 1, so that a citer names it as it holds it, as n or as m.
var KuhnChainSqueeze = kuhnChainSqueezeThm{family.Add(registry.ProofEntry{
	Name: "KuhnChainSqueeze",
	Key:  "prop_6a316089a31bf847",
	Build: family.Theorem(Statement{
		Binders: "∀n:num. ∀v τ:(num → num). ∀j l:num. ∀b:(num → num).",
		Hypotheses: []string{
			"injective_on({i:num | i < n}, τ)",
			"l = j + 1",
			"kuhn_le(n, «vertex»(v, τ, j), b)",
			"kuhn_le(n, b, «vertex»(v, τ, l))",
		},
		Conclusion: "b = «vertex»(v, τ, j) ∨ b = «vertex»(v, τ, l)",
	},
		func(
			a *Argument,
			n *Expr[Nat],
			v, τ *Expr[Fun[Nat, Nat]],
			j, l *Expr[Nat],
			b *Expr[Fun[Nat, Nat]],
			h Fact,
		) {
			given := a.Conjuncts(
				h,
				"τ is one-to-one below n",
				"vertex l is the next after vertex j",
				"b lies above vertex j",
				"b lies below vertex l")
			next := a.Have(
				"j ≤ l",
				"j ≤ l",
				ByArith(given[1]))
			lower := a.TermAs[Fun[Nat, Nat]]("«vertex»(v, τ, j)")
			upper := a.TermAs[Fun[Nat, Nat]]("«vertex»(v, τ, l)")
			a.Cases(a.Term("∀i:num. i < n ∧ τ(i) = j ⇒ b(i) = v(i)"))
			a.When(
				"b leaves the coordinates of step j low, so it is vertex j",
				func(c *Argument, low Fact) {
					agreeLow := c.Have(
						"b agrees with vertex j at step j",
						"∀i:num. i < n ∧ j ≤ τ(i) ∧ τ(i) < l ⇒ b(i) = «vertex»(v, τ, j, i)",
						Derive(func(d *Argument) {
							i := d.FixAs[Nat]("i")
							d.Show(
								"step j is the only step from j to l",
								ByArith(low.At(i), given[1]))
						}))
					c.Show(
						"b is vertex j, the lower of the two",
						Left(),
						By(
							agreeLow,
							next,
							given[3],
							given[2],
							At(KuhnChainAgree, n, v, τ, j, l, b, lower),
							KuhnLeRefl.At(n, lower),
							At(KuhnChainOrdered, n, v, τ, j, l)))
				})
			a.Otherwise(
				"b raises some coordinate of step j, so it is vertex l",
				func(c *Argument, notLow Fact) {
					k, raised := c.ObtainAs[Nat](
						"a coordinate k of step j where b is raised",
						"∃k:num. k < n ∧ τ(k) = j ∧ ¬(b(k) = v(k))",
						By(notLow))
					bLow := c.Unfolded(given[2], KuhnLeDef)
					up := c.Have(
						"b(k) = v(k) + 1",
						"b(k) = v(k) + 1",
						ByArith(raised, bLow.At(k)))
					agreeHigh := c.Have(
						"b agrees with vertex l at step j",
						"∀i:num. i < n ∧ j ≤ τ(i) ∧ τ(i) < l ⇒ b(i) = «vertex»(v, τ, l, i)",
						Derive(func(d *Argument) {
							d.FixAs[Nat]("i")
							atStep := d.Assume()
							same := d.Have(
								"τ is one-to-one, so i is k",
								"i = k",
								ByArith(given[1], given[0], raised, atStep, functions.InjectiveOnDef))
							d.Show(
								"b(i) = v(i) + 1",
								ByArith(same, given[1], up, atStep))
						}))
					c.Show(
						"b is vertex l, the upper of the two",
						Right(),
						By(
							agreeHigh,
							next,
							given[3],
							given[2],
							At(KuhnChainAgree, n, v, τ, j, l, b, upper),
							At(KuhnChainOrdered, n, v, τ, j, l),
							KuhnLeRefl.At(n, upper)))
				})
		}),
})}

// KuhnEarlierBelowExchanged — a vertex before m lies below the exchanged
// point «swapped»(v, τ, m), vertex m with the steps m - 1 and m exchanged:
// a coordinate the exchanged point leaves low has its step at m - 1 or
// after m, never before j, so vertex j leaves it low too.
var KuhnEarlierBelowExchanged = kuhnEarlierBelowExchangedThm{family.Add(registry.ProofEntry{
	Name: "KuhnEarlierBelowExchanged",
	Key:  "prop_237ee4daac74da22",
	Build: family.Theorem(Statement{
		Binders: "∀n:num. ∀v τ:(num → num). ∀j m:num.",
		Hypotheses: []string{
			"j < m",
		},
		Conclusion: "kuhn_le(n, «vertex»(v, τ, j), «swapped»(v, τ, m))",
	},
		func(a *Argument, n *Expr[Nat], v, τ *Expr[Fun[Nat, Nat]], j, m *Expr[Nat], earlier Fact) {
			a.Do(Unfold(KuhnLeDef))
			a.FixAs[Nat]("i")
			a.Cases(a.Term("τ(i) < m - 1 ∨ τ(i) = m"))
			a.When(
				"the step of i is before m - 1 or is m, where below n the exchanged point raises",
				func(b *Argument, raised Fact) {
					b.Show(
						"below n the exchanged point is v(i) + 1 and vertex "+
							"j is v(i) or v(i) + 1, and from n on both are v(i)",
						ByArith(raised))
				})
			a.Otherwise(
				"the step of i is m - 1 or after m, where the exchanged point does not raise",
				func(b *Argument, low Fact) {
					b.Show(
						"that step is not before j, so vertex j does not raise "+
							"i either, and both are v(i) below n and from n on",
						ByArith(earlier, low))
				})
		}),
})}

// KuhnExchangedBelowLater — the exchanged point «swapped»(v, τ, m), vertex
// m with the steps m - 1 and m exchanged, lies below every vertex after m:
// a coordinate the exchanged point raises has its step at most m, before
// j, so vertex j raises it too.
var KuhnExchangedBelowLater = kuhnExchangedBelowLaterThm{family.Add(registry.ProofEntry{
	Name: "KuhnExchangedBelowLater",
	Key:  "prop_10e89c28cd2c237b",
	Build: family.Theorem(Statement{
		Binders: "∀n:num. ∀v τ:(num → num). ∀j m:num.",
		Hypotheses: []string{
			"m < j",
		},
		Conclusion: "kuhn_le(n, «swapped»(v, τ, m), «vertex»(v, τ, j))",
	},
		func(a *Argument, n *Expr[Nat], v, τ *Expr[Fun[Nat, Nat]], j, m *Expr[Nat], later Fact) {
			a.Do(Unfold(KuhnLeDef))
			a.FixAs[Nat]("i")
			a.Cases(a.Term("τ(i) < m - 1 ∨ τ(i) = m"))
			a.When(
				"the step of i is before m - 1 or is m, where below n the exchanged point raises",
				func(b *Argument, raised Fact) {
					b.Show(
						"that step is before j, so below n vertex j raises i too, and from n on both are v(i)",
						ByArith(later, raised))
				})
			a.Otherwise(
				"the step of i is m - 1 or after m, where the exchanged point does not raise",
				func(b *Argument, low Fact) {
					b.Show(
						"the exchanged point is v(i), and vertex j is v(i) or v(i) + 1 below n and v(i) from n on",
						ByArith(low))
				})
		}),
})}
