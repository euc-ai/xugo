// constructions.go — the count of a set given by its description: a
// product, a function space, a universe, a powerset.
//
// Four parts, marked by banners:
//
// - How many pairs a base and its fibres span
// - How many maps a finite domain admits into a finite codomain
// - How many points a whole type holds
// - How many subsets a set has

package cardinality

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_product"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// How many pairs a base and its fibres span
// ---------------------------------------------------------------------------
//
// Every other part of the chapter counts ONE set, taken apart at a point
// or compared with a neighbour. This one counts a set of PAIRS:
// draw a first coordinate from a base set, and a second from a set that
// may depend on which first coordinate was drawn. The count is the
// product of the two sizes — as many rows as the base has points, each
// row as long as that point's fibre.
//
// The part holds one theorem and its three readings: the dependent law,
// then the same law at a fibre held still, then that read at counts
// instead of sizes, then the values of a two-place map that tells pairs
// apart. Each member says what its own reading is for.
//
// Three types meet here, which no member of the chapter has needed
// before: the base's element type A, the fibres' element type B, and
// the pairs' own type — a fourth, the values' type C, joins them in the
// last member. The pairs' type is `prod(A, B)`, the domain's product
// type constructor. It is BUILT rather than named, so it is inferred
// wherever a pair is written and has to be spelled out only where
// nothing infers it: the phantom `pair` (vocab.go), which the wrapper
// cites instantiate at, «noPairs», where a nullary constant has nothing
// to infer it from, and the last member's λ over pairs.

// Two spellings recur through this part, in the headline's own letters.
// The RECTANGLE `{(x, y) | x:A, y:B | x ∈ s ∧ y ∈ t(x)}` is the set the
// part counts: every pair whose first coordinate is drawn from the
// base and whose second lies in that coordinate's own fibre; at a fibre
// held still it is the product `set_cross(s, t)`. A ROW
// `image(λy:B. (p, y), t(p))` is what ONE point of the base
// contributes: its fibre with the point itself fixed as first
// coordinate — every pair in it shares that coordinate, which is what
// makes distinct points contribute disjoint rows.

// HasSizeProductDependent — the pairs drawn from a finite base and its
// fibres number the base's size times the common fibre size.
//
// Induction on the base's SIZE rather than on the base itself, which is
// what makes the whole argument fit in one recursion clause. A base of
// size suc m IS a base of size m with one further point added from
// outside it — that is `HasSizeClauses`, stated once and read here — so
// the step never has to argue that the point it adds is new, nor to
// compute a count from card's own recursion.
//
// At each step the enlarged rectangle splits in two. Every pair whose
// first coordinate is the new point forms that point's row, which is
// its fibre carried across by the pairing and so has the fibre's size;
// everything else is the rectangle the old base spans, counted by the
// induction hypothesis. The two are disjoint because a pair's first
// coordinate cannot be both the new point and one of the old ones, so
// the counts add: m·n from the old base and one further n from the new
// row, which is what (m+1)·n is.
//
// The base of the induction is where the two sides being sizes rather
// than mere finiteness pays: a base of size 0 is empty outright, so the
// rectangle over it is empty and 0·n is 0.
//
// Nothing is asked of the fibre map beyond the size of each fibre. Two
// points may have literally the same fibre, or disjoint ones; the rows
// they contribute are disjoint either way, because it is the FIRST
// coordinate that separates them.
var HasSizeProductDependent = hasSizeProductDependentThm{family.Add(registry.ProofEntry{
	Name: "HasSizeProductDependent",
	Key:  "prop_267c567a13c5fbd3",
	Build: family.Sections(
		Statement{
			Binders: "∀s:set(A). ∀t:(A → set(B)). ∀m n:num.",
			Hypotheses: []string{
				"has_size(s, m)",
				"∀x:A. x ∈ s ⇒ has_size(t(x), n)",
			},
			Conclusion: "has_size({(x, y) | x:A, y:B | x ∈ s ∧ y ∈ t(x)}, m * n)",
			Abbrev: Abbrev{
				{Name: "noPairs", Text: "∅⟨A:prod(A,B)⟩"},
			},
		},
		func(ctx *Script, headline string) *GoalStackNode {
			// Three lemmas the induction step spends, each at ONE point and
			// ONE base — two about the construction and one about what a
			// row counts. All three are stated out here over an arbitrary
			// point and base rather than inside the step: each is pure
			// membership bookkeeping about the two set-builder sides it
			// names, and out here the set driver meets exactly those, with
			// nothing of the step's counting apparatus to unfold alongside
			// them.

			// The split the whole induction turns on, and the only place
			// this proof looks inside the construction. A point added to the
			// base adds exactly its own row and disturbs nothing else.
			//
			// The old rectangle is written FIRST and the new row second,
			// which is not cosmetic: it is the order in which the counts
			// are added below, and it is the order in which `nat_arith.Mul`'s
			// successor clause states the product — `suc(m)·n = m·n + n`,
			// the old base's contribution first.
			rectangleGrows := ctx.Lemma(
				// `p` and not `x`: the rectangle binds `x` for its own first
				// coordinate, and a point named `x` out here would be
				// captured by it — which parses, and says something else.
				"∀p:A. ∀u:set(A). ∀t:(A → set(B)). "+
					"    {(x, y) | x:A, y:B | x ∈ insert(p, u) ∧ y ∈ t(x)} = "+
					"    {(x, y) | x:A, y:B | x ∈ u ∧ y ∈ t(x)} ∪ image(λy:B. (p, y), t(p))",
				func(a *Argument) {
					// Pure membership bookkeeping: a pair sits over
					// insert(p, u) exactly when its first coordinate is p or
					// lies in u, which is the two sides of the union. The
					// driver is handed nothing, there being nothing to spend.
					a.Do(BySets())
				})

			// Why the two halves can simply be added. A pair in the new
			// point's row has that point as its first coordinate; a pair in
			// the old rectangle has a first coordinate the old base holds;
			// and the point was chosen outside that base.
			rowMissesTheRest := ctx.Lemma(
				Statement{
					Binders: "∀p:A. ∀u:set(A). ∀t:(A → set(B)).",
					Hypotheses: []string{
						"p ∉ u",
					},
					Conclusion: "disjoint({(x, y) | x:A, y:B | x ∈ u ∧ y ∈ t(x)}, image(λy:B. (p, y), t(p)))",
				},
				func(a *Argument) {
					// The pair-equation law rides in the premise list.
					// Without it the driver reduces the goal to the right
					// first-order residual and then stalls, having no way to
					// read a first coordinate off a pair equation.
					a.Do(BySets(pairs.PairEq))
				})

			// A row is the fibre itself, relabelled. Pairing with a fixed
			// first coordinate identifies no two points — that is the
			// pairing's injectivity, and it is all the counting law asks
			// of a map.
			rowCounts := ctx.Lemma(
				Statement{
					Binders: "∀p:A. ∀c:set(B). ∀n:num.",
					Hypotheses: []string{
						"has_size(c, n)",
					},
					Conclusion: "has_size(image(λy:B. (p, y), c), n)",
				},
				func(a *Argument, p, c, n Term, counted Fact) {
					pairWith := a.Term("λy:B. (p, y)")

					injective := a.Have(
						"pairing with p identifies no two points: equal pairs have equal second coordinates",
						"injective_on(c, λy:B. (p, y))",
						// The map's two types land on B and on prod(A, B).
						// Bare PairEq: the instances wanted are pairs the
						// leaf already names.
						Simp(Fwd(functions.InjectiveOnDef.Inst(TypeBinder.BindA[value](), TypeBinder.BindB[pair]()))),
						BySets(pairs.PairEq))

					a.Show(
						"the pairing is injective on the fibre, so the image counts what the fibre does",
						// No shaping: nothing here is a set equation to fold —
						// the size assumed and the size claimed are both
						// sizes.
						By(
							counted,
							injective,
							// The law's two element types land on B and on
							// prod(A, B) — a fibre's points and the pairs they
							// become. Stated order (∀f. ∀s. ∀n): the pairing,
							// the set it is applied to, the size carried across.
							HasSizeImageInj.Inst(TypeBinder.BindA[value](), TypeBinder.BindB[pair]()).At(pairWith, c, n)))
				})

			// The theorem itself, with the base's SIZE moved in front of
			// everything else — the induction runs on it, and the base must
			// stay quantified inside, because the step reads the hypothesis
			// at a SMALLER base than the one it is proving about.
			countsByBaseSize := ctx.Lemma(
				Statement{
					Binders: "∀m:num. ∀s:set(A). ∀t:(A → set(B)). ∀n:num.",
					Hypotheses: []string{
						"has_size(s, m)",
						"∀x:A. x ∈ s ⇒ has_size(t(x), n)",
					},
					Conclusion: "has_size({(x, y) | x:A, y:B | x ∈ s ∧ y ∈ t(x)}, m * n)",
				},
				func(a *Argument) {
					// The size is named before the induction rather than
					// stripped: the case bodies state claims about it, and
					// stripping would put it out of the tactic's reach.
					m := a.Binder("m")

					a.Induct(m)
					a.Base(
						"at 0: a base of no points draws no first coordinate, and no rows make no pairs",
						func(b *Argument) {
							s := b.Fix()
							b.Fix()             // t — the fibre map, which the claims below spell by name
							b.Fix()             // the fibre size, which no claim here names — no row is drawn
							given := b.Assume() // the size, and the fibre condition it has no point to ask

							rectangle := b.Term("{(x, y) | x:A, y:B | x ∈ s ∧ y ∈ t(x)}")

							noPairsAtAll := b.Have(
								"a base of size zero is empty, so no pair can have "+
									"its first coordinate drawn, and the rectangle is empty",
								"{(x, y) | x:A, y:B | x ∈ s ∧ y ∈ t(x)} = «noPairs»",
								// The emptiness of s is the one fact the
								// set driver spends.
								BySets(given, At(HasSizeZero, s)))

							b.Show(
								"and the empty rectangle has size 0, which is what 0 · n counts",
								By(
									noPairsAtAll,
									// At the pair type: the size read here
									// is a size of PAIRS, unlike the one
									// read at the base just above.
									HasSizeZero.Inst[pair]().At(rectangle),
									// 0 · n = 0 — the zero clause of ·.
									nat_arith.Mul))
						})
					a.Step(
						"across one more point: the rectangle gains that point's "+
							"row and nothing else, so its count gains one further n",
						func(b *Argument, carried Fact) { // every base of m points spans m · n pairs
							s, t, n := b.Fix(), b.Fix(), b.Fix()
							given := b.Assume() // the size suc m, and the fibre condition on s

							// A base of size suc m IS a base of size m
							// with one further point put in from outside
							// — the recursion clause of has_size, and the
							// only place this proof consults it.
							pt, rest, split := b.Obtain2(
								"a base of one more than m points is a base of m points with a point from outside it added",
								"∃p:A. ∃u:set(A). has_size(u, m) ∧ p ∉ u ∧ s = insert(p, u)",
								// Normalized: the clause pack arrives as two
								// equivalences spread into clauses, and the
								// claim is one side of the second. This is
								// the one shaping here that is not needed
								// to CLOSE — measured by removal, the same
								// premises still close, at the cost of one
								// further CNF key. With the fold the leaf
								// settles under Basic and mints none.
								By(Normalized, given, At(HasSizeClauses, s, m)))

							oldRectangle := b.Term("{(x, y) | x:A, y:B | x ∈ u ∧ y ∈ t(x)}")
							newRow := b.Term("image(λy:B. (p, y), t(p))")
							// The old base's count. Built through the
							// parser because `*` is stated-only in this
							// chapter; vocab.go's note on Times says why.
							oldCount := b.Term("m * n")

							newPointsFibre := b.Have(
								"the point just added has a fibre of n, the enlarged base holding it",
								"has_size(t(p), n)",
								// Stated order (∀s. ∀x y): the added point is in
								// the base it was added to.
								By(given, split, At(set_basic.InInsert, rest, pt, pt)))

							oldPointsFibres := b.Have(
								"and so does every point the base already had",
								"∀x:A. x ∈ u ⇒ has_size(t(x), n)",
								// Bare: the claim quantifies over the point,
								// so there is no instance to name.
								By(given, split, set_basic.InInsert))

							counted := b.Have(
								"so the induction hypothesis counts the rectangle the old base spans",
								"has_size({(x, y) | x:A, y:B | x ∈ u ∧ y ∈ t(x)}, m * n)",
								By(oldPointsFibres, carried.At(rest, t, n), split))

							row := b.Have(
								"the new point's row is that fibre paired up, so it counts n as well",
								"has_size(image(λy:B. (p, y), t(p)), n)",
								By(newPointsFibre, rowCounts))

							apart := b.Have(
								"the row meets nothing the old base spans, its pairs all starting at a point that base misses",
								"disjoint({(x, y) | x:A, y:B | x ∈ u ∧ y ∈ t(x)}, image(λy:B. (p, y), t(p)))",
								By(split, rowMissesTheRest))

							grows := b.Have(
								"while the enlarged rectangle is exactly those two together",
								"{(x, y) | x:A, y:B | x ∈ s ∧ y ∈ t(x)} = "+
									"{(x, y) | x:A, y:B | x ∈ u ∧ y ∈ t(x)} ∪ image(λy:B. (p, y), t(p))",
								By(split, rectangleGrows))

							oneMoreRow := b.Have(
								"and one more point is one more row: (m+1) · n is m · n and a further n",
								"suc(m) * n = m * n + n",
								// The successor clause of ·.
								By(nat_arith.Mul))

							b.Show(
								"so the two disjoint parts add up, and their sum is the count the enlarged base owes",
								// The equation drives a REWRITE and is not
								// passed as a premise: `suc(m) · n` and
								// `m · n` are distinct opaque products to
								// the closer, which will not identify them
								// across an equation it is merely handed.
								// Measured: as a premise the same leaf
								// fails; as a rewrite it closes.
								oneMoreRow.Rw(), // ↦ has_size(rectangle over s, m · n + n)
								grows.Rw(),      // ↦ has_size(old rectangle ∪ new row, m · n + n)
								By(
									apart,
									counted,
									row,
									// At the pair type, both operands being
									// sets of pairs. Stated order
									// (∀s t. ∀m n): the old rectangle and
									// its count first, the new row and its
									// own second — the order `oneMoreRow`
									// puts the sum in.
									HasSizeUnion.Inst[pair]().At(oldRectangle, newRow, oldCount, n)))
						})
				})

			return ctx.Theorem(headline, func(a *Argument, s, t, m, n Term) {
				a.Show(
					"the same theorem, read with the base's size back where the statement puts it",
					// Bare of necessity: the leaf IS the lemma at these
					// four Skolems, so the cite closes it outright and has
					// no ∀-source left to ground.
					Cite(countsByBaseSize))
			})
		}),
})}

// HasSizeProduct — the product of two sets of known size, the rectangle
// of pairs drawn one from each, has the product of their sizes.
//
// Opened by its definition, the product set_cross(s, t) is the
// rectangle over s whose every fibre is t, and this is the member above
// read at that fibre: hand every point of the base the SAME second set.
// The dependent law asks only that each point's fibre have a common
// size, and a constant fibre meets that for the trivial reason — there
// is one fibre, and it has the size it has. So the general theorem
// specialises to this one with nothing left over.
//
// That direction is worth stating explicitly, because the other one is
// available and is worse: proving the count first and recovering the
// size from it needs the rectangle's finiteness supplied separately.
// The undependent rectangle is not a weaker relative of the dependent
// one requiring its own argument; it is the same theorem with the fibre
// map held still, and the constant map is the entire proof.
var HasSizeProduct = hasSizeProductThm{family.Add(registry.ProofEntry{
	Name: "HasSizeProduct",
	Key:  "prop_7b72daa9d300b59f",
	Build: family.Theorem(
		Statement{
			Binders: "∀s:set(A). ∀t:set(B). ∀m n:num.",
			Hypotheses: []string{
				"has_size(s, m)",
				"has_size(t, n)",
			},
			Conclusion: "has_size(set_cross(s, t), m * n)",
		},
		Opening(Unfold(set_product.SetCrossDef), func(a *Argument, s, t, m, n Term, given Fact) {
			// The fibre map that ignores its point. Its binder is the
			// dependent law's own first coordinate and is dead in the
			// body, `t` being a Skolem of the statement outside it — so
			// naming it `x` captures nothing and says which slot it fills.
			constantFibre := a.Term("λx:A. t")

			a.Show(
				"the dependent law at a fibre held still: one second set "+
					"over every point of the base, of the size it has anywhere",
				// No shaping. The law read here has the fibre still applied
				// to the point it ignores — `y ∈ (λx. t)(x)`, at every
				// point of the base — and reducing that to `y ∈ t` is the
				// whole distance between the two theorems: a β-reduction,
				// which the instantiation itself performs.
				By(
					given,
					// Stated order (∀s. ∀t. ∀m n): the base, the fibre map,
					// the base's size, the size common to the fibres.
					At(HasSizeProductDependent, s, constantFibre, m, n)))
		})),
})}

// CardProduct — a rectangle holds as many pairs as its sides' counts
// multiply to.
//
// The same fact as the member above, said with counts instead of sizes,
// and the translation between the two is all that happens here. A
// finite set has its own count as a size, so each side supplies one and
// the product law returns a size for the rectangle they span; the count
// this headline asks for is what CardOfSized reads off that size.
//
// So nothing here goes near the construction: no set is taken apart, no
// induction is run, and the pairs are counted once, by the member above.
var CardProduct = cardProductThm{family.Add(registry.ProofEntry{
	Name: "CardProduct",
	Key:  "prop_409e5e9f8cc9230",
	Build: family.Theorem(
		Statement{
			Binders: "∀s:set(A). ∀t:set(B).",
			Hypotheses: []string{
				"finite(s)",
				"finite(t)",
			},
			Conclusion: "card(set_cross(s, t)) = card(s) * card(t)",
		},
		func(a *Argument, s, t Term, given Fact) {
			// The two counts the product is taken of. The base's is built
			// through the chapter's handle; the other side's cannot be —
			// the handle is pinned at the element type A and t's points
			// are B's — so it goes through the parser instead (vocab.go's
			// note on the Card field).
			countOfBase := ops(a.Ctx()).Card.Apply(s)
			countOfSecondSide := a.Term("card(t)")

			sized := a.Have(
				"each side's finiteness makes its own count a size, and "+
					"at those two sizes the product law counts the rectangle",
				"has_size(set_cross(s, t), card(s) * card(t))",
				// No shaping. The two finiteness premises do arrive as
				// equivalences spread pointwise, but every set they are
				// spread over is one the product law is already stated
				// about, so there is nothing to fold back before the three
				// meet. (A `Normalized` here was measured inert: same
				// close, same keys, still green.)
				By(
					given,
					// Stated order (∀s. ∀t. ∀m n): the two sides, then the
					// sizes each is about to be given.
					At(HasSizeProduct, s, t, countOfBase, countOfSecondSide),
					// The base's finiteness read as a size.
					At(FiniteHasSize, s),
					// And the other side's, at the second element type: the
					// law is stated over one, and t's points are of the
					// other. Pinned rather than left to the cite, which
					// would ground the law's own type variable at A and
					// leave the premise unable to meet t.
					FiniteHasSize.Inst[value]()))

			a.Show(
				"so the rectangle's count is read off the size it was just given",
				// Read at the rectangle's element type: its points are
				// pairs, and an element type built out of the chapter's
				// letters is pinned rather than left to the cite, exactly
				// as the second side's finiteness is above.
				By(sized, CardOfSized.Inst[pair]()))
		}),
})}

// HasSizeProductImage — a two-place map that tells its argument pairs
// apart takes as many values on s × t as there are pairs, m · n. Its
// values are the image of the rectangle under the map read at a pair's
// two coordinates; that map separates the rectangle's points, since equal
// values have equal coordinates, which make equal pairs; and an
// image under a map that separates points is as large as what it is the
// image of — here the rectangle, with m · n pairs.
var HasSizeProductImage = hasSizeProductImageThm{family.Add(registry.ProofEntry{
	Name: "HasSizeProductImage",
	Key:  "prop_670f2e2c85de229",
	Build: family.Theorem(
		Statement{
			Binders: "∀f:(A → B → C). ∀s:set(A). ∀t:set(B). ∀m n:num.",
			Hypotheses: []string{
				"has_size(s, m)",
				"has_size(t, n)",
				"∀x u:A. ∀y v:B. x ∈ s ∧ y ∈ t ∧ u ∈ s ∧ v ∈ t ∧ f(x, y) = f(u, v) ⇒ x = u ∧ y = v",
			},
			Conclusion: "has_size({f(x, y) | x:A, y:B | x ∈ s ∧ y ∈ t}, m * n)",
		},
		func(a *Argument, f, s, t, m, n Term, given Fact) {
			parts := a.Conjuncts(
				given,
				"s has m points",
				"t has n points",
				"f tells its argument pairs apart")
			sized := a.Have(
				"the rectangle has m · n pairs",
				"has_size(set_cross(s, t), m * n)",
				By(parts[0], parts[1], At(HasSizeProduct, s, t, m, n)))
			same := a.Have(
				"the values are the rectangle's image under f read at a pair's two coordinates",
				"{f(x, y) | x:A, y:B | x ∈ s ∧ y ∈ t} = image(λz:prod(A, B). f(fst(z), snd(z)), set_cross(s, t))",
				BySets(At(set_product.InCrossProjections, s, t), pairs.Fst, pairs.Snd))
			separates := a.Have(
				"and that map separates the rectangle's points",
				"injective_on(set_cross(s, t), λz:prod(A, B). f(fst(z), snd(z)))",
				Derive(func(b *Argument) {
					// Separation is claimed of pairs of points of the rectangle.
					b.Do(Simp(Fwd(functions.InjectiveOnDef.Inst(TypeBinder.BindA[pair](), TypeBinder.BindB[C]()))))
					z, w := b.FixAs[pair]("z"), b.FixAs[pair]("w")
					b.Show(
						"their coordinates lie in s and t, where equal values mean "+
							"equal coordinates, and each point is the pair of its coordinates",
						By(
							// Stated order (∀x u. ∀y v): the two first
							// coordinates, then the two second ones.
							parts[2].At(b.Term("fst(z)"), b.Term("fst(w)"), b.Term("snd(z)"), b.Term("snd(w)")),
							At(set_product.InCrossProjections, s, t, z),
							At(set_product.InCrossProjections, s, t, w),
							pairs.PairEta.At(z),
							pairs.PairEta.At(w)))
				}))
			uncurried := a.Term("λz:prod(A, B). f(fst(z), snd(z))")
			rectangle := a.Term("set_cross(s, t)")
			a.Show(
				"so the values are as many as the pairs",
				same.Rw(),
				By(sized, separates, At(HasSizeImageInj, uncurried, rectangle, a.Term("m * n"))))
		}),
})}

// ---------------------------------------------------------------------------
// How many maps a finite domain admits into a finite codomain
// ---------------------------------------------------------------------------
//
// The set counted here is the maps from s into t pinned to a default d
// outside s — the pinning is what makes the collection a SET of the
// right size, since off s a map is otherwise free. The count is the
// codomain's size raised to the domain's: each point of the domain
// chooses among |t| values independently.
//
// The argument is one induction on the DOMAIN's size, and its step is
// a bijection: a map from one-more-point splits into its value at the
// new point paired with its truncation to the old domain, and every
// such pair (b, g) is assembled back by answering b at the new point
// and following g elsewhere. So the enlarged funspace stands in
// size-preserving correspondence with t × funspace(u), the product law
// counts the pairs, and nat_pow's recursion clause absorbs the factor.
//
// One engine boundary shapes the proofs below: the refuter will not
// instantiate a function-typed goal existential FROM THE EQUATION THAT
// DETERMINES IT — `∃g:(A→B). P(g) ∧ g = λ…` is unreachable for it, and
// stays unreachable with an α-identical instance already resident.
// Since a membership `X ∈ {h | P h}` normalizes to exactly that shape,
// every funspace membership whose subject is a λ-term supplies its
// witness by hand.
//
// In Go that reads `Unfold(set_basic.SetMemberDef), Unfold(set_basic.SetComprehensionDef)`,
// then the map taken as its own witness and the conditions closed by
// `BySets`. set_comprehension is in no chapter vocabulary — it is the
// encoding a set-builder parses into — and `Unfold` resolves it through the ParseScope's definitional-layer
// fallback, the same channel the session's
// `def_expand {const:"set_comprehension"}` uses.
//
// Two memberships meet the boundary, both in the image identity below,
// and each witness is the mathematics: it names a map the argument
// constructs — a truncation, and the map assembled from a pair.

// HasSizeFunspace — the maps from a finite s into a finite t, pinned
// to a default d outside s, number |t| raised to |s|.
//
// Induction on the DOMAIN's size via HasSizeClauses, exactly as the
// pairs part counts its rectangle: a domain of size suc m IS a
// domain of size m with one outside point added, so the step never
// argues the point is new. At each step the funspace over the enlarged
// domain is carried by the splitting bijection onto
// t × funspace(u), whose count is the product law's; nat_pow's
// successor clause turns n · nᵐ into nᵐ⁺¹. The base is where pinning
// to d pays: over the empty domain the conditions force every value to
// d, one map remains, and n⁰ = 1.
//
// Nothing is asked of t beyond its size, and the default d is
// arbitrary — it enters the count only through the membership
// conditions that pin the maps down.
var HasSizeFunspace = hasSizeFunspaceThm{family.Add(registry.ProofEntry{
	Name: "HasSizeFunspace",
	Key:  "prop_5f87ff9e34cebd10",
	Build: family.Sections(
		Statement{
			Binders: "∀s:set(A). ∀t:set(B). ∀m n:num. ∀d:B.",
			Hypotheses: []string{
				"has_size(s, m)",
				"has_size(t, n)",
			},
			Conclusion: "has_size({h:A → B | (∀x:A. x ∈ s ⇒ h(x) ∈ t) ∧ (∀x:A. x ∉ s ⇒ h(x) = d)}, " +
				"    nat_pow(n, m))",
			Abbrev: Abbrev{
				{Name: "funspaceSmaller", Text: "{h:(A → B) | " +
					"    (∀x:A. x ∈ u ⇒ h(x) ∈ t) ∧ (∀x:A. x ∉ u ⇒ h(x) = d)}"},
				{Name: "funspaceEnlarged", Text: "{h:(A → B) | " +
					"    (∀x:A. x ∈ insert(a, u) ⇒ h(x) ∈ t) ∧ (∀x:A. x ∉ insert(a, u) ⇒ h(x) = d)}"},
				{Name: "truncationText", Text: "λx:A. COND(x ∈ u, f(x), d)"},
				{Name: "splitMapText", Text: "λf:(A → B). (f(a), λx:A. COND(x ∈ u, f(x), d))"},
				{Name: "splitRectangle", Text: "set_cross(t, «funspaceSmaller»)"},
				{Name: "noMaps", Text: "∅⟨A:(A → B)⟩"},
			},
		},
		func(ctx *Script, headline string) *GoalStackNode {
			// splitInjective — the bijection separates members: two maps
			// splitting alike are equal, compared point by point. No
			// freshness is needed — the three cases cover every point.
			splitInjective := ctx.Lemma(
				Statement{
					Binders: "∀a:A. ∀u:set(A). ∀t:set(B). ∀d:B. ∀p q:(A → B).",
					Hypotheses: []string{
						"p ∈ «funspaceEnlarged»",
						"q ∈ «funspaceEnlarged»",
						"(p(a), λx:A. COND(x ∈ u, p(x), d)) = (q(a), λx:A. COND(x ∈ u, q(x), d))",
					},
					Conclusion: "p = q",
				},
				func(arg *Argument, a, u, t, d, p, q Term, alike Fact) {
					parts := arg.Conjuncts(
						alike,
						"p maps insert(a, u) into t and answers d off it",
						"so does q",
						"and the two split alike")
					// The two splits compared coordinatewise: PairEq at a
					// value beside a map, in its stated (∀a. ∀b. ∀x. ∀y)
					// order — p's coordinates, then q's.
					coordinatewise := pairs.PairEq.At(
						arg.TermAs[value]("p(a)"), arg.TermAs[mapping]("λx:A. COND(x ∈ u, p(x), d)"),
						arg.TermAs[value]("q(a)"), arg.TermAs[mapping]("λx:A. COND(x ∈ u, q(x), d)"))
					atNew := arg.Have(
						"the first coordinates agree: p and q take one value at a",
						"p(a) = q(a)",
						By(parts[2], coordinatewise))
					onOld := arg.Have(
						"the second coordinates agree: p and q truncate to u alike",
						"∀x:A. COND(x ∈ u, p(x), d) = COND(x ∈ u, q(x), d)",
						By(parts[2], coordinatewise))
					arg.Show(
						"so p and q agree at every point",
						Funext(),
						Derive(func(b *Argument) {
							x := b.Fix("x")
							notNew := b.Unless(
								b.Term("x = a"),
								"at the new point a they agree by the first coordinates",
								Given(func(c *Argument, isNew Fact) {
									c.Show(
										"x is a, where p and q take one value",
										isNew.Rw(), // ↦ p(a) = q(a)
										By(atNew))
								}))
							notOld := b.Unless(
								b.Term("x ∈ u"),
								"on u each truncation follows its own map, so p and q agree there as their truncations do",
								Given(func(c *Argument, inOld Fact) {
									c.Show(
										"at x the two truncations read p(x) and q(x)",
										By(inOld, onOld.At(x)))
								}))
							b.Show(
								"outside insert(a, u) both maps answer d",
								BySets(notNew, notOld, parts[0], parts[1]))
						}))
				})

			// sizesTransfer — the size-transfer law read at this proof's
			// types: a map from maps to pairs that separates the points of
			// a set of maps carries that set's size back from its image.
			// Stated over a GENERIC map and set — the step below reads it
			// at the split and the enlarged funspace — because the one
			// refutation that consumes the law's inner ∀-premise must run
			// over variable-sized atoms: read directly at the funspace
			// terms it outruns the engine's refutation budget (measured),
			// and at variables it is the same close the law's own proof
			// makes.
			// (The binders are j/w rather than the law's own f/s because
			// this proof already spends both names at other types — s is
			// the statement's domain set, f the map a split is taken of in
			// the image identity — and a proof-level free has one type per
			// name.)
			sizesTransfer := ctx.Lemma(
				"∀j:((A → B) → prod(B, (A → B))). ∀w:set(A → B). ∀k:num. "+
					"    (∀p q:(A → B). p ∈ w ∧ q ∈ w ∧ j(p) = j(q) ⇒ p = q) ⇒ "+
					"    has_size(image(j, w), k) ⇒ "+
					"    has_size(w, k)",
				func(arg *Argument, j, w, k Term, separates, counted Fact) {
					// The separation premise read as the law states it, here
					// at the generic map where the reading costs nothing.
					injective := arg.Have(
						"which is j injective on w",
						"injective_on(w, j)",
						Simp(
							Fwd(functions.InjectiveOnDef.Inst(TypeBinder.BindA[mapping](), TypeBinder.BindB[splitPair]()))),
						By(separates))
					arg.Show(
						"the transfer law, its separation premise handed over",
						// The law's two element types land on the maps and on
						// the pairs they split into; witnesses in the stated
						// (∀f. ∀s. ∀n) order.
						By(
							injective,
							counted,
							HasSizeImageInjEq.Inst(TypeBinder.BindA[mapping](), TypeBinder.BindB[splitPair]()).
								At(j, w, k)))
				})

			// imageIdentity — the bijection's image is exactly the
			// rectangle: splitting the enlarged funspace yields precisely
			// the pairs over t and the smaller funspace. Two facts about a
			// single map carry it, each a funspace membership of a λ-term
			// and so witnessed by the map itself: a map on insert(a, u)
			// truncates to a map on u, and a value in t beside a map on u
			// assembles into a map on insert(a, u). Then pointwise, a split
			// lies in the rectangle by the first, and a pair of the
			// rectangle is the split of its assembly by the second — the
			// freshness of a is what returns its second coordinate.
			imageIdentity := ctx.Lemma(
				Statement{
					Binders: "∀a:A. ∀u:set(A). ∀t:set(B). ∀d:B.",
					Hypotheses: []string{
						"a ∉ u",
					},
					Conclusion: "image(«splitMapText», «funspaceEnlarged») = «splitRectangle»",
				},
				func(
					arg *Argument,
					a *Expr[element],
					u *Expr[Set[element]],
					t *Expr[Set[value]],
					d *Expr[value],
					fresh Fact,
				) {
					smallerSet := arg.TermAs[Set[mapping]]("«funspaceSmaller»")
					enlargedSet := arg.TermAs[Set[mapping]]("«funspaceEnlarged»")
					splitMap := arg.TermAs[Fun[mapping, splitPair]]("«splitMapText»")

					// Each law opens its memberships before its binders are
					// taken: an unfold re-spells every resident fact, so the
					// antecedent is assumed after it, already read as the
					// conditions it states.
					truncates := arg.Have(
						"a map on insert(a, u) truncates to a map on u",
						"∀f:(A → B). f ∈ «funspaceEnlarged» ⇒ (λx:A. COND(x ∈ u, f(x), d)) ∈ «funspaceSmaller»",
						Unfold(set_basic.SetMemberDef),
						Unfold(set_basic.SetComprehensionDef),
						Derive(func(b *Argument) {
							b.Fix() // f — the witness below spells it by name
							inEnlarged := b.Assume()
							b.Take(b.Term("«truncationText»"))
							b.Show(
								"on u the truncation follows f into t, and off u it answers d",
								BySets(inEnlarged))
						}))
					assembles := arg.Have(
						"a value in t beside a map on u assembles into a map on insert(a, u)",
						Statement{
							Binders: "∀b:B. ∀g:(A → B).",
							Hypotheses: []string{
								"b ∈ t",
								"g ∈ «funspaceSmaller»",
							},
							Conclusion: "(λx:A. COND(x = a, b, g(x))) ∈ «funspaceEnlarged»",
						},
						Unfold(set_basic.SetMemberDef),
						Unfold(set_basic.SetComprehensionDef),
						Derive(func(c *Argument) {
							c.Fix() // the value b
							c.Fix() // the map g
							sides := c.Assume()
							c.Take(c.Term("λx:A. COND(x = a, b, g(x))"))
							c.Show(
								"at a it answers b ∈ t, on u it follows g into t, and elsewhere it answers d",
								BySets(sides))
						}))

					arg.Show(
						"the split image and t × funspace(u) have the same members",
						Simp(Fwd(set_basic.Extension.Inst[splitPair]())),
						Derive(func(b *Argument) {
							p := b.FixAs[splitPair]("p")
							b.Iff()
							b.Forward(
								"a split lies in the rectangle: its value at a lies in t, its truncation in funspace(u)",
								func(c *Argument, inImage Fact) {
									f, isSplit := c.Obtain(
										"p is the split of a map f on insert(a, u)",
										"∃f:(A → B). p = (f(a), λx:A. COND(x ∈ u, f(x), d)) ∧ f ∈ «funspaceEnlarged»",
										By(inImage, set_basic.InImage.At(splitMap, enlargedSet, p)))
									valueIn := c.Have(
										"the value at a lies in t, a being a point of insert(a, u)",
										"f(a) ∈ t",
										BySets(isSplit))
									c.Show(
										"so p is a value in t beside a map on u",
										By(
											valueIn,
											isSplit,
											truncates.At(f),
											set_product.InCross.At(
												t, smallerSet, c.TermAs[value]("f(a)"), c.TermAs[mapping]("«truncationText»"))))
								})
							b.Backward(
								"a pair of the rectangle is the split of the map answering "+
									"its first coordinate at a and following its second elsewhere",
								func(c *Argument, inRectangle Fact) {
									coords := c.Have(
										"its coordinates lie in t and in funspace(u)",
										"fst(p) ∈ t ∧ snd(p) ∈ «funspaceSmaller»",
										By(inRectangle, set_product.InCrossProjections.At(t, smallerSet, p)))
									assembled := c.TermAs[mapping]("λx:A. COND(x = a, fst(p), snd(p)(x))")
									inEnlarged := c.Have(
										"so the map assembled from them lies in funspace(insert(a, u))",
										"(λx:A. COND(x = a, fst(p), snd(p)(x))) ∈ «funspaceEnlarged»",
										By(coords, assembles.At(c.Term("fst(p)"), c.Term("snd(p)"))))
									truncated := c.Have(
										"its truncation to u is the second coordinate: on u the fresh a is missed, off u both answer d",
										"(λx:A. COND(x ∈ u, COND(x = a, fst(p), snd(p)(x)), d)) = snd(p)",
										Funext(),
										BySets(fresh, coords))
									splitBack := c.Have(
										"so the assembled map splits back to p",
										"(fst(p), λx:A. COND(x ∈ u, COND(x = a, fst(p), snd(p)(x)), d)) = p",
										truncated.Rw(), // ↦ (fst(p), snd(p)) = p
										By(pairs.PairEta.At(p)))
									c.Show(
										"and p, the split of a member of funspace(insert(a, u)), lies in the image",
										By(splitBack, inEnlarged, set_image.FunInImage.At(splitMap, enlargedSet, assembled)))
								})
						}))
				})

			// countsByDomainSize — the theorem with the domain's size moved
			// in front: the induction runs on it, and the domain stays
			// quantified inside because the step reads the hypothesis at a
			// smaller domain than the one it is proving about.
			countsByDomainSize := ctx.Lemma(
				Statement{
					Binders: "∀m:num. ∀s:set(A). ∀t:set(B). ∀n:num. ∀d:B.",
					Hypotheses: []string{
						"has_size(s, m)",
						"has_size(t, n)",
					},
					Conclusion: "has_size(«funspaceWhole», nat_pow(n, m))",
				},
				func(arg *Argument) {
					m := arg.Binder("m")

					arg.Induct(m)
					arg.Base(
						"at 0: an empty domain leaves one map — everything "+
							"pinned to d — and nat_pow(n, 0) counts exactly 1",
						func(b *Argument) {
							s := b.Fix()
							b.Fix()             // t — the claims below spell it by name
							b.Fix()             // the codomain's size, which no claim in the base names — no map is drawn
							b.Fix()             // d — the claims below spell it by name
							given := b.Assume() // the sizes of s and t

							only := b.Have(
								"a domain of size zero is empty: with no point left "+
									"to constrain a map, only the constant-d map remains",
								"«funspaceWhole» = insert(λx:A. d, «noMaps»)",
								// The emptiness of s is the one fact the
								// set driver spends.
								BySets(given, At(HasSizeZero, s)))

							one := b.Have(
								"and a one-map set has size 1: finite by the insertion rule, counted by the singleton law",
								"has_size(insert(λx:A. d, «noMaps»), 1)",
								// ↦ finite(…) ∧ card(…) = 1; the two laws
								// arrive at the map type `mapping` — the
								// singleton holds a map, not a point. Both stay bare:
								// the singleton law fires as a rewrite of
								// the card side (grounding it panics —
								// "install added no hyp"), and the
								// finiteness rules' conjuncts are read
								// whole.
								Unfold(HasSizeDef),
								By(CardSing.Inst[mapping](), finite_set.FiniteRules.Inst[mapping]()))

							b.Show(
								"nat_pow(n, 0) = 1 — the empty product — so the singleton's count is the required one",
								By(only, one, nat_arith.NatPow))
						})
					arg.Step(
						"across one more point: split every map into (value at the new point, "+
							"truncation), count the pairs, and absorb the factor n into the exponent",
						func(b *Argument, carried Fact) { // every domain of m points spans nat_pow(n, m) maps
							s, t, n, d := b.Fix(), b.Fix(), b.Fix(), b.Fix()
							given := b.Assume() // the size suc m, and t's size n

							// A domain of size suc m IS a smaller domain
							// with an outside point added — the recursion
							// clause of has_size, consulted once.
							pt, rest, split := b.Obtain2(
								"a domain of one more than m points is a domain of m points with a point from outside it added",
								"∃a:A. ∃u:set(A). has_size(u, m) ∧ a ∉ u ∧ s = insert(a, u)",
								// Normalized: the clause pack arrives as
								// equivalences spread into clauses, and the
								// claim is one side of the second.
								By(Normalized, given, At(HasSizeClauses, s, m)))

							// The step's terms, named once: the bijection,
							// the two funspaces, and the pair count.
							smallerSet := b.Term("«funspaceSmaller»")
							enlargedSet := b.Term("«funspaceEnlarged»")
							splitMap := b.Term("«splitMapText»")
							oldCount := b.Term("nat_pow(n, m)")
							newCount := b.Term("n * nat_pow(n, m)")

							counted := b.Have(
								"the smaller domain's maps are counted by the induction hypothesis",
								"has_size(«funspaceSmaller», nat_pow(n, m))",
								By(given, split, carried.At(rest, t, n, d)))

							b.Have(
								"so the pairs (value in t, map on the rest) number n · "+
									"nat_pow(n, m) — the product law at a value beside a map",
								"has_size(«splitRectangle», n * nat_pow(n, m))",
								// Stated letters: A the first side's
								// elements — the values t holds — and B
								// the second's, the smaller funspace's
								// maps. Witnesses in the stated (∀s. ∀t.
								// ∀m n) order: the two sides, then their
								// sizes.
								By(
									given,
									counted,
									HasSizeProduct.Inst(TypeBinder.BindA[value](), TypeBinder.BindB[mapping]()).
										At(t, smallerSet, n, oldCount)))

							imageEq := b.Have(
								"splitting carries the enlarged funspace exactly onto those pairs",
								"image(«splitMapText», «funspaceEnlarged») = «splitRectangle»",
								// The cite closes outright: the leaf is the
								// lemma's conclusion at these four Skolems,
								// its freshness antecedent answered by the
								// split just obtained.
								Cite(imageIdentity))

							onPairs := b.Have(
								"so the split image carries the pair count",
								"has_size(image(«splitMapText», «funspaceEnlarged»), n * nat_pow(n, m))",
								imageEq.Rw(), // ↦ has_size(t × funspace(u), n · nat_pow(n, m)), the pair count
								Assumption())

							transferred := b.Have(
								"and counting through the bijection, the enlarged funspace itself counts n · nat_pow(n, m)",
								"has_size(«funspaceEnlarged», n * nat_pow(n, m))",
								// The transfer read at the split, the
								// enlarged funspace, and this step's count
								// (stated order ∀f. ∀s. ∀k); its separation
								// premise is the injectivity section at the
								// same four Skolems.
								By(onPairs, At(splitInjective, pt, rest, t, d), At(sizesTransfer, splitMap, enlargedSet, newCount)))

							expSuc := b.Have(
								"one more point in the exponent is one more factor of n",
								"nat_pow(n, suc(m)) = n * nat_pow(n, m)",
								By(nat_arith.NatPow))

							whole := b.Have(
								"the domain is its split, spelled back",
								"s = insert(a, u)",
								By(split))

							b.Show(
								"rewriting the exponent and the domain leaves exactly the count just transferred",
								expSuc.Rw(), // ↦ has_size(funspace(s), n · nat_pow(n, m))
								whole.Rw(),  // ↦ …at insert(a, u), where the transfer states it
								By(transferred))
						})
				})

			return ctx.Theorem(headline, func(arg *Argument, s, t, m, n, d Term) {
				arg.Show(
					"the same count, with the domain's size back where the statement puts it",
					// Bare of necessity: the leaf IS the lemma at these five
					// Skolems, so the cite closes it outright and has no
					// ∀-source left to ground.
					Cite(countsByDomainSize))
			})
		}),
})}

// funspaceHasSizeAtCounts — the funspace law read at the counts the two
// finitenesses supply. `HasSizeFunspace` sizes the maps from a set of
// size m into a set of size n; a finite set has its own count as a
// size, so at a pair of finite sets the sizes are theirs to give, and
// what comes back is a size for the maps between them.
//
// The two members below are its whole readership. It is stated because they are one theorem read
// in its two halves — a size IS finiteness together with a count — and
// the fact they divide should be on the page once rather than proved
// twice.
var funspaceHasSizeAtCounts = funspaceHasSizeAtCountsThm{family.Add(registry.ProofEntry{
	Name: "funspaceHasSizeAtCounts",
	Key:  "prop_940d37cd4826b9a0",
	Build: family.Theorem(
		Statement{
			Binders: "∀s:set(A). ∀t:set(B). ∀d:B.",
			Hypotheses: []string{
				"finite(s)",
				"finite(t)",
			},
			Conclusion: "«funspaceSized»",
		},
		func(a *Argument, s, t, d Term, given Fact) {
			// The two counts the law is read at. The domain's is built
			// through the chapter's handle; the codomain's goes through
			// the parser, that handle being pinned at the element type A
			// while t's points are B's (vocab.go's note on the Card field).
			countOfDomain := ops(a.Ctx()).Card.Apply(s)
			countOfCodomain := a.Term("card(t)")

			a.Show(
				"each side's finiteness makes its own count a size, and at "+
					"those two sizes the funspace law returns a size for the maps",
				By(
					given,
					// Stated order (∀s. ∀t. ∀m n. ∀d): the two sets, the
					// sizes each is about to be given, and the default the
					// maps answer off the domain.
					At(HasSizeFunspace, s, t, countOfDomain, countOfCodomain, d),
					// The domain's finiteness read as a size.
					At(FiniteHasSize, s),
					// And the codomain's, pinned at the second element
					// type: left to the cite the law would ground its own
					// type variable at A, where the premise cannot meet t.
					FiniteHasSize.Inst[value]()))
		}),
})}

// CardFunspace — the maps from a finite s into a finite t, pinned to a
// default d outside s, are COUNTED by |t| raised to |s|.
//
// The member above returns a SIZE for that same set of maps, taken at
// the count each side's finiteness supplies; the count this headline
// asks for is what CardOfSized reads off that size.
//
// So nothing here goes near the construction: no domain is taken apart,
// no map is split, and the maps are counted once, above.
var CardFunspace = cardFunspaceThm{family.Add(registry.ProofEntry{
	Name: "CardFunspace",
	Key:  "prop_c1f1a53dd5070351",
	Build: family.Theorem(
		Statement{
			Binders: "∀s:set(A). ∀t:set(B). ∀d:B.",
			Hypotheses: []string{
				"finite(s)",
				"finite(t)",
			},
			Conclusion: "card(«funspaceWhole») = nat_pow(card(t), card(s))",
		},
		func(a *Argument, s, t, d Term, given Fact) {
			sized := a.Have(
				"the maps between the two finite sets have a size, "+
					"and it is the codomain's count raised to the domain's",
				"«funspaceSized»",
				By(given, At(funspaceHasSizeAtCounts, s, t, d)))

			a.Show(
				"so the maps' count is read off the size just proved",
				// Read at the funspace's element type: a map from one
				// letter to the other, so pinned.
				By(sized, CardOfSized.Inst[mapping]()))
		}),
})}

// FiniteFunspace — a finite domain admits only finitely many maps into
// a finite codomain, once the maps are pinned to a default d outside
// the domain.
//
// The other half of the size CardFunspace above reads, and read the
// same way. has_size is finiteness together with a count, so the
// funspace law taken at the two counts each side's finiteness supplies
// settles both halves at once: there the count, here the finiteness.
// Neither member is the other's corollary and neither re-runs the
// induction — they divide what one reading of the size law proved, and
// the maps are counted once, above.
//
// So the power stands in this proof and not in this statement: it is
// the size the law returns, and reading the abbreviation out of that
// size leaves the finiteness the headline asks for beside a count the
// headline has no use for.
var FiniteFunspace = finiteFunspaceThm{family.Add(registry.ProofEntry{
	Name: "FiniteFunspace",
	Key:  "prop_4c27ffc1c54946de",
	Build: family.Theorem(
		Statement{
			Binders: "∀s:set(A). ∀t:set(B). ∀d:B.",
			Hypotheses: []string{
				"finite(s)",
				"finite(t)",
			},
			Conclusion: "finite(«funspaceWhole»)",
		},
		func(a *Argument, s, t, d Term, given Fact) {
			a.Have(
				"the maps between the two finite sets have a size, "+
					"and it is the codomain's count raised to the domain's",
				"«funspaceSized»",
				By(given, At(funspaceHasSizeAtCounts, s, t, d)))

			a.Show(
				"and having a size is being finite together with having "+
					"a count, so the finiteness is that fact's other half",
				Unfold(HasSizeDef))
		}),
})}

// ---------------------------------------------------------------------------
// How many points a whole type holds
// ---------------------------------------------------------------------------
//
// The parts above count a set assembled from two others, and each
// answers in the sizes of the parts. This one answers in a number:
// where a type has finitely many inhabitants, its universe has that
// many points and there is nothing left to read off elsewhere.
//
// What makes a universe countable at all is that it can be named as a
// set the constructors build. At the smallest type there is, that
// naming is the whole of the set-theoretic content; at a function type
// it is again the only step, the maps themselves having been counted
// in the part above.

// HasSizeBool — there are exactly two truth values.
//
// A truth value is ⊥ or ⊤, so the universe at bool is the two-point
// set: a question about the constructors, carrying no counting at all.
// From there the count is the insertion clause read once. The one-point
// set {⊤} counts one, and ⊥ is not that point, so laying it in raises
// the count rather than leaving it alone. That same insertion is onto a
// finite set, and being finite beside counting two is what having size
// two means.
var HasSizeBool = hasSizeBoolThm{family.Add(registry.ProofEntry{
	Name: "HasSizeBool",
	Key:  "prop_6f6484da50758aff",
	// `𝕌⟨A:bool⟩` because the universe is nullary and takes its element
	// type from the annotation, as `∅⟨A:τ⟩` does at the pairs above.
	Build: family.Theorem("has_size(𝕌⟨A:bool⟩, 2)",
		func(a *Argument) {
			// The two values, and the one-point set the first is laid
			// into — the witnesses the counting laws are read at.
			falsity, truth := a.Term("⊥"), a.Term("⊤")
			truthAlone := a.Term("{⊤}")

			bothValues := a.Have(
				"a truth value is ⊥ or ⊤, so the universe at bool is the two-point set",
				"𝕌⟨A:bool⟩ = {⊥, ⊤}",
				BySets())

			// ↦ finite(𝕌) ∧ card(𝕌) = 2. Nothing below says what a size
			// is, so without this the count the statement asks for is out
			// of reach.
			a.Do(Unfold(HasSizeDef))

			// `Normalized` is the whole close here: the finiteness rules
			// arrive as one pack, the base beside the enlargement spread
			// into a disjunction, and straightening that out settles the
			// leaf. Without it the same rule closes by refutation and
			// mints a key for it.
			onePoint := a.Have(
				"{⊤} is one point laid into ∅, and ∅ is finite",
				"finite({⊤})",
				By(Normalized, finite_set.FiniteRules))
			newPoint := a.Have(
				"and ⊥ is not that point",
				"⊥ ∉ {⊤}",
				BySets())

			count := a.Have(
				"so laying ⊥ into {⊤} raises the count, from one to two",
				"card({⊥, ⊤}) = 2",
				By(
					onePoint,
					newPoint,
					// card({⊥, ⊤}) = suc(card({⊤})) — the insertion clause
					// on the branch the two premises above decide, read at
					// the set and then the point in its own stated order.
					At(InsertCountsOneMore, truthAlone, falsity),
					At(CardSing, truth), // card({⊤}) = 1
					nat_arith.Two),      // 2 = suc(1)
			)

			a.Show(
				"and that same insertion leaves the set finite, so the universe at bool is finite and counts two",
				By(onePoint, bothValues, count, finite_set.FiniteRules))
		}),
})}

// CardBool — the universe at bool counts two.
//
// The member above sizes that universe; the count this headline asks
// for is what CardOfSized reads off that size. Nothing else happens here —
// the two truth values are laid out where the size is proved, and this
// member neither names them nor counts anything.
var CardBool = cardBoolThm{family.Add(registry.ProofEntry{
	Name: "CardBool",
	Key:  "prop_e3bc739afeb7b56d",
	Build: family.Theorem("card(𝕌⟨A:bool⟩) = 2",
		func(a *Argument) {
			sized := a.Have(
				"the universe at bool has a size, and that size is two",
				"has_size(𝕌⟨A:bool⟩, 2)",
				Cite(HasSizeBool))

			a.Show(
				"so the universe's count is read off the size it has",
				By(sized, CardOfSized))
		}),
})}

// FiniteBool — there are only finitely many truth values.
//
// The other half of the size HasSizeBool proves, read the way CardBool
// reads the first: a size is finiteness together with a count, so that
// one fact leaves the finiteness standing alone, with a count this
// headline has no use for falling away beside it. The two truth values
// are laid out once, where the size is proved, and neither member here
// lays them out again.
var FiniteBool = finiteBoolThm{family.Add(registry.ProofEntry{
	Name: "FiniteBool",
	Key:  "prop_6e1ddc8d3cb659d2",
	Build: family.Theorem("finite(𝕌⟨A:bool⟩)",
		func(a *Argument) {
			a.Have(
				"the universe at bool has a size, and that size is two",
				"has_size(𝕌⟨A:bool⟩, 2)",
				Cite(HasSizeBool))

			a.Show(
				"and having a size is being finite together with having "+
					"a count, so the finiteness is that fact's other half",
				Unfold(HasSizeDef))
		}),
})}

// HasSizeFunspaceUniv — where a domain type and a codomain type each
// have finitely many inhabitants, so does the function type between
// them, and it holds the codomain's count raised to the domain's.
//
// The funspace law above read where both sides are whole types. Over 𝕌
// there is no point off the domain, so the default that law pins its
// maps to constrains nothing, and the set it counts is the function
// type entire — which is the only step this member makes; the maps are
// counted above, once.
//
// No default is ever chosen. Both halves are stated FOR EVERY default —
// the identity because the pinning is vacuous whichever one it names,
// the count because the law holds at each — and it is their meeting
// that leaves a statement with no default in it.
var HasSizeFunspaceUniv = hasSizeFunspaceUnivThm{family.Add(registry.ProofEntry{
	Name: "HasSizeFunspaceUniv",
	Key:  "prop_4df21ae5bef302",
	// `𝕌⟨A:τ⟩` at each of the three types, the universe being nullary
	// and taking its element type from the annotation, as at HasSizeBool
	// above.
	Build: family.Theorem(
		Statement{
			Binders: "∀m n:num.",
			Hypotheses: []string{
				"has_size(𝕌⟨A:A⟩, m)",
				"has_size(𝕌⟨A:B⟩, n)",
			},
			Conclusion: "has_size(𝕌⟨A:A → B⟩, nat_pow(n, m))",
		},
		func(a *Argument, m, n Term, given Fact) {
			allMaps := a.Have(
				"nothing lies off the whole domain, so the pinning off 𝕌 is "+
					"vacuous at every default and the maps it pins are all of them",
				"∀d:B. {h:A → B | (∀x:A. x ∈ 𝕌⟨A:A⟩ ⇒ h(x) ∈ 𝕌⟨A:B⟩) ∧ (∀x:A. x ∉ 𝕌⟨A:A⟩ ⇒ h(x) = d)} = 𝕌⟨A:A → B⟩",
				BySets())

			sized := a.Have(
				"and at each default the funspace law counts that "+
					"same set, the codomain's size raised to the domain's",
				"∀d:B. "+
					"    has_size({h:A → B | (∀x:A. x ∈ 𝕌⟨A:A⟩ ⇒ h(x) ∈ 𝕌⟨A:B⟩) ∧ (∀x:A. x ∉ 𝕌⟨A:A⟩ ⇒ h(x) = d)}, "+
					"        nat_pow(n, m))",
				Derive(func(b *Argument) {
					d := b.Fix()
					wholeDomain, wholeCodomain := b.Term("𝕌⟨A:A⟩"), b.Term("𝕌⟨A:B⟩")

					b.Show(
						"the law read at the two universes, whose sizes the hypothesis supplies",
						// Stated order (∀s. ∀t. ∀m n. ∀d): the domain and the
						// codomain, the two sizes they are given, and the
						// default the maps answer off the domain.
						By(given, At(HasSizeFunspace, wholeDomain, wholeCodomain, m, n, d)))
				}))

			a.Show(
				"and the two agree at every default, so the count the law returns is the function type's own",
				By(allMaps, sized))
		}),
})}

// funspaceUnivHasSizeAtCounts — the funspace law over whole types read
// at the counts the two finitenesses supply. `HasSizeFunspaceUniv`
// sizes the function type from a size for the domain type and a size
// for the codomain type; a finite type's universe has its own count as
// a size, so where both types are finite the sizes are theirs to give,
// and what comes back is a size for the function type.
//
// It exists for the two readings that divide it — a count for the function type, and its
// finiteness. A size IS finiteness together with a count, so those are
// one theorem read in its two halves, and the fact they divide belongs
// on the page once rather than proved twice.
var funspaceUnivHasSizeAtCounts = funspaceUnivHasSizeAtCountsThm{family.Add(registry.ProofEntry{
	Name: "funspaceUnivHasSizeAtCounts",
	Key:  "prop_3baf274e7ef1341d",
	Build: family.Theorem(
		Statement{
			Hypotheses: []string{
				"finite(𝕌⟨A:A⟩)",
				"finite(𝕌⟨A:B⟩)",
			},
			Conclusion: "has_size(𝕌⟨A:A → B⟩, nat_pow(card(𝕌⟨A:B⟩), card(𝕌⟨A:A⟩)))",
		},
		func(a *Argument, given Fact) {
			// The two counts the law is read at.
			countOfDomain := a.TermAs[Nat]("card(𝕌⟨A:A⟩)")
			countOfCodomain := a.TermAs[Nat]("card(𝕌⟨A:B⟩)")

			a.Show(
				"each type's finiteness makes its universe's own count a size, and at "+
					"those two sizes the funspace law returns a size for the function type",
				By(
					given,
					// Stated order (∀m n): the domain's size, then the
					// codomain's. Both element types are named beside them,
					// because the law binds the two SIZES and nothing else:
					// a count is a number and carries no element type, so
					// grounding alone leaves the law's universes standing at
					// its own type variables.
					HasSizeFunspaceUniv.At[element, value](countOfDomain, countOfCodomain),
					// Each side's finiteness read as a size, at each of the
					// two element types.
					FiniteHasSize.Inst[element](),
					FiniteHasSize.Inst[value]()))
		}),
})}

// CardFunspaceUniv — the function type between two types with finitely
// many inhabitants holds the codomain's count raised to the domain's.
//
// The member above sizes that function type, at the counts the two
// finitenesses supply; the count this headline asks for is what
// CardOfSized reads off that size. The maps themselves are counted in
// the part above, and nothing here goes near them.
var CardFunspaceUniv = cardFunspaceUnivThm{family.Add(registry.ProofEntry{
	Name: "CardFunspaceUniv",
	Key:  "prop_8820f501690077f5",
	Build: family.Theorem(
		Statement{
			Hypotheses: []string{
				"finite(𝕌⟨A:A⟩)",
				"finite(𝕌⟨A:B⟩)",
			},
			Conclusion: "card(𝕌⟨A:A → B⟩) = nat_pow(card(𝕌⟨A:B⟩), card(𝕌⟨A:A⟩))",
		},
		func(a *Argument, given Fact) {
			sized := a.Have(
				"the function type between the two finite types has a "+
					"size, and it is the codomain's count raised to the domain's",
				"has_size(𝕌⟨A:(A → B)⟩, nat_pow(card(𝕌⟨A:B⟩), card(𝕌⟨A:A⟩)))",
				By(given, funspaceUnivHasSizeAtCounts))

			a.Show(
				"so the function type's count is read off the size just proved",
				// Read at the function type's own points: maps from one
				// letter to the other, so pinned.
				By(sized, CardOfSized.Inst[mapping]()))
		}),
})}

// FiniteFunspaceUniv — only finitely many functions run between two
// types with finitely many inhabitants.
//
// The other half of the size CardFunspaceUniv above reads, and read the
// same way: a size is finiteness together with a count, so the one fact
// both members stand on settles both halves at once — there the count,
// here the finiteness. Neither is the other's corollary, and neither
// goes near the maps; the function type is counted once, above.
//
// So the power stands in this proof and not in this statement. It is
// the count the size carries, and reading the abbreviation out of that
// size leaves the finiteness the headline asks for beside a count the
// headline has no use for.
var FiniteFunspaceUniv = finiteFunspaceUnivThm{family.Add(registry.ProofEntry{
	Name: "FiniteFunspaceUniv",
	Key:  "prop_a5cb7a2c47e29684",
	Build: family.Theorem(
		Statement{
			Hypotheses: []string{
				"finite(𝕌⟨A:A⟩)",
				"finite(𝕌⟨A:B⟩)",
			},
			Conclusion: "finite(𝕌⟨A:A → B⟩)",
		},
		func(a *Argument, given Fact) {
			a.Have(
				"the function type between the two finite types has a "+
					"size, and it is the codomain's count raised to the domain's",
				"has_size(𝕌⟨A:(A → B)⟩, nat_pow(card(𝕌⟨A:B⟩), card(𝕌⟨A:A⟩)))",
				By(given, funspaceUnivHasSizeAtCounts))

			a.Show(
				"and having a size is being finite together with having "+
					"a count, so the finiteness is that fact's other half",
				Unfold(HasSizeDef))
		}),
})}

// ---------------------------------------------------------------------------
// How many subsets a set has
// ---------------------------------------------------------------------------
//
// The parts above count a set assembled out of two others, or the
// points a type holds. This one counts what ONE set generates: the sets
// that lie inside it.
//
// The answer is a power, and the reason is that a subset IS a map.
// Choosing a subset of s means answering one yes-or-no question at each
// point of s; a map from s into the truth values is exactly such an
// answer, and the choice says nothing about the points outside s, so
// the maps are pinned there. There are two truth values, so the count
// is two raised to the size of s — the function-space law of the part
// above, read where the codomain is bool.

// HasSizePowerset — a set of size n has 2ⁿ subsets.
//
// Containment in s is a pointwise condition — t ⊆ s says t answers ⊥
// wherever s does — and that is precisely the condition pinning a map
// off s. So the powerset of s is the set of maps from s into the truth
// values pinned to ⊥ outside it: an identity about membership and
// containment, with no count in it anywhere, and no subset exhibited to
// see it.
//
// From there the counting is already done. The function-space law of
// the part above counts those maps as the codomain's size raised to the
// domain's, and the codomain here is bool, whose two points are counted
// beside it. Nothing is asked of s but its size.
var HasSizePowerset = hasSizePowersetThm{family.Add(registry.ProofEntry{
	Name: "HasSizePowerset",
	Key:  "prop_170c1599572eaa43",
	Build: family.Theorem(
		Statement{
			Binders: "∀s:set(A). ∀n:num.",
			Hypotheses: []string{
				"has_size(s, n)",
			},
			Conclusion: "has_size({t:set(A) | t ⊆ s}, nat_pow(2, n))",
			Abbrev: Abbrev{
				{Name: "subsetsAsMaps", Text: "{h:(A → bool) | " +
					"    (∀x:A. x ∈ s ⇒ h(x) ∈ 𝕌⟨A:bool⟩) ∧ (∀x:A. x ∉ s ⇒ h(x) = ⊥)}"},
			},
		},
		func(a *Argument, s, n Term, sized Fact) {
			// The three things the funspace law needs that the headline
			// does not name: the codomain the subsets are read into, the
			// answer they are pinned to off s, and the codomain's count.
			truthValues, falsity := a.Term("𝕌⟨A:bool⟩"), a.Term("⊥")
			two := a.Ctx().Numeral(2)

			asMaps := a.Have(
				"a subset of s is a map into the truth values pinned to "+
					"⊥ off s: lying inside s is answering ⊥ wherever s does",
				"{t:set(A) | t ⊆ s} = «subsetsAsMaps»",
				BySets())

			counted := a.Have(
				"and the function-space law counts those maps: the codomain's size, raised to the size s is given",
				"has_size(«subsetsAsMaps», nat_pow(2, n))",
				// Stated order (∀s. ∀t. ∀m n. ∀d): the domain and the
				// codomain, the two sizes they are given, and the answer
				// the maps carry off the domain. The codomain's count
				// stands ahead of the law it feeds, both antecedents
				// being in hand where the law is read.
				By(sized, HasSizeBool, At(HasSizeFunspace, s, truthValues, n, two, falsity)))

			a.Show(
				"so the subsets number what those maps number, the two being one set",
				By(asMaps, counted))
		}),
})}

// CardPowerset — the subsets of a finite s are COUNTED by two raised
// to |s|.
//
// The member above returns a SIZE for those subsets, and asks for one
// in exchange: s's finiteness supplies its own count as the size it
// wants, and off the size that comes back CardOfSized reads the count
// this headline asks for. The powerset's finiteness is not this
// headline's business, and nothing is lost by that —
// finite_set.FinitePowerset states it one chapter out, by an induction
// that never counts.
//
// So nothing here goes near the subsets: none is exhibited, the
// powerset is not taken apart, and it is counted once, above.
var CardPowerset = cardPowersetThm{family.Add(registry.ProofEntry{
	Name: "CardPowerset",
	Key:  "prop_b9f851c6819d501a",
	Build: family.Theorem(
		Statement{
			Binders: "∀s:set(A).",
			Hypotheses: []string{
				"finite(s)",
			},
			Conclusion: "card({t:set(A) | t ⊆ s}) = nat_pow(2, card(s))",
		},
		func(a *Argument, s Term, finite Fact) {
			// The count the law is read at.
			count := ops(a.Ctx()).Card.Apply(s)

			sized := a.Have(
				"s's finiteness makes its own count a size, and at that "+
					"size the powerset law returns a size for the subsets",
				"has_size({t:set(A) | t ⊆ s}, nat_pow(2, card(s)))",
				By(
					finite,
					// The finiteness read as a size, which is the
					// antecedent the law below asks for.
					At(FiniteHasSize, s),
					// Stated order (∀s. ∀n): the set, and the size it
					// is given.
					At(HasSizePowerset, s, count)))

			a.Show(
				"so the subsets' count is read off the size just proved",
				// Read at the powerset's element type: a set over the
				// chapter's letter, so pinned.
				By(sized, CardOfSized.Inst[Set[element]]()))
		}),
})}
