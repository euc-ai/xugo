package nat_product

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/indexed_functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// HasSizeIndexedFunctions is the multiplication principle for varying
// finite factors. Each fresh coordinate contributes its own factor,
// and with no active coordinates the prescribed function is unique.
var HasSizeIndexedFunctions = hasSizeIndexedFunctionsThm{family.Add(registry.ProofEntry{
	Name: "HasSizeIndexedFunctions",
	Key:  "prop_6bdf8ff2c935957c",
	Build: family.Sections(Statement{
		Binders: "∀J:set(I). ∀z:(I → A). ∀X:(I → set(A)).",
		Hypotheses: []string{
			"finite(J)",
			"∀i:I. i ∈ J ⇒ finite(X(i))",
		},
		Conclusion: "has_size(indexed_functions(J, z, X), product(J, λi:I. card(X(i))))",
		Abbrev: Abbrev{
			{Name: "extend", Text: "λi:I. λv:A. λg:(I → A). λj:I. COND(j = i, v, g(j))"},
			{Name: "extensions", Text: "λi:I. λS:set(I). " +
				"    {«extend»(i, v, g) | v:A, g:(I → A) | v ∈ X(i) ∧ g ∈ indexed_functions(S, z, X)}"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		empty := ctx.Lemma(
			"∀z:(I → A). ∀X:(I → set(A)). indexed_functions(∅, z, X) = {z}",
			func(a *Argument, z *Expr[Fun[I, A]], X *Arrow[I, Set[A]]) {
				a.Do(
					Unfold(indexed_functions.IndexedFunctionsDef), Simp(Fwd(set_basic.Extension)))
				a.FixAs[Fun[I, A]]("f")
				a.Iff()
				a.Forward(
					"every coordinate has the prescribed value",
					func(b *Argument, given Fact) {
						eq := b.Have(
							"the map agrees with z at every coordinate",
							"f = z",
							Funext(),
							BySets(given))
						b.Show(
							"the prescribed map lies in its singleton",
							BySets(eq))
					})
				a.Backward(
					"z meets the condition at every coordinate",
					func(b *Argument, singleton Fact) {
						b.Show(
							"there are no active coordinates and z agrees with itself",
							BySets(singleton))
					})
			})

		extensions := ctx.Lemma(Statement{
			Binders:    "∀S:set(I). ∀z:(I → A). ∀X:(I → set(A)). ∀i:I.",
			Hypotheses: []string{"i ∉ S"},
			Conclusion: "indexed_functions(insert(i, S), z, X) = «extensions»(i, S)",
		}, func(
			a *Argument,
			S *Expr[Set[I]],
			z *Expr[Fun[I, A]],
			X *Arrow[I, Set[A]],
			i *Expr[I],
			fresh Fact,
		) {
			a.Do(Simp(Fwd(set_basic.Extension)))
			a.FixAs[Fun[I, A]]("f")
			a.Iff()
			a.Forward(
				"split off the value at the new coordinate",
				func(b *Argument, inBigger Fact) {
					values := b.Unfolded(inBigger, indexed_functions.IndexedFunctionsDef)
					atI := b.Have(
						"the value at i belongs to its factor",
						"f(i) ∈ X(i)",
						BySets(values))
					onOld := b.Have(
						"resetting i to z(i) gives a normalized map on S",
						"«extend»(i, z(i), f) ∈ indexed_functions(S, z, X)",
						Unfold(indexed_functions.IndexedFunctionsDef),
						BySets(fresh, values))
					b.Show(
						"the value and reset map exhibit f as an extension",
						BySets(atI, onOld))
				})
			a.Backward(
				"extend a map by an independent value at i",
				func(b *Argument, fromFactors Fact) {
					_, _, factors := b.Obtain2As[A, Fun[I, A]](
						"choose the value and the map on S",
						"∃v:A. ∃g:(I → A). v ∈ X(i) ∧ g ∈ indexed_functions(S, z, X) ∧ f = «extend»(i, v, g)",
						BySets(fromFactors))
					parts := b.Conjuncts(
						factors,
						"the value is in its factor",
						"the map is normalized on S",
						"f is the extension")
					values := b.Unfolded(parts[1], indexed_functions.IndexedFunctionsDef)
					b.Show(
						"the extension lies in each factor and follows z elsewhere",
						Unfold(indexed_functions.IndexedFunctionsDef),
						BySets(fresh, parts[0], values, parts[2]))
				})
		})

		unique := ctx.Lemma(Statement{
			Binders:    "∀S:set(I). ∀z:(I → A). ∀X:(I → set(A)). ∀i:I.",
			Hypotheses: []string{"i ∉ S"},
			Conclusion: "∀v w:A. ∀g h:(I → A). " +
				"    v ∈ X(i) ∧ " +
				"    g ∈ indexed_functions(S, z, X) ∧ " +
				"    w ∈ X(i) ∧ " +
				"    h ∈ indexed_functions(S, z, X) ∧ " +
				"    «extend»(i, v, g) = «extend»(i, w, h) ⇒ " +
				"    v = w ∧ g = h",
		}, func(
			a *Argument,
			S *Expr[Set[I]],
			z *Expr[Fun[I, A]],
			X *Arrow[I, Set[A]],
			i *Expr[I],
			fresh Fact,
		) {
			a.FixAs[A]("v")
			a.FixAs[A]("w")
			g := a.FixAs[Fun[I, A]]("g")
			h := a.FixAs[Fun[I, A]]("h")
			same := a.Assume()
			atEach := a.Have(
				"equal extensions agree pointwise",
				"∀j:I. COND(j = i, v, g(j)) = COND(j = i, w, h(j))",
				By(Normalized, same))
			a.Do(SplitConj(
				Case(
					"evaluate the extensions at i",
					BySets(atEach.At(i))),
				Case(
					"on S they agree with the original maps",
					Derive(func(b *Argument) {
						onS := b.Have(
							"every coordinate of S is different from i",
							"∀j:I. j ∈ S ⇒ g(j) = h(j)",
							b.ForEach(func(j *Expr[I]) Action {
								return Derive(func(c *Argument) {
									inS := c.Assume()
									c.Show(
										"evaluate the extensions away from i",
										BySets(fresh, inS, atEach.At(j)))
								})
							}))
						b.Show(
							"the normalized maps are determined by their values on S",
							By(same, onS, indexed_functions.IndexedFunctionsExtensional.At(S, z, X, g, h)))
					})),
			))
		})

		return ctx.Theorem(headline, func(
			a *Argument,
			J *Expr[Set[I]],
			z *Expr[Fun[I, A]],
			X *Arrow[I, Set[A]],
			finiteJ, finiteFactors Fact,
		) {
			a.Show(
				"induct over the finite index set",
				ByInduction(finite_set.FiniteInductFresh, finiteJ, Generalizing(finiteFactors),
					Case(
						"with no coordinates there is one map and the product is 1",
						Derive(func(b *Argument) {
							b.Assume()
							product := b.Have(
								"the empty product is one",
								"product(∅, λi:I. card(X(i))) = 1",
								By(NatProductClauses))
							singleton := b.TermAs[Set[Fun[I, A]]]("{z}")
							b.Show(
								"the size of the singleton matches the empty product",
								Simp(Fwd(empty)),
								product.Rw(),
								By(
									cardinality.HasSizeDef.At(singleton, b.TermAs[Nat]("1")),
									cardinality.CardSing.At(z),
									finite_set.FiniteSing.At(z)))
						})),
					Case(
						"a fresh coordinate adds a choice from its own factor",
						Derive(func(b *Argument) {
							i := b.FixAs[I]("i")
							S := b.FixAs[Set[I]]("S")
							parts := b.Conjuncts(
								b.Assume(),
								"the size formula on S",
								"i is new",
								"S is finite")
							factors := b.Assume()
							oldFactors := b.Have(
								"all old factors remain finite",
								"∀j:I. j ∈ S ⇒ finite(X(j))",
								b.ForEach(func(j *Expr[I]) Action {
									return Derive(func(c *Argument) {
										inS := c.Assume()
										c.Show(
											"j lies in the enlarged index set",
											BySets(inS, factors.At(j)))
									})
								}))
							oldSize := b.Have(
								"the induction hypothesis counts maps on S",
								"has_size(indexed_functions(S, z, X), product(S, λj:I. card(X(j))))",
								By(parts[0], oldFactors))
							newSize := b.Have(
								"the new factor is finite, so it has size card(X(i))",
								"has_size(X(i), card(X(i)))",
								BySets(
									factors.At(i),
									cardinality.HasSizeDef.At(b.TermAs[Set[A]]("X(i)"), b.TermAs[Nat]("card(X(i))"))))
							enlarged := b.Have(
								"the independent choices give the product of the two sizes",
								"has_size(«extensions»(i, S), card(X(i)) * product(S, λj:I. card(X(j))))",
								By(
									newSize,
									oldSize,
									parts[1],
									At(unique, S, z, X, i),
									cardinality.HasSizeProductImage.At(
										b.TermAs[Fun2[A, Fun[I, A], Fun[I, A]]]("«extend»(i)"),
										b.TermAs[Set[A]]("X(i)"),
										b.TermAs[Set[Fun[I, A]]]("indexed_functions(S, z, X)"),
										b.TermAs[Nat]("card(X(i))"),
										b.TermAs[Nat]("product(S, λj:I. card(X(j)))"))))
							image := b.Have(
								"the assembled maps are exactly the enlarged family",
								"indexed_functions(insert(i, S), z, X) = «extensions»(i, S)",
								By(parts[1], At(extensions, S, z, X, i)))
							product := b.Have(
								"the product picks up the factor at i",
								"product(insert(i, S), λj:I. card(X(j))) = card(X(i)) * product(S, λj:I. card(X(j)))",
								BySets(parts[1], parts[2], NatProductClauses))
							b.Show(
								"substitute the size and the set of extensions",
								By(enlarged, image, product))
						})),
				))
		})
	}),
})}
