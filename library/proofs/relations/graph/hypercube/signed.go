package hypercube

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// cubeBlockEntryDef places M and its negative on the two diagonal blocks.
// Matching vertices in opposite slices receive coefficient one.
var cubeBlockEntryDef = cubeBlockEntryDefThm{family.Define(registry.DefEntry{
	Name:  "cubeBlockEntryDef",
	Key:   "prop_fae5508d10375e7",
	Const: "cube_block_entry",
	Type:  "A → (set(A) → set(A) → real) → set(A) → set(A) → real",
	Equations: []string{
		"∀i:A. ∀M:(set(A) → set(A) → real). ∀X Y:set(A). " +
			"    cube_block_entry(i, M, X, Y) = " +
			"    COND(i ∈ X, " +
			"        COND(i ∈ Y, -M(delete(X, i), delete(Y, i)), COND(delete(X, i) = Y, &1, &0)), " +
			"        COND(i ∈ Y, COND(X = delete(Y, i), &1, &0), M(X, Y)))",
	},
})}

// cubeActionDef sums a matrix row against a function on the subsets of S.
var cubeActionDef = cubeActionDefThm{family.Define(registry.DefEntry{
	Name:  "cubeActionDef",
	Key:   "prop_6cb6d78f129262a9",
	Const: "cube_action",
	Type:  "set(A) → (set(A) → set(A) → real) → (set(A) → real) → set(A) → real",
	Equations: []string{
		"∀S:set(A). ∀M:(set(A) → set(A) → real). ∀v:(set(A) → real). ∀X:set(A). " +
			"    cube_action(S, M, v, X) = Σ_{Y∈{Y:set(A) | Y ⊆ S}} M(X, Y) * v(Y)",
	},
})}

// cubeSigningDef requires signs on the edges and zeroes on the other pairs of vertices.
var cubeSigningDef = cubeSigningDefThm{family.Define(registry.DefEntry{
	Name:  "cubeSigningDef",
	Key:   "prop_78d57412931a294",
	Const: "cube_signing",
	Type:  "set(A) → (set(A) → set(A) → real) → bool",
	Equations: []string{
		"∀S:set(A). ∀M:(set(A) → set(A) → real). " +
			"    cube_signing(S, M) ⇔ " +
			"    ∀X Y:set(A). " +
			"        X ⊆ S ∧ Y ⊆ S ⇒ " +
			"        (cube_adjacent(S, X, Y) ⇒ M(X, Y) = &1 ∨ M(X, Y) = -&1) ∧ " +
			"        (¬cube_adjacent(S, X, Y) ⇒ M(X, Y) = &0)",
	},
})}

// cubeSquareDef says that two applications of the operator multiply every coordinate by r.
var cubeSquareDef = cubeSquareDefThm{family.Define(registry.DefEntry{
	Name:  "cubeSquareDef",
	Key:   "prop_74e85a4e7b167cf8",
	Const: "cube_square",
	Type:  "set(A) → (set(A) → set(A) → real) → real → bool",
	Equations: []string{
		"∀S:set(A). ∀M:(set(A) → set(A) → real). ∀r:real. " +
			"    cube_square(S, M, r) ⇔ " +
			"    ∀v:(set(A) → real). ∀X:set(A). X ⊆ S ⇒ cube_action(S, M, cube_action(S, M, v), X) = r * v(X)",
	},
})}

// BlockEntries gives the four blocks at a pair of vertices missing the new coordinate.
var BlockEntries = blockEntriesThm{family.Add(registry.ProofEntry{
	Name: "BlockEntries",
	Key:  "prop_24b58ecc41d5289f",
	Build: family.Theorem(Statement{
		Binders: "∀i:A. ∀M:(set(A) → set(A) → real). ∀X Y:set(A).",
		Hypotheses: []string{
			"i ∉ X",
			"i ∉ Y",
		},
		Conclusion: "cube_block_entry(i, M, X, Y) = M(X, Y) ∧ " +
			"cube_block_entry(i, M, X, insert(i, Y)) = COND(X = Y, &1, &0) ∧ " +
			"cube_block_entry(i, M, insert(i, X), Y) = COND(X = Y, &1, &0) ∧ " +
			"cube_block_entry(i, M, insert(i, X), insert(i, Y)) = -M(X, Y)",
	},
		func(
			a *Argument,
			i *Expr[A],
			M *Arrow2[Set[A], Set[A], Real],
			X, Y *Expr[Set[A]],
			missesX, missesY Fact,
		) {
			slices := a.Have(
				"insertion marks each upper vertex and deletion recovers its lower copy",
				"delete(insert(i, X), i) = X ∧ delete(insert(i, Y), i) = Y ∧ i ∈ insert(i, X) ∧ i ∈ insert(i, Y)",
				BySets(missesX, missesY))
			a.Show(
				"the two membership tests select the corresponding block",
				Simp(Fwd(cubeBlockEntryDef)),
				ByArith(missesX, missesY, slices))
		}),
})}

// AdjacentSlices identifies the two horizontal copies of the old graph.
// A vertical edge joins exactly the two copies of a single vertex.
var AdjacentSlices = adjacentSlicesThm{family.Add(registry.ProofEntry{
	Name: "AdjacentSlices", Key: "prop_12e04dcf7f6f412d",
	Build: family.Theorem(Statement{
		Binders:    "∀i:A. ∀S X Y:set(A).",
		Hypotheses: []string{"i ∉ S", "X ⊆ S", "Y ⊆ S"},
		Conclusion: "(cube_adjacent(insert(i, S), X, Y) ⇔ cube_adjacent(S, X, Y)) ∧ " +
			"(cube_adjacent(insert(i, S), X, insert(i, Y)) ⇔ X = Y) ∧ " +
			"(cube_adjacent(insert(i, S), insert(i, X), Y) ⇔ X = Y) ∧ " +
			"(cube_adjacent(insert(i, S), insert(i, X), insert(i, Y)) ⇔ cube_adjacent(S, X, Y))",
	}, func(
		a *Argument,
		i *Expr[A],
		S, X, Y *Expr[Set[A]],
		fresh, inX, inY Fact,
	) {
		missing := a.Have(
			"both lower vertices miss the new coordinate",
			"i ∉ X ∧ i ∉ Y",
			BySets(fresh, inX, inY))
		edges := a.Have(
			"a coordinate flip either joins opposite copies or stays in one slice",
			"∀j:A. "+
				"    ((j ∈ insert(i, S) ∧ Y = set_toggle(j, X)) ⇔ j ∈ S ∧ Y = set_toggle(j, X)) ∧ "+
				"    ((j ∈ insert(i, S) ∧ insert(i, Y) = set_toggle(j, X)) ⇔ j = i ∧ X = Y) ∧ "+
				"    ((j ∈ insert(i, S) ∧ Y = set_toggle(j, insert(i, X))) ⇔ j = i ∧ X = Y) ∧ "+
				"    ((j ∈ insert(i, S) ∧ insert(i, Y) = set_toggle(j, insert(i, X))) ⇔ "+
				"        j ∈ S ∧ Y = set_toggle(j, X))",
			Derive(func(b *Argument) {
				j := b.FixAs[A]("j")
				b.Cases(b.Term("j = i"))
				b.When(
					"flipping the new coordinate switches between the two copies",
					func(c *Argument, same Fact) {
						c.Do(same.Rw())
						up := c.Have(
							"the flip inserts i into the lower vertex",
							"set_toggle(i, X) = insert(i, X)",
							By(missing, set_basic.ToggleWhenAbsent.At(i, X)))
						down := c.Have(
							"the flip removes i from the upper vertex",
							"set_toggle(i, insert(i, X)) = X",
							By(Normalized, up, set_basic.ToggleInvolution.At(i, X)))
						c.Do(down.Rw(), up.Rw(), BySets(fresh, inX, inY))
					})
				b.Otherwise(
					"an old coordinate flip preserves which copy a vertex belongs to",
					func(c *Argument, different Fact) {
						parallel := c.Have(
							"the old flip commutes with insertion of the new coordinate",
							"set_toggle(j, insert(i, X)) = insert(i, set_toggle(j, X))",
							By(different, set_basic.ToggleInsertCommute.At(i, j, X)))
						absent := c.Have(
							"the old flip leaves the new coordinate absent",
							"i ∉ set_toggle(j, X)",
							By(missing, different, set_basic.InToggle.At(j, X, i)))
						c.Do(parallel.Rw(), BySets(fresh, inX, inY, absent, different))
					})
			}))
		a.Show(
			"existence of a flipping coordinate gives the four adjacency tests",
			Simp(Fwd(CubeAdjacentDef)),
			Simp(Fwd(edges)),
			Basic())
	}),
})}

// BlockSigning preserves the edge signs when a new coordinate doubles the cube.
var BlockSigning = blockSigningThm{family.Add(registry.ProofEntry{
	Name: "BlockSigning", Key: "prop_d0e7194a51ec3c3e",
	Build: family.Sections(Statement{
		Binders:    "∀i:A. ∀S:set(A). ∀M:(set(A) → set(A) → real).",
		Hypotheses: []string{"i ∉ S", "cube_signing(S, M)"},
		Conclusion: "cube_signing(insert(i, S), cube_block_entry(i, M))",
		Abbrev: Abbrev{
			{Name: "edgeValue", Text: "λU:set(A). λV:set(A). " +
				"    (cube_adjacent(insert(i, S), U, V) ⇒ " +
				"        cube_block_entry(i, M, U, V) = &1 ∨ cube_block_entry(i, M, U, V) = -&1) ∧ " +
				"    (¬cube_adjacent(insert(i, S), U, V) ⇒ cube_block_entry(i, M, U, V) = &0)"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		// A relation true at the four corners of {u, v} × {w, z} is true at every pair (x, y) in it.
		four := ctx.Lemma(
			Statement{
				Binders: "∀P:(A → B → bool). ∀x u v:A. ∀y w z:B.",
				Hypotheses: []string{
					"(x = u ∨ x = v)",
					"(y = w ∨ y = z)",
					"P(u, w)",
					"P(u, z)",
					"P(v, w)",
					"P(v, z)",
				},
				Conclusion: "P(x, y)",
			},
			func(
				a *Argument,
				P *Arrow2[A, B, Bool],
				x, u, v *Expr[A],
				y, w, z *Expr[B],
				h Fact,
			) {
				a.Do(By(h))
			})
		return ctx.Theorem(headline, func(
			a *Argument,
			i *Expr[A],
			S *Expr[Set[A]],
			M *Arrow2[Set[A], Set[A], Real],
			fresh, signing Fact,
		) {
			old := a.Have(
				"the original matrix has precisely the required edge coefficients",
				Statement{
					Binders:    "∀U V:set(A).",
					Hypotheses: []string{"U ⊆ S", "V ⊆ S"},
					Conclusion: "(cube_adjacent(S, U, V) ⇒ M(U, V) = &1 ∨ M(U, V) = -&1) ∧ " +
						"(¬cube_adjacent(S, U, V) ⇒ M(U, V) = &0)",
				},
				By(signing, cubeSigningDef.At(S, M)))
			a.Do(Unfold(cubeSigningDef))
			X := a.FixAs[Set[A]]("X")
			Y := a.FixAs[Set[A]]("Y")
			inside := a.Assume()
			slices := a.Have(
				"each of the four blocks has the signs of the corresponding cube edges",
				Statement{
					Binders:    "∀U V:set(A).",
					Hypotheses: []string{"U ⊆ S", "V ⊆ S"},
					Conclusion: "«edgeValue»(U, V) ∧ " +
						"«edgeValue»(U, insert(i, V)) ∧ " +
						"«edgeValue»(insert(i, U), V) ∧ " +
						"«edgeValue»(insert(i, U), insert(i, V))",
				},
				Derive(func(b *Argument) {
					U := b.FixAs[Set[A]]("U")
					V := b.FixAs[Set[A]]("V")
					vertices := b.Assume()
					missing := b.Have(
						"the old vertices both miss i",
						"i ∉ U ∧ i ∉ V",
						BySets(fresh, vertices))
					b.Show(
						"the diagonal blocks keep or negate old signs and the identity blocks sign vertical edges",
						ByArith(
							fresh,
							old.At(U, V),
							vertices,
							missing,
							BlockEntries.At(i, M, U, V),
							AdjacentSlices.At(i, S, U, V)))
				}))
			cover := a.Have(
				"deleting i identifies the old vertices below either chosen endpoint",
				"(delete(X, i) ⊆ S ∧ (X = delete(X, i) ∨ X = insert(i, delete(X, i)))) ∧ "+
					"(delete(Y, i) ⊆ S ∧ (Y = delete(Y, i) ∨ Y = insert(i, delete(Y, i))))",
				BySets(inside))
			u, w := a.Term("delete(X, i)"), a.Term("delete(Y, i)")
			oldPair := a.Have(
				"the four values above these two old endpoints have the required signs",
				"«edgeValue»(delete(X, i), delete(Y, i)) ∧ "+
					"«edgeValue»(delete(X, i), insert(i, delete(Y, i))) ∧ "+
					"«edgeValue»(insert(i, delete(X, i)), delete(Y, i)) ∧ "+
					"«edgeValue»(insert(i, delete(X, i)), insert(i, delete(Y, i)))",
				By(cover, slices.At(u, w)))
			a.Show(
				"the two endpoints belong to one of those four blocks",
				By(
					cover,
					oldPair,
					At(
						four,
						a.Term("«edgeValue»"),
						X,
						u,
						a.Term("insert(i, delete(X, i))"),
						Y,
						w,
						a.Term("insert(i, delete(Y, i))"))))
		})
	}),
})}

// SumInsert splits a sum on the enlarged cube into its two sums on the
// old cube. In the second sum each subset carries the new coordinate.
var SumInsert = sumInsertThm{family.Add(registry.ProofEntry{
	Name: "SumInsert",
	Key:  "prop_bcc316b320afa4a4",
	Build: family.Theorem(Statement{
		Binders:    "∀i:A. ∀S:set(A). ∀f:(set(A) → real).",
		Hypotheses: []string{"finite(S)", "i ∉ S"},
		Conclusion: "sum({X:set(A) | X ⊆ insert(i, S)}, f) = " +
			"sum(«vertices», f) + Σ_{X∈«vertices»} f(insert(i, X))",
		Abbrev: Abbrev{
			{Name: "vertices", Text: "{X:set(A) | X ⊆ S}"},
			{Name: "upper", Text: "image(λX:set(A). insert(i, X), «vertices»)"},
		},
	}, func(a *Argument, i *Expr[A], S *Expr[Set[A]], f *Arrow[Set[A], Real], finiteS, fresh Fact) {
		vertices := a.TermAs[Set[Set[A]]]("«vertices»")
		upper := a.TermAs[Set[Set[A]]]("«upper»")
		insertAt := a.TermAs[Fun[Set[A], Set[A]]]("λX:set(A). insert(i, X)")
		separate := a.Have(
			"the new coordinate separates the two slices",
			"disjoint(«vertices», «upper»)",
			BySets(fresh))
		injective := a.Have(
			"deleting the new coordinate recovers the original vertex",
			"injective_on(«vertices», λX:set(A). insert(i, X))",
			Unfold(functions.InjectiveOnDef),
			BySets(fresh))
		reindex := a.Have(
			"insertion indexes the upper slice by the original vertices",
			"sum(«upper», f) = Σ_{X∈«vertices»} f(insert(i, X))",
			By(injective, real_sum.Image.At(vertices, insertAt, f), functions.ComposeApply))
		finiteVertices := a.Have(
			"a finite coordinate set has finitely many subsets",
			"finite(«vertices»)",
			By(finiteS, finite_set.FinitePowerset.At(S)))
		a.Show(
			"the slices cover the enlarged cube, so their disjoint sums add",
			Simp(Fwd(finite_set.PowersetClauses)),
			By(
				finiteVertices,
				separate,
				reindex,
				finite_set.FiniteImage.At(insertAt, vertices),
				real_sum.Union.At(vertices, upper, f)))
	}),
})}

// BlockAction evaluates a row of the doubled matrix on each slice. Its
// off-diagonal identity blocks return the opposite slice at the same vertex.
var BlockAction = blockActionThm{family.Add(registry.ProofEntry{
	Name: "BlockAction",
	Key:  "prop_6cea6b441a1a2a7b",
	Build: family.Sections(Statement{
		Binders:    "∀i:A. ∀S:set(A). ∀M:(set(A) → set(A) → real). ∀v:(set(A) → real). ∀X:set(A).",
		Hypotheses: []string{"finite(S)", "i ∉ S", "X ⊆ S"},
		Conclusion: "cube_action(insert(i, S), cube_block_entry(i, M), v, X) = " +
			"cube_action(S, M, v, X) + v(insert(i, X)) ∧ " +
			"cube_action(insert(i, S), cube_block_entry(i, M), v, insert(i, X)) = " +
			"v(X) - cube_action(S, M, λY:set(A). v(insert(i, Y)), X)",
		Abbrev: Abbrev{
			{Name: "vertices", Text: "{Y:set(A) | Y ⊆ S}"},
			{Name: "lowerRow", Text: "λY:set(A). cube_block_entry(i, M, X, Y) * v(Y)"},
			{Name: "upperRow", Text: "λY:set(A). cube_block_entry(i, M, insert(i, X), Y) * v(Y)"},
			{Name: "oldRow", Text: "λY:set(A). M(X, Y) * v(Y)"},
			{Name: "upperValues", Text: "λY:set(A). v(insert(i, Y))"},
			{Name: "oldUpperRow", Text: "λY:set(A). M(X, Y) * v(insert(i, Y))"},
			{Name: "matchLower", Text: "λY:set(A). COND(X = Y, &1, &0) * v(Y)"},
			{Name: "matchUpper", Text: "λY:set(A). COND(X = Y, &1, &0) * v(insert(i, Y))"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		identity := ctx.Lemma(Statement{
			Binders:    "∀s:set(A). ∀x:A. ∀v:(A → real).",
			Hypotheses: []string{"x ∈ s"},
			Conclusion: "(Σ_{y∈s} COND(x = y, &1, &0) * v(y)) = v(x)",
		},
			func(a *Argument, s *Expr[Set[A]], x *Expr[A], v *Arrow[A, Real], member Fact) {
				supported := a.Have(
					"only the matching summand survives",
					"∀y:A. COND(x = y, &1, &0) * v(y) = COND(y = x, v(x), &0)",
					Derive(func(b *Argument) {
						b.FixAs[A]("y")
						b.Cases(b.Term("x = y"))
						b.When(
							"the matching coordinate contributes its value",
							func(c *Argument, equal Fact) { c.Do(ByArith(equal)) })
						b.Otherwise(
							"each other coordinate contributes zero",
							func(c *Argument, different Fact) { c.Do(ByArith(different)) })
					}))
				a.Show(
					"the delta sum returns the coordinate at x",
					ByArith(
						supported,
						member,
						real_sum.Delta.At(a.TermAs[Real]("v(x)"), s, x),
						real_sum.CongruenceEverywhere.At(s, a.TermAs[Fun[A, Real]]("λy:A. COND(x = y, &1, &0) * v(y)"),
							a.TermAs[Fun[A, Real]]("λy:A. COND(y = x, v(x), &0)"))))
			})
		return ctx.Theorem(headline, func(
			a *Argument,
			i *Expr[A],
			S *Expr[Set[A]],
			M *Arrow2[Set[A], Set[A], Real],
			v *Arrow[Set[A], Real],
			X *Expr[Set[A]],
			finiteS, fresh, vertex Fact,
		) {
			a.Do(Simp(Fwd(cubeActionDef)))
			vertices := a.TermAs[Set[Set[A]]]("«vertices»")
			lowerRow := a.TermAs[Fun[Set[A], Real]]("«lowerRow»")
			upperRow := a.TermAs[Fun[Set[A], Real]]("«upperRow»")
			lowerPoints := a.Have(
				"the old vertices all miss the new coordinate",
				"X ∈ «vertices» ∧ i ∉ X ∧ (∀Y:set(A). Y ∈ «vertices» ⇒ i ∉ Y)",
				BySets(fresh, vertex))
			entries := a.Have(
				"the four matrix blocks give the contributions from each column",
				Statement{
					Binders:    "∀Y:set(A).",
					Hypotheses: []string{"Y ∈ «vertices»"},
					Conclusion: "«lowerRow»(Y) = «oldRow»(Y) ∧ " +
						"«lowerRow»(insert(i, Y)) = «matchUpper»(Y) ∧ " +
						"«upperRow»(Y) = «matchLower»(Y) ∧ " +
						"«upperRow»(insert(i, Y)) = -«oldUpperRow»(Y)",
				},
				Derive(func(b *Argument) {
					Y := b.FixAs[Set[A]]()
					inCube := b.Assume()
					b.Do(ByArith(inCube, lowerPoints, BlockEntries.At(i, M, X, Y)))
				}))
			lowerOld := a.Have(
				"the lower diagonal block contributes the old row sum",
				"sum(«vertices», «lowerRow») = sum(«vertices», «oldRow»)",
				By(entries, real_sum.Congruence.At(vertices, lowerRow, a.TermAs[Fun[Set[A], Real]]("«oldRow»"))))
			lowerCross := a.Have(
				"the other half of a lower row is a delta on the upper values",
				"(Σ_{Y∈«vertices»} «lowerRow»(insert(i, Y))) = sum(«vertices», «matchUpper»)",
				By(
					entries,
					real_sum.Congruence.At(
						vertices,
						a.TermAs[Fun[Set[A], Real]]("λY:set(A). «lowerRow»(insert(i, Y))"),
						a.TermAs[Fun[Set[A], Real]]("«matchUpper»"))))
			upperCross := a.Have(
				"the lower half of an upper row is a delta on the lower values",
				"sum(«vertices», «upperRow») = sum(«vertices», «matchLower»)",
				By(
					entries,
					real_sum.Congruence.At(vertices, upperRow, a.TermAs[Fun[Set[A], Real]]("«matchLower»"))))
			upperOld := a.Have(
				"the upper diagonal block negates the old row on the upper values",
				"(Σ_{Y∈«vertices»} «upperRow»(insert(i, Y))) = (Σ_{Y∈«vertices»} -«oldUpperRow»(Y))",
				By(
					entries,
					real_sum.Congruence.At(
						vertices,
						a.TermAs[Fun[Set[A], Real]]("λY:set(A). «upperRow»(insert(i, Y))"),
						a.TermAs[Fun[Set[A], Real]]("λY:set(A). -«oldUpperRow»(Y)"))))
			identityAt := ctx.AtTypeVars(identity, TypeBinder.BindA[Set[A]]())
			upperValue := a.Have(
				"the vertical edge in a lower row reads the upper value at X",
				"sum(«vertices», «matchUpper») = v(insert(i, X))",
				By(lowerPoints, At(identityAt, vertices, X, a.Term("«upperValues»"))))
			lowerValue := a.Have(
				"the vertical edge in an upper row reads the lower value at X",
				"sum(«vertices», «matchLower») = v(X)",
				By(lowerPoints, At(identityAt, vertices, X, v)))
			opposite := a.Have(
				"negation commutes with the upper diagonal sum",
				"(Σ_{Y∈«vertices»} -«oldUpperRow»(Y)) = -sum(«vertices», «oldUpperRow»)",
				By(real_sum.Neg.At(a.TermAs[Fun[Set[A], Real]]("«oldUpperRow»"), vertices)))
			a.Show(
				"adding the two halves evaluates each row",
				ByArith(
					finiteS,
					fresh,
					lowerOld,
					lowerCross,
					upperCross,
					upperOld,
					upperValue,
					lowerValue,
					opposite,
					SumInsert.At(i, S, lowerRow),
					SumInsert.At(i, S, upperRow)))
		})
	}),
})}

// ActionLinear distributes a matrix row over a linear combination.
// The inputs need to agree with that combination only on the cube.
var ActionLinear = actionLinearThm{family.Add(registry.ProofEntry{
	Name: "ActionLinear",
	Key:  "prop_841fae956d1ea005",
	Build: family.Theorem(Statement{
		Binders:    "∀S:set(A). ∀M:(set(A) → set(A) → real). ∀f g h:(set(A) → real). ∀r:real. ∀X:set(A).",
		Hypotheses: []string{"finite(S)", "∀Y:set(A). Y ⊆ S ⇒ h(Y) = f(Y) + r * g(Y)"},
		Conclusion: "cube_action(S, M, h, X) = cube_action(S, M, f, X) + r * cube_action(S, M, g, X)",
		Abbrev: Abbrev{
			{Name: "vertices", Text: "{Y:set(A) | Y ⊆ S}"},
			{Name: "first", Text: "λY:set(A). M(X, Y) * f(Y)"},
			{Name: "second", Text: "λY:set(A). M(X, Y) * g(Y)"},
			{Name: "combined", Text: "λY:set(A). M(X, Y) * h(Y)"},
		},
	}, func(
		a *Argument,
		S *Expr[Set[A]],
		M *Arrow2[Set[A], Set[A], Real],
		f, g, h *Arrow[Set[A], Real],
		r *Expr[Real],
		X *Expr[Set[A]],
		finiteS, combine Fact,
	) {
		a.Do(Unfold(cubeActionDef))
		vertices := a.TermAs[Set[Set[A]]]("«vertices»")
		distributes := a.Have(
			"each matrix coefficient distributes across the two terms",
			"∀Y:set(A). Y ∈ «vertices» ⇒ «combined»(Y) = «first»(Y) + r * «second»(Y)",
			Derive(func(b *Argument) {
				Y := b.FixAs[Set[A]]("Y")
				member := b.Assume()
				subset := b.Have(
					"a vertex is a subset of S",
					"Y ⊆ S",
					BySets(member))
				value := b.Have(
					"the input has the stated value at this vertex",
					"h(Y) = f(Y) + r * g(Y)",
					By(combine.At(Y), subset))
				b.Do(value.Rw(), ByArith())
			}))
		finiteVertices := a.Have(
			"there are finitely many summands",
			"finite(«vertices»)",
			By(finiteS, finite_set.FinitePowerset.At(S)))
		a.Show(
			"addition and scalar multiplication commute with this finite sum",
			By(
				distributes,
				finiteVertices,
				real_sum.Congruence.At(
					vertices,
					a.TermAs[Fun[Set[A], Real]]("«combined»"),
					a.TermAs[Fun[Set[A], Real]]("λY:set(A). «first»(Y) + r * «second»(Y)")),
				real_sum.Add.At(
					a.TermAs[Fun[Set[A], Real]]("«first»"),
					a.TermAs[Fun[Set[A], Real]]("λY:set(A). r * «second»(Y)"),
					vertices),
				real_sum.ScalarLeft.At(r, a.TermAs[Fun[Set[A], Real]]("«second»"), vertices)))
	}),
})}

// BlockSquare doubles a signed matrix and raises its square scalar by one.
// The old square acts on each slice and the mixed terms cancel.
var BlockSquare = blockSquareThm{family.Add(registry.ProofEntry{
	Name: "BlockSquare",
	Key:  "prop_d09b07e0d0cd178c",
	Build: family.Theorem(Statement{
		Binders:    "∀i:A. ∀S:set(A). ∀M:(set(A) → set(A) → real). ∀r:real.",
		Hypotheses: []string{"finite(S)", "i ∉ S", "cube_square(S, M, r)"},
		Conclusion: "cube_square(insert(i, S), cube_block_entry(i, M), r + &1)",
		Abbrev: Abbrev{
			{Name: "doubled", Text: "cube_action(insert(i, S), cube_block_entry(i, M))"},
			// «upper» and «upperImage» spell v, the vector the body fixes once the square is unfolded.
			{Name: "upper", Text: "λY:set(A). v(insert(i, Y))"},
			{Name: "upperImage", Text: "λY:set(A). «doubled»(v, insert(i, Y))"},
		},
	}, func(
		a *Argument,
		i *Expr[A],
		S *Expr[Set[A]],
		M *Arrow2[Set[A], Set[A], Real],
		r *Expr[Real],
		finiteS, fresh, square Fact,
	) {
		oldSquare := a.Have(
			"the old operator squares to r on each old vertex",
			"∀u:(set(A) → real). ∀Y:set(A). Y ⊆ S ⇒ cube_action(S, M, cube_action(S, M, u), Y) = r * u(Y)",
			By(square, cubeSquareDef.At(S, M, r)))
		a.Do(Simp(Fwd(cubeSquareDef)))
		v := a.FixAs[Fun[Set[A], Real]]("v")
		X := a.FixAs[Set[A]]("X")
		inside := a.Assume()
		// The `&1 *` and `(-&1) *` factors put each slice in ActionLinear's form h = f + r·g.
		once := a.Have(
			"on either slice one application combines the old action with the opposite slice's values",
			Statement{
				Binders:    "∀Y:set(A).",
				Hypotheses: []string{"Y ⊆ S"},
				Conclusion: "«doubled»(v, Y) = cube_action(S, M, v, Y) + &1 * «upper»(Y) ∧ " +
					"«upperImage»(Y) = v(Y) + (-&1) * cube_action(S, M, «upper», Y)",
			},
			Derive(func(b *Argument) {
				Y := b.FixAs[Set[A]]("Y")
				vertex := b.Assume()
				b.Do(ByArith(finiteS, fresh, vertex, BlockAction.At(i, S, M, v, Y)))
			}))
		both := a.Have(
			"squaring on either copy of an old vertex raises its scalar by one",
			Statement{
				Binders:    "∀Z:set(A).",
				Hypotheses: []string{"Z ⊆ S"},
				Conclusion: "«doubled»(«doubled»(v), Z) = (r + &1) * v(Z) ∧ " +
					"«doubled»(«doubled»(v), insert(i, Z)) = (r + &1) * v(insert(i, Z))",
			},
			Derive(func(b *Argument) {
				Z := b.FixAs[Set[A]]("Z")
				vertex := b.Assume()
				w := b.TermAs[Fun[Set[A], Real]]("«doubled»(v)")
				up := b.TermAs[Fun[Set[A], Real]]("«upper»")
				lowerOld := b.Have(
					"linearity expands the old action on the lower image",
					"cube_action(S, M, «doubled»(v), Z) = "+
						"cube_action(S, M, cube_action(S, M, v), Z) + &1 * cube_action(S, M, «upper», Z)",
					By(
						finiteS,
						once,
						ActionLinear.At(
							S, M, b.TermAs[Fun[Set[A], Real]]("cube_action(S, M, v)"), up, w, b.TermAs[Real]("&1"), Z)))
				upperOld := b.Have(
					"linearity expands the action on the upper image with the opposite sign",
					"cube_action(S, M, «upperImage», Z) = "+
						"cube_action(S, M, v, Z) + (-&1) * cube_action(S, M, cube_action(S, M, «upper»), Z)",
					By(
						finiteS,
						once,
						ActionLinear.At(
							S,
							M,
							v,
							b.TermAs[Fun[Set[A], Real]]("cube_action(S, M, «upper»)"),
							b.TermAs[Fun[Set[A], Real]]("«upperImage»"),
							b.TermAs[Real]("-&1"),
							Z)))
				b.Show(
					"the mixed terms cancel in each slice, leaving the old square plus the identity",
					ByArith(
						finiteS,
						fresh,
						vertex,
						once.At(Z),
						oldSquare.At(v, Z),
						oldSquare.At(up, Z),
						lowerOld,
						upperOld,
						BlockAction.At(i, S, M, w, Z)))
			}))
		cover := a.Have(
			"each new vertex is an old vertex or the upper copy of one",
			"X ⊆ S ∨ (delete(X, i) ⊆ S ∧ X = insert(i, delete(X, i)))",
			BySets(inside))
		a.Show(
			"the two slice identities therefore cover the entire enlarged cube",
			By(cover, both.At(X), both.At(a.Term("delete(X, i)"))))
	}),
})}

// SignedCube constructs a signing of a finite cube whose square is the number
// of coordinates times the identity. Each fresh coordinate doubles the matrix.
var SignedCube = signedCubeThm{family.Add(registry.ProofEntry{
	Name: "SignedCube", Key: "prop_24a0d959b47b8a66",
	Build: family.Theorem(Statement{
		Binders: "∀S:set(A).", Hypotheses: []string{"finite(S)"},
		Conclusion: "∃M:(set(A) → set(A) → real). cube_signing(S, M) ∧ cube_square(S, M, &card(S))",
	}, func(a *Argument, S *Expr[Set[A]], finiteS Fact) {
		a.Do(ByInduction(finite_set.FiniteInductFresh, finiteS,
			Case(
				"the zero matrix signs the cube with no coordinates",
				Derive(func(b *Argument) {
					b.Do(Witness(b.Term("λX:set(A). λY:set(A). &0")), SplitConj(
						Case(
							"there is no coordinate available for an edge",
							Unfold(cubeSigningDef),
							Unfold(CubeAdjacentDef),
							BySets()),
						Case(
							"every zero row has zero action",
							Unfold(cubeSquareDef),
							Unfold(cubeActionDef),
							Simp(Fwd(cardinality.CardClauses), Fwd(real_ring.MulLeftZero), Fwd(real_sum.Zero)),
							Basic())))
				})),
			Case(
				"doubling the old matrix signs the cube with an additional coordinate",
				Derive(func(b *Argument) {
					i := b.FixAs[A]("i")
					T := b.FixAs[Set[A]]("T")
					parts := b.Conjuncts(
						b.Assume(),
						"a signing of the old cube",
						"the new coordinate is fresh",
						"the old cube has finitely many coordinates")
					oldSigning, fresh, finiteOld := parts[0], parts[1], parts[2]
					M, old := b.UnpackAs[Fun2[Set[A], Set[A], Real]](oldSigning, "M")
					b.Do(Witness(b.Term("cube_block_entry(i, M)")))
					size := b.Have(
						"the new coordinate increases the cardinality by one",
						"card(insert(i, T)) = suc(card(T))",
						ByArith(finiteOld, fresh, cardinality.CardClauses))
					b.Show(
						"the block signing has exactly that larger square",
						By(
							Normalized,
							finiteOld,
							fresh,
							size,
							old,
							real_ring.OfNumSuc.At(b.TermAs[Nat]("card(T)")),
							BlockSigning.At(i, T, M),
							BlockSquare.At(i, T, M, b.TermAs[Real]("&card(T)"))))
				}))))
	}),
})}
