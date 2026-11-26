// basis.go — a basis adapted to a finite filtration whose steps have dimension
// at most one, built by induction along the filtration: a step of dimension
// one contributes one new vector and an equal step contributes none.

package filtered_space

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/linear_independence"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// FilteredSpaceAdaptedBasis — a finite filtration with steps of dimension at most
// one has a basis with distinct entry layers: extend a basis one step at a time,
// assigning the current layer precisely when a new vector is needed.
var FilteredSpaceAdaptedBasis = filteredSpaceAdaptedBasisThm{family.Add(registry.ProofEntry{
	Name: "FilteredSpaceAdaptedBasis",
	Key:  "prop_8a3a447ca4cc6267",
	Build: family.Sections(Statement{
		Binders: "∀K:field_on(A). ∀M:module_ops(A, B). ∀F:(num → set(B)). ∀r:num.",
		Hypotheses: []string{
			"module_on(field_ring(K), M)",
			"finite_dimensional(field_ring(K), M)",
			"F(0) = {M.zero}",
			"F(r) = M.carrier",
			"∀i:num. i ≤ r ⇒ submodule(field_ring(K), M, F(i))",
			"∀i:num. " +
				"    i < r ⇒ " +
				"    F(i) ⊆ F(i + 1) ∧ " +
				"    module_dim(field_ring(K), restrict_module(M, F(i + 1))) ≤ " +
				"    module_dim(field_ring(K), restrict_module(M, F(i))) + 1",
		},
		Conclusion: "∃E:set(B). ∃layer:(B → num). " +
			"    finite(E) ∧ " +
			"    module_basis(field_ring(K), M, E) ∧ " +
			"    injective_on(E, layer) ∧ " +
			"    (∀e:B. e ∈ E ⇒ 0 < layer(e) ∧ layer(e) ≤ r ∧ e ∈ F(layer(e)) ∧ e ∉ F(layer(e) - 1)) ∧ " +
			"    (∀i:num. i ≤ r ⇒ module_span(field_ring(K), M, {e:B | e ∈ E ∧ layer(e) ≤ i}) = F(i))",
		Abbrev: Abbrev{
			// E is independent and spans F(n), and its labels are the entry layers that recover each piece up to n.
			{Name: "adapted", Text: "λE:set(B). λlayer:(B → num). λn:num. " +
				"    finite(E) ∧ " +
				"    module_independent(field_ring(K), M, E) ∧ " +
				"    module_span(field_ring(K), M, E) = F(n) ∧ " +
				"    injective_on(E, layer) ∧ " +
				"    (∀e:B. e ∈ E ⇒ 0 < layer(e) ∧ layer(e) ≤ n ∧ e ∈ F(layer(e)) ∧ e ∉ F(layer(e) - 1)) ∧ " +
				"    (∀i:num. i ≤ n ⇒ module_span(field_ring(K), M, {e:B | e ∈ E ∧ layer(e) ≤ i}) = F(i))"},
		},
	},
		func(ctx *Script, headline string) *GoalStackNode {
			extend := ctx.Lemma(Statement{
				Binders: "∀K:field_on(A). ∀M:module_ops(A, B). ∀U W E:set(B).",
				Hypotheses: []string{
					"module_on(field_ring(K), M)",
					"submodule(field_ring(K), M, U)",
					"submodule(field_ring(K), M, W)",
					"U ⊆ W",
					"finite_dimensional(field_ring(K), restrict_module(M, W))",
					"finite(E)",
					"module_independent(field_ring(K), M, E)",
					"module_span(field_ring(K), M, E) = U",
					"module_dim(field_ring(K), restrict_module(M, W)) ≤ " +
						"module_dim(field_ring(K), restrict_module(M, U)) + 1",
				},
				Conclusion: "module_span(field_ring(K), M, E) = W ∨ " +
					"(∃e:B. " +
					"    e ∈ W ∧ " +
					"    e ∉ U ∧ " +
					"    e ∉ E ∧ " +
					"    module_independent(field_ring(K), M, insert(e, E)) ∧ " +
					"    module_span(field_ring(K), M, insert(e, E)) = W)",
			}, func(
				a *Argument,
				K field.FieldFact[on.K],
				M *Expr[ModuleOps[A, B]],
				U, W, E *Expr[Set[B]],
				given Fact,
			) {
				data := a.Conjuncts(
					given,
					"M is a module",
					"U is a submodule",
					"W is a submodule",
					"U lies in W",
					"W is finite dimensional",
					"E is finite",
					"E is independent",
					"E spans U",
					"the dimension increases by at most one")
				onM, subU, subW, nested := data[0], data[1], data[2], data[3]
				finiteW, finiteE, independentE, spanE, growth := data[4], data[5], data[6], data[7], data[8]
				R := a.TermAs[module_record.RingOps[A]]("field_ring(K)")
				inv := a.TermAs[Fun[A, A]]("K.inv")
				MW := a.TermAs[ModuleOps[A, B]]("restrict_module(M, W)")
				MU := a.TermAs[ModuleOps[A, B]]("restrict_module(M, U)")
				scalars := field.FieldRingSubfield.Read(K)
				onW := a.Have(
					"E lies in W and is independent in the module W",
					"E ⊆ W ∧ "+
						"module_independent(field_ring(K), restrict_module(M, W), E) ∧ "+
						"module_on(field_ring(K), restrict_module(M, W))",
					By(
						spanE,
						onM,
						nested,
						independentE,
						subW,
						submodule.SubsetSpan.At(R, M, E),
						submodule.SubmoduleSubset.At(R, M, W),
						linear_independence.IndependentRestrict.At(R, M, W, E),
						submodule.SubmoduleModuleOn.At(R, M, W),
						set_order.SubsetTrans))
				D, extension := a.ObtainAs[Set[B]](
					"extend E to a basis of W",
					"∃D:set(B). E ⊆ D ∧ module_basis(field_ring(K), restrict_module(M, W), D)",
					By(onW, scalars, linear_independence.BasisExtends.At(R, MW, inv, E)),
					Named("D"))
				basisW := a.Have(
					"the extended basis is finite of size the dimension of W, independent in M, and spans W",
					"finite(D) ∧ "+
						"card(D) = module_dim(field_ring(K), restrict_module(M, W)) ∧ "+
						"module_independent(field_ring(K), M, D) ∧ "+
						"module_span(field_ring(K), M, D) = W",
					By(
						finiteW,
						onM,
						extension,
						onW,
						scalars,
						subW,
						module_dimension.FiniteDimensionalBasis.At(R, MW, inv, D),
						linear_independence.BasisRestrict.At(R, M, W, D)))
				dimensionU := a.Have(
					"the size of E is the dimension of U",
					"module_dim(field_ring(K), restrict_module(M, U)) = card(E)",
					By(
						finiteE,
						spanE,
						onM,
						independentE,
						scalars,
						subU,
						submodule.SubmoduleModuleOn.At(R, M, U),
						linear_independence.BasisRestrict.At(R, M, U, E),
						module_dimension.DimBasis.At(R, MU, inv, E)))
				different := a.Unless(
					a.TermAs[Bool]("D = E").Core(),
					"E already spans W",
					Given(func(b *Argument, same Fact) {
						b.Show(
							"the old basis spans W",
							By(Normalized, same, basisW))
					}))
				e, fresh := a.ObtainAs[B](
					"choose a vector added by the extension",
					"∃e:B. e ∈ D ∧ e ∉ E",
					BySets(different, extension),
					Named("e"))
				count := a.Have(
					"one new vector reaches the size of D",
					"card(D) ≤ card(insert(e, E))",
					ByArith(finiteE, growth, dimensionU, fresh, basisW, cardinality.InsertCountsOneMore.At(E, e)))
				whole := a.Have(
					"the enlargement is the whole extended basis",
					"insert(e, E) = D",
					BySets(
						count,
						fresh,
						extension,
						basisW,
						cardinality.CardSubsetLe.At(a.TermAs[Set[B]]("insert(e, E)"), D)))
				nontrivial := a.Have(
					"the scalar one is nonzero",
					"field_ring(K).one ≠ field_ring(K).zero",
					By(
						field.OneNotZeroOn.Read(K),
						field.FieldRingDef,
						module_record.RingOneDef,
						module_record.RingZeroDef))
				basis := a.Have(
					"the enlarged independent set spans W",
					"module_independent(field_ring(K), M, insert(e, E)) ∧ "+
						"module_span(field_ring(K), M, insert(e, E)) = W",
					By(Normalized, whole, basisW))
				outside := a.Have(
					"the new vector is outside the old span",
					"e ∉ module_span(field_ring(K), M, E)",
					By(nontrivial, onM, fresh, basis, linear_independence.IndependentInsertOutsideSpan.At(R, M, E, e)))
				a.Show(
					"the extension adds exactly one vector outside U",
					Right(),
					Witness(e),
					BySets(outside, spanE, fresh, basisW, basis, submodule.SubsetSpan.At(R, M, D)))
			})

			advance := ctx.Lemma(Statement{
				Binders: "∀K:field_on(A). " +
					"∀M:module_ops(A, B). " +
					"∀F:(num → set(B)). " +
					"∀n:num. " +
					"∀E:set(B). " +
					"∀layer:(B → num).",
				Hypotheses: []string{
					"module_on(field_ring(K), M)",
					"finite_dimensional(field_ring(K), M)",
					"submodule(field_ring(K), M, F(n))",
					"submodule(field_ring(K), M, F(n + 1))",
					"F(n) ⊆ F(n + 1)",
					"module_dim(field_ring(K), restrict_module(M, F(n + 1))) ≤ " +
						"module_dim(field_ring(K), restrict_module(M, F(n))) + 1",
					"«adapted»(E, layer, n)",
				},
				Conclusion: "∃D:set(B). ∃label:(B → num). «adapted»(D, label, n + 1)",
			}, func(
				a *Argument,
				K field.FieldFact[on.K],
				M *Expr[ModuleOps[A, B]],
				F *Arrow[Nat, Set[B]],
				n *Expr[Nat],
				given Fact,
				E *Expr[Set[B]],
				layer *Expr[Fun[B, Nat]],
				stage Fact,
			) {
				data := a.Conjuncts(
					given,
					"M is a module",
					"M is finite dimensional",
					"the piece at n is a submodule",
					"the piece at n + 1 is a submodule",
					"the piece at n lies in the next",
					"the dimension increases by at most one")
				onM, finiteM, lower, upper, nested, growth := data[0], data[1], data[2], data[3], data[4], data[5]
				old := a.Conjuncts(
					stage,
					"E is finite",
					"E is independent",
					"E spans the piece at n",
					"the old labels are injective",
					"each old vector has its stated entry layer",
					"the old labels recover each piece through n")
				finiteE, independentE, oldSpan, injective, entry, spans :=
					old[0], old[1], old[2], old[3], old[4], old[5]
				R := a.TermAs[module_record.RingOps[A]]("field_ring(K)")
				inv := a.TermAs[Fun[A, A]]("K.inv")
				next := a.TermAs[Nat]("n + 1")
				enlargement := a.Have(
					"a basis of the next piece that keeps the old labels "+
						"and labels each new vector n + 1 is adapted there",
					Statement{
						Binders: "∀D:set(B). ∀label:(B → num).",
						Hypotheses: []string{
							"finite(D)",
							"module_independent(field_ring(K), M, D)",
							"module_span(field_ring(K), M, D) = F(n + 1)",
							"injective_on(D, label)",
							"∀v:B. v ∈ E ⇒ v ∈ D ∧ label(v) = layer(v)",
							"∀v:B. v ∈ D ∧ v ∉ E ⇒ label(v) = n + 1 ∧ v ∈ F(n + 1) ∧ v ∉ F(n)",
						},
						Conclusion: "«adapted»(D, label, n + 1)",
					},
					Derive(func(b *Argument) {
						b.FixAs[Set[B]]("D")
						b.FixAs[Fun[B, Nat]]("label")
						parts := b.Conjuncts(
							b.Assume(),
							"D is finite",
							"D is independent",
							"D spans the next piece",
							"the new labels are injective",
							"D keeps E and its labels",
							"each new vector enters at the next stage")
						finiteD, independentD, nextSpan, injectiveD, keeps, fresh :=
							parts[0], parts[1], parts[2], parts[3], parts[4], parts[5]
						entries := b.Have(
							"each vector of D enters at its label",
							"∀v:B. v ∈ D ⇒ 0 < label(v) ∧ label(v) ≤ n + 1 ∧ v ∈ F(label(v)) ∧ v ∉ F(label(v) - 1)",
							Derive(func(c *Argument) {
								v := c.FixAs[B]("v")
								vInD := c.Assume()
								c.Cases(c.TermAs[Bool]("v ∈ E"))
								c.When(
									"an old vector keeps its entry layer",
									func(d *Argument, isOld Fact) {
										d.Show(
											"the retained label still records the entry layer",
											ByArith(isOld, keeps.At(v), entry.At(v)))
									})
								c.Otherwise(
									"a new vector enters at the next stage",
									func(d *Argument, isNew Fact) {
										facts := d.Conjuncts(
											GroupPremises(vInD, isNew, fresh.At(v)),
											"its label is n + 1",
											"it belongs to the next piece",
											"it is outside the piece at n")
										atNew, inNext, outside := facts[0], facts[1], facts[2]
										previous := d.Have(
											"the preceding label is n",
											"label(v) - 1 = n",
											ByArith(atNew))
										d.Show(
											"the new vector belongs to the next piece and not the preceding piece",
											ByArith(atNew, previous, inNext, outside))
									})
							}))
						recovers := b.Have(
							"the labels recover each piece through n + 1",
							"∀i:num. i ≤ n + 1 ⇒ module_span(field_ring(K), M, {v:B | v ∈ D ∧ label(v) ≤ i}) = F(i)",
							Derive(func(c *Argument) {
								i := c.FixAs[Nat]("i")
								below := c.Assume()
								c.Cases(c.TermAs[Bool]("i ≤ n"))
								c.When(
									"a piece through n selects exactly the old selected vectors",
									func(d *Argument, earlier Fact) {
										excluded := d.Have(
											"no new vector is selected",
											"∀v:B. v ∈ D ∧ v ∉ E ⇒ ¬(label(v) ≤ i)",
											ByArith(earlier, fresh))
										selection := d.Have(
											"the selected subset is the old one",
											"{v:B | v ∈ D ∧ label(v) ≤ i} = {v:B | v ∈ E ∧ layer(v) ≤ i}",
											BySets(keeps, excluded))
										d.Show(
											"the old selection spans this piece",
											By(selection, earlier, spans.At(i)))
									})
								c.Otherwise(
									"the next stage selects all of D",
									func(d *Argument, later Fact) {
										atNext := d.Have(
											"this stage is the next stage",
											"i = n + 1",
											ByArith(later, below))
										all := d.Have(
											"every label is at most i, so the selected subset is D",
											"{v:B | v ∈ D ∧ label(v) ≤ i} = D",
											BySets(atNext, entries))
										d.Show(
											"D spans the next piece",
											By(all, atNext, nextSpan))
									})
							}))
						b.Show(
							"D and its labels meet every clause",
							By(finiteD, independentD, nextSpan, injectiveD, entries, recovers))
					}))
				finiteNext := a.Have(
					"the next filtration piece is finite dimensional",
					"finite_dimensional(field_ring(K), restrict_module(M, F(n + 1)))",
					By(
						finiteM,
						onM,
						upper,
						field.FieldRingSubfield.Read(K),
						module_dimension.SubmoduleDim.At(R, M, inv, F.Apply(next))))
				alternative := a.Have(
					"the next piece needs at most one new vector",
					"module_span(field_ring(K), M, E) = F(n + 1) ∨ "+
						"(∃e:B. "+
						"    e ∈ F(n + 1) ∧ "+
						"    e ∉ F(n) ∧ "+
						"    e ∉ E ∧ "+
						"    module_independent(field_ring(K), M, insert(e, E)) ∧ "+
						"    module_span(field_ring(K), M, insert(e, E)) = F(n + 1))",
					By(
						onM,
						finiteE,
						independentE,
						oldSpan,
						lower,
						upper,
						nested,
						growth,
						finiteNext,
						Read(extend, K).At(M, F.Apply(n), F.Apply(next), E)))
				a.Do(alternative.SplitDisj(
					LeftHolds(
						"the old basis already spans the next piece",
						Given(func(b *Argument, sameSpan Fact) {
							b.Take(E)
							b.Take(layer)
							b.Show(
								"retain the old basis and labels",
								By(Normalized, finiteE, independentE, sameSpan, injective, enlargement.At(E, layer)))
						})),
					RightHolds(
						"a new vector spans the next piece together with E",
						Given(func(b *Argument, newVector Fact) {
							_, enlarged := b.UnpackAs[B](newVector, "e")
							nextLayer, layerDef := b.LetAs[Fun[B, Nat]]("nextLayer", "λv:B. COND(v = e, n + 1, layer(v))")
							values := b.Have(
								"retain old labels and assign the new vector the next stage",
								"nextLayer(e) = n + 1 ∧ (∀v:B. v ∈ E ⇒ nextLayer(v) = layer(v))",
								By(Normalized, layerDef, enlarged))
							labels := b.Conjuncts(
								values,
								"the new vector has the next label",
								"the labels agree on E")
							atNew, agree := labels[0], labels[1]
							inserted := b.TermAs[Set[B]]("insert(e, E)")
							separate := b.Have(
								"the new label differs from every old label",
								"∀v:B. v ∈ E ⇒ nextLayer(v) ≠ nextLayer(e)",
								ByArith(atNew, agree, entry))
							injectiveNext := b.Have(
								"old injectivity and separation give injectivity on the insertion",
								"injective_on(insert(e, E), nextLayer)",
								BySets(
									injective,
									agree,
									separate,
									functions.InjectiveOnDef.At(E, layer),
									functions.InjectiveOnDef.At(inserted, nextLayer)))
							finiteInserted := b.Have(
								"one insertion preserves finiteness",
								"finite(insert(e, E))",
								By(finiteE, finite_set.FiniteRules))
							keeps := b.Have(
								"the insertion keeps E and its labels",
								"∀v:B. v ∈ E ⇒ v ∈ insert(e, E) ∧ nextLayer(v) = layer(v)",
								BySets(agree))
							fresh := b.Have(
								"the only new vector is the one inserted, at the next stage",
								"∀v:B. v ∈ insert(e, E) ∧ v ∉ E ⇒ nextLayer(v) = n + 1 ∧ v ∈ F(n + 1) ∧ v ∉ F(n)",
								BySets(atNew, enlarged))
							b.Take(inserted)
							b.Take(nextLayer)
							b.Show(
								"the enlarged basis realizes the next filtration stage",
								By(
									Normalized,
									finiteInserted,
									enlarged,
									injectiveNext,
									keeps,
									fresh,
									enlargement.At(inserted, nextLayer)))
						}))))
			})

			stages := ctx.Lemma(Statement{
				Binders: "∀K:field_on(A). ∀M:module_ops(A, B). ∀F:(num → set(B)). ∀r n:num.",
				Hypotheses: []string{
					"module_on(field_ring(K), M)",
					"finite_dimensional(field_ring(K), M)",
					"F(0) = {M.zero}",
					"∀i:num. i ≤ r ⇒ submodule(field_ring(K), M, F(i))",
					"∀i:num. " +
						"    i < r ⇒ " +
						"    F(i) ⊆ F(i + 1) ∧ " +
						"    module_dim(field_ring(K), restrict_module(M, F(i + 1))) ≤ " +
						"    module_dim(field_ring(K), restrict_module(M, F(i))) + 1",
					"n ≤ r",
				},
				Conclusion: "∃E:set(B). ∃layer:(B → num). «adapted»(E, layer, n)",
			}, func(
				a *Argument,
				K field.FieldFact[on.K],
				M *Expr[ModuleOps[A, B]],
				F *Arrow[Nat, Set[B]],
				r *Expr[Nat],
				given Fact,
				n *Expr[Nat],
			) {
				data := a.Conjuncts(
					given,
					"M is a module",
					"M is finite dimensional",
					"F starts at zero",
					"the filtration pieces are submodules",
					"successive pieces are nested with dimension growth at most one")
				onM, finiteM, start, pieces, steps := data[0], data[1], data[2], data[3], data[4]
				R := a.TermAs[module_record.RingOps[A]]("field_ring(K)")
				a.Induct(n)
				a.Base(
					"the empty basis realizes the zero filtration piece",
					func(b *Argument) {
						b.Assume()
						empty := b.TermAs[Set[B]]("∅")
						zeroLayer := b.TermAs[Fun[B, Nat]]("λe:B. 0")
						b.Take(empty)
						b.Take(zeroLayer)
						b.Show(
							"the empty basis has no labels and spans F at zero",
							SplitConjAll(
								Case(
									"the empty set is finite",
									By(finite_set.FiniteRules)),
								Case(
									"the empty set is independent",
									By(linear_independence.IndependentEmpty.At(R, M))),
								Case(
									"the empty span is F at zero",
									By(Normalized, start, onM, submodule.SpanEmpty.At(R, M))),
								Case(
									"the empty labeling is injective",
									BySets(functions.InjectiveOnDef.At(empty, zeroLayer))),
								Case(
									"there is no vector whose layer must be checked",
									BySets()),
								Case(
									"every stage below zero is zero",
									Derive(func(c *Argument) {
										c.FixAs[Nat]("i")
										below := c.Assume()
										atZero := c.Have(
											"the only stage below zero is zero",
											"i = 0",
											ByArith(below))
										selection := c.Have(
											"the selected subset of the empty basis is empty",
											"{e:B | e ∈ ∅ ∧ 0 ≤ i} = ∅",
											BySets())
										c.Show(
											"the selected span is F at zero",
											By(Normalized, selection, atZero, start, onM, submodule.SpanEmpty.At(R, M)))
									}))))
					})
				a.Step(
					"one stage extends the adapted basis",
					func(b *Argument, ih Fact) {
						successor := b.Have(
							"the successor of n is the next stage n + 1",
							"suc(n) = n + 1",
							By(nat_arith.Add1))
						b.Do(successor.Rw())
						nextBound := b.Assume()
						bounds := b.Have(
							"the preceding stage is below r",
							"n ≤ r ∧ n < r",
							ByArith(nextBound))
						E, layer, stage := b.Obtain2As[Set[B], Fun[B, Nat]](
							"use the adapted basis at the preceding stage",
							"∃E:set(B). ∃layer:(B → num). «adapted»(E, layer, n)",
							By(ih, bounds),
							Named("E", "layer"))
						next := b.TermAs[Nat]("n + 1")
						b.Show(
							"it extends to the next stage",
							By(
								onM,
								finiteM,
								nextBound,
								bounds,
								stage,
								pieces.At(n),
								pieces.At(next),
								steps.At(n),
								Read(advance, K).At(M, F, n, E, layer)))
					})
			})
			return ctx.Theorem(headline, func(
				a *Argument,
				K field.FieldFact[on.K],
				M *Expr[ModuleOps[A, B]],
				F *Arrow[Nat, Set[B]],
				r *Expr[Nat],
				given Fact,
			) {
				R := a.TermAs[module_record.RingOps[A]]("field_ring(K)")
				E, layer, adapted := a.Obtain2As[Set[B], Fun[B, Nat]](
					"take the adapted basis at the final stage",
					"∃E:set(B). ∃layer:(B → num). «adapted»(E, layer, r)",
					ByArith(given, Read(stages, K).At(M, F, r, r)),
					Named("E", "layer"))
				a.Take(E)
				a.Take(layer)
				a.Show(
					"the final filtration piece is M, so its adapted independent set is a basis",
					By(Normalized, adapted, given, linear_independence.ModuleBasisDef.At(R, M, E)))
			})
		}),
})}
