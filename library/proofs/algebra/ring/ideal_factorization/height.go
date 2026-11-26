package ideal_factorization

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/quotient_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/fractional_ideal"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/quotient_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_ideal"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// FiniteQuotientIdealHeight — a finite quotient bounds the lengths of
// ideal chains: each strict ideal inclusion lowers the index, so every
// step spends at least one from the index of I.
var FiniteQuotientIdealHeight = finiteQuotientIdealHeightThm{family.Add(registry.ProofEntry{
	Name: "FiniteQuotientIdealHeight",
	Key:  "prop_56a60b7e5b9607d3",
	Build: family.Theorem(Statement{
		Binders:    "∀R:comm_ring_on(A). ∀I:set(A).",
		Hypotheses: []string{"ring_ideal(R, I)", "finite(left_cosets(R.add, R.carrier, I))"},
		Conclusion: "finite_ideal_height(R, I)",
	}, func(a *Argument, R comm_ring.CommRingFact[on.R], I *Expr[Set[A]], h Fact) {
		given := a.Conjuncts(
			h,
			"I is an ideal",
			"R modulo I is finite")
		idealI, finiteI := given[0], given[1]
		a.Do(Simp(Fwd(FiniteIdealHeightDef)))
		a.Take(a.TermAs[Nat]("ideal_index(R, I)"))
		a.FixAs[Fun[Nat, Set[A]]]()
		n := a.FixAs[Nat]()
		chain := a.Assume()
		parts := a.Conjuncts(
			a.Unfolded(chain, idealChainDef),
			"the chain begins at I",
			"the chain ends at the carrier",
			"every term of the chain prefix is an ideal",
			"adjacent ideals in the prefix are strictly included")
		start, ideals, advances := parts[0], parts[2], parts[3]
		prefix := a.Have(
			"each chain step spends at least one unit of index",
			Statement{
				Binders: "∀k:num.",
				Hypotheses: []string{
					"k ≤ n",
				},
				Conclusion: "I ⊆ C(k) ∧ " +
					"finite(left_cosets(R.add, R.carrier, C(k))) ∧ " +
					"k + ideal_index(R, C(k)) ≤ ideal_index(R, I)",
			},
			Derive(func(b *Argument) {
				b.Induct("k")
				b.Base(
					"at zero the ideal is I",
					Simp(Fwd(start), Fwd(set_basic.SubsetDef)),
					ByArith(finiteI))
				b.Step(
					"a strict ideal inclusion lowers the remaining index",
					func(c *Argument, ih Fact) {
						within := c.Assume()
						k := c.TermAs[Nat]("k")
						current := c.TermAs[Set[A]]("C(k)")
						next := c.TermAs[Set[A]]("C(suc(k))")
						bounds := c.Have(
							"both adjacent indices lie in the chain prefix",
							"k < n ∧ k ≤ n ∧ suc(k) = k + 1",
							ByArith(within))
						previous := c.Have(
							"the preceding ideal has the induction bounds",
							"I ⊆ C(k) ∧ "+
								"finite(left_cosets(R.add, R.carrier, C(k))) ∧ "+
								"k + ideal_index(R, C(k)) ≤ ideal_index(R, I)",
							By(ih, bounds))
						strict := c.Have(
							"the next ideal strictly contains the preceding ideal",
							"C(k) ⊆ C(suc(k)) ∧ C(k) ≠ C(suc(k))",
							By(Normalized, advances.At(k), bounds))
						integral := c.Have(
							"both adjacent terms are ideals",
							"ring_ideal(R, C(k)) ∧ ring_ideal(R, C(suc(k)))",
							By(ideals, bounds, within))
						containsI := c.Have(
							"the next ideal still contains I",
							"I ⊆ C(suc(k))",
							BySets(previous, strict))
						finiteNext := c.Have(
							"the next quotient is finite",
							"finite(left_cosets(R.add, R.carrier, C(suc(k))))",
							By(
								idealI,
								finiteI,
								containsI,
								integral,
								quotient_ring.FiniteQuotientAboveIdeal.Read(R).At(I, next)))
						decrease := c.Have(
							"strict inclusion lowers the index",
							"ideal_index(R, C(suc(k))) < ideal_index(R, C(k))",
							By(
								previous,
								strict,
								integral,
								quotient_ring.StrictIdealInclusionLowersIndex.Read(R).At(current, next)))
						remaining := c.Have(
							"the decrease pays for the next step",
							"suc(k) + ideal_index(R, C(suc(k))) ≤ ideal_index(R, I)",
							ByArith(previous, decrease))
						c.Show(
							"the prefix bounds hold at the next ideal",
							By(containsI, finiteNext, remaining))
					})
			}))
		a.Show(
			"the chain length is at most the index of I",
			ByArith(prefix.At(n)))
	}),
})}

// FiniteColengthIdealHeight — an ideal I of S whose quotient S/I is a
// finite-dimensional vector space over a subfield k inside S has finite
// height, at most the dimension of S/I over k: each strict step of a chain
// above I adds a nonzero quotient to the dimension.
var FiniteColengthIdealHeight = finiteColengthIdealHeightThm{family.Add(registry.ProofEntry{
	Name: "FiniteColengthIdealHeight",
	Key:  "prop_66702e8d6f775f35",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S k I:set(A).",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"subfield(L, k)",
			"k ⊆ S",
			"ring_ideal(«R», I)",
			"finite_dimensional(«scalars», «quotient»)",
		},
		Conclusion: "finite_ideal_height(«R», I) ∧ " +
			"ideal_height(«R», I) ≤ module_dim(«scalars», «quotient»)",
		Abbrev: Abbrev{
			{Name: "scalars", Text: "restrict_ring(field_ring(L), k)"},
			{Name: "quotient", Text: "quotient_module(restrict_module(regular_module(field_ring(L)), S), I)"},
		},
	}, func(a *Argument, L field.FieldFact[on.L], S, k, I *Expr[Set[A]], h Fact) {
		given := a.Conjuncts(
			h,
			"S is a subring",
			"k is a subfield",
			"k lies in S",
			"I is an ideal of S",
			"S modulo I has finite dimension")
		subringS, subfieldK, kInS, idealI, finiteQuotient :=
			given[0], given[1], given[2], given[3], given[4]
		_, scalarDef := a.LetAs[RingOps[A]]("K", "restrict_ring(field_ring(L), k)")
		M, ambientDef := a.LetAs[module_record.ModuleOps[A, A]]("M", "regular_module(field_ring(L))")
		r := a.TermAs[RingOps[A]]("«R»")
		inv := a.TermAs[Fun[A, A]]("L.inv")
		ringS := a.Have(
			"S is a commutative ring",
			"comm_ring_on(«R»)",
			By(subringS, comm_ring.SubringRingOn.Read(field.RingOn.Read(L)).At(S)))
		ambient := a.Have(
			"the ambient field is a module over k",
			"module_on(K, M)",
			Simp(Fwd(ambientDef), Fwd(scalarDef)),
			By(
				subfieldK,
				field.SubfieldSubring.Read(L).At(k),
				module.RegularModuleOverSubring.Read(field.RingOn.Read(L)).At(k)))
		scalars := a.Have(
			"the scalar ring is a field on its carrier",
			"ring_subfield(K, L.inv, K.carrier)",
			Simp(Fwd(scalarDef)),
			By(subfieldK, field.SubfieldRingSubfield.Read(L).At(k, k)))
		idealsAsModules := a.Have(
			"every ideal of S is a k-submodule contained in S",
			"∀H:set(A). ring_ideal(«R», H) ⇒ submodule(K, M, H) ∧ H ⊆ S",
			Derive(func(b *Argument) {
				H := b.FixAs[Set[A]]("H")
				ideal := b.Assume()
				integral := b.Have(
					"an ideal of S is an S-submodule inside S",
					"submodule(«R», M, H) ∧ H ⊆ S",
					Simp(Fwd(ambientDef)),
					By(ideal, subringS, fractional_ideal.IntegralIdealFractional.Read(L).At(S, H)))
				b.Show(
					"restricting scalars to k preserves the submodule",
					Simp(Fwd(scalarDef)),
					By(
						kInS,
						integral,
						submodule.SubmoduleRestrictScalars.At(
							r, M, H, b.TermAs[RingOps[A]]("restrict_ring(field_ring(L), k)"))))
			}))
		endpoints := a.Have(
			"S and I are k-submodules",
			"submodule(K, M, S) ∧ submodule(K, M, I)",
			By(idealsAsModules.At(S), idealsAsModules.At(I), idealI, ring_ideal.CarrierIdeal.Read(ringS)))
		chainBound := a.Have(
			"every strict ideal chain has length at most the colength",
			Statement{
				Binders:    "∀C:(num → set(A)). ∀n:num.",
				Hypotheses: []string{"ideal_chain(«R», I, C, n)"},
				Conclusion: "n ≤ module_dim(K, quotient_module(restrict_module(M, S), I))",
			},
			Derive(func(b *Argument) {
				b.FixAs[Fun[Nat, Set[A]]]("C")
				n := b.FixAs[Nat]("n")
				chain := b.Assume()
				parts := b.Conjuncts(
					b.Unfolded(chain, idealChainDef),
					"the chain begins at I",
					"the chain ends at S",
					"the chain prefix consists of ideals",
					"each adjacent inclusion is strict")
				start, end, ideals, advances := parts[0], parts[1], parts[2], parts[3]
				prefix := b.Have(
					"each strict step adds at least one dimension above I",
					"∀j:num. j ≤ n ⇒ I ⊆ C(j) ∧ j ≤ module_dim(K, quotient_module(restrict_module(M, C(j)), I))",
					Derive(func(c *Argument) {
						c.Induct("j")
						c.Base(
							"the chain starts at I and dimension is nonnegative",
							Simp(Fwd(start), Fwd(set_basic.SubsetDef)),
							ByArith())
						c.Step(
							"the next strict quotient contributes a positive dimension",
							func(d *Argument, ih Fact) {
								within := d.Assume()
								j := d.TermAs[Nat]("j")
								current := d.TermAs[Set[A]]("C(j)")
								next := d.TermAs[Set[A]]("C(suc(j))")
								bounds := d.Have(
									"both adjacent indices lie in the chain prefix",
									"j < n ∧ j ≤ n ∧ suc(j) = j + 1",
									ByArith(within))
								previous := d.Have(
									"the preceding ideal contains I and has the dimension bound",
									"I ⊆ C(j) ∧ j ≤ module_dim(K, quotient_module(restrict_module(M, C(j)), I))",
									By(ih, bounds))
								strict := d.Have(
									"the next ideal strictly contains the preceding ideal",
									"C(j) ⊆ C(suc(j)) ∧ C(j) ≠ C(suc(j))",
									By(Normalized, advances.At(j), bounds))
								integral := d.Have(
									"both adjacent terms are ideals of S",
									"ring_ideal(«R», C(j)) ∧ ring_ideal(«R», C(suc(j)))",
									By(ideals.At(j), ideals.At(d.TermAs[Nat]("suc(j)")), bounds, within))
								submodules := d.Have(
									"the adjacent ideals are k-submodules inside S",
									"submodule(K, M, C(j)) ∧ submodule(K, M, C(suc(j))) ∧ C(suc(j)) ⊆ S",
									By(idealsAsModules.At(current), idealsAsModules.At(next), integral))
								containsI := d.Have(
									"the next ideal contains I",
									"I ⊆ C(suc(j))",
									BySets(previous, strict))
								finiteNext := d.Have(
									"the next quotient above I inherits finite dimensionality from S modulo I",
									"finite_dimensional(K, quotient_module(restrict_module(M, C(suc(j))), I))",
									By(
										scalars,
										endpoints,
										submodules,
										containsI,
										finiteQuotient,
										module_dimension.QuotientChainDim.Read(ambient).At(inv, S, next, I)))
								increment := d.Have(
									"the next dimension is the preceding dimension plus the finite adjacent quotient",
									"finite_dimensional(K, quotient_module(restrict_module(M, C(suc(j))), C(j))) ∧ "+
										"module_dim(K, quotient_module(restrict_module(M, C(suc(j))), I)) = "+
										"module_dim(K, quotient_module(restrict_module(M, C(suc(j))), C(j))) + "+
										"module_dim(K, quotient_module(restrict_module(M, C(j)), I))",
									By(
										scalars,
										endpoints,
										submodules,
										strict,
										previous,
										finiteNext,
										module_dimension.QuotientChainDim.Read(ambient).At(inv, next, current, I)))
								positive := d.Have(
									"strictness makes the adjacent quotient dimension nonzero",
									"module_dim(K, quotient_module(restrict_module(M, C(suc(j))), C(j))) ≠ 0",
									By(
										scalars,
										submodules,
										strict,
										increment,
										module_dimension.QuotientDimZeroIff.Read(ambient).At(inv, next, current)))
								d.Show(
									"the positive increment pays for the next step",
									ByArith(containsI, previous, increment, positive))
							})
					}))
				b.Show(
					"at the endpoint the chain length is bounded by the dimension of S modulo I",
					Simp(Rev(end)),
					ByArith(prefix.At(n)))
			}))
		bounded := a.Have(
			"the colength bounds every ideal chain",
			"finite_ideal_height(«R», I)",
			Simp(Fwd(FiniteIdealHeightDef)),
			Derive(func(b *Argument) {
				b.Take(b.TermAs[Nat]("module_dim(K, quotient_module(restrict_module(M, S), I))"))
				b.Show(
					"the dimension is a bound on chain lengths",
					By(chainBound))
			}))
		C, maximalChain := a.ObtainAs[Fun[Nat, Set[A]]](
			"take an ideal chain attaining the height",
			"∃C:(num → set(A)). ideal_chain(«R», I, C, ideal_height(«R», I))",
			By(bounded, idealI, IdealHeightMaximum.Read(ringS).At(I)))
		a.Show(
			"the attained height satisfies the same colength bound",
			By(chainBound.At(C, a.TermAs[Nat]("ideal_height(«R», I)")), maximalChain, bounded))
	}),
})}

// GeneratedModuloFiniteColength — an ideal I of S above an ideal H whose
// quotient S/H is a finite-dimensional vector space over a subfield k
// inside S is generated by finitely many of its members modulo H. I/H is a
// subspace of S/H, so it is finite-dimensional too, and finitely many
// members of I lift a basis of it: every member of I is a combination of
// them over k plus a member of H, and a combination over k lies in the
// ideal they span.
var GeneratedModuloFiniteColength = generatedModuloFiniteColengthThm{family.Add(registry.ProofEntry{
	Name: "GeneratedModuloFiniteColength",
	Key:  "prop_3f94d0108480ee7f",
	Reading: "No Noetherian hypothesis: finite colength of H is what bounds the generators, " +
		"and H itself need not be finitely generated. With H = I it says nothing, G = ∅.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S k H I:set(A).",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"subfield(L, k)",
			"k ⊆ S",
			"ring_ideal(«R», H)",
			"ring_ideal(«R», I)",
			"H ⊆ I",
			"finite_dimensional(«scalars», «quotient»)",
		},
		Conclusion: "∃G:set(A). finite(G) ∧ G ⊆ I ∧ I ⊆ set_mul(L.add, ideal_span(«R», G), H)",
		Abbrev: Abbrev{
			{Name: "scalars", Text: "restrict_ring(field_ring(L), k)"},
			{Name: "ambient", Text: "regular_module(field_ring(L))"},
			{Name: "quotient", Text: "quotient_module(restrict_module(«ambient», S), H)"},
		},
	}, func(a *Argument, L field.FieldFact[on.L], S, k, H, I *Expr[Set[A]], h Fact) {
		given := a.Conjuncts(
			h,
			"S is a subring",
			"k is a subfield",
			"k lies in S",
			"H is an ideal of S",
			"so is I",
			"H lies in I",
			"S modulo H has finite dimension")
		subringS, subfieldK, kInS, idealH, idealI, HInI, finiteQuotient :=
			given[0], given[1], given[2], given[3], given[4], given[5], given[6]
		r := a.TermAs[RingOps[A]]("«R»")
		K := a.TermAs[RingOps[A]]("«scalars»")
		M := a.TermAs[module_record.ModuleOps[A, A]]("«ambient»")
		inv := a.TermAs[Fun[A, A]]("L.inv")
		ringS := a.Have(
			"S is a commutative ring",
			"comm_ring_on(«R»)",
			By(subringS, comm_ring.SubringRingOn.Read(field.RingOn.Read(L)).At(S)))
		ambient := a.Have(
			"the ambient field is a module over k",
			"module_on(«scalars», «ambient»)",
			By(
				subfieldK,
				field.SubfieldSubring.Read(L).At(k),
				module.RegularModuleOverSubring.Read(field.RingOn.Read(L)).At(k)))
		scalars := a.Have(
			"the scalar ring is a field on its carrier",
			"ring_subfield(«scalars», L.inv, k)",
			By(subfieldK, field.SubfieldRingSubfield.Read(L).At(k, k)))
		idealsAsModules := a.Have(
			"every ideal of S is a k-submodule contained in S",
			"∀J:set(A). ring_ideal(«R», J) ⇒ submodule(«scalars», «ambient», J) ∧ J ⊆ S",
			Derive(func(b *Argument) {
				J := b.FixAs[Set[A]]("J")
				ideal := b.Assume()
				integral := b.Have(
					"an ideal of S is an S-submodule inside S",
					"submodule(«R», «ambient», J) ∧ J ⊆ S",
					By(ideal, subringS, fractional_ideal.IntegralIdealFractional.Read(L).At(S, J)))
				b.Show(
					"restricting scalars to k preserves the submodule",
					By(kInS, integral, submodule.SubmoduleRestrictScalars.At(r, M, J, K)))
			}))
		endpoints := a.Have(
			"S, H and I are k-submodules, I inside S",
			"submodule(«scalars», «ambient», S) ∧ "+
				"submodule(«scalars», «ambient», H) ∧ "+
				"submodule(«scalars», «ambient», I) ∧ "+
				"I ⊆ S",
			By(
				idealsAsModules.At(S),
				idealsAsModules.At(H),
				idealsAsModules.At(I),
				idealH,
				idealI,
				ring_ideal.CarrierIdeal.Read(ringS)))
		finiteAbove := a.Have(
			"I/H, a subspace of S/H, has finite dimension",
			"finite_dimensional(«scalars», quotient_module(restrict_module(«ambient», I), H))",
			By(
				scalars,
				endpoints,
				HInI,
				finiteQuotient,
				module_dimension.QuotientChainDim.Read(ambient).At(inv, S, I, H)))
		T, lifted := a.UnpackAs[Set[A]](
			GroupPremises(
				scalars,
				endpoints,
				HInI,
				finiteAbove,
				module_dimension.QuotientComplementLift.Read(ambient).At(inv, I, H)),
			"T")
		lift := a.Conjuncts(
			lifted,
			"T is finite",
			"T lies in I",
			"T is independent over k",
			"I lies in the span of T over k plus H",
			"that span meets H only in zero",
			"T has the dimension of I/H")
		finiteT, TInI, cover := lift[0], lift[1], lift[3]
		TInS := a.Have(
			"T lies in S",
			"T ⊆ S",
			BySets(TInI, endpoints))
		spanT := a.TermAs[Set[A]]("ideal_span(«R», T)")
		spanIdeal := a.Have(
			"the ideal T generates is a k-submodule",
			"submodule(«scalars», «ambient», ideal_span(«R», T))",
			By(TInS, ring_ideal.SpanIdeal.Read(ringS).At(T), idealsAsModules.At(spanT)))
		combinations := a.Have(
			"a combination of T over k lies in the ideal T generates",
			"module_span(«scalars», «ambient», T) ⊆ ideal_span(«R», T)",
			By(spanIdeal, ring_ideal.SpanContains.At(r, T), submodule.SpanLeast.At(K, M, T, spanT)))
		a.Take(T)
		a.Show(
			"T is finite, lies in I, and generates I modulo H",
			Unfold(quotient_group.SetMulDef),
			BySets(finiteT, TInI, a.Unfolded(cover, quotient_group.SetMulDef), combinations))
	}),
})}

// IdealHeightMaximum — the height of a bounded ideal is attained and
// bounds every chain: chain lengths are nonempty and bounded, so their
// natural maximum satisfies the predicate defining the chosen height.
var IdealHeightMaximum = idealHeightMaximumThm{family.Add(registry.ProofEntry{
	Name: "IdealHeightMaximum",
	Key:  "prop_28dd8cdecd592d72",
	Build: family.Theorem(Statement{
		Binders:    "∀R:comm_ring_on(A). ∀I:set(A).",
		Hypotheses: []string{"ring_ideal(R, I)", "finite_ideal_height(R, I)"},
		Conclusion: "(∃C:(num → set(A)). ideal_chain(R, I, C, ideal_height(R, I))) ∧ " +
			"(∀C:(num → set(A)). ∀n:num. ideal_chain(R, I, C, n) ⇒ n ≤ ideal_height(R, I))",
	}, func(a *Argument, R comm_ring.CommRingFact[on.R], I *Expr[Set[A]], given Fact) {
		r := a.TermAs[RingOps[A]]("R")
		nonempty := a.Have(
			"some chain starts at I",
			"∃n:num. ∃C:(num → set(A)). ideal_chain(R, I, C, n)",
			Derive(func(b *Argument) {
				b.Cases(b.TermAs[Bool]("I = R.carrier"))
				b.When(
					"the unit ideal has a chain of length zero",
					func(c *Argument, unit Fact) {
						c.Take(c.TermAs[Nat]("0"))
						c.Take(c.TermAs[Fun[Nat, Set[A]]]("λi:num. I"))
						c.Show(
							"the constant chain has the required endpoints",
							Simp(Fwd(idealChainDef)),
							ByArith(unit, given))
					})
				b.Otherwise(
					"a proper ideal has a one-step chain to the unit ideal",
					func(c *Argument, proper Fact) {
						c.Take(c.TermAs[Nat]("1"))
						c.Take(c.TermAs[Fun[Nat, Set[A]]]("λi:num. COND(i = 0, I, R.carrier)"))
						ideal := c.Conjuncts(
							given,
							"I is an ideal",
							"I has finite height")[0]
						c.Do(Unfold(idealChainDef), SplitConjAll(
							Case(
								"the last term is the carrier",
								ByArith()),
							Case(
								"each term is I or the carrier",
								Derive(func(d *Argument) {
									d.FixAs[Nat]()
									d.Assume()
									d.Cases(d.TermAs[Bool]("i = 0"))
									d.When(
										"the initial term is the ideal I",
										func(e *Argument, zero Fact) {
											e.Show(
												"I is an ideal",
												By(ideal, zero))
										})
									d.Otherwise(
										"the later term is the unit ideal",
										func(e *Argument, positive Fact) {
											e.Show(
												"the carrier is an ideal",
												By(ring_ideal.CarrierIdeal.Read(R), positive))
										})
								})),
							Case(
								"the only step is the proper inclusion of I in the carrier",
								Derive(func(d *Argument) {
									d.FixAs[Nat]()
									beforeOne := d.Assume()
									zero := d.Have(
										"an index below one is zero",
										"i = 0",
										ByArith(beforeOne))
									d.Do(zero.Rw())
									d.Show(
										"I is properly contained in the carrier",
										By(ideal, proper, ring_ideal.IdealSubset.At(r, I)))
								}))))
					})
			}))
		bounded := a.Have(
			"the natural set of chain lengths is bounded",
			"∃B:num. ∀n:num. (∃C:(num → set(A)). ideal_chain(R, I, C, n)) ⇒ n ≤ B",
			By(Normalized, given, FiniteIdealHeightDef.At(r, I)))
		maximum := a.Have(
			"there is an attained maximum chain length",
			"∃h:num. "+
				"    (∃C:(num → set(A)). ideal_chain(R, I, C, h)) ∧ "+
				"    (∀C:(num → set(A)). ∀n:num. ideal_chain(R, I, C, n) ⇒ n ≤ h)",
			By(
				nonempty,
				bounded,
				nat_order.MaximumExists.At(
					a.TermAs[Set[Nat]]("λh:num. ∃C:(num → set(A)). ideal_chain(R, I, C, h)"))))
		a.Show(
			"the chosen height is attained and bounds every chain",
			Simp(Fwd(IdealHeightDef)),
			By(maximum))
	}),
})}

// IdealHeightStrict — strict inclusion lowers bounded ideal height:
// prepending the smaller ideal adds one to a longest chain above the
// larger ideal, and the smaller ideal's height bounds that chain.
var IdealHeightStrict = idealHeightStrictThm{family.Add(registry.ProofEntry{
	Name: "IdealHeightStrict",
	Key:  "prop_7f2e3729fce005c3",
	Build: family.Sections(Statement{
		Binders: "∀R:comm_ring_on(A). ∀I J:set(A).",
		Hypotheses: []string{
			"ring_ideal(R, I)",
			"ring_ideal(R, J)",
			"I ⊆ J",
			"I ≠ J",
			"finite_ideal_height(R, I)",
		},
		Conclusion: "finite_ideal_height(R, J) ∧ ideal_height(R, J) < ideal_height(R, I)",
		Abbrev: Abbrev{
			{Name: "Prepended", Text: "λC:(num → set(A)). λi:num. COND(i = 0, I, C(i - 1))"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		prepend := ctx.Lemma(Statement{
			Binders:    "∀R:ring_ops(A). ∀I J:set(A). ∀C:(num → set(A)). ∀n:num.",
			Hypotheses: []string{"ring_ideal(R, I)", "I ⊆ J", "I ≠ J", "ideal_chain(R, J, C, n)"},
			Conclusion: "ideal_chain(R, I, «Prepended»(C), n + 1)",
		}, func(
			a *Argument,
			R *Expr[RingOps[A]],
			I, J *Expr[Set[A]],
			C *Arrow[Nat, Set[A]],
			n *Expr[Nat],
			given Fact,
		) {
			parts := a.Conjuncts(
				given,
				"I is an ideal",
				"I lies in J",
				"I differs from J",
				"C is a chain above J")
			old := a.Conjuncts(
				a.Unfolded(parts[3], idealChainDef),
				"C starts at J",
				"C ends at the carrier",
				"the old prefix consists of ideals",
				"the old prefix has strict adjacent inclusions")
			initial := a.Have(
				"the new first term is I",
				"«Prepended»(C, 0) = I",
				ByArith())
			endpoint := a.Have(
				"the shifted endpoint is a positive index",
				"n + 1 ≠ 0 ∧ (n + 1) - 1 = n",
				ByArith())
			terminal := a.Have(
				"the new chain still ends at the carrier",
				"«Prepended»(C, n + 1) = R.carrier",
				By(Normalized, old[1], endpoint))
			ideals := a.Have(
				"each new prefix term is an ideal",
				"∀i:num. i ≤ n + 1 ⇒ ring_ideal(R, «Prepended»(C, i))",
				Derive(func(b *Argument) {
					b.FixAs[Nat]()
					within := b.Assume()
					b.Cases(b.TermAs[Bool]("i = 0"))
					b.When(
						"the new first term is the ideal I",
						func(c *Argument, zero Fact) {
							c.Show(
								"I is an ideal",
								By(zero, parts[0]))
						})
					b.Otherwise(
						"a later term belongs to the old prefix",
						func(c *Argument, positive Fact) {
							previous := c.Have(
								"the preceding index lies in the old prefix",
								"i - 1 ≤ n",
								ByArith(positive, within))
							c.Show(
								"the old prefix term is an ideal",
								By(old[2].At(c.TermAs[Nat]("i - 1")), positive, previous))
						})
				}))
			strict := a.Have(
				"every new prefix step is strict",
				Statement{
					Binders: "∀i:num.",
					Hypotheses: []string{
						"i < n + 1",
					},
					Conclusion: "«Prepended»(C, i) ⊆ «Prepended»(C, i + 1) ∧ «Prepended»(C, i) ≠ «Prepended»(C, i + 1)",
				},
				Derive(func(b *Argument) {
					b.FixAs[Nat]()
					within := b.Assume()
					b.Cases(b.TermAs[Bool]("i = 0"))
					b.When(
						"the new first step is the strict inclusion of I in J",
						func(c *Argument, zero Fact) {
							shift := c.Have(
								"the next term reads the old initial index",
								"i + 1 ≠ 0 ∧ (i + 1) - 1 = i",
								ByArith())
							c.Show(
								"I is strictly included in the next term J",
								By(Normalized, parts[1], parts[2], old[0], zero, shift))
						})
					b.Otherwise(
						"a later step is an old strict inclusion",
						func(c *Argument, positive Fact) {
							shift := c.Have(
								"both shifted indices read one old adjacent pair",
								"i - 1 < n ∧ (i - 1) + 1 = i ∧ (i + 1) - 1 = i ∧ i + 1 ≠ 0",
								ByArith(positive, within))
							c.Show(
								"the old adjacent inclusion remains strict",
								By(old[3].At(c.TermAs[Nat]("i - 1")), positive, shift))
						})
				}))
			a.Show(
				"prepending I adds one to the chain length",
				By(
					initial,
					terminal,
					ideals,
					strict,
					idealChainDef.At(R, I, a.TermAs[Fun[Nat, Set[A]]]("«Prepended»(C)"), a.TermAs[Nat]("n + 1"))))
		})
		return ctx.Theorem(headline, func(
			a *Argument,
			R comm_ring.CommRingFact[on.R],
			I, J *Expr[Set[A]],
			h Fact,
		) {
			r := a.TermAs[RingOps[A]]("R")
			heightI := a.TermAs[Nat]("ideal_height(R, I)")
			heightJ := a.TermAs[Nat]("ideal_height(R, J)")
			bound := a.Have(
				"the height of I bounds every chain above I",
				"∀C:(num → set(A)). ∀n:num. ideal_chain(R, I, C, n) ⇒ n ≤ ideal_height(R, I)",
				By(h, IdealHeightMaximum.Read(R).At(I)))
			lifted := a.Have(
				"every chain above J can be lengthened above I",
				"∀C:(num → set(A)). ∀n:num. ideal_chain(R, J, C, n) ⇒ n + 1 ≤ ideal_height(R, I)",
				Derive(func(b *Argument) {
					C := b.FixAs[Fun[Nat, Set[A]]]()
					n := b.FixAs[Nat]()
					chain := b.Assume()
					D := b.TermAs[Fun[Nat, Set[A]]]("«Prepended»(C)")
					longer := b.Have(
						"prepending I gives a longer chain above I",
						"ideal_chain(R, I, «Prepended»(C), n + 1)",
						By(h, chain, At(prepend, r, I, J, C, n)))
					b.Show(
						"the longer chain is bounded by the height of I",
						By(bound.At(D, b.TermAs[Nat]("n + 1")), longer))
				}))
			finiteJ := a.Have(
				"the height of I also bounds all chain lengths above J",
				"finite_ideal_height(R, J)",
				Simp(Fwd(FiniteIdealHeightDef)),
				Derive(func(b *Argument) {
					b.Take(heightI)
					C := b.FixAs[Fun[Nat, Set[A]]]()
					n := b.FixAs[Nat]()
					chain := b.Assume()
					b.Show(
						"discarding the prepended step gives the required bound",
						ByArith(lifted.At(C, n), chain))
				}))
			C, longest := a.ObtainAs[Fun[Nat, Set[A]]](
				"some chain attains the height of J",
				"∃C:(num → set(A)). ideal_chain(R, J, C, ideal_height(R, J))",
				By(h, finiteJ, IdealHeightMaximum.Read(R).At(J)))
			a.Show(
				"J has finite height strictly smaller than the height of I",
				ByArith(finiteJ, lifted.At(C, heightJ), longest))
		})
	}),
})}
