package int_lattice

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/quotient_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/free_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/function_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/linear_independence"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/principal_ideal_domain"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/characteristic_zero"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_div_rem"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_embed"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_real_lift"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// SubmoduleFreeTriangular gives every integer submodule a positive triangular
// indexed basis of rank at most its ambient dimension. The last-coordinate
// image either vanishes or splits off one positive final pivot.
var SubmoduleFreeTriangular = submoduleFreeTriangularThm{family.Add(registry.ProofEntry{
	Name: "SubmoduleFreeTriangular",
	Key:  "prop_d3b7f14b9b83fdc8",
	Build: family.Sections(Statement{
		Binders: "∀n:num. ∀M:set(num → int).",
		Hypotheses: []string{
			"submodule(int_ring, «ℤⁿ», M)",
		},
		Conclusion: "∃r:num. ∃b:(num → num → int). ∃p:(num → num). " +
			"    r ≤ n ∧ integer_triangular_basis(n, M, r, b, p)",
	}, func(ctx *Script, headline string) *GoalStackNode {
		support := ctx.Lemma("∀n:num. ∀v:(num → int). "+
			"    v ∈ «ℤⁿ».carrier ⇔ "+
			"    finite(fun_support(int_of_num(0), v)) ∧ "+
			"    fun_support(int_of_num(0), v) ⊆ {i:num | i < n}", func(a *Argument) {
			a.Show(
				"the carrier consists of integer vectors supported below n",
				Simp(Fwd(free_module.FreeModuleRecordDef), Fwd(function_module.FiniteSuppMember)),
				By(set_basic.InUniv))
		})
		emptySpan := ctx.Lemma(Statement{
			Binders: "∀R:ring_ops(A). ∀V:module_ops(A, B).",
			Hypotheses: []string{
				"module_on(R, V)",
			},
			Conclusion: "module_span(R, V, ∅) = {V.zero}",
		}, func(
			a *Argument,
			R *Expr[RingOps[A]],
			V *Expr[ModuleOps[A, B]],
			onV module.ModuleFact[on.R, on.V],
		) {
			empty := a.TermAs[Set[B]]("∅")
			spanSub := a.Have(
				"the empty span is a submodule",
				"submodule(R, V, module_span(R, V, ∅))",
				By(onV, set_order.EmptySubset, submodule.SpanSubmodule.At(R, V, empty)))
			belowZero := a.Have(
				"it lies in the zero submodule",
				"module_span(R, V, ∅) ⊆ {V.zero}",
				By(
					onV,
					submodule.ZeroSubmodule,
					set_order.EmptySubset,
					submodule.SpanLeast.At(R, V, empty, a.TermAs[Set[B]]("{V.zero}"))))
			a.Show(
				"the empty span is exactly the zero submodule",
				BySets(
					belowZero,
					spanSub,
					submodule.SubmoduleZero.At(R, V, a.TermAs[Set[B]]("module_span(R, V, ∅)"))))
		})
		transport := ctx.Lemma(Statement{
			Binders: "∀m n:num. ∀K:set(num → int).",
			Hypotheses: []string{
				"submodule(int_ring, free_module_record(int_ring, {i:num | i < m}), K)",
				"K ⊆ «ℤⁿ».carrier",
			},
			Conclusion: "submodule(int_ring, «ℤⁿ», K)",
		}, func(a *Argument) {
			a.Show(
				"changing the support bound preserves the operations and their closure",
				Simp(
					Fwd(free_module.FreeModuleRecordDef),
					Fwd(submodule.SubmoduleDef),
					Fwd(module_record.ModuleAdditiveGroupDef)),
				Unfold(group.SubgroupDef),
				StripQuant(),
				StripImp(),
				Given(func(b *Argument, closure Fact) {
					b.Show(
						"the same zero, addition, negation and scalar action preserve K",
						By(closure))
				}))
		})
		lowerSupport := ctx.Lemma(Statement{
			Binders: "∀n:num. ∀v:(num → int).",
			Hypotheses: []string{
				"v ∈ free_module_record(int_ring, {i:num | i < suc(n)}).carrier",
				"v(n) = &0",
			},
			Conclusion: "v ∈ «ℤⁿ».carrier",
		}, func(a *Argument) {
			a.Show(
				"a vector with zero last coordinate is supported below n",
				Simp(Fwd(free_module.FreeModuleRecordDef), Fwd(function_module.FiniteSuppMember)),
				StripQuant(),
				StripImp(),
				Given(func(b *Argument, supported Fact) {
					b.Show(
						"remove n from the support bound",
						BySets(supported, nat_order.LessThanSucClause))
				}))
		})
		raiseTriangular := ctx.Lemma(Statement{
			Binders: "∀m n r:num. ∀K:set(num → int). ∀b:(num → num → int). ∀p:(num → num).",
			Hypotheses: []string{
				"m ≤ n",
				"integer_triangular_basis(m, K, r, b, p)",
			},
			Conclusion: "integer_triangular_basis(n, K, r, b, p)",
		}, func(a *Argument) {
			a.Show(
				"the same basis and pivots work with a larger ambient support bound",
				Simp(
					Fwd(IntegerTriangularBasisDef),
					Fwd(free_module.FreeModuleRecordDef),
					Fwd(module_record.RestrictModuleDef)),
				StripQuant(),
				StripImp(),
				Given(func(c *Argument, triangular Fact) {
					c.Show(
						"only the upper bound on the pivots changes",
						By(triangular, nat_order.LessThanLessEqTrans))
				}))
		})
		positiveLift := ctx.Lemma(Statement{
			Binders: "∀n:num. ∀M:set(num → int). ∀b:(num → int).",
			Hypotheses: []string{
				"submodule(int_ring, free_module_record(int_ring, {i:num | i < suc(n)}), M)",
				"b ∈ M",
				"b(n) ≠ &0",
				"∀v:(num → int). " +
					"    v ∈ M ⇒ " +
					"    ∃u:(num → int). ∃a:int. " +
					"        u ∈ M ∧ u(n) = &0 ∧ v = fun_add(int_ring.add, u, fun_smul(int_ring.mul, a, b))",
			},
			Conclusion: "∃c:(num → int). " +
				"    c ∈ M ∧ " +
				"    &0 < c(n) ∧ " +
				"    (∀v:(num → int). " +
				"        v ∈ M ⇒ " +
				"        ∃u:(num → int). ∃a:int. " +
				"            u ∈ M ∧ u(n) = &0 ∧ v = fun_add(int_ring.add, u, fun_smul(int_ring.mul, a, c)))",
		}, func(a *Argument, n *Expr[Nat], M *Expr[Set[Fun[Nat, Int]]], b *Arrow[Nat, Int], given Fact) {
			parts := a.Conjuncts(
				given,
				"M is a submodule",
				"b lies in M",
				"the last coordinate is nonzero",
				"b splits every vector")
			notPositive := a.Unless(
				a.Term("0 < b(n)").Core(),
				"a positive lift already has the desired sign",
				Given(func(c *Argument, positive Fact) {
					c.Show(
						"use b itself",
						Witness(b),
						By(parts[3], positive, parts[1]))
				}))
			negated := a.TermAs[Fun[Nat, Int]]("fun_neg(λz:int. -z, b)")
			negativeIn := a.Have(
				"the negated lift remains in M",
				"fun_neg(λz:int. -z, b) ∈ M",
				By(parts[1], At(submodule.SubmoduleNeg.Read(parts[0]), b)))
			positive := a.Have(
				"its last coordinate is positive",
				"0 < fun_neg(λz:int. -z, b, n)",
				Simp(Fwd(function_module.FunNegDef)),
				ByArith(parts[2], notPositive))
			decomposes := a.Have(
				"negate the scalar coefficient to preserve each decomposition",
				Statement{
					Binders: "∀v:(num → int).",
					Hypotheses: []string{
						"v ∈ M",
					},
					Conclusion: "∃u:(num → int). ∃a:int. " +
						"    u ∈ M ∧ " +
						"    u(n) = &0 ∧ " +
						"    v = fun_add(int_ring.add, u, fun_smul(int_ring.mul, a, fun_neg(λz:int. -z, b)))",
				},
				Simp(
					Fwd(int_real_lift.IntRingDef),
					Fwd(module_record.RingAddDef),
					Fwd(module_record.RingMulDef),
					Fwd(function_module.FunAddDef),
					Fwd(function_module.FunSmulDef),
					Fwd(function_module.FunNegDef)),
				Derive(func(d *Argument) {
					v := d.FixAs[Fun[Nat, Int]]("v")
					vIn := d.Assume()
					u, _, split := d.Obtain2As[Fun[Nat, Int], Int](
						"split v using b",
						"∃u:(num → int). ∃a:int. u ∈ M ∧ u(n) = &0 ∧ v = fun_add(int_add, u, fun_smul(int_mul, a, b))",
						By(
							vIn,
							d.Simplified(
								parts[3],
								Fwd(int_real_lift.IntRingDef),
								Fwd(module_record.RingAddDef),
								Fwd(module_record.RingMulDef)).At(v)),
						Named("u", "scalar"))
					data := d.Conjuncts(
						d.Simplified(split, Fwd(function_module.FunAddDef), Fwd(function_module.FunSmulDef)),
						"u lies in M",
						"u has last coordinate zero",
						"v is u plus scalar times b")
					d.Show(
						"the two sign changes cancel",
						Witness(u),
						Witness(d.TermAs[Int]("-scalar")),
						SplitConj(Case(
							"u keeps its membership and zero coordinate",
							By(data[0], data[1])), Case(
							"the product is unchanged",
							data[2].Rw(),
							Funext(),
							ByArith())))
				}))
			a.Show(
				"use the negated lift",
				Witness(negated),
				By(negativeIn, positive, decomposes))
		})
		appendInjective := ctx.Lemma(Statement{
			Binders: "∀r:num. ∀e:(num → num → int). ∀c:(num → int).",
			Hypotheses: []string{
				"injective_on({i:num | i < r}, e)",
				"∀i:num. i < r ⇒ e(i) ≠ c",
			},
			Conclusion: "injective_on({i:num | i < suc(r)}, λi:num. COND(i < r, e(i), c))",
		}, func(a *Argument, r *Expr[Nat], e *Arrow2[Nat, Nat, Int], c *Arrow[Nat, Int], given Fact) {
			a.Show(
				"append a vector distinct from all previous vectors",
				Simp(Fwd(functions.InjectiveOnDef)),
				Derive(func(b *Argument) {
					x, y := b.FixAs[Nat]("x"), b.FixAs[Nat]("y")
					equalImages := b.Assume()
					b.Show(
						"old indices use injectivity and the last index uses freshness",
						BySets(
							given,
							equalImages,
							functions.InjectiveOnDef.At(b.TermAs[Set[Nat]]("{i:num | i < r}"), e),
							nat_order.LessThanSucClause.At(x, r),
							nat_order.LessThanSucClause.At(y, r)))
				}))
		})
		noMultiple := ctx.Lemma(Statement{
			Binders: "∀n:num. ∀V:module_ops(int, num → int). ∀K F:set(num → int). ∀c:(num → int).",
			Hypotheses: []string{
				"V = free_module_record(int_ring, {i:num | i < suc(n)})",
				"module_span(int_ring, V, F) = K",
				"∀v:(num → int). v ∈ K ⇒ v(n) = &0",
				"&0 < c(n)",
			},
			Conclusion: "∀a:int. " +
				"    a ∈ int_ring.carrier ∧ V.smul(a, c) ∈ module_span(int_ring, V, F) ⇒ a = int_ring.zero",
		}, func(
			a *Argument,
			n *Expr[Nat],
			V *Expr[ModuleOps[Int, Fun[Nat, Int]]],
			K, F *Expr[Set[Fun[Nat, Int]]],
			c *Arrow[Nat, Int],
			given Fact,
		) {
			parts := a.Conjuncts(
				given,
				"V is the free ambient module",
				"F spans K",
				"K has last coordinate zero",
				"c has positive last coordinate")
			a.Show(
				"no nonzero multiple of c belongs to the old span",
				Simp(
					Fwd(int_real_lift.IntRingDef),
					Fwd(module_record.RingCarrierDef),
					Fwd(module_record.RingZeroDef)),
				Derive(func(b *Argument) {
					scalar := b.FixAs[Int]("scalar")
					inSpan := b.Assume()
					zero := b.Have(
						"a multiple in K has last coordinate zero",
						"V.smul(scalar, c, n) = 0",
						parts[1].Simp(Fwd(int_real_lift.IntRingDef)),
						By(Normalized, parts[2].At(b.TermAs[Fun[Nat, Int]]("V.smul(scalar,c)")), parts[1], inSpan))
					productZero := b.Simplified(
						zero,
						Fwd(parts[0]),
						Fwd(free_module.FreeModuleRecordDef),
						Fwd(module_record.ModSmulDef),
						Fwd(function_module.FunSmulDef))
					b.Show(
						"a positive last coordinate cancels the scalar",
						ByArith(productZero, parts[3], int_real_lift.MulEqZero.At(scalar, b.TermAs[Int]("c(n)"))))
				}))
		})
		appendImage := ctx.Lemma("∀r:num. ∀e:(num → num → int). ∀c:(num → int). "+
			"    {COND(i < r, e(i), c):(num → int) | i:num | i < suc(r)} = "+
			"    insert(c, {e(i):(num → int) | i:num | i < r})", func(
			a *Argument,
			r *Expr[Nat],
			e *Arrow2[Nat, Nat, Int],
			c *Arrow[Nat, Int],
		) {
			a.Show(
				"the appended image is the old image with c inserted",
				BySets(nat_order.LessThanSucClause, nat_order.LessThanIrrefl.At(r)))
		})
		restrictionIndependent := ctx.Lemma("∀m n:num. ∀K:set(num → int). "+
			"    restrict_module(free_module_record(int_ring, {i:num | i < m}), K) = "+
			"    restrict_module(«ℤⁿ», K)", func(a *Argument) {
			a.Show(
				"restricting to K forgets the ambient support bound",
				Simp(
					Fwd(free_module.FreeModuleRecordDef),
					Fwd(module_record.RestrictModuleDef),
					Fwd(module_record.ModAddDef),
					Fwd(module_record.ModZeroDef),
					Fwd(module_record.ModNegDef),
					Fwd(module_record.ModSmulDef)),
				Basic())
		})
		return ctx.Theorem(headline, func(a *Argument) {
			a.Induct("n")
			a.Base(
				"the module in dimension zero contains only its zero vector",
				func(b *Argument) {
					M := b.FixAs[Set[Fun[Nat, Int]]]("M")
					sub := b.Assume()
					R := b.TermAs[RingOps[Int]]("int_ring")
					V := b.TermAs[ModuleOps[Int, Fun[Nat, Int]]]("free_module_record(int_ring, {i:num | i < 0})")
					empty := b.TermAs[Set[Fun[Nat, Int]]]("∅")
					belowCarrier := b.Have(
						"M lies in the ambient carrier",
						"M ⊆ free_module_record(int_ring, {i:num | i < 0}).carrier",
						By(sub, submodule.SubmoduleSubset))
					onV := b.Have(
						"the ambient free module is a module",
						"module_on(int_ring, free_module_record(int_ring, {i:num | i < 0}))",
						By(free_module.FreeModuleOn.Read(int_real_lift.CommRingOn).At(
							b.TermAs[Set[Nat]]("{i:num | i < 0}"))))
					allZero := b.Have(
						"every vector in M is zero",
						"∀v:(num → int). v ∈ M ⇒ v = λj:num. int_of_num(0)",
						Derive(func(c *Argument) {
							v := c.FixAs[Fun[Nat, Int]]("v")
							vIn := c.Assume()
							inFree := c.Have(
								"v belongs to the zero-dimensional free module",
								"v ∈ free_module_record(int_ring, {i:num | i < 0}).carrier",
								BySets(vIn, belowCarrier))
							c.Show(
								"its support has no coordinates",
								Funext(),
								StripQuant(),
								BySets(inFree, At(support, c.TermAs[Nat]("0"), v), nat_order.LessThan))
						}))
					spans := b.Have(
						"the empty family spans M",
						"module_span(int_ring, free_module_record(int_ring, {i:num | i < 0}), ∅) = M",
						BySets(allZero, onV, sub, At(emptySpan, R, V), submodule.SubmoduleZero.At(R, V, M)))
					basis := b.Have(
						"the empty family is a basis of M",
						"module_basis(int_ring, restrict_module(free_module_record(int_ring, {i:num | i < 0}), M), ∅)",
						By(
							spans,
							onV,
							sub,
							linear_independence.IndependentEmpty.At(R, V),
							At(linear_independence.BasisRestrict.Read(onV), M, empty)))
					zeroBasis := b.TermAs[Fun2[Nat, Nat, Int]]("λi:num. λj:num. 0")
					zeroPivots := b.TermAs[Fun[Nat, Nat]]("λi:num. 0")
					b.Show(
						"rank zero and empty pivot data give a triangular basis",
						Witness(b.TermAs[Nat]("0")),
						Witness(zeroBasis),
						Witness(zeroPivots),
						BySets(
							basis,
							IntegerTriangularBasisDef.At(b.TermAs[Nat]("0"), b.TermAs[Nat]("0"), M, zeroBasis, zeroPivots),
							linear_independence.IndexedModuleBasisDef.At(
								R,
								b.TermAs[ModuleOps[Int, Fun[Nat, Int]]](
									"restrict_module(free_module_record(int_ring, {i:num | i < 0}), M)"),
								b.TermAs[Nat]("0"),
								zeroBasis),
							nat_order.LessThan,
							nat_order.LessEqRefl,
							functions.InjectiveOnDef))
				})
			a.Step(
				"split off the last coordinate and apply the induction hypothesis to its kernel",
				func(b *Argument, ih Fact) {
					n := b.TermAs[Nat]("n")
					M := b.FixAs[Set[Fun[Nat, Int]]]("M")
					sub := b.Assume()
					R := b.TermAs[RingOps[Int]]("int_ring")
					// The coordinate split is stated for the indices below n + 1, the indices below suc(n).
					successor := b.Have(
						"the two successor spellings agree",
						"n + 1 = suc(n)",
						ByArith())
					belowSuccessor := b.Have(
						"M is a submodule of the vectors supported below n + 1",
						"submodule(int_ring, free_module_record(int_ring, {i:num | i < n + 1}), M)",
						successor.Rw(),
						By(sub))
					_, split := b.UnpackAs[Int](GroupPremises(IntegerRingPrincipalIdealDomain, belowSuccessor,
						principal_ideal_domain.CoordinateProjectionSplit.At(R, n, M)), "d")
					alternatives := b.Conjuncts(
						split,
						"d is a scalar",
						"d generates the last-coordinate image",
						"a zero image kills the last coordinate",
						"a nonzero image splits along a lift")
					b.Cases(b.Term("d = 0"))
					b.When(
						"a zero last-coordinate image needs no new basis vector",
						func(f *Argument, dZero Fact) {
							killed := f.Have(
								"all vectors in M have last coordinate zero",
								"∀v:(num → int). v ∈ M ⇒ v(n) = 0",
								By(dZero, alternatives[2]))
							supported := f.Have(
								"M is supported below n",
								"M ⊆ «ℤⁿ».carrier",
								Unfold(set_basic.SubsetDef),
								Derive(func(g *Argument) {
									v := g.FixAs[Fun[Nat, Int]]("v")
									vIn := g.Assume()
									g.Show(
										"drop the zero last coordinate",
										BySets(
											vIn,
											killed.At(v),
											sub,
											submodule.SubmoduleSubset.At(
												R,
												g.TermAs[ModuleOps[Int, Fun[Nat, Int]]]("free_module_record(int_ring, {i:num | i < suc(n)})"),
												M),
											At(lowerSupport, n, v)))
								}))
							smaller := f.Have(
								"M is a submodule in dimension n",
								"submodule(int_ring, «ℤⁿ», M)",
								By(supported, sub, At(transport, f.TermAs[Nat]("suc(n)"), n, M)))
							r, e, p, triangular := f.Obtain3As[Nat, Fun2[Nat, Nat, Int], Fun[Nat, Nat]](
								"apply induction to M",
								"∃r:num. ∃e:(num → num → int). ∃p:(num → num). r ≤ n ∧ integer_triangular_basis(n, M, r, e, p)",
								By(ih.At(M), smaller),
								Named("r", "e", "p"))
							data := f.Conjuncts(
								triangular,
								"the old rank is at most n",
								"the old basis is triangular")
							bound := f.Have(
								"the old rank is also at most suc(n)",
								"r ≤ suc(n)",
								ByArith(data[0]))
							f.Show(
								"retain the old basis and pivots",
								Witness(r),
								Witness(e),
								Witness(p),
								By(
									bound,
									data[1],
									nat_order.LessEqRefl,
									nat_order.LessEqSucClause.At(n, n),
									At(raiseTriangular, n, f.TermAs[Nat]("suc(n)"), r, M, e, p)))
						})
					b.Otherwise(
						"a nonzero last-coordinate image contributes one final pivot",
						func(f *Argument, dNonzero Fact) {
							w, lift := f.ObtainAs[Fun[Nat, Int]](
								"choose a lift of the nonzero coordinate generator",
								"∃w:(num → int). "+
									"    w ∈ M ∧ "+
									"    w(n) = d ∧ "+
									"    (∀v:(num → int). "+
									"        v ∈ M ⇒ "+
									"        ∃u:(num → int). ∃a:int. "+
									"            u ∈ M ∧ u(n) = 0 ∧ v = fun_add(int_ring.add, u, fun_smul(int_ring.mul, a, w)))",
								Simp(Fwd(int_real_lift.IntRingDef), Fwd(module_record.RingAddDef), Fwd(module_record.RingMulDef)),
								By(dNonzero, alternatives[3]),
								Named("w"))
							liftData := f.Conjuncts(
								lift,
								"the lift lies in M",
								"its last coordinate is d",
								"the lift splits every vector")
							K, kDef := f.LetAs[Set[Fun[Nat, Int]]]("K", "{v:(num → int) | v ∈ M ∧ v(n) = 0}")
							kernelSub := f.Have(
								"the zero-coordinate part K is a submodule",
								"submodule(int_ring, free_module_record(int_ring, {i:num | i < suc(n)}), K)",
								Derive(func(g *Argument) {
									coordinate := g.Have(
										"last-coordinate evaluation is linear",
										"module_homomorphism(int_ring, "+
											"    free_module_record(int_ring, {i:num | i < suc(n)}), "+
											"    regular_module(int_ring), "+
											"    λv:(num → int). v(n))",
										By(free_module.CoordinateProjectionLinear.Read(int_real_lift.CommRingOn).At(
											g.TermAs[Set[Nat]]("{i:num | i < suc(n)}"), n)))
									asKernel := g.Have(
										"K is the intersection with the coordinate kernel",
										"K = "+
											"M ∩ "+
											"group_kernel(int_of_num(0), "+
											"    free_module_record(int_ring, {i:num | i < suc(n)}).carrier, "+
											"    λv:(num → int). v(n))",
										Simp(Fwd(free_module.FreeModuleRecordDef), Fwd(module_record.ModCarrierDef)),
										Simp(Fwd(set_basic.Extension)),
										Derive(func(h *Argument) {
											v := h.FixAs[Fun[Nat, Int]]("v")
											h.Show(
												"membership says exactly that v lies in M and its last coordinate is zero",
												kDef.Rw(),
												BySets(
													submodule.SubmoduleSubset.Read(sub),
													group_homomorphism.InKernel.At(
														h.TermAs[Int]("0"),
														h.TermAs[Set[Fun[Nat, Int]]]("finite_supp(int_of_num(0), 𝕌, {i:num | i < suc(n)})"),
														h.TermAs[Fun[Fun[Nat, Int], Int]]("λv:(num → int). v(n)"),
														v)))
										}))
									kernel := g.Have(
										"the coordinate kernel is a submodule",
										"submodule(int_ring, "+
											"    free_module_record(int_ring, {i:num | i < suc(n)}), "+
											"    group_kernel(int_of_num(0), "+
											"        free_module_record(int_ring, {i:num | i < suc(n)}).carrier, "+
											"        λv:(num → int). v(n)))",
										By(module_homomorphism.KernelSubmodule.Read(coordinate)))
									g.Show(
										"intersect two submodules",
										asKernel.Rw(),
										By(
											kernel,
											submodule.SubmoduleInter.Read(sub).At(g.TermAs[Set[Fun[Nat, Int]]](
												"group_kernel(int_of_num(0), "+
													"    free_module_record(int_ring, {i:num | i < suc(n)}).carrier, "+
													"    λv:(num → int). v(n))"))))
								}))
							kernelSupport := f.Have(
								"K is supported below n",
								"K ⊆ «ℤⁿ».carrier",
								Unfold(set_basic.SubsetDef),
								Derive(func(g *Argument) {
									v := g.FixAs[Fun[Nat, Int]]("v")
									vIn := g.Assume()
									g.Show(
										"the last coordinate vanishes by the definition of K",
										BySets(kDef, vIn, submodule.SubmoduleSubset.Read(kernelSub), At(lowerSupport, n, v)))
								}))
							smallerKernel := f.Have(
								"K is a submodule in dimension n",
								"submodule(int_ring, «ℤⁿ», K)",
								By(kernelSupport, kernelSub, At(transport, f.TermAs[Nat]("suc(n)"), n, K)))
							r, e, _, old := f.Obtain3As[Nat, Fun2[Nat, Nat, Int], Fun[Nat, Nat]](
								"apply induction to K",
								"∃r:num. ∃e:(num → num → int). ∃p:(num → num). r ≤ n ∧ integer_triangular_basis(n,K,r,e,p)",
								By(ih.At(K), smallerKernel),
								Named("r", "e", "p"))
							oldData := f.Conjuncts(
								old,
								"the kernel rank is at most n",
								"the kernel has a triangular basis")
							oldTriangular := f.Conjuncts(
								f.Unfolded(oldData[1], IntegerTriangularBasisDef),
								"the old family is an indexed basis",
								"old pivots are positive and vanish to their right",
								"old pivots strictly increase")
							oldIndexData := f.Conjuncts(
								f.Unfolded(oldTriangular[0], linear_independence.IndexedModuleBasisDef),
								"the old indexing is injective",
								"the old image is a basis of K")
							wNonzero := f.Have(
								"the lift has a nonzero last coordinate",
								"w(n) ≠ 0",
								By(Normalized, dNonzero, liftData[1]))
							c, normalized := f.ObtainAs[Fun[Nat, Int]](
								"choose the splitting lift with positive last coordinate",
								"∃c:(num → int). "+
									"    c ∈ M ∧ "+
									"    0 < c(n) ∧ "+
									"    (∀v:(num → int). "+
									"        v ∈ M ⇒ "+
									"        ∃u:(num → int). ∃a:int. "+
									"            u ∈ M ∧ u(n) = 0 ∧ v = fun_add(int_ring.add,u,fun_smul(int_ring.mul,a,c)))",
								By(sub, liftData[0], wNonzero, liftData[2], At(positiveLift, n, M, w)),
								Named("c"))
							newData := f.Conjuncts(
								normalized,
								"the new vector lies in M",
								"its last coordinate is positive",
								"it splits every vector of M")
							F, fDef := f.LetAs[Set[Fun[Nat, Int]]]("F", "{e(i):(num → int) | i:num | i < r}")
							V, vDef := f.LetAs[ModuleOps[Int, Fun[Nat, Int]]](
								"V", "free_module_record(int_ring, {i:num | i < suc(n)})")
							onV := f.Have(
								"V is the ambient free module",
								"module_on(int_ring,V)",
								vDef.Rw(),
								By(free_module.FreeModuleOn.Read(int_real_lift.CommRingOn).At(
									f.TermAs[Set[Nat]]("{i:num | i < suc(n)}"))))
							oldBasis := f.Have(
								"the old vectors form a basis of K with the ambient operations",
								"module_basis(int_ring,restrict_module(V,K),F)",
								vDef.Rw(),
								By(oldIndexData[1], At(restrictionIndependent, n, f.TermAs[Nat]("suc(n)"), K)))
							oldSpan := f.Have(
								"the old family is independent and spans K",
								"module_independent(int_ring,V,F) ∧ module_span(int_ring,V,F) = K",
								By(kernelSub, oldBasis, At(linear_independence.BasisRestrict.Read(onV), K, F)))
							oldSpanData := f.Conjuncts(
								oldSpan,
								"the old family is independent",
								"the old span is K")
							newInV := f.Have(
								"the new vector lies in V",
								"c ∈ V.carrier",
								BySets(newData[0], sub, submodule.SubmoduleSubset.At(R, V, M)))
							killed := f.Have(
								"K has last coordinate zero",
								"∀v:(num → int). v ∈ K ⇒ v(n) = 0",
								BySets(kDef))
							noOldMultiple := f.Have(
								"no nonzero multiple of the new vector lies in the old span",
								Statement{
									Binders: "∀a:int.",
									Hypotheses: []string{
										"a ∈ ring_carrier(int_ring)",
										"V.smul(a, c) ∈ module_span(int_ring, V, F)",
									},
									Conclusion: "a = ring_zero(int_ring)",
								},
								By(vDef, oldSpanData[1], killed, newData[1], At(noMultiple, n, V, K, F, c)))
							independent := f.Have(
								"adjoin the new vector without a relation",
								"module_independent(int_ring,V,insert(c,F))",
								By(
									noOldMultiple,
									newInV,
									oldSpanData[0],
									At(linear_independence.IndependentInsertNoMultiple.Read(onV), F, c)))
							fInK := f.Have(
								"old basis vectors lie in K",
								"F ⊆ K",
								By(Normalized, oldSpanData[1], submodule.SubsetSpan.At(R, V, F)))
							gInM := f.Have(
								"all enlarged basis vectors lie in M",
								"insert(c,F) ⊆ M",
								BySets(fInK, kDef, newData[0]))
							G, gDef := f.LetAs[Set[Fun[Nat, Int]]]("G", "insert(c,F)")
							spanInside := f.Have(
								"the enlarged span lies in M",
								"module_span(int_ring,V,G) ⊆ M",
								By(gInM, sub, submodule.SpanLeast.At(R, V, G, M)))
							spanFormula := f.Have(
								"the enlarged span is a new-vector multiple plus an old-span vector",
								"module_span(int_ring,V,G) = "+
									"{V.add(V.smul(a,c),u):(num → int) | "+
									"    a:int,u:(num → int) | "+
									"    a ∈ ring_carrier(int_ring) ∧ u ∈ module_span(int_ring,V,F)}",
								gDef.Rw(),
								By(
									oldSpanData[0],
									linear_independence.IndependentInCarrier.At(R, V, F),
									newInV,
									At(submodule.SpanInsert.Read(onV), F, c)))
							nativeSplit := f.Simplified(
								newData[2],
								Fwd(int_real_lift.IntRingDef),
								Fwd(module_record.RingAddDef),
								Fwd(module_record.RingMulDef))
							covers := f.Have(
								"the split puts every vector of M in the enlarged span",
								"∀v:(num → int). v ∈ M ⇒ v ∈ module_span(int_ring,V,G)",
								Derive(func(g *Argument) {
									v := g.FixAs[Fun[Nat, Int]]("v")
									vIn := g.Assume()
									u, scalar, split := g.Obtain2As[Fun[Nat, Int], Int](
										"split v along the positive lift",
										"∃u:(num → int). ∃a:int. u ∈ M ∧ u(n) = 0 ∧ v = V.add(u,V.smul(a,c))",
										vDef.Rw(),
										By(vIn, nativeSplit.At(v)),
										Named("u", "scalar"))
									pieces := g.Conjuncts(
										split,
										"u lies in M",
										"u has last coordinate zero",
										"v is u plus the new-vector multiple")
									uInSpan := g.Have(
										"u lies in the old span",
										"u ∈ module_span(int_ring,V,F)",
										BySets(pieces[0], pieces[1], oldSpanData[1], kDef))
									scalarIn := g.Have(
										"the coefficient is an integer scalar",
										"scalar ∈ ring_carrier(int_ring)",
										Cite(int_real_lift.IntegerRingCarrierUniversal))
									carriers := g.Have(
										"both summands lie in V",
										"u ∈ V.carrier ∧ V.smul(scalar,c) ∈ V.carrier",
										BySets(
											pieces[0],
											sub,
											newInV,
											submodule.SubmoduleSubset.At(R, V, M),
											At(module.SmulIn.Read(onV), scalar, c)))
									swapped := g.Have(
										"commute the two summands",
										"v = V.add(V.smul(scalar,c),u)",
										By(
											Normalized,
											pieces[2],
											carriers,
											At(module.AddComm.Read(onV), u, g.TermAs[Fun[Nat, Int]]("V.smul(scalar,c)"))))
									g.Show(
										"the span formula contains this decomposition",
										spanFormula.Rw(),
										BySets(swapped, scalarIn, uInSpan))
								}))
							spans := f.Have(
								"the enlarged family spans M",
								"module_span(int_ring,V,G) = M",
								BySets(covers, spanInside))
							basis := f.Have(
								"the enlarged family is a basis of M",
								"module_basis(int_ring,restrict_module(V,M),G)",
								By(sub, independent, spans, At(linear_independence.BasisRestrict.Read(onV), M, G)))
							B, bDef := f.LetAs[Fun2[Nat, Nat, Int]]("B", "λi:num. COND(i < r,e(i),c)")
							P, pDef := f.LetAs[Fun[Nat, Nat]]("P", "λi:num. COND(i < r,p(i),n)")
							fresh := f.Have(
								"the positive lift differs from every old vector",
								"∀i:num. i < r ⇒ e(i) ≠ c",
								Derive(func(g *Argument) {
									i := g.FixAs[Nat]("i")
									iIn := g.Assume()
									nonzero := g.Have(
										"the new last coordinate is nonzero",
										"c(n) ≠ 0",
										ByArith(newData[1]))
									g.Show(
										"the old vector's last coordinate is zero, so their last coordinates distinguish the vectors",
										By(Normalized, nonzero, iIn, oldTriangular[1].At(i)))
								}))
							newInjective := f.Have(
								"the appended indexing is injective",
								"injective_on({i:num | i < suc(r)},B)",
								bDef.Rw(),
								By(oldIndexData[0], fresh, At(appendInjective, r, e, c)))
							image := f.Have(
								"the appended image is G",
								"{B(i):(num → int) | i:num | i < suc(r)} = G",
								bDef.Rw(),
								gDef.Rw(),
								fDef.Rw(),
								By(At(appendImage, r, e, c)))
							indexed := f.Have(
								"the appended family is an indexed basis of M",
								"indexed_module_basis( "+
									"    int_ring,restrict_module(free_module_record(int_ring,{i:num | i < suc(n)}),M),suc(r),B)",
								Unfold(linear_independence.IndexedModuleBasisDef),
								vDef.Rw(),
								By(newInjective, image, basis))
							ambientNew := f.Have(
								"the new vector has ambient support",
								"c ∈ free_module_record(int_ring,{i:num | i < suc(n)}).carrier",
								vDef.Rw(),
								By(newInV))
							rightZero := f.Have(
								"the new vector vanishes right of n",
								"∀j:num. n < j ⇒ c(j) = 0",
								Derive(func(g *Argument) {
									g.FixAs[Nat]("j")
									toRight := g.Assume()
									outside := g.Have(
										"j lies outside the ambient support",
										"¬(j < suc(n))",
										ByArith(toRight))
									g.Show(
										"support containment gives the zero coordinate",
										BySets(ambientNew, At(support, g.TermAs[Nat]("suc(n)"), c), outside))
								}))
							pivots := f.Have(
								"all appended pivots are positive and vanish to their right",
								"∀i:num. i < suc(r) ⇒ P(i) < suc(n) ∧ 0 < B(i, P(i)) ∧ (∀j:num. P(i) < j ⇒ B(i, j) = 0)",
								bDef.Rw(),
								pDef.Rw(),
								Derive(func(g *Argument) {
									i := g.FixAs[Nat]("i")
									g.Assume()
									g.Cases(g.Term("i < r"))
									g.When(
										"an old index keeps its old pivot",
										func(h *Argument, oldIndex Fact) {
											below := h.Have(
												"the old pivot is below the new dimension",
												"p(i) < suc(n)",
												ByArith(oldIndex, oldTriangular[1].At(i)))
											h.Show(
												"retain its positive pivot and right-zero coordinates",
												By(Normalized, oldIndex, oldTriangular[1].At(i), below))
										})
									g.Otherwise(
										"the appended index uses pivot n",
										func(h *Argument, newIndex Fact) {
											h.Show(
												"the positive lift supplies the final pivot",
												By(Normalized, newIndex, newData[1], rightZero, nat_order.LessThanSucClause.At(n, n)))
										})
								}))
							increasing := f.Have(
								"the appended pivots strictly increase",
								"∀i j:num. i < j ∧ j < suc(r) ⇒ P(i) < P(j)",
								pDef.Rw(),
								Derive(func(g *Argument) {
									i, j := g.FixAs[Nat]("i"), g.FixAs[Nat]("j")
									ordered := g.Assume()
									iOld := g.Have(
										"the earlier index is old",
										"i < r",
										ByArith(ordered))
									g.Cases(g.Term("j < r"))
									g.When(
										"two old indices retain their pivot order",
										func(h *Argument, jOld Fact) {
											h.Show(
												"use the old strictly increasing pivot map",
												By(iOld, jOld, ordered, oldTriangular[2].At(i, j)))
										})
									g.Otherwise(
										"the final pivot follows every old pivot",
										func(h *Argument, jNew Fact) {
											h.Show(
												"every old pivot is below n",
												By(iOld, jNew, oldTriangular[1].At(i)))
										})
								}))
							bound := f.Have(
								"adjoining one vector preserves the rank bound",
								"suc(r) ≤ suc(n)",
								ByArith(oldData[0]))
							f.Show(
								"the appended basis and pivot map complete the induction",
								Witness(f.TermAs[Nat]("suc(r)")),
								Witness(B),
								Witness(P),
								By(
									bound,
									indexed,
									pivots,
									increasing,
									IntegerTriangularBasisDef.At(f.TermAs[Nat]("suc(n)"), f.TermAs[Nat]("suc(r)"), M, B, P)))
						})
				})
		})

	}),
})}

// LinearCombinationCoordinate — a coordinate of an integer combination of
// integer vectors is the same combination of their coordinates: evaluation
// at j passes through the finite sum, each summand read as an integer.
var LinearCombinationCoordinate = linearCombinationCoordinateThm{family.Add(registry.ProofEntry{
	Name: "LinearCombinationCoordinate",
	Key:  "prop_7ee3b337dc0262da",
	Build: family.Theorem("∀n:num. ∀a:(num → int). ∀b:(num → num → int). ∀j:num. "+
		"    module_sum(fun_add(int_add), "+
		"        fun_zero(int_of_num(0)), "+
		"        {i:num | i < n}, "+
		"        λi:num. fun_smul(int_mul, a(i), b(i)), "+
		"        j) = "+
		"    module_sum(int_add, 0, {i:num | i < n}, λi:num. a(i) * b(i, j))",
		func(arg *Argument, n *Expr[Nat], a *Arrow[Nat, Int], b *Arrow2[Nat, Nat, Int], j *Expr[Nat]) {
			R := arg.TermAs[RingOps[Int]]("int_ring")
			V := arg.TermAs[ModuleOps[Int, Int]]("regular_module(int_ring)")
			I := arg.TermAs[Set[Nat]]("{i:num | i < n}")
			members := arg.Have(
				"every summand coordinate is an integer",
				"∀i z:num. i < n ⇒ fun_smul(int_mul, a(i), b(i), z) ∈ regular_module(int_ring).carrier",
				By(int_real_lift.IntegerRingCarrierUniversal, module_record.RegularModuleDef))
			applied := arg.Have(
				"evaluation passes through the finite sum",
				"module_sum(fun_add(regular_module(int_ring).add), "+
					"    fun_zero(regular_module(int_ring).zero), "+
					"    {i:num | i < n}, "+
					"    λi:num. fun_smul(int_mul, a(i), b(i)), "+
					"    j) = "+
					"module_sum(regular_module(int_ring).add, "+
					"    regular_module(int_ring).zero, "+
					"    {i:num | i < n}, "+
					"    λi:num. fun_smul(int_mul, a(i), b(i), j))",
				BySets(
					members,
					characteristic_zero.IntegerRingRegularModule,
					num_segment.FiniteBelowStrict.At(n),
					function_module.ModuleSumApply.At(
						R, V, I, arg.TermAs[Fun2[Nat, Nat, Int]]("λi:num. fun_smul(int_mul, a(i), b(i))"), j)))
			arg.Show(
				"use native integer multiplication at each coordinate",
				SimpAll(
					Fwd(module_record.RegularModuleDef),
					Fwd(int_real_lift.IntRingDef),
					Fwd(module_record.ModAddDef),
					Fwd(module_record.ModZeroDef),
					Fwd(function_module.FunSmulDef)),
				By(applied))
		}),
})}

// TriangularQuotientRepresentatives reduces coordinates from right to left.
// The largest nonzero coefficient of a lattice difference would change its
// pivot coordinate by a nonzero multiple of the diagonal, which two bounded
// remainders cannot do.
var TriangularQuotientRepresentatives = triangularQuotientRepresentativesThm{family.Add(registry.ProofEntry{
	Name: "TriangularQuotientRepresentatives",
	Key:  "prop_ca6eec7851dacd65",
	Build: family.Sections(Statement{
		Binders: "∀n:num. ∀M:set(num → int). ∀b:(num → num → int). ∀X:set(num → int).",
		Hypotheses: []string{
			"submodule(int_ring, «ℤⁿ», M)",
			"integer_triangular_basis(n, M, n, b, λi:num. i)",
			"X ∈ left_cosets(«ℤⁿ».add, «ℤⁿ».carrier, M)",
		},
		Conclusion: "∃v:(num → int). " +
			"    v ∈ X ∧ " +
			"    v ∈ integer_remainder_box(n, λi:num. b(i, i)) ∧ " +
			"    (∀w:(num → int). w ∈ X ∧ w ∈ integer_remainder_box(n, λi:num. b(i, i)) ⇒ w = v)",
	}, func(ctx *Script, headline string) *GoalStackNode {
		closure := ctx.Lemma(Statement{
			Binders:    "∀n:num. ∀M:set(num → int).",
			Hypotheses: []string{"submodule(int_ring, «ℤⁿ», M)"},
			Conclusion: "(λj:num. int_of_num(0)) ∈ M ∧ " +
				"(∀u v:(num → int). u ∈ M ∧ v ∈ M ⇒ (λj:num. u(j) - v(j)) ∈ M) ∧ " +
				"(∀c:int. ∀u:(num → int). u ∈ M ⇒ (λj:num. c * u(j)) ∈ M)",
		}, func(a *Argument) {
			a.Show(
				"submodules are closed under native integer vector operations",
				Simp(
					Fwd(int_real_lift.IntRingDef),
					Fwd(submodule.SubmoduleDef),
					Fwd(free_module.FreeModuleRecordDef),
					Fwd(module_record.ModuleAdditiveGroupDef),
					Fwd(function_module.FunAddDef),
					Fwd(function_module.FunNegDef),
					Fwd(function_module.FunSmulDef)),
				Unfold(group.SubgroupDef),
				Simp(Fwd(int_real_lift.SubAddNeg), Fwd(function_module.FunZeroDef), Fwd(set_basic.InUniv)),
				StripQuant(),
				StripImp(),
				Given(func(b *Argument, closed Fact) {
					b.Show(
						"zero, differences and scalar multiples stay in M",
						By(closed))
				}))
		})
		ambient := ctx.Lemma("∀n:num. submodule(int_ring, «ℤⁿ», «ℤⁿ».carrier)", func(
			a *Argument,
			n *Expr[Nat],
		) {
			a.Show(
				"the ambient carrier is a submodule",
				By(
					free_module.FreeModuleOn.Read(int_real_lift.CommRingOn).At(a.TermAs[Set[Nat]]("{i:num | i < n}")),
					submodule.CarrierSubmodule))
		})
		difference := ctx.Lemma(Statement{
			Binders:    "∀n:num. ∀M:set(num → int). ∀u v:(num → int).",
			Hypotheses: []string{"submodule(int_ring, «ℤⁿ», M)", "u ∈ M", "v ∈ M"},
			Conclusion: "(λj:num. u(j) - v(j)) ∈ M",
		}, func(a *Argument, n *Expr[Nat], M *Expr[Set[Fun[Nat, Int]]], u, v *Arrow[Nat, Int], given Fact) {
			a.Show(
				"subtract two lattice vectors",
				By(given, At(closure, n, M)))
		})
		reduce := ctx.Lemma(Statement{
			Binders: "∀n:num. ∀M:set(num → int). ∀b:(num → num → int).",
			Hypotheses: []string{
				"submodule(int_ring, «ℤⁿ», M)",
				"∀i:num. i < n ⇒ b(i) ∈ M ∧ 0 < b(i, i) ∧ (∀j:num. i < j ⇒ b(i, j) = 0)",
			},
			Conclusion: "∀k:num. ∀v:(num → int). " +
				"    v ∈ «ℤⁿ».carrier ⇒ " +
				"    ∃w:(num → int). " +
				"        w ∈ «ℤⁿ».carrier ∧ " +
				"        (λj:num. w(j) - v(j)) ∈ M ∧ " +
				"        (∀j:num. k ≤ j ∧ j < n ⇒ 0 ≤ w(j) ∧ w(j) < b(j, j))",
		}, func(
			a *Argument,
			n *Expr[Nat],
			M *Expr[Set[Fun[Nat, Int]]],
			b *Arrow2[Nat, Nat, Int],
			given Fact,
		) {
			a.Show(
				"reduce successive coordinates downwards",
				ByInduction(At(
					nat_order.DownwardInduction,
					a.TermAs[Set[Nat]](
						"λk:num. ∀v:(num → int). "+
							"    v ∈ «ℤⁿ».carrier ⇒ "+
							"    ∃w:(num → int). "+
							"        w ∈ «ℤⁿ».carrier ∧ "+
							"        (λj:num. w(j) - v(j)) ∈ M ∧ "+
							"        (∀j:num. k ≤ j ∧ j < n ⇒ 0 ≤ w(j) ∧ w(j) < b(j, j))"),
					n),
					Case(
						"coordinates at or above n impose no condition",
						Derive(func(c *Argument) {
							c.FixAs[Nat]("k")
							beyond := c.Assume()
							v := c.FixAs[Fun[Nat, Int]]("v")
							vIn := c.Assume()
							c.Show(
								"keep the original vector",
								Witness(v),
								SplitConj(
									Case(
										"its difference from itself is the lattice zero",
										Simp(Fwd(int_real_lift.SubRefl)),
										By(vIn, given, At(closure, n, M))),
									Case(
										"the coordinate range is empty",
										ByArith(beyond))))
						})),
					Case(
						"subtract a multiple of the current positive pivot",
						Derive(func(c *Argument) {
							k := c.FixAs[Nat]("k")
							descending := c.Assume()
							v := c.FixAs[Fun[Nat, Int]]("v")
							vIn := c.Assume()
							induction := c.Conjuncts(
								descending,
								"k lies below n",
								"every higher coordinate range can be reduced")
							_, reduced := c.ObtainAs[Fun[Nat, Int]](
								"reduce the coordinates above k",
								"∃w:(num → int). "+
									"    w ∈ «ℤⁿ».carrier ∧ "+
									"    (λj:num. w(j) - v(j)) ∈ M ∧ "+
									"    (∀j:num. suc(k) ≤ j ∧ j < n ⇒ 0 ≤ w(j) ∧ w(j) < b(j, j))",
								By(induction[1].At(c.TermAs[Nat]("suc(k)"), v), vIn, nat_order.LessThanSucClause.At(k, k)),
								Named("w"))
							pivot := c.Have(
								"the current row has a positive last pivot",
								"b(k) ∈ M ∧ 0 < b(k, k) ∧ (∀j:num. k < j ⇒ b(k, j) = 0)",
								By(given, induction[0]))
							qDef := c.Let("q", c.TermAs[Int]("div(w(k), b(k, k))"))
							u, uDef := c.LetAs[Fun[Nat, Int]]("u", "λj:num. w(j) - q * b(k, j)")
							multiple := c.Have(
								"the pivot multiple lies in M",
								"(λj:num. q * b(k, j)) ∈ M",
								By(given, pivot, At(closure, n, M)))
							multipleIn := c.Have(
								"the same multiple has ambient support",
								"(λj:num. q * b(k, j)) ∈ «ℤⁿ».carrier",
								BySets(
									given,
									multiple,
									submodule.SubmoduleSubset.At(
										c.TermAs[RingOps[Int]]("int_ring"), c.TermAs[ModuleOps[Int, Fun[Nat, Int]]]("«ℤⁿ»"), M)))
							uIn := c.Have(
								"subtracting the multiple preserves support",
								"u ∈ «ℤⁿ».carrier",
								Derive(func(d *Argument) {
									data := d.Conjuncts(
										reduced,
										"w has ambient support",
										"w is congruent to v",
										"higher coordinates are reduced")
									d.Show(
										"the ambient carrier is closed under this difference",
										By(
											uDef,
											data[0],
											multipleIn,
											At(ambient, n),
											At(closure, n, d.TermAs[Set[Fun[Nat, Int]]]("«ℤⁿ».carrier"))))
								}))
							differenceEq := c.Have(
								"the new coset difference subtracts the same pivot multiple",
								"(λj:num. u(j) - v(j)) = λj:num. w(j) - v(j) - q * b(k, j)",
								Simp(Fwd(uDef)),
								Funext(),
								ByArith())
							congruent := c.Have(
								"the new vector remains congruent to v",
								"(λj:num. u(j) - v(j)) ∈ M",
								differenceEq.Rw(),
								By(
									given,
									reduced,
									multiple,
									At(
										difference,
										n,
										M,
										c.TermAs[Fun[Nat, Int]]("λj:num. w(j) - v(j)"),
										c.TermAs[Fun[Nat, Int]]("λj:num. q * b(k, j)"))))
							division := c.Have(
								"Euclidean division gives the new coordinate",
								"q * b(k, k) + rem(w(k), b(k, k)) = w(k) ∧ 0 ≤ rem(w(k), b(k, k)) ∧ rem(w(k), b(k, k)) < b(k, k)",
								ByArith(
									qDef,
									pivot,
									int_div_rem.DivisionAlgorithm.At(c.TermAs[Int]("w(k)"), c.TermAs[Int]("b(k, k)")),
									int_real_lift.AbsFixedIffNonneg.At(c.TermAs[Int]("b(k, k)"))))
							current := c.Have(
								"the current coordinate is now reduced",
								"0 ≤ u(k) ∧ u(k) < b(k, k)",
								uDef.Rw(),
								ByArith(division))
							unchanged := c.Have(
								"higher coordinates are unchanged",
								"∀j:num. k < j ⇒ u(j) = w(j)",
								Derive(func(d *Argument) {
									d.FixAs[Nat]("j")
									d.Assume()
									d.Show(
										"the row vanishes to the right of k",
										Simp(Fwd(uDef), Fwd(pivot)),
										ByArith())
								}))
							bounded := c.Have(
								"the whole remaining coordinate range is reduced",
								"∀j:num. k ≤ j ∧ j < n ⇒ 0 ≤ u(j) ∧ u(j) < b(j, j)",
								Derive(func(d *Argument) {
									j := d.FixAs[Nat]("j")
									rangeAt := d.Assume()
									data := d.Conjuncts(
										reduced,
										"w has ambient support",
										"w is congruent to v",
										"higher coordinates are reduced")
									d.Cases(d.Term("j = k"))
									d.When(
										"the pivot coordinate uses its new remainder",
										func(e *Argument, equal Fact) {
											e.Show(
												"use the current coordinate bound",
												By(Normalized, equal, current))
										})
									d.Otherwise(
										"a higher coordinate keeps its old remainder",
										func(e *Argument, different Fact) {
											above := e.Have(
												"j lies in the successor range",
												"k < j ∧ suc(k) ≤ j",
												ByArith(different, rangeAt))
											e.Show(
												"transfer the old bounds through the unchanged coordinate",
												By(Normalized, unchanged.At(j), data[2].At(j), above, rangeAt))
										})
								}))
							c.Show(
								"use the reduced vector",
								Witness(u),
								By(uIn, congruent, bounded))
						}))))
		})
		expand := ctx.Lemma(Statement{
			Binders: "∀n:num. ∀M:set(num → int). ∀b:(num → num → int). ∀v:(num → int).",
			Abbrev: Abbrev{
				{Name: "V", Text: "restrict_module(free_module_record(int_ring, {i:num | i < n}), M)"},
				{Name: "E", Text: "image(b, {i:num | i < n})"},
				{Name: "C", Text: "module_basis_coordinates(int_ring, «V», «E», v)"},
			},
			Hypotheses: []string{
				"submodule(int_ring, «ℤⁿ», M)",
				"indexed_module_basis(int_ring, «V», n, b)",
				"v ∈ M",
			},
			Conclusion: "∃a:(num → int). " +
				"    module_sum(fun_add(int_ring.add), " +
				"        fun_zero(int_ring.zero), " +
				"        {i:num | i < n}, " +
				"        λi:num. fun_smul(int_ring.mul, a(i), b(i))) = " +
				"    v",
		}, func(
			a *Argument,
			n *Expr[Nat],
			M *Expr[Set[Fun[Nat, Int]]],
			b *Arrow2[Nat, Nat, Int],
			v *Arrow[Nat, Int],
			given Fact,
		) {
			parts := a.Conjuncts(
				given,
				"M is a submodule",
				"b indexes its basis",
				"v lies in M")
			R := a.TermAs[RingOps[Int]]("int_ring")
			V := a.TermAs[ModuleOps[Int, Fun[Nat, Int]]]("«V»")
			I := a.TermAs[Set[Nat]]("{i:num | i < n}")
			E := a.TermAs[Set[Fun[Nat, Int]]]("«E»")
			onV := a.Have(
				"the restricted lattice is a module",
				"module_on(int_ring, «V»)",
				By(
					parts[0],
					free_module.FreeModuleOn.Read(int_real_lift.CommRingOn).At(I),
					submodule.SubmoduleModuleOn.At(R, a.TermAs[ModuleOps[Int, Fun[Nat, Int]]]("«ℤⁿ»"), M)))
			image := a.Have(
				"the image has its indexed set description",
				"«E» = {b(i):num → int | i:num | i < n}",
				BySets())
			indexed := a.Have(
				"the rows form a finite basis, indexed one-to-one",
				"finite(«E») ∧ module_basis(int_ring, «V», «E») ∧ injective_on({i:num | i < n}, b)",
				image.Rw(),
				By(parts[1], linear_independence.IndexedBasisImage.At(R, V, n, b)))
			expansion := a.Have(
				"basis coordinates expand v",
				"module_sum(«V».add, «V».zero, «E», λe:(num → int). «V».smul(«C»(e), e)) = v",
				By(onV, indexed, parts[2], module_dimension.BasisCoordinatesSpec.At(R, V, E, v)))
			rows := a.Have(
				"each indexed row lies in M",
				"∀i:num. i < n ⇒ b(i) ∈ M",
				a.ForEach(func(i *Expr[Nat]) Action {
					return BySets(parts[1], linear_independence.IndexedBasisInCarrier.At(R, V, n, b, i))
				}))
			summands := a.Have(
				"each expansion summand lies in the restricted module",
				"∀i:num. i < n ⇒ «V».smul(«C»(b(i)), b(i)) ∈ «V».carrier",
				By(onV, rows, int_real_lift.IntegerRingCarrierUniversal, module.SmulIn.Read(onV)))
			reindex := a.Have(
				"index the expansion by row numbers",
				"module_sum(«V».add, «V».zero, «E», λe:(num → int). «V».smul(«C»(e), e)) = "+
					"module_sum(«V».add, «V».zero, {i:num | i < n}, λi:num. «V».smul(«C»(b(i)), b(i)))",
				BySets(
					onV,
					indexed,
					summands,
					num_segment.FiniteBelowStrict.At(n),
					module.ModuleSumImage.At(
						R, V, I, b, a.TermAs[Fun[Fun[Nat, Int], Fun[Nat, Int]]]("λe:(num → int). «V».smul(«C»(e), e)"))))
			a.Show(
				"use the indexed coordinate coefficients",
				Witness(a.TermAs[Fun[Nat, Int]]("λi:num. «C»(b(i))")),
				By(expansion, reindex))
		})
		remainderMultiple := ctx.Lemma(Statement{
			Binders:    "∀a d x y:int.",
			Hypotheses: []string{"0 < d", "0 ≤ x", "x < d", "0 ≤ y", "y < d", "x - y = a * d"},
			Conclusion: "a = 0",
		}, func(arg *Argument, a, d, x, y *Expr[Int], given Fact) {
			abs := arg.Have(
				"a positive diagonal is its absolute value",
				"|d| = d",
				ByArith(given, int_real_lift.AbsFixedIffNonneg.At(d)))
			divisions := arg.Have(
				"x has two bounded division decompositions",
				"x = a * d + y ∧ 0 ≤ y ∧ y < |d| ∧ x = 0 * d + x ∧ 0 ≤ x ∧ x < |d|",
				ByArith(abs, given))
			arg.Show(
				"the two quotient coefficients agree",
				By(
					Normalized,
					divisions,
					int_div_rem.DivUnique.At(x, d, a, y),
					int_div_rem.DivUnique.At(x, d, arg.TermAs[Int]("0"), x)))
		})
		coefficients := ctx.Lemma(Statement{
			Binders: "∀n:num. ∀a:(num → int). ∀b:(num → num → int). ∀u v:(num → int).",
			Hypotheses: []string{
				"∀i:num. i < n ⇒ 0 < b(i, i) ∧ (∀j:num. i < j ⇒ b(i, j) = 0)",
				"∀j:num. module_sum(int_add, 0, {i:num | i < n}, λi:num. a(i) * b(i, j)) = u(j) - v(j)",
				"∀i:num. i < n ⇒ 0 ≤ u(i) ∧ u(i) < b(i, i) ∧ 0 ≤ v(i) ∧ v(i) < b(i, i)",
			},
			Conclusion: "∀i:num. i < n ⇒ a(i) = 0",
		}, func(
			arg *Argument,
			n *Expr[Nat],
			a *Arrow[Nat, Int],
			b *Arrow2[Nat, Nat, Int],
			u, v *Arrow[Nat, Int],
			given Fact,
		) {
			data := arg.Conjuncts(
				given,
				"the diagonal is positive and rows vanish to its right",
				"the scalar sums give the vector difference",
				"both vectors lie in the diagonal intervals")
			arg.Cases(arg.Term("∃i:num. i < n ∧ a(i) ≠ 0"))
			arg.Otherwise(
				"without a nonzero coefficient every coefficient vanishes",
				func(c *Argument, none Fact) {
					c.Show(
						"the coefficients are zero",
						By(Normalized, none))
				})
			arg.When(
				"a largest nonzero coefficient contradicts bounded remainders",
				func(c *Argument, some Fact) {
					bounded := c.Have(
						"nonzero coefficient indices are bounded by n",
						"∃N:num. ∀i:num. i < n ∧ a(i) ≠ 0 ⇒ i ≤ N",
						Witness(n),
						ByArith())
					j, largest := c.ObtainAs[Nat](
						"choose the largest nonzero coefficient",
						"∃j:num. j < n ∧ a(j) ≠ 0 ∧ (∀i:num. i < n ∧ a(i) ≠ 0 ⇒ i ≤ j)",
						By(some, bounded, nat_order.MaximumExists.At(c.TermAs[Set[Nat]]("λi:num. i < n ∧ a(i) ≠ 0"))),
						Named("j"))
					maximum := c.Conjuncts(
						largest,
						"j is an index",
						"its coefficient is nonzero",
						"every nonzero coefficient index is at most j")
					offDiagonal := c.Have(
						"all other rows contribute zero at coordinate j",
						"∀i:num. i < n ∧ i ≠ j ⇒ a(i) * b(i, j) = 0",
						Derive(func(d *Argument) {
							i := d.FixAs[Nat]("i")
							index := d.Assume()
							d.Cases(d.Term("i < j"))
							d.When(
								"an earlier row vanishes to the right of its pivot",
								func(e *Argument, earlier Fact) {
									e.Show(
										"its coordinate contribution is zero",
										Simp(Fwd(data[0])),
										ByArith())
								})
							d.Otherwise(
								"a later row has zero coefficient by maximality",
								func(e *Argument, notEarlier Fact) {
									later := e.Have(
										"i is not at most j",
										"¬(i ≤ j)",
										ByArith(notEarlier, index))
									zero := e.Have(
										"the coefficient at i vanishes",
										"a(i) = 0",
										By(maximum[2].At(i), index, later))
									e.Show(
										"its coordinate contribution is zero",
										ByArith(zero))
								})
						}))
					singleGuard := c.Have(
						"the scalar sum has just one potentially nonzero term",
						"finite({i:num | i < n}) ∧ "+
							"j ∈ {i:num | i < n} ∧ "+
							"(∀i:num. i ∈ {i:num | i < n} ⇒ a(i) * b(i,j) ∈ regular_module(int_ring).carrier) ∧ "+
							"(∀i:num. i ∈ {i:num | i < n} ∧ i ≠ j ⇒ a(i) * b(i,j) = regular_module(int_ring).zero)",
						Simp(Fwd(module_record.RegularModuleDef)),
						BySets(offDiagonal, maximum[0], num_segment.FiniteBelowStrict.At(n)))
					isolated := c.Have(
						"only the diagonal contribution remains",
						"module_sum(int_add, 0, {i:num | i < n}, λi:num. a(i) * b(i,j)) = a(j) * b(j,j)",
						By(
							singleGuard,
							module.ModuleSumSingle.Read(characteristic_zero.IntegerRingRegularModule).At(
								c.TermAs[Set[Nat]]("{i:num | i < n}"), j, c.TermAs[Fun[Nat, Int]]("λi:num. a(i) * b(i,j)"))))
					pivotDifference := c.Have(
						"the remainder difference is the diagonal multiple",
						"u(j) - v(j) = a(j) * b(j, j)",
						By(data[1].At(j), isolated))
					zero := c.Have(
						"bounded remainders force the coefficient to be zero",
						"a(j) = 0",
						By(
							data[0].At(j),
							data[2].At(j),
							maximum[0],
							pivotDifference,
							At(
								remainderMultiple,
								c.TermAs[Int]("a(j)"),
								c.TermAs[Int]("b(j, j)"),
								c.TermAs[Int]("u(j)"),
								c.TermAs[Int]("v(j)"))))
					c.Show(
						"this contradicts the selected nonzero coefficient",
						By(maximum[1], zero))
				})
		})
		zeroSum := ctx.Lemma(Statement{
			Binders:    "∀n:num. ∀a f:(num → int).",
			Hypotheses: []string{"∀i:num. i < n ⇒ a(i) = 0"},
			Conclusion: "module_sum(int_add, 0, {i:num | i < n}, λi:num. a(i) * f(i)) = 0",
		}, func(arg *Argument, n *Expr[Nat], a, f *Arrow[Nat, Int], zero Fact) {
			terms := arg.Have(
				"every summand is zero",
				"∀i:num. i < n ⇒ a(i) * f(i) = 0",
				By(zero, int_real_lift.MulLeftZero))
			arg.Show(
				"the finite sum vanishes",
				BySets(
					terms,
					num_segment.FiniteBelowStrict.At(n),
					module.ModuleSumZero.Read(characteristic_zero.IntegerRingRegularModule).At(
						arg.TermAs[Set[Nat]]("{i:num | i < n}"), arg.TermAs[Fun[Nat, Int]]("λi:num. a(i) * f(i)"))))
		})
		unique := ctx.Lemma(Statement{
			Binders: "∀n:num. ∀M:set(num → int). ∀b:(num → num → int). ∀u v:(num → int).",
			Hypotheses: []string{
				"submodule(int_ring, «ℤⁿ», M)",
				"indexed_module_basis(int_ring, restrict_module(«ℤⁿ», M), n, b)",
				"∀i:num. i < n ⇒ 0 < b(i, i) ∧ (∀j:num. i < j ⇒ b(i, j) = 0)",
				"(λj:num. u(j) - v(j)) ∈ M",
				"∀i:num. i < n ⇒ 0 ≤ u(i) ∧ u(i) < b(i, i) ∧ 0 ≤ v(i) ∧ v(i) < b(i, i)",
			},
			Conclusion: "u = v",
		}, func(
			arg *Argument,
			n *Expr[Nat],
			M *Expr[Set[Fun[Nat, Int]]],
			b *Arrow2[Nat, Nat, Int],
			u, v *Arrow[Nat, Int],
			given Fact,
		) {
			data := arg.Conjuncts(
				given,
				"M is a submodule",
				"b is its indexed basis",
				"the rows have positive last pivots",
				"the difference lies in M",
				"both vectors have bounded coordinates")
			a, expansion := arg.ObtainAs[Fun[Nat, Int]](
				"expand the lattice difference in the indexed basis",
				"∃a:(num → int). "+
					"    module_sum(fun_add(int_ring.add), "+
					"        fun_zero(int_ring.zero), "+
					"        {i:num | i < n}, "+
					"        λi:num. fun_smul(int_ring.mul, a(i), b(i))) = "+
					"    λj:num. u(j) - v(j)",
				By(
					data[0],
					data[1],
					data[3],
					At(expand, n, M, b, arg.TermAs[Fun[Nat, Int]]("λj:num. u(j) - v(j)"))),
				Named("a"))
			expansion = arg.Simplified(
				expansion,
				Fwd(int_real_lift.IntRingDef),
				Fwd(LinearCombinationCoordinate))
			coordinates := arg.Have(
				"the scalar coordinate sums expand the difference",
				"∀j:num. module_sum(int_add, 0, {i:num | i < n}, λi:num. a(i) * b(i, j)) = u(j) - v(j)",
				By(expansion))
			zero := arg.Have(
				"every coefficient of the difference vanishes",
				"∀i:num. i < n ⇒ a(i) = 0",
				By(data[2], data[4], coordinates, At(coefficients, n, a, b, u, v)))
			arg.Show(
				"the two vectors agree at every coordinate",
				Funext(),
				Derive(func(c *Argument) {
					c.FixAs[Nat]("j")
					vanishes := c.Have(
						"the difference sum is zero",
						"module_sum(int_add, 0, {i:num | i < n}, λi:num. a(i) * b(i, j)) = 0",
						By(zero, At(zeroSum, n, a, c.TermAs[Fun[Nat, Int]]("λi:num. b(i, j)"))))
					coordinate := c.Have(
						"the same sum is the coordinate difference",
						"module_sum(int_add, 0, {i:num | i < n}, λi:num. a(i) * b(i, j)) = u(j) - v(j)",
						By(expansion))
					c.Show(
						"the coordinate difference vanishes",
						ByArith(vanishes, coordinate))
				}))
		})
		cosetMember := ctx.Lemma(Statement{
			Binders:    "∀n:num. ∀M:set(num → int). ∀x v:(num → int).",
			Hypotheses: []string{"submodule(int_ring, «ℤⁿ», M)", "x ∈ «ℤⁿ».carrier", "v ∈ «ℤⁿ».carrier"},
			Conclusion: "v ∈ left_coset(«ℤⁿ».add, x, M) ⇔ (λj:num. v(j) - x(j)) ∈ M",
		}, func(a *Argument, n *Expr[Nat], M *Expr[Set[Fun[Nat, Int]]], x, v *Arrow[Nat, Int], given Fact) {
			data := a.Conjuncts(
				given,
				"M is a submodule",
				"x has ambient support",
				"v has ambient support")
			onFn := a.Have(
				"the ambient vectors form a module",
				"module_on(int_ring, «ℤⁿ»)",
				By(free_module.FreeModuleOn.Read(int_real_lift.CommRingOn).At(
					a.TermAs[Set[Nat]]("{i:num | i < n}"))))
			additive := module.AddGroupOn.Read(onFn)
			xm, vm :=
				proof.MemberOf(a.TermAs[Fun[Nat, Int]]("x"), data[1]),
				proof.MemberOf(a.TermAs[Fun[Nat, Int]]("v"), data[2])
			coset := a.Have(
				"membership is measured by the additive group difference",
				"v ∈ left_coset(«ℤⁿ».add, x, M) ⇔ "+
					"module_additive_group(«ℤⁿ»).mul(module_additive_group(«ℤⁿ»).inv(x), v) ∈ M",
				By(
					data[0],
					submodule.SubmoduleSubset.At(
						a.TermAs[RingOps[Int]]("int_ring"), a.TermAs[ModuleOps[Int, Fun[Nat, Int]]]("«ℤⁿ»"), M),
					group.InLeftCosetOn.Read(additive).At(xm, vm, M)))
			nativeCoset := a.Simplified(
				coset,
				Fwd(module_record.ModuleAdditiveGroupDef),
				Fwd(free_module.FreeModuleRecordDef),
				Fwd(int_real_lift.IntRingDef),
				Fwd(function_module.FunAddDef),
				Fwd(function_module.FunNegDef))
			order := a.Have(
				"the additive group difference is the native integer difference",
				"(λj:num. v(j) - x(j)) = λj:num. -x(j) + v(j)",
				Funext(),
				ByArith())
			a.Show(
				"read the coset condition in native vector coordinates",
				Simp(
					Fwd(module_record.ModuleAdditiveGroupDef),
					Fwd(free_module.FreeModuleRecordDef),
					Fwd(int_real_lift.IntRingDef),
					Fwd(function_module.FunAddDef),
					Fwd(function_module.FunNegDef)),
				order.Rw(),
				By(nativeCoset))
		})
		return ctx.Theorem(headline, func(
			a *Argument,
			n *Expr[Nat],
			M *Expr[Set[Fun[Nat, Int]]],
			b *Arrow2[Nat, Nat, Int],
			X *Expr[Set[Fun[Nat, Int]]],
			given Fact,
		) {
			data := a.Conjuncts(
				given,
				"M is an integer submodule",
				"b is a full triangular basis",
				"X is a coset of M")
			R := a.TermAs[RingOps[Int]]("int_ring")
			Fn := a.TermAs[ModuleOps[Int, Fun[Nat, Int]]]("«ℤⁿ»")
			V := a.TermAs[ModuleOps[Int, Fun[Nat, Int]]]("restrict_module(«ℤⁿ», M)")
			indexed := a.Have(
				"the full triangular rows index a basis",
				"indexed_module_basis(int_ring, restrict_module(«ℤⁿ», M), n, b)",
				By(data[1], IntegerTriangularBasisDef.At(n, n, M, b, a.TermAs[Fun[Nat, Nat]]("λi:num. i"))))
			pivots := a.Have(
				"the positive diagonal contains the last nonzero coordinates",
				"∀i:num. i < n ⇒ 0 < b(i, i) ∧ (∀j:num. i < j ⇒ b(i, j) = 0)",
				By(data[1], IntegerTriangularBasisDef.At(n, n, M, b, a.TermAs[Fun[Nat, Nat]]("λi:num. i"))))
			rows := a.Have(
				"all indexed rows belong to M",
				"∀i:num. i < n ⇒ b(i) ∈ M",
				a.ForEach(func(i *Expr[Nat]) Action {
					return BySets(indexed, linear_independence.IndexedBasisInCarrier.At(R, V, n, b, i))
				}))
			onFn := a.Have(
				"the ambient vectors form a module",
				"module_on(int_ring, «ℤⁿ»)",
				By(free_module.FreeModuleOn.Read(int_real_lift.CommRingOn).At(
					a.TermAs[Set[Nat]]("{i:num | i < n}"))))
			additive := module.AddGroupOn.Read(onFn)
			x, presentation := a.ObtainAs[Fun[Nat, Int]](
				"choose a vector presenting the coset",
				"∃x:(num → int). X = left_coset(«ℤⁿ».add, x, M) ∧ x ∈ «ℤⁿ».carrier",
				By(
					data[2],
					data[0],
					submodule.SubmoduleSubset.At(R, Fn, M),
					quotient_group.InLeftCosets.Read(additive).At(M, X)),
				Named("x"))
			present := a.Conjuncts(
				presentation,
				"X is the coset of x",
				"x has ambient support")
			basisData := a.Have(
				"the rows satisfy the reduction hypotheses",
				"∀i:num. i < n ⇒ b(i) ∈ M ∧ 0 < b(i, i) ∧ (∀j:num. i < j ⇒ b(i, j) = 0)",
				By(rows, pivots))
			v, reduced := a.ObtainAs[Fun[Nat, Int]](
				"reduce the chosen vector through coordinate zero",
				"∃v:(num → int). "+
					"    v ∈ «ℤⁿ».carrier ∧ "+
					"    (λj:num. v(j) - x(j)) ∈ M ∧ "+
					"    (∀j:num. 0 ≤ j ∧ j < n ⇒ 0 ≤ v(j) ∧ v(j) < b(j, j))",
				By(data[0], present[1], basisData, At(reduce, n, M, b, a.TermAs[Nat]("0"), x)),
				Named("v"))
			rem := a.Conjuncts(
				reduced,
				"v has ambient support",
				"v differs from x by a lattice vector",
				"all coordinates from zero are reduced")
			inX := a.Have(
				"the reduced vector belongs to X",
				"v ∈ X",
				By(data[0], present[0], present[1], rem[0], rem[1], At(cosetMember, n, M, x, v)))
			bounds := a.Have(
				"every coordinate below n is reduced",
				"∀i:num. i < n ⇒ 0 ≤ v(i) ∧ v(i) < b(i, i)",
				By(rem[2], nat_order.ZeroLessEq))
			inBox := a.Have(
				"the reduced vector belongs to the remainder box",
				"v ∈ integer_remainder_box(n, λi:num. b(i, i))",
				BySets(rem[0], bounds, integerRemainderBoxDef.At(n, a.TermAs[Fun[Nat, Int]]("λi:num. b(i, i)"))))
			a.Show(
				"v is the unique bounded representative of X",
				Witness(v),
				SplitConj(
					Case(
						"v lies in the required coset and remainder box",
						By(inX, inBox)),
					Case(
						"every other bounded representative equals v",
						Derive(func(c *Argument) {
							w := c.FixAs[Fun[Nat, Int]]("w")
							other := c.Assume()
							memberships := c.Conjuncts(
								other,
								"w belongs to X",
								"w belongs to the remainder box")
							box := c.Have(
								"w has ambient support and reduced coordinates",
								"w ∈ «ℤⁿ».carrier ∧ (∀i:num. i < n ⇒ 0 ≤ w(i) ∧ w(i) < b(i, i))",
								BySets(memberships[1], integerRemainderBoxDef.At(n, c.TermAs[Fun[Nat, Int]]("λi:num. b(i, i)"))))
							wData := c.Conjuncts(
								box,
								"w has ambient support",
								"w has reduced coordinates")
							wDifference := c.Have(
								"w differs from x by a lattice vector",
								"(λj:num. w(j) - x(j)) ∈ M",
								By(data[0], present[1], wData[0], memberships[0], present[0], At(cosetMember, n, M, x, w)))
							cancel := c.Have(
								"subtracting the common coset vector cancels",
								"(λj:num. w(j) - v(j)) = λj:num. w(j) - x(j) - (v(j) - x(j))",
								Funext(),
								ByArith())
							latticeDifference := c.Have(
								"the two representatives differ by a lattice vector",
								"(λj:num. w(j) - v(j)) ∈ M",
								cancel.Rw(),
								By(
									data[0],
									wDifference,
									rem[1],
									At(
										difference,
										n,
										M,
										c.TermAs[Fun[Nat, Int]]("λj:num. w(j) - x(j)"),
										c.TermAs[Fun[Nat, Int]]("λj:num. v(j) - x(j)"))))
							bothBounded := c.Have(
								"both representatives lie in the diagonal intervals",
								"∀i:num. i < n ⇒ 0 ≤ w(i) ∧ w(i) < b(i, i) ∧ 0 ≤ v(i) ∧ v(i) < b(i, i)",
								By(wData[1], bounds))
							c.Show(
								"triangular remainder uniqueness identifies w and v",
								By(data[0], indexed, pivots, latticeDifference, bothBounded, At(unique, n, M, b, w, v)))
						}))))
		})
	}),
})}

// TriangularIndexProduct counts the unique diagonal remainders in each coset:
// appending one bounded coordinate multiplies the box size by its interval length.
var TriangularIndexProduct = triangularIndexProductThm{family.Add(registry.ProofEntry{
	Name: "TriangularIndexProduct",
	Key:  "prop_671349c6270bae5a",
	Build: family.Sections(Statement{
		Binders: "∀n:num. ∀M:set(num → int). ∀b:(num → num → int).",
		Hypotheses: []string{
			"submodule(int_ring, «ℤⁿ», M)",
			"integer_triangular_basis(n, M, n, b, λi:num. i)",
		},
		Conclusion: "finite(left_cosets(«ℤⁿ».add, «ℤⁿ».carrier, M)) ∧ " +
			"card(left_cosets(«ℤⁿ».add, «ℤⁿ».carrier, M)) = " +
			"set_fold(λi:num. λa:num. num_of_int(b(i, i)) * a, {i:num | i < n}, 1)",
	}, func(ctx *Script, headline string) *GoalStackNode {
		supported := ctx.Lemma("∀n:num. ∀v:(num → int). "+
			"    v ∈ «ℤⁿ».carrier ⇔ ∀j:num. ¬(j < n) ⇒ v(j) = 0", func(a *Argument) {
			a.Show(
				"support below n is exactly a zero tail",
				Simp(Fwd(free_module.FreeModuleRecordDef), Fwd(function_module.FiniteSuppMember)),
				BySets(num_segment.FiniteBelowStrict, finite_set.FiniteSubset))
		})
		boxMember := ctx.Lemma("∀n:num. ∀d v:(num → int). "+
			"    v ∈ integer_remainder_box(n, d) ⇔ "+
			"    (∀j:num. ¬(j < n) ⇒ v(j) = 0) ∧ (∀j:num. j < n ⇒ 0 ≤ v(j) ∧ v(j) < d(j))", func(a *Argument) {
			a.Show(
				"a remainder has a zero tail and bounded initial coordinates",
				Simp(Fwd(integerRemainderBoxDef), Fwd(supported)),
				BySets())
		})
		intervalSize := ctx.Lemma(Statement{
			Binders: "∀d:int.",
			Hypotheses: []string{
				"0 < d",
			},
			Conclusion: "has_size({z:int | 0 ≤ z ∧ z < d}, num_of_int(d))",
		}, func(a *Argument, d *Expr[Int], positive Fact) {
			interval := a.Have(
				"the half-open interval ends at d minus one",
				"{z:int | 0 ≤ z ∧ z < d} = {z:int | 0 ≤ z ∧ z ≤ d - 1}",
				Simp(Fwd(set_basic.Extension)),
				Derive(func(b *Argument) {
					discrete := b.Have(
						"strict integer bounds use the predecessor",
						"∀z:int. z < d ⇔ z ≤ d - 1",
						ByArith())
					b.Show(
						"the two intervals have the same members",
						By(discrete))
				}))
			length := a.Have(
				"positivity removes the maximum with zero",
				"max(d - 1 - 0 + 1, 0) = d",
				ByArith(positive))
			a.Show(
				"the integer interval has its natural length",
				interval.Rw(),
				By(
					length,
					int_embed.IntIntervalSize.At(a.TermAs[Int]("0"), a.TermAs[Int]("d - &1")),
					int_embed.OfNumRetract.At(a.TermAs[Nat]("card({z:int | 0 ≤ z ∧ z ≤ d - 1})")),
					cardinality.HasSizeDef))
		})
		productClauses := ctx.Lemma("∀d:(num → int). "+
			"    set_fold(λi:num. λa:num. num_of_int(d(i)) * a, {i:num | i < 0}, 1) = 1 ∧ "+
			"    (∀n:num. "+
			"        set_fold(λi:num. λa:num. num_of_int(d(i)) * a, {i:num | i < suc(n)}, 1) = "+
			"        num_of_int(d(n)) * "+
			"        set_fold(λi:num. λa:num. num_of_int(d(i)) * a, {i:num | i < n}, 1))", func(
			a *Argument,
			d *Arrow[Nat, Int],
		) {
			commutes := a.Have(
				"multiplication steps commute in the finite fold",
				Statement{
					Binders: "∀i j a:num.",
					Hypotheses: []string{
						"i ≠ j",
					},
					Conclusion: "num_of_int(d(i)) * (num_of_int(d(j)) * a) = num_of_int(d(j)) * (num_of_int(d(i)) * a)",
				},
				ByArith())
			a.Show(
				"an empty product is one and insertion adds the next factor",
				Simp(Fwd(num_segment.BelowStrictClauses)),
				BySets(
					commutes,
					cardinality.FiniteRecursion.At(
						a.TermAs[Fun2[Nat, Nat, Nat]]("λi:num. λa:num. num_of_int(d(i)) * a"), a.TermAs[Nat]("1")),
					num_segment.FiniteBelowStrict,
					nat_order.LessThanIrrefl))
		})
		appendIn := ctx.Lemma(Statement{
			Binders: "∀n:num. ∀d w:(num → int). ∀z:int.",
			Hypotheses: []string{
				"w ∈ integer_remainder_box(n, d)",
				"0 ≤ z",
				"z < d(n)",
			},
			Conclusion: "(λj:num. COND(j = n, z, w(j))) ∈ integer_remainder_box(suc(n), d)",
		}, func(a *Argument) {
			a.Show(
				"appending a bounded coordinate preserves the zero tail and bounds",
				Simp(Fwd(boxMember)),
				BySets(nat_order.LessThanSucClause))
		})
		truncate := ctx.Lemma(Statement{
			Binders: "∀n:num. ∀d v:(num → int).",
			Hypotheses: []string{
				"v ∈ integer_remainder_box(suc(n), d)",
			},
			Conclusion: "(λj:num. COND(j < n, v(j), 0)) ∈ integer_remainder_box(n, d) ∧ " +
				"0 ≤ v(n) ∧ " +
				"v(n) < d(n) ∧ " +
				"(λj:num. COND(j = n, v(n), COND(j < n, v(j), 0))) = v",
		}, func(a *Argument) {
			a.Show(
				"truncation and the last coordinate recover every bounded vector",
				Simp(Fwd(boxMember)),
				BySets(nat_order.LessThanSucClause))
		})
		appendCoordinateInjective := ctx.Lemma(Statement{
			Binders: "∀n:num. ∀d w u:(num → int). ∀z y:int.",
			Hypotheses: []string{
				"w ∈ integer_remainder_box(n, d)",
				"u ∈ integer_remainder_box(n, d)",
				"(λj:num. COND(j = n, z, w(j))) = (λj:num. COND(j = n, y, u(j)))",
			},
			Conclusion: "w = u ∧ z = y",
		}, func(a *Argument) {
			a.Show(
				"the appended vector determines its old vector and last coordinate",
				Simp(Fwd(boxMember)),
				BySets(nat_order.LessThanIrrefl))
		})
		successorBoxImage := ctx.Lemma("∀n:num. ∀d:(num → int). "+
			"    integer_remainder_box(suc(n), d) = "+
			"    {(λj:num. COND(j = n, z, w(j))):(num → int) | "+
			"        w:(num → int), "+
			"        z:int | "+
			"        w ∈ integer_remainder_box(n, d) ∧ 0 ≤ z ∧ z < d(n)}", func(
			a *Argument,
			n *Expr[Nat],
			d *Arrow[Nat, Int],
		) {
			a.Show(
				"appending coordinates gives exactly the successor box",
				Simp(Fwd(set_basic.Extension)),
				Derive(func(b *Argument) {
					v := b.FixAs[Fun[Nat, Int]]("v")
					b.Iff()
					b.Forward(
						"use the truncation and last coordinate",
						func(c *Argument, inBox Fact) {
							appended := c.Have(
								"these two coordinates append to v",
								"∃w:(num → int). ∃z:int. "+
									"    (w ∈ integer_remainder_box(n, d) ∧ 0 ≤ z ∧ z < d(n)) ∧ v = (λj:num. COND(j = n, z, w(j)))",
								Witness(c.TermAs[Fun[Nat, Int]]("λj:num. COND(j < n, v(j), 0)")),
								Witness(c.TermAs[Int]("v(n)")),
								By(inBox, At(truncate, n, d, v)))
							c.Show(
								"so v is one of the appended vectors",
								BySets(appended))
						})
					b.Backward(
						"each append image satisfies the box bounds",
						func(c *Argument, inImage Fact) {
							w, z, presentation := c.Unpack2As[Fun[Nat, Int], Int](inImage, "w", "z")
							parts := c.Conjuncts(
								presentation,
								"the old vector belongs to the smaller box",
								"the last coordinate is nonnegative",
								"it is below its diagonal bound",
								"v is their appended vector")
							c.Show(
								"the append membership law applies",
								parts[3].Rw(),
								By(parts[1], parts[2], parts[0], At(appendIn, n, d, w, z)))
						})
				}))
		})
		emptyBox := ctx.Lemma("∀d:(num → int). "+
			"    integer_remainder_box(0, d) = {λj:num. int_of_num(0)}", func(a *Argument) {
			a.Show(
				"a vector with no supported coordinates is the zero vector",
				BySets(boxMember, nat_order.LessThanZeroClause))
		})
		pairMember := ctx.Lemma("∀n:num. ∀d w:(num → int). ∀z:int. "+
			"    w ∈ integer_remainder_box(n, d) ∧ z ∈ {t:int | 0 ≤ t ∧ t < d(n)} ⇔ "+
			"    w ∈ integer_remainder_box(n, d) ∧ 0 ≤ z ∧ z < d(n)", func(
			a *Argument,
			n *Expr[Nat],
			d, w *Arrow[Nat, Int],
			z *Expr[Int],
		) {
			a.Show(
				"membership in the coordinate pair is the stated pair of bounds",
				BySets())
		})
		boxSize := ctx.Lemma(Statement{
			Binders: "∀n:num. ∀d:(num → int).",
			Hypotheses: []string{
				"∀i:num. i < n ⇒ 0 < d(i)",
			},
			Conclusion: "has_size(integer_remainder_box(n, d), " +
				"    set_fold(λi:num. λa:num. num_of_int(d(i)) * a, {i:num | i < n}, 1))",
		}, func(a *Argument) {
			n := a.Binder("n")
			a.Induct(n)
			a.Base(
				"the empty box contributes one representative",
				Simp(
					Fwd(emptyBox),
					Fwd(productClauses),
					Fwd(cardinality.HasSizeDef),
					Fwd(cardinality.CardSing),
					Fwd(finite_set.FiniteSing)),
				Basic())
			a.Step(
				"one more coordinate multiplies the smaller box size",
				func(b *Argument, ih Fact) {
					d := b.FixAs[Fun[Nat, Int]]("d")
					positive := b.Assume()
					lowerPositive := b.Have(
						"the old diagonal remains positive",
						"∀i:num. i < n ⇒ 0 < d(i)",
						By(positive, nat_order.LessThanSucClause))
					oldSize := b.Have(
						"the induction hypothesis counts the old box",
						"has_size(integer_remainder_box(n, d), "+
							"    set_fold(λi:num. λa:num. num_of_int(d(i)) * a, {i:num | i < n}, 1))",
						By(ih.At(d), lowerPositive))
					lastPositive := b.Have(
						"the new diagonal entry is positive",
						"0 < d(n)",
						ByArith(positive.At(n)))
					lastSize := b.Have(
						"the new interval has its diagonal length",
						"has_size({z:int | 0 ≤ z ∧ z < d(n)}, num_of_int(d(n)))",
						By(lastPositive, At(intervalSize, b.TermAs[Int]("d(n)"))))
					injective := b.Have(
						"append is injective on the two coordinate sets",
						Statement{
							Binders: "∀w u:(num → int). ∀z y:int.",
							Hypotheses: []string{
								"w ∈ integer_remainder_box(n, d)",
								"z ∈ {t:int | 0 ≤ t ∧ t < d(n)}",
								"u ∈ integer_remainder_box(n, d)",
								"y ∈ {t:int | 0 ≤ t ∧ t < d(n)}",
								"(λj:num. COND(j = n, z, w(j))) = λj:num. COND(j = n, y, u(j))",
							},
							Conclusion: "w = u ∧ z = y",
						},
						By(At(appendCoordinateInjective, n, d)))
					oldProduct := b.TermAs[Nat]("set_fold(λi:num. λa:num. num_of_int(d(i)) * a, {i:num | i < n}, 1)")
					lastLength := b.TermAs[Nat]("num_of_int(d(n))")
					oldBox := b.TermAs[Set[Fun[Nat, Int]]]("integer_remainder_box(n, d)")
					lastInterval := b.TermAs[Set[Int]]("{t:int | 0 ≤ t ∧ t < d(n)}")
					appendMap := b.TermAs[Fun2[Fun[Nat, Int], Int, Fun[Nat, Int]]](
						"λw:(num → int). λz:int. λj:num. COND(j = n, z, w(j))")
					imageSize := b.Have(
						"the product image has the product of the two sizes",
						"has_size({(λj:num. COND(j = n, z, w(j))):(num → int) | "+
							"        w:(num → int), "+
							"        z:int | "+
							"        w ∈ integer_remainder_box(n, d) ∧ z ∈ {t:int | 0 ≤ t ∧ t < d(n)}}, "+
							"    set_fold(λi:num. λa:num. num_of_int(d(i)) * a, {i:num | i < n}, 1) * num_of_int(d(n)))",
						By(
							injective,
							oldSize,
							lastSize,
							cardinality.HasSizeProductImage.At(appendMap, oldBox, lastInterval, oldProduct, lastLength)))
					image := b.Have(
						"this product image is the whole successor box",
						"integer_remainder_box(suc(n), d) = "+
							"{(λj:num. COND(j = n, z, w(j))):(num → int) | "+
							"    w:(num → int), "+
							"    z:int | "+
							"    w ∈ integer_remainder_box(n, d) ∧ z ∈ {t:int | 0 ≤ t ∧ t < d(n)}}",
						Simp(Fwd(successorBoxImage), Fwd(pairMember)),
						Basic())
					b.Show(
						"the successor count is its diagonal product",
						image.Rw(),
						Simp(Fwd(productClauses)),
						Derive(func(c *Argument) {
							order := c.Have(
								"the two product orders agree",
								"num_of_int(d(n)) * set_fold(λi:num. λa:num. num_of_int(d(i)) * a, {i:num | i < n}, 1) = "+
									"set_fold(λi:num. λa:num. num_of_int(d(i)) * a, {i:num | i < n}, 1) * num_of_int(d(n))",
								ByArith())
							c.Show(
								"use the counted product image",
								order.Rw(),
								By(imageSize))
						}))
				})
		})
		return ctx.Theorem(headline, func(
			a *Argument,
			n *Expr[Nat],
			M *Expr[Set[Fun[Nat, Int]]],
			b *Arrow2[Nat, Nat, Int],
			given Fact,
		) {
			parts := a.Conjuncts(
				given,
				"M is an integer submodule",
				"b is a full triangular basis")
			R := a.TermAs[RingOps[Int]]("int_ring")
			ambient := a.TermAs[ModuleOps[Int, Fun[Nat, Int]]]("«ℤⁿ»")
			diagonal := a.TermAs[Fun[Nat, Int]]("λi:num. b(i, i)")
			box := a.TermAs[Set[Fun[Nat, Int]]]("integer_remainder_box(n, λi:num. b(i, i))")
			product := a.TermAs[Nat]("set_fold(λi:num. λa:num. num_of_int(b(i, i)) * a, {i:num | i < n}, 1)")
			quotient := a.TermAs[Set[Set[Fun[Nat, Int]]]]("left_cosets(«ℤⁿ».add, «ℤⁿ».carrier, M)")
			onFn := a.Have(
				"the ambient vectors form a module",
				"module_on(int_ring, «ℤⁿ»)",
				By(free_module.FreeModuleOn.Read(int_real_lift.CommRingOn).At(
					a.TermAs[Set[Nat]]("{i:num | i < n}"))))
			additive := module.AddGroupOn.Read(onFn)
			boxInside := a.Have(
				"every remainder has ambient support",
				"integer_remainder_box(n, λi:num. b(i, i)) ⊆ «ℤⁿ».carrier",
				BySets(integerRemainderBoxDef.At(n, diagonal)))
			positive := a.Have(
				"the triangular diagonal is positive",
				"∀i:num. i < n ⇒ 0 < b(i, i)",
				By(parts[1], IntegerTriangularBasisDef.At(n, n, M, b, a.TermAs[Fun[Nat, Nat]]("λi:num. i"))))
			size := a.Have(
				"the remainder box has the diagonal product size",
				"has_size(integer_remainder_box(n, λi:num. b(i, i)), "+
					"    set_fold(λi:num. λa:num. num_of_int(b(i, i)) * a, {i:num | i < n}, 1))",
				By(positive, At(boxSize, n, diagonal)))
			representatives := a.Have(
				"the box gives one representative in each coset",
				Statement{
					Binders: "∀X:set(num → int).",
					Hypotheses: []string{
						"X ∈ left_cosets(«ℤⁿ».add, «ℤⁿ».carrier, M)",
					},
					Conclusion: "∃v:(num → int). " +
						"    v ∈ X ∧ " +
						"    v ∈ integer_remainder_box(n, λi:num. b(i, i)) ∧ " +
						"    (∀w:(num → int). w ∈ X ∧ w ∈ integer_remainder_box(n, λi:num. b(i, i)) ⇒ w = v)",
				},
				By(given, At(TriangularQuotientRepresentatives, n, M, b)))
			quotientSize := a.Have(
				"the quotient has the same diagonal product size",
				"has_size(left_cosets(«ℤⁿ».add, «ℤⁿ».carrier, M), "+
					"    set_fold(λi:num. λa:num. num_of_int(b(i, i)) * a, {i:num | i < n}, 1))",
				By(
					parts[0],
					submodule.SubmoduleDef.At(R, ambient, M),
					boxInside,
					size,
					representatives,
					quotient_group.LeftCosetsTransversalSize.Read(additive).At(M, box, product)))
			a.Show(
				"read finiteness and cardinality from this size",
				By(quotientSize, cardinality.HasSizeDef.At(quotient, product)))
		})
	}),
})}
