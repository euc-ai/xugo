package int_lattice

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
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
	"github.com/euc-ai/xugo/library/proofs/nat_num/binomial"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/registry"
)

// ConstantSumCardinalityMultiple — summing one vector of an integer module
// over a finite index set gives the vector times the number of indices: by
// induction on the index set, the empty sum and the zero multiple are both
// zero, and a fresh index adds one more copy of the vector.
var ConstantSumCardinalityMultiple = constantSumCardinalityMultipleThm{family.Add(registry.ProofEntry{
	Name: "ConstantSumCardinalityMultiple",
	Key:  "prop_476ec3af7ebb56ed",
	Build: family.Theorem(Statement{
		Binders:    "∀M:module_ops(int, B). ∀x:B. ∀s:set(D).",
		Hypotheses: []string{"module_on(int_ring, M)", "x ∈ M.carrier", "finite(s)"},
		Conclusion: "module_sum(M.add, M.zero, s, λu:D. x) = M.smul(int_of_num(card(s)), x)",
	}, func(
		a *Argument,
		M *Expr[ModuleOps[Int, B]],
		moduleFact Fact,
		x *Expr[B],
		inModule Fact,
		s *Expr[Set[D]],
		finiteS Fact,
	) {
		a.Show(
			"one copy per element gives the cardinality multiple",
			ByInduction(finite_set.FiniteInductFresh, finiteS,
				Case(
					"the empty sum and the zero multiple are zero",
					Simp(Fwd(module.ModuleSumEmpty), Fwd(cardinality.CardClauses)),
					By(
						module.ZeroSmul.Read(moduleFact),
						inModule,
						int_real_lift.IntRingDef,
						module_record.RingZeroDef)),
				Case(
					"adjoining a fresh index adds one copy of the vector",
					Derive(func(b *Argument) {
						y := b.FixAs[D]("y")
						t := b.FixAs[Set[D]]("t")
						induction := b.Assume()
						n := b.TermAs[Int]("card(t)")
						one := b.TermAs[Int]("1")
						scaled := b.TermAs[B]("M.smul(int_of_num(card(t)), x)")
						successor := b.Have(
							"the successor scalar adds one copy of the vector",
							"M.smul(int_of_num(suc(card(t))), x) = M.add(x, M.smul(int_of_num(card(t)), x))",
							BySets(
								inModule,
								At(module.SmulAddRight.Read(moduleFact), n, one, x),
								At(module.SmulOne.Read(moduleFact), x),
								At(module.AddComm.Read(moduleFact), scaled, x),
								At(module.SmulIn.Read(moduleFact), n, x),
								int_embed.OfNumSuc.At(b.TermAs[Nat]("card(t)"))))
						b.Show(
							"sum insertion agrees with cardinality insertion",
							By(
								successor,
								inModule,
								induction,
								At(module.ModuleSumInsert.Read(moduleFact), t, y, b.TermAs[Fun[D, B]]("λu:D. x")),
								cardinality.InsertCountsOneMore.At(t, y)))
					}))))
	}),
})}

// FiniteModuleOrderAnnihilates — a finite integer module is annihilated
// by its order: translation by x permutes the carrier, so the sum of all
// vectors is that sum plus card(M.carrier) copies of x, and cancelling
// the sum leaves card(M.carrier)·x = 0.
var FiniteModuleOrderAnnihilates = finiteModuleOrderAnnihilatesThm{family.Add(registry.ProofEntry{
	Name: "FiniteModuleOrderAnnihilates",
	Key:  "prop_f4f5831a97bc56c0",
	Build: family.Theorem(Statement{
		Binders: "∀M:module_ops(int, B). ∀x:B.",
		Hypotheses: []string{
			"module_on(int_ring, M)",
			"finite(M.carrier)",
			"x ∈ M.carrier",
		},
		Conclusion: "M.smul(int_of_num(card(M.carrier)), x) = M.zero",
	}, func(
		a *Argument,
		M *Expr[ModuleOps[Int, B]],
		moduleFact, finiteCarrier Fact,
		x *Expr[B],
		inModule Fact,
	) {
		additive := module.AddGroupOn.Read(moduleFact)
		carrier := a.TermAs[Set[B]]("M.carrier")
		translate := a.TermAs[Fun[B, B]]("M.add(x)")
		identity := a.TermAs[Fun[B, B]]("λy:B. y")
		constant := a.TermAs[Fun[B, B]]("λy:B. x")
		closed := a.Have(
			"translation preserves the module carrier",
			"∀y:B. y ∈ M.carrier ⇒ M.add(x, y) ∈ M.carrier",
			By(inModule, At(group.MulIn.Read(additive), x)))
		inverseTranslation := a.Have(
			"negative translation supplies a preimage of each carrier element",
			Statement{
				Binders: "∀y:B.",
				Hypotheses: []string{
					"y ∈ M.carrier",
				},
				Conclusion: "M.neg(x) ∈ M.carrier ∧ " +
					"M.add(M.neg(x), y) ∈ M.carrier ∧ " +
					"M.add(x, M.add(M.neg(x), y)) = y",
			},
			By(
				inModule,
				At(group.InvIn.Read(additive), x),
				At(group.MulIn.Read(additive), a.TermAs[B]("M.neg(x)")),
				At(group.MulInvCancelLeftOn.Read(additive), x)))
		onto := a.Have(
			"translation maps the carrier onto itself",
			"image(M.add(x), M.carrier) = M.carrier",
			BySets(closed, inverseTranslation))
		oneToOne := a.Have(
			"additive cancellation makes translation injective",
			"injective_on(M.carrier, M.add(x))",
			By(
				inModule,
				At(group.LeftCancelOn.Read(additive), x),
				functions.InjectiveOnDef.At(carrier, translate)))
		invariant := a.Have(
			"permuting the carrier preserves its total sum",
			"module_sum(M.add, M.zero, M.carrier, λy:B. y) = "+
				"module_sum(M.add, M.zero, M.carrier, λy:B. M.add(x, y))",
			By(
				closed,
				onto,
				oneToOne,
				finiteCarrier,
				module.ModuleSumImage.Read(moduleFact).At(carrier, translate, identity)))
		expanded := a.Have(
			"the translated sum adds a constant sum to the total sum",
			"module_sum(M.add, M.zero, M.carrier, λy:B. M.add(x, y)) = "+
				"M.add(module_sum(M.add, M.zero, M.carrier, λy:B. x), "+
				"    module_sum(M.add, M.zero, M.carrier, λy:B. y))",
			By(inModule, finiteCarrier, module.ModuleSumAdd.Read(moduleFact).At(carrier, constant, identity)))
		sumsInCarrier := a.Have(
			"both finite sums and zero lie in the additive group",
			"module_sum(M.add, M.zero, M.carrier, λy:B. x) ∈ M.carrier ∧ "+
				"module_sum(M.add, M.zero, M.carrier, λy:B. y) ∈ M.carrier ∧ "+
				"M.zero ∈ M.carrier",
			By(
				group.OneIn.Read(additive),
				inModule,
				finiteCarrier,
				module.ModuleSumIn.Read(moduleFact).At(carrier, constant),
				module.ModuleSumIn.Read(moduleFact).At(carrier, identity)))
		total := a.TermAs[B]("module_sum(M.add, M.zero, M.carrier, λy:B. y)")
		repeated := a.TermAs[B]("module_sum(M.add, M.zero, M.carrier, λy:B. x)")
		a.Show(
			"cancel the total sum to annihilate the translating vector",
			By(
				invariant,
				expanded,
				inModule,
				finiteCarrier,
				sumsInCarrier,
				At(group.LeftIdentityOn.Read(additive), total),
				At(group.RightCancelOn.Read(additive), total, repeated, a.TermAs[B]("M.zero")),
				ConstantSumCardinalityMultiple.At(M, x, carrier)))
	}),
})}

// IndexAnnihilatesQuotient — multiplication by the finite index sends the
// ambient module into the submodule: the quotient is a finite integer
// module, so its order kills every class, and the class of a vector is
// the zero class exactly when the vector lies in the submodule.
var IndexAnnihilatesQuotient = indexAnnihilatesQuotientThm{family.Add(registry.ProofEntry{
	Name: "IndexAnnihilatesQuotient",
	Key:  "prop_d5d24dff4d5c237",
	Build: family.Theorem(Statement{
		Binders: "∀M:module_ops(int, B). ∀N:set(B).",
		Hypotheses: []string{
			"module_on(int_ring, M)",
			"submodule(int_ring, M, N)",
			"finite(left_cosets(M.add, M.carrier, N))",
		},
		Conclusion: "image(M.smul(int_of_num(card(left_cosets(M.add, M.carrier, N)))), M.carrier) ⊆ N",
	}, func(a *Argument, M *Expr[ModuleOps[Int, B]], N *Expr[Set[B]], assumptions Fact) {
		moduleFact := a.Have(
			"the ambient structure is an integer module",
			"module_on(int_ring, M)",
			By(assumptions))
		quotientOperations := a.Have(
			"the quotient carrier, zero and scalar action are the coset operations",
			"quotient_module(M, N).carrier = left_cosets(M.add, M.carrier, N) ∧ "+
				"quotient_module(M, N).zero = N ∧ "+
				"(∀c:int. ∀X:set(B). quotient_module(M, N).smul(c, X) = quotient_smul(M.add, M.smul, N, c, X))",
			Simp(
				Fwd(submodule.QuotientModuleDef),
				Fwd(module_record.ModCarrierDef),
				Fwd(module_record.ModZeroDef),
				Fwd(module_record.ModSmulDef)),
			Basic())
		quotientKilled := a.Have(
			"the finite quotient is annihilated by its cardinality",
			Statement{
				Binders: "∀X:set(B).",
				Hypotheses: []string{
					"X ∈ left_cosets(M.add, M.carrier, N)",
				},
				Conclusion: "quotient_smul(M.add, " +
					"    M.smul, " +
					"    N, " +
					"    int_of_num(card(left_cosets(M.add, M.carrier, N))), " +
					"    X) = " +
					"N",
			},
			By(
				submodule.QuotientModuleOn.Read(moduleFact).At(N),
				quotientOperations,
				assumptions,
				FiniteModuleOrderAnnihilates.Inst[Set[B]]().At(
					a.TermAs[ModuleOps[Int, Set[B]]]("quotient_module(M, N)"))))
		R := a.TermAs[RingOps[Int]]("int_ring")
		subgroupAndScalar := a.Have(
			"the submodule is an additive subgroup and the index is an integer scalar",
			"subgroup(module_additive_group(M), N) ∧ "+
				"N ⊆ M.carrier ∧ "+
				"int_of_num(card(left_cosets(M.add, M.carrier, N))) ∈ ring_carrier(int_ring)",
			BySets(
				assumptions,
				submodule.SubmoduleSubgroup.At(R, M, N),
				submodule.SubmoduleSubset.At(R, M, N),
				int_real_lift.IntegerRingCarrierUniversal.At(
					a.TermAs[Int]("card(left_cosets(M.add, M.carrier, N))"))))
		pointwise := a.Have(
			"each index multiple lies in the submodule",
			"∀x:B. x ∈ M.carrier ⇒ M.smul(int_of_num(card(left_cosets(M.add, M.carrier, N))), x) ∈ N",
			Derive(func(b *Argument) {
				x := b.FixAs[B]("x")
				inModule := b.Assume()
				coset := b.TermAs[Set[B]]("left_coset(M.add, x, N)")
				index := b.TermAs[Int]("card(left_cosets(M.add, M.carrier, N))")
				additive := module.AddGroupOn.Read(moduleFact)
				classInQuotient := b.Have(
					"the vector represents a quotient class",
					"left_coset(M.add, x, N) ∈ left_cosets(M.add, M.carrier, N)",
					By(inModule, subgroupAndScalar, quotient_group.LeftCosetInLeftCosets.Read(additive)))
				zeroClass := b.Have(
					"the coset of the index multiple is the zero class",
					"left_coset(M.add, M.smul(int_of_num(card(left_cosets(M.add, M.carrier, N))), x), N) = N",
					By(
						quotientKilled.At(coset),
						inModule,
						classInQuotient,
						subgroupAndScalar,
						assumptions,
						At(submodule.QuotientSmulCoset.Read(moduleFact), N, index, x)))
				b.Show(
					"the index multiple belongs to its zero coset",
					By(
						zeroClass,
						inModule,
						subgroupAndScalar,
						At(module.SmulIn.Read(moduleFact), index, x),
						At(group.InOwnLeftCosetOn.Read(additive),
							b.TermAs[B]("M.smul(int_of_num(card(left_cosets(M.add, M.carrier, N))), x)"), N)))
			}))
		a.Show(
			"the image of index multiplication lies in the submodule",
			By(
				pointwise,
				set_image.ImageSubsetIff.At(
					a.TermAs[Fun[B, B]]("M.smul(int_of_num(card(left_cosets(M.add, M.carrier, N))))"),
					a.TermAs[Set[B]]("M.carrier"), N)))
	}),
})}

// FiniteIndexPositive — a submodule of an integer module with finitely
// many cosets has positive index: the coset of zero lies in the quotient,
// so the finite quotient is not empty.
var FiniteIndexPositive = finiteIndexPositiveThm{family.Add(registry.ProofEntry{
	Name: "FiniteIndexPositive",
	Key:  "prop_7bfa1b4c169f5e81",
	Build: family.Theorem(Statement{
		Binders: "∀M:module_ops(int, B). ∀N:set(B).",
		Hypotheses: []string{
			"module_on(int_ring, M)",
			"submodule(int_ring, M, N)",
			"finite(left_cosets(M.add, M.carrier, N))",
		},
		Conclusion: "0 < card(left_cosets(M.add, M.carrier, N))",
	}, func(
		a *Argument,
		M *Expr[ModuleOps[Int, B]],
		moduleFact Fact,
		N *Expr[Set[B]],
		conditions Fact,
	) {
		additive := module.AddGroupOn.Read(moduleFact)
		quotient := a.TermAs[Set[Set[B]]]("left_cosets(M.add, M.carrier, N)")
		zeroClass := a.Have(
			"the zero coset belongs to the quotient",
			"left_coset(M.add, M.zero, N) ∈ left_cosets(M.add, M.carrier, N)",
			BySets(
				conditions,
				submodule.SubmoduleSubset.At(a.TermAs[RingOps[Int]]("int_ring"), M, N),
				group.OneIn.Read(additive),
				quotient_group.LeftCosetInLeftCosets.Read(additive)))
		nonzero := a.Have(
			"a nonempty finite quotient has nonzero cardinality",
			"card(left_cosets(M.add, M.carrier, N)) ≠ 0",
			BySets(zeroClass, conditions, cardinality.CardEqZero.At(quotient)))
		a.Show(
			"its natural-number cardinality is positive",
			ByArith(nonzero))
	}),
})}

// IntegerBasisSizeUnique — two finite bases of an integer module have the
// same size. Expanding each vector of E in F and reading back its own E
// coordinate makes every row of the coordinate pairing sum to one, and
// expanding each vector of F in E does the same for every column; summing
// the pairing both ways counts E and counts F, so the two sizes have one
// integer image, and distinct naturals have distinct integer images.
var IntegerBasisSizeUnique = integerBasisSizeUniqueThm{family.Add(registry.ProofEntry{
	Name: "IntegerBasisSizeUnique",
	Key:  "prop_fd4a5d9c79995b30",
	Build: family.Sections(Statement{
		Binders: "∀M:module_ops(int, B). ∀E F:set(B).",
		Hypotheses: []string{
			"module_on(int_ring, M)",
			"finite(E)",
			"module_basis(int_ring, M, E)",
			"finite(F)",
			"module_basis(int_ring, M, F)",
		},
		Conclusion: "card(E) = card(F)",
		Abbrev: Abbrev{
			{Name: "pairing", Text: "λe:B. λf:B. " +
				"    module_basis_coordinates(int_ring, M, F, e, f) * " +
				"    module_basis_coordinates(int_ring, M, E, f, e)"},
			{Name: "rows", Text: "λe:B. module_sum(int_add, 0, F, λf:B. «pairing»(e, f))"},
			{Name: "columns", Text: "λf:B. module_sum(int_add, 0, E, λe:B. «pairing»(e, f))"},
			{Name: "transpose", Text: "λf:B. " +
				"    module_sum(int_add, " +
				"        0, " +
				"        E, " +
				"        λe:B. " +
				"            module_basis_coordinates(int_ring, M, E, f, e) * " +
				"            module_basis_coordinates(int_ring, M, F, e, f))"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		integerOps := ctx.Lemma("ring_add(int_ring) = int_add ∧ "+
			"ring_zero(int_ring) = 0 ∧ "+
			"ring_one(int_ring) = 1 ∧ "+
			"ring_mul(int_ring) = int_mul ∧ "+
			"ring_carrier(int_ring) = 𝕌", func(a *Argument) {
			a.Show(
				"the integer ring has its native operations and universal carrier",
				Simp(
					Fwd(int_real_lift.IntRingDef),
					Fwd(module_record.RingAddDef),
					Fwd(module_record.RingZeroDef),
					Fwd(module_record.RingOneDef),
					Fwd(module_record.RingMulDef),
					Fwd(module_record.RingCarrierDef)),
				Basic())
		})
		integerModuleCarrier := ctx.Lemma("∀x:int. "+
			"    x ∈ mod_carrier(regular_module(int_ring))", func(a *Argument) {
			a.Show(
				"the regular module contains every integer",
				Simp(Fwd(module_record.RegularModuleDef), Fwd(module_record.ModCarrierDef), Fwd(integerOps)),
				BySets())
		})

		constantSum := ctx.Lemma(Statement{
			Binders: "∀s:set(B).", Hypotheses: []string{"finite(s)"},
			Conclusion: "module_sum(ring_add(int_ring), ring_zero(int_ring), s, λx:B. ring_one(int_ring)) = " +
				"int_of_num(card(s))",
		}, func(a *Argument, s *Expr[Set[B]], finiteS Fact) {
			one := a.TermAs[Int]("ring_one(int_ring)")
			a.Show(
				"in the regular module a sum of ones is the count times one",
				By(
					Normalized,
					finiteS,
					characteristic_zero.IntegerRingRegularModule,
					At(integerModuleCarrier, one),
					integerOps,
					int_real_lift.MulRightIdentity,
					ConstantSumCardinalityMultiple.At(
						a.TermAs[ModuleOps[Int, Int]]("regular_module(int_ring)"), one, s)))
		})

		coordinateExpansion := ctx.Lemma(Statement{
			Binders: "∀M:module_ops(int, B). ∀E F:set(B). ∀u d:B.",
			Hypotheses: []string{
				"module_on(int_ring, M)",
				"finite(E)",
				"module_basis(int_ring, M, E)",
				"finite(F)",
				"module_basis(int_ring, M, F)",
				"u ∈ M.carrier",
				"d ∈ E",
			},
			Conclusion: "module_basis_coordinates(int_ring, M, E, u, d) = " +
				"module_sum(ring_add(int_ring), " +
				"    ring_zero(int_ring), " +
				"    F, " +
				"    λf:B. " +
				"        module_basis_coordinates(int_ring, M, F, u, f) * " +
				"        module_basis_coordinates(int_ring, M, E, f, d))",
		}, func(
			a *Argument,
			M *Expr[ModuleOps[Int, B]],
			E, F *Expr[Set[B]],
			u, d *Expr[B],
			assumptions Fact,
		) {
			R := a.TermAs[RingOps[Int]]("int_ring")
			functional := a.TermAs[Fun[B, Int]]("λv:B. module_basis_coordinates(int_ring, M, E, v, d)")
			coordinate := a.Have(
				"the chosen coordinate is an integer-linear functional",
				"module_homomorphism(int_ring, "+
					"    M, "+
					"    regular_module(int_ring), "+
					"    λv:B. module_basis_coordinates(int_ring, M, E, v, d))",
				By(assumptions, module_dimension.BasisCoordinateLinear.At(R, M, E, d)))
			a.Show(
				"apply the coordinate functional to the expansion of u in F",
				By(
					assumptions,
					coordinate,
					module_dimension.HomBasisExpansion.At(
						R, M, a.TermAs[ModuleOps[Int, Int]]("regular_module(int_ring)"), F, functional, u)))
		})

		return ctx.Theorem(headline, func(
			a *Argument,
			M *Expr[ModuleOps[Int, B]],
			E, F *Expr[Set[B]],
			assumptions Fact,
		) {
			R := a.TermAs[RingOps[Int]]("int_ring")
			carriers := a.Have(
				"both bases lie in the module",
				"E ⊆ M.carrier ∧ F ⊆ M.carrier",
				By(
					assumptions,
					linear_independence.ModuleBasisDef.At(R, M, E),
					linear_independence.ModuleBasisDef.At(R, M, F),
					linear_independence.IndependentInCarrier.At(R, M, E),
					linear_independence.IndependentInCarrier.At(R, M, F)))
			rows := a.Have(
				"each row sum recovers one diagonal coordinate",
				"∀e:B. e ∈ E ⇒ «rows»(e) = 1",
				Derive(func(b *Argument) {
					e := b.FixAs[B]("e")
					inE := b.Assume()
					b.Show(
						"expand e in F and read its own E coordinate",
						BySets(
							inE,
							carriers,
							assumptions,
							At(coordinateExpansion, M, E, F, e, e),
							module_dimension.BasisCoordinateDelta.At(R, M, E, e)))
				}))
			columns := a.Have(
				"each transposed column sum also recovers one",
				"∀f:B. f ∈ F ⇒ «transpose»(f) = 1",
				Derive(func(b *Argument) {
					f := b.FixAs[B]("f")
					inF := b.Assume()
					b.Show(
						"expand f in E and read its own F coordinate",
						BySets(
							inF,
							carriers,
							assumptions,
							At(coordinateExpansion, M, F, E, f, f),
							module_dimension.BasisCoordinateDelta.At(R, M, F, f)))
				}))
			add := a.TermAs[Fun2[Int, Int, Int]]("int_add")
			zero := a.TermAs[Int]("0")
			ones := a.TermAs[Fun[B, Int]]("λx:B. 1")
			rowFunction := a.TermAs[Fun[B, Int]]("«rows»")
			columnFunction := a.TermAs[Fun[B, Int]]("«columns»")
			transposed := a.TermAs[Fun[B, Int]]("«transpose»")
			totalE := a.Have(
				"summing the rows counts E",
				"module_sum(int_add, 0, E, «rows») = int_of_num(card(E))",
				CalcEq(Leg(
					a.TermAs[Int]("module_sum(int_add, &0, E, λe:B. 1)"),
					"replace each row by one",
					By(rows, module.ModuleSumCongruence.At(add, zero, E, rowFunction, ones))),
					FinalLeg(
						"a constant-one sum is the cardinality",
						By(assumptions, At(constantSum, E), integerOps))))
			totalF := a.Have(
				"summing the transposed columns counts F",
				"module_sum(int_add, 0, F, «transpose») = int_of_num(card(F))",
				CalcEq(Leg(
					a.TermAs[Int]("module_sum(int_add, &0, F, λf:B. 1)"),
					"replace each column by one",
					By(columns, module.ModuleSumCongruence.At(add, zero, F, transposed, ones))),
					FinalLeg(
						"a constant-one sum is the cardinality",
						By(assumptions, At(constantSum, F), integerOps))))
			swap := a.Have(
				"interchange the finite sums",
				"module_sum(int_add, 0, E, «rows») = module_sum(int_add, 0, F, «columns»)",
				By(
					assumptions,
					integerModuleCarrier,
					At(
						module.ModuleSumSwap.Read(characteristic_zero.IntegerRingRegularModule),
						E,
						F,
						a.TermAs[Fun2[B, B, Int]]("«pairing»"))))
			commuted := a.Have(
				"commuting each scalar product aligns the columns",
				"∀f:B. «columns»(f) = «transpose»(f)",
				Derive(func(b *Argument) {
					b.FixAs[B]("f")
					b.Show(
						"the two products agree term by term",
						By(
							module.ModuleSumCongruence.At(add, zero, E,
								b.TermAs[Fun[B, Int]]("λe:B. «pairing»(e, f)"),
								b.TermAs[Fun[B, Int]](
									"λe:B. "+
										"    module_basis_coordinates(int_ring, M, E, f, e) * "+
										"    module_basis_coordinates(int_ring, M, F, e, f)")),
							int_real_lift.MulSym))
				}))
			coerced := a.Have(
				"the two cardinalities have equal integer images",
				"int_of_num(card(E)) = int_of_num(card(F))",
				CalcEq(Leg(
					a.TermAs[Int]("module_sum(int_add, &0, E, «rows»)"),
					"the row total counts E",
					By(totalE)),
					Leg(
						a.TermAs[Int]("module_sum(int_add, &0, F, «columns»)"),
						"interchange the summations",
						By(swap)),
					Leg(
						a.TermAs[Int]("module_sum(int_add, &0, F, «transpose»)"),
						"commute the scalar factors",
						By(commuted, module.ModuleSumCongruence.At(add, zero, F, columnFunction, transposed))),
					FinalLeg(
						"the column total counts F",
						By(totalF))))
			a.Show(
				"integer coercion preserves cardinality equality",
				By(coerced, int_embed.OfNumEq.At(a.TermAs[Nat]("card(E)"), a.TermAs[Nat]("card(F)"))))
		})
	}),
})}

// IndexedBasisIsomorphism — an indexed basis e of n vectors identifies an
// integer module M with the integer vectors supported below n: u ↦ Σ_{i<n}
// u(i) e(i) is linear, as the free lift is, one-to-one, the basis being
// independent, and onto, every vector being the sum of its coordinates.
var IndexedBasisIsomorphism = indexedBasisIsomorphismThm{family.Add(registry.ProofEntry{
	Name: "IndexedBasisIsomorphism",
	Key:  "prop_2c4039ba07ff181d",
	Build: family.Sections(Statement{
		Binders:    "∀M:module_ops(int, B). ∀n:num. ∀e:(num → B).",
		Hypotheses: []string{"module_on(int_ring, M)", "indexed_module_basis(int_ring, M, n, e)"},
		Conclusion: "module_isomorphism(int_ring, «V», M, «H»)",
		Abbrev: Abbrev{
			{Name: "I", Text: "{i:num | i < n}"}, {Name: "basis", Text: "image(e, «I»)"},
			{Name: "V", Text: "free_module_record(int_ring, «I»)"},
			{Name: "H", Text: "λu:(num → int). module_sum(M.add, M.zero, «I», λi:num. M.smul(u(i), e(i)))"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		integerOps := ctx.Lemma("ring_add(int_ring) = int_add ∧ "+
			"ring_zero(int_ring) = 0 ∧ "+
			"ring_one(int_ring) = 1 ∧ "+
			"ring_mul(int_ring) = int_mul ∧ "+
			"ring_carrier(int_ring) = 𝕌", func(a *Argument) {
			a.Show(
				"the integer ring has its native operations and universal carrier",
				Simp(
					Fwd(int_real_lift.IntRingDef),
					Fwd(module_record.RingAddDef),
					Fwd(module_record.RingZeroDef),
					Fwd(module_record.RingOneDef),
					Fwd(module_record.RingMulDef),
					Fwd(module_record.RingCarrierDef)),
				Basic())
		})
		coordinateSupport := ctx.Lemma("∀n:num. ∀v:(num → int). "+
			"    v ∈ «V».carrier ⇔ "+
			"    finite(fun_support(int_of_num(0), v)) ∧ "+
			"    fun_support(int_of_num(0), v) ⊆ «I»", func(a *Argument) {
			a.Show(
				"the coordinate carrier consists of finitely supported vectors below n",
				Simp(Fwd(free_module.FreeModuleRecordDef), Fwd(function_module.FiniteSuppMember)),
				By(set_basic.InUniv))
		})
		reindexSum := ctx.Lemma(Statement{
			Binders:    "∀M:module_ops(int, B). ∀n:num. ∀e:(num → B). ∀a:(num → int).",
			Hypotheses: []string{"module_on(int_ring, M)", "indexed_module_basis(int_ring, M, n, e)"},
			Conclusion: "module_sum(M.add, M.zero, «I», λi:num. M.smul(a(i), e(i))) = " +
				"module_sum(M.add, M.zero, «basis», λx:B. M.smul(a(inverse_on(«I», e, x)), x))",
		}, func(
			arg *Argument,
			M *Expr[ModuleOps[Int, B]],
			n *Expr[Nat],
			e *Arrow[Nat, B],
			a *Arrow[Nat, Int],
			assumptions Fact,
		) {
			R := arg.TermAs[RingOps[Int]]("int_ring")
			I := arg.TermAs[Set[Nat]]("«I»")
			parts := arg.Conjuncts(
				assumptions,
				"the module laws",
				"the indexed basis")
			data := arg.Have(
				"the index set is finite and the indexing injective",
				"finite(«I») ∧ injective_on(«I», e)",
				By(
					parts[1],
					num_segment.FiniteBelowStrict.At(n),
					linear_independence.IndexedBasisImage.At(R, M, n, e)))
			indices := arg.Have(
				"the inverse enumeration recovers each index",
				"∀i:num. i < n ⇒ inverse_on(«I», e, e(i)) = i ∧ e(i) ∈ M.carrier",
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]("i")
					inRange := b.Assume()
					b.Show(
						"injectivity recovers i and the indexed basis vector e(i) lies in M",
						BySets(
							inRange,
							data,
							parts[1],
							functions.InverseOnLeft.At(I, e, i),
							linear_independence.IndexedBasisInCarrier.At(R, M, n, e, i)))
				}))
			members := arg.Have(
				"the reindexed summands belong to the module",
				"∀i:num. i < n ⇒ M.smul(a(inverse_on(«I», e, e(i))), e(i)) ∈ M.carrier",
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]("i")
					inRange := b.Assume()
					b.Show(
						"integer scalar multiples of basis vectors stay in the carrier",
						By(
							inRange,
							indices,
							int_real_lift.IntegerRingCarrierUniversal,
							At(module.SmulIn.Read(parts[0]), b.TermAs[Int]("a(inverse_on(«I», e, e(i)))"), e.Apply(i))))
				}))
			middle := arg.TermAs[B](
				"module_sum(M.add, M.zero, «I», λi:num. M.smul(a(inverse_on(«I», e, e(i))), e(i)))")
			arg.Show(
				"reindex the finite sum along the basis enumeration",
				CalcEq(Leg(
					middle,
					"replace each recovered inverse index by its index",
					BySets(
						indices,
						module.ModuleSumCongruence.At(
							arg.TermAs[Fun2[B, B, B]]("M.add"),
							arg.TermAs[B]("M.zero"),
							I,
							arg.TermAs[Fun[Nat, B]]("λi:num. M.smul(a(i), e(i))"),
							arg.TermAs[Fun[Nat, B]]("λi:num. M.smul(a(inverse_on(«I», e, e(i))), e(i))")))),
					FinalLeg(
						"the injective image-sum formula reindexes the sum",
						BySets(
							members,
							data,
							At(
								module.ModuleSumImage.Read(parts[0]),
								I,
								e,
								arg.TermAs[Fun[B, B]]("λx:B. M.smul(a(inverse_on(«I», e, x)), x)"))))))
		})

		liftAgreement := ctx.Lemma(Statement{
			Binders: "∀M:module_ops(int, B). ∀n:num. ∀e:(num → B). ∀u:(num → int).",
			Hypotheses: []string{
				"module_on(int_ring, M)",
				"indexed_module_basis(int_ring, M, n, e)",
				"u ∈ «V».carrier",
			},
			Conclusion: "module_sum(M.add, M.zero, «I», λi:num. M.smul(u(i), e(i))) = " +
				"free_lift(int_of_num(0), M.add, M.zero, M.smul, e, u)",
		}, func(
			a *Argument,
			M *Expr[ModuleOps[Int, B]],
			n *Expr[Nat],
			e *Arrow[Nat, B],
			u *Arrow[Nat, Int],
			assumptions Fact,
		) {
			parts := a.Conjuncts(
				assumptions,
				"the module laws",
				"the indexed basis",
				"the coefficient vector is supported below n")
			R := a.TermAs[RingOps[Int]]("int_ring")
			members := a.Have(
				"each coordinate summand lies in the carrier",
				"∀i:num. i < n ⇒ e(i) ∈ M.carrier ∧ M.smul(u(i), e(i)) ∈ M.carrier",
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]("i")
					inRange := b.Assume()
					b.Show(
						"the indexed basis vector and scalar closure give the summand",
						BySets(
							inRange,
							parts[1],
							linear_independence.IndexedBasisInCarrier.At(R, M, n, e, i),
							At(module.SmulIn.Read(parts[0]), u.Apply(i), e.Apply(i))))
				}))
			supported := a.Simplified(parts[2], Fwd(coordinateSupport))
			zeroTail := a.Have(
				"summands outside the support vanish",
				"∀i:num. i ∈ «I» ∧ i ∉ fun_support(int_of_num(0), u) ⇒ M.smul(u(i), e(i)) = M.zero",
				BySets(members, module.ZeroSmul.Read(parts[0])))
			a.Show(
				"zero coefficients outside the support do not change the sum",
				Simp(Fwd(free_module.FreeLiftDef)),
				BySets(
					members,
					supported,
					num_segment.FiniteBelowStrict.At(n),
					zeroTail,
					At(
						module.ModuleSumSupport.Read(parts[0]),
						a.TermAs[Set[Nat]]("«I»"),
						a.TermAs[Set[Nat]]("fun_support(int_of_num(0), u)"),
						a.TermAs[Fun[Nat, B]]("λi:num. M.smul(u(i), e(i))"))))
		})

		return ctx.Theorem(headline, func(
			a *Argument,
			M *Expr[ModuleOps[Int, B]],
			n *Expr[Nat],
			e *Arrow[Nat, B],
			assumptions Fact,
		) {
			parts := a.Conjuncts(
				assumptions,
				"the module laws",
				"the indexed basis")
			R := a.TermAs[RingOps[Int]]("int_ring")
			I := a.TermAs[Set[Nat]]("«I»")
			basis := a.TermAs[Set[B]]("«basis»")
			V := a.TermAs[ModuleOps[Int, Fun[Nat, Int]]]("«V»")
			H := a.TermAs[Fun[Fun[Nat, Int], B]]("«H»")
			image := a.Have(
				"the image has its indexed set description",
				"«basis» = {e(i):B | i:num | i < n}",
				BySets())
			data := a.Have(
				"the indexed basis is a finite injective image basis",
				"finite(«I») ∧ "+
					"injective_on(«I», e) ∧ "+
					"finite(«basis») ∧ "+
					"module_basis(int_ring, M, «basis») ∧ "+
					"«basis» ⊆ M.carrier",
				image.Rw(),
				By(
					parts[1],
					num_segment.FiniteBelowStrict.At(n),
					linear_independence.IndexedBasisImage.At(R, M, n, e),
					linear_independence.BasisInCarrier.At(R, M, a.TermAs[Set[B]]("{e(i):B | i:num | i < n}"))))
			hom := a.Have(
				"the coordinate sum is an integer-module homomorphism",
				"module_homomorphism(int_ring, «V», M, «H»)",
				Derive(func(b *Argument) {
					basisMembers := b.Have(
						"each indexed basis vector lies in M",
						"∀i:num. i < n ⇒ e(i) ∈ M.carrier",
						BySets(data))
					lift := b.Have(
						"the free lift is linear",
						"module_homomorphism(int_ring, «V», M, free_lift(int_of_num(0), M.add, M.zero, M.smul, e))",
						By(parts[0], basisMembers, free_module.FreeLiftHom.At(R, M, I, e), integerOps))
					b.Show(
						"agreement with the free lift gives linearity of the coordinate sum",
						By(
							assumptions,
							lift,
							At(liftAgreement, M, n, e),
							module_homomorphism.HomCongruence.At(
								R, V, M, b.TermAs[Fun[Fun[Nat, Int], B]]("free_lift(int_of_num(0), M.add, M.zero, M.smul, e)"), H)))
				}))
			oneToOne := a.Have(
				"basis independence makes the coordinate sum injective",
				"injective_on(«V».carrier, «H»)",
				Simp(Fwd(functions.InjectiveOnDef)),
				Derive(func(b *Argument) {
					x := b.FixAs[Fun[Nat, Int]]("x")
					y := b.FixAs[Fun[Nat, Int]]("y")
					sameImage := b.Assume()
					images := b.Conjuncts(
						sameImage,
						"x is supported below n",
						"y is supported below n",
						"the two coordinate sums agree")
					equalCombinations := b.Have(
						"reindex the two equal combinations over the basis set",
						"module_sum(M.add, M.zero, «basis», λv:B. M.smul(x(inverse_on(«I», e, v)), v)) = "+
							"module_sum(M.add, M.zero, «basis», λv:B. M.smul(y(inverse_on(«I», e, v)), v))",
						By(images[2], assumptions, At(reindexSum, M, n, e, x), At(reindexSum, M, n, e, y)))
					coefficients := b.Have(
						"independence equates the reindexed coefficients",
						"∀v:B. v ∈ «basis» ⇒ x(inverse_on(«I», e, v)) = y(inverse_on(«I», e, v))",
						BySets(
							equalCombinations,
							parts[0],
							data,
							linear_independence.ModuleBasisDef.At(R, M, basis),
							At(
								linear_independence.IndependentUniqueCoefficients,
								R,
								M,
								basis,
								basis,
								b.TermAs[Fun[B, Int]]("λv:B. x(inverse_on(«I», e, v))"),
								b.TermAs[Fun[B, Int]]("λv:B. y(inverse_on(«I», e, v))"))))
					bounded := b.Have(
						"the coefficients agree at every index below n",
						"∀i:num. i < n ⇒ x(i) = y(i)",
						Derive(func(c *Argument) {
							i := c.FixAs[Nat]("i")
							inRange := c.Assume()
							c.Show(
								"recover the index from its basis vector",
								BySets(coefficients, inRange, data, functions.InverseOnLeft.At(I, e, i)))
						}))
					xSupport := b.Simplified(images[0], Fwd(function_module.FiniteSuppMember))
					ySupport := b.Simplified(images[1], Fwd(function_module.FiniteSuppMember))
					b.Show(
						"equal bounded coordinates and zero tails give equal vectors",
						Funext(),
						Derive(func(c *Argument) {
							c.FixAs[Nat]("j")
							c.Show(
								"the coordinates agree inside and outside the support bound",
								BySets(bounded, xSupport, ySupport))
						}))
				}))
			onto := a.Have(
				"the coordinate sum reaches the whole carrier",
				"image(«H», «V».carrier) = M.carrier",
				Derive(func(b *Argument) {
					outputs := b.Have(
						"every finite coordinate sum lies in M",
						"∀u:(num → int). «H»(u) ∈ M.carrier",
						Derive(func(c *Argument) {
							c.FixAs[Fun[Nat, Int]]("u")
							c.Show(
								"a finite sum of integer multiples of basis vectors lies in M",
								BySets(
									data,
									At(module.ModuleSumIn.Read(parts[0]), I, c.TermAs[Fun[Nat, B]]("λi:num. M.smul(u(i), e(i))")),
									module.SmulIn.Read(parts[0])))
						}))
					preimages := b.Have(
						"the basis coordinates supply a supported preimage",
						"∀v:B. v ∈ M.carrier ⇒ ∃u:(num → int). u ∈ finite_supp(int_of_num(0), 𝕌, «I») ∧ «H»(u) = v",
						Derive(func(c *Argument) {
							v := c.FixAs[B]("v")
							inModule := c.Assume()
							coefficients, definition := c.LetAs[Fun[Nat, Int]](
								"coefficients",
								"λi:num. COND(i < n, module_basis_coordinates(int_ring, M, «basis», v, e(i)), int_of_num(0))")
							c.Take(coefficients)
							c.Show(
								"the chosen coefficients form a supported preimage of v",
								SplitConj(
									Case(
										"the coefficient vector is supported on a finite initial segment",
										Derive(func(d *Argument) {
											subset := d.Have(
												"nonzero coefficients occur only below n",
												"fun_support(int_of_num(0), coefficients) ⊆ «I»",
												BySets(definition))
											d.Show(
												"finite support follows from the finite initial segment",
												Simp(Fwd(function_module.FiniteSuppMember)),
												BySets(
													subset,
													data,
													finite_set.FiniteSubset.At(d.TermAs[Set[Nat]]("fun_support(int_of_num(0), coefficients)"), I)))
										})),
									Case(
										"the finite coordinate sum reconstructs v",
										CalcEq(Leg(
											c.TermAs[B](
												"module_sum(M.add, "+
													"    M.zero, "+
													"    «I», "+
													"    λi:num. M.smul(module_basis_coordinates(int_ring, M, «basis», v, e(i)), e(i)))"),
											"below n the chosen coefficients are the basis coordinates",
											BySets(
												definition,
												module.ModuleSumCongruence.At(
													c.TermAs[Fun2[B, B, B]]("M.add"),
													c.TermAs[B]("M.zero"),
													I,
													c.TermAs[Fun[Nat, B]]("λi:num. M.smul(coefficients(i), e(i))"),
													c.TermAs[Fun[Nat, B]](
														"λi:num. M.smul(module_basis_coordinates(int_ring, M, «basis», v, e(i)), e(i))")))),
											FinalLeg(
												"the indexed basis expansion is v",
												By(assumptions, inModule, module_dimension.IndexedBasisExpansion.At(R, M, n, e, v)))))))
						}))
					b.Show(
						"supported preimages and carrier closure give surjectivity",
						BySets(preimages, outputs))
				}))
			a.Show(
				"the coordinate sum is a module isomorphism",
				Simp(Fwd(module_homomorphism.ModuleIsomorphismDef)),
				By(hom, oneToOne, onto))
		})
	}),
})}

// NonzeroScalarInjective — multiplication by a nonzero integer is one-to-one
// on an integer module with a finite basis: c·x = c·y gives c times each
// coordinate of x equal to c times that of y, the integers cancel c, and a
// vector is the sum of its coordinates.
var NonzeroScalarInjective = nonzeroScalarInjectiveThm{family.Add(registry.ProofEntry{
	Name: "NonzeroScalarInjective",
	Key:  "prop_2db171bb958ca4b8",
	Build: family.Theorem(Statement{
		Binders: "∀M:module_ops(int, B). ∀E:set(B). ∀c:int.",
		Hypotheses: []string{
			"module_on(int_ring, M)",
			"finite(E)",
			"module_basis(int_ring, M, E)",
			"c ≠ 0",
		},
		Conclusion: "injective_on(M.carrier, M.smul(c))",
	}, Opening(Simp(Fwd(functions.InjectiveOnDef)), func(
		a *Argument,
		M *Expr[ModuleOps[Int, B]],
		E *Expr[Set[B]],
		c *Expr[Int],
		assumptions Fact,
		x, y *Expr[B],
		sameMultiple Fact,
	) {
		R := a.TermAs[RingOps[Int]]("int_ring")
		coordinates := a.Have(
			"cancellation equates every basis coordinate",
			Statement{
				Binders: "∀e:B.",
				Hypotheses: []string{
					"e ∈ E",
				},
				Conclusion: "module_basis_coordinates(int_ring, M, E, x, e) = " +
					"module_basis_coordinates(int_ring, M, E, y, e)",
			},
			Derive(func(b *Argument) {
				b.FixAs[B]("e")
				b.Assume()
				b.Show(
					"cancel the nonzero integer in the two scaled coordinates",
					By(
						sameMultiple,
						assumptions,
						int_real_lift.IntegerRingCarrierUniversal,
						module_dimension.BasisCoordinatesSmul.At(R, M, E, c, x),
						module_dimension.BasisCoordinatesSmul.At(R, M, E, c, y),
						int_real_lift.MulLeftCancel.At(
							c,
							b.TermAs[Int]("module_basis_coordinates(int_ring, M, E, x, e)"),
							b.TermAs[Int]("module_basis_coordinates(int_ring, M, E, y, e)"))))
			}))
		a.Show(
			"the basis expansions recover equality of the vectors",
			By(
				coordinates,
				sameMultiple,
				assumptions,
				module_dimension.BasisCoordinatesSpec.At(R, M, E, x),
				module_dimension.BasisCoordinatesSpec.At(R, M, E, y),
				module.ModuleSumCongruence.At(a.TermAs[Fun2[B, B, B]]("M.add"), a.TermAs[B]("M.zero"), E,
					a.TermAs[Fun[B, B]]("λe:B. M.smul(module_basis_coordinates(int_ring, M, E, x, e), e)"),
					a.TermAs[Fun[B, B]]("λe:B. M.smul(module_basis_coordinates(int_ring, M, E, y, e), e)"))))
	})),
})}

// FullRankIffFiniteIndex — a submodule of a finite free integer module has
// finite index exactly when it has full rank. The index multiple gives the
// forward rank bound; a full triangular coordinate basis gives the converse.
var FullRankIffFiniteIndex = fullRankIffFiniteIndexThm{family.Add(registry.ProofEntry{
	Name: "FullRankIffFiniteIndex",
	Key:  "prop_a065f604ab1d73ea",
	Build: family.Sections(Statement{
		Binders: "∀M:module_ops(int, B). ∀E N:set(B).",
		Hypotheses: []string{
			"module_on(int_ring, M)",
			"finite(E)",
			"module_basis(int_ring, M, E)",
			"submodule(int_ring, M, N)",
		},
		Conclusion: "finite(left_cosets(M.add, M.carrier, N)) ⇔ " +
			"∃F:set(B). finite(F) ∧ module_basis(int_ring, restrict_module(M, N), F) ∧ card(F) = card(E)",
	}, func(ctx *Script, headline string) *GoalStackNode {
		scalarHom := ctx.Lemma(Statement{
			Binders: "∀M:module_ops(int, B). ∀c:int.", Hypotheses: []string{"module_on(int_ring, M)"},
			Conclusion: "module_homomorphism(int_ring, M, M, M.smul(c))",
		}, func(a *Argument, M *Expr[ModuleOps[Int, B]], c *Expr[Int], moduleFact Fact) {
			commute := a.Have(
				"integer scalar actions commute",
				"∀d:int. ∀u:B. u ∈ M.carrier ⇒ M.smul(c, M.smul(d, u)) = M.smul(d, M.smul(c, u))",
				Derive(func(b *Argument) {
					d := b.FixAs[Int]("d")
					u := b.FixAs[B]("u")
					inModule := b.Assume()
					b.Show(
						"combine the two scalars and commute their integer product",
						By(
							Normalized,
							inModule,
							int_real_lift.IntegerRingCarrierUniversal,
							At(module.SmulMul.Read(moduleFact), c, d, u),
							At(module.SmulMul.Read(moduleFact), d, c, u),
							int_real_lift.MulSym.At(c, d)))
				}))
			a.Show(
				"scalar multiplication preserves addition and the scalar action",
				By(
					commute,
					moduleFact,
					int_real_lift.IntegerRingCarrierUniversal,
					module_homomorphism.ModuleHomomorphismDef.At(
						a.TermAs[RingOps[Int]]("int_ring"), M, M, a.TermAs[Fun[B, B]]("M.smul(c)")),
					At(module.SmulIn.Read(moduleFact), c),
					At(module.SmulAddLeft.Read(moduleFact), c)))
		})
		finiteIndexFullRank := ctx.Lemma(Statement{
			Binders: "∀M:module_ops(int, B). ∀E N:set(B).",
			Hypotheses: []string{
				"module_on(int_ring, M)",
				"finite(E)",
				"module_basis(int_ring, M, E)",
				"submodule(int_ring, M, N)",
				"finite(left_cosets(M.add, M.carrier, N))",
			},
			Conclusion: "∃F:set(B). " +
				"    finite(F) ∧ module_basis(int_ring, restrict_module(M, N), F) ∧ card(F) = card(E)",
		}, func(a *Argument, M *Expr[ModuleOps[Int, B]], E, N *Expr[Set[B]], assumptions Fact) {
			parts := a.Conjuncts(
				assumptions,
				"the module laws",
				"E is finite",
				"E is a basis",
				"N is a submodule",
				"the quotient is finite")
			R := a.TermAs[RingOps[Int]]("int_ring")
			positive := a.Have(
				"the finite quotient has positive index",
				"0 < card(left_cosets(M.add, M.carrier, N))",
				By(parts[0], parts[3], parts[4], FiniteIndexPositive.At(M, N)))
			m, indexDefinition := a.LetAs[Int]("m", "int_of_num(card(left_cosets(M.add, M.carrier, N)))")
			P, imageDefinition := a.LetAs[Set[B]]("P", "image(M.smul(m), M.carrier)")
			indexNonzero := a.Have(
				"the positive index is a nonzero integer",
				"m ≠ 0",
				ByArith(
					indexDefinition,
					positive,
					int_embed.OfNumLt.At(a.TermAs[Nat]("0"), a.TermAs[Nat]("card(left_cosets(M.add, M.carrier, N))"))))
			imageInN := a.Have(
				"the index multiple of M lies in N",
				"P ⊆ N",
				By(Normalized, indexDefinition, imageDefinition, assumptions, IndexAnnihilatesQuotient.At(M, N)))
			scaled := a.Have(
				"the nonzero index multiple is an injective endomorphism",
				"module_homomorphism(int_ring, M, M, M.smul(m)) ∧ injective_on(M.carrier, M.smul(m))",
				By(assumptions, indexNonzero, At(scalarHom, M, m), NonzeroScalarInjective.At(M, E, m)))
			scalarParts := a.Conjuncts(
				scaled,
				"index multiplication is linear",
				"index multiplication is injective")
			imageSubmodule := a.Have(
				"the index multiple is a submodule of M",
				"submodule(int_ring, M, P)",
				By(Normalized, imageDefinition, module_homomorphism.ImageSubmodule.Read(scalarParts[0])))
			imageData := a.Have(
				"the multiplied basis is a finite basis of the index multiple",
				"finite(image(M.smul(m), E)) ∧ "+
					"module_basis(int_ring, restrict_module(M, P), image(M.smul(m), E)) ∧ "+
					"card(image(M.smul(m), E)) = card(E)",
				By(
					Normalized,
					imageDefinition,
					assumptions,
					scaled,
					linear_independence.InjectiveImageBasis.At(R, M, M, a.TermAs[Fun[B, B]]("M.smul(m)"), E)))
			restricted := a.Have(
				"P is a submodule inside N and both restricted modules exist",
				"module_on(int_ring, restrict_module(M, N)) ∧ "+
					"submodule(int_ring, restrict_module(M, N), P) ∧ "+
					"module_on(int_ring, restrict_module(M, P))",
				By(
					parts[3],
					imageSubmodule,
					imageInN,
					At(submodule.SubmoduleModuleOn.Read(parts[0]), N),
					At(submodule.SubmoduleModuleOn.Read(parts[0]), P),
					submodule.SubmoduleRestrict.At(R, M, N, P)))
			F, basisN := a.ObtainAs[Set[B]](
				"choose a finite basis of N with the ambient rank bound",
				"∃F:set(B). finite(F) ∧ module_basis(int_ring, restrict_module(M, N), F) ∧ card(F) ≤ card(E)",
				By(
					assumptions,
					IntegerRingPrincipalIdealDomain,
					principal_ideal_domain.SubmoduleFree.At(R, M, N, E)),
				Named("F"))
			G, basisP := a.ObtainAs[Set[B]](
				"apply the submodule rank bound inside N",
				"∃G:set(B). "+
					"    finite(G) ∧ "+
					"    module_basis(int_ring, restrict_module(restrict_module(M, N), P), G) ∧ "+
					"    card(G) ≤ card(F)",
				By(
					basisN,
					restricted,
					IntegerRingPrincipalIdealDomain,
					principal_ideal_domain.SubmoduleFree.At(
						R, a.TermAs[ModuleOps[Int, B]]("restrict_module(M, N)"), P, F)),
				Named("G"))
			basisP = a.Simplified(basisP, Fwd(module_record.RestrictModuleTwice))
			rankP := a.Have(
				"the index multiple has the ambient basis cardinality",
				"card(G) = card(E)",
				By(
					Normalized,
					basisP,
					imageData,
					restricted,
					IntegerBasisSizeUnique.At(
						a.TermAs[ModuleOps[Int, B]]("restrict_module(M, P)"), a.TermAs[Set[B]]("image(M.smul(m), E)"), G)))
			rankN := a.Have(
				"the two rank bounds force full rank for N",
				"card(F) = card(E)",
				ByArith(rankP, basisP, basisN))
			a.Take(F)
			a.Show(
				"the chosen finite basis of N has full rank",
				By(rankN, basisN))
		})

		fullRankFiniteIndex := ctx.Lemma(Statement{
			Binders: "∀M:module_ops(int, B). ∀E N F:set(B).",
			Hypotheses: []string{
				"module_on(int_ring, M)",
				"finite(E)",
				"module_basis(int_ring, M, E)",
				"submodule(int_ring, M, N)",
				"finite(F)",
				"module_basis(int_ring, restrict_module(M, N), F)",
				"card(F) = card(E)",
			},
			Conclusion: "finite(left_cosets(M.add, M.carrier, N))",
		}, func(a *Argument, M *Expr[ModuleOps[Int, B]], E, N, F *Expr[Set[B]], assumptions Fact) {
			parts := a.Conjuncts(
				assumptions,
				"the module laws",
				"E is finite",
				"E is a basis",
				"N is a submodule",
				"F is finite",
				"F is a basis of N",
				"F has the ambient cardinality")
			R := a.TermAs[RingOps[Int]]("int_ring")
			n, dimensionDefinition := a.LetAs[Nat]("n", "card(E)")
			e, indexed := a.ObtainAs[Fun[Nat, B]](
				"enumerate the ambient finite basis",
				"∃e:(num → B). indexed_module_basis(int_ring, M, n, e)",
				By(
					Normalized,
					dimensionDefinition,
					parts[1],
					parts[2],
					linear_independence.FiniteBasisIndexed.At(R, M, E)),
				Named("e"))
			V, freeDefinition := a.LetAs[ModuleOps[Int, Fun[Nat, Int]]](
				"V", "free_module_record(int_ring, {i:num | i < n})")
			h, sumDefinition := a.LetAs[Fun[Fun[Nat, Int], B]](
				"h", "λu:(num → int). module_sum(M.add, M.zero, {i:num | i < n}, λi:num. M.smul(u(i), e(i)))")
			g, inverseDefinition := a.LetAs[Fun[B, Fun[Nat, Int]]]("g", "inverse_on(V.carrier, h)")
			K, imageDefinition := a.LetAs[Set[Fun[Nat, Int]]]("K", "image(g, N)")
			coordinatesBack := a.Have(
				"the indexed coordinate sum identifies V with M",
				"module_isomorphism(int_ring, V, M, h)",
				By(parts[0], indexed, freeDefinition, sumDefinition, IndexedBasisIsomorphism.At(M, n, e)))
			coordinates := a.Have(
				"the inverse identifies M with its coordinate module",
				"module_isomorphism(int_ring, M, V, g)",
				By(
					Normalized,
					coordinatesBack,
					inverseDefinition,
					module_homomorphism.IsomorphismInverse.At(R, V, M, h)))
			coordinateData := a.Have(
				"the coordinate map is injective and linear and V is a module",
				"module_homomorphism(int_ring, M, V, g) ∧ injective_on(M.carrier, g) ∧ module_on(int_ring, V)",
				By(
					coordinates,
					module_homomorphism.ModuleIsomorphismDef.At(R, M, V, g),
					module_homomorphism.ModuleHomomorphismDef.At(R, M, V, g)))
			coordinateParts := a.Conjuncts(
				coordinateData,
				"the coordinate map is linear",
				"the coordinate map is injective",
				"V is an integer module")
			onSubmodule := a.Have(
				"restriction gives an injective coordinate map from N",
				"module_homomorphism(int_ring, restrict_module(M, N), V, g) ∧ injective_on(N, g)",
				By(
					coordinateParts[0],
					coordinateParts[1],
					submodule.SubmoduleSubset.At(R, M, N),
					parts[3],
					module_homomorphism.HomRestrictSource.At(R, M, V, g, N),
					functions.InjectiveOnSubset.At(g, N, a.TermAs[Set[B]]("M.carrier"))))
			coordinateSubmodule := a.Have(
				"the coordinate image of N is a submodule",
				"submodule(int_ring, V, K)",
				By(
					Normalized,
					coordinateParts[0],
					parts[3],
					imageDefinition,
					module_homomorphism.HomImageSubmodule.At(R, M, V, g, N)))
			imageData := a.Have(
				"the finite full-rank basis transports to K",
				"finite(image(g, F)) ∧ "+
					"module_basis(int_ring, restrict_module(V, K), image(g, F)) ∧ "+
					"card(image(g, F)) = card(F)",
				By(
					Normalized,
					onSubmodule,
					parts[4],
					parts[5],
					imageDefinition,
					linear_independence.InjectiveImageBasis.At(
						R, a.TermAs[ModuleOps[Int, B]]("restrict_module(M, N)"), V, g, F)))
			r, b, p, triangular := a.Obtain3As[Nat, Fun2[Nat, Nat, Int], Fun[Nat, Nat]](
				"choose a triangular coordinate basis",
				"∃r:num. ∃b:(num → num → int). ∃p:(num → num). r ≤ n ∧ integer_triangular_basis(n, K, r, b, p)",
				By(Normalized, freeDefinition, coordinateSubmodule, SubmoduleFreeTriangular.At(n, K)),
				Named("r", "b", "p"))
			unfolded := a.Unfolded(triangular, IntegerTriangularBasisDef)
			coordinateLattice := a.TermAs[ModuleOps[Int, Fun[Nat, Int]]]("restrict_module(V, K)")
			triangleData := a.Have(
				"the triangular vectors form a finite basis of K with r members",
				"finite({b(i):num → int | i:num | i < r}) ∧ "+
					"card({b(i):num → int | i:num | i < r}) = r ∧ "+
					"module_basis(int_ring, restrict_module(V, K), {b(i):num → int | i:num | i < r})",
				By(freeDefinition, unfolded, linear_independence.IndexedBasisImage.At(R, coordinateLattice, r, b)))
			fullRank := a.Have(
				"basis-cardinality invariance forces r to equal n",
				"r = n",
				By(
					coordinateSubmodule,
					At(submodule.SubmoduleModuleOn.Read(coordinateParts[2]), K),
					imageData,
					triangleData,
					parts[6],
					IntegerBasisSizeUnique.At(
						coordinateLattice,
						a.TermAs[Set[Fun[Nat, Int]]]("image(g, F)"),
						a.TermAs[Set[Fun[Nat, Int]]]("{b(i):num → int | i:num | i < r}"))))
			fullTriangle := a.Simplified(triangular, Fwd(fullRank))
			fullUnfolded := a.Unfolded(fullTriangle, IntegerTriangularBasisDef)
			pivots := a.Conjuncts(
				a.Have(
					"the full pivot family strictly increases inside the initial segment",
					"(∀i:num. i < n ⇒ p(i) < n) ∧ (∀i j:num. i < j ∧ j < n ⇒ p(i) < p(j))",
					By(fullUnfolded)),
				"every pivot lies below n",
				"the pivots strictly increase")
			climbs := a.Have(
				"the pivots climb at every step below n",
				"∀j:num. suc(j) < n ⇒ p(j) < p(suc(j))",
				Derive(func(b *Argument) {
					j := b.FixAs[Nat]("j")
					inside := b.Assume()
					b.Show(
						"j lies below its successor",
						ByArith(inside, pivots[1].At(j, b.TermAs[Nat]("suc(j)"))))
				}))
			identity := a.Have(
				"the full increasing pivot sequence is the identity",
				"∀i:num. i < n ⇒ p(i) = i",
				By(At(num_segment.IncreasingSelfMapIsIdentity, n, p), pivots[0], climbs))
			standardTriangle := a.Have(
				"the triangular basis has the standard full pivot sequence",
				"integer_triangular_basis(n, K, n, b, λi:num. i)",
				Simp(Fwd(IntegerTriangularBasisDef)),
				By(fullUnfolded, identity))
			finiteCoordinates := a.Have(
				"a full triangular coordinate basis has finite index",
				"finite(left_cosets(V.add, V.carrier, K))",
				freeDefinition.Rw(),
				By(freeDefinition, coordinateSubmodule, standardTriangle, TriangularIndexProduct.At(n, K, b)))
			a.Show(
				"the coordinate isomorphism transports quotient finiteness back to M",
				By(
					Normalized,
					coordinates,
					parts[3],
					imageDefinition,
					finiteCoordinates,
					module_homomorphism.IsomorphismQuotientFinite.At(R, M, V, g, N)))
		})

		return ctx.Theorem(headline, func(
			a *Argument,
			M *Expr[ModuleOps[Int, B]],
			E, N *Expr[Set[B]],
			assumptions Fact,
		) {
			a.Iff()
			a.Forward(
				"a finite quotient forces full rank",
				func(b *Argument, finiteQuotient Fact) {
					b.Show(
						"the finite-index submodule has a finite basis of ambient cardinality",
						By(assumptions, finiteQuotient, At(finiteIndexFullRank, M, E, N)))
				})
			a.Backward(
				"full rank makes the quotient finite",
				func(b *Argument, fullRank Fact) {
					F, basis := b.UnpackAs[Set[B]](fullRank, "F")
					b.Show(
						"a full-rank finite basis gives a finite quotient",
						By(assumptions, basis, At(fullRankFiniteIndex, M, E, N, F)))
				})
		})
	}),
})}

// BoundedIndexSubmodulesFinite — only finitely many submodules have bounded
// finite index: they contain the factorial multiple and are determined by a
// finite set of coefficient remainders.
var BoundedIndexSubmodulesFinite = boundedIndexSubmodulesFiniteThm{family.Add(registry.ProofEntry{
	Name: "BoundedIndexSubmodulesFinite",
	Key:  "prop_45e8392f4c95ada1",
	Reading: "Finiteness of each quotient is explicit; the " +
		"total function card alone does not assert a finite index.",
	Build: family.Sections(Statement{
		Binders: "∀M:module_ops(int, B). ∀E:set(B). ∀n:num.",
		Hypotheses: []string{
			"module_on(int_ring, M)",
			"finite(E)",
			"module_basis(int_ring, M, E)",
		},
		Conclusion: "finite({N:set(B) | " +
			"        submodule(int_ring, M, N) ∧ " +
			"        finite(left_cosets(M.add, M.carrier, N)) ∧ " +
			"        card(left_cosets(M.add, M.carrier, N)) ≤ n})",
	}, func(ctx *Script, headline string) *GoalStackNode {
		scalarDivision := ctx.Lemma(Statement{
			Binders:    "∀M:module_ops(int, B).",
			Hypotheses: []string{"module_on(int_ring, M)"},
			Conclusion: "∀k c:int. ∀e:B. " +
				"    &0 < k ∧ e ∈ M.carrier ⇒ " +
				"    M.smul(c, e) = M.add(M.smul(rem(c, k), e), M.smul(k, M.smul(div(c, k), e)))",
		}, func(
			a *Argument,
			M *Expr[ModuleOps[Int, B]],
			moduleFact Fact,
			k, c *Expr[Int],
			e *Expr[B],
			conditions Fact,
		) {
			division := a.Have(
				"integer division separates a coefficient into its remainder and multiple",
				"c = rem(c, k) + k * div(c, k)",
				ByArith(conditions, int_div_rem.DivisionAlgorithm.At(c, k)))
			a.Show(
				"scalar addition and multiplication give the vector decomposition",
				BySets(
					division,
					conditions,
					At(
						module.SmulAddRight.Read(moduleFact),
						a.TermAs[Int]("rem(c, k)"),
						a.TermAs[Int]("k * div(c, k)"),
						e),
					At(module.SmulMul.Read(moduleFact), k, a.TermAs[Int]("div(c, k)"), e),
				))
		})

		finiteCoefficients := ctx.Lemma(Statement{
			Binders:    "∀E:set(B). ∀k:int.",
			Hypotheses: []string{"finite(E)", "&0 < k"},
			Conclusion: "finite( " +
				"    {h:B → int | (∀e:B. e ∈ E ⇒ h(e) ∈ {c:int | &0 ≤ c ∧ c < k}) ∧ (∀e:B. e ∉ E ⇒ h(e) = &0)})",
		}, func(a *Argument, E *Expr[Set[B]], k *Expr[Int], conditions Fact) {
			interval := a.TermAs[Set[Int]]("{c:int | &0 ≤ c ∧ c < k}")
			finiteInterval := a.Have(
				"the residue interval lies in a finite closed integer interval",
				"finite({c:int | &0 ≤ c ∧ c < k})",
				BySets(
					int_embed.IntIntervalSize.At(a.TermAs[Int]("0"), k),
					int_real_lift.LessEqOfLessThan,
					finite_set.FiniteSubset.At(interval, a.TermAs[Set[Int]]("{c:int | &0 ≤ c ∧ c ≤ k}"))))
			a.Show(
				"finitely many basis positions and residues give finitely many coefficient functions",
				By(finiteInterval, conditions, cardinality.FiniteFunspace.At(E, interval, a.TermAs[Int]("0"))))
		})

		combinationInModule := ctx.Lemma(Statement{
			Binders:    "∀M:module_ops(int, B).",
			Hypotheses: []string{"module_on(int_ring, M)"},
			Conclusion: "∀E:set(B). ∀a:B → int. " +
				"    finite(E) ∧ E ⊆ M.carrier ⇒ module_sum(M.add, M.zero, E, λe:B. M.smul(a(e), e)) ∈ M.carrier",
		}, func(
			b *Argument,
			M *Expr[ModuleOps[Int, B]],
			moduleFact Fact,
			E *Expr[Set[B]],
			a *Expr[Fun[B, Int]],
			conditions Fact,
		) {
			b.Show(
				"integer scalar closure and finite summation preserve the module carrier",
				BySets(
					conditions,
					module.ModuleSumIn.Read(moduleFact).At(E, b.TermAs[Fun[B, B]]("λe:B. M.smul(a(e), e)")),
					module.SmulIn.Read(moduleFact)))
		})

		divideCombination := ctx.Lemma(Statement{
			Binders:    "∀M:module_ops(int, B).",
			Hypotheses: []string{"module_on(int_ring, M)"},
			Conclusion: "∀E:set(B). ∀a:B → int. ∀k:int. " +
				"    finite(E) ∧ E ⊆ M.carrier ∧ &0 < k ⇒ " +
				"    module_sum(M.add, M.zero, E, λe:B. M.smul(a(e), e)) = " +
				"    M.add(module_sum(M.add, M.zero, E, λe:B. M.smul(rem(a(e), k), e)), " +
				"        M.smul(k, module_sum(M.add, M.zero, E, λe:B. M.smul(div(a(e), k), e))))",
		}, func(
			b *Argument,
			M *Expr[ModuleOps[Int, B]],
			moduleFact Fact,
			E *Expr[Set[B]],
			a *Expr[Fun[B, Int]],
			k *Expr[Int],
			conditions Fact,
		) {
			summands := b.Have(
				"the remainder, quotient, and scaled quotient summands lie in the module",
				Statement{
					Binders: "∀e:B.",
					Hypotheses: []string{
						"e ∈ E",
					},
					Conclusion: "M.smul(rem(a(e), k), e) ∈ M.carrier ∧ " +
						"M.smul(div(a(e), k), e) ∈ M.carrier ∧ " +
						"M.smul(k, M.smul(div(a(e), k), e)) ∈ M.carrier",
				},
				BySets(conditions, module.SmulIn.Read(moduleFact)))
			pointwise := b.Have(
				"divide each coefficient before summing",
				"module_sum(M.add, M.zero, E, λe:B. M.smul(a(e), e)) = "+
					"module_sum(M.add, "+
					"    M.zero, "+
					"    E, "+
					"    λe:B. M.add(M.smul(rem(a(e), k), e), M.smul(k, M.smul(div(a(e), k), e))))",
				BySets(
					moduleFact,
					conditions,
					At(scalarDivision, M, k),
					module.ModuleSumCongruence.At(b.TermAs[Op[B]]("M.add"), b.TermAs[B]("M.zero"), E,
						b.TermAs[Fun[B, B]]("λe:B. M.smul(a(e), e)"),
						b.TermAs[Fun[B, B]]("λe:B. M.add(M.smul(rem(a(e), k), e), M.smul(k, M.smul(div(a(e), k), e)))"))))
			guards := b.Have(
				"both finite-sum identities have their carrier hypotheses",
				"finite(E) ∧ "+
					"k ∈ ring_carrier(int_ring) ∧ "+
					"(∀e:B. e ∈ E ⇒ M.smul(div(a(e), k), e) ∈ M.carrier) ∧ "+
					"(∀e:B. "+
					"    e ∈ E ⇒ M.smul(rem(a(e), k), e) ∈ M.carrier ∧ M.smul(k, M.smul(div(a(e), k), e)) ∈ M.carrier)",
				BySets(summands, conditions, int_real_lift.IntegerRingCarrierUniversal.At(k)))
			b.Show(
				"distribute the sum and pull out the common scalar",
				By(
					pointwise,
					guards,
					module.ModuleSumAdd.Read(moduleFact).At(
						E,
						b.TermAs[Fun[B, B]]("λe:B. M.smul(rem(a(e), k), e)"),
						b.TermAs[Fun[B, B]]("λe:B. M.smul(k, M.smul(div(a(e), k), e))")),
					At(
						module.ModuleSumSmul.Read(moduleFact), E, k, b.TermAs[Fun[B, B]]("λe:B. M.smul(div(a(e), k), e)"))))
		})

		remainderRepresentatives := ctx.Lemma(Statement{
			Binders: "∀M:module_ops(int, B). ∀E:set(B). ∀k:int.",
			Hypotheses: []string{
				"module_on(int_ring, M)",
				"finite(E)",
				"module_basis(int_ring, M, E)",
				"&0 < k",
			},
			Conclusion: "finite(«remainderVectors») ∧ " +
				"«remainderVectors» ⊆ M.carrier ∧ " +
				"(∀v:B. " +
				"    v ∈ M.carrier ⇒ ∃r q:B. r ∈ «remainderVectors» ∧ q ∈ M.carrier ∧ v = M.add(r, M.smul(k, q)))",
			Abbrev: Abbrev{
				{Name: "residueFunctions", Text: "{h:B → int | " +
					"    (∀e:B. e ∈ E ⇒ h(e) ∈ {c:int | &0 ≤ c ∧ c < k}) ∧ (∀e:B. e ∉ E ⇒ h(e) = &0)}"},
				{Name: "remainderVectors", Text: "image( " +
					"    λh:B → int. module_sum(M.add, M.zero, E, λe:B. M.smul(h(e), e)), «residueFunctions»)"},
			},
		}, func(a *Argument, M *Expr[ModuleOps[Int, B]], E *Expr[Set[B]], k *Expr[Int], conditions Fact) {
			ring := a.TermAs[RingOps[Int]]("int_ring")
			basisInModule := a.Have(
				"basis vectors lie in the ambient module",
				"E ⊆ M.carrier",
				By(
					conditions,
					linear_independence.ModuleBasisDef.At(ring, M, E),
					linear_independence.IndependentInCarrier.At(ring, M, E)))
			evaluate := a.TermAs[Fun[Fun[B, Int], B]](
				"λh:B → int. module_sum(M.add, M.zero, E, λe:B. M.smul(h(e), e))")
			coefficients := a.TermAs[Set[Fun[B, Int]]]("«residueFunctions»")
			a.Show(
				"finite residue sums form a complete set of representatives",
				SplitConj(
					Case(
						"the remainder vectors form a finite subset of the module",
						SplitConj(
							Case(
								"the coefficient-evaluation image is finite",
								By(conditions, At(finiteCoefficients, E, k), finite_set.FiniteImage.At(evaluate, coefficients))),
							Case(
								"each coefficient sum is a module vector",
								BySets(basisInModule, conditions, At(combinationInModule, M, E))))),
					Case(
						"every vector has a remainder plus a scalar multiple",
						Derive(func(b *Argument) {
							v := b.FixAs[B]("v")
							inModule := b.Assume()
							residues, residueDefinition := b.LetAs[Fun[B, Int]](
								"residues",
								"λe:B. COND(e ∈ E, rem(module_basis_coordinates(int_ring, M, E, v, e), k), int_of_num(0))")
							remainder := b.TermAs[B]("module_sum(M.add, M.zero, E, λe:B. M.smul(residues(e), e))")
							quotient := b.TermAs[B](
								"module_sum(M.add, " +
									"    M.zero, " +
									"    E, " +
									"    λe:B. M.smul(div(module_basis_coordinates(int_ring, M, E, v, e), k), e))")
							b.Take(remainder)
							b.Take(quotient)
							bounds := b.Have(
								"division gives a coefficient in the residue interval",
								"∀e:B. "+
									"    &0 ≤ rem(module_basis_coordinates(int_ring, M, E, v, e), k) ∧ "+
									"    rem(module_basis_coordinates(int_ring, M, E, v, e), k) < k",
								Derive(func(c *Argument) {
									c.FixAs[B]("e")
									c.Show(
										"division by a positive modulus gives the residue bounds",
										ByArith(
											conditions,
											int_div_rem.DivisionAlgorithm.At(
												c.TermAs[Int]("module_basis_coordinates(int_ring, M, E, v, e)"), k),
											int_real_lift.AbsFixedIffNonneg.At(k)))
								}))
							inCoefficients := b.Have(
								"the truncated remainder coefficients belong to the finite function space",
								"residues ∈ «residueFunctions»",
								residueDefinition.Rw(),
								BySets(bounds))
							sameSum := b.Have(
								"off-basis truncation leaves the remainder sum unchanged",
								"module_sum(M.add, M.zero, E, λe:B. M.smul(residues(e), e)) = "+
									"module_sum(M.add, "+
									"    M.zero, "+
									"    E, "+
									"    λe:B. M.smul(rem(module_basis_coordinates(int_ring, M, E, v, e), k), e))",
								residueDefinition.Rw(),
								BySets(module.ModuleSumCongruence.At(b.TermAs[Op[B]]("M.add"), b.TermAs[B]("M.zero"), E,
									b.TermAs[Fun[B, B]](
										"λe:B. "+
											"    M.smul(COND(e ∈ E, rem(module_basis_coordinates(int_ring, M, E, v, e), k), int_of_num(0)), "+
											"        e)"),
									b.TermAs[Fun[B, B]]("λe:B. M.smul(rem(module_basis_coordinates(int_ring, M, E, v, e), k), e)"))))
							b.Show(
								"the chosen sums supply the remainder decomposition",
								SplitConjAll(
									Case(
										"the remainder is in the finite image",
										By(inCoefficients, set_image.FunInImage.At(evaluate, coefficients, residues))),
									Case(
										"the quotient sum is a module vector",
										By(
											basisInModule,
											conditions,
											At(
												combinationInModule,
												M,
												E,
												b.TermAs[Fun[B, Int]]("λe:B. div(module_basis_coordinates(int_ring, M, E, v, e), k)")))),
									Case(
										"basis expansion agrees with coefficient division",
										By(
											sameSum,
											inModule,
											basisInModule,
											conditions,
											At(
												divideCombination, M, E, b.TermAs[Fun[B, Int]]("module_basis_coordinates(int_ring, M, E, v)"), k),
											module_dimension.BasisCoordinatesSpec.At(ring, M, E, v)))))
						}))))
		})

		factorialMultiple := ctx.Lemma(Statement{
			Binders:    "∀m n:num.",
			Hypotheses: []string{"0 < m", "m ≤ n"},
			Conclusion: "factorial(n) = m * (factorial(m - 1) * factorial(n - m) * binomial(n, m))",
		}, func(a *Argument, m, n *Expr[Nat], conditions Fact) {
			predecessor := a.Have(
				"a positive index is the successor of its predecessor",
				"m = suc(m - 1)",
				ByArith(conditions))
			atIndex := a.Have(
				"the index is a factor of its own factorial",
				"factorial(m) = m * factorial(m - 1)",
				By(Normalized, predecessor, nat_arith.Factorial))
			a.Show(
				"the binomial factorial formula supplies the remaining factors",
				CalcEq(
					Leg(
						a.TermAs[Nat]("factorial(m) * factorial(n - m) * binomial(n, m)"),
						"split n! by the binomial formula",
						By(conditions, binomial.FactorialFormula.At(n, m))),
					FinalLeg(
						"m! is m times (m - 1)!",
						Simp(Fwd(atIndex), Fwd(nat_arith.MulAssoc)),
						Basic())))
		})

		scalarImage := ctx.Lemma(Statement{
			Binders:    "∀M:module_ops(int, B).",
			Hypotheses: []string{"module_on(int_ring, M)"},
			Conclusion: "∀c d:int. image(M.smul(c * d), M.carrier) ⊆ image(M.smul(c), M.carrier)",
		}, func(a *Argument, M *Expr[ModuleOps[Int, B]], moduleFact Fact, c, d *Expr[Int]) {
			pointwise := a.Have(
				"multiplying the preimage by the second scalar gives an image witness",
				"∀u:B. u ∈ M.carrier ⇒ M.smul(c * d, u) ∈ image(M.smul(c), M.carrier)",
				Derive(func(b *Argument) {
					u := b.FixAs[B]("u")
					inModule := b.Assume()
					b.Show(
						"the scalar multiple d times u is the required preimage",
						BySets(
							inModule,
							At(module.SmulMul.Read(moduleFact), c, d, u),
							At(module.SmulIn.Read(moduleFact), d, u)))
				}))
			a.Show(
				"the pointwise preimages give the image inclusion",
				BySets(pointwise))
		})

		translationInvariant := ctx.Lemma(Statement{
			Binders:    "∀M:module_ops(int, B).",
			Hypotheses: []string{"module_on(int_ring, M)"},
			Conclusion: "∀N:set(B). " +
				"    submodule(int_ring, M, N) ⇒ ∀r s:B. r ∈ M.carrier ∧ s ∈ N ⇒ (M.add(r, s) ∈ N ⇔ r ∈ N)",
		}, func(
			a *Argument,
			M *Expr[ModuleOps[Int, B]],
			moduleFact Fact,
			N *Expr[Set[B]],
			submoduleFact Fact,
			r, s *Expr[B],
			conditions Fact,
		) {
			ring := a.TermAs[RingOps[Int]]("int_ring")
			a.Show(
				"adding or subtracting a submodule member preserves membership",
				BySets(
					submoduleFact,
					conditions,
					submodule.SubmoduleSubset.At(ring, M, N),
					submodule.SubmoduleAdd.At(ring, M, N, r, s),
					submodule.SubmoduleSub.At(ring, M, N, a.TermAs[B]("M.add(r, s)"), s),
					At(group.MulInvCancelRightOn.Read(module.AddGroupOn.Read(moduleFact)), s, r)))
		})

		remainderMembership := ctx.Lemma(Statement{
			Binders:    "∀M:module_ops(int, B).",
			Hypotheses: []string{"module_on(int_ring, M)"},
			Conclusion: "∀k:int. ∀N:set(B). ∀r q v:B. " +
				"    submodule(int_ring, M, N) ∧ " +
				"    image(M.smul(k), M.carrier) ⊆ N ∧ " +
				"    r ∈ M.carrier ∧ " +
				"    q ∈ M.carrier ∧ " +
				"    v = M.add(r, M.smul(k, q)) ⇒ " +
				"    (v ∈ N ⇔ r ∈ N)",
		}, func(
			a *Argument,
			M *Expr[ModuleOps[Int, B]],
			moduleFact Fact,
			k *Expr[Int],
			N *Expr[Set[B]],
			r, q, v *Expr[B],
			conditions Fact,
		) {
			discarded := a.Have(
				"the discarded scalar multiple is in the submodule",
				"M.smul(k, q) ∈ N",
				BySets(conditions))
			a.Show(
				"submodule membership depends only on the remainder",
				By(
					Normalized,
					moduleFact,
					discarded,
					conditions,
					At(translationInvariant, M, N, r, a.TermAs[B]("M.smul(k, q)"))))
		})

		intersectionsDetermine := ctx.Lemma(Statement{
			Binders:    "∀M:module_ops(int, B).",
			Hypotheses: []string{"module_on(int_ring, M)"},
			Conclusion: "∀k:int. ∀R N₁ N₂:set(B). " +
				"    submodule(int_ring, M, N₁) ∧ " +
				"    submodule(int_ring, M, N₂) ∧ " +
				"    image(M.smul(k), M.carrier) ⊆ N₁ ∧ " +
				"    image(M.smul(k), M.carrier) ⊆ N₂ ∧ " +
				"    R ⊆ M.carrier ∧ " +
				"    (∀v:B. v ∈ M.carrier ⇒ ∃r q:B. r ∈ R ∧ q ∈ M.carrier ∧ v = M.add(r, M.smul(k, q))) ∧ " +
				"    N₁ ∩ R = N₂ ∩ R ⇒ " +
				"    N₁ = N₂",
		}, func(
			a *Argument,
			M *Expr[ModuleOps[Int, B]],
			moduleFact Fact,
			k *Expr[Int],
			R, N1, N2 *Expr[Set[B]],
			conditions Fact,
		) {
			pointwise := a.Have(
				"equal intersections give the same membership test throughout the module",
				"∀v:B. v ∈ M.carrier ⇒ (v ∈ N₁ ⇔ v ∈ N₂)",
				Derive(func(b *Argument) {
					v := b.FixAs[B]("v")
					inModule := b.Assume()
					r, q, decomposition := b.Obtain2As[B, B](
						"choose a common remainder decomposition",
						"∃r q:B. r ∈ R ∧ q ∈ M.carrier ∧ v = M.add(r, M.smul(k, q))",
						By(inModule, conditions))
					b.Show(
						"both submodules test membership on the same remainder",
						BySets(
							moduleFact,
							decomposition,
							conditions,
							At(remainderMembership, M, k, N1, r, q, v),
							At(remainderMembership, M, k, N2, r, q, v)))
				}))
			ring := a.TermAs[RingOps[Int]]("int_ring")
			a.Show(
				"both submodules are subsets of the carrier, so their membership predicates agree",
				BySets(
					pointwise,
					conditions,
					submodule.SubmoduleSubset.At(ring, M, N1),
					submodule.SubmoduleSubset.At(ring, M, N2)))
		})

		finiteContaining := ctx.Lemma(Statement{
			Binders:    "∀M:module_ops(int, B).",
			Hypotheses: []string{"module_on(int_ring, M)"},
			Conclusion: "∀k:int. ∀R:set(B). " +
				"    finite(R) ∧ " +
				"    R ⊆ M.carrier ∧ " +
				"    (∀v:B. v ∈ M.carrier ⇒ ∃r q:B. r ∈ R ∧ q ∈ M.carrier ∧ v = M.add(r, M.smul(k, q))) ⇒ " +
				"    finite({N:set(B) | submodule(int_ring, M, N) ∧ image(M.smul(k), M.carrier) ⊆ N})",
		}, func(
			a *Argument,
			M *Expr[ModuleOps[Int, B]],
			moduleFact Fact,
			k *Expr[Int],
			R *Expr[Set[B]],
			conditions Fact,
		) {
			submodules := a.TermAs[Set[Set[B]]](
				"{N:set(B) | submodule(int_ring, M, N) ∧ image(M.smul(k), M.carrier) ⊆ N}")
			intersect := a.TermAs[Fun[Set[B], Set[B]]]("λN:set(B). N ∩ R")
			powerset := a.TermAs[Set[Set[B]]]("{T:set(B) | T ⊆ R}")
			oneToOne := a.Have(
				"intersection with the remainder set determines the submodule",
				"injective_on({N:set(B) | submodule(int_ring, M, N) ∧ image(M.smul(k), M.carrier) ⊆ N}, "+
					"    λN:set(B). N ∩ R)",
				BySets(
					moduleFact,
					conditions,
					At(intersectionsDetermine, M, k, R),
					functions.InjectiveOnDef.At(submodules, intersect)))
			finiteImage := a.Have(
				"the intersection map has finite range",
				"finite(image(λN:set(B). N ∩ R, "+
					"        {N:set(B) | submodule(int_ring, M, N) ∧ image(M.smul(k), M.carrier) ⊆ N}))",
				Derive(func(b *Argument) {
					rangeSubset := b.Have(
						"every intersection is a subset of the remainder set",
						"image(λN:set(B). N ∩ R, "+
							"    {N:set(B) | submodule(int_ring, M, N) ∧ image(M.smul(k), M.carrier) ⊆ N}) ⊆ "+
							"{T:set(B) | T ⊆ R}",
						BySets())
					b.Show(
						"the range is a subset of a finite powerset",
						By(
							rangeSubset,
							conditions,
							finite_set.FinitePowerset.At(R),
							finite_set.FiniteSubset.At(
								b.TermAs[Set[Set[B]]](
									"image(λN:set(B). N ∩ R, "+
										"    {N:set(B) | submodule(int_ring, M, N) ∧ image(M.smul(k), M.carrier) ⊆ N})"),
								powerset)))
				}))
			a.Show(
				"the injective map into its finite image has finite domain",
				By(finiteImage, oneToOne, finite_set.FiniteImageInjEq.At(intersect, submodules)))
		})

		factorialContained := ctx.Lemma(Statement{
			Binders: "∀M:module_ops(int, B). ∀E N:set(B). ∀n:num.",
			Hypotheses: []string{
				"module_on(int_ring, M)",
				"finite(E)",
				"module_basis(int_ring, M, E)",
				"submodule(int_ring, M, N)",
				"finite(left_cosets(M.add, M.carrier, N))",
				"card(left_cosets(M.add, M.carrier, N)) ≤ n",
			},
			Conclusion: "image(M.smul(factorial(n)), M.carrier) ⊆ N",
		}, func(
			a *Argument,
			M *Expr[ModuleOps[Int, B]],
			E, N *Expr[Set[B]],
			n *Expr[Nat],
			conditions Fact,
		) {
			index := a.TermAs[Nat]("card(left_cosets(M.add, M.carrier, N))")
			_, multiple := a.ObtainAs[Nat](
				"the positive bounded index divides the common factorial",
				"∃d:num. factorial(n) = card(left_cosets(M.add, M.carrier, N)) * d",
				Derive(func(b *Argument) {
					b.Take(b.TermAs[Nat](
						"factorial(card(left_cosets(M.add, M.carrier, N)) - 1) * " +
							"factorial(n - card(left_cosets(M.add, M.carrier, N))) * " +
							"binomial(n, card(left_cosets(M.add, M.carrier, N)))"))
					b.Show(
						"the explicit binomial factor gives the multiple",
						By(FiniteIndexPositive.At(M, N), conditions, At(factorialMultiple, index, n)))
				}))
			embedded := a.Have(
				"the same factorization holds for integer scalars",
				"factorial(n) = int_of_num(card(left_cosets(M.add, M.carrier, N))) * int_of_num(d)",
				Simp(Fwd(multiple), Fwd(int_embed.OfNumMul)),
				Basic())
			a.Show(
				"a multiple of the annihilating index sends the module into the submodule",
				BySets(
					embedded,
					conditions,
					IndexAnnihilatesQuotient.At(M, N),
					At(scalarImage, M, a.TermAs[Int]("card(left_cosets(M.add, M.carrier, N))"), a.TermAs[Int]("d"))))
		})

		return ctx.Theorem(headline, func(
			a *Argument,
			M *Expr[ModuleOps[Int, B]],
			E *Expr[Set[B]],
			n *Expr[Nat],
			conditions Fact,
		) {
			positive := a.Have(
				"the common factorial scalar is positive",
				"int_of_num(0) < factorial(n)",
				ByArith(
					nat_arith.FactorialNonzero.At(n),
					int_embed.OfNumLt.At(a.TermAs[Nat]("0"), a.TermAs[Nat]("factorial(n)"))))
			R, representatives := a.ObtainAs[Set[B]](
				"choose finite representatives modulo the common factorial",
				"∃R:set(B). "+
					"    finite(R) ∧ "+
					"    R ⊆ M.carrier ∧ "+
					"    (∀v:B. v ∈ M.carrier ⇒ ∃r q:B. r ∈ R ∧ q ∈ M.carrier ∧ v = M.add(r, M.smul(factorial(n), q)))",
				Derive(func(b *Argument) {
					b.Take(b.TermAs[Set[B]](
						"image(λh:B → int. module_sum(M.add, M.zero, E, λe:B. M.smul(h(e), e)), " +
							"    {h:B → int | " +
							"        (∀e:B. e ∈ E ⇒ h(e) ∈ {c:int | &0 ≤ c ∧ c < factorial(n)}) ∧ (∀e:B. e ∉ E ⇒ h(e) = &0)})"))
					b.Show(
						"the coefficient residue construction supplies the representatives",
						By(positive, conditions, At(remainderRepresentatives, M, E, b.TermAs[Int]("factorial(n)"))))
				}))
			containing := a.TermAs[Set[Set[B]]](
				"{N:set(B) | submodule(int_ring, M, N) ∧ image(M.smul(factorial(n)), M.carrier) ⊆ N}")
			bounded := a.TermAs[Set[Set[B]]](
				"{N:set(B) | " +
					"    submodule(int_ring, M, N) ∧ " +
					"    finite(left_cosets(M.add, M.carrier, N)) ∧ " +
					"    card(left_cosets(M.add, M.carrier, N)) ≤ n}")
			finiteSuperset := a.Have(
				"only finitely many submodules contain the common factorial image",
				"finite({N:set(B) | submodule(int_ring, M, N) ∧ image(M.smul(factorial(n)), M.carrier) ⊆ N})",
				By(representatives, conditions, At(finiteContaining, M, a.TermAs[Int]("factorial(n)"), R)))
			inclusion := a.Have(
				"every bounded-index submodule contains that image",
				"{N:set(B) | "+
					"    submodule(int_ring, M, N) ∧ "+
					"    finite(left_cosets(M.add, M.carrier, N)) ∧ "+
					"    card(left_cosets(M.add, M.carrier, N)) ≤ n} ⊆ "+
					"{N:set(B) | submodule(int_ring, M, N) ∧ image(M.smul(factorial(n)), M.carrier) ⊆ N}",
				BySets(conditions, At(factorialContained, M, E)))
			a.Show(
				"the bounded-index family is a subset of that finite family",
				By(finiteSuperset, inclusion, finite_set.FiniteSubset.At(bounded, containing)))
		})
	}),
})}
