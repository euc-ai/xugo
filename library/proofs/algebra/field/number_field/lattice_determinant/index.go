package lattice_determinant

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/number_field/number_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/free_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/function_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/int_lattice"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/linear_determinant"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/linear_independence"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/characteristic_zero"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_construction"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_divides"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_embed"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_real_lift"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/real/rational"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/vector/determinant"
	"github.com/euc-ai/xugo/library/registry"
)

// IntegerBasisChangeDetUnit — an integer basis change has determinant
// plus or minus one: the coordinate changes from e to f and back are inverse
// matrices over the integer image, so their determinants, integers mapped
// into the field, multiply to one, and a unit of the integers is plus or
// minus one.
var IntegerBasisChangeDetUnit = integerBasisChangeDetUnitThm{family.Add(registry.ProofEntry{
	Name: "IntegerBasisChangeDetUnit",
	Key:  "prop_bb88c28083d45ddd",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀M:module_ops(A, B). ∀n:num. ∀e f:(num → B).",
		Hypotheses: []string{
			"characteristic_zero(field_ring(L))",
			"module_on(«ℤ», M)",
			"indexed_module_basis(«ℤ», M, n, e)",
			"indexed_module_basis(«ℤ», M, n, f)",
		},
		Conclusion: "matrix_over(«ℤ», n, basis_change_matrix(«ℤ», M, n, e, f)) ∧ " +
			"(«D» = L.one ∨ «D» = -L.one)",
		Abbrev: Abbrev{
			{Name: "D", Text: "determinant(«ℤ», n, basis_change_matrix(«ℤ», M, n, e, f))"},
		},
	}, func(
		a *Argument,
		L field.FieldFact[on.L],
		M *Expr[ModuleOps[A, B]],
		n *Expr[Nat],
		e, f *Arrow[Nat, B],
		given Fact,
	) {
		R, ringDef := a.LetAs[module_record.RingOps[A]]("R", "«ℤ»")
		P, pDef := a.LetAs[Fun2[Nat, Nat, A]]("P", "basis_change_matrix(R, M, n, e, f)")
		Q, qDef := a.LetAs[Fun2[Nat, Nat, A]]("Q", "basis_change_matrix(R, M, n, f, e)")
		characteristicZero := a.Have(
			"the field has characteristic zero",
			"characteristic_zero(field_ring(L))",
			By(given))
		integerModule := a.Have(
			"the integer scalars act on M",
			"module_on(R, M)",
			By(given, ringDef))
		eBasis := a.Have(
			"e is an indexed basis",
			"indexed_module_basis(R, M, n, e)",
			By(given, ringDef))
		fBasis := a.Have(
			"f is an indexed basis",
			"indexed_module_basis(R, M, n, f)",
			By(given, ringDef))
		ring := a.Have(
			"the module's scalar ring is commutative",
			"comm_ring_on(R)",
			By(integerModule, module.RingOn.At(R, M)))
		changes := a.Have(
			"the opposite coordinate changes are inverse matrices over the integer scalars",
			"matrix_product(R, n, P, Q) = matrix_identity(R, n) ∧ matrix_over(R, n, P) ∧ matrix_over(R, n, Q)",
			By(
				Normalized,
				pDef,
				qDef,
				integerModule,
				eBasis,
				fBasis,
				linear_determinant.BasisChangeInverse.At(R, M, n, e, f)))
		determinantProduct := a.Have(
			"the two determinants multiply to the scalar unit",
			"R.mul(determinant(R, n, P), determinant(R, n, Q)) = R.one",
			By(
				changes,
				determinant.DeterminantMultiplicative.Read(ring).At(n, P, Q),
				determinant.DeterminantIdentity.Read(ring).At(n)))
		integral := a.Have(
			"both determinants are integer images",
			"determinant(R, n, P) ∈ integer_image(field_ring(L)) ∧ "+
				"determinant(R, n, Q) ∈ integer_image(field_ring(L))",
			By(
				Normalized,
				characteristicZero,
				L,
				ringDef,
				changes,
				DeterminantIntegralEntries.Read(L).At(n, P),
				DeterminantIntegralEntries.Read(L).At(n, Q)))
		r, s, determinantValues := a.Obtain2As[Int, Int](
			"choose the two native integer determinants",
			"∃r s:int. "+
				"    determinant(R, n, P) = integer_map(field_ring(L), r) ∧ "+
				"    determinant(R, n, Q) = integer_map(field_ring(L), s)",
			BySets(integral, characteristic_zero.IntegerImageDef))
		restrictedOps := a.Have(
			"restriction preserves the scalar product and unit",
			"R.mul = field_ring(L).mul ∧ R.one = field_ring(L).one",
			ringDef.Rw(),
			Simp(
				Fwd(module_record.RestrictRingDef),
				Fwd(module_record.RingMulDef),
				Fwd(module_record.RingOneDef)),
			Basic())
		fieldOps := a.Have(
			"the field ring has the field's unit and negation",
			"field_ring(L).one = L.one ∧ field_ring(L).neg = L.neg",
			Simp(Fwd(field.FieldRingDef), Fwd(module_record.RingOneDef), Fwd(module_record.RingNegDef)),
			Basic())
		integerProduct := a.Have(
			"the integer map preserves the product and unit",
			"integer_map(field_ring(L), r * s) = "+
				"field_ring(L).mul(integer_map(field_ring(L), r), integer_map(field_ring(L), s)) ∧ "+
				"integer_map(field_ring(L), 1) = field_ring(L).one",
			By(characteristic_zero.IntegerMapHom.Read(field.RingOn.Read(L))))
		mappedUnit := a.Have(
			"the mapped integer determinants have product one",
			"integer_map(field_ring(L), r * s) = integer_map(field_ring(L), 1)",
			By(Normalized, determinantProduct, integerProduct, determinantValues, restrictedOps))
		injective := a.Have(
			"characteristic zero makes the integer map injective",
			"injective_on(𝕌, integer_map(field_ring(L)))",
			By(
				field.RingOn.Read(L),
				characteristicZero,
				characteristic_zero.IntegerMapInjective.At(a.TermAs[module_record.RingOps[A]]("field_ring(L)"))))
		nativeUnit := a.Have(
			"the native integer determinants multiply to one",
			"r * s = 1",
			BySets(
				mappedUnit,
				injective,
				functions.InjectiveOnDef.At(
					a.TermAs[Set[Int]]("𝕌"), a.TermAs[Fun[Int, A]]("integer_map(field_ring(L))"))))
		signedUnit := a.Have(
			"a unit of the integers is plus or minus one",
			"r = 1 ∨ r = -1",
			By(nativeUnit, int_divides.UnitPlusMinusOne.At(r, s)))
		negativeUnit := a.Have(
			"the integer map preserves the negative unit",
			"integer_map(field_ring(L), -1) = field_ring(L).neg(integer_map(field_ring(L), 1))",
			By(characteristic_zero.IntegerMapHom.Read(field.RingOn.Read(L))))
		a.Show(
			"the integer change matrix has determinant plus or minus the field unit",
			By(Normalized, negativeUnit, fieldOps, integerProduct, determinantValues, changes, signedUnit))
	}),
})}

// LatticeIndexEqAbsDet — for full lattices N ⊆ M of a number field L with
// bases e of M and f of N over the integers of L, the quotient M/N is finite
// and its index is the absolute value of the rational determinant of the
// change of basis from e to f.
//
// Two scalar rings act on the lattices. The host scalars are the integer
// image «ℤ» of ℤ in L, the ring R of the statement's modules U (on M) and
// W (on N); the native scalars are ℤ itself, acting on the same additive
// groups by restriction of scalars (V on M, with N inside it). The counting
// is done natively and carried back to the host at the end.
//
// The argument has four phases. (1) The e-coordinates identify V with the
// integer vectors supported below n, N with a submodule K of them, and M/N
// with the quotient by K, finite because N has full rank. (2) K has a
// triangular basis b with r rows; the coordinates carry the n-element basis
// f of N to a basis of K, so r = n by uniqueness of basis size, and the n
// strictly increasing pivots below n are the identity. (3) The index of a
// full triangular submodule is the product of its diagonal; pulling b back
// to a basis g of N makes the change from e to g the transposed triangle
// mapped into L, with that product as its determinant. (4) The change from
// g to f is an integer change of basis, of determinant ±1, so det(e → f) is
// plus or minus the index, and so is its rational value.
var LatticeIndexEqAbsDet = latticeIndexEqAbsDetThm{family.Add(registry.ProofEntry{
	Name: "LatticeIndexEqAbsDet",
	Key:  "prop_5896e4d678f93820",
	Build: family.Sections(Statement{
		Binders: "∀L:field_on(A). ∀M N:set(A). ∀n:num. ∀e f:(num → A).",
		Hypotheses: []string{
			"number_field(L)",
			"full_integer_lattice(L, M)",
			"full_integer_lattice(L, N)",
			"N ⊆ M",
			"indexed_module_basis(«ℤ», restrict_module(regular_module(field_ring(L)), M), n, e)",
			"indexed_module_basis(«ℤ», restrict_module(regular_module(field_ring(L)), N), n, f)",
		},
		Conclusion: "finite(left_cosets(L.add, M, N)) ∧ " +
			"real_of_num(card(left_cosets(L.add, M, N))) = " +
			"real_abs(rational_value(L, " +
			"        determinant(«ℤ», " +
			"            n, " +
			"            basis_change_matrix(«ℤ», " +
			"                restrict_module(regular_module(field_ring(L)), M), " +
			"                n, " +
			"                e, " +
			"                f))))",
	}, func(ctx *Script, headline string) *GoalStackNode {
		nativeCoordinates := ctx.Lemma(Statement{
			Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀E:set(B). ∀v:B.",
			Hypotheses: []string{
				"comm_ring_on(R)", "characteristic_zero(R)",
				"module_on(restrict_ring(R, integer_image(R)), M)",
				"finite(E)", "module_basis(restrict_ring(R, integer_image(R)), M, E)", "v ∈ M.carrier",
			},
			Conclusion: "module_basis_coordinates(restrict_ring(R, integer_image(R)), M, E, v) = " +
				"λx:B. " +
				"    integer_map(R, " +
				"        module_basis_coordinates(int_ring, scalar_restriction(integer_map(R), M), E, v, x))",
		}, func(
			a *Argument,
			R *Expr[module_record.RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			E *Expr[Set[B]],
			v *Expr[B],
			given Fact,
		) {
			parts := a.Conjuncts(
				given,
				"R is a commutative ring",
				"R has characteristic zero",
				"M is a module over the integer image",
				"E is finite",
				"E is a basis of M",
				"v lies in M")
			ring, characteristicZero, moduleOn, finiteE, basis, vIn :=
				parts[0], parts[1], parts[2], parts[3], parts[4], parts[5]
			Z, zDef := a.LetAs[module_record.RingOps[A]]("Z", "restrict_ring(R, integer_image(R))")
			V, vDef := a.LetAs[ModuleOps[Int, B]]("V", "scalar_restriction(integer_map(R), M)")
			cDef := a.Let("c", a.TermAs[Fun[B, Int]]("module_basis_coordinates(int_ring, V, E, v)"))
			integerRing := a.TermAs[module_record.RingOps[Int]]("int_ring")
			nativeOps := a.Have(
				"scalar restriction keeps addition and the carrier",
				"V.add = M.add ∧ "+
					"V.zero = M.zero ∧ "+
					"V.smul = (λz:int. λx:B. M.smul(integer_map(R, z), x)) ∧ "+
					"V.carrier = M.carrier",
				Simp(
					Fwd(vDef),
					Fwd(module_record.ScalarRestrictionDef),
					Fwd(module_record.ModAddDef),
					Fwd(module_record.ModZeroDef),
					Fwd(module_record.ModSmulDef),
					Fwd(module_record.ModCarrierDef)),
				Basic())
			nativeBasis := a.Have(
				"the same finite family is a native integer basis",
				"module_on(int_ring, V) ∧ module_basis(int_ring, V, E)",
				By(
					Normalized,
					ring,
					characteristicZero,
					moduleOn,
					basis,
					zDef,
					vDef,
					int_lattice.IntegerScalarRestriction.At(R, M)))
			nativeSpec := a.Have(
				"native coordinates give the finite expansion and vanish off the basis",
				"(∀x:B. x ∈ E ⇒ c(x) ∈ ring_carrier(int_ring)) ∧ "+
					"(∀x:B. x ∉ E ⇒ c(x) = ring_zero(int_ring)) ∧ "+
					"module_sum(V.add, V.zero, E, λx:B. V.smul(c(x), x)) = v",
				Derive(func(b *Argument) {
					vNative := b.Have(
						"the vector belongs to the restricted module",
						"v ∈ V.carrier",
						By(Normalized, vIn, nativeOps))
					integerOps := b.Have(
						"native integer scalars have the usual zero and universal carrier",
						"ring_carrier(int_ring) = 𝕌 ∧ ring_zero(int_ring) = 0",
						Simp(
							Fwd(int_real_lift.IntRingDef),
							Fwd(module_record.RingCarrierDef),
							Fwd(module_record.RingZeroDef)),
						Basic())
					b.Show(
						"read the native coordinate specification",
						By(
							Normalized,
							cDef,
							vNative,
							finiteE,
							nativeBasis,
							integerOps,
							module_dimension.BasisCoordinatesSpec.At(integerRing, V, E, v)))
				}))
			imageOps := a.Have(
				"restriction uses the host zero and the integer image carrier",
				"Z.zero = R.zero ∧ Z.carrier = integer_image(R)",
				Simp(
					Fwd(zDef),
					Fwd(module_record.RestrictRingDef),
					Fwd(module_record.RingZeroDef),
					Fwd(module_record.RingCarrierDef)),
				Basic())
			mapZero := a.Have(
				"the integer map preserves zero",
				"integer_map(R, 0) = R.zero",
				By(ring, characteristic_zero.IntegerMapHom))
			mappedIn := a.Have(
				"every mapped coefficient is an integer-image scalar",
				"∀x:B. integer_map(R, c(x)) ∈ Z.carrier",
				BySets(imageOps, characteristic_zero.IntegerImageDef))
			nativeZero := a.Have(
				"the native zero is the zero integer",
				"ring_zero(int_ring) = 0",
				Simp(Fwd(int_real_lift.IntRingDef), Fwd(module_record.RingZeroDef)),
				Basic())
			mappedOutside := a.Have(
				"mapped coordinates vanish off the basis",
				"∀x:B. x ∉ E ⇒ integer_map(R, c(x)) = Z.zero",
				By(Normalized, nativeSpec, nativeZero, mapZero, imageOps))
			mappedExpansion := a.Have(
				"mapping the native coefficients preserves the module expansion",
				"module_sum(M.add, M.zero, E, λx:B. M.smul(integer_map(R, c(x)), x)) = v",
				nativeSpec.Simp(Fwd(nativeOps)),
				By(nativeSpec))
			a.Show(
				"host coordinate uniqueness identifies the mapped native coordinates",
				By(
					moduleOn,
					finiteE,
					basis,
					vIn,
					mappedIn,
					mappedOutside,
					mappedExpansion,
					module_dimension.BasisCoordinatesUnique.At(
						Z, M, E, v, a.TermAs[Fun[B, A]]("λx:B. integer_map(R, c(x))"))))
		})

		indexedBasisImage := ctx.Lemma(Statement{
			Binders: "∀R:ring_ops(A). " +
				"∀M:module_ops(A, B). " +
				"∀N:module_ops(A, C). " +
				"∀f:(B → C). " +
				"∀n:num. " +
				"∀e:(num → B).",
			Hypotheses: []string{"module_isomorphism(R, M, N, f)", "indexed_module_basis(R, M, n, e)"},
			Conclusion: "indexed_module_basis(R, N, n, λi:num. f(e(i)))",
		}, func(
			a *Argument,
			R *Expr[module_record.RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			N *Expr[ModuleOps[A, C]],
			f *Arrow[B, C],
			n *Expr[Nat],
			e *Arrow[Nat, B],
			given Fact,
		) {
			isomorphism := a.Have(
				"an isomorphism is an injective homomorphism onto the carrier",
				"module_homomorphism(R, M, N, f) ∧ injective_on(M.carrier, f) ∧ image(f, M.carrier) = N.carrier",
				By(given, module_homomorphism.ModuleIsomorphismDef))
			basis := a.Have(
				"the indexed basis is independent and spans the source carrier",
				"injective_on({i:num | i < n}, e) ∧ "+
					"module_independent(R, M, {e(i):B | i:num | i < n}) ∧ "+
					"module_span(R, M, {e(i):B | i:num | i < n}) = M.carrier",
				By(given, linear_independence.IndexedModuleBasisDef, linear_independence.ModuleBasisDef))
			basisIn := a.Have(
				"basis vectors belong to the source carrier",
				"{e(i):B | i:num | i < n} ⊆ M.carrier",
				By(basis, linear_independence.ModuleIndependentDef))
			image := a.Have(
				"the image family has the same indexing",
				"image(f, {e(i):B | i:num | i < n}) = {f(e(i)):C | i:num | i < n}",
				BySets())
			independent := a.Have(
				"injectivity preserves linear independence",
				"module_independent(R, N, image(f, {e(i):B | i:num | i < n}))",
				By(
					isomorphism,
					basis,
					linear_independence.IndependentImage.At(R, M, N, f, a.TermAs[Set[B]]("{e(i):B | i:num | i < n}"))))
			span := a.Have(
				"surjectivity carries the spanning set onto the target carrier",
				"module_span(R, N, image(f, {e(i):B | i:num | i < n})) = N.carrier",
				By(
					isomorphism,
					basis,
					basisIn,
					linear_independence.HomSpan.At(R, M, N, f, a.TermAs[Set[B]]("{e(i):B | i:num | i < n}"))))
			indexing := a.Have(
				"the image family is indexed injectively",
				"injective_on({i:num | i < n}, λi:num. f(e(i)))",
				isomorphism.Simp(Fwd(functions.InjectiveOnDef)),
				basis.Simp(Fwd(functions.InjectiveOnDef)),
				Simp(Fwd(functions.InjectiveOnDef)),
				BySets(Normalized, isomorphism, basis, basisIn))
			a.Show(
				"the indexed image is a basis",
				By(
					Normalized,
					image,
					independent,
					span,
					indexing,
					linear_independence.IndexedModuleBasisDef,
					linear_independence.ModuleBasisDef))
		})

		integerMapNaturalLaws := ctx.Lemma(
			"∀R:comm_ring_on(A). "+
				"    (∀n:num. integer_map(R, n) ∈ R.carrier) ∧ "+
				"    integer_map(R, 1) = R.one ∧ "+
				"    (∀m n:num. integer_map(R, m * n) = integer_map(R, m) * integer_map(R, n))",
			func(a *Argument, R comm_ring.CommRingFact[on.R]) {
				a.Do(SplitConjAll(
					Case(
						"natural integer images belong to the ring",
						BySets(characteristic_zero.IntegerMapHom.Read(R))),
					Case(
						"the integer image of one is the ring identity",
						By(characteristic_zero.IntegerMapHom.Read(R))),
					Case(
						"natural integer images preserve multiplication",
						By(characteristic_zero.IntegerMapHom.Read(R), int_embed.OfNumMul)),
				))
			})

		naturalProductStepsCommute := ctx.Lemma(Statement{
			Binders:    "∀d:(num → num). ∀x y z:num.",
			Hypotheses: []string{"x ≠ y"},
			Conclusion: "d(x) * (d(y) * z) = d(y) * (d(x) * z)",
		}, By(nat_arith.MulAssoc, nat_arith.MulSym))

		naturalProductRecursion := ctx.Lemma(
			"∀d:(num → num). "+
				"    set_fold(λi:num. λa:num. d(i) * a, ∅, 1) = 1 ∧ "+
				"    (∀x:num. ∀s:set(num). "+
				"        finite(s) ⇒ "+
				"        set_fold(λi:num. λa:num. d(i) * a, insert(x, s), 1) = "+
				"        COND(x ∈ s, "+
				"            set_fold(λi:num. λa:num. d(i) * a, s, 1), "+
				"            d(x) * set_fold(λi:num. λa:num. d(i) * a, s, 1)))",
			func(a *Argument, d *Arrow[Nat, Nat]) {
				a.Show(
					"natural products obey finite fold recursion",
					By(
						naturalProductStepsCommute,
						cardinality.FiniteRecursion.At(
							a.TermAs[Op[Nat]]("λi:num. λa:num. d(i) * a"),
							a.TermAs[Nat]("1"))))
			})

		integerMapNaturalProduct := ctx.Lemma(Statement{
			Binders: "∀R:ring_ops(A). ∀S:set(num). ∀d:(num → num).",
			Hypotheses: []string{
				"comm_ring_on(R)",
				"finite(S)",
			},
			Conclusion: "module_sum(R.mul, R.one, S, λi:num. integer_map(R, int_of_num(d(i)))) = " +
				"integer_map(R, int_of_num(set_fold(λi:num. λa:num. d(i) * a, S, 1)))",
		}, func(
			a *Argument,
			R *Expr[module_record.RingOps[A]],
			S *Expr[Set[Nat]],
			d *Arrow[Nat, Nat],
			given Fact,
		) {
			ring := a.Have(
				"the ring is commutative",
				"comm_ring_on(R)",
				By(given))
			laws := At(ctx.AtTypeVars(integerMapNaturalLaws, TypeBinder.BindA[A]()), R)
			factors := a.TermAs[Fun[Nat, A]]("λi:num. integer_map(R, int_of_num(d(i)))")
			a.Show(
				"integer images commute with finite natural products",
				ByInduction(
					finite_set.FiniteInductFresh,
					given,
					Case(
						"the empty product maps to the identity",
						By(
							ring,
							module.ModuleSumEmpty.At(a.TermAs[Op[A]]("R.mul"), a.TermAs[A]("R.one"), factors),
							At(naturalProductRecursion, d),
							laws)),
					Case(
						"a fresh insertion multiplies both products by the same integer image",
						Derive(func(b *Argument) {
							x := b.FixAs[Nat]("x")
							s := b.FixAs[Set[Nat]]("s")
							induction := b.Assume()
							b.Show(
								"preservation of multiplication carries the induction step",
								By(
									ring,
									induction,
									At(naturalProductRecursion, d),
									laws,
									module.ModuleSumInsertMonoid.Read(comm_ring.MulMonoidOn.Read(ring)).At(s, x, factors)))
						})),
				))
		})

		return ctx.Theorem(headline, func(
			a *Argument,
			L field.FieldFact[on.L],
			M, N *Expr[Set[A]],
			n *Expr[Nat],
			e, f *Arrow[Nat, A],
			given Fact,
		) {
			// Phase 1 — the finite quotient in coordinates. Over the native scalars N has
			// full rank in V, so V/N is finite. Summing integer coefficients against e
			// (the map S) identifies the free module Zn of integer vectors supported
			// below n with V; its inverse C, the e-coordinate map, takes N to a submodule
			// K of Zn and V/N to Zn/K, which has the same number m of cosets.
			host := a.TermAs[module_record.RingOps[A]]("field_ring(L)")
			R, rDef := a.LetAs[module_record.RingOps[A]](
				"R", "restrict_ring(field_ring(L), integer_image(field_ring(L)))")
			U, uDef := a.LetAs[ModuleOps[A, A]]("U", "restrict_module(regular_module(field_ring(L)), M)")
			W, wDef := a.LetAs[ModuleOps[A, A]]("W", "restrict_module(regular_module(field_ring(L)), N)")
			V, vDef := a.LetAs[ModuleOps[Int, A]]("V", "scalar_restriction(integer_map(field_ring(L)), U)")
			I, iDef := a.LetAs[Set[Nat]]("I", "{i:num | i < n}")
			E, eDef := a.LetAs[Set[A]]("E", "{e(i):A | i:num | i < n}")
			F, fDef := a.LetAs[Set[A]]("F", "{f(i):A | i:num | i < n}")
			integerRing := a.TermAs[module_record.RingOps[Int]]("int_ring")
			regular := a.TermAs[ModuleOps[A, A]]("regular_module(field_ring(L))")
			numberField := a.Have(
				"L is a number field",
				"number_field(L)",
				By(given))
			scalars := a.Conjuncts(
				GroupPremises(L, numberField, number_field.NumberFieldScalars.At(a.TermAs[FieldOps[A]]("L"))),
				"L has characteristic zero",
				"its rational image is a subfield",
				"the integer image lies in the rational image",
				"the integer image is a commutative ring",
				"and a principal ideal domain",
				"L is a module over the integer image",
				"and over the rational image")
			rings := a.Have(
				"the field has characteristic zero, and its ring and the integer image are commutative rings",
				"characteristic_zero(field_ring(L)) ∧ comm_ring_on(field_ring(L)) ∧ comm_ring_on(R)",
				By(Normalized, rDef, scalars[0], scalars[3], field.RingOn.Read(L)))
			ambient := a.Have(
				"integer-image scalars act on the ambient additive group",
				"module_on(R, regular_module(field_ring(L)))",
				By(Normalized, rDef, scalars[5]))
			lattices := a.Have(
				"both lattices are submodules of the ambient module",
				"submodule(R, regular_module(field_ring(L)), M) ∧ submodule(R, regular_module(field_ring(L)), N)",
				By(Normalized, rDef, given, int_lattice.FullIntegerLatticeDef, int_lattice.IntegerLatticeDef))
			modules := a.Have(
				"U and W are modules over R, and N is a submodule of U",
				"module_on(R, U) ∧ module_on(R, W) ∧ submodule(R, U, N)",
				By(
					Normalized,
					ambient,
					uDef,
					wDef,
					lattices,
					given,
					submodule.SubmoduleModuleOn.At(R, regular, M),
					submodule.SubmoduleModuleOn.At(R, regular, N),
					submodule.SubmoduleRestrict.At(R, regular, M, N)))
			bases := a.Have(
				"e and f are injective on I, and their images E and F are bases of U and W",
				"injective_on(I, e) ∧ injective_on(I, f) ∧ module_basis(R, U, E) ∧ module_basis(R, W, F)",
				By(Normalized, iDef, eDef, fDef, given, linear_independence.IndexedModuleBasisDef))
			images := a.Have(
				"the basis sets are their indexed images",
				"E = image(e, I) ∧ F = image(f, I)",
				BySets(iDef, eDef, fDef))
			finiteI := a.Have(
				"the index set has size n",
				"finite(I) ∧ card(I) = n",
				By(
					iDef,
					num_segment.FiniteBelowStrict.At(n),
					num_segment.HasSizeBelowStrict.At(n),
					cardinality.CardOfSized.Inst[Nat]().At(I, n)))
			finiteBases := a.Have(
				"both basis sets have size n",
				"finite(E) ∧ finite(F) ∧ card(E) = n ∧ card(F) = n",
				By(
					Normalized,
					finiteI,
					images,
					bases,
					finite_set.FiniteImage.At(e, I),
					finite_set.FiniteImage.At(f, I),
					cardinality.CardImageInj.At(e, I),
					cardinality.CardImageInj.At(f, I)))
			additive := a.Have(
				"V keeps L's addition, zero and negation on M, U scales by "+
					"L's product, W is U on N, and W over native scalars is V on N",
				"V.add = L.add ∧ "+
					"V.zero = L.zero ∧ "+
					"V.neg = L.neg ∧ "+
					"V.carrier = M ∧ "+
					"U.smul = L.mul ∧ "+
					"W = restrict_module(U, N) ∧ "+
					"scalar_restriction(integer_map(field_ring(L)), W) = restrict_module(V, N)",
				Simp(
					Fwd(vDef),
					Fwd(uDef),
					Fwd(wDef),
					Fwd(module_record.RegularModuleDef),
					Fwd(field.FieldRingDef),
					Fwd(module_record.RingAddDef),
					Fwd(module_record.RingZeroDef),
					Fwd(module_record.RingNegDef),
					Fwd(module_record.RingMulDef),
					Fwd(module_record.RingCarrierDef),
					Fwd(module_record.ScalarRestrictionDef.Inst(
						TypeBinder.BindA[Int](), TypeBinder.BindC[A](), TypeBinder.BindB[A]())),
					Fwd(module_record.RestrictModuleDef.Inst(TypeBinder.BindA[A](), TypeBinder.BindB[A]())),
					Fwd(module_record.RestrictModuleDef.Inst(TypeBinder.BindA[Int](), TypeBinder.BindB[A]())),
					Fwd(module_record.ModAddDef.Inst(TypeBinder.BindA[Int](), TypeBinder.BindB[A]())),
					Fwd(module_record.ModZeroDef.Inst(TypeBinder.BindA[Int](), TypeBinder.BindB[A]())),
					Fwd(module_record.ModNegDef.Inst(TypeBinder.BindA[Int](), TypeBinder.BindB[A]())),
					Fwd(module_record.ModSmulDef.Inst(TypeBinder.BindA[A](), TypeBinder.BindB[A]())),
					Fwd(module_record.ModCarrierDef.Inst(TypeBinder.BindA[Int](), TypeBinder.BindB[A]())),
					Fwd(module_record.ModAddDef.Inst(TypeBinder.BindA[A](), TypeBinder.BindB[A]())),
					Fwd(module_record.ModZeroDef.Inst(TypeBinder.BindA[A](), TypeBinder.BindB[A]())),
					Fwd(module_record.ModNegDef.Inst(TypeBinder.BindA[A](), TypeBinder.BindB[A]())),
					Fwd(module_record.ModSmulDef.Inst(TypeBinder.BindA[Int](), TypeBinder.BindB[A]())),
					Fwd(module_record.ModCarrierDef.Inst(TypeBinder.BindA[A](), TypeBinder.BindB[A]()))),
				Basic())
			native := a.Have(
				"over the native scalars V is a module with submodule N, and E and F are bases of V and of N",
				"module_on(int_ring, V) ∧ "+
					"submodule(int_ring, V, N) ∧ "+
					"module_basis(int_ring, V, E) ∧ "+
					"module_basis(int_ring, restrict_module(V, N), F)",
				By(
					Normalized,
					rDef,
					vDef,
					rings,
					modules,
					bases,
					additive,
					int_lattice.IntegerScalarRestriction.At(host, U),
					int_lattice.IntegerScalarRestriction.At(host, W)))
			equalRank := a.Have(
				"the submodule has a finite basis of the same cardinality",
				"∃F₁:set(A). finite(F₁) ∧ module_basis(int_ring, restrict_module(V, N), F₁) ∧ card(F₁) = card(E)",
				Witness(F),
				By(Normalized, finiteBases, native))
			finiteNative := a.Have(
				"equal rank makes the native quotient finite",
				"finite(left_cosets(V.add, V.carrier, N))",
				By(native, finiteBases, equalRank, int_lattice.FullRankIffFiniteIndex.Inst[A]().At(V, E, N)))
			finiteHost := a.Have(
				"the original additive quotient is finite",
				"finite(left_cosets(L.add, M, N))",
				By(Normalized, finiteNative, additive))
			nativeIndexed := a.Have(
				"e is an indexed native basis of V",
				"indexed_module_basis(int_ring, V, n, e)",
				By(iDef, eDef, bases, native, linear_independence.IndexedModuleBasisDef.At(integerRing, V, n, e)))
			Zn, znDef := a.LetAs[ModuleOps[Int, Fun[Nat, Int]]]("Zn", "free_module_record(int_ring, I)")
			S, sDef := a.LetAs[Fun[Fun[Nat, Int], A]](
				"S", "λu:(num → int). module_sum(V.add, V.zero, I, λi:num. V.smul(u(i), e(i)))")
			C, cDef := a.LetAs[Fun[A, Fun[Nat, Int]]]("C", "inverse_on(Zn.carrier, S)")
			K, kDef := a.LetAs[Set[Fun[Nat, Int]]]("K", "image(C, N)")
			sumIso := a.Have(
				"summing integer coefficients against e identifies the finite free module with V",
				"module_isomorphism(int_ring, Zn, V, S)",
				By(native, nativeIndexed, iDef, znDef, sDef, int_lattice.IndexedBasisIsomorphism.At(V, n, e)))
			sumParts := a.Have(
				"the coordinate sum is linear, injective, and onto",
				"module_homomorphism(int_ring, Zn, V, S) ∧ "+
					"injective_on(Zn.carrier, S) ∧ "+
					"image(S, Zn.carrier) = V.carrier",
				By(sumIso, module_homomorphism.ModuleIsomorphismDef))
			iso := a.Have(
				"its inverse, the e coordinate map, identifies V with the finite free module",
				"module_isomorphism(int_ring, V, Zn, C)",
				By(Normalized, cDef, sumIso, module_homomorphism.IsomorphismInverse.At(integerRing, Zn, V, S)))
			isoParts := a.Have(
				"the coordinate isomorphism is linear, injective, and onto",
				"module_homomorphism(int_ring, V, Zn, C) ∧ "+
					"injective_on(V.carrier, C) ∧ "+
					"image(C, V.carrier) = Zn.carrier",
				By(iso, module_homomorphism.ModuleIsomorphismDef.At(integerRing, V, Zn, C)))
			subK := a.Have(
				"the coordinate image of N is a submodule",
				"submodule(int_ring, Zn, K)",
				By(
					Normalized,
					kDef,
					isoParts,
					native,
					module_homomorphism.HomImageSubmodule.At(integerRing, V, Zn, C, N)))
			quotientIso := a.Have(
				"the coordinate isomorphism descends to the quotients",
				"module_isomorphism(int_ring, "+
					"    quotient_module(V, N), "+
					"    quotient_module(Zn, K), "+
					"    λX:set(A). image(C, X))",
				By(
					Normalized,
					kDef,
					iso,
					native,
					module_homomorphism.QuotientIsomorphism.At(integerRing, V, Zn, C, N)))
			quotientCarriers := a.Have(
				"quotient module carriers are the additive coset sets",
				"quotient_module(V, N).carrier = left_cosets(V.add, V.carrier, N) ∧ "+
					"quotient_module(Zn, K).carrier = left_cosets(Zn.add, Zn.carrier, K)",
				Simp(Fwd(submodule.QuotientModuleDef), Fwd(module_record.ModCarrierDef)),
				Basic())
			quotientBijection := a.Have(
				"the induced map bijects the coset sets",
				"injective_on(left_cosets(V.add, V.carrier, N), λX:set(A). image(C, X)) ∧ "+
					"image(λX:set(A). image(C, X), left_cosets(V.add, V.carrier, N)) = "+
					"left_cosets(Zn.add, Zn.carrier, K)",
				By(
					quotientIso,
					quotientCarriers,
					module_homomorphism.ModuleIsomorphismDef.At(
						integerRing,
						a.TermAs[ModuleOps[Int, Set[A]]]("quotient_module(V, N)"),
						a.TermAs[ModuleOps[Int, Set[Fun[Nat, Int]]]]("quotient_module(Zn, K)"),
						a.TermAs[Fun[Set[A], Set[Fun[Nat, Int]]]]("λX:set(A). image(C, X)"))))
			quotientCard := a.Have(
				"both finite quotients have the same cardinality",
				"finite(left_cosets(Zn.add, Zn.carrier, K)) ∧ "+
					"card(left_cosets(Zn.add, Zn.carrier, K)) = card(left_cosets(V.add, V.carrier, N))",
				By(
					finiteNative,
					quotientBijection,
					finite_set.FiniteImage.At(
						a.TermAs[Fun[Set[A], Set[Fun[Nat, Int]]]]("λX:set(A). image(C, X)"),
						a.TermAs[Set[Set[A]]]("left_cosets(V.add, V.carrier, N)")),
					cardinality.CardImageInj.At(
						a.TermAs[Fun[Set[A], Set[Fun[Nat, Int]]]]("λX:set(A). image(C, X)"),
						a.TermAs[Set[Set[A]]]("left_cosets(V.add, V.carrier, N)"))))
			nativeParts := a.Conjuncts(
				native,
				"V is a native module",
				"N is a native submodule of V",
				"E is a native basis of V",
				"F is a native basis of N")
			onV, subN := nativeParts[0], nativeParts[1]
			m, mDef := a.LetAs[Nat]("m", "card(left_cosets(V.add, V.carrier, N))")
			onZnAndRing := a.Have(
				"the native scalars form a commutative ring, and Zn is a native module",
				"comm_ring_on(int_ring) ∧ module_on(int_ring, Zn)",
				By(
					onV,
					isoParts,
					module.RingOn.At(integerRing, V),
					module_homomorphism.HomTarget.At(integerRing, V, Zn, C)))
			onZn := a.Have(
				"Zn is a native module",
				"module_on(int_ring, Zn)",
				By(onZnAndRing))
			freeCarrier := a.Have(
				"the coordinate module has finite support carrier",
				"Zn.carrier = finite_supp(int_of_num(0), 𝕌, I)",
				Simp(
					Fwd(znDef),
					Fwd(int_real_lift.IntRingDef),
					Fwd(free_module.FreeModuleRecordDef),
					Fwd(module_record.ModCarrierDef)),
				Basic())
			nIn := a.Have(
				"the submodule carrier lies in V",
				"N ⊆ V.carrier",
				By(subN, submodule.SubmoduleSubset))
			nativeN := a.TermAs[ModuleOps[Int, A]]("restrict_module(V, N)")
			nativeNCarrier := a.Have(
				"the restricted native carrier is N",
				"restrict_module(V, N).carrier = N",
				Simp(Fwd(module_record.RestrictModuleDef), Fwd(module_record.ModCarrierDef)),
				Basic())

			// Phase 2 — a full triangular basis of K. K has a triangular basis b with r
			// rows and pivots p; C carries the n-element basis F of N to a basis of K,
			// so r = n, and n strictly increasing pivots below n are the identity.
			r, b, p, triangular := a.Obtain3As[Nat, Fun2[Nat, Nat, Int], Fun[Nat, Nat]](
				"choose a triangular basis of the image submodule",
				"∃r:num. ∃b:(num → num → int). ∃p:(num → num). r ≤ n ∧ integer_triangular_basis(n, K, r, b, p)",
				By(Normalized, iDef, znDef, subK, int_lattice.SubmoduleFreeTriangular.At(n, K)),
				Named("r", "b", "p"))
			T, tDef := a.LetAs[ModuleOps[Int, Fun[Nat, Int]]]("T", "restrict_module(Zn, K)")
			onT := a.Have(
				"the triangular image is a module",
				"module_on(int_ring, T)",
				By(Normalized, tDef, onZn, subK, submodule.SubmoduleModuleOn.At(integerRing, Zn, K)))
			triIndexed := a.Have(
				"the triangular vectors are an indexed basis",
				"indexed_module_basis(int_ring, T, r, b)",
				By(tDef, znDef, iDef, triangular, int_lattice.IntegerTriangularBasisDef.At(n, r, K, b, p)))
			tOps := a.Have(
				"T inherits Zn's operations and has carrier K",
				"T.add = Zn.add ∧ T.zero = Zn.zero ∧ T.smul = Zn.smul ∧ T.carrier = K",
				Simp(
					Fwd(tDef),
					Fwd(module_record.RestrictModuleDef),
					Fwd(module_record.ModAddDef),
					Fwd(module_record.ModZeroDef),
					Fwd(module_record.ModSmulDef),
					Fwd(module_record.ModCarrierDef)),
				Basic())
			pivotRows := a.Have(
				"the triangular basis has increasing positive pivots",
				"(∀i:num. i < r ⇒ p(i) < n ∧ &0 < b(i, p(i)) ∧ (∀k:num. p(i) < k ⇒ b(i, k) = &0)) ∧ "+
					"(∀i k:num. i < k ∧ k < r ⇒ p(i) < p(k))",
				By(Normalized, triangular, int_lattice.IntegerTriangularBasisDef.At(n, r, K, b, p)))
			onN := a.Have(
				"the coordinate map restricts to an injective homomorphism on N",
				"module_homomorphism(int_ring, restrict_module(V, N), Zn, C) ∧ injective_on(N, C)",
				By(
					isoParts,
					subN,
					nIn,
					module_homomorphism.HomRestrictSource.At(integerRing, V, Zn, C, N),
					functions.InjectiveOnSubset.At(C, N, a.TermAs[Set[A]]("V.carrier"))))
			transported := a.Have(
				"the coordinate map carries the basis F of N to a basis of K with n members",
				"finite(image(C, F)) ∧ module_basis(int_ring, T, image(C, F)) ∧ card(image(C, F)) = n",
				By(
					Normalized,
					onN,
					nativeNCarrier,
					native,
					finiteBases,
					kDef,
					tDef,
					linear_independence.InjectiveImageBasis.At(integerRing, nativeN, Zn, C, F)))
			triangle := a.Have(
				"the triangular vectors form a basis of K with r members",
				"finite({b(i):num → int | i:num | i < r}) ∧ "+
					"card({b(i):num → int | i:num | i < r}) = r ∧ "+
					"module_basis(int_ring, T, {b(i):num → int | i:num | i < r})",
				By(triIndexed, linear_independence.IndexedBasisImage.At(integerRing, T, r, b)))
			fullRows := a.Have(
				"two bases of K have the same size, so the triangular basis has all n rows",
				"r = n",
				By(
					onT,
					transported,
					triangle,
					int_lattice.IntegerBasisSizeUnique.At(
						T,
						a.TermAs[Set[Fun[Nat, Int]]]("image(C, F)"),
						a.TermAs[Set[Fun[Nat, Int]]]("{b(i):num → int | i:num | i < r}"))))
			fullPivotRange := a.Have(
				"all full pivots lie in the n coordinate range",
				"∀i:num. i < n ⇒ p(i) < n",
				By(Normalized, fullRows, pivotRows))
			rowParts := a.Conjuncts(
				pivotRows,
				"each row has a positive pivot below n that ends the row",
				"the pivots increase strictly")
			fullPivotClimbs := a.Have(
				"the full pivot sequence climbs at every step below n",
				"∀j:num. suc(j) < n ⇒ p(j) < p(suc(j))",
				Derive(func(c *Argument) {
					j := c.FixAs[Nat]("j")
					inside := c.Assume()
					c.Show(
						"j lies below its successor",
						ByArith(inside, fullRows, rowParts[1].At(j, c.TermAs[Nat]("suc(j)"))))
				}))
			pivotIdentity := a.Have(
				"strictly increasing full pivots are the identity",
				"∀i:num. i < n ⇒ p(i) = i",
				By(fullPivotRange, fullPivotClimbs, At(num_segment.IncreasingSelfMapIsIdentity, n, p)))
			diagonalRows := a.Have(
				"the full triangular basis has positive diagonal and zero right tails",
				"∀i:num. i < n ⇒ &0 < b(i, i) ∧ (∀k:num. i < k ⇒ b(i, k) = &0)",
				Derive(func(c *Argument) {
					i := c.FixAs[Nat]("i")
					inside := c.Assume()
					c.Show(
						"replace the pivot by its row index",
						By(Normalized, Broadcast, fullRows, inside, pivotIdentity.At(i), rowParts[0].At(i)))
				}))
			fullIndexed := a.Have(
				"b is an indexed native basis with length n",
				"indexed_module_basis(int_ring, T, n, b)",
				By(Normalized, fullRows, triIndexed))
			fullTriangular := a.Have(
				"the image submodule has a full triangular basis",
				"integer_triangular_basis(n, K, n, b, λi:num. i)",
				By(
					Normalized,
					iDef,
					znDef,
					tDef,
					fullIndexed,
					diagonalRows,
					int_lattice.IntegerTriangularBasisDef.At(n, n, K, b, a.TermAs[Fun[Nat, Nat]]("λi:num. i"))))

			// Phase 3 — the index as a determinant. The index of a full triangular
			// submodule of Zn is the product of its diagonal. S pulls b back to a basis g
			// of N, the change matrix P from e to g is the transpose of b mapped into L,
			// upper triangular, and det P is m mapped into L.
			indexProduct := a.Have(
				"the index equals the positive diagonal product",
				"m = set_fold(λi:num. λa:num. num_of_int(b(i, i)) * a, I, 1)",
				Derive(func(c *Argument) {
					nativeAdd := c.Have(
						"the native ring addition is integer addition",
						"ring_add(int_ring) = int_add",
						Simp(Fwd(int_real_lift.IntRingDef), Fwd(module_record.RingAddDef)),
						Basic())
					freeAdd := c.Have(
						"the coordinate addition is pointwise native addition",
						"Zn.add = fun_add(ring_add(int_ring))",
						Simp(Fwd(znDef), Fwd(free_module.FreeModuleRecordDef), Fwd(module_record.ModAddDef)),
						Basic())
					c.Show(
						"apply the triangular quotient index formula",
						By(
							iDef,
							znDef,
							freeAdd,
							nativeAdd,
							freeCarrier,
							fullTriangular,
							subK,
							quotientCard,
							int_lattice.TriangularIndexProduct.At(n, K, b)))
				}))
			leftInverse := a.Have(
				"summing the coordinates recovers each vector",
				"∀x:A. x ∈ V.carrier ⇒ S(C(x)) = x",
				By(
					Normalized,
					cDef,
					sumParts,
					At(
						functions.InverseOnRight.Inst(TypeBinder.BindA[Fun[Nat, Int]](), TypeBinder.BindB[A]()),
						a.TermAs[Set[Fun[Nat, Int]]]("Zn.carrier"),
						S)))
			sumOfK := a.Have(
				"S carries K back onto N",
				"image(S, K) = N",
				BySets(kDef, nIn, leftInverse))
			sumPoints := a.Have(
				"each vector of K maps into N",
				"∀u:(num → int). u ∈ K ⇒ S(u) ∈ N",
				BySets(sumOfK))
			restrictedHom := a.Have(
				"S restricts to a homomorphism from K to N",
				"module_homomorphism(int_ring, T, restrict_module(V, N), S)",
				By(
					Normalized,
					tDef,
					sumParts,
					subK,
					subN,
					sumPoints,
					module_homomorphism.HomRestrict.At(integerRing, Zn, V, S, K, N)))
			kIn := a.Have(
				"the coordinate image lies in Zn",
				"K ⊆ Zn.carrier",
				By(subK, submodule.SubmoduleSubset))
			sumInjective := a.Have(
				"S stays injective on K",
				"injective_on(K, S)",
				By(kIn, sumParts, functions.InjectiveOnSubset.At(S, K, a.TermAs[Set[Fun[Nat, Int]]]("Zn.carrier"))))
			restrictedIso := a.Have(
				"S identifies K with N as native modules",
				"module_isomorphism(int_ring, T, restrict_module(V, N), S)",
				By(
					Normalized,
					restrictedHom,
					sumInjective,
					sumOfK,
					tOps,
					nativeNCarrier,
					module_homomorphism.ModuleIsomorphismDef.At(integerRing, T, nativeN, S)))
			g, gDef := a.LetAs[Fun[Nat, A]]("g", "λi:num. S(b(i))")
			gNativeIndexed := a.Have(
				"g, the pull-back of b by S, is an indexed native basis of N",
				"indexed_module_basis(int_ring, restrict_module(V, N), n, g)",
				By(
					Normalized,
					gDef,
					restrictedIso,
					fullIndexed,
					At(
						ctx.AtTypeVars(
							indexedBasisImage,
							TypeBinder.BindA[Int](),
							TypeBinder.BindB[Fun[Nat, Int]](),
							TypeBinder.BindC[A]()),
						integerRing,
						T,
						nativeN,
						S,
						n,
						b)))
			gNativeBasis := a.Have(
				"the pulled-back family is an injectively indexed native basis",
				"injective_on(I, g) ∧ module_basis(int_ring, restrict_module(V, N), {g(i):A | i:num | i < n})",
				By(Normalized, iDef, gNativeIndexed, linear_independence.IndexedModuleBasisDef))
			gHostBasis := a.Have(
				"scalar restriction transfers this basis back to the host integer image",
				"module_basis(R, W, {g(i):A | i:num | i < n})",
				By(
					Normalized,
					gNativeBasis,
					rings,
					modules,
					rDef,
					additive,
					int_lattice.IntegerScalarRestriction.At(host, W)))
			gHostIndexed := a.Have(
				"g is an indexed R basis of N",
				"indexed_module_basis(R, W, n, g)",
				By(gNativeBasis, iDef, gHostBasis, linear_independence.IndexedModuleBasisDef.At(R, W, n, g)))
			bIn := a.Have(
				"the triangular basis vectors lie in K",
				"∀j:num. j < n ⇒ b(j) ∈ K",
				Derive(func(c *Argument) {
					basis := c.Have(
						"the indexed image of b is a basis of T",
						"module_basis(int_ring, T, {b(i):num → int | i:num | i < n})",
						By(fullIndexed, linear_independence.IndexedModuleBasisDef.At(integerRing, T, n, b)))
					carrier := c.Have(
						"that basis set lies in K",
						"{b(i):num → int | i:num | i < n} ⊆ K",
						By(
							basis,
							tOps,
							linear_independence.ModuleBasisDef.At(
								integerRing, T, c.TermAs[Set[Fun[Nat, Int]]]("{b(i):num → int | i:num | i < n}")),
							linear_independence.IndependentInCarrier.At(
								integerRing, T, c.TermAs[Set[Fun[Nat, Int]]]("{b(i):num → int | i:num | i < n}"))))
					c.Show(
						"each index supplies a member of K",
						BySets(carrier))
				}))
			gCoordinates := a.Have(
				"the coordinates of g are the chosen triangular vectors",
				"∀j:num. j < n ⇒ C(g(j)) = b(j)",
				Simp(Fwd(gDef), Fwd(cDef)),
				BySets(
					Normalized,
					bIn,
					kIn,
					sumParts,
					At(
						functions.InverseOnLeft.Inst(TypeBinder.BindA[Fun[Nat, Int]](), TypeBinder.BindB[A]()),
						a.TermAs[Set[Fun[Nat, Int]]]("Zn.carrier"),
						S)))
			gIn := a.Have(
				"the pulled-back basis lies in N and V",
				"∀j:num. j < n ⇒ g(j) ∈ N ∧ g(j) ∈ V.carrier",
				BySets(Normalized, gDef, sumPoints, bIn, nIn))
			uCarrier := a.Have(
				"the host restriction has carrier M",
				"U.carrier = M",
				Simp(Fwd(uDef), Fwd(module_record.RestrictModuleDef), Fwd(module_record.ModCarrierDef)),
				Basic())
			gInU := a.Have(
				"g also lies in the ambient lattice module",
				"∀j:num. j < n ⇒ g(j) ∈ U.carrier",
				By(Normalized, gIn, uCarrier, additive))
			hostCoordinates := a.Have(
				"host coordinates are integer images of native coordinates",
				Statement{
					Binders: "∀j:num.",
					Hypotheses: []string{
						"j < n",
					},
					Conclusion: "module_basis_coordinates(R, U, E, g(j)) = " +
						"λx:A. integer_map(field_ring(L), module_basis_coordinates(int_ring, V, E, g(j), x))",
				},
				By(
					Normalized,
					rings,
					rDef,
					vDef,
					modules,
					finiteBases,
					bases,
					gInU,
					At(ctx.AtTypeVars(nativeCoordinates, TypeBinder.BindA[A](), TypeBinder.BindB[A]()), host, U, E)))
			coordinates := a.Have(
				"below n the coordinate map reads the basis coordinates, and it vanishes from n on",
				Statement{
					Binders: "∀v:A.",
					Hypotheses: []string{
						"v ∈ V.carrier",
					},
					Conclusion: "C(v) = λi:num. COND(i < n, module_basis_coordinates(int_ring, V, E, v, e(i)), 0)",
				},
				Derive(func(c *Argument) {
					v := c.FixAs[A]("v")
					inV := c.Assume()
					w, vectorDef := c.LetAs[Fun[Nat, Int]](
						"w", "λi:num. COND(i < n, module_basis_coordinates(int_ring, V, E, v, e(i)), 0)")
					bounded := c.Have(
						"w vanishes from n on",
						"fun_support(int_of_num(0), w) ⊆ I",
						BySets(vectorDef, iDef))
					supported := c.Have(
						"w is finitely supported below n",
						"w ∈ Zn.carrier",
						Simp(Fwd(freeCarrier), Fwd(function_module.FiniteSuppMember)),
						BySets(
							bounded,
							finiteI,
							finite_set.FiniteSubset.At(c.TermAs[Set[Nat]]("fun_support(int_of_num(0), w)"), I)))
					expansion := c.Have(
						"summing w against e recovers v",
						"S(w) = v",
						CalcEq(
							Leg(
								c.TermAs[A](
									"module_sum(V.add, "+
										"    V.zero, "+
										"    I, "+
										"    λi:num. V.smul(module_basis_coordinates(int_ring, V, E, v, e(i)), e(i)))"),
								"below n the vector w holds the basis coordinates",
								BySets(
									sDef,
									vectorDef,
									iDef,
									module.ModuleSumCongruence.At(
										c.TermAs[Op[A]]("V.add"),
										c.TermAs[A]("V.zero"),
										I,
										c.TermAs[Fun[Nat, A]]("λi:num. V.smul(w(i), e(i))"),
										c.TermAs[Fun[Nat, A]]("λi:num. V.smul(module_basis_coordinates(int_ring, V, E, v, e(i)), e(i))")))),
							FinalLeg(
								"the indexed basis expansion is v",
								By(
									native,
									nativeIndexed,
									inV,
									images,
									iDef,
									module_dimension.IndexedBasisExpansion.At(integerRing, V, n, e, v)))))
					c.Show(
						"the inverse of the coordinate sum returns w",
						By(
							Normalized,
							cDef,
							vectorDef,
							supported,
							expansion,
							sumParts,
							functions.InverseOnLeft.At(c.TermAs[Set[Fun[Nat, Int]]]("Zn.carrier"), S, w)))
				}))
			coordinateEntries := a.Have(
				"the ambient change matrix contains the mapped triangular entries",
				Statement{
					Binders: "∀i j:num.",
					Hypotheses: []string{
						"i < n",
						"j < n",
					},
					Conclusion: "module_basis_coordinates(R, U, E, g(j), e(i)) = integer_map(field_ring(L), b(j, i))",
				},
				Derive(func(c *Argument) {
					c.FixAs[Nat]("i")
					j := c.FixAs[Nat]("j")
					inside := c.Assume()
					nativeEntries := c.Have(
						"b(j) lists the native coordinates of g(j)",
						"b(j) = λk:num. COND(k < n, module_basis_coordinates(int_ring, V, E, g(j), e(k)), int_of_num(0))",
						By(inside, gIn.At(j), gCoordinates.At(j), coordinates.At(c.TermAs[A]("g(j)"))))
					c.Show(
						"the host coordinate is the integer image of the native one",
						By(Normalized, inside, nativeEntries, hostCoordinates.At(j)))
				}))
			P, pDef := a.LetAs[Fun2[Nat, Nat, A]]("P", "basis_change_matrix(R, U, n, e, g)")
			entries := a.Have(
				"the change matrix is the transpose of the mapped triangular basis",
				"∀i j:num. P(i, j) = COND(i < n ∧ j < n, integer_map(field_ring(L), b(j, i)), R.zero)",
				By(
					Normalized,
					pDef,
					eDef,
					coordinateEntries,
					At(
						linear_determinant.BasisChangeMatrixDef.Inst(TypeBinder.BindA[A](), TypeBinder.BindB[A]()),
						R,
						U,
						n,
						e,
						g)))
			rOps := a.Have(
				"R keeps the field's zero, one and product, with the integer image as carrier",
				"R.zero = field_ring(L).zero ∧ "+
					"R.one = field_ring(L).one ∧ "+
					"R.mul = field_ring(L).mul ∧ "+
					"R.carrier = integer_image(field_ring(L))",
				Simp(
					Fwd(rDef),
					Fwd(module_record.RestrictRingDef),
					Fwd(module_record.RingZeroDef),
					Fwd(module_record.RingOneDef),
					Fwd(module_record.RingMulDef),
					Fwd(module_record.RingCarrierDef)),
				Basic())
			mappedScalars := a.Have(
				"integer images are R scalars",
				"∀z:int. integer_map(field_ring(L), z) ∈ R.carrier",
				BySets(rOps, characteristic_zero.IntegerImageDef))
			mappedZero := a.Have(
				"the integer map sends zero to R.zero",
				"integer_map(field_ring(L), 0) = R.zero",
				rOps.Simp(
					Fwd(field.FieldRingDef),
					Fwd(module_record.RingZeroDef),
					Fwd(module_record.RingOneDef),
					Fwd(module_record.RingMulDef)),
				By(Normalized, rOps, rings, characteristic_zero.IntegerMapHom.At(host)))
			ringR := a.Have(
				"R is a commutative ring",
				"comm_ring_on(R)",
				By(rings))
			scalarEntries := a.Have(
				"every entry lies in the integer-image ring",
				"∀i j:num. P(i, j) ∈ R.carrier",
				Derive(func(c *Argument) {
					i, j := c.FixAs[Nat]("i"), c.FixAs[Nat]("j")
					c.Cases(c.TermAs[Bool]("i < n ∧ j < n"))
					c.When(
						"inside the square an entry is an integer image",
						func(d *Argument, inside Fact) {
							d.Show(
								"which is an R scalar",
								By(Normalized, entries.At(i, j), inside, mappedScalars.At(d.TermAs[Int]("b(j, i)"))))
						})
					c.Otherwise(
						"outside it an entry is zero",
						func(d *Argument, outside Fact) {
							d.Show(
								"which is an R scalar",
								By(Normalized, entries.At(i, j), outside, comm_ring.ZeroIn.Read(ringR)))
						})
				}))
			padding := a.Have(
				"entries past the square are zero",
				"∀i j:num. n ≤ i ∨ n ≤ j ⇒ P(i, j) = R.zero",
				Derive(func(c *Argument) {
					i, j := c.FixAs[Nat]("i"), c.FixAs[Nat]("j")
					past := c.Assume()
					c.Show(
						"an entry past the square is the zero padding",
						By(entries.At(i, j), past, nat_order.NotLessThan.At(i, n), nat_order.NotLessThan.At(j, n)))
				}))
			matrixP := a.Have(
				"P is a matrix over R",
				"matrix_over(R, n, P)",
				By(scalarEntries, padding, determinant.MatrixOverEntries.Read(ringR).At(n, P)))
			upper := a.Have(
				"P is upper triangular",
				"∀i j:num. j < i ∧ i < n ⇒ P(i, j) = R.zero",
				Derive(func(c *Argument) {
					i, j := c.FixAs[Nat]("i"), c.FixAs[Nat]("j")
					inside := c.Assume()
					jIn := c.Have(
						"the column is in range",
						"j < n",
						ByArith(inside))
					zero := c.Have(
						"the corresponding triangular row entry is zero",
						"b(j, i) = &0",
						By(Normalized, diagonalRows.At(j), jIn, inside))
					c.Show(
						"the mapped entry vanishes",
						By(Normalized, entries.At(i, j), zero, jIn, inside, mappedZero))
				}))
			triangularDet := a.Have(
				"the determinant of P is its diagonal product",
				"determinant(R, n, P) = module_sum(R.mul, R.one, I, λi:num. P(i, i))",
				By(rings, matrixP, upper, iDef, determinant.DeterminantTriangular.At(R, n, P)))
			diagonal, diagonalDef := a.LetAs[Fun[Nat, Nat]]("d", "λi:num. COND(i < n, num_of_int(b(i, i)), 0)")
			diagonalLift := a.Have(
				"the positive diagonal entries are natural integer lifts",
				"∀i:num. i < n ⇒ int_of_num(d(i)) = b(i, i)",
				Derive(func(c *Argument) {
					i := c.FixAs[Nat]("i")
					inside := c.Assume()
					c.Do(Simp(Fwd(diagonalDef), Fwd(inside)))
					nonnegative := c.Have(
						"the positive pivot is nonnegative",
						"&0 ≤ b(i, i)",
						ByArith(diagonalRows.At(i), inside))
					c.Show(
						"num_of_int inverts the nonnegative integer lift",
						By(nonnegative, int_embed.NumOfIntSection.At(c.TermAs[Int]("b(i, i)"))))
				}))
			mappedDiagonal := a.Have(
				"every diagonal entry is the image of d",
				"∀i:num. P(i, i) = integer_map(field_ring(L), int_of_num(d(i)))",
				Derive(func(c *Argument) {
					i := c.FixAs[Nat]("i")
					c.Cases(c.TermAs[Bool]("i < n"))
					c.When(
						"within the diagonal",
						func(d *Argument, inside Fact) {
							d.Show(
								"map the positive pivot",
								By(Normalized, inside, diagonalLift.At(i), entries.At(i, i)))
						})
					c.Otherwise(
						"outside the diagonal",
						func(d *Argument, outside Fact) {
							d.Show(
								"both padded values are zero",
								Simp(Fwd(diagonalDef), Fwd(outside)),
								By(Normalized, outside, mappedZero, entries.At(i, i)))
						})
				}))
			agreeingSteps := a.Have(
				"the two natural product steps agree on I",
				"∀i:num. i ∈ I ⇒ (λa:num. num_of_int(b(i, i)) * a) = λa:num. d(i) * a",
				BySets(Normalized, iDef, diagonalDef))
			naturalProduct := a.Have(
				"the natural diagonal product is the index",
				"m = set_fold(λi:num. λa:num. d(i) * a, I, 1)",
				Derive(func(c *Argument) {
					law := c.Simplified(cardinality.FoldOfAgreeingSteps.Inst(
						TypeBinder.BindA[Nat](), TypeBinder.BindB[Nat]()).At(
						I,
						c.TermAs[Op[Nat]]("λi:num. λa:num. num_of_int(b(i, i)) * a"),
						c.TermAs[Op[Nat]]("λi:num. λa:num. d(i) * a"),
						c.TermAs[Nat]("1")))
					c.Show(
						"the two folds take the same step at every index of I, so they are equal",
						By(
							indexProduct,
							finiteI,
							agreeingSteps,
							law,
							At(naturalProductStepsCommute, c.TermAs[Fun[Nat, Nat]]("λi:num. num_of_int(b(i, i))")),
							At(naturalProductStepsCommute, diagonal)))
				}))
			hostRing := a.Have(
				"the host field ring is commutative",
				"comm_ring_on(field_ring(L))",
				By(rings))
			mappedProduct := a.Have(
				"mapping the natural diagonal product gives the host product",
				"module_sum(L.mul, L.one, I, λi:num. integer_map(field_ring(L), int_of_num(d(i)))) = "+
					"integer_map(field_ring(L), int_of_num(m))",
				By(
					hostRing,
					finiteI,
					naturalProduct,
					At(ctx.AtTypeVars(integerMapNaturalProduct, TypeBinder.BindA[A]()), host, I, diagonal)))
			hostProducts := a.Have(
				"R multiplication and one are the host field operations",
				"R.mul = L.mul ∧ R.one = L.one",
				Simp(
					Fwd(rDef),
					Fwd(module_record.RestrictRingDef),
					Fwd(field.FieldRingDef),
					Fwd(module_record.RingMulDef),
					Fwd(module_record.RingOneDef)),
				Basic())
			determinantP := a.Have(
				"the triangular change determinant is the integer image of the index",
				"determinant(R, n, P) = integer_map(field_ring(L), m)",
				triangularDet.Simp(Fwd(hostProducts), Fwd(mappedDiagonal)),
				By(triangularDet, mappedProduct))

			// Phase 4 — from g to f. The change from g to f is an integer change of basis,
			// of determinant ±1; the change from e to f is the product of the two, so its
			// determinant D is ±μ, where μ is m mapped into L, and its rational value is ±m.
			unitChange := a.Have(
				"the change from g to f is a matrix over R of determinant ±1",
				"matrix_over(R, n, basis_change_matrix(R, W, n, g, f)) ∧ "+
					"(determinant(R, n, basis_change_matrix(R, W, n, g, f)) = L.one ∨ "+
					"    determinant(R, n, basis_change_matrix(R, W, n, g, f)) = L.neg(L.one))",
				By(L, rDef, rings, modules, gHostIndexed, given, IntegerBasisChangeDetUnit.Read(L).At(W, n, g, f)))
			wCarrier := a.Have(
				"W has carrier N",
				"W.carrier = N",
				Simp(Fwd(wDef), Fwd(module_record.RestrictModuleDef), Fwd(module_record.ModCarrierDef)),
				Basic())
			fCarrier := a.Have(
				"the f basis set lies in N",
				"F ⊆ N",
				By(
					Normalized,
					wCarrier,
					bases,
					linear_independence.ModuleBasisDef.At(R, W, F),
					linear_independence.IndependentInCarrier.At(R, W, F)))
			fPoints := a.Have(
				"each f index gives a vector of N",
				"∀j:num. j < n ⇒ f(j) ∈ N",
				BySets(fCarrier, fDef))
			composition := a.Have(
				"the two basis changes compose to the original one",
				"matrix_product(R, n, P, basis_change_matrix(R, W, n, g, f)) = basis_change_matrix(R, U, n, e, f)",
				By(
					Normalized,
					pDef,
					additive,
					modules,
					given,
					gHostIndexed,
					fPoints,
					linear_determinant.BasisChangeCompose.At(R, U, N, n, e, g, f)))
			secondMatrix := a.TermAs[Fun2[Nat, Nat, A]]("basis_change_matrix(R, W, n, g, f)")
			determinantProduct := a.Have(
				"determinants multiply under basis-change composition",
				"determinant(R, n, basis_change_matrix(R, U, n, e, f)) = "+
					"R.mul(determinant(R, n, P), determinant(R, n, basis_change_matrix(R, W, n, g, f)))",
				By(
					composition,
					matrixP,
					unitChange,
					determinant.DeterminantMultiplicative.Read(ringR).AsFact().At(n, P, secondMatrix)))
			indexImage, indexImageDef := a.LetAs[A]("μ", "integer_map(field_ring(L), m)")
			a.Let("D", a.TermAs[A]("determinant(R, n, basis_change_matrix(R, U, n, e, f))"))
			indexImageIn := a.Have(
				"the integer image of the index lies in the host field",
				"μ ∈ L.carrier",
				BySets(characteristic_zero.IntegerMapHom.Read(hostRing), indexImageDef))
			determinantSign := a.Have(
				"the original determinant differs by at most a sign",
				"D = μ ∨ D = L.neg(μ)",
				determinantProduct.Simp(Fwd(hostProducts), Fwd(determinantP)),
				Derive(func(c *Argument) {
					unitsIn := c.Have(
						"both unit signs belong to the field",
						"L.one ∈ L.carrier ∧ L.neg(L.one) ∈ L.carrier",
						By(
							comm_ring.OneIn.Read(hostRing),
							comm_ring.NegIn.Read(hostRing).AsFact().At(c.TermAs[A]("L.one"))))
					secondIn := c.Have(
						"the second basis-change determinant lies in the field",
						"determinant(R, n, basis_change_matrix(R, W, n, g, f)) ∈ L.carrier",
						By(unitsIn, unitChange))
					determinantIn := c.Have(
						"the original determinant lies in the field",
						"D ∈ L.carrier",
						By(
							indexImageIn,
							secondIn,
							determinantProduct,
							comm_ring.MulIn.Read(hostRing).AsFact().At(
								indexImage, c.TermAs[A]("determinant(R, n, basis_change_matrix(R, W, n, g, f))"))))
					c.Show(
						"multiplication by a unit sign changes only the sign",
						ByArith(Normalized, L, indexImageIn, determinantIn, secondIn, unitChange, determinantProduct))
				}))
			mapNeg := a.Have(
				"the native integer embedding preserves negation",
				"∀z:int. integer_map(field_ring(L), -z) = L.neg(integer_map(field_ring(L), z))",
				By(characteristic_zero.IntegerMapHom.Read(hostRing)))
			mapSigns := a.Have(
				"the two index signs are rational images",
				"rational_map(L, real_of_num(m)) = μ ∧ rational_map(L, -real_of_num(m)) = L.neg(μ)",
				By(
					Normalized,
					indexImageDef,
					rings,
					characteristic_zero.RationalEmbedding.Read(L),
					mapNeg.At(a.TermAs[Int]("m")),
					int_construction.OfNumBridge.At(m),
					int_construction.NegBridge.At(a.TermAs[Int]("m"))))
			rationalSigns := a.Have(
				"both signed natural values are rational",
				"rational(real_of_num(m)) ∧ rational(-real_of_num(m))",
				By(rational.OfNumRational.At(m), rational.RationalNeg.At(a.TermAs[Real]("real_of_num(m)"))))
			values := a.Have(
				"rational_value recovers the two signed indices",
				"rational_value(L, μ) = real_of_num(m) ∧ rational_value(L, L.neg(μ)) = -real_of_num(m)",
				By(Normalized, rationalSigns, mapSigns, rings, characteristic_zero.RationalEmbedding.Read(L)))
			valueSign := a.Have(
				"the determinant value is the signed index",
				"rational_value(L, D) = real_of_num(m) ∨ rational_value(L, D) = -real_of_num(m)",
				By(Normalized, determinantSign, values))
			absolute := a.Have(
				"absolute value removes the determinant sign",
				"real_abs(rational_value(L, D)) = real_of_num(m)",
				By(
					Normalized,
					valueSign,
					real_sgn_abs.AbsEven.At(a.TermAs[Real]("real_of_num(m)")),
					real_sgn_abs.AbsOfNum.At(m)))
			hostIndex := a.Have(
				"the native index counts the original additive cosets",
				"m = card(left_cosets(L.add, M, N))",
				By(Normalized, mDef, additive))
			a.Show(
				"the finite quotient index is the absolute rational determinant",
				By(Normalized, finiteHost, absolute, hostIndex))
		})

	}),
})}
