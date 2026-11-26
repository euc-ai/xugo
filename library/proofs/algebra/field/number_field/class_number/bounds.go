package class_number

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_extension"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_norm"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/number_field/integral_closure"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/number_field/lattice_determinant"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/number_field/number_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/number_field/ring_of_integers"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/int_lattice"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/linear_determinant"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/linear_independence"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/characteristic_zero"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/real/real_pow"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/vector/determinant"
	"github.com/euc-ai/xugo/library/registry"
)

// structureConstantBoundSpec — the structure-constant bound is at least one
// and bounds every sum over the first index of absolute structure constants:
// those finitely many sums, with one adjoined, lie in an initial segment, so
// the set has the maximum the definition chooses.
var structureConstantBoundSpec = structureConstantBoundSpecThm{family.Add(registry.ProofEntry{
	Name: "structureConstantBoundSpec",
	Key:  "prop_80f5efab8e18aa08",
	Build: family.Theorem("∀R:ring_ops(A). ∀n:num. ∀e:(num → A). "+
		"    1 ≤ structure_constant_bound(R, n, e) ∧ "+
		"    (∀j k:num. "+
		"        j < n ∧ k < n ⇒ "+
		"        Σ_{i<n} num_of_int(|integral_structure_constant(R, n, e, i, j, k)|) ≤ "+
		"        structure_constant_bound(R, n, e))",
		func(a *Argument, R *Expr[RingOps[A]], n *Expr[Nat], e *Arrow[Nat, A]) {
			s, sDef := a.LetAs[Set[Nat]]("s", "{i:num | i < n}")
			T, sumsDef := a.LetAs[Set[Nat]](
				"T",
				"{nat_sum(s, λi:num. num_of_int(int_abs(integral_structure_constant(R, n, e, i, j, k)))) | "+
					"    j:num, "+
					"    k:num | "+
					"    j < n ∧ k < n}")
			U, setDef := a.LetAs[Set[Nat]]("U", "{1} ∪ T")
			one := a.TermAs[Nat]("1")
			finiteSegment := a.Have(
				"the strict index segment is finite",
				"finite(s)",
				By(sDef, num_segment.FiniteBelowStrict.At(n)))
			membershipForm := a.Have(
				"the double index restriction is membership in the two finite segments",
				"T = "+
					"{nat_sum(s, λi:num. num_of_int(int_abs(integral_structure_constant(R, n, e, i, j, k)))) | "+
					"    j:num, "+
					"    k:num | "+
					"    j ∈ s ∧ k ∈ s}",
				BySets(sumsDef, sDef))
			finiteSums := a.Have(
				"the sums over the first index form a finite set",
				"finite(T)",
				By(
					membershipForm,
					finiteSegment,
					finite_set.FiniteProductDependent.At(
						a.TermAs[Fun[Nat, Fun[Nat, Nat]]](
							"λj:num. λk:num. "+
								"    nat_sum(s, λi:num. num_of_int(int_abs(integral_structure_constant(R, n, e, i, j, k))))"),
						s,
						a.TermAs[Fun[Nat, Set[Nat]]]("λj:num. s"))))
			finiteNonempty := a.Have(
				"adjoining one makes the finite set nonempty",
				"finite(U) ∧ 1 ∈ U",
				BySets(
					Normalized,
					setDef,
					finiteSums,
					finite_set.FiniteSing.At(one),
					finite_set.FiniteUnion.At(a.TermAs[Set[Nat]]("{1}"), T)))
			N, bounded := a.ObtainAs[Nat](
				"a finite natural set lies in an initial segment",
				"∃N:num. U ⊆ 0 .. N",
				By(finiteNonempty, num_segment.FiniteIffBounded.At(U)),
				Named("N"))
			upperBound := a.Have(
				"the segment endpoint bounds every member",
				"∀x:num. x ∈ U ⇒ x ≤ N",
				BySets(bounded, num_segment.IntervalDef.At(a.TermAs[Nat]("0"), N)))
			nonempty := a.Have(
				"one witnesses nonemptiness",
				"∃x:num. x ∈ U",
				Witness(one),
				By(finiteNonempty))
			upperExists := a.Have(
				"the segment endpoint witnesses an upper bound",
				"∃N:num. ∀x:num. x ∈ U ⇒ x ≤ N",
				Witness(N),
				By(upperBound))
			maximum := a.Have(
				"a bounded nonempty natural set has a maximum",
				"∃m:num. m ∈ U ∧ (∀x:num. x ∈ U ⇒ x ≤ m)",
				By(nonempty, upperExists, nat_order.MaximumExists.At(a.TermAs[Set[Nat]]("λx:num. x ∈ U"))))
			sumsIn := a.Have(
				"each sum over the first index at valid j and k belongs to the finite set",
				Statement{
					Binders: "∀j k:num.",
					Hypotheses: []string{
						"j < n",
						"k < n",
					},
					Conclusion: "nat_sum(s, " +
						"    λi:num. num_of_int(int_abs(integral_structure_constant(R, n, e, i, j, k)))) ∈ " +
						"U",
				},
				BySets(setDef, sumsDef))
			a.Show(
				"the defining maximum bounds one and every sum over the first index",
				Unfold(structureConstantBoundDef),
				BySets(HilbertDenoted, maximum, setDef, sumsDef, sDef, sumsIn))
		}),
})}

// fieldNormCoordinateBound estimates the multiplication matrix in a common
// integral and rational basis. The sums over the first index of absolute
// structure constants bound its entries; the determinant estimate gives the
// norm bound.
var fieldNormCoordinateBound = fieldNormCoordinateBoundThm{family.Add(registry.ProofEntry{
	Name: "fieldNormCoordinateBound",
	Key:  "prop_9046601467dcb8b7",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀n H:num. ∀e:(num → A). ∀a:A.",
		Hypotheses: []string{
			"number_field(L)",
			"integral_basis(field_ring(L), n, e)",
			"a ∈ «O»",
			"∀i:num. " +
				"    i < n ⇒ " +
				"    int_abs(integer_value(field_ring(L), " +
				"            module_basis_coordinates( " +
				"                restrict_ring(field_ring(L), integer_image(field_ring(L))), " +
				"                restrict_module(regular_module(field_ring(L)), «O»), " +
				"                {e(j) | j:num | j < n}, " +
				"                a, " +
				"                e(i)))) ≤ " +
				"    H",
		},
		Conclusion: "real_abs(rational_value(L, field_norm(field_ring(L), rational_image(L), a))) ≤ " +
			"real_of_num(class_number_bound(field_ring(L), n, e) * H ^ n)",
	}, func(
		arg *Argument,
		L field.FieldFact[on.L],
		n, H *Expr[Nat],
		e *Arrow[Nat, A],
		a *Expr[A],
		given Fact,
	) {
		fieldL := arg.TermAs[field.FieldOps[A]]("L")
		R := arg.TermAs[RingOps[A]]("field_ring(L)")
		O := arg.TermAs[Set[A]]("«O»")
		Q := arg.TermAs[Set[A]]("rational_image(L)")
		RZ := arg.TermAs[RingOps[A]]("restrict_ring(field_ring(L), integer_image(field_ring(L)))")
		RQ := arg.TermAs[RingOps[A]]("restrict_ring(field_ring(L), rational_image(L))")
		M := arg.TermAs[module_record.ModuleOps[A, A]]("regular_module(field_ring(L))")
		MO := arg.TermAs[module_record.ModuleOps[A, A]](
			"restrict_module(regular_module(field_ring(L)), «O»)")
		s, sDef := arg.LetAs[Set[Nat]]("s", "{i:num | i < n}")
		E, basisDef := arg.LetAs[Set[A]]("E", "{e(i):A | i:num | i < n}")
		scalars := arg.Conjuncts(
			GroupPremises(L, given, number_field.NumberFieldScalars.At(fieldL)),
			"L has characteristic zero",
			"its rational image is a subfield",
			"the integer image lies in the rational image",
			"the integer image is a commutative ring",
			"and a principal ideal domain",
			"L is a module over the integer image",
			"and over the rational image")
		charZero, rationalSubfield, moduleQ := scalars[0], scalars[1], scalars[6]
		fullLattice := arg.Have(
			"the integer ring is a full integer lattice",
			"full_integer_lattice(L, «O»)",
			By(given, ring_of_integers.RingOfIntegersFreeRankN.Read(L)))
		indexedZ := arg.Have(
			"the integral basis is an indexed integer-module basis",
			"indexed_module_basis(restrict_ring(field_ring(L), integer_image(field_ring(L))), "+
				"    restrict_module(regular_module(field_ring(L)), «O»), "+
				"    n, "+
				"    e)",
			By(given, ring_of_integers.IntegralBasisDef.At(R, n, e)))
		basisZ := arg.Have(
			"the finite integral basis has distinct indexed vectors",
			"finite(E) ∧ "+
				"module_basis(restrict_ring(field_ring(L), integer_image(field_ring(L))), "+
				"    restrict_module(regular_module(field_ring(L)), «O»), "+
				"    E) ∧ "+
				"injective_on(s, e)",
			By(indexedZ, basisDef, sDef, linear_independence.IndexedBasisImage.At(RZ, MO, n, e)))
		rational := arg.Conjuncts(
			GroupPremises(
				scalars[0], fullLattice, basisZ, int_lattice.FullLatticeBasisRational.Read(L).At(O, E)),
			"the same integral basis is a rational basis of the field",
			"rational and integral coordinates agree on the integer ring")
		basisQ, coordinateRestriction := rational[0], rational[1]
		indexedQ := arg.Have(
			"the original sequence is an indexed rational basis",
			"indexed_module_basis(restrict_ring(field_ring(L), rational_image(L)), "+
				"    regular_module(field_ring(L)), "+
				"    n, "+
				"    e)",
			By(basisQ, basisZ, basisDef, sDef, linear_independence.IndexedModuleBasisDef.At(RQ, M, n, e)))
		rationalRing := arg.Have(
			"the rational image, a subfield, is a subring of the field",
			"subring(field_ring(L), rational_image(L))",
			By(rationalSubfield, field.SubfieldSubring.Read(L).At(Q)))
		rationalRingOn := arg.Have(
			"so it is a commutative ring under the field's operations",
			"comm_ring_on(restrict_ring(field_ring(L), rational_image(L)))",
			By(rationalRing, comm_ring.SubringRingOn.Read(field.RingOn.Read(L)).At(Q)))
		integersInField := arg.Have(
			"integral vectors lie in the field",
			"«O» ⊆ L.carrier",
			By(given, integral_closure.IntegralClosureSubring.Read(L), comm_ring.SubringSubset.At(R, O)))
		moduleZ := arg.Conjuncts(
			GroupPremises(L, given, ring_of_integers.RingOfIntegersIntegerModule.At(fieldL)),
			"the integer ring is a submodule of the field over integer scalars",
			"it is a module over integer scalars")[1]
		basisIn := arg.Have(
			"the integral basis lies in the integer ring",
			"E ⊆ «O»",
			BySets(basisZ, linear_independence.BasisInCarrier.At(RZ, MO, E)))
		coordinateImages := arg.Have(
			"rational coordinates of integral vectors are the images of their integer values",
			Statement{
				Binders: "∀v z:A.",
				Hypotheses: []string{
					"v ∈ «O»",
					"z ∈ E",
				},
				Conclusion: "integer_map(field_ring(L), " +
					"    integer_value(field_ring(L), " +
					"        module_basis_coordinates(restrict_ring(field_ring(L), integer_image(field_ring(L))), " +
					"            restrict_module(regular_module(field_ring(L)), «O»), " +
					"            E, " +
					"            v, " +
					"            z))) = " +
					"module_basis_coordinates(restrict_ring(field_ring(L), rational_image(L)), " +
					"    regular_module(field_ring(L)), " +
					"    E, " +
					"    v, " +
					"    z)",
			},
			Derive(func(b *Argument) {
				v := b.FixAs[A]("v")
				b.FixAs[A]("z")
				inBasis := b.Assume()
				coordinate := b.TermAs[A](
					"module_basis_coordinates(restrict_ring(field_ring(L), integer_image(field_ring(L))), " +
						"    restrict_module(regular_module(field_ring(L)), «O»), " +
						"    E, " +
						"    v, " +
						"    z)")
				scalar := b.Have(
					"the chosen integral coordinate lies in the integer scalar carrier",
					"module_basis_coordinates(restrict_ring(field_ring(L), integer_image(field_ring(L))), "+
						"    restrict_module(regular_module(field_ring(L)), «O»), "+
						"    E, "+
						"    v, "+
						"    z) ∈ "+
						"restrict_ring(field_ring(L), integer_image(field_ring(L))).carrier",
					By(basisZ, inBasis, module_dimension.BasisCoordinatesSpec.Read(moduleZ).AsFact().At(E, v)))
				carrier := b.Have(
					"the restricted coefficient carrier is the integer image",
					"restrict_ring(field_ring(L), integer_image(field_ring(L))).carrier = integer_image(field_ring(L))",
					Simp(Fwd(module_record.RestrictRingDef), Fwd(module_record.RingCarrierDef)),
					Refl())
				b.Show(
					"recover the coordinate and transport it to the rational basis",
					By(
						Normalized,
						scalar,
						carrier,
						coordinateRestriction,
						inBasis,
						characteristic_zero.IntegerValueRightInverse.At(R, coordinate)))
			}))
		c, coeffDef := arg.LetAs[Fun[Nat, Int]](
			"c",
			"λi:num. "+
				"    integer_value(field_ring(L), "+
				"        module_basis_coordinates(restrict_ring(field_ring(L), integer_image(field_ring(L))), "+
				"            restrict_module(regular_module(field_ring(L)), «O»), "+
				"            E, "+
				"            a, "+
				"            e(i)))")
		vectorsIn := arg.Have(
			"a and the indexed basis vectors lie in the field",
			"a ∈ L.carrier ∧ (∀i:num. i ∈ s ⇒ e(i) ∈ «O» ∧ e(i) ∈ L.carrier ∧ e(i) ∈ E)",
			BySets(given, basisIn, basisDef, sDef, integersInField))
		coefficients := arg.Have(
			"the integer coordinates retain the given bounds and give rational coordinates",
			Statement{
				Binders: "∀i:num.",
				Hypotheses: []string{
					"i ∈ s",
				},
				Conclusion: "int_abs(c(i)) ≤ H ∧ " +
					"integer_map(field_ring(L), c(i)) = " +
					"module_basis_coordinates(restrict_ring(field_ring(L), rational_image(L)), " +
					"    regular_module(field_ring(L)), " +
					"    E, " +
					"    a, " +
					"    e(i))",
			},
			BySets(Normalized, coeffDef, given, sDef, vectorsIn, coordinateImages))
		mulMonoid := arg.Have(
			"field multiplication is a commutative monoid on its carrier",
			"comm_monoid_on(L.carrier, L.mul, L.one)",
			By(field.RingOn.Read(L), comm_ring.MulMonoidOn.Inst[A]().At(R)))
		productsIntegral := arg.Have(
			"products of integral basis vectors are integral",
			"∀i j:num. i ∈ s ∧ j ∈ s ⇒ L.mul(e(i), e(j)) ∈ «O»",
			By(vectorsIn, given, integral_closure.IntegralMul.Read(L)))
		functionalExpansion := arg.Have(
			"a multiplication coordinate expands over the rational basis",
			Statement{
				Binders: "∀j k:num.",
				Hypotheses: []string{
					"j ∈ s",
					"k ∈ s",
				},
				Conclusion: "module_basis_coordinates(restrict_ring(field_ring(L), rational_image(L)), " +
					"    regular_module(field_ring(L)), " +
					"    E, " +
					"    L.mul(e(j), a), " +
					"    e(k)) = " +
					"module_sum(L.add, " +
					"    L.zero, " +
					"    s, " +
					"    λi:num. " +
					"        L.mul(module_basis_coordinates(restrict_ring(field_ring(L), rational_image(L)), " +
					"                regular_module(field_ring(L)), " +
					"                E, " +
					"                L.mul(e(j), e(i)), " +
					"                e(k)), " +
					"            module_basis_coordinates(restrict_ring(field_ring(L), rational_image(L)), " +
					"                regular_module(field_ring(L)), " +
					"                E, " +
					"                a, " +
					"                e(i))))",
			},
			Derive(func(b *Argument) {
				b.FixAs[Nat]("j")
				k := b.FixAs[Nat]("k")
				indices := b.Assume()
				leftScale := b.TermAs[Fun[A, A]]("L.mul(e(j))")
				scaling := b.Have(
					"multiplication by the indexed vector is rational linear",
					"module_homomorphism(restrict_ring(field_ring(L), rational_image(L)), "+
						"    regular_module(field_ring(L)), "+
						"    regular_module(field_ring(L)), "+
						"    L.mul(e(j)))",
					By(
						vectorsIn,
						indices,
						rationalRing,
						field_extension.ScaleLinear.Read(L).AsFact().At(Q, b.TermAs[A]("e(j)"))))
				b.Show(
					"the indexed functional expansion gives the coordinate sum",
					By(
						sDef,
						basisDef,
						vectorsIn,
						indices,
						basisZ,
						basisQ,
						indexedQ,
						scaling,
						moduleQ,
						module_dimension.IndexedImageCoordinates.At(RQ, M, E, n, e, leftScale, a, e.Apply(k))))
			}))
		commutes := arg.Have(
			"field elements commute under multiplication",
			"∀x y:A. x ∈ L.carrier ∧ y ∈ L.carrier ⇒ L.mul(x, y) = L.mul(y, x)",
			By(comm_monoid.CommOn.Read(mulMonoid)))
		structureImages := arg.Have(
			"the structure constants give the rational coordinates of basis products",
			Statement{
				Binders: "∀i j k:num.",
				Hypotheses: []string{
					"i ∈ s",
					"j ∈ s",
					"k ∈ s",
				},
				Conclusion: "integer_map(field_ring(L), " +
					"    integral_structure_constant(field_ring(L), n, e, i, j, k)) = " +
					"module_basis_coordinates(restrict_ring(field_ring(L), rational_image(L)), " +
					"    regular_module(field_ring(L)), " +
					"    E, " +
					"    L.mul(e(i), e(j)), " +
					"    e(k))",
			},
			By(
				Normalized,
				coordinateImages,
				productsIntegral,
				vectorsIn,
				basisDef,
				sDef,
				integralStructureConstantDef.Inst[A]().At(R, n, e)))
		integerExpansion := arg.Have(
			"each multiplication coordinate is a sum of products of integer images",
			Statement{
				Binders: "∀j k:num.",
				Hypotheses: []string{
					"j ∈ s",
					"k ∈ s",
				},
				Conclusion: "module_basis_coordinates(restrict_ring(field_ring(L), rational_image(L)), " +
					"    regular_module(field_ring(L)), " +
					"    E, " +
					"    L.mul(a, e(j)), " +
					"    e(k)) = " +
					"module_sum(L.add, " +
					"    L.zero, " +
					"    s, " +
					"    λi:num. " +
					"        L.mul(integer_map(field_ring(L), c(i)), " +
					"            integer_map(field_ring(L), " +
					"                integral_structure_constant(field_ring(L), n, e, i, j, k))))",
			},
			Derive(func(b *Argument) {
				j, k := b.FixAs[Nat]("j"), b.FixAs[Nat]("k")
				indices := b.Assume()
				terms := b.Have(
					"the coordinate products equal the corresponding products of integer images",
					Statement{
						Binders: "∀i:num.",
						Hypotheses: []string{
							"i ∈ s",
						},
						Conclusion: "L.mul(module_basis_coordinates(restrict_ring(field_ring(L), rational_image(L)), " +
							"        regular_module(field_ring(L)), " +
							"        E, " +
							"        L.mul(e(j), e(i)), " +
							"        e(k)), " +
							"    module_basis_coordinates(restrict_ring(field_ring(L), rational_image(L)), " +
							"        regular_module(field_ring(L)), " +
							"        E, " +
							"        a, " +
							"        e(i))) = " +
							"L.mul(integer_map(field_ring(L), c(i)), " +
							"    integer_map(field_ring(L), integral_structure_constant(field_ring(L), n, e, i, j, k)))",
					},
					Derive(func(d *Argument) {
						mapIn := d.Have(
							"integer images belong to the field carrier",
							"∀z:int. integer_map(field_ring(L), z) ∈ L.carrier",
							BySets(field.RingOn.Read(L), characteristic_zero.IntegerMapHom.Inst[A]().At(R)))
						i := d.FixAs[Nat]("i")
						index := d.Assume()
						basisCommutes := d.Have(
							"the two integral basis vectors commute",
							"L.mul(e(j), e(i)) = L.mul(e(i), e(j))",
							By(commutes.At(d.TermAs[A]("e(j)"), d.TermAs[A]("e(i)")), vectorsIn, indices, index))
						structure := d.Have(
							"the reversed basis product has the same structure coordinate",
							"module_basis_coordinates(restrict_ring(field_ring(L), rational_image(L)), "+
								"    regular_module(field_ring(L)), "+
								"    E, "+
								"    L.mul(e(j), e(i)), "+
								"    e(k)) = "+
								"integer_map(field_ring(L), integral_structure_constant(field_ring(L), n, e, i, j, k))",
							By(structureImages.At(i, j, k), basisCommutes, indices, index))
						productCommutes := d.Have(
							"the scalar coefficient and structure constant commute",
							"L.mul(integer_map(field_ring(L), integral_structure_constant(field_ring(L), n, e, i, j, k)), "+
								"    integer_map(field_ring(L), c(i))) = "+
								"L.mul(integer_map(field_ring(L), c(i)), "+
								"    integer_map(field_ring(L), integral_structure_constant(field_ring(L), n, e, i, j, k)))",
							By(
								commutes.At(
									d.TermAs[A](
										"integer_map(field_ring(L), integral_structure_constant(field_ring(L), n, e, i, j, k))"),
									d.TermAs[A]("integer_map(field_ring(L), c(i))")),
								mapIn))
						d.Show(
							"replace the two coordinates and order their scalar factors",
							By(coefficients.At(i), structure, productCommutes, index))
					}))
				sums := b.Have(
					"the two finite coordinate sums have equal summands",
					"module_sum(L.add, "+
						"    L.zero, "+
						"    s, "+
						"    λi:num. "+
						"        L.mul(module_basis_coordinates(restrict_ring(field_ring(L), rational_image(L)), "+
						"                regular_module(field_ring(L)), "+
						"                E, "+
						"                L.mul(e(j), e(i)), "+
						"                e(k)), "+
						"            module_basis_coordinates(restrict_ring(field_ring(L), rational_image(L)), "+
						"                regular_module(field_ring(L)), "+
						"                E, "+
						"                a, "+
						"                e(i)))) = "+
						"module_sum(L.add, "+
						"    L.zero, "+
						"    s, "+
						"    λi:num. "+
						"        L.mul(integer_map(field_ring(L), c(i)), "+
						"            integer_map(field_ring(L), "+
						"                integral_structure_constant(field_ring(L), n, e, i, j, k))))",
					By(
						terms,
						module.ModuleSumCongruence.At(
							b.TermAs[Op[A]]("L.add"),
							b.TermAs[A]("L.zero"),
							s,
							b.TermAs[Fun[Nat, A]](
								"λi:num. "+
									"    L.mul(module_basis_coordinates(restrict_ring(field_ring(L), rational_image(L)), "+
									"            regular_module(field_ring(L)), "+
									"            E, "+
									"            L.mul(e(j), e(i)), "+
									"            e(k)), "+
									"        module_basis_coordinates(restrict_ring(field_ring(L), rational_image(L)), "+
									"            regular_module(field_ring(L)), "+
									"            E, "+
									"            a, "+
									"            e(i)))"),
							b.TermAs[Fun[Nat, A]](
								"λi:num. "+
									"    L.mul(integer_map(field_ring(L), c(i)), "+
									"        integer_map(field_ring(L), integral_structure_constant(field_ring(L), n, e, i, j, k)))"))))
				productCommutes := b.Have(
					"a commutes with the indexed basis vector",
					"L.mul(a, e(j)) = L.mul(e(j), a)",
					By(commutes.At(a, b.TermAs[A]("e(j)")), vectorsIn, indices))
				b.Show(
					"the functional expansion is the integer-image product sum",
					By(functionalExpansion.At(j, k), sums, productCommutes, indices))
			}))
		P, matrixDef := arg.LetAs[Fun[Nat, Fun[Nat, A]]](
			"P",
			"module_basis_matrix(restrict_ring(field_ring(L), rational_image(L)), "+
				"    regular_module(field_ring(L)), "+
				"    n, "+
				"    e, "+
				"    L.mul(a))")
		productsIn := arg.Have(
			"multiplication by a preserves the field carrier on basis vectors",
			"∀j:num. j ∈ s ⇒ L.mul(a, e(j)) ∈ L.carrier",
			By(vectorsIn, field.RingOn.Read(L), comm_ring.MulIn.Inst[A]().At(R)))
		validEntries := arg.Have(
			"valid multiplication-matrix entries lie in the rational scalar carrier",
			"∀i j:num. i < n ∧ j < n ⇒ P(i, j) ∈ restrict_ring(field_ring(L), rational_image(L)).carrier",
			Derive(func(b *Argument) {
				i, j := b.FixAs[Nat]("i"), b.FixAs[Nat]("j")
				inRange := b.Assume()
				indices := b.Have(
					"valid row and column numbers belong to the strict segment",
					"i ∈ s ∧ j ∈ s",
					BySets(inRange, sDef))
				rowIn := b.Have(
					"the row basis vector lies in the basis image",
					"e(i) ∈ E",
					BySets(basisDef, inRange))
				productIn := b.Have(
					"the multiplied column vector lies in the field",
					"L.mul(a, e(j)) ∈ L.carrier",
					By(productsIn.At(j), indices))
				coordinateIn := b.Have(
					"its basis coordinate belongs to the rational scalar carrier",
					"module_basis_coordinates(restrict_ring(field_ring(L), rational_image(L)), "+
						"    regular_module(field_ring(L)), "+
						"    E, "+
						"    L.mul(a, e(j)), "+
						"    e(i)) ∈ "+
						"restrict_ring(field_ring(L), rational_image(L)).carrier",
					By(
						basisZ,
						basisQ,
						indices,
						rowIn,
						productIn,
						module_dimension.BasisCoordinatesSpec.Read(moduleQ).AsFact().At(E, b.TermAs[A]("L.mul(a, e(j))"))))
				b.Show(
					"the matrix entry is this rational coordinate",
					By(
						Normalized,
						matrixDef,
						basisDef,
						inRange,
						coordinateIn,
						linear_determinant.ModuleBasisMatrixDef.At(RQ, M, n, e, arg.TermAs[Fun[A, A]]("L.mul(a)"), i, j)))
			}))
		rationalZero := arg.Have(
			"the rational scalar ring has the field zero",
			"restrict_ring(field_ring(L), rational_image(L)).zero = L.zero",
			Simp(Fwd(module_record.RestrictRingDef), Fwd(module_record.RingZeroDef), Fwd(field.FieldRingDef)),
			Refl())
		padding := arg.Have(
			"the multiplication matrix is zero outside its valid rows and columns",
			"∀i j:num. n ≤ i ∨ n ≤ j ⇒ P(i, j) = restrict_ring(field_ring(L), rational_image(L)).zero",
			Derive(func(b *Argument) {
				i, j := b.FixAs[Nat]("i"), b.FixAs[Nat]("j")
				outside := b.Assume()
				notValid := b.Have(
					"an outside position fails the two strict index bounds",
					"¬(i < n ∧ j < n)",
					ByArith(outside))
				b.Show(
					"the matrix definition selects its zero branch",
					By(
						matrixDef,
						notValid,
						rationalZero,
						linear_determinant.ModuleBasisMatrixDef.At(RQ, M, n, e, arg.TermAs[Fun[A, A]]("L.mul(a)"), i, j)))
			}))
		allEntries := arg.Have(
			"every padded matrix entry lies in the rational scalar carrier",
			"∀i j:num. P(i, j) ∈ restrict_ring(field_ring(L), rational_image(L)).carrier",
			Derive(func(b *Argument) {
				i, j := b.FixAs[Nat]("i"), b.FixAs[Nat]("j")
				b.Cases(b.TermAs[Bool]("i < n ∧ j < n"))
				b.When(
					"a valid position has a rational coordinate",
					func(d *Argument, inRange Fact) {
						d.Show(
							"use the valid-entry carrier fact",
							By(validEntries.At(i, j), inRange))
					})
				b.Otherwise(
					"an outside position is the scalar zero",
					func(d *Argument, notValid Fact) {
						outside := d.Have(
							"failure of the strict bounds puts an index outside",
							"n ≤ i ∨ n ≤ j",
							ByArith(notValid))
						zeroIn := d.Have(
							"the rational scalar zero belongs to its carrier",
							"restrict_ring(field_ring(L), rational_image(L)).zero ∈ "+
								"restrict_ring(field_ring(L), rational_image(L)).carrier",
							By(rationalRingOn, comm_ring.ZeroIn.Inst[A]().At(RQ)))
						d.Show(
							"the padded zero entry belongs to the scalar carrier",
							By(Normalized, padding.At(i, j), outside, zeroIn, rationalZero))
					})
			}))
		matrixOver := arg.Have(
			"the padded multiplication matrix is a matrix over the rational image",
			"matrix_over(restrict_ring(field_ring(L), rational_image(L)), n, P)",
			By(allEntries, padding, rationalRingOn, determinant.MatrixOverEntries.Inst[A]().At(RQ, n, P)))
		normDet := arg.Have(
			"the field norm is the determinant of this multiplication matrix",
			"field_norm(field_ring(L), rational_image(L), a) = "+
				"determinant(restrict_ring(field_ring(L), rational_image(L)), n, P)",
			By(
				Normalized,
				matrixDef,
				rationalSubfield,
				vectorsIn,
				indexedQ,
				field_norm.FieldNormFromBasis.Read(L).AsFact().At(Q, a, n, e)))
		S, boundDef := arg.LetAs[Nat]("S", "structure_constant_bound(field_ring(L), n, e)")
		budget, budgetDef := arg.LetAs[Real]("budget", "real_of_num(S * H)")
		nonnegative := arg.Have(
			"the entry budget is nonnegative",
			"real_of_num(0) ≤ budget",
			ByArith(
				budgetDef,
				real_construction.OfNumLessEq.At(arg.TermAs[Nat]("0"), arg.TermAs[Nat]("S * H"))))
		entryBounds := arg.Have(
			"the structure-constant budget bounds each valid matrix entry",
			"∀i j:num. i < n ∧ j < n ⇒ real_abs(rational_value(L, P(i, j))) ≤ budget",
			Derive(func(b *Argument) {
				i, j := b.FixAs[Nat]("i"), b.FixAs[Nat]("j")
				inRange := b.Assume()
				indices := b.Have(
					"the valid indices lie in the summation segment",
					"i ∈ s ∧ j ∈ s",
					BySets(sDef, inRange))
				entry := b.Have(
					"the matrix entry is the corresponding integer-image product sum",
					"P(i, j) = "+
						"module_sum(L.add, "+
						"    L.zero, "+
						"    s, "+
						"    λk:num. "+
						"        L.mul(integer_map(field_ring(L), c(k)), "+
						"            integer_map(field_ring(L), "+
						"                integral_structure_constant(field_ring(L), n, e, k, j, i))))",
					By(
						matrixDef,
						basisDef,
						inRange,
						indices,
						integerExpansion.At(j, i),
						linear_determinant.ModuleBasisMatrixDef.At(RQ, M, n, e, arg.TermAs[Fun[A, A]]("L.mul(a)"), i, j)))
				finiteSegment := b.Have(
					"the index segment is finite",
					"finite(s)",
					By(sDef, num_segment.FiniteBelowStrict.At(n)))
				boundedCoefficients := b.Have(
					"the integer coordinate coefficients obey the given bound",
					"∀k:num. k ∈ s ⇒ int_abs(c(k)) ≤ H",
					By(coefficients))
				d := b.TermAs[Fun[Nat, Int]]("λk:num. integral_structure_constant(field_ring(L), n, e, k, j, i)")
				sum := b.TermAs[Nat](
					"nat_sum(s, " +
						"    λk:num. num_of_int(int_abs(integral_structure_constant(field_ring(L), n, e, k, j, i))))")
				weighted := b.Have(
					"the generic weighted-sum estimate bounds the entry sum",
					"real_abs(rational_value(L, "+
						"        module_sum(L.add, "+
						"            L.zero, "+
						"            s, "+
						"            λk:num. "+
						"                L.mul(integer_map(field_ring(L), c(k)), "+
						"                    integer_map(field_ring(L), "+
						"                        integral_structure_constant(field_ring(L), n, e, k, j, i)))))) ≤ "+
						"real_of_num(H * "+
						"    nat_sum(s, "+
						"        λk:num. num_of_int(int_abs(integral_structure_constant(field_ring(L), n, e, k, j, i)))))",
					By(
						charZero,
						finiteSegment,
						boundedCoefficients,
						characteristic_zero.IntegerWeightedSumBound.Read(L).At(s, c, d, H)))
				sumBound := b.Have(
					"the structure-constant bound controls the sum over "+
						"the first index of absolute structure constants",
					"nat_sum(s, "+
						"    λk:num. num_of_int(int_abs(integral_structure_constant(field_ring(L), n, e, k, j, i)))) ≤ "+
						"S",
					By(Normalized, boundDef, sDef, inRange, structureConstantBoundSpec.At(R, n, e)))
				scaled := b.Have(
					"multiplication by H preserves the natural budget bound",
					"H * "+
						"nat_sum(s, "+
						"    λk:num. num_of_int(int_abs(integral_structure_constant(field_ring(L), n, e, k, j, i)))) ≤ "+
						"S * H",
					ByArith(sumBound, nat_order.LessEqMulMono.At(H, sum, S)))
				b.Show(
					"transport the natural budget to the real entry bound",
					ByArith(
						Normalized,
						budgetDef,
						entry,
						weighted,
						scaled,
						real_construction.OfNumLessEq.At(
							b.TermAs[Nat](
								"H * "+
									"nat_sum(s, "+
									"    λk:num. num_of_int(int_abs(integral_structure_constant(field_ring(L), n, e, k, j, i))))"),
							b.TermAs[Nat]("S * H"))))
			}))
		determinantBound := arg.Have(
			"the determinant estimate bounds the absolute field norm",
			"real_abs( "+
				"    rational_value(L, determinant(restrict_ring(field_ring(L), rational_image(L)), n, P))) ≤ "+
				"real_of_num(factorial(n)) * budget ^ n",
			By(
				charZero,
				matrixOver,
				nonnegative,
				entryBounds,
				lattice_determinant.DeterminantEntryBound.Read(L).At(n, P, budget)))
		naturalFactor := arg.Have(
			"the class-number bound packages the product-power factor",
			"factorial(n) * (S * H) ^ n = class_number_bound(field_ring(L), n, e) * H ^ n",
			Simp(
				Fwd(classNumberBoundDef),
				Rev(boundDef),
				Fwd(nat_arith.MulPowDistrib),
				Fwd(nat_arith.MulAssoc)),
			Refl())
		realFactor := arg.Have(
			"natural multiplication and powers embed into the exact real bound",
			"real_of_num(factorial(n)) * budget ^ n = "+
				"real_of_num(class_number_bound(field_ring(L), n, e) * H ^ n)",
			Simp(Fwd(budgetDef), Fwd(real_pow.OfNumPow), Rev(real_construction.OfNumMul), Fwd(naturalFactor)),
			Refl())
		arg.Show(
			"the determinant formula gives the stated norm bound",
			By(normDet, realFactor, determinantBound))
	}),
})}
