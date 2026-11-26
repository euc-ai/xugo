package ring_of_integers

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_norm"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/number_field/integral_closure"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/number_field/lattice_determinant"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/number_field/number_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/int_lattice"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/linear_determinant"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/linear_independence"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/vector/determinant"
	"github.com/euc-ai/xugo/library/registry"
)

// FieldNormFromIntegralBasis — in an integral basis of the ring of integers,
// the field norm of an algebraic integer a is the determinant, over the
// integer scalars, of the matrix of multiplication by a, a matrix with integer
// entries: the integral basis is also a rational basis of the field, where the
// norm is the determinant of the rational matrix of multiplication by a. Each
// a·e(j) is an algebraic integer, on which the rational and integer
// coordinates agree, so the rational matrix is the integer one, and its
// determinant is the same element computed over either restriction of the
// field ring.
var FieldNormFromIntegralBasis = fieldNormFromIntegralBasisThm{family.Add(registry.ProofEntry{
	Name: "FieldNormFromIntegralBasis",
	Key:  "prop_b103d19292ba09da",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀n:num. ∀e:(num → A). ∀a:A.",
		Hypotheses: []string{
			"number_field(L)",
			"integral_basis(field_ring(L), n, e)",
			"a ∈ «O»",
		},
		Conclusion: "field_norm(field_ring(L), rational_image(L), a) = determinant(«ℤ», n, «Mₐ») ∧ " +
			"matrix_over(«ℤ», n, «Mₐ»)",
		Abbrev: Abbrev{
			{Name: "Mₐ", Text: "module_basis_matrix(«ℤ», " +
				"    restrict_module(regular_module(field_ring(L)), «O»), " +
				"    n, " +
				"    e, " +
				"    L.mul(a))"},
		},
	}, func(
		arg *Argument,
		L field.FieldFact[on.L],
		n *Expr[Nat],
		e *Arrow[Nat, A],
		a *Expr[A],
		given Fact,
	) {
		fieldL := arg.TermAs[FieldOps[A]]("L")
		R := arg.TermAs[RingOps[A]]("field_ring(L)")
		O := arg.TermAs[Set[A]]("«O»")
		Q := arg.TermAs[Set[A]]("rational_image(L)")
		integerScalars := arg.TermAs[RingOps[A]]("«ℤ»")
		rationalScalars := arg.TermAs[RingOps[A]]("restrict_ring(field_ring(L), rational_image(L))")
		regular := arg.TermAs[module_record.ModuleOps[A, A]]("regular_module(field_ring(L))")
		moduleO := arg.TermAs[module_record.ModuleOps[A, A]](
			"restrict_module(regular_module(field_ring(L)), «O»)")
		scalars := arg.Conjuncts(
			GroupPremises(L, given, number_field.NumberFieldScalars.At(fieldL)),
			"L has characteristic zero",
			"its rational image is a subfield",
			"the integer image lies in the rational image",
			"the integer image is a commutative ring",
			"and a principal ideal domain",
			"L is a module over the integer image",
			"and over the rational image")
		rationalSubfield := scalars[1]
		fullLattice := arg.Have(
			"the integer ring is a full integer lattice",
			"full_integer_lattice(L, «O»)",
			By(given, RingOfIntegersFreeRankN.Read(L)))
		E, basisDef := arg.LetAs[Set[A]]("E", "{e(i):A | i:num | i < n}")
		indexedZ := arg.Have(
			"the integral basis is an indexed integer basis of the integer ring",
			"indexed_module_basis(«ℤ», restrict_module(regular_module(field_ring(L)), «O»), n, e)",
			By(given, IntegralBasisDef.At(R, n, e)))
		basisZ := arg.Have(
			"its image E is a finite integer basis, enumerated one-to-one",
			"finite(E) ∧ "+
				"module_basis(«ℤ», restrict_module(regular_module(field_ring(L)), «O»), E) ∧ "+
				"injective_on({i:num | i < n}, e)",
			By(indexedZ, basisDef, linear_independence.IndexedBasisImage.At(integerScalars, moduleO, n, e)))
		rational := arg.Conjuncts(
			GroupPremises(
				scalars[0], fullLattice, basisZ, int_lattice.FullLatticeBasisRational.Read(L).At(O, E)),
			"E is also a rational basis of the field",
			"rational and integer coordinates agree on algebraic integers")
		basisQ, coordinateRestriction := rational[0], rational[1]
		indexedQ := arg.Have(
			"so the integral basis is an indexed rational basis of the field",
			"indexed_module_basis(restrict_ring(field_ring(L), rational_image(L)), "+
				"    regular_module(field_ring(L)), "+
				"    n, "+
				"    e)",
			By(
				basisQ,
				basisZ,
				basisDef,
				linear_independence.IndexedModuleBasisDef.At(rationalScalars, regular, n, e)))
		integersInField := arg.Have(
			"algebraic integers lie in the field, a subring of it",
			"«O» ⊆ L.carrier",
			By(given, integral_closure.IntegralClosureSubring.Read(L), comm_ring.SubringSubset.At(R, O)))
		integerModule := arg.Conjuncts(
			GroupPremises(L, given, RingOfIntegersIntegerModule.At(fieldL)),
			"the integer ring is a submodule of L over the integer scalars",
			"it is a module over the integer scalars")[1]
		basisInO := arg.Have(
			"the integral basis consists of algebraic integers",
			"E ⊆ «O»",
			By(
				basisZ,
				linear_independence.BasisInCarrier.At(integerScalars, moduleO, E),
				module_record.RestrictModuleDef.At(regular, O)))
		vectorsInE := arg.Have(
			"the vectors of the integral basis lie in E",
			"∀i:num. i < n ⇒ e(i) ∈ E",
			BySets(basisDef))
		columns := arg.Have(
			"multiplication by a keeps the integral basis in the integer ring",
			"∀j:num. j < n ⇒ a * e(j) ∈ «O»",
			Derive(func(b *Argument) {
				j := b.FixAs[Nat]("j")
				index := b.Assume()
				ej := b.TermAs[A]("e(j)")
				b.Show(
					"a product of algebraic integers is one",
					By(
						index,
						vectorsInE.At(j),
						given,
						basisInO,
						integral_closure.IntegralMul.Read(L).At(a, ej),
						set_basic.SubsetDef.At(E, O)))
			}))
		matricesAgree := arg.Have(
			"the rational matrix of multiplication by a is the integer one",
			"module_basis_matrix(restrict_ring(field_ring(L), rational_image(L)), "+
				"    regular_module(field_ring(L)), "+
				"    n, "+
				"    e, "+
				"    L.mul(a)) = "+
				"«Mₐ»",
			Derive(func(b *Argument) {
				b.Do(Funext(), Simp(Fwd(linear_determinant.ModuleBasisMatrixDef), Rev(basisDef)))
				b.FixAs[Nat]("i")
				j := b.FixAs[Nat]("j")
				b.Cases(b.Term("i < n ∧ j < n"))
				b.When(
					"inside the matrix block the column is an algebraic integer, where the coordinates agree",
					func(c *Argument, inside Fact) {
						product := c.Have(
							"the column a·e(j) is an algebraic integer",
							"a * e(j) ∈ «O»",
							By(inside, columns.At(j)))
						c.Show(
							"coordinate restriction at that algebraic integer identifies the entries",
							Simp(Fwd(coordinateRestriction), Fwd(product)),
							Refl())
					})
				b.Otherwise(
					"outside the matrix block both entries are the zero padding",
					func(c *Argument, outside Fact) {
						c.Show(
							"the zero padding agrees",
							By(outside))
					})
			}))
		times := arg.TermAs[Fun[A, A]]("L.mul(a)")
		products := arg.TermAs[Fun[Nat, A]]("λj:num. a * e(j)")
		matrixOver := arg.Have(
			"the matrix of multiplication by a is a matrix over the integer scalars",
			"matrix_over(«ℤ», n, «Mₐ»)",
			By(
				integerModule,
				indexedZ,
				columns,
				module_record.RestrictModuleDef.At(regular, O),
				linear_determinant.ModuleBasisMatrixAsChange.At(integerScalars, moduleO, n, e, times),
				linear_determinant.BasisChangeMatrixOver.At(integerScalars, moduleO, n, e, products)))
		determinantsAgree := arg.Have(
			"the determinant reads only the ring operations, which "+
				"both restrictions keep, so the two determinants agree",
			"determinant(restrict_ring(field_ring(L), rational_image(L)), "+
				"    n, "+
				"    module_basis_matrix(restrict_ring(field_ring(L), rational_image(L)), "+
				"        regular_module(field_ring(L)), "+
				"        n, "+
				"        e, "+
				"        L.mul(a))) = "+
				"determinant(«ℤ», n, «Mₐ»)",
			Simp(Fwd(matricesAgree), Fwd(determinant.DeterminantDef), Fwd(module_record.RestrictRingDef)),
			Refl())
		inField := arg.Have(
			"a lies in the field",
			"a ∈ L.carrier",
			BySets(given, integersInField))
		am := arg.MemberOf[on.L](a, inField)
		normFormula := arg.Have(
			"the field norm is the rational determinant of multiplication by a",
			"field_norm(field_ring(L), rational_image(L), a) = "+
				"determinant(restrict_ring(field_ring(L), rational_image(L)), "+
				"    n, "+
				"    module_basis_matrix(restrict_ring(field_ring(L), rational_image(L)), "+
				"        regular_module(field_ring(L)), "+
				"        n, "+
				"        e, "+
				"        L.mul(a)))",
			By(inField, rationalSubfield, indexedQ, field_norm.FieldNormFromBasis.Read(L).At(Q, am, n, e)))
		arg.Do(Simp(Fwd(normFormula), Fwd(determinantsAgree)))
		arg.Show(
			"the norm is the integer determinant of a matrix over the integer scalars",
			By(matrixOver))
	}),
})}

// IntegralNormInInt — the field norm of an algebraic integer is an integer:
// in an integral basis it is the determinant of the matrix of multiplication
// by a, whose entries are integers.
var IntegralNormInInt = integralNormInIntThm{family.Add(registry.ProofEntry{
	Name: "IntegralNormInInt",
	Key:  "prop_b65bb1c1af5681b4",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀a:A.",
		Hypotheses: []string{
			"number_field(L)",
			"a ∈ «O»",
		},
		Conclusion: "field_norm(field_ring(L), rational_image(L), a) ∈ integer_image(field_ring(L))",
	}, func(arg *Argument, L field.FieldFact[on.L], a *Expr[A], given Fact) {
		fieldL := arg.TermAs[FieldOps[A]]("L")
		basisExists := arg.Have(
			"the ring of integers has an integral basis",
			"∃n:num. ∃e:(num → A). integral_basis(field_ring(L), n, e)",
			By(given, IntegralBasisExists.Read(L)))
		n, e, basis := arg.Unpack2As[Nat, Fun[Nat, A]](basisExists, "n", "e")
		matrix := arg.TermAs[Fun2[Nat, Nat, A]](
			"module_basis_matrix(restrict_ring(field_ring(L), integer_image(field_ring(L))), " +
				"    restrict_module(regular_module(field_ring(L)), «O»), " +
				"    n, " +
				"    e, " +
				"    L.mul(a))")
		arg.Show(
			"the norm is the determinant of a matrix over the integers, which is an integer",
			By(
				given,
				basis,
				number_field.NumberFieldDef.At(fieldL),
				FieldNormFromIntegralBasis.Read(L).At(n, e, a),
				lattice_determinant.DeterminantIntegralEntries.Read(L).At(n, matrix)))
	}),
})}
