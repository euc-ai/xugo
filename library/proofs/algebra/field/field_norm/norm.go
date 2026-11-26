package field_norm

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_extension"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/linear_determinant"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/vector/determinant"
	"github.com/euc-ai/xugo/library/registry"
)

// FieldNormFromBasis — the norm is the determinant of multiplication in any
// indexed finite basis: K is a field under L's operations, whose ring is
// L's ring restricted to K; over that ring L is a module and
// multiplication by a is linear; so the
// determinant of multiplication by a, which defines the norm, is the
// determinant of its matrix in the basis and lies in the field K's
// carrier, K (LinearDeterminantFromBasis at the field K).
var FieldNormFromBasis = fieldNormFromBasisThm{family.Add(registry.ProofEntry{
	Name: "FieldNormFromBasis",
	Key:  "prop_edfcf41405bf3e2b",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀K:set(A). ∀a:A. ∀n:num. ∀e:(num → A).",
		Hypotheses: []string{
			"subfield(L, K)",
			"a ∈ L.carrier",
			"indexed_module_basis(restrict_ring(field_ring(L), K), regular_module(field_ring(L)), n, e)",
		},
		Conclusion: "field_norm(field_ring(L), K, a) = " +
			"determinant(restrict_ring(field_ring(L), K), " +
			"    n, " +
			"    module_basis_matrix(restrict_ring(field_ring(L), K), " +
			"        regular_module(field_ring(L)), " +
			"        n, " +
			"        e, " +
			"        L.mul(a))) ∧ " +
			"field_norm(field_ring(L), K, a) ∈ K",
	},
		func(
			arg *Argument,
			L field.FieldFact[on.L],
			K *Expr[Set[A]],
			a *Expr[A],
			n *Expr[Nat],
			e *Vec[A, DimN],
			hypotheses Fact,
		) {
			given := arg.Conjuncts(
				hypotheses,
				"K is a subfield of L",
				"a lies in L",
				"e is an indexed basis of L over K")
			subK, aInL, indexed := given[0], arg.MemberOf[on.L](a, given[1]), given[2]
			regular := arg.TermAs[module_record.ModuleOps[A, A]]("regular_module(field_ring(L))")
			fieldK := arg.Have(
				"K is a field under L's operations",
				"field_on(restrict_field(L, K))",
				By(subK, field.SubfieldFieldOn.Read(L).At(K)))
			// The ring of the field K is L's ring restricted to K
			// (RestrictFieldRing): the facts over the scalars K are read over it,
			// the ring a determinant of the field K is taken in.
			moduleK := arg.Have(
				"L is a module over the ring of the field K",
				"module_on(field_ring(restrict_field(L, K)), regular_module(field_ring(L)))",
				Simp(Rev(field.RestrictFieldRing)),
				By(subK, field_extension.SubfieldScalars.Read(L).At(K)))
			multiplication := arg.Have(
				"multiplication by a is linear over K",
				"module_homomorphism(field_ring(restrict_field(L, K)), "+
					"    regular_module(field_ring(L)), "+
					"    regular_module(field_ring(L)), "+
					"    L.mul(a))",
				Simp(Rev(field.RestrictFieldRing)),
				By(subK, aInL, field_extension.MultiplicationLinear.Read(L).At(K, aInL)))
			carrier := arg.Have(
				"the field K has the carrier K",
				"restrict_field(L, K).carrier = K",
				Simp(Fwd(field.RestrictFieldDef), Fwd(field.FieldCarrierDef)),
				Basic())
			basis := arg.Simplified(indexed, Fwd(field.RestrictFieldRing))
			overK := arg.Have(
				"the indexed basis computes the determinant of multiplication by a over the field K, a scalar of K",
				"module_determinant(field_ring(restrict_field(L, K)), regular_module(field_ring(L)), L.mul(a)) = "+
					"determinant(field_ring(restrict_field(L, K)), "+
					"    n, "+
					"    module_basis_matrix(field_ring(restrict_field(L, K)), "+
					"        regular_module(field_ring(L)), "+
					"        n, "+
					"        e, "+
					"        L.mul(a))) ∧ "+
					"module_determinant(field_ring(restrict_field(L, K)), regular_module(field_ring(L)), L.mul(a)) ∈ "+
					"restrict_field(L, K).carrier",
				By(
					moduleK,
					multiplication,
					basis,
					linear_determinant.LinearDeterminantFromBasis.Read(fieldK).At(
						regular, arg.TermAs[Fun[A, A]]("L.mul(a)"), n, e)))
			computed := arg.Simplified(overK, Fwd(carrier))
			arg.Show(
				"the determinant of multiplication by a over K is the field norm",
				Simp(Fwd(FieldNormDef), Fwd(field.RestrictFieldRing)),
				By(computed))
		}),
})}

var FieldNormMultiplicative = fieldNormMultiplicativeThm{family.Add(registry.ProofEntry{
	Name: "FieldNormMultiplicative",
	Key:  "prop_390be5edfb35f18",
	Deps: []registry.EntryLike{FieldNormDef, linear_determinant.LinearDeterminantCompose},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀K:set(A). ∀a b:A.",
		Hypotheses: []string{
			"subfield(L, K)",
			"finite_extension(L, K, L.carrier)",
			"a ∈ L.carrier",
			"b ∈ L.carrier",
		},
		Conclusion: "field_norm(field_ring(L), K, a * b) = " +
			"field_norm(field_ring(L), K, a) * field_norm(field_ring(L), K, b) ∧ " +
			"field_norm(field_ring(L), K, L.one) = L.one",
	},
		"Multiplication by ab is the composite of multiplication "+
			"by a and b. Multiplication by one is identity."),
})}

var FieldNormZeroIffZero = fieldNormZeroIffZeroThm{family.Add(registry.ProofEntry{
	Name: "FieldNormZeroIffZero",
	Key:  "prop_f01b36ad1b2d670",
	Reading: "A field extension has positive dimension. This prevents " +
		"the empty determinant from making the norm of zero equal to one.",
	Deps: []registry.EntryLike{
		FieldNormFromBasis,
		FieldNormMultiplicative,
		determinant.DeterminantZeroIffDependent,
		module_dimension.DimZero,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀K:set(A). ∀a:A.",
		Hypotheses: []string{
			"subfield(L, K)",
			"finite_extension(L, K, L.carrier)",
			"a ∈ L.carrier",
		},
		Conclusion: "field_norm(field_ring(L), K, a) = L.zero ⇔ a = L.zero",
	},
		"A nonzero multiplication map is invertible, so its determinant is nonzero. The "+
			"zero map has determinant zero because a field extension has positive dimension."),
})}

var FieldNormScalar = fieldNormScalarThm{family.Add(registry.ProofEntry{
	Name: "FieldNormScalar",
	Key:  "prop_f477db9786265b9c",
	Deps: []registry.EntryLike{
		FieldNormDef,
		linear_determinant.LinearDeterminantScalar,
		field_extension.ExtensionDegreeDef,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀K:set(A). ∀a:A.",
		Hypotheses: []string{
			"subfield(L, K)",
			"finite_extension(L, K, L.carrier)",
			"a ∈ K",
		},
		Conclusion: "field_norm(field_ring(L), K, a) = " +
			"monoid_pow(L.mul, L.one, a, extension_degree(L, K, L.carrier))",
	}, "Use the scalar determinant formula and the definition of extension degree."),
})}
