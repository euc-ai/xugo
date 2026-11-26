// field_extension.go — the chapter: a subfield M of the field above a
// subfield K, read as a vector space over K with the field's own
// operations; its degree [M:K]; and the tower law.

package field_extension

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/abelian_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/free_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/linear_independence"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_domain"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/proofs/sets/set_product"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// ---------------------------------------------------------------------------
// The definitions
// ---------------------------------------------------------------------------

// FiniteExtensionDef — `finite_extension(L, K, M)`: M is finite-dimensional
// as a vector space over K, the scalars acting by the field's product.
var FiniteExtensionDef = finiteExtensionDefThm{family.Define(registry.DefEntry{
	Name:  "FiniteExtensionDef",
	Key:   "prop_b14b5838a52c2776",
	Const: "finite_extension",
	Type:  "field_ops(A) → set(A) → set(A) → bool",
	Equations: []string{
		"∀L:field_ops(A). ∀K M:set(A). " +
			"    finite_extension(L, K, M) ⇔ " +
			"    finite_dimensional(restrict_ring(field_ring(L), K), " +
			"        restrict_module(regular_module(field_ring(L)), M))",
	},
})}

// ExtensionDegreeDef — `extension_degree(L, K, M)`, the degree [M:K]: the
// dimension of M over K. It is a number nothing is said about when M is
// not a finite extension of K.
var ExtensionDegreeDef = extensionDegreeDefThm{family.Define(registry.DefEntry{
	Name:  "ExtensionDegreeDef",
	Key:   "prop_333fc92a6726ef05",
	Const: "extension_degree",
	Type:  "field_ops(A) → set(A) → set(A) → num",
	Equations: []string{
		"∀L:field_ops(A). ∀K M:set(A). " +
			"    extension_degree(L, K, M) = " +
			"    module_dim(restrict_ring(field_ring(L), K), " +
			"        restrict_module(regular_module(field_ring(L)), M))",
	},
})}

// ---------------------------------------------------------------------------
// An extension is a vector space over the smaller field
// ---------------------------------------------------------------------------

// RingExtensionModuleOn — a commutative ring M under the field's
// operations, holding a subfield K, is a vector space over K: the
// vectors' sum, zero and negation are the field's, and K acts by the
// field's product. K is a field in its own right, so the scalars are the
// ring on K; every other module axiom is a law of the ring M — its
// additive group, the closure of M under the product, the two
// distributive laws, the associativity of the product and one as its
// identity — read, where a scalar enters, at a scalar of K as a member of
// M, since K lies in M.
var RingExtensionModuleOn = ringExtensionModuleOnThm{family.Add(registry.ProofEntry{
	Name: "RingExtensionModuleOn",
	Key:  "prop_dfbde086737734",
	Reading: "K ⊆ M is load-bearing in the four axioms where a scalar meets a vector — " +
		"closure under scaling, both distributive laws and the associativity of scaling — each a " +
		"law of the ring M at a scalar of K read as a member of M. Of M nothing is asked beyond " +
		"its ring under the field's operations: it need not lie in L.carrier, nor be a field.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀K M:set(A).",
		Hypotheses: []string{
			"subfield(L, K)",
			"comm_ring_on(restrict_ring(field_ring(L), M))",
			"K ⊆ M",
		},
		Conclusion: "module_on(«scalarsOn»(K), «vectorsOn»(M))",
	},
		func(a *Argument, L field.FieldFact[on.L], K, M *Expr[Set[A]], h Fact) {
			parts := a.Conjuncts(
				h,
				"K is a subfield",
				"M is a commutative ring under the field's operations",
				"K lies in M")
			subK, ringM, kInM := parts[0], parts[1], parts[2]
			fieldK := a.Have(
				"K is a field under the field's operations",
				"field_on(restrict_field(L, K))",
				By(subK, field.SubfieldFieldOn.Read(L).At(K)))
			scalarsInM := a.Unfolded(kInM, set_basic.SubsetDef)
			additive := comm_ring.AddGroupOn.Read(ringM)
			multiplicative := comm_ring.MulMonoidOn.Read(ringM)
			a.Show(
				"so M is a vector space over K, one module axiom at a time",
				Unfold(module.ModuleOn),
				SplitConjAll(
					Case(
						"the scalars K are a commutative ring, K being a field",
						Simp(Fwd(field.RestrictFieldRing)),
						By(field.RingOn.Read(fieldK))),
					Case(
						"M is a group under the field's sum, the additive group of the ring M",
						Simp(Fwd(module_record.ModuleAdditiveGroupDef)),
						By(abelian_group.GroupOn.Read(additive), module_record.AdditiveGroupDef)),
					Case(
						"whose sum commutes",
						By(abelian_group.CommOn.Read(additive))),
					Case(
						"a scalar of K lies in M, so its product with a vector of M does",
						By(scalarsInM, comm_ring.MulIn.Read(ringM))),
					Case(
						"a scalar distributes over a sum of vectors, by distributivity in M",
						By(scalarsInM, comm_ring.LeftDistribOn.Read(ringM))),
					Case(
						"a sum of scalars distributes over a vector, likewise",
						By(scalarsInM, comm_ring.RightDistribOn.Read(ringM))),
					Case(
						"scaling by a product is scaling twice, the product associating in M",
						By(scalarsInM, comm_monoid.AssocOn.Read(multiplicative))),
					Case(
						"and one fixes every vector, being the identity of the product",
						By(comm_monoid.LeftIdentityOn.Read(multiplicative))),
				))
		}),
})}

// ExtensionModuleOn — a subfield M above a subfield K is a vector space
// over K: M's sum, zero and negation are the field's, and K acts by the
// field's product. M is a field in its own right, so a commutative ring
// under the field's operations, and this is RingExtensionModuleOn at that
// ring.
var ExtensionModuleOn = extensionModuleOnThm{family.Add(registry.ProofEntry{
	Name: "ExtensionModuleOn",
	Key:  "prop_a678dc5aebaa4a6b",
	Reading: "K ⊆ M is load-bearing in the four axioms where a scalar meets a " +
		"vector — closure under scaling, both distributive laws and the associativity " +
		"of scaling; of M being a subfield only its ring is used, never its inverses.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀K M:set(A).",
		Hypotheses: []string{
			"subfield(L, K)",
			"subfield(L, M)",
			"K ⊆ M",
		},
		Conclusion: "module_on(«scalarsOn»(K), «vectorsOn»(M))",
	},
		func(a *Argument, L field.FieldFact[on.L], K, M *Expr[Set[A]], h Fact) {
			parts := a.Conjuncts(
				h,
				"K is a subfield",
				"M is a subfield",
				"K lies in M")
			subK, subM, kInM := parts[0], parts[1], parts[2]
			fieldM := a.Have(
				"M is a field under the field's operations",
				"field_on(restrict_field(L, M))",
				By(subM, field.SubfieldFieldOn.Read(L).At(M)))
			ringM := a.Have(
				"so M is a commutative ring under the field's operations",
				"comm_ring_on(restrict_ring(field_ring(L), M))",
				Simp(Fwd(field.RestrictFieldRing)),
				By(field.RingOn.Read(fieldM)))
			a.Show(
				"so M is a commutative ring holding K, and a vector space over it",
				By(subK, ringM, kInM, RingExtensionModuleOn.Read(L).At(K, M)))
		}),
})}

// SubfieldScalars — a subfield K supplies scalars acting on the whole
// field: K is a subring of the field's ring, and the field's ring, a
// module over itself, is a module over the ring on K. A subfield meets
// every condition of a subring, and a module over a ring is one over any
// subring of its scalars.
var SubfieldScalars = subfieldScalarsThm{family.Add(registry.ProofEntry{
	Name: "SubfieldScalars",
	Key:  "prop_9a4e62acf2c897e2",
	Build: family.Theorem(Statement{
		Binders:    "∀L:field_on(A). ∀K:set(A).",
		Hypotheses: []string{"subfield(L, K)"},
		Conclusion: "subring(field_ring(L), K) ∧ module_on(«scalarsOn»(K), regular_module(field_ring(L)))",
	},
		func(a *Argument, L field.FieldFact[on.L], K *Expr[Set[A]], subK Fact) {
			subringK := a.Have(
				"K is a subring of the field's ring",
				"subring(field_ring(L), K)",
				By(subK, field.SubfieldSubring.Read(L).At(K)))
			moduleK := a.Have(
				"the field's ring, a module over itself, is a module over the ring on K",
				"module_on(«scalarsOn»(K), regular_module(field_ring(L)))",
				By(subringK, module.RegularModuleOverSubring.Read(field.RingOn.Read(L)).At(K)))
			a.Show(
				"so K supplies the scalars",
				By(subringK, moduleK))
		}),
})}

// SubfieldSubmodule — a subfield M above a subfield K and inside a set N
// is a K-submodule of N: M holds zero and is closed under the sum and,
// K lying in it, under K-multiples, so it is a K-submodule of the field,
// and a submodule lying in N is a submodule of the restriction to N.
var SubfieldSubmodule = subfieldSubmoduleThm{family.Add(registry.ProofEntry{
	Name: "SubfieldSubmodule",
	Key:  "prop_2762000489c391e5",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀K M N:set(A).",
		Hypotheses: []string{
			"subfield(L, K)",
			"subfield(L, M)",
			"K ⊆ M",
			"M ⊆ N",
		},
		Conclusion: "submodule(«scalarsOn»(K), «vectorsOn»(N), M)",
	},
		func(a *Argument, L field.FieldFact[on.L], K, M, N *Expr[Set[A]], h Fact) {
			parts := a.Conjuncts(
				h,
				"K is a subfield",
				"M is a subfield",
				"K lies in M",
				"M lies in N")
			subK, subM, kInM, mInN := parts[0], parts[1], parts[2], parts[3]
			rK := a.TermAs[module_record.RingOps[A]]("«scalarsOn»(K)")
			whole := a.TermAs[module_record.ModuleOps[A, A]]("regular_module(field_ring(L))")
			overK := a.Have(
				"the field's ring is a module over K",
				"module_on(«scalarsOn»(K), regular_module(field_ring(L)))",
				By(subK, SubfieldScalars.Read(L).At(K)))
			inField := a.Have(
				"M is a K-submodule of the field, closed under sums and K-multiples",
				"submodule(«scalarsOn»(K), regular_module(field_ring(L)), M)",
				By(
					kInM,
					field.SubfieldSubset.Read(subM),
					field.SubfieldZero.Read(subM),
					field.SubfieldAdd.Read(subM),
					field.SubfieldMul.Read(subM),
					set_basic.SubsetDef.At(K, M),
					submodule.SubmoduleCriterion.Read(overK).At(M)))
			a.Show(
				"and M lies in N, so it is a K-submodule of N",
				By(inField, mInN, submodule.SubmoduleRestrict.At(rK, whole, N, M)))
		}),
})}

// ScaleLinear — multiplication by a member a of the field is a linear map
// of the field over each of its subrings S: it keeps L, distributes over
// sums and commutes with the multiples by S, the field's product being
// associative and commutative.
var ScaleLinear = scaleLinearThm{family.Add(registry.ProofEntry{
	Name: "ScaleLinear",
	Key:  "prop_255969e96e8121d0",
	Reading: "a may be zero, mul(zero) being the zero map on L; S enters " +
		"only as the scalars, so the one map is linear over every subring at once.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S:set(A). ∀a:A.",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"a ∈ L.carrier",
		},
		Conclusion: "module_homomorphism(«scalarsOn»(S), " +
			"    regular_module(field_ring(L)), " +
			"    regular_module(field_ring(L)), " +
			"    L.mul(a))",
	},
		func(arg *Argument, L field.FieldFact[on.L], S *Expr[Set[A]], a *Expr[A], given Fact) {
			parts := arg.Conjuncts(
				given,
				"S is a subring of L",
				"a lies in L")
			subring, aInL := parts[0], parts[1]
			inField := arg.Have(
				"S lies in L",
				"S ⊆ L.carrier",
				By(comm_ring.SubringSubset.Read(subring)))
			ringL := field.RingOn.Read(L)
			arg.Show(
				"L is an S-module, and multiplication by a keeps L, "+
					"distributes over sums and commutes with multiples by S",
				Unfold(module_homomorphism.ModuleHomomorphismDef),
				By(
					module.ModuleRestrictScalars.Read(module.RegularModuleOn.Read(ringL)).At(S),
					subring,
					aInL,
					arg.Unfolded(inField, set_basic.SubsetDef),
					comm_ring.MulIn.Read(ringL),
					comm_ring.LeftDistribOn.Read(ringL),
					comm_monoid.LeftCommOn.Read(comm_ring.MulMonoidOn.Read(ringL))))
		}),
})}

// MultiplicationLinear — multiplication by an element z of the field is
// linear over a subfield K: L.mul(z) is an endomorphism of the field's
// ring as a module over the ring on K. A subfield is a subring, and
// multiplication by z is linear over every subring (ScaleLinear).
var MultiplicationLinear = multiplicationLinearThm{family.Add(registry.ProofEntry{
	Name: "MultiplicationLinear",
	Key:  "prop_2dc3e13c9000fb3f",
	Build: family.Theorem(Statement{
		Binders:    "∀L:field_on(A). ∀K:set(A). ∀z:A.",
		Hypotheses: []string{"subfield(L, K)", "z ∈ L.carrier"},
		Conclusion: "module_homomorphism(«scalarsOn»(K), " +
			"    regular_module(field_ring(L)), " +
			"    regular_module(field_ring(L)), " +
			"    L.mul(z))",
	},
		func(a *Argument, L field.FieldFact[on.L], K *Expr[Set[A]], z *Expr[A], h Fact) {
			given := a.Conjuncts(
				h,
				"K is a subfield",
				"z lies in L")
			zInL := a.MemberOf[on.L](z, given[1])
			a.Show(
				"K is a subring of the field's ring, and multiplication by z is linear over every subring",
				By(given[0], field.SubfieldSubring.Read(L).At(K), ScaleLinear.Read(L).At(K, zInL)))
		}),
})}

// SubfieldRetraction — a subfield k of L is the image of a k-linear map
// of L onto k that fixes k: one alone is independent over k, so it lies
// in a basis of L over k, and the linear map that is one at one and zero
// at every other basis vector sends each c of k, c times one, to c.
var SubfieldRetraction = subfieldRetractionThm{family.Add(registry.ProofEntry{
	Name: "SubfieldRetraction",
	Key:  "prop_cee01db5b56eb737",
	Reading: "No finiteness is asked of L over k: the basis through one may " +
		"be infinite, and the axiom of choice enters through the basis extension.",
	Build: family.Theorem(Statement{
		Binders:    "∀L:field_on(A). ∀k:set(A).",
		Hypotheses: []string{"subfield(L, k)"},
		Conclusion: "∃π:(A → A). " +
			"    module_homomorphism(«scalarsOn»(k), regular_module(field_ring(L)), «vectorsOn»(k), π) ∧ " +
			"    (∀c:A. c ∈ k ⇒ π(c) = c)",
	},
		func(a *Argument, L field.FieldFact[on.L], k *Expr[Set[A]], subK Fact) {
			one := a.TermAs[A]("L.one")
			ring := field.RingOn.Read(L)
			rightIdentity := comm_monoid.RightIdentityOn.Read(comm_ring.MulMonoidOn.Read(ring))
			lOverK := a.Have(
				"L is a vector space over k",
				"module_on(«scalarsOn»(k), regular_module(field_ring(L)))",
				By(subK, SubfieldScalars.Read(L).At(k)))
			kOverK := a.Have(
				"and so is k itself",
				"module_on(«scalarsOn»(k), «vectorsOn»(k))",
				By(subK, ExtensionModuleOn.Read(L).At(k, k), set_order.SubsetRefl.At(k)))
			kInL := a.Have(
				"k lies in L",
				"k ⊆ L.carrier",
				By(field.SubfieldSubset.Read(subK)))
			oneAlone := a.Have(
				"one alone is independent over k",
				"module_independent(«scalarsOn»(k), regular_module(field_ring(L)), {L.one})",
				Derive(func(b *Argument) {
					onlyZero := b.Have(
						"a scalar c of k with c · one in the span of nothing is zero",
						Statement{
							Binders: "∀c:A.",
							Hypotheses: []string{
								"c ∈ k",
								"c * L.one ∈ module_span(«scalarsOn»(k), regular_module(field_ring(L)), ∅)",
							},
							Conclusion: "c = L.zero",
						},
						Derive(func(d *Argument) {
							c := d.FixAs[A]("c")
							parts := d.Conjuncts(
								d.Assume(),
								"c lies in k",
								"c · one lies in the span of nothing")
							d.Show(
								"c · one is c, and the span of nothing is zero alone",
								BySets(parts[0], parts[1], kInL, submodule.SpanEmpty.Read(lOverK), rightIdentity.AsFact().At(c)))
						}))
					b.Show(
						"so one joins the empty set independently",
						By(
							onlyZero,
							comm_ring.OneIn.Read(ring),
							linear_independence.IndependentInsertNoMultiple.Read(lOverK).AsFact().At(
								b.TermAs[Set[A]]("∅"), one),
							linear_independence.IndependentEmpty))
				}))
			B, throughOne := a.ObtainAs[Set[A]](
				"k being a field, one lies in a basis B of L over k",
				"∃B:set(A). {L.one} ⊆ B ∧ module_basis(«scalarsOn»(k), regular_module(field_ring(L)), B)",
				By(
					subK,
					oneAlone,
					linear_independence.BasisExtends.Read(lOverK).At(
						a.TermAs[Fun[A, A]]("L.inv"), a.TermAs[Set[A]]("{L.one}")),
					field.SubfieldRingSubfield.Read(L).At(k, k)))
			basisParts := a.Conjuncts(
				throughOne,
				"one lies in B",
				"B is a basis of L over k")
			oneInB, basis := basisParts[0], basisParts[1]
			values := a.Have(
				"one and zero lie in k",
				"∀e:A. e ∈ B ⇒ COND(e = L.one, L.one, L.zero) ∈ k",
				By(field.SubfieldOne.Read(subK), field.SubfieldZero.Read(subK)))
			π, extension := a.ObtainAs[Fun[A, A]](
				"the k-linear map π of L into k that is one at one and zero at the other vectors of B",
				"∃π:(A → A). "+
					"    module_homomorphism(«scalarsOn»(k), regular_module(field_ring(L)), «vectorsOn»(k), π) ∧ "+
					"    (∀e:A. e ∈ B ⇒ π(e) = COND(e = L.one, L.one, L.zero))",
				By(
					kOverK,
					basis,
					values,
					free_module.BasisLinearExtension.Read(lOverK).At(
						a.TermAs[module_record.ModuleOps[A, A]]("«vectorsOn»(k)"),
						B,
						a.TermAs[Fun[A, A]]("λe:A. COND(e = L.one, L.one, L.zero)"))))
			extensionParts := a.Conjuncts(
				extension,
				"π is k-linear",
				"π is one at one and zero at the other vectors of B")
			linear, onBasis := extensionParts[0], extensionParts[1]
			a.Take(π)
			fixes := a.Have(
				"π fixes k: π(c) = π(c · one) = c · π(one) = c",
				"∀c:A. c ∈ k ⇒ π(c) = c",
				Derive(func(b *Argument) {
					c := b.FixAs[A]("c")
					cInK := b.Assume()
					atOne := b.Have(
						"π is one at one, a vector of B",
						"π(L.one) = L.one",
						BySets(onBasis.At(one), oneInB))
					b.Show(
						"by the k-linearity of π at c and one, c lying in L",
						BySets(
							Normalized,
							atOne,
							cInK,
							kInL,
							module_homomorphism.HomSmul.Read(linear).AsFact().At(c, one),
							rightIdentity.AsFact().At(c),
							comm_ring.OneIn.Read(ring)))
				}))
			a.Show(
				"so π is a k-linear map of L onto k fixing k",
				By(linear, fixes))
		}),
})}

// ---------------------------------------------------------------------------
// The tower law
// ---------------------------------------------------------------------------

// TowerSpan — spanning sets multiply: B spanning M over K and C spanning
// N over M give the products b * c spanning N over K. A span is the meet
// of the subspaces holding its set, so B lies in M and C in N. A vector
// of N is Σ m(c) * c over finitely many c ∈ C with each m(c) in M, and
// each m(c) is Σ k(b) * b over finitely many b ∈ B with each k(b) in K;
// so each term m(c) * c = Σ k(b) * (b * c) lies in the K-span of the
// products, and so does their sum. The products lie in N, so their span
// does too.
var TowerSpan = towerSpanThm{family.Add(registry.ProofEntry{
	Name: "TowerSpan",
	Key:  "prop_9bdd01ebfe9574d",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀K M N B C:set(A).",
		Hypotheses: []string{
			"subfield(L, K)",
			"subfield(L, M)",
			"subfield(L, N)",
			"K ⊆ M",
			"M ⊆ N",
			"module_span(«scalarsOn»(K), «vectorsOn»(M), B) = M",
			"module_span(«scalarsOn»(M), «vectorsOn»(N), C) = N",
		},
		Conclusion: "module_span(«scalarsOn»(K), «vectorsOn»(N), «towerProducts») = N",
		Abbrev: Abbrev{
			{Name: "towerProductSpan", Text: "module_span(«scalarsOn»(K), «vectorsOn»(N), «towerProducts»)"},
		},
	},
		func(a *Argument, L field.FieldFact[on.L], K, M, N, B, C *Expr[Set[A]], tower Fact) {
			h := a.Conjuncts(
				tower,
				"K is a subfield",
				"M is a subfield",
				"N is a subfield",
				"K lies in M",
				"M lies in N",
				"B spans M over K",
				"C spans N over M")
			subK, subM, subN, kInM, mInN, spanB, spanC := h[0], h[1], h[2], h[3], h[4], h[5], h[6]
			rK, vN :=
				a.TermAs[module_record.RingOps[A]]("«scalarsOn»(K)"),
				a.TermAs[module_record.ModuleOps[A, A]]("«vectorsOn»(N)")
			products, productSpan := a.TermAs[Set[A]]("«towerProducts»"), a.TermAs[Set[A]]("«towerProductSpan»")

			bInM := a.Have(
				"B lies in every subspace holding it, so in their meet M",
				"B ⊆ M",
				BySets(a.Unfolded(spanB, submodule.ModuleSpanDef)))
			cInN := a.Have(
				"C lies in every subspace holding it, so in their meet N",
				"C ⊆ N",
				BySets(a.Unfolded(spanC, submodule.ModuleSpanDef)))
			overKM := a.Have(
				"M is a vector space over K",
				"module_on(«scalarsOn»(K), «vectorsOn»(M))",
				By(subK, subM, kInM, ExtensionModuleOn.Read(L).At(K, M)))
			overMN := a.Have(
				"N is a vector space over M",
				"module_on(«scalarsOn»(M), «vectorsOn»(N))",
				By(subM, subN, mInN, ExtensionModuleOn.Read(L).At(M, N)))
			kInN := a.Have(
				"K lies in N",
				"K ⊆ N",
				By(kInM, mInN, set_order.SubsetTrans.At(K, M, N)))
			overKN := a.Have(
				"N is a vector space over K",
				"module_on(«scalarsOn»(K), «vectorsOn»(N))",
				By(subK, subN, kInN, ExtensionModuleOn.Read(L).At(K, N)))
			mInL := a.Have(
				"M lies in L",
				"M ⊆ L.carrier",
				By(subM, field.SubfieldSubset))
			nInL := a.Have(
				"N lies in L",
				"N ⊆ L.carrier",
				By(subN, field.SubfieldSubset))

			closedN := a.Have(
				"N is closed under the product",
				"∀x y:A. x ∈ N ∧ y ∈ N ⇒ x * y ∈ N",
				By(subN, field.SubfieldMul))
			productsInN := a.Have(
				"the products lie in N",
				"«towerProducts» ⊆ N",
				BySets(bInM, mInN, cInN, closedN))
			productsInSpan := a.Have(
				"and in their K-span",
				"«towerProducts» ⊆ «towerProductSpan»",
				Cite(submodule.SubsetSpan, rK, vN, products))
			spanSub := a.Have(
				"which is a subspace of N",
				"submodule(«scalarsOn»(K), «vectorsOn»(N), «towerProductSpan»)",
				By(productsInN, submodule.SpanSubmodule.Read(overKN)))
			twice := a.Have(
				"N's vectors restricted to the span are the field's restricted to it",
				"restrict_module(«vectorsOn»(N), «towerProductSpan») = «vectorsOn»(«towerProductSpan»)",
				Unfold(module_record.RestrictModuleDef))
			spanModule := a.Have(
				"and so a vector space over K in its own right",
				"module_on(«scalarsOn»(K), «vectorsOn»(«towerProductSpan»))",
				twice.RwRev(),
				By(spanSub, submodule.SubmoduleModuleOn.Read(overKN).At(productSpan)))

			everyVector := a.Have(
				"every vector of N is a K-combination of products",
				"∀v:A. v ∈ N ⇒ v ∈ «towerProductSpan»",
				Derive(func(b *Argument) {
					v := b.FixAs[A]()
					inN := b.Assume()
					T, _, expansion := b.Obtain2As[Set[A], Fun[A, A]](
						"v is an M-combination of finitely many c ∈ C",
						"∃T:set(A). ∃m:(A → A). "+
							"    finite(T) ∧ "+
							"    T ⊆ C ∧ "+
							"    (∀x:A. x ∈ T ⇒ m(x) ∈ M) ∧ "+
							"    v = module_sum(L.add, L.zero, T, λx:A. m(x) * x)",
						By(inN, spanC, cInN, linear_independence.SpanMembership.Read(overMN).At(C, v)))
					overC := b.Conjuncts(
						expansion,
						"T is finite",
						"T lies in C",
						"the coefficients m(c) lie in M",
						"v is their combination")
					terms := b.Have(
						"each term m(c) * c lies in the span of the products",
						"∀c:A. c ∈ T ⇒ m(c) * c ∈ «towerProductSpan»",
						Derive(func(d *Argument) {
							c := d.FixAs[A]()
							inT := d.Assume()
							mc := d.Have(
								"m(c) lies in M",
								"m(c) ∈ M",
								By(inT, overC[2]))
							cC := d.Have(
								"c lies in C",
								"c ∈ C",
								BySets(inT, overC[1]))
							cN := d.Have(
								"and in N",
								"c ∈ N",
								BySets(cC, cInN))
							U, _, expandM := d.Obtain2As[Set[A], Fun[A, A]](
								"m(c) is a K-combination of finitely many b ∈ B",
								"∃U:set(A). ∃k:(A → A). "+
									"    finite(U) ∧ "+
									"    U ⊆ B ∧ "+
									"    (∀x:A. x ∈ U ⇒ k(x) ∈ K) ∧ "+
									"    m(c) = module_sum(L.add, L.zero, U, λx:A. k(x) * x)",
								By(mc, spanB, bInM, linear_independence.SpanMembership.Read(overKM).At(B, d.TermAs[A]("m(c)"))))
							overB := d.Conjuncts(
								expandM,
								"U is finite",
								"U lies in B",
								"the coefficients k(b) lie in K",
								"m(c) is their combination")
							inM := d.Have(
								"each k(b) * b lies in M",
								"∀x:A. x ∈ U ⇒ k(x) * x ∈ M",
								Derive(func(e *Argument) {
									e.FixAs[A]()
									inU := e.Assume()
									scalars := e.Have(
										"a scalar of K times a vector of M",
										"k(x) ∈ K ∧ x ∈ M",
										BySets(inU, overB[1], overB[2], bInM))
									e.Show(
										"lies in M",
										By(scalars, module.SmulIn.Read(overKM)))
								}))
							distribute := d.Have(
								"multiplying by c distributes over the combination",
								"module_sum(L.add, L.zero, U, λx:A. k(x) * x) * c = "+
									"module_sum(L.add, L.zero, U, λx:A. k(x) * x * c)",
								By(
									overB[0],
									inM,
									module.ModuleSumSmulRight.Read(overMN).At(
										U, d.TermAs[Fun[A, A]]("λx:A. k(x) * x"), proof.MemberOf(c, cN))))
							each := d.Have(
								"each k(b) * b * c lies in the span of the products",
								"∀x:A. x ∈ U ⇒ k(x) * x * c ∈ «towerProductSpan»",
								Derive(func(e *Argument) {
									e.FixAs[A]()
									inU := e.Assume()
									parts := e.Have(
										"x ∈ B, k(x) ∈ K, and k(x), x, c lie in L",
										"x ∈ B ∧ k(x) ∈ K ∧ k(x) ∈ L.carrier ∧ x ∈ L.carrier ∧ c ∈ L.carrier",
										BySets(inU, overB[1], overB[2], bInM, kInM, mInL, nInL, cN))
									regroup := e.Have(
										"by associativity in L",
										"k(x) * x * c = k(x) * (x * c)",
										ByArith(field.RingOn.Read(L), parts))
									product := e.Have(
										"x * c is one of the products",
										"x * c ∈ «towerProducts»",
										BySets(parts, cC))
									spanned := e.Have(
										"so it lies in their span",
										"x * c ∈ «towerProductSpan»",
										BySets(product, productsInSpan))
									scaled := e.Have(
										"so k(x) * (x * c) lies in the span",
										"k(x) * (x * c) ∈ «towerProductSpan»",
										By(parts, spanned, submodule.SubmoduleSmul.Read(spanSub)))
									e.Show(
										"and so does k(x) * x * c",
										regroup.Rw(),
										By(scaled))
								}))
							sum := d.Have(
								"so does their sum",
								"module_sum(L.add, L.zero, U, λx:A. k(x) * x * c) ∈ «towerProductSpan»",
								By(
									overB[0],
									each,
									module.ModuleSumIn.Read(spanModule).At(U, d.TermAs[Fun[A, A]]("λx:A. k(x) * x * c"))))
							d.Show(
								"which is m(c) * c",
								overB[3].Rw(),
								distribute.Rw(),
								By(sum))
						}))
					sum := b.Have(
						"so does their sum",
						"module_sum(L.add, L.zero, T, λx:A. m(x) * x) ∈ «towerProductSpan»",
						By(
							overC[0],
							terms,
							module.ModuleSumIn.Read(spanModule).At(T, b.TermAs[Fun[A, A]]("λx:A. m(x) * x"))))
					b.Show(
						"which is v",
						overC[3].Rw(),
						By(sum))
				}))
			inclusion := a.Have(
				"so N lies in the span of the products",
				"N ⊆ «towerProductSpan»",
				By(everyVector, set_basic.SubsetDef))
			carrier := a.Have(
				"N is a subspace of itself",
				"submodule(«scalarsOn»(K), «vectorsOn»(N), N)",
				By(submodule.CarrierSubmodule.Read(overKN)))
			spanInN := a.Have(
				"the span of the products lies in N",
				"«towerProductSpan» ⊆ N",
				By(productsInN, carrier, submodule.SpanLeast.At(rK, vN, products, N)))
			a.Show(
				"so the products span N over K",
				By(spanInN, inclusion, set_order.SubsetAntisym.At(productSpan, N)))
		}),
})}

// TowerIndependent — independent sets multiply: finite sets B independent
// over K and C independent over M give card(B) * card(C) distinct products
// b * c, independent over K. Distinct pairs give distinct products: with
// one c the nonzero c cancels, and with c₁ ≠ c₂ the equation would put c₁
// in the M-span of c₂. A vanishing K-combination of products, its
// coefficients extended by zero to a' on all of them and the products
// indexed by the pairs (c, b) of C × B, regroups as
// Σ_c (Σ_b a'(b * c) * b) * c: C's independence over M makes each inner
// sum zero, and B's over K each coefficient.
var TowerIndependent = towerIndependentThm{family.Add(registry.ProofEntry{
	Name: "TowerIndependent",
	Key:  "prop_3afff238c37725f1",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀K M N B C:set(A).",
		Hypotheses: []string{
			"subfield(L, K)",
			"subfield(L, M)",
			"subfield(L, N)",
			"K ⊆ M",
			"M ⊆ N",
			"finite(B)",
			"finite(C)",
			"module_independent(«scalarsOn»(K), «vectorsOn»(M), B)",
			"module_independent(«scalarsOn»(M), «vectorsOn»(N), C)",
		},
		Conclusion: "module_independent(«scalarsOn»(K), «vectorsOn»(N), «towerProducts») ∧ " +
			"has_size(«towerProducts», card(B) * card(C))",
	},
		func(a *Argument, L field.FieldFact[on.L], K, M, N, B, C *Expr[Set[A]], tower Fact) {
			h := a.Conjuncts(
				tower,
				"K is a subfield",
				"M is a subfield",
				"N is a subfield",
				"K lies in M",
				"M lies in N",
				"B is finite",
				"C is finite",
				"B is independent over K",
				"C is independent over M")
			subK, subM, subN, kInM, mInN, finB, finC, indB, indC :=
				h[0], h[1], h[2], h[3], h[4], h[5], h[6], h[7], h[8]
			rM, vN :=
				a.TermAs[module_record.RingOps[A]]("«scalarsOn»(M)"),
				a.TermAs[module_record.ModuleOps[A, A]]("«vectorsOn»(N)")
			add, zero := a.TermAs[Op[A]]("L.add"), a.TermAs[A]("L.zero")
			products := a.TermAs[Set[A]]("«towerProducts»")

			overKM := a.Have(
				"M is a vector space over K",
				"module_on(«scalarsOn»(K), «vectorsOn»(M))",
				By(subK, subM, kInM, ExtensionModuleOn.Read(L).At(K, M)))
			overMN := a.Have(
				"N is a vector space over M",
				"module_on(«scalarsOn»(M), «vectorsOn»(N))",
				By(subM, subN, mInN, ExtensionModuleOn.Read(L).At(M, N)))
			kInN := a.Have(
				"K lies in N",
				"K ⊆ N",
				By(kInM, mInN, set_order.SubsetTrans.At(K, M, N)))
			overKN := a.Have(
				"N is a vector space over K",
				"module_on(«scalarsOn»(K), «vectorsOn»(N))",
				By(subK, subN, kInN, ExtensionModuleOn.Read(L).At(K, N)))
			freeB := a.Conjuncts(
				a.Unfolded(indB, linear_independence.ModuleIndependentDef),
				"B lies in M",
				"a vanishing K-combination of B has zero coefficients")
			freeC := a.Conjuncts(
				a.Unfolded(indC, linear_independence.ModuleIndependentDef),
				"C lies in N",
				"a vanishing M-combination of C has zero coefficients")
			bInM, bFree, cInN, cFree := freeB[0], freeB[1], freeC[0], freeC[1]
			mInL := a.Have(
				"M lies in L",
				"M ⊆ L.carrier",
				By(subM, field.SubfieldSubset))
			nInL := a.Have(
				"N lies in L",
				"N ⊆ L.carrier",
				By(subN, field.SubfieldSubset))
			zeroOffB := a.Have(
				"zero is not in B",
				"L.zero ∉ B",
				By(indB, field.OneNotZeroOn.Read(L), linear_independence.IndependentZeroNotIn.Read(overKM)))
			zeroOffC := a.Have(
				"zero is not in C",
				"L.zero ∉ C",
				By(indC, field.OneNotZeroOn.Read(L), linear_independence.IndependentZeroNotIn.Read(overMN)))

			distinct := a.Have(
				"distinct pairs give distinct products",
				"∀b₁ b₂ c₁ c₂:A. b₁ ∈ B ∧ c₁ ∈ C ∧ b₂ ∈ B ∧ c₂ ∈ C ∧ b₁ * c₁ = b₂ * c₂ ⇒ b₁ = b₂ ∧ c₁ = c₂",
				Derive(func(b *Argument) {
					b1, b2, c1, c2 := b.FixAs[A](), b.FixAs[A](), b.FixAs[A](), b.FixAs[A]()
					pair := b.Conjuncts(
						b.Assume(),
						"b₁ lies in B",
						"c₁ lies in C",
						"b₂ lies in B",
						"c₂ lies in C",
						"the two products agree")
					in := b.Have(
						"b₁, b₂ lie in M and c₁, c₂ in N, all four in L",
						"b₁ ∈ M ∧ "+
							"b₂ ∈ M ∧ "+
							"c₁ ∈ N ∧ "+
							"c₂ ∈ N ∧ "+
							"b₁ ∈ L.carrier ∧ "+
							"b₂ ∈ L.carrier ∧ "+
							"c₁ ∈ L.carrier ∧ "+
							"c₂ ∈ L.carrier",
						BySets(bInM, cInN, mInL, nInL, pair[0], pair[1], pair[2], pair[3]))
					b.Cases(b.Term("c₁ = c₂"))
					b.When(
						"with one c, the nonzero c₁ cancels",
						func(c *Argument, same Fact) {
							shifted := c.Have(
								"the products are b₁ * c₁ and b₂ * c₁",
								"b₁ * c₁ = b₂ * c₁",
								By(pair[4], same))
							nonzero := c.Have(
								"c₁ is not zero",
								"c₁ ≠ L.zero",
								By(Normalized, zeroOffC, pair[1]))
							c.Show(
								"so b₁ = b₂",
								By(
									same,
									in,
									nonzero,
									shifted,
									integral_domain.MulCancelRight.Read(integral_domain.FieldIntegralDomain.Read(L)).AsFact().At(
										c1, b1, b2)))
						})
					b.Otherwise(
						"with c₁ ≠ c₂, c₁ would lie in the M-span of c₂",
						func(c *Argument, apart Fact) {
							nonzero := c.Have(
								"b₁ is not zero",
								"b₁ ≠ L.zero",
								By(Normalized, zeroOffB, pair[0]))
							invIn := c.Have(
								"its inverse lies in L",
								"L.inv(b₁) ∈ L.carrier",
								By(in, field.InvIn.Read(L)))
							invEq := c.Have(
								"and inverts it",
								"L.inv(b₁) * b₁ = L.one",
								By(in, nonzero, field.MulLeftInverseOn.Read(L)))
							ratio := c.Have(
								"so c₁ is c₂ scaled by inv(b₁) * b₂",
								"c₁ = L.inv(b₁) * b₂ * c₂",
								ByArith(field.RingOn.Read(L), in, invIn, Scaled(c.Term("L.inv(b₁)"), pair[4]), Scaled(c1, invEq)))
							factor := c.Have(
								"a scalar in M",
								"L.inv(b₁) * b₂ ∈ M",
								By(in, subM, field.SubfieldMul, field.SubfieldInv))
							c1InN := c.Have(
								"c₁ lies in N",
								"c₁ ∈ N",
								BySets(in))
							single := c.Have(
								"{c₂} lies in N",
								"{c₂} ⊆ N",
								BySets(in))
							missing := c.Have(
								"c₁ is not c₂",
								"c₁ ∉ {c₂}",
								BySets(apart))
							lineC2 := c.TermAs[Set[A]]("{c₂}")
							subspace := c.Have(
								"the M-span of c₂ is a subspace of N",
								"submodule(«scalarsOn»(M), «vectorsOn»(N), module_span(«scalarsOn»(M), «vectorsOn»(N), {c₂}))",
								By(single, submodule.SpanSubmodule.Read(overMN)))
							own := c.Have(
								"containing c₂",
								"c₂ ∈ module_span(«scalarsOn»(M), «vectorsOn»(N), {c₂})",
								BySets(submodule.SubsetSpan.At(rM, vN, lineC2)))
							spanned := c.Have(
								"so c₁ lies in the M-span of c₂",
								"c₁ ∈ module_span(«scalarsOn»(M), «vectorsOn»(N), {c₂})",
								By(
									ratio,
									submodule.SubmoduleSmul.Read(subspace).At(
										proof.MemberOf(c.TermAs[A]("L.inv(b₁) * b₂"), factor), proof.MemberOf(c2, own))))
							pairInC := c.Have(
								"{c₁, c₂} lies in C",
								"{c₁, c₂} ⊆ C",
								BySets(pair[1], pair[3]))
							pairFree := c.Have(
								"so {c₁, c₂} is independent over M",
								"module_independent(«scalarsOn»(M), «vectorsOn»(N), {c₁, c₂})",
								By(
									indC,
									pairInC,
									linear_independence.IndependentSubset.At(rM, vN, C, c.TermAs[Set[A]]("{c₁, c₂}"))))
							inverse := c.TermAs[Fun[A, A]]("L.inv")
							scalarsM := c.Have(
								"M, a subfield, is a field under L's operations, with L's inverse",
								"ring_subfield(«scalarsOn»(M), L.inv, M)",
								By(subM, field.SubfieldRingSubfield.Read(L).At(M, M)))
							c.Show(
								"which C's independence over M forbids",
								By(
									spanned,
									single,
									missing,
									pairFree,
									scalarsM,
									linear_independence.IndependentInsertIff.Read(overMN).At(
										inverse, lineC2, proof.MemberOf(c1, c1InN))))
						})
				}))
			sized := a.Have(
				"so there are card(B) * card(C) products",
				"has_size(«towerProducts», card(B) * card(C))",
				By(
					distinct,
					finB,
					finC,
					cardinality.FiniteHasSize.At(B),
					cardinality.FiniteHasSize.At(C),
					cardinality.HasSizeProductImage.At(
						a.TermAs[Op[A]]("L.mul"), B, C, a.TermAs[Nat]("card(B)"), a.TermAs[Nat]("card(C)"))))

			closedN := a.Have(
				"N is closed under the product",
				"∀x y:A. x ∈ N ∧ y ∈ N ⇒ x * y ∈ N",
				By(subN, field.SubfieldMul))
			productsInN := a.Have(
				"the products lie in N",
				"«towerProducts» ⊆ N",
				BySets(bInM, mInN, cInN, closedN))

			cross := a.TermAs[Set[Prod[A, A]]]("set_cross(C, B)")
			g := a.TermAs[Fun[Prod[A, A], A]]("λp:prod(A, A). snd(p) * fst(p)")
			pairsApart := a.Have(
				"distinct pairs (c, b) give distinct products b * c",
				Statement{
					Binders: "∀p q:prod(A, A).",
					Hypotheses: []string{
						"p ∈ set_cross(C, B)",
						"q ∈ set_cross(C, B)",
						"snd(p) * fst(p) = snd(q) * fst(q)",
					},
					Conclusion: "p = q",
				},
				Derive(func(b *Argument) {
					p, q := b.FixAs[Prod[A, A]](), b.FixAs[Prod[A, A]]()
					hpq := b.Conjuncts(
						b.Assume(),
						"p lies in C × B",
						"q lies in C × B",
						"their products agree")
					coordinates := b.Have(
						"the coordinates lie in C and B",
						"fst(p) ∈ C ∧ snd(p) ∈ B ∧ fst(q) ∈ C ∧ snd(q) ∈ B",
						By(hpq[0], hpq[1], set_product.InCrossProjections))
					same := b.Have(
						"so they agree",
						"snd(p) = snd(q) ∧ fst(p) = fst(q)",
						By(
							coordinates,
							hpq[2],
							distinct.At(b.Term("snd(p)"), b.Term("snd(q)"), b.Term("fst(p)"), b.Term("fst(q)"))))
					b.Show(
						"and so do the pairs",
						By(same, pairs.PairEta.At(p), pairs.PairEta.At(q)))
				}))
			oneToOne := a.Have(
				"(c, b) ↦ b * c is one-to-one on C × B",
				"injective_on(set_cross(C, B), λp:prod(A, A). snd(p) * fst(p))",
				By(pairsApart, functions.InjectiveOnDef))
			forward := a.Have(
				"each pair maps to a product",
				"∀p:prod(A, A). p ∈ set_cross(C, B) ⇒ snd(p) * fst(p) ∈ «towerProducts»",
				Derive(func(b *Argument) {
					b.FixAs[Prod[A, A]]()
					inCross := b.Assume()
					coordinates := b.Have(
						"its coordinates lie in C and B",
						"fst(p) ∈ C ∧ snd(p) ∈ B",
						By(inCross, set_product.InCrossProjections))
					b.Show(
						"so its product is one of the products",
						BySets(coordinates))
				}))
			backward := a.Have(
				"each product b * c is the image of (c, b)",
				"∀b c:A. b ∈ B ∧ c ∈ C ⇒ b * c ∈ image(λp:prod(A, A). snd(p) * fst(p), set_cross(C, B))",
				Derive(func(d *Argument) {
					b, c := d.FixAs[A](), d.FixAs[A]()
					in := d.Assume()
					d.Show(
						"it is the image of the pair (c, b) of C × B",
						By(
							in,
							set_image.FunInImage.At(g, cross, d.TermAs[Prod[A, A]]("(c, b)")),
							set_product.InCross.At(C, B, c, b),
							pairs.Fst.At(c, b),
							pairs.Snd.At(c, b)))
				}))
			imageIsProducts := a.Have(
				"the image of C × B is the set of products",
				"image(λp:prod(A, A). snd(p) * fst(p), set_cross(C, B)) = «towerProducts»",
				BySets(forward, backward))
			finCross := a.Have(
				"C × B is finite",
				"finite(set_cross(C, B))",
				By(finC, finB, finite_set.FiniteProduct.At(C, B)))

			vanishing := a.Have(
				"a vanishing K-combination of products has zero coefficients",
				"∀T:set(A). ∀a:(A → A). "+
					"    finite(T) ∧ "+
					"    T ⊆ «towerProducts» ∧ "+
					"    (∀x:A. x ∈ T ⇒ a(x) ∈ K) ∧ "+
					"    module_sum(L.add, L.zero, T, λx:A. a(x) * x) = L.zero ⇒ "+
					"    ∀x:A. x ∈ T ⇒ a(x) = L.zero",
				Derive(func(d *Argument) {
					T, coefficient := d.FixAs[Set[A]](), d.FixAs[Fun[A, A]]()
					hT := d.Conjuncts(
						d.Assume(),
						"T is finite",
						"T lies among the products",
						"the coefficients lie in K",
						"the combination vanishes")
					extension := d.Let("a'", d.Term("λy:A. COND(y ∈ T, a(y), L.zero)"))
					values := d.Have(
						"a' is a on T and zero off T",
						"∀y:A. (y ∈ T ⇒ a'(y) = a(y)) ∧ (y ∉ T ⇒ a'(y) = L.zero)",
						extension.Rw(),
						d.ForEach(func(y *Expr[A]) Action { return Basic() }))
					inK := d.Have(
						"a' takes its values in K",
						"∀y:A. a'(y) ∈ K",
						Derive(func(e *Argument) {
							e.FixAs[A]()
							e.Cases(e.Term("y ∈ T"))
							e.When(
								"on T, a'(y) = a(y) lies in K",
								func(f *Argument, inT Fact) {
									f.Show(
										"a(y) ∈ K",
										By(Normalized, values, inT, hT[2]))
								})
							e.Otherwise(
								"off T, a'(y) = zero lies in K",
								func(f *Argument, outT Fact) {
									f.Show(
										"zero ∈ K",
										By(Normalized, values, outT, subK, field.SubfieldZero))
								})
						}))
					finP := d.Have(
						"there are finitely many products",
						"finite(«towerProducts»)",
						By(sized, cardinality.HasSizeDef.At(products, d.TermAs[Nat]("card(B) * card(C)"))))
					overP := d.Have(
						"read over all the products, the combination still vanishes",
						"module_sum(L.add, L.zero, «towerProducts», λy:A. a'(y) * y) = L.zero",
						extension.Rw(),
						CalcEq(
							Leg(
								d.Term("module_sum(L.add, L.zero, T, λy:A. a(y) * y)"),
								"a' is a extended by zero, so the terms off T add nothing",
								By(
									finP,
									hT[1],
									productsInN,
									hT[2],
									linear_independence.CombinationExtendByZero.Read(overKN).At(T, products, coefficient))),
							FinalLeg(
								"which vanishes",
								By(hT[3])),
						))
					termsInN := d.Have(
						"each a'(y) * y with y a product lies in N",
						"∀y:A. y ∈ «towerProducts» ⇒ a'(y) * y ∈ N",
						By(inK, productsInN, module.SmulIn.Read(overKN), set_basic.SubsetDef))
					termsInM := d.Have(
						"each a'(b * c) * b lies in M",
						"∀c b:A. b ∈ B ⇒ a'(b * c) * b ∈ M",
						Derive(func(e *Argument) {
							e.FixAs[A]()
							e.FixAs[A]()
							inB := e.Assume()
							scalars := e.Have(
								"a scalar of K times a vector of M",
								"a'(b * c) ∈ K ∧ b ∈ M",
								BySets(inK, inB, bInM))
							e.Show(
								"lies in M",
								By(scalars, module.SmulIn.Read(overKM)))
						}))
					innerInM := d.Have(
						"each inner sum lies in M",
						"∀c:A. module_sum(L.add, L.zero, B, λb:A. a'(b * c) * b) ∈ M",
						Derive(func(e *Argument) {
							e.FixAs[A]()
							e.Show(
								"a finite sum of vectors of M",
								By(
									finB,
									termsInM,
									module.ModuleSumIn.Read(overKM).At(B, e.TermAs[Fun[A, A]]("λb:A. a'(b * c) * b"))))
						}))
					regroup := d.Have(
						"each inner sum, times c, is the c-part of the double sum",
						Statement{
							Binders: "∀c:A.",
							Hypotheses: []string{
								"c ∈ C",
							},
							Conclusion: "module_sum(L.add, L.zero, B, λb:A. a'(b * c) * b) * c = " +
								"module_sum(L.add, L.zero, B, λb:A. a'(b * c) * (b * c))",
						},
						Derive(func(e *Argument) {
							c := e.FixAs[A]()
							inC := e.Assume()
							cN := e.Have(
								"c lies in N",
								"c ∈ N",
								BySets(inC, cInN))
							termwise := e.Have(
								"termwise by associativity",
								"∀b:A. b ∈ B ⇒ a'(b * c) * b * c = a'(b * c) * (b * c)",
								Derive(func(f *Argument) {
									f.FixAs[A]()
									inB := f.Assume()
									inL := f.Have(
										"a'(b * c), b and c lie in L",
										"a'(b * c) ∈ L.carrier ∧ b ∈ L.carrier ∧ c ∈ L.carrier",
										BySets(inK, inB, inC, bInM, cInN, kInM, mInL, nInL))
									f.Show(
										"in the ring L",
										ByArith(field.RingOn.Read(L), inL))
								}))
							e.Show(
								"c distributes over the inner sum",
								CalcEq(
									Leg(
										e.Term("module_sum(L.add, L.zero, B, λb:A. a'(b * c) * b * c)"),
										"multiplying by c distributes over the sum",
										By(
											finB,
											termsInM,
											module.ModuleSumSmulRight.Read(overMN).At(
												B, e.TermAs[Fun[A, A]]("λb:A. a'(b * c) * b"), proof.MemberOf(c, cN)))),
									FinalLeg(
										"and regroups termwise",
										By(
											termwise,
											module.ModuleSumCongruence.At(add, zero, B,
												e.TermAs[Fun[A, A]]("λb:A. a'(b * c) * b * c"), e.TermAs[Fun[A, A]]("λb:A. a'(b * c) * (b * c)")))),
								))
						}))
					crossTerms := d.Have(
						"each a'(b * c) * (b * c) lies in N",
						"∀c b:A. c ∈ C ∧ b ∈ B ⇒ a'(b * c) * (b * c) ∈ N",
						Derive(func(e *Argument) {
							e.FixAs[A]()
							e.FixAs[A]()
							in := e.Assume()
							product := e.Have(
								"b * c is one of the products",
								"b * c ∈ «towerProducts»",
								BySets(in))
							e.Show(
								"so its term lies in N",
								By(product, termsInN))
						}))
					pairTerms := d.Have(
						"and so does each term indexed by a pair",
						"∀p:prod(A, A). p ∈ set_cross(C, B) ⇒ a'(snd(p) * fst(p)) * (snd(p) * fst(p)) ∈ N",
						By(crossTerms, set_product.InCrossProjections))
					extendedTerms := d.TermAs[Fun[A, A]]("λy:A. a'(y) * y")
					total := d.Have(
						"grouped by c, the combination still vanishes",
						"module_sum(L.add, L.zero, C, λc:A. module_sum(L.add, L.zero, B, λb:A. a'(b * c) * b) * c) = "+
							"L.zero",
						CalcEq(
							Leg(
								d.Term(
									"module_sum(L.add, L.zero, C, λc:A. module_sum(L.add, L.zero, B, λb:A. a'(b * c) * (b * c)))"),
								"each c-part regroups",
								By(
									regroup,
									module.ModuleSumCongruence.At(add, zero, C,
										d.TermAs[Fun[A, A]]("λc:A. module_sum(L.add, L.zero, B, λb:A. a'(b * c) * b) * c"),
										d.TermAs[Fun[A, A]]("λc:A. module_sum(L.add, L.zero, B, λb:A. a'(b * c) * (b * c))")))),
							Leg(
								d.Term(
									"module_sum(L.add, "+
										"    L.zero, "+
										"    set_cross(C, B), "+
										"    λp:prod(A, A). a'(snd(p) * fst(p)) * (snd(p) * fst(p)))"),
								"a double sum is a sum over pairs",
								By(
									finC,
									finB,
									crossTerms,
									module.ModuleSumCross.Read(overKN).At(
										C, B, d.TermAs[Fun2[A, A, A]]("λc:A. λb:A. a'(b * c) * (b * c)")))),
							Leg(
								d.Term(
									"module_sum(L.add, "+
										"    L.zero, "+
										"    image(λp:prod(A, A). snd(p) * fst(p), set_cross(C, B)), "+
										"    λy:A. a'(y) * y)"),
								"the pairs index the products one-to-one",
								By(finCross, oneToOne, pairTerms, module.ModuleSumImage.Read(overKN).At(cross, g, extendedTerms))),
							Leg(
								d.Term("module_sum(L.add, L.zero, «towerProducts», λy:A. a'(y) * y)"),
								"the image is the set of products",
								By(imageIsProducts)),
							FinalLeg(
								"which vanishes",
								By(overP)),
						))
					innerZero := d.Have(
						"so each inner sum is zero, C being independent over M",
						"∀c:A. c ∈ C ⇒ module_sum(L.add, L.zero, B, λb:A. a'(b * c) * b) = L.zero",
						By(
							finC,
							set_order.SubsetRefl.At(C),
							innerInM,
							total,
							cFree.At(C, d.TermAs[Fun[A, A]]("λc:A. module_sum(L.add, L.zero, B, λb:A. a'(b * c) * b)"))))
					allZero := d.Have(
						"so each a'(b * c) is zero, B being independent over K",
						"∀c b:A. c ∈ C ∧ b ∈ B ⇒ a'(b * c) = L.zero",
						Derive(func(e *Argument) {
							e.FixAs[A]()
							e.FixAs[A]()
							in := e.Conjuncts(
								e.Assume(),
								"c lies in C",
								"b lies in B")
							e.Show(
								"by B's independence over K",
								By(
									finB,
									set_order.SubsetRefl.At(B),
									inK,
									in[0],
									in[1],
									innerZero,
									bFree.At(B, e.TermAs[Fun[A, A]]("λb:A. a'(b * c)"))))
						}))
					x := d.FixAs[A]()
					inT := d.Assume()
					b, c, factored := d.Obtain2As[A, A](
						"x is a product b * c",
						"∃b c:A. x = b * c ∧ b ∈ B ∧ c ∈ C",
						BySets(hT[1], inT))
					d.Show(
						"so a(x) = a'(b * c) = zero",
						By(Normalized, factored, inT, values.At(x), allZero.At(c, b)))
				}))
			independent := a.Have(
				"so the products are independent over K",
				"module_independent(«scalarsOn»(K), «vectorsOn»(N), «towerProducts»)",
				By(productsInN, vanishing, linear_independence.ModuleIndependentDef))
			a.Show(
				"the products are independent over K, card(B) * card(C) of them",
				By(independent, sized))
		}),
})}

// TowerBasis — finite bases multiply: a finite basis B of M over K and a
// finite basis C of N over M give the card(B) * card(C) products b * c as
// a basis of N over K, since they span N (TowerSpan) and are independent
// and distinct (TowerIndependent).
var TowerBasis = towerBasisThm{family.Add(registry.ProofEntry{
	Name: "TowerBasis",
	Key:  "prop_e2da7d28e55a5973",
	Reading: "finite(B) and finite(C) are load-bearing for the count: infinite " +
		"bases multiply to a basis as well, but has_size holds of no infinite set.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀K M N B C:set(A).",
		Hypotheses: []string{
			"subfield(L, K)",
			"subfield(L, M)",
			"subfield(L, N)",
			"K ⊆ M",
			"M ⊆ N",
			"module_basis(«scalarsOn»(K), «vectorsOn»(M), B)",
			"module_basis(«scalarsOn»(M), «vectorsOn»(N), C)",
			"finite(B)",
			"finite(C)",
		},
		Conclusion: "module_basis(«scalarsOn»(K), «vectorsOn»(N), «towerProducts») ∧ " +
			"has_size(«towerProducts», card(B) * card(C))",
	},
		func(a *Argument, L field.FieldFact[on.L], K, M, N, B, C *Expr[Set[A]], tower Fact) {
			h := a.Conjuncts(
				tower,
				"K is a subfield",
				"M is a subfield",
				"N is a subfield",
				"K lies in M",
				"M lies in N",
				"B is a basis of M over K",
				"C is a basis of N over M",
				"B is finite",
				"C is finite")
			subK, subM, subN, kInM, mInN, basisB, basisC, finB, finC :=
				h[0], h[1], h[2], h[3], h[4], h[5], h[6], h[7], h[8]
			partsB := a.Conjuncts(
				a.Unfolded(basisB, linear_independence.ModuleBasisDef),
				"B is independent over K",
				"B spans M over K")
			partsC := a.Conjuncts(
				a.Unfolded(basisC, linear_independence.ModuleBasisDef),
				"C is independent over M",
				"C spans N over M")
			indB, spanB, indC, spanC := partsB[0], partsB[1], partsC[0], partsC[1]
			spanning := a.Have(
				"the products span N over K",
				"module_span(«scalarsOn»(K), «vectorsOn»(N), «towerProducts») = N",
				By(subK, subM, subN, kInM, mInN, spanB, spanC, TowerSpan.Read(L).At(K, M, N, B, C)))
			independent := a.Have(
				"they are independent over K, card(B) * card(C) of them",
				"module_independent(«scalarsOn»(K), «vectorsOn»(N), «towerProducts») ∧ "+
					"has_size(«towerProducts», card(B) * card(C))",
				By(
					subK,
					subM,
					subN,
					kInM,
					mInN,
					finB,
					finC,
					indB,
					indC,
					TowerIndependent.Read(L).At(K, M, N, B, C)))
			a.Show(
				"so they are a basis of N over K, card(B) * card(C) of them",
				By(independent, spanning, linear_independence.ModuleBasisDef))
		}),
})}

// BasisDegree — a finite basis gives the degree: M with a finite basis B
// over K is finite over K, and [M:K], the dimension, is card(B).
var BasisDegree = basisDegreeThm{family.Add(registry.ProofEntry{
	Name: "BasisDegree",
	Key:  "prop_74005858b5b30e85",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀K M B:set(A).",
		Hypotheses: []string{
			"subfield(L, K)",
			"subfield(L, M)",
			"K ⊆ M",
			"finite(B)",
			"module_basis(«scalarsOn»(K), «vectorsOn»(M), B)",
		},
		Conclusion: "finite_extension(L, K, M) ∧ extension_degree(L, K, M) = card(B)",
	},
		func(a *Argument, L field.FieldFact[on.L], K, M, B *Expr[Set[A]], h Fact) {
			parts := a.Conjuncts(
				h,
				"K is a subfield",
				"M is a subfield",
				"K lies in M",
				"B is finite",
				"B is a basis of M over K")
			subK, subM, kInM, finB, basis := parts[0], parts[1], parts[2], parts[3], parts[4]
			space := a.Have(
				"M is a vector space over K",
				"module_on(«scalarsOn»(K), «vectorsOn»(M))",
				By(subK, subM, kInM, ExtensionModuleOn.Read(L).At(K, M)))
			inv := a.TermAs[Fun[A, A]]("L.inv")
			fieldK := a.Have(
				"K, a subfield, is a field under L's operations, with L's inverse",
				"ring_subfield(«scalarsOn»(K), L.inv, K)",
				By(subK, field.SubfieldRingSubfield.Read(L).At(K, K)))
			finite := a.Have(
				"M has the finite basis B over K, so it is finite over K",
				"finite_extension(L, K, M)",
				Unfold(FiniteExtensionDef),
				Unfold(module_dimension.FiniteDimensionalDef),
				Derive(func(b *Argument) {
					b.Take(B)
					b.Show(
						"B is a finite basis",
						By(finB, basis))
				}))
			degree := a.Have(
				"[M:K], the dimension of M over K, is the size of B",
				"extension_degree(L, K, M) = card(B)",
				Simp(Fwd(ExtensionDegreeDef)),
				By(finB, basis, fieldK, module_dimension.DimBasis.Read(space).At(inv, B)))
			a.Show(
				"M is finite over K, of degree card(B)",
				By(finite, degree))
		}),
})}

// ExtensionOverItself — a subfield is a finite extension of itself, of
// degree one: one is a basis of K over itself, K's regular module being
// the field's vectors restricted to K, and that basis has one member.
var ExtensionOverItself = extensionOverItselfThm{family.Add(registry.ProofEntry{
	Name: "ExtensionOverItself",
	Key:  "prop_86ecf3d3d4501481",
	Build: family.Theorem(Statement{
		Binders:    "∀L:field_on(A). ∀K:set(A).",
		Hypotheses: []string{"subfield(L, K)"},
		Conclusion: "finite_extension(L, K, K) ∧ extension_degree(L, K, K) = 1",
	},
		func(a *Argument, L field.FieldFact[on.L], K *Expr[Set[A]], subK Fact) {
			one := a.TermAs[A]("L.one")
			fieldOnK := a.Have(
				"K is a field under L's operations",
				"field_on(restrict_field(L, K))",
				By(subK, field.SubfieldFieldOn.Read(L).At(K)))
			ringK := a.Have(
				"so its scalar ring is commutative",
				"comm_ring_on(«scalarsOn»(K))",
				Simp(Fwd(field.RestrictFieldRing)),
				By(field.RingOn.Read(fieldOnK)))
			fieldRing := a.TermAs[module_record.RingOps[A]]("field_ring(L)")
			basisK := a.Have(
				"one is a basis of K over itself, K's regular module being the ambient one restricted to K",
				"module_basis(«scalarsOn»(K), «vectorsOn»(K), {L.one})",
				By(
					Normalized,
					module_record.RegularModuleRestrict.At(fieldRing, K),
					linear_independence.RegularModuleBasis.Read(ringK)))
			a.Show(
				"so K is finite over itself, of degree the size of {one}",
				By(
					Normalized,
					subK,
					basisK,
					set_order.SubsetRefl.At(K),
					finite_set.FiniteSing.At(one),
					cardinality.CardSing.At(one),
					BasisDegree.Read(L).At(K, K, a.TermAs[Set[A]]("{L.one}"))))
		}),
})}

// TowerLaw — degrees multiply in a tower: a finite basis B of M over K
// and a finite basis C of N over M multiply to a finite basis of N over
// K with card(B) · card(C) members (TowerBasis), and each degree is the
// size of a finite basis (BasisDegree), so N is finite over K and
// [N:K] = card(B) · card(C) = [M:K] · [N:M].
var TowerLaw = towerLawThm{family.Add(registry.ProofEntry{
	Name: "TowerLaw",
	Key:  "prop_af3927c3d68ce8b9",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀K M N:set(A).",
		Hypotheses: []string{
			"subfield(L, K)",
			"subfield(L, M)",
			"subfield(L, N)",
			"K ⊆ M",
			"M ⊆ N",
			"finite_extension(L, K, M)",
			"finite_extension(L, M, N)",
		},
		Conclusion: "finite_extension(L, K, N) ∧ " +
			"extension_degree(L, K, N) = extension_degree(L, K, M) * extension_degree(L, M, N)",
	},
		func(a *Argument, L field.FieldFact[on.L], K, M, N *Expr[Set[A]], tower Fact) {
			_, basisB := a.ObtainAs[Set[A]](
				"M has a finite basis B over K",
				"∃B:set(A). finite(B) ∧ module_basis(«scalarsOn»(K), «vectorsOn»(M), B)",
				By(tower, FiniteExtensionDef, module_dimension.FiniteDimensionalDef))
			_, basisC := a.ObtainAs[Set[A]](
				"and N has a finite basis C over M",
				"∃C:set(A). finite(C) ∧ module_basis(«scalarsOn»(M), «vectorsOn»(N), C)",
				By(tower, FiniteExtensionDef, module_dimension.FiniteDimensionalDef))
			products := a.TermAs[Set[A]]("«towerProducts»")
			productBasis := a.Have(
				"the products b * c are a basis of N over K with card(B) * card(C) members",
				"module_basis(«scalarsOn»(K), «vectorsOn»(N), «towerProducts») ∧ "+
					"has_size(«towerProducts», card(B) * card(C))",
				By(tower, basisB, basisC, TowerBasis.Read(L)))
			counted := cardinality.HasSizeDef.At(products, a.TermAs[Nat]("card(B) * card(C)"))
			kInN := a.Have(
				"K lies in N",
				"K ⊆ N",
				By(tower, set_order.SubsetTrans))
			degreeM := a.Have(
				"M is finite over K, [M:K] the size of B",
				"finite_extension(L, K, M) ∧ extension_degree(L, K, M) = card(B)",
				By(tower, basisB, BasisDegree.Read(L)))
			degreeN := a.Have(
				"N is finite over M, [N:M] the size of C",
				"finite_extension(L, M, N) ∧ extension_degree(L, M, N) = card(C)",
				By(tower, basisC, BasisDegree.Read(L)))
			degreeK := a.Have(
				"N is finite over K, [N:K] the size of the products",
				"finite_extension(L, K, N) ∧ extension_degree(L, K, N) = card(«towerProducts»)",
				By(tower, kInN, productBasis, counted, BasisDegree.Read(L)))
			degree := a.Have(
				"so the degrees multiply",
				"extension_degree(L, K, N) = extension_degree(L, K, M) * extension_degree(L, M, N)",
				CalcEq(
					Leg(
						a.Term("card(«towerProducts»)"),
						"[N:K] is the size of the finite basis of products",
						By(degreeK)),
					Leg(
						a.Term("card(B) * card(C)"),
						"the products number card(B) * card(C)",
						By(productBasis, counted)),
					FinalLeg(
						"and the two factors are [M:K] and [N:M]",
						By(Normalized, degreeM, degreeN)),
				))
			a.Show(
				"so N is finite over K, of degree [M:K] · [N:M]",
				By(degreeK, degree))
		}),
})}

// TowerFinite — in a tower whose ends form a finite extension, so does
// each step: M is a K-submodule of N, and a finite K-spanning set of N
// still spans it over M.
var TowerFinite = towerFiniteThm{family.Add(registry.ProofEntry{
	Name: "TowerFinite",
	Key:  "prop_1016ba3964b056ce",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀K M N:set(A).",
		Hypotheses: []string{
			"subfield(L, K)",
			"subfield(L, M)",
			"subfield(L, N)",
			"K ⊆ M",
			"M ⊆ N",
			"finite_extension(L, K, N)",
		},
		Conclusion: "finite_extension(L, K, M) ∧ finite_extension(L, M, N)",
		Abbrev: Abbrev{
			{Name: "spanOverK", Text: "module_span(«scalarsOn»(K), «vectorsOn»(N))"},
			{Name: "spanOverM", Text: "module_span(«scalarsOn»(M), «vectorsOn»(N))"},
		},
	},
		func(a *Argument, L field.FieldFact[on.L], K, M, N *Expr[Set[A]], tower Fact) {
			h := a.Conjuncts(
				tower,
				"K is a subfield",
				"M is a subfield",
				"N is a subfield",
				"K lies in M",
				"M lies in N",
				"N is finite over K")
			subK, subM, subN, kInM, mInN, finiteN := h[0], h[1], h[2], h[3], h[4], h[5]
			rK, rM :=
				a.TermAs[module_record.RingOps[A]]("«scalarsOn»(K)"),
				a.TermAs[module_record.RingOps[A]]("«scalarsOn»(M)")
			vN := a.TermAs[module_record.ModuleOps[A, A]]("«vectorsOn»(N)")
			whole := a.TermAs[module_record.ModuleOps[A, A]]("regular_module(field_ring(L))")
			inv := a.TermAs[Fun[A, A]]("L.inv")
			kInN := a.Have(
				"K lies in N through M",
				"K ⊆ N",
				By(kInM, mInN, set_order.SubsetTrans.At(K, M, N)))
			overK := a.Have(
				"N is a vector space over K",
				"module_on(«scalarsOn»(K), «vectorsOn»(N))",
				By(subK, subN, kInN, ExtensionModuleOn.Read(L).At(K, N)))
			overM := a.Have(
				"N is a vector space over M",
				"module_on(«scalarsOn»(M), «vectorsOn»(N))",
				By(subM, subN, mInN, ExtensionModuleOn.Read(L).At(M, N)))
			fieldK := a.Have(
				"K is a field of scalars with L's inverse",
				"ring_subfield(«scalarsOn»(K), L.inv, K)",
				By(subK, field.SubfieldRingSubfield.Read(L).At(K, K)))
			fieldM := a.Have(
				"M is a field of scalars with the same inverse",
				"ring_subfield(«scalarsOn»(M), L.inv, M)",
				By(subM, field.SubfieldRingSubfield.Read(L).At(M, M)))
			finiteDim := a.Have(
				"N has finite dimension over K",
				"finite_dimensional(«scalarsOn»(K), «vectorsOn»(N))",
				By(finiteN, FiniteExtensionDef.At(a.TermAs[FieldOps[A]]("L"), K, N)))
			middle := a.Have(
				"M is a K-submodule of N",
				"submodule(«scalarsOn»(K), «vectorsOn»(N), M)",
				By(subK, subM, kInM, mInN, SubfieldSubmodule.Read(L).At(K, M, N)))
			finiteLower := a.Have(
				"M, a submodule of finite-dimensional N over K, is finite over K",
				"finite_extension(L, K, M)",
				By(
					Normalized,
					fieldK,
					finiteDim,
					middle,
					module_dimension.SubmoduleDim.Read(overK).At(inv, M),
					module_record.RestrictModuleTwice.At(whole, N, M),
					FiniteExtensionDef.At(a.TermAs[FieldOps[A]]("L"), K, M)))
			finiteUpper := a.Have(
				"N remains finite-dimensional when the scalars grow from K to M",
				"finite_extension(L, M, N)",
				Derive(func(b *Argument) {
					S, spanningK := b.ObtainAs[Set[A]](
						"choose a finite K-spanning set of N",
						"∃S:set(A). finite(S) ∧ S ⊆ N ∧ «spanOverK»(S) = N",
						By(fieldK, finiteDim, module_dimension.FiniteDimensionalSpanning.Read(overK).At(inv)))
					spansM := b.Have(
						"the K-span of S is N, so the M-span of S is the M-span of N, which is N",
						"«spanOverM»(S) = N",
						By(
							Normalized,
							spanningK,
							kInM,
							submodule.SpanOfSubringSpan.Read(overM).At(rK, S),
							submodule.CarrierSubmodule.Read(overM),
							submodule.SpanOfSubmodule.At(rM, vN, N)))
					finiteSpanning := b.Have(
						"the same finite set supplies a spanning witness over M",
						"∃T:set(A). finite(T) ∧ T ⊆ N ∧ «spanOverM»(T) = N",
						Witness(S),
						By(spanningK, spansM))
					b.Show(
						"a finite spanning set makes N finite-dimensional over M",
						By(
							finiteSpanning,
							fieldM,
							module_dimension.FiniteDimensionalSpanning.Read(overM).At(inv),
							FiniteExtensionDef.At(a.TermAs[FieldOps[A]]("L"), M, N)))
				}))
			a.Show(
				"both steps of the tower are finite",
				By(finiteLower, finiteUpper))
		}),
})}

// DegreeOneIff — a finite extension has degree one exactly when it is
// the smaller field itself: K has dimension one over itself, so a
// degree-one extension has the same dimension as its submodule K.
var DegreeOneIff = degreeOneIffThm{family.Add(registry.ProofEntry{
	Name: "DegreeOneIff",
	Key:  "prop_5025ee6bf155142",
	Reading: "finite_extension(L, K, M) is load-bearing for ⇒ only: the " +
		"degree of an infinite extension is an unspecified number that may be one.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀K M:set(A).",
		Hypotheses: []string{
			"subfield(L, K)",
			"subfield(L, M)",
			"K ⊆ M",
			"finite_extension(L, K, M)",
		},
		Conclusion: "extension_degree(L, K, M) = 1 ⇔ M = K",
	},
		func(a *Argument, L field.FieldFact[on.L], K, M *Expr[Set[A]], extension Fact) {
			h := a.Conjuncts(
				extension,
				"K is a subfield",
				"M is a subfield",
				"K lies in M",
				"M is finite over K")
			subK, subM, kInM, finiteM := h[0], h[1], h[2], h[3]
			whole := a.TermAs[module_record.ModuleOps[A, A]]("regular_module(field_ring(L))")
			inv := a.TermAs[Fun[A, A]]("L.inv")
			selfDegree := a.Have(
				"the extension K over itself has degree one",
				"extension_degree(L, K, K) = 1",
				By(subK, ExtensionOverItself.Read(L).At(K)))
			a.Iff()
			a.Forward(
				"degree one leaves no room beyond the submodule K",
				func(b *Argument, degreeOne Fact) {
					overK := b.Have(
						"M is a vector space over K",
						"module_on(«scalarsOn»(K), «vectorsOn»(M))",
						By(subK, subM, kInM, ExtensionModuleOn.Read(L).At(K, M)))
					finiteDim := b.Have(
						"M is finite-dimensional over K",
						"finite_dimensional(«scalarsOn»(K), «vectorsOn»(M))",
						By(finiteM, FiniteExtensionDef.At(b.TermAs[FieldOps[A]]("L"), K, M)))
					inside := b.Have(
						"K is a K-submodule of M",
						"submodule(«scalarsOn»(K), «vectorsOn»(M), K)",
						By(subK, set_order.SubsetRefl.At(K), kInM, SubfieldSubmodule.Read(L).At(K, K, M)))
					sameDimension := b.Have(
						"K as a submodule and M both have dimension one",
						"module_dim(«scalarsOn»(K), restrict_module(«vectorsOn»(M), K)) = "+
							"module_dim(«scalarsOn»(K), «vectorsOn»(M))",
						By(
							selfDegree,
							degreeOne,
							module_record.RestrictModuleTwice.At(whole, M, K),
							ExtensionDegreeDef.At(b.TermAs[FieldOps[A]]("L"), K, K),
							ExtensionDegreeDef.At(b.TermAs[FieldOps[A]]("L"), K, M)))
					b.Show(
						"a submodule of full dimension is the entire finite-dimensional space",
						By(
							Normalized,
							subK,
							field.SubfieldRingSubfield.Read(L).At(K, K),
							finiteDim,
							inside,
							sameDimension,
							module_dimension.SubmoduleDimEq.Read(overK).At(inv, K)))
				})
			a.Backward(
				"when M is K its degree is the self-degree",
				func(b *Argument, equal Fact) {
					b.Show(
						"the self-degree computation applies",
						By(Normalized, selfDegree, equal))
				})
		}),
})}

// IntermediateDegree — a field E between B and K, with K finite over B, is
// finite over B, of degree at most [K : B], and it is K when the degrees agree:
// E is a B-submodule of K, and a submodule of a finite-dimensional space is
// finite-dimensional, of no larger dimension, and the whole space at the same
// dimension.
var IntermediateDegree = intermediateDegreeThm{family.Add(registry.ProofEntry{
	Name: "IntermediateDegree",
	Key:  "prop_fb0804cc2334d827",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀B E K:set(A).",
		Hypotheses: []string{
			"subfield(L, B)",
			"subfield(L, E)",
			"subfield(L, K)",
			"B ⊆ E",
			"E ⊆ K",
			"finite_extension(L, B, K)",
		},
		Conclusion: "finite_extension(L, B, E) ∧ " +
			"extension_degree(L, B, E) ≤ extension_degree(L, B, K) ∧ " +
			"(extension_degree(L, B, E) = extension_degree(L, B, K) ⇒ E = K)",
	}, func(
		a *Argument,
		L field.FieldFact[on.L],
		B, E, K *Expr[Set[A]],
		BField, EField, KField, BInE, EInK, finite Fact,
	) {
		l := a.TermAs[FieldOps[A]]("L")
		inverse := a.TermAs[Fun[A, A]]("L.inv")
		_, RDef := a.LetAs[module_record.RingOps[A]]("R", "«scalarsOn»(B)")
		_, VDef := a.LetAs[module_record.ModuleOps[A, A]]("V", "«vectorsOn»(K)")
		BInK := a.Have(
			"B lies in K through E",
			"B ⊆ K",
			BySets(BInE, EInK))
		vectors := a.Have(
			"K is a vector space over B",
			"module_on(R, V)",
			By(Normalized, BField, KField, RDef, VDef, BInK, ExtensionModuleOn.Read(L).At(B, K)))
		finiteDimensional := a.Have(
			"K is finite dimensional over B",
			"finite_dimensional(R, V)",
			By(Normalized, finite, RDef, VDef, FiniteExtensionDef.At(l, B, K)))
		insideK := a.Have(
			"E is a submodule of K over B",
			"submodule(R, V, E)",
			By(Normalized, BField, EField, BInE, EInK, RDef, VDef, SubfieldSubmodule.Read(L).At(B, E, K)))
		scalarCarrier := a.Have(
			"R has carrier B",
			"R.carrier = B",
			Simp(Fwd(RDef), Fwd(module_record.RestrictRingDef), Fwd(module_record.RingCarrierDef)),
			Basic())
		scalarField := a.Have(
			"the scalars B, a subfield, are a field under the operations of R, with the inverse of L",
			"ring_subfield(R, L.inv, R.carrier)",
			scalarCarrier.Rw(),
			RDef.Rw(),
			By(BField, field.SubfieldRingSubfield.Read(L).At(B, B)))
		bounded := a.Have(
			"a submodule of a finite-dimensional space is finite dimensional, of no larger dimension",
			"finite_dimensional(R, restrict_module(V, E)) ∧ "+
				"module_dim(R, restrict_module(V, E)) ≤ module_dim(R, V)",
			By(
				scalarField,
				finiteDimensional,
				insideK,
				module_dimension.SubmoduleDim.Read(vectors).At(inverse, E)))
		restrictTwice := a.Have(
			"restricting V to E is restricting L to E",
			"restrict_module(V, E) = restrict_module(regular_module(field_ring(L)), E)",
			VDef.Rw(),
			Simp(
				Fwd(module_record.RestrictModuleDef),
				Fwd(module_record.ModAddDef),
				Fwd(module_record.ModZeroDef),
				Fwd(module_record.ModNegDef),
				Fwd(module_record.ModSmulDef)),
			Basic())
		carrier := a.Have(
			"V has carrier K",
			"V.carrier = K",
			Simp(Fwd(VDef), Fwd(module_record.RestrictModuleDef), Fwd(module_record.ModCarrierDef)),
			Basic())
		degreeBound := a.Have(
			"E is finite over B of degree at most [K : B]",
			"finite_extension(L, B, E) ∧ extension_degree(L, B, E) ≤ extension_degree(L, B, K)",
			Simp(Fwd(FiniteExtensionDef), Fwd(ExtensionDegreeDef)),
			By(Normalized, VDef, restrictTwice, RDef, bounded))
		equalDegree := a.Have(
			"equal degrees force E = K",
			"extension_degree(L, B, E) = extension_degree(L, B, K) ⇒ E = K",
			Derive(func(b *Argument) {
				equal := b.Assume()
				dimensions := b.Have(
					"the dimensions over B agree",
					"module_dim(R, restrict_module(V, E)) = module_dim(R, V)",
					By(
						Normalized,
						VDef,
						RDef,
						restrictTwice,
						equal,
						ExtensionDegreeDef.At(l, B, E),
						ExtensionDegreeDef.At(l, B, K)))
				b.Show(
					"a full-dimensional submodule is the whole space",
					By(
						Normalized,
						scalarField,
						carrier,
						finiteDimensional,
						insideK,
						dimensions,
						module_dimension.SubmoduleDimEq.Read(vectors).At(inverse, E)))
			}))
		a.Show(
			"collect the bound and the equality case",
			By(degreeBound, equalDegree))
	}),
})}

// FiniteEmbeddingOnto — an embedding of a finite extension into itself that
// fixes its base field is onto: its image has the full finite dimension.
var FiniteEmbeddingOnto = finiteEmbeddingOntoThm{family.Add(registry.ProofEntry{
	Name: "FiniteEmbeddingOnto",
	Key:  "prop_52d80fa5abdf6cf1",
	Build: family.Sections(Statement{
		Binders: "∀L:field_on(A). ∀K M:set(A). ∀f:(A → A).",
		Hypotheses: []string{
			"subfield(L, K)",
			"subfield(L, M)",
			"K ⊆ M",
			"finite_extension(L, K, M)",
			"ring_homomorphism(restrict_ring(field_ring(L), M), field_ring(L), f)",
			"∀x:A. x ∈ K ⇒ f(x) = x",
			"image(f, M) ⊆ M",
		},
		Conclusion: "image(f, M) = M",
	}, func(ctx *Script, headline string) *GoalStackNode {
		// A homomorphism of E into L fixing K is linear over K.
		baseLinear := ctx.Lemma(Statement{
			Binders: "∀L:field_on(A). ∀K E:set(A). ∀f:(A → A).",
			Hypotheses: []string{
				"subfield(L, K)",
				"subfield(L, E)",
				"K ⊆ E",
				"ring_homomorphism(restrict_ring(field_ring(L), E), field_ring(L), f)",
				"∀x:A. x ∈ K ⇒ f(x) = x",
			},
			Conclusion: "module_homomorphism(restrict_ring(field_ring(L), K), " +
				"    restrict_module(regular_module(field_ring(L)), E), " +
				"    regular_module(field_ring(L)), " +
				"    f)",
		}, func(
			a *Argument,
			L field.FieldFact[on.L],
			K *Expr[Set[A]],
			E *Expr[Set[A]],
			f *Arrow[A, A],
			kField, eField, nested, hom, fixesK Fact,
		) {
			a.Show(
				"f is additive and fixes the scalars in K, so it is K-linear",
				By(
					Normalized,
					ring_homomorphism.MapIn.Read(hom),
					ring_homomorphism.MapAdd.Read(hom),
					ring_homomorphism.MapMul.Read(hom),
					kField,
					eField,
					nested,
					fixesK,
					At(ExtensionModuleOn.Read(L), K, E),
					At(SubfieldScalars.Read(L), K),
					module_homomorphism.ModuleHomomorphismDef.At(
						a.TermAs[comm_ring.RingOps[A]]("restrict_ring(field_ring(L), K)"),
						a.TermAs[module_record.ModuleOps[A, A]]("restrict_module(regular_module(field_ring(L)), E)"),
						a.TermAs[module_record.ModuleOps[A, A]]("regular_module(field_ring(L))"),
						f),
					set_basic.SubsetDef))
		})
		return ctx.Theorem(headline, func(
			a *Argument,
			L field.FieldFact[on.L],
			K *Expr[Set[A]],
			M *Expr[Set[A]],
			f *Arrow[A, A],
			kField, mField, nested, finiteM, hom, fixesK, into Fact,
		) {
			I, IDef := a.LetAs[Set[A]]("I", "image(f, M)")
			R, RDef := a.LetAs[comm_ring.RingOps[A]]("R", "restrict_ring(field_ring(L), K)")
			W, WDef := a.LetAs[module_record.ModuleOps[A, A]]("W", "regular_module(field_ring(L))")
			V, VDef := a.LetAs[module_record.ModuleOps[A, A]]("V", "restrict_module(W, M)")
			scalarField := a.Have(
				"R with the inverse of L is a field on its carrier K",
				"ring_subfield(R, L.inv, R.carrier)",
				Derive(func(c *Argument) {
					c.Do(Simp(Fwd(RDef), Fwd(module_record.RestrictRingDef)))
					c.Do(By(
						Normalized,
						kField,
						module_record.RestrictRingDef,
						field.SubfieldRingSubfield.Read(L).At(K, K)))
				}))
			fieldM := a.Have(
				"M is a field under the operations of L",
				"field_on(restrict_field(L, M))",
				By(mField, field.SubfieldFieldOn.Read(L).At(M)))
			homM := a.Have(
				"f is a homomorphism of the field M into L",
				"ring_homomorphism(field_ring(restrict_field(L, M)), field_ring(L), f)",
				Simp(Rev(field.RestrictFieldRing)),
				By(hom))
			injective := a.Have(
				"f is injective on M, as every homomorphism of fields is",
				"injective_on(M, f)",
				By(
					L,
					homM,
					ring_homomorphism.FieldHomomorphismInjective.Read(fieldM).At(a.TermAs[FieldOps[A]]("L"), f)))
			finiteLinearEmbedding := a.Have(
				"the embedding is a linear map on a finite dimensional module",
				"module_homomorphism(R, V, W, f) ∧ finite_dimensional(R, V) ∧ module_on(R, V)",
				By(
					Normalized,
					fixesK,
					VDef,
					WDef,
					RDef,
					kField,
					mField,
					nested,
					finiteM,
					hom,
					At(baseLinear, a.TermAs[FieldOps[A]]("L"), K, M, f),
					At(FiniteExtensionDef, a.TermAs[FieldOps[A]]("L"), K, M),
					At(ExtensionModuleOn.Read(L), K, M)))
			imageRestriction := a.Have(
				"V has carrier M, and V and W restrict to the same module on the image",
				"V.carrier = M ∧ restrict_module(V, I) = restrict_module(W, I)",
				Derive(func(c *Argument) {
					c.Do(Simp(Fwd(VDef), Fwd(module_record.RestrictModuleDef)))
					c.Do(TrivialNormalized())
				}))
			embedding := a.Conjuncts(
				finiteLinearEmbedding,
				"f is K-linear",
				"M is finite dimensional over K",
				"M is a module over K")
			imageDimension := a.Have(
				"the image has the same finite dimension as the source",
				"finite_dimensional(R, restrict_module(W, I)) ∧ "+
					"module_dim(R, restrict_module(W, I)) = module_dim(R, V)",
				By(
					Normalized,
					scalarField,
					IDef,
					imageRestriction,
					finiteLinearEmbedding,
					injective,
					module_dimension.InjectiveImageDim.At(R, a.TermAs[Fun[A, A]]("L.inv"), V, W, f)))
			imageSubmodule := a.Have(
				"the image is a submodule of the ambient regular module",
				"submodule(R, W, I)",
				By(Normalized, module_homomorphism.ImageSubmodule.Read(embedding[0]), IDef, imageRestriction))
			imageInSource := a.Have(
				"the image is a submodule of the source module",
				"submodule(R, V, I)",
				By(Normalized, VDef, into, imageSubmodule, submodule.SubmoduleRestrict.At(R, W, M, I)))
			imageIsSource := a.Have(
				"a submodule of full dimension equals the source carrier",
				"I = V.carrier",
				By(
					scalarField,
					embedding[1],
					imageRestriction,
					imageDimension,
					imageInSource,
					At(module_dimension.SubmoduleDimEq.Read(embedding[2]), a.TermAs[Fun[A, A]]("L.inv"), I)))
			a.Show(
				"the image is the carrier M",
				By(Normalized, imageIsSource, imageRestriction))
		})
	}),
})}

// ExtensionDegreePositive — a finite extension has positive degree: the larger
// field holds one, which is not zero, so it is not the zero space.
var ExtensionDegreePositive = extensionDegreePositiveThm{family.Add(registry.ProofEntry{
	Name: "ExtensionDegreePositive",
	Key:  "prop_1beaae0a7f17f42a",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀K L:set(A).",
		Hypotheses: []string{
			"subfield(M, K)",
			"subfield(M, L)",
			"K ⊆ L",
			"finite_extension(M, K, L)",
		},
		Conclusion: "0 < extension_degree(M, K, L)",
	}, func(
		a *Argument,
		M field.FieldFact[on.M],
		K, L *Expr[Set[A]],
		subfieldK, subfieldL, inclusion, finite Fact,
	) {
		m := a.TermAs[FieldOps[A]]("M")
		space := a.Have(
			"L is a vector space over K",
			"module_on(restrict_ring(field_ring(M), K), restrict_module(regular_module(field_ring(M)), L))",
			By(subfieldK, subfieldL, inclusion, ExtensionModuleOn.Read(M).At(K, L)))
		nontrivial := a.Have(
			"L holds one, which is not zero",
			"L ≠ {M.zero}",
			BySets(field.OneNotZeroOn.Read(M), subfieldL, field.SubfieldOne.At(m, L)))
		a.Show(
			"a finite-dimensional space of dimension zero is the zero space",
			ByArith(
				nontrivial,
				subfieldK,
				finite,
				FiniteExtensionDef.At(m, K, L),
				field.SubfieldRingSubfield.Read(M).At(K, K),
				module_dimension.DimZero.Read(space).At(a.TermAs[Fun[A, A]]("M.inv")),
				ExtensionDegreeDef.At(m, K, L)))
	}),
})}
