// correspondence.go — the Galois correspondence: the subfields between K
// and a Galois extension and the subgroups of its automorphisms, each
// determining the other and reversing inclusion; restriction to a normal
// intermediate field, normal intermediate fields answering to normal
// subgroups; and the quotient by the automorphisms fixing such a field.

package galois_correspondence

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_automorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_extension"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/finite_group/finite_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group_isomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/quotient_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/symmetric_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_division"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_roots"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/separable_polynomial"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// permutationRestrictDef — `permutation_restrict(E, p)`: a permutation
// that moves no point outside E and agrees with p on E, chosen. When p
// carries E onto itself there is exactly one.
var permutationRestrictDef = permutationRestrictDefThm{family.Define(registry.DefEntry{
	Name:  "permutationRestrictDef",
	Key:   "prop_bb8089a8942a6363",
	Const: "permutation_restrict",
	Type:  "set(A) → permutation(A) → permutation(A)",
	Equations: []string{
		"∀E:set(A). ∀p:permutation(A). " +
			"    permutation_restrict(E, p) = " +
			"    εq:permutation(A). " +
			"        q ∈ symmetric_group(E) ∧ (∀x:A. x ∈ E ⇒ permutation_map(q, x) = permutation_map(p, x))",
	},
})}

// CorrespondenceFixed — an intermediate field of a Galois extension is
// the field fixed by the automorphisms fixing it: M is Galois over E as
// well, and the automorphisms of a finite Galois extension fix exactly
// its base.
var CorrespondenceFixed = correspondenceFixedThm{family.Add(registry.ProofEntry{
	Name: "CorrespondenceFixed",
	Key:  "prop_1c21bdfb786126fa",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀K E M:set(A).",
		Hypotheses: []string{
			"subfield(L, K)",
			"subfield(L, E)",
			"subfield(L, M)",
			"K ⊆ E",
			"E ⊆ M",
			"galois_over(L, K, M)",
		},
		Conclusion: "fixed_field(M, field_automorphisms(L, E, M)) = E",
	},
		func(a *Argument, L field.FieldFact[on.L], K, E, M *Expr[Set[A]], tower Fact) {
			galois := a.Have(
				"M is Galois over the intermediate field E",
				"galois_over(L, E, M)",
				By(tower, GaloisTower.Read(L).At(K, E, M)))
			finiteNormalSeparable := a.Unfolded(galois, GaloisOverDef)
			a.Show(
				"the automorphisms fixing E fix exactly E, M being finite and Galois over E",
				By(tower, finiteNormalSeparable, galois, GaloisIffFixed.Read(L).At(E, M)))
		}),
})}

// CorrespondenceAutomorphisms — a subgroup of the Galois group of a finite
// extension is the group fixing its fixed field, which lies between: this
// half of the Galois correspondence needs no Galois hypothesis. H is a group
// of permutations inside the finite Aut_K(M) (field_automorphism.GaloisGroupSubgroup),
// so it is finite, its fixed field F lies between K and M as every member of
// H fixes K, and Artin's theorem makes H the group fixing F.
var CorrespondenceAutomorphisms = correspondenceAutomorphismsThm{family.Add(registry.ProofEntry{
	Name: "CorrespondenceAutomorphisms",
	Key:  "prop_ee15c3d3a344a39e",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀K M:set(A). ∀H:set(permutation(A)).",
		Hypotheses: []string{
			"subfield(L, K)",
			"subfield(L, M)",
			"K ⊆ M",
			"finite_extension(L, K, M)",
			"subgroup(galois_group(L, K, M), H)",
		},
		Conclusion: "subfield(L, fixed_field(M, H)) ∧ " +
			"K ⊆ fixed_field(M, H) ∧ " +
			"fixed_field(M, H) ⊆ M ∧ " +
			"field_automorphisms(L, fixed_field(M, H), M) = H",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			K, M *Expr[Set[A]],
			H *Expr[Set[Permutation[A]]],
			setting Fact,
		) {
			autK := a.TermAs[Set[Permutation[A]]]("field_automorphisms(L, K, M)")
			opened := a.Conjuncts(
				a.Have(
					"H is a group of permutations made of automorphisms of M fixing K",
					"subgroup(permutation_group, H) ∧ H ⊆ field_automorphisms(L, K, M)",
					By(setting, field_automorphism.GaloisGroupSubgroup.At(a.TermAs[FieldOps[A]]("L"), K, M, H))),
				"H is a group of permutations",
				"H lies in Aut_K(M)")
			subgroupH, inAutK := opened[0], opened[1]
			finiteH := a.Have(
				"H is finite, inside the finite group Aut_K(M)",
				"finite(H)",
				By(
					setting,
					inAutK,
					field_automorphism.AutomorphismsBound.Read(L).At(K, M),
					finite_set.FiniteSubset.At(H, autK)))
			automorphisms := a.Have(
				"the members of H are automorphisms of M",
				"H ⊆ field_automorphisms(L, ∅, M)",
				BySets(inAutK, field_automorphism.AutomorphismsAntitone.Read(L).At(a.TermAs[Set[A]]("∅"), K, M)))
			subfieldF := a.Have(
				"the fixed field F of H is a subfield",
				"subfield(L, fixed_field(M, H))",
				By(setting, automorphisms, field_automorphism.FixedFieldSubfield.Read(L).At(M, H)))
			between := a.Have(
				"F lies between K and M: H lies among the automorphisms "+
					"fixing K, so F holds their fixed field, which holds K",
				"K ⊆ fixed_field(M, H) ∧ fixed_field(M, H) ⊆ M",
				BySets(
					setting,
					inAutK,
					field_automorphism.SubfieldFixed.Read(L).At(K, M),
					field_automorphism.FixedFieldAntitone.At(M, H, autK),
					field_automorphism.FixedFieldDef.At(M, H)))
			a.Show(
				"Artin: the automorphisms fixing F are exactly H",
				By(
					setting,
					subgroupH,
					subfieldF,
					between,
					finiteH,
					automorphisms,
					field_automorphism.ArtinAutomorphisms.Read(L).At(M, H)))
		}),
})}

// CorrespondenceAntitone — for M Galois over K, a field F between K and
// M, and any subset E of M, E lies in F exactly when the automorphisms of
// M fixing F lie among those fixing E: a Galois connection whose
// intermediate fields are closed.
var CorrespondenceAntitone = correspondenceAntitoneThm{family.Add(registry.ProofEntry{
	Name: "CorrespondenceAntitone",
	Key:  "prop_d199c2a4aad391fc",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀K E F M:set(A).",
		Hypotheses: []string{
			"subfield(L, K)",
			"subfield(L, M)",
			"E ⊆ M",
			"subfield(L, F)",
			"K ⊆ F",
			"F ⊆ M",
			"galois_over(L, K, M)",
		},
		Conclusion: "E ⊆ F ⇔ field_automorphisms(L, F, M) ⊆ field_automorphisms(L, E, M)",
	},
		func(a *Argument, L field.FieldFact[on.L], K, E, F, M *Expr[Set[A]], tower Fact) {
			autE := a.TermAs[Set[Permutation[A]]]("field_automorphisms(L, E, M)")
			autF := a.TermAs[Set[Permutation[A]]]("field_automorphisms(L, F, M)")
			a.Iff()
			a.Forward(
				"an automorphism fixing F fixes its subset E",
				Cite(field_automorphism.AutomorphismsAntitone.Read(L)))
			a.Backward(
				"the smaller group fixes the larger field, and the "+
					"intermediate field F is the field its group fixes",
				func(b *Argument, fewer Fact) {
					b.Show(
						"E lies in the field Aut_E(M) fixes, inside the field the smaller group Aut_F(M) fixes, which is F",
						BySets(
							tower,
							fewer,
							field_automorphism.FixedFieldAntitone.At(M, autF, autE),
							field_automorphism.SubfieldFixed.Read(L).At(E, M),
							CorrespondenceFixed.Read(L).At(K, F, M)))
				})
		}),
})}

// CorrespondenceDegree — the group fixing an intermediate field E has
// [M : E] members, and [E : K] is its index. M is Galois over E as over
// K, so Aut_E(M) and Aut_K(M) have [M : E] and [M : K] members; Lagrange
// makes |Aut_K(M)| the order of Aut_E(M) times the index, the tower law
// makes [M : K] = [E : K] · [M : E], and [M : E] cancels.
var CorrespondenceDegree = correspondenceDegreeThm{family.Add(registry.ProofEntry{
	Name: "CorrespondenceDegree",
	Key:  "prop_13a10bebd02d44f5",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀K E M:set(A).",
		Hypotheses: []string{
			"subfield(L, K)",
			"subfield(L, E)",
			"subfield(L, M)",
			"K ⊆ E",
			"E ⊆ M",
			"galois_over(L, K, M)",
		},
		Conclusion: "card(field_automorphisms(L, E, M)) = extension_degree(L, E, M) ∧ " +
			"card(left_cosets(permutation_compose, " +
			"        field_automorphisms(L, K, M), " +
			"        field_automorphisms(L, E, M))) = " +
			"extension_degree(L, K, E)",
	},
		func(a *Argument, L field.FieldFact[on.L], K, E, M *Expr[Set[A]], tower Fact) {
			autE := a.TermAs[Set[Permutation[A]]]("field_automorphisms(L, E, M)")
			degreeKE := a.TermAs[Nat]("extension_degree(L, K, E)")
			degreeEM := a.TermAs[Nat]("extension_degree(L, E, M)")
			index := a.TermAs[Nat](
				"card( " +
					"    left_cosets(permutation_compose, field_automorphisms(L, K, M), field_automorphisms(L, E, M)))")
			galoisE := a.Have(
				"M is Galois over the intermediate field E",
				"galois_over(L, E, M)",
				By(tower, GaloisTower.Read(L).At(K, E, M)))
			kInM := a.Have(
				"K lies in M",
				"K ⊆ M",
				BySets(tower))
			finite := a.Have(
				"M is finite over K, being Galois",
				"finite_extension(L, K, M)",
				By(tower, GaloisOverDef))
			finiteTower := a.Have(
				"so both steps of the tower K ⊆ E ⊆ M are finite",
				"finite_extension(L, K, E) ∧ finite_extension(L, E, M)",
				By(tower, finite, field_extension.TowerFinite.Read(L).At(K, E, M)))
			countE := a.Have(
				"M is Galois over E, so Aut_E(M) has [M : E] members",
				"card(field_automorphisms(L, E, M)) = extension_degree(L, E, M)",
				By(tower, finiteTower, galoisE, GaloisIffCard.Read(L).At(E, M)))
			countK := a.Have(
				"M is Galois over K, so Aut_K(M) has [M : K] members",
				"card(field_automorphisms(L, K, M)) = extension_degree(L, K, M)",
				By(tower, kInM, finite, GaloisIffCard.Read(L).At(K, M)))
			degrees := a.Have(
				"the degrees multiply along the tower",
				"extension_degree(L, K, M) = extension_degree(L, K, E) * extension_degree(L, E, M)",
				By(tower, finiteTower, field_extension.TowerLaw.Read(L).At(K, E, M)))
			groupK := a.Have(
				"the automorphisms fixing K form a group",
				"group_on(galois_group(L, K, M))",
				Cite(field_automorphism.GaloisGroupOn.Read(L)))
			lagrange := a.Have(
				"Lagrange in the finite group Aut_K(M): its order is the order of Aut_E(M) times the index",
				"card(field_automorphisms(L, K, M)) = "+
					"card(field_automorphisms(L, E, M)) * "+
					"card( "+
					"    left_cosets(permutation_compose, field_automorphisms(L, K, M), field_automorphisms(L, E, M)))",
				By(
					tower,
					kInM,
					finite,
					field_automorphism.AutomorphismsTowerSubgroup.Read(L).At(K, E, M),
					field_automorphism.AutomorphismsBound.Read(L).At(K, M),
					quotient_group.LagrangeIndex.Read(groupK).At(autE)))
			positive := a.Have(
				"the degree [M : E] is positive",
				"0 < extension_degree(L, E, M)",
				By(tower, finiteTower, field_extension.ExtensionDegreePositive.Read(L).At(E, M)))
			indexDegree := a.Have(
				"so [M : E] · index = [M : K] = [E : K] · [M : E], and cancelling [M : E] leaves the index [E : K]",
				"card(left_cosets(permutation_compose, "+
					"        field_automorphisms(L, K, M), "+
					"        field_automorphisms(L, E, M))) = "+
					"extension_degree(L, K, E)",
				By(
					positive,
					countE,
					lagrange,
					countK,
					degrees,
					nat_arith.MulSym.At(degreeKE, degreeEM),
					nat_arith.MulEqLCancel.At(degreeEM, index, degreeKE),
					nat_order.PosIffNonzero.At(degreeEM)))
			a.Show(
				"Aut_E(M) has [M : E] members and index [E : K]",
				By(countE, indexDegree))
		}),
})}

// RestrictionInto — an automorphism fixing K carries a normal
// intermediate field into itself.
var RestrictionInto = restrictionIntoThm{family.Add(registry.ProofEntry{
	Name: "RestrictionInto",
	Key:  "prop_1c892c09510f6bc0",
	Deps: []registry.EntryLike{
		field_automorphism.AutomorphismPermutesRoots,
		NormalIffMinimalPolynomial,
		algebraic_element.MinimalPolynomialSpec,
		algebraic_element.FiniteExtensionAlgebraic,
		separable_polynomial.SplitsMono,
		polynomial_roots.FactorTheorem,
		polynomial_division.IrreducibleDividesProduct,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀K E M:set(A). ∀p:permutation(A). ∀x:A.",
		Hypotheses: []string{
			"subfield(L, K)",
			"subfield(L, E)",
			"subfield(L, M)",
			"K ⊆ E",
			"E ⊆ M",
			"finite_extension(L, K, M)",
			"normal_over(L, K, E)",
			"p ∈ field_automorphisms(L, K, M)",
			"x ∈ E",
		},
		Conclusion: "permutation_map(p, x) ∈ E",
	},
		"p(x) is a root of the minimal polynomial of x over K (AutomorphismPermutesRoots), "+
			"which splits over E (NormalIffMinimalPolynomial); over E it is a constant times a "+
			"product of factors x - b with b ∈ E, so its roots in the field are those b "+
			"(FactorTheorem, IrreducibleDividesProduct at the linear factors)"),
})}

// RestrictionAutomorphism — restricted to a normal intermediate field E,
// an automorphism of M fixing K is an automorphism of E fixing K.
var RestrictionAutomorphism = restrictionAutomorphismThm{family.Add(registry.ProofEntry{
	Name: "RestrictionAutomorphism",
	Key:  "prop_fc089639124c216e",
	Deps: []registry.EntryLike{
		permutationRestrictDef,
		RestrictionInto,
		field_automorphism.FieldAutomorphismsDef,
		field_automorphism.AutomorphismsSubgroup,
		symmetric_group.MapInverse,
		symmetric_group.PermutationEq,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀K E M:set(A). ∀p:permutation(A).",
		Hypotheses: []string{
			"subfield(L, K)",
			"subfield(L, E)",
			"subfield(L, M)",
			"K ⊆ E",
			"E ⊆ M",
			"finite_extension(L, K, M)",
			"normal_over(L, K, E)",
			"p ∈ field_automorphisms(L, K, M)",
		},
		Conclusion: "permutation_restrict(E, p) ∈ field_automorphisms(L, K, E) ∧ " +
			"(∀x:A. x ∈ E ⇒ permutation_map(permutation_restrict(E, p), x) = permutation_map(p, x))",
	},
		"p and its inverse, also in Aut_K(M) (AutomorphismsSubgroup), carry E into E (RestrictionInto), "+
			"so the map that is p on E and the identity elsewhere is a bijection, a permutation; the choice "+
			"is that permutation (PermutationEq), and it keeps sums and products on E and fixes K as p does"),
})}

// RestrictionHomomorphism — restriction to a normal intermediate field
// is a homomorphism of the automorphism groups.
var RestrictionHomomorphism = restrictionHomomorphismThm{family.Add(registry.ProofEntry{
	Name: "RestrictionHomomorphism",
	Key:  "prop_2812459564e1848a",
	Deps: []registry.EntryLike{
		RestrictionAutomorphism,
		group_homomorphism.GroupHomomorphism,
		field_automorphism.GaloisGroupDef,
		field_automorphism.GaloisGroupOn,
		symmetric_group.MapCompose,
		symmetric_group.PermutationEq,
		symmetric_group.InSymmetricGroup,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀K E M:set(A).",
		Hypotheses: []string{
			"subfield(L, K)",
			"subfield(L, E)",
			"subfield(L, M)",
			"K ⊆ E",
			"E ⊆ M",
			"galois_over(L, K, M)",
			"normal_over(L, K, E)",
		},
		Conclusion: "group_homomorphism(galois_group(L, K, M), " +
			"    galois_group(L, K, E), " +
			"    λp:permutation(A). permutation_restrict(E, p))",
	},
		"both are groups on their sets (GaloisGroupOn); restrictions land in Aut_K(E) "+
			"(RestrictionAutomorphism); the restriction of p ∘ q and the composite of the restrictions "+
			"agree on E, where p and q act, and outside E, where both are the identity (PermutationEq)"),
})}

// RestrictionKernel — the automorphisms restricting to the identity on E
// are those fixing E.
var RestrictionKernel = restrictionKernelThm{family.Add(registry.ProofEntry{
	Name: "RestrictionKernel",
	Key:  "prop_9459d8adc03ccbf6",
	Deps: []registry.EntryLike{
		RestrictionAutomorphism,
		group_homomorphism.GroupKernelDef,
		field_automorphism.FieldAutomorphismsDef,
		field_automorphism.AutomorphismsAntitone,
		symmetric_group.PermutationEq,
		symmetric_group.MapIdentity,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀K E M:set(A).",
		Hypotheses: []string{
			"subfield(L, K)",
			"subfield(L, E)",
			"subfield(L, M)",
			"K ⊆ E",
			"E ⊆ M",
			"galois_over(L, K, M)",
			"normal_over(L, K, E)",
		},
		Conclusion: "group_kernel(permutation_identity, " +
			"    field_automorphisms(L, K, M), " +
			"    λp:permutation(A). permutation_restrict(E, p)) = " +
			"field_automorphisms(L, E, M)",
	},
		"the restriction of p is the identity exactly when p fixes every member of E "+
			"(RestrictionAutomorphism, PermutationEq); and Aut_E(M) ⊆ Aut_K(M) (AutomorphismsAntitone)"),
})}

// RestrictionOnto — every automorphism of a normal intermediate field
// fixing K is a restriction.
var RestrictionOnto = restrictionOntoThm{family.Add(registry.ProofEntry{
	Name: "RestrictionOnto",
	Key:  "prop_d16fe592a605773",
	Deps: []registry.EntryLike{
		RestrictionHomomorphism,
		RestrictionKernel,
		CorrespondenceDegree,
		GaloisIffCard,
		GaloisOverDef,
		field_automorphism.AutomorphismsBound,
		quotient_group.FirstIsomorphism,
		finite_group.Lagrange,
		set_basic.Extension,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀K E M:set(A).",
		Hypotheses: []string{
			"subfield(L, K)",
			"subfield(L, E)",
			"subfield(L, M)",
			"K ⊆ E",
			"E ⊆ M",
			"galois_over(L, K, M)",
			"normal_over(L, K, E)",
		},
		Conclusion: "image(λp:permutation(A). permutation_restrict(E, p), " +
			"    field_automorphisms(L, K, M)) = " +
			"field_automorphisms(L, K, E)",
	},
		"the image is a subgroup of Aut_K(E) isomorphic to the quotient by the kernel Aut_E(M) "+
			"(FirstIsomorphism, RestrictionKernel), so it has [E : K] members (CorrespondenceDegree); "+
			"Aut_K(E) has at most [E : K] (AutomorphismsBound), so the image is all of it"),
})}

// NormalIffNormalSubgroup — an intermediate field is normal over K
// exactly when the automorphisms fixing it form a normal subgroup.
var NormalIffNormalSubgroup = normalIffNormalSubgroupThm{family.Add(registry.ProofEntry{
	Name: "NormalIffNormalSubgroup",
	Key:  "prop_3f5f0ab390836b9a",
	Deps: []registry.EntryLike{
		RestrictionInto,
		RestrictionKernel,
		group_homomorphism.KernelNormal,
		RestrictionHomomorphism,
		CorrespondenceFixed,
		ConjugateAutomorphism,
		NormalIffMinimalPolynomial,
		group.NormalSubgroupDef,
		field_automorphism.FieldAutomorphismsDef,
		field_automorphism.GaloisGroupDef,
		separable_polynomial.SplitsMono,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀K E M:set(A).",
		Hypotheses: []string{
			"subfield(L, K)",
			"subfield(L, E)",
			"subfield(L, M)",
			"K ⊆ E",
			"E ⊆ M",
			"galois_over(L, K, M)",
		},
		Conclusion: "normal_over(L, K, E) ⇔ " +
			"normal_subgroup(galois_group(L, K, M), field_automorphisms(L, E, M))",
	},
		"⇒: Aut_E(M) is the kernel of restriction (RestrictionKernel), normal (KernelNormal); ⇐: "+
			"for p ∈ Aut_K(M) and q ∈ Aut_E(M), p⁻¹ q p fixes E, so q fixes p(E), and p(E) ⊆ the "+
			"field Aut_E(M) fixes, E (CorrespondenceFixed); so every conjugate in M of a ∈ E lies in "+
			"E (ConjugateAutomorphism), and the minimal polynomial, which splits over M, splits over E"),
})}

// QuotientGalois — a normal intermediate field E is Galois over K, and
// restriction to E induces an isomorphism from the quotient of Aut_K(M) by
// Aut_E(M) onto Aut_K(E).
var QuotientGalois = quotientGaloisThm{family.Add(registry.ProofEntry{
	Name: "QuotientGalois",
	Key:  "prop_bdad5df1a36386c9",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀K E M:set(A).",
		Hypotheses: []string{
			"subfield(L, K)",
			"subfield(L, E)",
			"subfield(L, M)",
			"K ⊆ E",
			"E ⊆ M",
			"galois_over(L, K, M)",
			"normal_over(L, K, E)",
		},
		Conclusion: "galois_over(L, K, E) ∧ " +
			"group_isomorphic(«quotientAutomorphisms», galois_group(L, K, E))",
		Abbrev: Abbrev{
			{Name: "quotientAutomorphisms", Text: "quotient_group(galois_group(L, K, M), " +
				"    field_automorphisms(L, E, M))"},
		},
	},
		func(a *Argument, L field.FieldFact[on.L], K, E, M *Expr[Set[A]], tower Fact) {
			galoisM := a.Have(
				"M is Galois over K",
				"galois_over(L, K, M)",
				By(tower))
			finiteNormalSeparable := a.Unfolded(galoisM, GaloisOverDef)
			finite := a.Have(
				"E lies inside the finite extension M, so it is finite over K",
				"finite_extension(L, K, E)",
				By(tower, finiteNormalSeparable, field_extension.TowerFinite.Read(L).At(K, E, M)))
			separable := a.Have(
				"each member of E is a member of M, so separable over K",
				"∀a:A. a ∈ E ⇒ separable_over(L, K, a)",
				By(tower, finiteNormalSeparable, set_basic.SubsetDef.At(E, M)))
			galoisE := a.Have(
				"E is Galois over K: finite, normal by hypothesis, and separable",
				"galois_over(L, K, E)",
				By(finite, tower, separable, GaloisOverDef))
			kernel := a.Have(
				"restriction to E has kernel Aut_E(M)",
				"group_kernel(permutation_identity, "+
					"    field_automorphisms(L, K, M), "+
					"    λp:permutation(A). permutation_restrict(E, p)) = "+
					"field_automorphisms(L, E, M)",
				By(tower, RestrictionKernel.Read(L).At(K, E, M)))
			image := a.Have(
				"and its image is all of Aut_K(E)",
				"image(λp:permutation(A). permutation_restrict(E, p), field_automorphisms(L, K, M)) = "+
					"field_automorphisms(L, K, E)",
				By(tower, RestrictionOnto.Read(L).At(K, E, M)))
			restriction := a.Have(
				"restriction to E is a homomorphism of the automorphism groups",
				"group_homomorphism(galois_group(L, K, M), "+
					"    galois_group(L, K, E), "+
					"    λp:permutation(A). permutation_restrict(E, p))",
				By(tower, RestrictionHomomorphism.Read(L).At(K, E, M)))
			firstIsomorphism := a.Simplified(
				quotient_group.FirstIsomorphism.Read(restriction),
				Fwd(field_automorphism.GaloisGroupDef),
				Fwd(group.RestrictGroupDef))
			isomorphism := a.Have(
				"restriction is a homomorphism Aut_K(M) → Aut_K(E), so the map it "+
					"induces on the cosets of its kernel is an isomorphism onto its image",
				"group_isomorphism(«quotientAutomorphisms», "+
					"    galois_group(L, K, E), "+
					"    induced_map(λp:permutation(A). permutation_restrict(E, p)))",
				Simp(Fwd(field_automorphism.GaloisGroupDef), Fwd(group.RestrictGroupDef)),
				By(firstIsomorphism, kernel, image))
			a.Show(
				"E is Galois over K, and the induced map makes the quotient isomorphic to Aut_K(E)",
				Simp(Fwd(group_isomorphism.GroupIsomorphicDef)),
				By(galoisE, isomorphism))
		}),
})}
