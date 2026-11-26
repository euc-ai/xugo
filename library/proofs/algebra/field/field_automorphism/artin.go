// artin.go — Artin's theorem from two inequalities proved alike: evaluated on
// a finite basis, the automorphisms of M fixing K are independent columns, by
// Dedekind, so |Aut_K(M)| ≤ [M : K], and every group fixing a set above K has
// positive order; evaluated along a finite group H, members of M independent
// over the fixed field are independent columns, by a relation of least
// support, so [M : M^H] ≤ |H|.

package field_automorphism

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_extension"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/symmetric_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/free_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/function_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/linear_independence"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_domain"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// Dedekind — distinct automorphisms of M are linearly independent over
// L: a combination of finitely many of them with coefficients in L that
// vanishes at every point of M has every coefficient zero. They are
// characters of M with values in the domain L: each fixes one and keeps the
// product, and two distinct permutations of M differ on it.
var Dedekind = dedekindThm{family.Add(registry.ProofEntry{
	Name: "Dedekind",
	Key:  "prop_4910c5f11d6cb837",
	Reading: "The automorphisms are a set, so they are distinct by being its members; the " +
		"combination is a finite sum over that set, indexed by the permutations themselves.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). " +
			"∀M:set(A). " +
			"∀H:set(permutation(A)). " +
			"∀c:(permutation(A) → A). " +
			"∀p:permutation(A).",
		Hypotheses: []string{
			"subfield(L, M)",
			"finite(H)",
			"H ⊆ field_automorphisms(L, ∅, M)",
			"∀q:permutation(A). q ∈ H ⇒ c(q) ∈ L.carrier",
			"∀x:A. " +
				"    x ∈ M ⇒ " +
				"    module_sum(L.add, L.zero, H, λr:permutation(A). c(r) * permutation_map(r, x)) = L.zero",
			"p ∈ H",
		},
		Conclusion: "c(p) = L.zero",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			M *Expr[Set[A]],
			H *Expr[Set[Permutation[A]]],
			c *Arrow[Permutation[A], A],
			h Fact,
		) {
			parts := a.Conjuncts(
				h,
				"M is a subfield of L",
				"H is finite",
				"the members of H are automorphisms of M",
				"the coefficients lie in L",
				"the combination vanishes on M")
			subfield, finH, onAut, coefficients, vanishes := parts[0], parts[1], parts[2], parts[3], parts[4]
			inL := a.Have(
				"M lies in L",
				"M ⊆ L.carrier",
				By(subfield, field.SubfieldSubset))
			permuted := a.Have(
				"the members of H permute M",
				"∀q:permutation(A). q ∈ H ⇒ q ∈ symmetric_group(M)",
				BySets(a.Unfolded(onAut, FieldAutomorphismsDef)))
			characters := a.Have(
				"each member of H fixes one and keeps the product, with values in L",
				Statement{
					Binders:    "∀q:permutation(A).",
					Hypotheses: []string{"q ∈ H"},
					Conclusion: "permutation_map(q, L.one) = L.one ∧ " +
						"(∀x:A. x ∈ M ⇒ permutation_map(q, x) ∈ L.carrier) ∧ " +
						"(∀x y:A. " +
						"    x ∈ M ∧ y ∈ M ⇒ permutation_map(q, x * y) = permutation_map(q, x) * permutation_map(q, y))",
				},
				Derive(func(b *Argument) {
					q := b.FixAs[Permutation[A]]("q")
					qIn := b.Assume()
					automorphism := b.Have(
						"q is an automorphism of M",
						"q ∈ field_automorphisms(L, ∅, M)",
						By(qIn, onAut, set_basic.SubsetDef))
					b.Show(
						"it fixes one, it keeps the products of M, and its values on M lie in M, which lies in L",
						BySets(
							subfield,
							automorphism,
							b.Unfolded(automorphism, FieldAutomorphismsDef),
							inL,
							AutomorphismFixesUnits.Read(L).At(b.TermAs[Set[A]]("∅"), M, q),
							symmetric_group.SymmetricGroupMapsInto))
				}))
			separated := a.Have(
				"two distinct members of H differ on M",
				Statement{
					Binders: "∀q r:permutation(A).",
					Hypotheses: []string{
						"q ∈ H",
						"r ∈ H",
						"q ≠ r",
					},
					Conclusion: "∃x:A. x ∈ M ∧ permutation_map(q, x) ≠ permutation_map(r, x)",
				},
				Derive(func(b *Argument) {
					q := b.FixAs[Permutation[A]]("q")
					r := b.FixAs[Permutation[A]]("r")
					members := b.Assume()
					b.Show(
						"two permutations of M agreeing on M are equal",
						By(
							members,
							permuted,
							symmetric_group.InSymmetricGroup.At(M, q),
							symmetric_group.InSymmetricGroup.At(M, r),
							symmetric_group.PermutationEq.At(q, r)))
				}))
			a.Show(
				"so they are independent characters of M over the domain L",
				By(
					field.SubfieldOne.Read(subfield),
					field.SubfieldMul.Read(subfield),
					finH,
					characters,
					separated,
					coefficients,
					vanishes,
					linear_independence.CharactersIndependent.Read(
						integral_domain.FieldIntegralDomain.Read(L)).AsFact().At(
						a.TermAs[Op[A]]("L.mul"),
						a.TermAs[A]("L.one"),
						M,
						H,
						a.TermAs[Fun2[Permutation[A], A, A]]("λq:permutation(A). λx:A. permutation_map(q, x)"),
						c)))
		}),
})}

// AutomorphismsBound — the automorphisms of a finite extension fixing
// the smaller field are no more than its degree: evaluation on a finite
// basis embeds them as independent columns over the ambient field, a
// relation among the columns extending K-linearly from the basis to all
// of M, where Dedekind clears it.
var AutomorphismsBound = automorphismsBoundThm{family.Add(registry.ProofEntry{
	Name: "AutomorphismsBound",
	Key:  "prop_64658baecf15acc5",
	Reading: "finite_extension(L, K, M) is load-bearing: the translations " +
		"t ↦ t + k are infinitely many automorphisms of ℚ(t) fixing ℚ.",
	Build: family.Sections(Statement{
		Binders: "∀L:field_on(A). ∀K M:set(A).",
		Hypotheses: []string{
			"subfield(L, K)",
			"subfield(L, M)",
			"K ⊆ M",
			"finite_extension(L, K, M)",
		},
		Conclusion: "finite(field_automorphisms(L, K, M)) ∧ " +
			"card(field_automorphisms(L, K, M)) ≤ extension_degree(L, K, M)",
		Abbrev: Abbrev{
			{Name: "basisScalars", Text: "restrict_ring(field_ring(L), K)"},
			{Name: "basisVectors", Text: "restrict_module(regular_module(field_ring(L)), M)"},
			{Name: "coordinates", Text: "module_basis_coordinates(«basisScalars», «basisVectors», B)"},
			{Name: "evaluation", Text: "λp:permutation(A). λb:A. COND(b ∈ B, permutation_map(p, b), L.zero)"},
			{Name: "columns", Text: "free_module_record(field_ring(L), B)"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		automorphismLinear := ctx.Lemma(Statement{
			Binders: "∀L:field_on(A). ∀K M:set(A). ∀p:permutation(A).",
			Hypotheses: []string{
				"subfield(L, K)",
				"subfield(L, M)",
				"K ⊆ M",
				"p ∈ field_automorphisms(L, K, M)",
			},
			Conclusion: "module_homomorphism(«basisScalars», " +
				"    «basisVectors», " +
				"    regular_module(field_ring(L)), " +
				"    λx:A. permutation_map(p, x))",
		}, func(a *Argument, L field.FieldFact[on.L], K, M *Expr[Set[A]], p *Expr[Permutation[A]], h Fact) {
			laws := a.Unfolded(h, FieldAutomorphismsDef)
			a.Show(
				"an automorphism fixing K is K-linear",
				BySets(
					L,
					laws,
					symmetric_group.SymmetricGroupMapsInto.Inst[A]().At(M, p),
					field.SubfieldSubset,
					field_extension.ExtensionModuleOn.Read(L).At(K, M),
					field_extension.SubfieldScalars.Read(L).At(K),
					module_homomorphism.ModuleHomomorphismDef))
		})

		basisExpansion := ctx.Lemma(Statement{
			Binders: "∀L:field_on(A). ∀K M B:set(A). ∀x:A.",
			Hypotheses: []string{
				"subfield(L, K)",
				"subfield(L, M)",
				"K ⊆ M",
				"finite(B)",
				"module_basis(«basisScalars», «basisVectors», B)",
				"x ∈ M",
			},
			Conclusion: "B ⊆ M ∧ " +
				"(∀b:A. b ∈ B ⇒ «coordinates»(x, b) ∈ L.carrier) ∧ " +
				"(∀p:permutation(A). " +
				"    p ∈ field_automorphisms(L, K, M) ⇒ " +
				"    permutation_map(p, x) = " +
				"    module_sum(L.add, L.zero, B, λb:A. «coordinates»(x, b) * permutation_map(p, b)))",
		}, func(a *Argument, L field.FieldFact[on.L], K, M, B *Expr[Set[A]], x *Expr[A], h Fact) {
			R := a.TermAs[module_record.RingOps[A]]("«basisScalars»")
			W := a.TermAs[module_record.ModuleOps[A, A]]("«basisVectors»")
			inM := a.Have(
				"the basis lies in M",
				"B ⊆ M",
				By(Normalized, h, linear_independence.BasisInCarrier))
			scalars := a.Have(
				"the basis coordinates lie in L",
				"∀b:A. b ∈ B ⇒ «coordinates»(x, b) ∈ L.carrier",
				By(
					L,
					h,
					field_extension.ExtensionModuleOn.Read(L).At(K, M),
					module_dimension.BasisCoordinatesSpec.At(R, W, B, x),
					field.SubfieldSubset.At(a.TermAs[FieldOps[A]]("L"), K),
					set_basic.SubsetDef))
			expands := a.Have(
				"each automorphism is determined by its basis values",
				Statement{
					Binders: "∀p:permutation(A).",
					Hypotheses: []string{
						"p ∈ field_automorphisms(L, K, M)",
					},
					Conclusion: "permutation_map(p, x) = " +
						"module_sum(L.add, L.zero, B, λb:A. «coordinates»(x, b) * permutation_map(p, b))",
				},
				Derive(func(b *Argument) {
					p := b.FixAs[Permutation[A]]("p")
					aut := b.Assume()
					linear := b.Have(
						"p is K-linear",
						"module_homomorphism(«basisScalars», "+
							"    «basisVectors», "+
							"    regular_module(field_ring(L)), "+
							"    λx:A. permutation_map(p, x))",
						By(L, h, aut, At(automorphismLinear, b.TermAs[FieldOps[A]]("L"), K, M, p)))
					b.Show(
						"apply the linear map to the basis expansion",
						By(
							h,
							linear,
							module_dimension.HomBasisExpansion.At(
								R,
								W,
								b.TermAs[module_record.ModuleOps[A, A]]("regular_module(field_ring(L))"),
								B,
								b.TermAs[Fun[A, A]]("λx:A. permutation_map(p, x)"),
								x)))
				}))
			a.Show(
				"the coordinates and the automorphism expansions have the required properties",
				By(inM, scalars, expands))
		})

		basisDetermines := ctx.Lemma(Statement{
			Binders: "∀L:field_on(A). ∀K M B:set(A). ∀p q:permutation(A).",
			Hypotheses: []string{
				"subfield(L, K)",
				"subfield(L, M)",
				"K ⊆ M",
				"finite(B)",
				"module_basis(«basisScalars», «basisVectors», B)",
				"p ∈ field_automorphisms(L, K, M)",
				"q ∈ field_automorphisms(L, K, M)",
				"∀b:A. b ∈ B ⇒ permutation_map(p, b) = permutation_map(q, b)",
			},
			Conclusion: "p = q",
		}, func(
			a *Argument,
			L field.FieldFact[on.L],
			K, M, B *Expr[Set[A]],
			p, q *Expr[Permutation[A]],
			h Fact,
		) {
			agree := a.Have(
				"equal basis values give equal values throughout M",
				"∀x:A. x ∈ M ⇒ permutation_map(p, x) = permutation_map(q, x)",
				Derive(func(b *Argument) {
					x := b.FixAs[A]("x")
					xIn := b.Assume()
					expansions := b.Have(
						"expand p and q with the same coordinates",
						"permutation_map(p, x) = "+
							"module_sum(L.add, L.zero, B, λb:A. «coordinates»(x, b) * permutation_map(p, b)) ∧ "+
							"permutation_map(q, x) = "+
							"module_sum(L.add, L.zero, B, λb:A. «coordinates»(x, b) * permutation_map(q, b))",
						By(L, h, xIn, At(basisExpansion, b.TermAs[FieldOps[A]]("L"), K, M, B, x)))
					b.Show(
						"the two finite sums agree term by term",
						By(
							expansions,
							h,
							module.ModuleSumCongruence.At(
								b.TermAs[Op[A]]("L.add"),
								b.TermAs[A]("L.zero"),
								B,
								b.TermAs[Fun[A, A]]("λb:A. «coordinates»(x, b) * permutation_map(p, b)"),
								b.TermAs[Fun[A, A]]("λb:A. «coordinates»(x, b) * permutation_map(q, b)"))))
				}))
			laws := a.Unfolded(h, FieldAutomorphismsDef)
			a.Show(
				"outside M both permutations are the identity",
				BySets(
					agree,
					laws,
					symmetric_group.InSymmetricGroup.Inst[A]().At(M),
					symmetric_group.PermutationEq.At(p, q)))
		})

		weightedInterchange := ctx.Lemma(Statement{
			Binders: "∀L:field_on(A). ∀H:set(D). ∀B:set(E). ∀c:(D → A). ∀d:(E → A). ∀f:(D → E → A).",
			Hypotheses: []string{
				"finite(H)",
				"finite(B)",
				"∀p:D. p ∈ H ⇒ c(p) ∈ L.carrier",
				"∀b:E. b ∈ B ⇒ d(b) ∈ L.carrier",
				"∀p:D. ∀b:E. p ∈ H ∧ b ∈ B ⇒ f(p, b) ∈ L.carrier",
			},
			Conclusion: "module_sum(L.add, " +
				"    L.zero, " +
				"    H, " +
				"    λp:D. c(p) * module_sum(L.add, L.zero, B, λb:E. d(b) * f(p, b))) = " +
				"module_sum(L.add, L.zero, B, λb:E. d(b) * module_sum(L.add, L.zero, H, λp:D. c(p) * f(p, b)))",
		}, func(
			a *Argument,
			L field.FieldFact[on.L],
			H *Expr[Set[D]],
			B *Expr[Set[E]],
			c *Arrow[D, A],
			d *Arrow[E, A],
			f *Arrow2[D, E, A],
			h Fact,
		) {
			ring := field.RingOn.Read(L)
			regular := module.RegularModuleOn.Read(ring)
			left := a.Have(
				"distribute each coefficient into its inner sum",
				Statement{
					Binders: "∀p:D.",
					Hypotheses: []string{
						"p ∈ H",
					},
					Conclusion: "c(p) * module_sum(L.add, L.zero, B, λb:E. d(b) * f(p, b)) = " +
						"module_sum(L.add, L.zero, B, λb:E. c(p) * (d(b) * f(p, b)))",
				},
				Derive(func(b *Argument) {
					b.FixAs[D]("p")
					pIn := b.Assume()
					b.Show(
						"multiplication commutes with the finite sum",
						By(
							h,
							pIn,
							comm_ring.MulIn.Read(ring),
							module.ModuleSumSmul.Read(regular).AsFact().At(
								B, b.TermAs[A]("c(p)"), b.TermAs[Fun[E, A]]("λb:E. d(b) * f(p, b)"))))
				}))
			commute := a.Have(
				"the two scalar weights commute",
				"∀p:D. ∀b:E. p ∈ H ∧ b ∈ B ⇒ c(p) * (d(b) * f(p, b)) = d(b) * (c(p) * f(p, b))",
				ByArith(ring, h))
			right := a.Have(
				"collect the basis weight after summing over H",
				Statement{
					Binders: "∀b:E.",
					Hypotheses: []string{
						"b ∈ B",
					},
					Conclusion: "module_sum(L.add, L.zero, H, λp:D. c(p) * (d(b) * f(p, b))) = " +
						"d(b) * module_sum(L.add, L.zero, H, λp:D. c(p) * f(p, b))",
				},
				Derive(func(b *Argument) {
					b.FixAs[E]("b")
					bIn := b.Assume()
					rearranged := b.Have(
						"commute the weights in each summand",
						"module_sum(L.add, L.zero, H, λp:D. c(p) * (d(b) * f(p, b))) = "+
							"module_sum(L.add, L.zero, H, λp:D. d(b) * (c(p) * f(p, b)))",
						By(commute, bIn, module.ModuleSumCongruence))
					b.Show(
						"take the common basis weight out of the sum",
						By(
							rearranged,
							bIn,
							h,
							comm_ring.MulIn.Read(ring),
							module.ModuleSumSmul.Read(regular).AsFact().At(
								H, b.TermAs[A]("d(b)"), b.TermAs[Fun[D, A]]("λp:D. c(p) * f(p, b)"))))
				}))
			swapped := a.Have(
				"interchange the two finite sums",
				"module_sum(L.add, "+
					"    L.zero, "+
					"    H, "+
					"    λp:D. module_sum(L.add, L.zero, B, λb:E. c(p) * (d(b) * f(p, b)))) = "+
					"module_sum(L.add, L.zero, B, λb:E. module_sum(L.add, L.zero, H, λp:D. c(p) * (d(b) * f(p, b))))",
				By(
					h,
					regular,
					comm_ring.MulIn.Read(ring),
					module.ModuleSumSwap.At(
						a.TermAs[module_record.RingOps[A]]("field_ring(L)"),
						a.TermAs[module_record.ModuleOps[A, A]]("regular_module(field_ring(L))"),
						H,
						B,
						a.TermAs[Fun2[D, E, A]]("λp:D. λb:E. c(p) * (d(b) * f(p, b))"))))
			a.Show(
				"the distributed sums give the weighted interchange",
				By(
					left,
					right,
					swapped,
					module.ModuleSumCongruence.At(
						a.TermAs[Op[A]]("L.add"),
						a.TermAs[A]("L.zero"),
						H,
						a.TermAs[Fun[D, A]]("λp:D. c(p) * module_sum(L.add, L.zero, B, λb:E. d(b) * f(p, b))"),
						a.TermAs[Fun[D, A]]("λp:D. module_sum(L.add, L.zero, B, λb:E. c(p) * (d(b) * f(p, b)))")),
					module.ModuleSumCongruence.At(
						a.TermAs[Op[A]]("L.add"),
						a.TermAs[A]("L.zero"),
						B,
						a.TermAs[Fun[E, A]]("λb:E. module_sum(L.add, L.zero, H, λp:D. c(p) * (d(b) * f(p, b)))"),
						a.TermAs[Fun[E, A]]("λb:E. d(b) * module_sum(L.add, L.zero, H, λp:D. c(p) * f(p, b))"))))
		})

		basisRelation := ctx.Lemma(Statement{
			Binders: "∀L:field_on(A). ∀K M B:set(A). ∀H:set(permutation(A)). ∀c:(permutation(A) → A). ∀x:A.",
			Hypotheses: []string{
				"subfield(L, K)",
				"subfield(L, M)",
				"K ⊆ M",
				"finite(B)",
				"module_basis(«basisScalars», «basisVectors», B)",
				"finite(H)",
				"H ⊆ field_automorphisms(L, K, M)",
				"∀p:permutation(A). p ∈ H ⇒ c(p) ∈ L.carrier",
				"∀b:A. " +
					"    b ∈ B ⇒ " +
					"    module_sum(L.add, L.zero, H, λp:permutation(A). c(p) * permutation_map(p, b)) = L.zero",
				"x ∈ M",
			},
			Conclusion: "module_sum(L.add, L.zero, H, λp:permutation(A). c(p) * permutation_map(p, x)) = " +
				"L.zero",
		}, func(
			a *Argument,
			L field.FieldFact[on.L],
			K, M, B *Expr[Set[A]],
			H *Expr[Set[Permutation[A]]],
			c *Arrow[Permutation[A], A],
			x *Expr[A],
			h Fact,
		) {
			expansions := a.Have(
				"expand every automorphism at x using B",
				"B ⊆ M ∧ "+
					"(∀b:A. b ∈ B ⇒ «coordinates»(x, b) ∈ L.carrier) ∧ "+
					"(∀p:permutation(A). "+
					"    p ∈ field_automorphisms(L, K, M) ⇒ "+
					"    permutation_map(p, x) = "+
					"    module_sum(L.add, L.zero, B, λb:A. «coordinates»(x, b) * permutation_map(p, b)))",
				By(L, h, At(basisExpansion, a.TermAs[FieldOps[A]]("L"), K, M, B, x)))
			values := a.Have(
				"the automorphisms' basis values lie in L",
				"∀p:permutation(A). ∀b:A. p ∈ H ∧ b ∈ B ⇒ permutation_map(p, b) ∈ L.carrier",
				BySets(
					expansions,
					h,
					FieldAutomorphismsDef.At(a.TermAs[FieldOps[A]]("L"), K, M),
					symmetric_group.SymmetricGroupMapsInto.Inst[A]().At(M),
					field.SubfieldSubset.At(a.TermAs[FieldOps[A]]("L"), M)))
			interchanged := a.Have(
				"the relation at x is a basis-weighted sum of the relations on B",
				"module_sum(L.add, "+
					"    L.zero, "+
					"    H, "+
					"    λp:permutation(A). "+
					"        c(p) * "+
					"        module_sum(L.add, L.zero, B, λb:A. «coordinates»(x, b) * permutation_map(p, b))) = "+
					"module_sum(L.add, "+
					"    L.zero, "+
					"    B, "+
					"    λb:A. "+
					"        «coordinates»(x, b) * "+
					"        module_sum(L.add, L.zero, H, λp:permutation(A). c(p) * permutation_map(p, b)))",
				By(
					L,
					values,
					expansions,
					h,
					At(
						weightedInterchange,
						a.TermAs[FieldOps[A]]("L"),
						H,
						B,
						c,
						a.TermAs[Fun[A, A]]("«coordinates»(x)"),
						a.TermAs[Fun2[Permutation[A], A, A]]("λp:permutation(A). λb:A. permutation_map(p, b)"))))
			zero := a.Have(
				"every basis-coordinate relation is zero",
				"module_sum(L.add, "+
					"    L.zero, "+
					"    B, "+
					"    λb:A. "+
					"        «coordinates»(x, b) * "+
					"        module_sum(L.add, L.zero, H, λp:permutation(A). c(p) * permutation_map(p, b))) = "+
					"L.zero",
				By(
					Normalized,
					expansions,
					h,
					comm_ring.MulRightZeroOn.Read(field.RingOn.Read(L)),
					module.ModuleSumZero.Read(module.RegularModuleOn.Read(field.RingOn.Read(L))).At(
						B,
						a.TermAs[Fun[A, A]](
							"λb:A. "+
								"    «coordinates»(x, b) * "+
								"    module_sum(L.add, L.zero, H, λp:permutation(A). c(p) * permutation_map(p, b))"))))
			a.Show(
				"basis expansion extends the vanishing relation to x",
				By(
					zero,
					interchanged,
					expansions,
					h,
					module.ModuleSumCongruence.At(
						a.TermAs[Op[A]]("L.add"),
						a.TermAs[A]("L.zero"),
						H,
						a.TermAs[Fun[Permutation[A], A]]("λp:permutation(A). c(p) * permutation_map(p, x)"),
						a.TermAs[Fun[Permutation[A], A]](
							"λp:permutation(A). "+
								"    c(p) * module_sum(L.add, L.zero, B, λb:A. «coordinates»(x, b) * permutation_map(p, b))")),
					set_basic.SubsetDef.At(H, a.TermAs[Set[Permutation[A]]]("field_automorphisms(L, K, M)"))))
		})

		evaluationColumns := ctx.Lemma(Statement{
			Binders: "∀L:field_on(A). ∀K M B:set(A).",
			Hypotheses: []string{
				"subfield(L, K)",
				"subfield(L, M)",
				"K ⊆ M",
				"finite(B)",
				"module_basis(«basisScalars», «basisVectors», B)",
			},
			Conclusion: "(∀p:permutation(A). " +
				"    p ∈ field_automorphisms(L, K, M) ⇒ «evaluation»(p) ∈ «columns».carrier) ∧ " +
				"injective_on(field_automorphisms(L, K, M), «evaluation»)",
		}, func(a *Argument, L field.FieldFact[on.L], K, M, B *Expr[Set[A]], h Fact) {
			inM := a.Have(
				"B lies in M",
				"B ⊆ M",
				By(Normalized, h, linear_independence.BasisInCarrier))
			carrier := a.Have(
				"each evaluation column belongs to the free module",
				"∀p:permutation(A). p ∈ field_automorphisms(L, K, M) ⇒ «evaluation»(p) ∈ «columns».carrier",
				Derive(func(b *Argument) {
					p := b.FixAs[Permutation[A]]("p")
					aut := b.Assume()
					support := b.TermAs[Set[A]]("fun_support(L.zero, λb:A. «evaluation»(p, b))")
					supported := b.Have(
						"the column vanishes outside B",
						"fun_support(L.zero, λb:A. «evaluation»(p, b)) ⊆ B",
						BySets())
					finiteSupport := b.Have(
						"the column has finite support",
						"finite(fun_support(L.zero, λb:A. «evaluation»(p, b)))",
						By(h, supported, finite_set.FiniteSubset.At(support, B)))
					values := b.Have(
						"the values of the column lie in L",
						"∀b:A. «evaluation»(p, b) ∈ L.carrier",
						BySets(
							aut,
							inM,
							h,
							FieldAutomorphismsDef.At(b.TermAs[FieldOps[A]]("L"), K, M),
							symmetric_group.SymmetricGroupMapsInto.Inst[A]().At(M, p),
							field.SubfieldSubset.At(b.TermAs[FieldOps[A]]("L"), M),
							comm_ring.ZeroIn.Read(field.RingOn.Read(L))))
					b.Show(
						"a finitely supported column with values in L lies in the free module",
						By(finiteSupport, supported, values, function_module.FiniteSuppMember))
				}))
			injective := a.Have(
				"basis values separate the automorphisms",
				"injective_on(field_automorphisms(L, K, M), «evaluation»)",
				Derive(func(b *Argument) {
					b.Do(Simp(Fwd(
						functions.InjectiveOnDef.Inst(TypeBinder.BindA[Permutation[A]](), TypeBinder.BindB[Fun[A, A]]()))))
					x := b.FixAs[Permutation[A]]("x")
					y := b.FixAs[Permutation[A]]("y")
					given := b.Assume()
					agree := b.Have(
						"equal columns agree on B",
						"∀b:A. b ∈ B ⇒ permutation_map(x, b) = permutation_map(y, b)",
						By(Normalized, given))
					b.Show(
						"the basis determines both permutations",
						By(L, h, given, agree, At(basisDetermines, b.TermAs[FieldOps[A]]("L"), K, M, B, x, y)))
				}))
			a.Show(
				"the evaluation columns lie in the free module and separate automorphisms",
				By(carrier, injective))
		})

		evaluationIndependent := ctx.Lemma(Statement{
			Binders: "∀L:field_on(A). ∀K M B:set(A).",
			Hypotheses: []string{
				"subfield(L, K)",
				"subfield(L, M)",
				"K ⊆ M",
				"finite(B)",
				"module_basis(«basisScalars», «basisVectors», B)",
			},
			Conclusion: "module_independent(field_ring(L), " +
				"    «columns», " +
				"    image(«evaluation», field_automorphisms(L, K, M)))",
		}, func(a *Argument, L field.FieldFact[on.L], K, M, B *Expr[Set[A]], h Fact) {
			ring := field.RingOn.Read(L)
			scalars := a.TermAs[module_record.RingOps[A]]("field_ring(L)")
			evaluation := a.TermAs[Fun2[Permutation[A], A, A]]("«evaluation»")
			aut := a.TermAs[Set[Permutation[A]]]("field_automorphisms(L, K, M)")
			properties := a.Have(
				"evaluation has values in the free module and separates automorphisms",
				"(∀p:permutation(A). p ∈ field_automorphisms(L, K, M) ⇒ «evaluation»(p) ∈ «columns».carrier) ∧ "+
					"injective_on(field_automorphisms(L, K, M), «evaluation»)",
				By(L, h, At(evaluationColumns, a.TermAs[FieldOps[A]]("L"), K, M, B)))
			space := a.Have(
				"the columns are a module over L",
				"module_on(field_ring(L), «columns»)",
				By(ring, free_module.FreeModuleOn.At(scalars, B)))
			criterion := a.Have(
				"every finite vanishing combination of the columns has zero coefficients",
				Statement{
					Binders: "∀H:set(permutation(A)). ∀c:(permutation(A) → A).",
					Hypotheses: []string{
						"finite(H)",
						"H ⊆ field_automorphisms(L, K, M)",
						"∀p:permutation(A). p ∈ H ⇒ c(p) ∈ L.carrier",
						"module_sum(«columns».add, " +
							"    «columns».zero, " +
							"    H, " +
							"    λp:permutation(A). «columns».smul(c(p), «evaluation»(p))) = " +
							"«columns».zero",
					},
					Conclusion: "∀p:permutation(A). p ∈ H ⇒ c(p) = L.zero",
				},
				Derive(func(b *Argument) {
					H := b.FixAs[Set[Permutation[A]]]("H")
					c := b.FixAs[Fun[Permutation[A], A]]("c")
					given := b.Assume()
					columnsOfH := b.Have(
						"the columns of H belong to the free module",
						"∀p:permutation(A). p ∈ H ⇒ «evaluation»(p) ∈ «columns».carrier",
						BySets(given, properties))
					rows := b.Have(
						"each coordinate of the zero vector relation vanishes, and on B it reads the automorphisms",
						Statement{
							Binders: "∀b:A.",
							Hypotheses: []string{
								"b ∈ B",
							},
							Conclusion: "module_sum(L.add, L.zero, H, λp:permutation(A). c(p) * permutation_map(p, b)) = " +
								"L.zero",
						},
						Derive(func(d *Argument) {
							x := d.FixAs[A]("b")
							bIn := d.Assume()
							d.Show(
								"at b in B a column reads permutation_map(p, b)",
								By(columnsOfH, given, bIn, free_module.CoordinateRelation.Read(ring).At(B, H, evaluation, c, x)))
						}))
					everywhere := b.Have(
						"extend the coordinate relations from B to all of M",
						Statement{
							Binders: "∀x:A.",
							Hypotheses: []string{
								"x ∈ M",
							},
							Conclusion: "module_sum(L.add, L.zero, H, λp:permutation(A). c(p) * permutation_map(p, x)) = " +
								"L.zero",
						},
						By(L, h, given, rows, At(basisRelation, b.TermAs[FieldOps[A]]("L"), K, M, B, H, c)))
					unrestricted := b.Have(
						"these are automorphisms over the empty fixed set",
						"H ⊆ field_automorphisms(L, ∅, M)",
						BySets(L, given, AutomorphismsAntitone.Read(L).At(b.TermAs[Set[A]]("∅"), K, M)))
					b.Show(
						"Dedekind independence clears every coefficient",
						By(L, h, given, unrestricted, everywhere, Dedekind.Read(L).AsFact().At(M, H, c)))
				}))
			a.Show(
				"the whole evaluation image is independent over L",
				By(
					properties,
					criterion,
					linear_independence.IndependentImageCriterion.Read(space).At(evaluation, aut)))
		})

		return ctx.Theorem(headline, func(
			a *Argument,
			L field.FieldFact[on.L],
			K, M *Expr[Set[A]],
			h Fact,
		) {
			B, basis := a.ObtainAs[Set[A]](
				"choose a finite K-basis of M",
				"∃B:set(A). finite(B) ∧ module_basis(«basisScalars», «basisVectors», B)",
				By(
					h,
					field_extension.FiniteExtensionDef.At(a.TermAs[FieldOps[A]]("L"), K, M),
					module_dimension.FiniteDimensionalDef))
			R := a.TermAs[module_record.RingOps[A]]("field_ring(L)")
			V := a.TermAs[module_record.ModuleOps[A, Fun[A, A]]]("«columns»")
			evaluation := a.TermAs[Fun2[Permutation[A], A, A]]("«evaluation»")
			aut := a.TermAs[Set[Permutation[A]]]("field_automorphisms(L, K, M)")
			image := a.TermAs[Set[Fun[A, A]]]("image(«evaluation», field_automorphisms(L, K, M))")
			inv := a.TermAs[Fun[A, A]]("L.inv")
			fieldRing := field.RingOn.Read(L)
			scalarField := field.FieldRingSubfield.Read(L)
			finiteDim := a.Have(
				"the delta functions are a finite basis of the free module, so it is finite dimensional",
				"finite_dimensional(field_ring(L), «columns»)",
				By(
					basis,
					fieldRing,
					scalarField,
					finite_set.FiniteImage.At(a.TermAs[Fun2[A, A, A]]("λb:A. delta_at(b)"), B),
					free_module.DeltaAtBasis.At(R, B),
					free_module.FreeModuleOn.At(R, B),
					module_dimension.FiniteBasisDim.At(
						R, V, inv, a.TermAs[Set[Fun[A, A]]]("image(λb:A. delta_at(b), B)"))))
			independent := a.Have(
				"the evaluation image is independent over L",
				"module_independent(field_ring(L), «columns», image(«evaluation», field_automorphisms(L, K, M)))",
				By(L, h, basis, At(evaluationIndependent, a.TermAs[FieldOps[A]]("L"), K, M, B)))
			imageBound := a.Have(
				"bound the whole evaluation image by the dimension",
				"finite(image(«evaluation», field_automorphisms(L, K, M))) ∧ "+
					"card(image(«evaluation», field_automorphisms(L, K, M))) ≤ module_dim(field_ring(L), «columns»)",
				By(
					fieldRing,
					finiteDim,
					independent,
					scalarField,
					module_dimension.IndependentBound.At(R, V, inv, image),
					free_module.FreeModuleOn.At(R, B)))
			dimension := a.Have(
				"the free module has one dimension per basis element",
				"module_dim(field_ring(L), «columns») = card(B)",
				By(basis, scalarField, module_dimension.FreeModuleDim.At(R, inv, B)))
			injective := a.Have(
				"evaluation is injective on all the automorphisms",
				"injective_on(field_automorphisms(L, K, M), «evaluation»)",
				By(L, h, basis, At(evaluationColumns, a.TermAs[FieldOps[A]]("L"), K, M, B)))
			finite := a.Have(
				"the finite evaluation image makes the automorphism set finite",
				"finite(field_automorphisms(L, K, M))",
				By(injective, imageBound, finite_set.FiniteImageInjEq.At(evaluation, aut)))
			sameCard := a.Have(
				"injectivity preserves the number of automorphisms",
				"card(image(«evaluation», field_automorphisms(L, K, M))) = card(field_automorphisms(L, K, M))",
				By(finite, injective, cardinality.CardImageInj.At(evaluation, aut)))
			degree := a.Have(
				"the chosen basis counts the extension degree",
				"extension_degree(L, K, M) = card(B)",
				By(L, h, basis, field_extension.BasisDegree.Read(L).At(K, M, B)))
			a.Show(
				"the automorphism set is finite with size bounded by the extension degree",
				ByArith(finite, sameCard, dimension, degree, imageBound))
		})
	}),
})}

// AutomorphismsOrderPositive — for M finite over K, the automorphisms of M fixing
// a set E holding K have a positive count: they lie among those fixing K, which
// are finitely many, and the identity is one of them.
var AutomorphismsOrderPositive = automorphismsOrderPositiveThm{family.Add(registry.ProofEntry{
	Name: "AutomorphismsOrderPositive",
	Key:  "prop_f8425e78670a13a0",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀K E M:set(A).",
		Hypotheses: []string{
			"subfield(L, K)",
			"subfield(L, M)",
			"K ⊆ M",
			"finite_extension(L, K, M)",
			"K ⊆ E",
		},
		Conclusion: "0 < card(field_automorphisms(L, E, M))",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			K, E, M *Expr[Set[A]],
			subfieldK, subfieldM, KInM, finiteM, KInE Fact,
		) {
			automorphisms := a.TermAs[Set[Permutation[A]]]("field_automorphisms(L, E, M)")
			inBaseGroup := a.Have(
				"the group over E lies in the group over K",
				"field_automorphisms(L, E, M) ⊆ field_automorphisms(L, K, M)",
				By(KInE, AutomorphismsAntitone.Read(L).At(K, E, M)))
			finiteGroup := a.Have(
				"so it is finite",
				"finite(field_automorphisms(L, E, M))",
				By(
					subfieldK,
					subfieldM,
					KInM,
					finiteM,
					inBaseGroup,
					AutomorphismsBound.Read(L).At(K, M),
					finite_set.FiniteSubset))
			isSubgroup := a.Have(
				"it is a subgroup of the permutations",
				"subgroup(permutation_group, field_automorphisms(L, E, M))",
				By(AutomorphismsSubgroup.Read(L).At(E, M)))
			identity := a.Have(
				"so it holds the identity",
				"permutation_identity ∈ field_automorphisms(L, E, M)",
				By(group.SubgroupOne.Read(isSubgroup)))
			a.Show(
				"a finite set with a point has a positive count",
				BySets(
					finiteGroup,
					identity,
					cardinality.CardEqZero.At(automorphisms),
					nat_order.PosIffNonzero.At(a.TermAs[Nat]("card(field_automorphisms(L, E, M))"))))
		}),
})}

// ArtinIndependentBound — Artin's lemma: independent elements over a finite
// group's fixed field are no more numerous than the group. Evaluated along
// the group they are columns of a space of dimension |H|, and the crux clears
// a relation among those columns: take one of least support, normalized at
// one coefficient; minimality makes the normalized relation unique, applying
// an automorphism gives another such relation, so its coefficients are fixed;
// its row at the identity then contradicts independence over the fixed field.
var ArtinIndependentBound = artinIndependentBoundThm{family.Add(registry.ProofEntry{
	Name: "ArtinIndependentBound",
	Key:  "prop_491805f557afc3f3",
	Reading: "The subgroup hypothesis is load-bearing: σ of order two alone is " +
		"no group, and M has two members independent over M^σ while card({σ}) = 1.",
	Build: family.Sections(Statement{
		Binders: "∀L:field_on(A). ∀M:set(A). ∀H:set(permutation(A)). ∀I:set(A).",
		Hypotheses: []string{
			"subfield(L, M)",
			"finite(H)",
			"subgroup(permutation_group, H)",
			"H ⊆ field_automorphisms(L, ∅, M)",
			"module_independent(restrict_ring(field_ring(L), fixed_field(M, H)), " +
				"    restrict_module(regular_module(field_ring(L)), M), " +
				"    I)",
		},
		Conclusion: "finite(I) ∧ card(I) ≤ card(H)",
		Abbrev: Abbrev{
			{Name: "evaluation", Text: "λx:A. λp:permutation(A). COND(p ∈ H, permutation_map(p, x), L.zero)"},
			{Name: "evaluationScalars", Text: "restrict_ring(field_ring(L), M)"},
			{Name: "evaluationModule", Text: "free_module_record(«evaluationScalars», H)"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		finiteSums := ctx.Lemma(Statement{
			Binders: "∀L:field_on(A). ∀M:set(A). ∀p:permutation(A). ∀T:set(B). ∀f:(B → A).",
			Hypotheses: []string{
				"subfield(L, M)",
				"p ∈ field_automorphisms(L, ∅, M)",
				"finite(T)",
				"(∀x:B. x ∈ T ⇒ f(x) ∈ M)",
			},
			Conclusion: "permutation_map(p, module_sum(L.add, L.zero, T, f)) = " +
				"module_sum(L.add, L.zero, T, λx:B. permutation_map(p, f(x)))",
		},
			func(
				a *Argument,
				L field.FieldFact[on.L],
				M *Expr[Set[A]],
				p *Expr[Permutation[A]],
				T *Expr[Set[B]],
				f *Arrow[B, A],
				h Fact,
			) {
				parts := a.Conjuncts(
					h,
					"M is a subfield",
					"p is an automorphism",
					"the index set is finite",
					"the summands lie in M")
				sub, aut, finite, values := parts[0], parts[1], parts[2], parts[3]
				restricted := a.Have(
					"M carries the restricted field structure",
					"field_on(restrict_field(L, M))",
					By(L, sub, field.SubfieldFieldOn.Read(L).At(M)))
				additive := a.Have(
					"M is a commutative monoid under addition",
					"comm_monoid_on(M, L.add, L.zero)",
					By(comm_ring.AddMonoidOn.Read(field.RingOn.Read(restricted))))
				keepsAdd := a.Have(
					"p preserves addition on M",
					"∀u v:A. u ∈ M ∧ v ∈ M ⇒ permutation_map(p, u + v) = permutation_map(p, u) + permutation_map(p, v)",
					BySets(aut, FieldAutomorphismsDef.At(a.TermAs[FieldOps[A]]("L"), a.TermAs[Set[A]]("∅"), M)))
				a.Show(
					"p transports the finite sum",
					By(
						keepsAdd,
						sub,
						aut,
						finite,
						values,
						AutomorphismFixesUnits.Read(L).At(a.TermAs[Set[A]]("∅"), M, p),
						module.ModuleSumMonoidHomomorphism.Read(additive).AsFact().At(
							a.TermAs[Op[A]]("L.add"), a.TermAs[A]("L.zero"), a.TermAs[Fun[A, A]]("permutation_map(p)"), T, f)))
			})

		scaleCombination := ctx.Lemma(Statement{
			Binders: "∀L:field_on(A). ∀T:set(B). ∀c v:(B → A). ∀t:A.",
			Hypotheses: []string{
				"finite(T)",
				"t ∈ L.carrier",
				"(∀x:B. x ∈ T ⇒ c(x) ∈ L.carrier ∧ v(x) ∈ L.carrier)",
			},
			Conclusion: "module_sum(L.add, L.zero, T, λx:B. t * c(x) * v(x)) = " +
				"t * module_sum(L.add, L.zero, T, λx:B. c(x) * v(x))",
		}, func(
			a *Argument,
			L field.FieldFact[on.L],
			T *Expr[Set[B]],
			c, v *Arrow[B, A],
			t *Expr[A],
			h Fact,
		) {
			ring := field.RingOn.Read(L)
			regular := module.RegularModuleOn.Read(ring)
			terms := a.Have(
				"associate each scaled summand and check its carrier",
				"∀x:B. x ∈ T ⇒ t * c(x) * v(x) = t * (c(x) * v(x)) ∧ c(x) * v(x) ∈ L.carrier",
				ByArith(L, h, comm_ring.MulIn.Read(ring)))
			a.Show(
				"pull the scalar out of the finite combination",
				By(
					terms,
					h,
					module.ModuleSumCongruence.At(
						a.TermAs[Op[A]]("L.add"),
						a.TermAs[A]("L.zero"),
						T,
						a.TermAs[Fun[B, A]]("λx:B. t * c(x) * v(x)"),
						a.TermAs[Fun[B, A]]("λx:B. t * (c(x) * v(x))")),
					module.ModuleSumSmul.Read(regular).AsFact().At(T, t, a.TermAs[Fun[B, A]]("λx:B. c(x) * v(x)"))))
		})

		subtractCombinations := ctx.Lemma(Statement{
			Binders: "∀L:field_on(A). ∀T:set(B). ∀c d v:(B → A).",
			Hypotheses: []string{
				"finite(T)",
				"(∀x:B. x ∈ T ⇒ c(x) ∈ L.carrier ∧ d(x) ∈ L.carrier ∧ v(x) ∈ L.carrier)",
				"module_sum(L.add, L.zero, T, λx:B. c(x) * v(x)) = module_sum(L.add, L.zero, T, λx:B. d(x) * v(x))",
			},
			Conclusion: "module_sum(L.add, L.zero, T, λx:B. (c(x) - d(x)) * v(x)) = L.zero",
		}, func(a *Argument, L field.FieldFact[on.L], T *Expr[Set[B]], c, d, v *Arrow[B, A], h Fact) {
			ring := field.RingOn.Read(L)
			regular := module.RegularModuleOn.Read(ring)
			terms := a.Have(
				"the termwise difference cancels the second combination",
				Statement{
					Binders: "∀x:B.",
					Hypotheses: []string{
						"x ∈ T",
					},
					Conclusion: "(c(x) - d(x)) * v(x) + d(x) * v(x) = c(x) * v(x) ∧ " +
						"(c(x) - d(x)) * v(x) ∈ L.carrier ∧ " +
						"d(x) * v(x) ∈ L.carrier",
				},
				ByArith(L, h, comm_ring.MulIn.Read(ring), comm_ring.SubIn.Read(ring)))
			sumIdentity := a.Have(
				"sum the cancellation identity",
				"module_sum(L.add, L.zero, T, λx:B. (c(x) - d(x)) * v(x)) + "+
					"module_sum(L.add, L.zero, T, λx:B. d(x) * v(x)) = "+
					"module_sum(L.add, L.zero, T, λx:B. c(x) * v(x))",
				By(
					terms,
					h,
					module.ModuleSumAdd.Read(regular).At(
						T, a.TermAs[Fun[B, A]]("λx:B. (c(x) - d(x)) * v(x)"), a.TermAs[Fun[B, A]]("λx:B. d(x) * v(x)")),
					module.ModuleSumCongruence.At(
						a.TermAs[Op[A]]("L.add"),
						a.TermAs[A]("L.zero"),
						T,
						a.TermAs[Fun[B, A]]("λx:B. (c(x) - d(x)) * v(x) + d(x) * v(x)"),
						a.TermAs[Fun[B, A]]("λx:B. c(x) * v(x)"))))
			sumIn := a.Have(
				"the two sums used for cancellation lie in L",
				"module_sum(L.add, L.zero, T, λx:B. (c(x) - d(x)) * v(x)) ∈ L.carrier ∧ "+
					"module_sum(L.add, L.zero, T, λx:B. d(x) * v(x)) ∈ L.carrier",
				By(
					terms,
					h,
					module.ModuleSumIn.Read(regular).At(T, a.TermAs[Fun[B, A]]("λx:B. (c(x) - d(x)) * v(x)")),
					module.ModuleSumIn.Read(regular).At(T, a.TermAs[Fun[B, A]]("λx:B. d(x) * v(x)"))))
			firstIn := a.Have(
				"the equal original sum lies in L",
				"module_sum(L.add, L.zero, T, λx:B. c(x) * v(x)) ∈ L.carrier",
				By(sumIn, h))
			a.Show(
				"cancel the equal original combinations",
				ByArith(L, sumIdentity, firstIn, sumIn, h))
		})

		deleteZero := ctx.Lemma(Statement{
			Binders: "∀L:field_on(A). ∀T:set(B). ∀c:(B → A). ∀w:B. ∀v:(B → A).",
			Hypotheses: []string{
				"finite(T)",
				"(∀x:B. x ∈ T ⇒ c(x) ∈ L.carrier ∧ v(x) ∈ L.carrier)",
				"c(w) = L.zero",
				"module_sum(L.add, L.zero, T, λx:B. c(x) * v(x)) = L.zero",
			},
			Conclusion: "module_sum(L.add, L.zero, delete(T, w), λx:B. c(x) * v(x)) = L.zero",
		}, func(
			a *Argument,
			L field.FieldFact[on.L],
			T *Expr[Set[B]],
			c *Arrow[B, A],
			w *Expr[B],
			v *Arrow[B, A],
			h Fact,
		) {
			ring := field.RingOn.Read(L)
			regular := module.RegularModuleOn.Read(ring)
			deleted := a.Have(
				"the deleted set omits only w",
				"delete(T, w) ⊆ T ∧ (∀x:B. x ∈ T ∧ x ∉ delete(T, w) ⇒ x = w)",
				BySets())
			terms := a.Have(
				"the omitted summand vanishes",
				"∀x:B. x ∈ T ⇒ c(x) * v(x) ∈ L.carrier ∧ (x ∉ delete(T, w) ⇒ c(x) * v(x) = L.zero)",
				By(Normalized, L, deleted, h, comm_ring.MulIn.Read(ring), comm_ring.MulLeftZeroOn.Read(ring)))
			a.Show(
				"deleting its zero coefficient preserves the relation",
				By(
					terms,
					deleted,
					h,
					module.ModuleSumSupport.Read(regular).At(
						T, a.TermAs[Set[B]]("delete(T, w)"), a.TermAs[Fun[B, A]]("λx:B. c(x) * v(x)"))))
		})

		minimumSupport := ctx.Lemma(Statement{
			Binders: "∀P:(set(A) → bool).",
			Hypotheses: []string{
				"(∃T:set(A). finite(T) ∧ P(T))",
			},
			Conclusion: "∃T:set(A). finite(T) ∧ P(T) ∧ (∀U:set(A). finite(U) ∧ P(U) ⇒ card(T) ≤ card(U))",
		}, func(a *Argument, P *Arrow[Set[A], Bool], h Fact) {
			hasCount := a.Have(
				"finite admissible supports have a cardinality",
				"∃n:num. ∃T:set(A). finite(T) ∧ P(T) ∧ card(T) = n",
				Derive(func(b *Argument) {
					T, data := b.UnpackAs[Set[A]](h, "T")
					b.Take(b.TermAs[Nat]("card(T)"))
					b.Take(T)
					b.Show(
						"this support realizes its cardinality",
						By(data))
				}))
			least := a.Have(
				"choose the least cardinality of an admissible support",
				"∃n:num. "+
					"    (∃T:set(A). finite(T) ∧ P(T) ∧ card(T) = n) ∧ "+
					"    (∀m:num. m < n ⇒ ¬(∃U:set(A). finite(U) ∧ P(U) ∧ card(U) = m))",
				By(
					hasCount,
					nat_order.WellOrdering.At(
						a.TermAs[Fun[Nat, Bool]]("λn:num. ∃T:set(A). finite(T) ∧ P(T) ∧ card(T) = n"))))
			_, leastData := a.UnpackAs[Nat](least, "n")
			parts := a.Conjuncts(
				leastData,
				"the least cardinality is realized",
				"no smaller cardinality is realized")
			T, data := a.UnpackAs[Set[A]](parts[0], "T")
			a.Take(T)
			bound := a.Have(
				"every competing support has at least this cardinality",
				"∀U:set(A). finite(U) ∧ P(U) ⇒ card(T) ≤ card(U)",
				Derive(func(b *Argument) {
					U := b.FixAs[Set[A]]("U")
					given := b.Assume()
					realized := b.Have(
						"the competing support realizes its own cardinality",
						"∃W:set(A). finite(W) ∧ P(W) ∧ card(W) = card(U)",
						Derive(func(c *Argument) {
							c.Take(U)
							c.Show(
								"use U itself",
								By(given))
						}))
					notSmaller := b.Have(
						"its cardinality cannot be smaller",
						"¬(card(U) < n)",
						By(parts[1].At(b.TermAs[Nat]("card(U)")), realized))
					b.Show(
						"compare the two cardinalities",
						ByArith(notSmaller, data))
				}))
			a.Show(
				"the chosen finite support has minimum cardinality",
				By(bound, data))
		})

		normalizeRelation := ctx.Lemma(Statement{
			Binders: "∀L:field_on(A). ∀M:set(A). ∀H:set(permutation(A)). ∀T:set(A). ∀c:(A → A). ∀w:A.",
			Hypotheses: []string{
				"subfield(L, M)",
				"finite(T)",
				"(∀x:A. x ∈ T ⇒ c(x) ∈ M)",
				"(∀p:permutation(A). ∀x:A. p ∈ H ∧ x ∈ T ⇒ permutation_map(p, x) ∈ L.carrier)",
				"w ∈ T",
				"c(w) ≠ L.zero",
				"(∀p:permutation(A). " +
					"    p ∈ H ⇒ module_sum(L.add, L.zero, T, λx:A. c(x) * permutation_map(p, x)) = L.zero)",
			},
			Conclusion: "(∀x:A. x ∈ T ⇒ L.inv(c(w)) * c(x) ∈ M) ∧ " +
				"L.inv(c(w)) * c(w) = L.one ∧ " +
				"(∀q:permutation(A). " +
				"    q ∈ H ⇒ " +
				"    module_sum(L.add, L.zero, T, λx:A. L.inv(c(w)) * c(x) * permutation_map(q, x)) = L.zero)",
		}, func(
			a *Argument,
			L field.FieldFact[on.L],
			M *Expr[Set[A]],
			H *Expr[Set[Permutation[A]]],
			T *Expr[Set[A]],
			c *Arrow[A, A],
			w *Expr[A],
			h Fact,
		) {
			ps := a.Conjuncts(
				h,
				"M is a subfield",
				"T is finite",
				"the coefficients lie in M",
				"the row values lie in L",
				"w lies in T",
				"its coefficient is nonzero",
				"the original rows vanish")
			sub, finite, values, rowValues, wIn, nonzero, rows :=
				ps[0], ps[1], ps[2], ps[3], ps[4], ps[5], ps[6]
			scalar := a.TermAs[A]("L.inv(c(w))")
			inverseIn := a.Have(
				"the normalizing inverse lies in M and L",
				"c(w) ∈ L.carrier ∧ L.inv(c(w)) ∈ M ∧ L.inv(c(w)) ∈ L.carrier",
				BySets(
					values.At(w),
					wIn,
					sub,
					field.SubfieldInv.At(a.TermAs[FieldOps[A]]("L"), M, c.Apply(w)),
					field.SubfieldSubset.At(a.TermAs[FieldOps[A]]("L"), M)))
			normalized := a.Have(
				"scaling stays in M and makes the distinguished coefficient one",
				"(∀x:A. x ∈ T ⇒ L.inv(c(w)) * c(x) ∈ M) ∧ L.inv(c(w)) * c(w) = L.one",
				By(
					L,
					nonzero,
					values,
					sub,
					inverseIn,
					field.SubfieldMul.Inst[A]().At(a.TermAs[FieldOps[A]]("L"), M),
					field.MulLeftInverseOn.Read(L).AsFact().At(c.Apply(w))))
			coefficients := a.Have(
				"the original coefficients lie in L",
				"∀x:A. x ∈ T ⇒ c(x) ∈ L.carrier",
				BySets(values, sub, field.SubfieldSubset.At(a.TermAs[FieldOps[A]]("L"), M)))
			scaledRows := a.Have(
				"scale each zero equation by the normalizing inverse",
				Statement{
					Binders: "∀q:permutation(A).",
					Hypotheses: []string{
						"q ∈ H",
					},
					Conclusion: "module_sum(L.add, L.zero, T, λx:A. (L.inv(c(w)) * c(x)) * permutation_map(q, x)) = " +
						"L.zero",
				},
				Derive(func(b *Argument) {
					q := b.FixAs[Permutation[A]]("q")
					qIn := b.Assume()
					b.Show(
						"a scalar multiple of a zero combination vanishes",
						By(
							L,
							finite,
							coefficients,
							rowValues.At(q),
							rows.At(q),
							qIn,
							inverseIn,
							At(
								scaleCombination,
								a.TermAs[FieldOps[A]]("L"),
								T,
								c,
								b.TermAs[Fun[A, A]]("λx:A. permutation_map(q, x)"),
								scalar),
							comm_ring.MulRightZeroOn.Read(field.RingOn.Read(L)).AsFact().At(scalar)))
				}))
			a.Show(
				"the normalized coefficients retain all vanishing rows",
				By(scaledRows, normalized))
		})

		normalizedUnique := ctx.Lemma(Statement{
			Binders: "∀L:field_on(A). ∀M:set(A). ∀H:set(permutation(A)). ∀T:set(A). ∀c:(A → A). ∀w:A.",
			Hypotheses: []string{
				"subfield(L, M)",
				"finite(T)",
				"(∀x:A. x ∈ T ⇒ c(x) ∈ M)",
				"(∀p:permutation(A). ∀x:A. p ∈ H ∧ x ∈ T ⇒ permutation_map(p, x) ∈ L.carrier)",
				"c(w) = L.one",
				"(∀p:permutation(A). " +
					"    p ∈ H ⇒ module_sum(L.add, L.zero, T, λx:A. c(x) * permutation_map(p, x)) = L.zero)",
				"(∀e:(A → A). " +
					"    (∀x:A. x ∈ delete(T, w) ⇒ e(x) ∈ M) ∧ " +
					"    (∀p:permutation(A). " +
					"        p ∈ H ⇒ " +
					"        module_sum(L.add, L.zero, delete(T, w), λx:A. e(x) * permutation_map(p, x)) = L.zero) ⇒ " +
					"    ∀x:A. x ∈ delete(T, w) ⇒ e(x) = L.zero)",
			},
			Conclusion: "∀d:(A → A). " +
				"    (∀x:A. x ∈ T ⇒ d(x) ∈ M) ∧ " +
				"    d(w) = L.one ∧ " +
				"    (∀p:permutation(A). " +
				"        p ∈ H ⇒ module_sum(L.add, L.zero, T, λx:A. d(x) * permutation_map(p, x)) = L.zero) ⇒ " +
				"    ∀x:A. x ∈ T ⇒ d(x) = c(x)",
		}, func(
			a *Argument,
			L field.FieldFact[on.L],
			M *Expr[Set[A]],
			H *Expr[Set[Permutation[A]]],
			T *Expr[Set[A]],
			c *Arrow[A, A],
			w *Expr[A],
			h Fact,
		) {
			ps := a.Conjuncts(
				h,
				"M is a subfield",
				"T is finite",
				"the coefficients lie in M",
				"the row values lie in L",
				"the distinguished coefficient is one",
				"the original rows vanish",
				"the deleted set admits only the zero relation")
			sub, finite, values, rowValues, one, rows, noDeleted :=
				ps[0], ps[1], ps[2], ps[3], ps[4], ps[5], ps[6]
			d := a.FixAs[Fun[A, A]]("d")
			given := a.Assume()
			carriers := a.Have(
				"both coefficients and their differences lie in the scalar fields",
				"∀x:A. x ∈ T ⇒ c(x) ∈ L.carrier ∧ d(x) ∈ L.carrier ∧ d(x) - c(x) ∈ M ∧ d(x) - c(x) ∈ L.carrier",
				BySets(
					L,
					values,
					sub,
					given,
					field.SubfieldSub.Inst[A]().At(a.TermAs[FieldOps[A]]("L"), M),
					field.SubfieldSubset.At(a.TermAs[FieldOps[A]]("L"), M)))
			zeroAtW := a.Have(
				"the difference vanishes at the normalized coefficient",
				"d(w) - c(w) = L.zero",
				Derive(func(b *Argument) {
					inL := b.Have(
						"both normalized coefficients equal one and lie in L",
						"d(w) ∈ L.carrier ∧ c(w) ∈ L.carrier",
						By(Normalized, one, given, comm_ring.OneIn.Read(field.RingOn.Read(L))))
					b.Show(
						"one minus one is zero",
						ByArith(L, one, inL, given))
				}))
			differenceRows := a.Have(
				"subtract the two normalized relations",
				Statement{
					Binders: "∀p:permutation(A).",
					Hypotheses: []string{
						"p ∈ H",
					},
					Conclusion: "module_sum(L.add, L.zero, T, λx:A. (d(x) - c(x)) * permutation_map(p, x)) = L.zero",
				},
				By(
					L,
					finite,
					carriers,
					rowValues,
					rows,
					given,
					At(subtractCombinations, a.TermAs[FieldOps[A]]("L"), T, d, c)))
			deletedRows := a.Have(
				"drop the zero distinguished difference coefficient",
				Statement{
					Binders: "∀p:permutation(A).",
					Hypotheses: []string{
						"p ∈ H",
					},
					Conclusion: "module_sum(L.add, " +
						"    L.zero, " +
						"    delete(T, w), " +
						"    λx:A. (d(x) - c(x)) * permutation_map(p, x)) = " +
						"L.zero",
				},
				By(
					L,
					finite,
					carriers,
					rowValues,
					differenceRows,
					zeroAtW,
					At(deleteZero, a.TermAs[FieldOps[A]]("L"), T, a.TermAs[Fun[A, A]]("λx:A. d(x) - c(x)"), w)))
			zeroDeleted := a.Have(
				"the deleted relation has every coefficient zero",
				"∀x:A. x ∈ delete(T, w) ⇒ d(x) - c(x) = L.zero",
				BySets(carriers, deletedRows, noDeleted.At(a.TermAs[Fun[A, A]]("λx:A. d(x) - c(x)"))))
			zeroAll := a.Have(
				"restore the distinguished zero coefficient",
				"∀x:A. x ∈ T ⇒ d(x) - c(x) = L.zero",
				BySets(zeroDeleted, zeroAtW))
			a.Show(
				"the normalized relations have equal coefficients",
				ByArith(L, zeroAll, carriers))
		})

		coefficientAction := ctx.Lemma(Statement{
			Binders: "∀L:field_on(A). " +
				"∀M:set(A). " +
				"∀H:set(permutation(A)). " +
				"∀T:set(A). " +
				"∀c:(A → A). " +
				"∀q:permutation(A).",
			Hypotheses: []string{
				"subfield(L, M)",
				"subgroup(permutation_group, H)",
				"H ⊆ field_automorphisms(L, ∅, M)",
				"finite(T)",
				"(∀x:A. x ∈ T ⇒ c(x) ∈ M ∧ x ∈ M)",
				"(∀p:permutation(A). " +
					"    p ∈ H ⇒ module_sum(L.add, L.zero, T, λx:A. c(x) * permutation_map(p, x)) = L.zero)",
				"q ∈ H",
			},
			Conclusion: "∀p:permutation(A). " +
				"    p ∈ H ⇒ " +
				"    module_sum(L.add, L.zero, T, λx:A. permutation_map(q, c(x)) * permutation_map(p, x)) = L.zero",
		},
			func(
				a *Argument,
				L field.FieldFact[on.L],
				M *Expr[Set[A]],
				H *Expr[Set[Permutation[A]]],
				T *Expr[Set[A]],
				c *Arrow[A, A],
				q *Expr[Permutation[A]],
				h Fact,
			) {
				ps := a.Conjuncts(
					h,
					"M is a subfield",
					"H is a subgroup",
					"H consists of automorphisms",
					"T is finite",
					"the coefficients and elements lie in M",
					"all original rows vanish",
					"q lies in H")
				sub, subgroup, automorphisms, finite, values, rows, qIn :=
					ps[0], ps[1], ps[2], ps[3], ps[4], ps[5], ps[6]
				p := a.FixAs[Permutation[A]]("p")
				pIn := a.Assume()
				r := a.TermAs[Permutation[A]]("permutation_compose(permutation_inverse(q), p)")
				rIn := a.Have(
					"the inverse-translated row lies in H",
					"permutation_compose(permutation_inverse(q), p) ∈ H",
					By(pIn, qIn, group.SubgroupMul.Read(subgroup), group.SubgroupInv.Read(subgroup)))
				auts := a.Have(
					"q and its translated row are automorphisms",
					"q ∈ field_automorphisms(L, ∅, M) ∧ "+
						"permutation_compose(permutation_inverse(q), p) ∈ field_automorphisms(L, ∅, M)",
					By(
						qIn,
						rIn,
						automorphisms,
						set_basic.SubsetDef.At(H, a.TermAs[Set[Permutation[A]]]("field_automorphisms(L, ∅, M)"))))
				laws := a.Have(
					"the translated row permutes M and q preserves products",
					"permutation_compose(permutation_inverse(q), p) ∈ symmetric_group(M) ∧ "+
						"(∀u v:A. "+
						"    u ∈ M ∧ v ∈ M ⇒ permutation_map(q, u * v) = permutation_map(q, u) * permutation_map(q, v))",
					BySets(auts, FieldAutomorphismsDef.At(a.TermAs[FieldOps[A]]("L"), a.TermAs[Set[A]]("∅"), M)))
				terms := a.Have(
					"the original translated summands lie in M",
					Statement{
						Binders: "∀x:A.",
						Hypotheses: []string{
							"x ∈ T",
						},
						Conclusion: "permutation_map(permutation_compose(permutation_inverse(q), p), x) ∈ M ∧ " +
							"c(x) * permutation_map(permutation_compose(permutation_inverse(q), p), x) ∈ M",
					},
					By(
						values,
						sub,
						laws,
						symmetric_group.SymmetricGroupMapsInto.Inst[A]().At(M, r),
						field.SubfieldMul.Inst[A]().At(a.TermAs[FieldOps[A]]("L"), M)))
				termwise := a.Have(
					"q transports each product to the desired row",
					Statement{
						Binders: "∀x:A.",
						Hypotheses: []string{
							"x ∈ T",
						},
						Conclusion: "permutation_map(q, " +
							"    c(x) * permutation_map(permutation_compose(permutation_inverse(q), p), x)) = " +
							"permutation_map(q, c(x)) * permutation_map(p, x)",
					},
					By(
						symmetric_group.MapInverseRight.Inst[A]().At(q),
						values,
						terms,
						laws,
						symmetric_group.MapCompose.Inst[A]().At(a.TermAs[Permutation[A]]("permutation_inverse(q)"), p)))
				transported := a.Have(
					"q transports the zero translated relation",
					"module_sum(L.add, "+
						"    L.zero, "+
						"    T, "+
						"    λx:A. "+
						"        permutation_map(q, "+
						"            c(x) * permutation_map(permutation_compose(permutation_inverse(q), p), x))) = "+
						"L.zero",
					By(
						L,
						finite,
						terms,
						rows.At(r),
						rIn,
						sub,
						auts,
						At(
							finiteSums,
							a.TermAs[FieldOps[A]]("L"),
							M,
							q,
							T,
							a.TermAs[Fun[A, A]](
								"λx:A. c(x) * permutation_map(permutation_compose(permutation_inverse(q), p), x)")),
						AutomorphismFixesUnits.Read(L).At(a.TermAs[Set[A]]("∅"), M, q)))
				a.Show(
					"the transformed coefficients give another vanishing relation",
					By(
						termwise,
						transported,
						module.ModuleSumCongruence.At(
							a.TermAs[Op[A]]("L.add"),
							a.TermAs[A]("L.zero"),
							T,
							a.TermAs[Fun[A, A]](
								"λx:A. "+
									"    permutation_map(q, "+
									"        c(x) * permutation_map(permutation_compose(permutation_inverse(q), p), x))"),
							a.TermAs[Fun[A, A]]("λx:A. permutation_map(q, c(x)) * permutation_map(p, x)"))))
			})

		normalizedFixed := ctx.Lemma(Statement{
			Binders: "∀L:field_on(A). ∀M:set(A). ∀H:set(permutation(A)). ∀T:set(A). ∀c:(A → A). ∀w:A.",
			Hypotheses: []string{
				"subfield(L, M)",
				"subgroup(permutation_group, H)",
				"H ⊆ field_automorphisms(L, ∅, M)",
				"finite(T)",
				"(∀x:A. x ∈ T ⇒ c(x) ∈ M ∧ x ∈ M)",
				"c(w) = L.one",
				"(∀p:permutation(A). " +
					"    p ∈ H ⇒ module_sum(L.add, L.zero, T, λx:A. c(x) * permutation_map(p, x)) = L.zero)",
				"(∀d:(A → A). " +
					"    (∀x:A. x ∈ T ⇒ d(x) ∈ M) ∧ " +
					"    d(w) = L.one ∧ " +
					"    (∀p:permutation(A). " +
					"        p ∈ H ⇒ module_sum(L.add, L.zero, T, λx:A. d(x) * permutation_map(p, x)) = L.zero) ⇒ " +
					"    ∀x:A. x ∈ T ⇒ d(x) = c(x))",
			},
			Conclusion: "∀x:A. x ∈ T ⇒ c(x) ∈ fixed_field(M, H)",
		},
			func(
				a *Argument,
				L field.FieldFact[on.L],
				M *Expr[Set[A]],
				H *Expr[Set[Permutation[A]]],
				T *Expr[Set[A]],
				c *Arrow[A, A],
				w *Expr[A],
				h Fact,
			) {
				ps := a.Conjuncts(
					h,
					"M is a subfield",
					"H is a subgroup",
					"H consists of automorphisms",
					"T is finite",
					"the coefficients and elements lie in M",
					"the distinguished coefficient is one",
					"the original rows vanish",
					"the normalized relation is unique")
				sub, subgroup, automorphisms, finite, values, one, rows, unique :=
					ps[0], ps[1], ps[2], ps[3], ps[4], ps[5], ps[6], ps[7]
				fixed := a.Have(
					"every q in H fixes every coefficient",
					"∀q:permutation(A). q ∈ H ⇒ ∀x:A. x ∈ T ⇒ permutation_map(q, c(x)) = c(x)",
					Derive(func(b *Argument) {
						q := b.FixAs[Permutation[A]]("q")
						qIn := b.Assume()
						aut := b.Have(
							"q is an automorphism of M",
							"q ∈ field_automorphisms(L, ∅, M)",
							By(qIn, automorphisms, set_basic.SubsetDef))
						permutes := b.Have(
							"q permutes M",
							"q ∈ symmetric_group(M)",
							BySets(aut, FieldAutomorphismsDef.At(b.TermAs[FieldOps[A]]("L"), b.TermAs[Set[A]]("∅"), M)))
						coeffIn := b.Have(
							"the transported coefficients remain in M",
							"∀x:A. x ∈ T ⇒ permutation_map(q, c(x)) ∈ M",
							By(values, permutes, symmetric_group.SymmetricGroupMapsInto.Inst[A]().At(M, q)))
						normalized := b.Have(
							"transport preserves the coefficient one",
							"permutation_map(q, c(w)) = L.one",
							By(Normalized, L, one, aut, sub, AutomorphismFixesUnits.Read(L).At(b.TermAs[Set[A]]("∅"), M, q)))
						transported := b.Have(
							"transport preserves all vanishing rows",
							Statement{
								Binders: "∀p:permutation(A).",
								Hypotheses: []string{
									"p ∈ H",
								},
								Conclusion: "module_sum(L.add, " +
									"    L.zero, " +
									"    T, " +
									"    λx:A. permutation_map(q, c(x)) * permutation_map(p, x)) = " +
									"L.zero",
							},
							By(L, finite, values, rows, qIn, sub, subgroup, automorphisms, coefficientAction))
						b.Show(
							"normalized uniqueness identifies the transported relation",
							By(
								coeffIn,
								transported,
								normalized,
								unique.At(b.TermAs[Fun[A, A]]("λx:A. permutation_map(q, c(x))"))))
					}))
				a.Show(
					"the coefficients belong to the fixed field",
					BySets(values, fixed, FixedFieldDef.At(M, H)))
			})

		identityRow := ctx.Lemma(Statement{
			Binders: "∀L:field_on(A). ∀M:set(A). ∀H:set(permutation(A)). ∀I T:set(A). ∀c:(A → A). ∀w:A.",
			Hypotheses: []string{
				"subgroup(permutation_group, H)",
				"module_independent(restrict_ring(field_ring(L), fixed_field(M, H)), " +
					"    restrict_module(regular_module(field_ring(L)), M), " +
					"    I)",
				"finite(T)",
				"T ⊆ I",
				"(∀x:A. x ∈ T ⇒ c(x) ∈ fixed_field(M, H))",
				"(∀p:permutation(A). " +
					"    p ∈ H ⇒ module_sum(L.add, L.zero, T, λx:A. c(x) * permutation_map(p, x)) = L.zero)",
				"w ∈ T",
			},
			Conclusion: "c(w) = L.zero",
		}, func(
			a *Argument,
			L field.FieldFact[on.L],
			M *Expr[Set[A]],
			H *Expr[Set[Permutation[A]]],
			I, T *Expr[Set[A]],
			c *Arrow[A, A],
			w *Expr[A],
			h Fact,
		) {
			ps := a.Conjuncts(
				h,
				"H is a subgroup",
				"I is independent over the fixed field",
				"T is finite",
				"T lies in I",
				"the coefficients lie in the fixed field",
				"every automorphism row vanishes",
				"w lies in T")
			subgroup, independent, finite, subset, coefficients, rows, wIn :=
				ps[0], ps[1], ps[2], ps[3], ps[4], ps[5], ps[6]
			id := a.TermAs[Permutation[A]]("permutation_identity⟨A:A⟩")
			idIn := a.Have(
				"the identity permutation lies in H",
				"permutation_identity⟨A:A⟩ ∈ H",
				By(group.SubgroupOne.Read(subgroup)))
			dependence := a.Have(
				"the identity row is a relation among the original elements",
				"module_sum(L.add, L.zero, T, λx:A. c(x) * x) = L.zero",
				By(rows.At(id), idIn, symmetric_group.MapIdentity))
			a.Show(
				"fixed-field independence clears the distinguished coefficient",
				By(
					finite,
					coefficients,
					dependence,
					wIn,
					subset,
					independent,
					linear_independence.IndependentVanishingCombination.At(
						a.TermAs[module_record.RingOps[A]]("restrict_ring(field_ring(L), fixed_field(M, H))"),
						a.TermAs[module_record.ModuleOps[A, A]]("restrict_module(regular_module(field_ring(L)), M)"),
						I,
						T,
						c,
						w)))
		})

		columnIndependence := ctx.Lemma(Statement{
			Binders: "∀L:field_on(A). ∀M:set(A). ∀H:set(permutation(A)). ∀I T:set(A). ∀c:(A → A). ∀w:A.",
			Hypotheses: []string{
				"subfield(L, M)",
				"subgroup(permutation_group, H)",
				"H ⊆ field_automorphisms(L, ∅, M)",
				"module_independent(restrict_ring(field_ring(L), fixed_field(M, H)), " +
					"    restrict_module(regular_module(field_ring(L)), M), " +
					"    I)",
				"I ⊆ M",
				"finite(T)",
				"T ⊆ I",
				"(∀x:A. x ∈ T ⇒ c(x) ∈ M)",
				"(∀p:permutation(A). " +
					"    p ∈ H ⇒ module_sum(L.add, L.zero, T, λx:A. c(x) * permutation_map(p, x)) = L.zero)",
				"w ∈ T",
			},
			Conclusion: "c(w) = L.zero",
			Abbrev: Abbrev{
				{Name: "relationSupport", Text: "λU:set(A). " +
					"    U ⊆ I ∧ " +
					"    (∃d:(A → A). ∃z:A. " +
					"        (∀x:A. x ∈ U ⇒ d(x) ∈ M) ∧ " +
					"        (∀p:permutation(A). " +
					"            p ∈ H ⇒ " +
					"            module_sum(L.add, L.zero, U, λx:A. d(x) * permutation_map(p, x)) = L.zero) ∧ " +
					"        z ∈ U ∧ " +
					"        d(z) ≠ L.zero)"},
			},
		}, func(
			a *Argument,
			L field.FieldFact[on.L],
			M *Expr[Set[A]],
			H *Expr[Set[Permutation[A]]],
			I, T *Expr[Set[A]],
			c *Arrow[A, A],
			w *Expr[A],
			h Fact,
		) {
			ps := a.Conjuncts(
				h,
				"M is a subfield",
				"H is a subgroup",
				"H consists of automorphisms",
				"I is independent over the fixed field",
				"I lies in M",
				"T is finite",
				"T lies in I",
				"the coefficients lie in M",
				"all rows vanish",
				"w lies in T")
			sub, subgroup, automorphisms, independent, inM, finite, subset, coefficients, rows, wIn :=
				ps[0], ps[1], ps[2], ps[3], ps[4], ps[5], ps[6], ps[7], ps[8], ps[9]
			nonzero := a.SupposeNot()
			initial := a.Have(
				"the supposed nonzero relation gives an admissible finite support",
				"∃U:set(A). finite(U) ∧ «relationSupport»(U)",
				Derive(func(b *Argument) {
					b.Take(T)
					witness := b.Have(
						"use the original coefficients and distinguished member",
						"∃d:(A → A). ∃z:A. "+
							"    (∀x:A. x ∈ T ⇒ d(x) ∈ M) ∧ "+
							"    (∀p:permutation(A). "+
							"        p ∈ H ⇒ module_sum(L.add, L.zero, T, λx:A. d(x) * permutation_map(p, x)) = L.zero) ∧ "+
							"    z ∈ T ∧ "+
							"    d(z) ≠ L.zero",
						Derive(func(arg *Argument) {
							arg.Take(c)
							arg.Take(w)
							arg.Show(
								"the original relation is nonzero",
								By(coefficients, rows, wIn, nonzero))
						}))
					b.Show(
						"T is a finite admissible support",
						By(finite, subset, witness))
				}))
			selected := a.Have(
				"select a nonzero relation of minimum support cardinality",
				"∃U:set(A). "+
					"    finite(U) ∧ "+
					"    «relationSupport»(U) ∧ "+
					"    (∀W:set(A). finite(W) ∧ «relationSupport»(W) ⇒ card(U) ≤ card(W))",
				By(initial, At(minimumSupport, a.TermAs[Fun[Set[A], Bool]]("«relationSupport»"))))
			U, minimum := a.UnpackAs[Set[A]](selected, "U")
			ms := a.Conjuncts(
				minimum,
				"U is finite",
				"U lies in I",
				"U carries a nonzero relation",
				"U has minimum support cardinality")
			finiteU, subsetU, hasRelation, comparison := ms[0], ms[1], ms[2], ms[3]
			d, z, relation := a.Unpack2As[Fun[A, A], A](hasRelation, "d", "z")
			deletion := a.Have(
				"deleting z reduces the support cardinality by one",
				"finite(delete(U, z)) ∧ delete(U, z) ⊆ I ∧ card(U) = suc(card(delete(U, z)))",
				BySets(
					finiteU,
					subsetU,
					relation,
					finite_set.FiniteDeleteImp.At(U, z),
					cardinality.CountsOneMore.At(U, z)))
			noDeleted := a.Have(
				"the smaller support admits only the zero relation",
				Statement{
					Binders: "∀e:(A → A).",
					Hypotheses: []string{
						"(∀x:A. x ∈ delete(U, z) ⇒ e(x) ∈ M)",
						"(∀p:permutation(A). " +
							"    p ∈ H ⇒ module_sum(L.add, L.zero, delete(U, z), λx:A. e(x) * permutation_map(p, x)) = L.zero)",
					},
					Conclusion: "∀x:A. x ∈ delete(U, z) ⇒ e(x) = L.zero",
				},
				Derive(func(b *Argument) {
					e := b.FixAs[Fun[A, A]]("e")
					given := b.Assume()
					x := b.FixAs[A]("x")
					xIn := b.Assume()
					notZero := b.SupposeNot()
					smaller := b.Have(
						"a nonzero smaller relation would be admissible",
						"«relationSupport»(delete(U, z))",
						Derive(func(arg *Argument) {
							witness := arg.Have(
								"the smaller relation has a nonzero coefficient",
								"∃v:(A → A). ∃y:A. "+
									"    (∀t:A. t ∈ delete(U, z) ⇒ v(t) ∈ M) ∧ "+
									"    (∀q:permutation(A). "+
									"        q ∈ H ⇒ "+
									"        module_sum(L.add, L.zero, delete(U, z), λt:A. v(t) * permutation_map(q, t)) = L.zero) ∧ "+
									"    y ∈ delete(U, z) ∧ "+
									"    v(y) ≠ L.zero",
								Derive(func(inner *Argument) {
									inner.Take(e)
									inner.Take(x)
									inner.Show(
										"use the smaller relation and x",
										By(given, xIn, notZero))
								}))
							arg.Show(
								"its support still lies in I",
								By(deletion, witness))
						}))
					bound := b.Have(
						"minimality would bound U by its deletion",
						"card(U) ≤ card(delete(U, z))",
						By(comparison.At(b.TermAs[Set[A]]("delete(U, z)")), smaller, deletion))
					b.Show(
						"a set cannot be at most one member fewer than itself",
						ByArith(bound, deletion))
				}))
			values := a.Have(
				"the minimum relation's coefficients and elements lie in M",
				"∀x:A. x ∈ U ⇒ d(x) ∈ M ∧ x ∈ M",
				BySets(inM, subsetU, relation))
			rowValues := a.Have(
				"automorphism row values lie in L",
				"∀p:permutation(A). ∀x:A. p ∈ H ∧ x ∈ U ⇒ permutation_map(p, x) ∈ L.carrier",
				BySets(
					values,
					sub,
					automorphisms,
					field.SubfieldSubset.At(a.TermAs[FieldOps[A]]("L"), M),
					FieldAutomorphismsDef.At(a.TermAs[FieldOps[A]]("L"), a.TermAs[Set[A]]("∅"), M),
					symmetric_group.SymmetricGroupMapsInto.Inst[A]().At(M)))
			normalized := a.Have(
				"normalize the minimum relation at z",
				"(∀x:A. x ∈ U ⇒ L.inv(d(z)) * d(x) ∈ M) ∧ "+
					"L.inv(d(z)) * d(z) = L.one ∧ "+
					"(∀q:permutation(A). "+
					"    q ∈ H ⇒ "+
					"    module_sum(L.add, L.zero, U, λx:A. (L.inv(d(z)) * d(x)) * permutation_map(q, x)) = L.zero)",
				By(
					L,
					finiteU,
					values,
					sub,
					rowValues,
					relation,
					At(normalizeRelation, a.TermAs[FieldOps[A]]("L"), M, H, U, d, z)))
			normalizedValues := a.Have(
				"normalization keeps coefficients and elements in M",
				"∀x:A. x ∈ U ⇒ L.inv(d(z)) * d(x) ∈ M ∧ x ∈ M",
				By(values, normalized))
			normalizedCoefficients := a.TermAs[Fun[A, A]]("λx:A. L.inv(d(z)) * d(x)")
			unique := a.Have(
				"the normalized minimum relation is unique",
				Statement{
					Binders: "∀b:(A → A).",
					Hypotheses: []string{
						"(∀x:A. x ∈ U ⇒ b(x) ∈ M)",
						"b(z) = L.one",
						"(∀p:permutation(A). " +
							"    p ∈ H ⇒ module_sum(L.add, L.zero, U, λx:A. b(x) * permutation_map(p, x)) = L.zero)",
					},
					Conclusion: "∀x:A. x ∈ U ⇒ b(x) = L.inv(d(z)) * d(x)",
				},
				By(
					L,
					finiteU,
					normalizedValues,
					noDeleted,
					sub,
					rowValues,
					normalized,
					At(normalizedUnique, a.TermAs[FieldOps[A]]("L"), M, H, U, normalizedCoefficients, z)))
			fixed := a.Have(
				"the normalized coefficients lie in the fixed field",
				"∀x:A. x ∈ U ⇒ L.inv(d(z)) * d(x) ∈ fixed_field(M, H)",
				By(
					L,
					finiteU,
					normalizedValues,
					unique,
					sub,
					subgroup,
					automorphisms,
					normalized,
					At(normalizedFixed, a.TermAs[FieldOps[A]]("L"), M, H, U, normalizedCoefficients, z)))
			zero := a.Have(
				"the identity row forces its distinguished coefficient to zero",
				"L.inv(d(z)) * d(z) = L.zero",
				By(
					L,
					finiteU,
					fixed,
					subgroup,
					subsetU,
					normalized,
					relation,
					independent,
					At(identityRow, a.TermAs[FieldOps[A]]("L"), M, H, I, U, normalizedCoefficients, z)))
			a.Show(
				"the distinguished coefficient cannot be both one and zero",
				By(field.OneNotZeroOn.Read(L), zero, normalized))
		})

		evaluationColumns := ctx.Lemma(Statement{
			Binders: "∀L:field_on(A). ∀M:set(A). ∀H:set(permutation(A)).",
			Hypotheses: []string{
				"subfield(L, M)",
				"finite(H)",
				"subgroup(permutation_group, H)",
				"H ⊆ field_automorphisms(L, ∅, M)",
			},
			Conclusion: "(∀x:A. x ∈ M ⇒ «evaluation»(x) ∈ «evaluationModule».carrier) ∧ " +
				"injective_on(M, «evaluation»)",
		}, func(
			a *Argument,
			L field.FieldFact[on.L],
			M *Expr[Set[A]],
			H *Expr[Set[Permutation[A]]],
			h Fact,
		) {
			ps := a.Conjuncts(
				h,
				"M is a subfield",
				"H is finite",
				"H is a subgroup",
				"H consists of automorphisms")
			sub, finite, subgroup, automorphisms := ps[0], ps[1], ps[2], ps[3]
			maps := a.Have(
				"the automorphisms send M into M",
				"∀p:permutation(A). ∀x:A. p ∈ H ∧ x ∈ M ⇒ permutation_map(p, x) ∈ M",
				BySets(
					automorphisms,
					FieldAutomorphismsDef.At(a.TermAs[FieldOps[A]]("L"), a.TermAs[Set[A]]("∅"), M),
					symmetric_group.SymmetricGroupMapsInto.Inst[A]().At(M)))
			carrier := a.Have(
				"each evaluation column belongs to the free module",
				"∀x:A. x ∈ M ⇒ «evaluation»(x) ∈ «evaluationModule».carrier",
				Derive(func(b *Argument) {
					b.FixAs[A]("x")
					xIn := b.Assume()
					support := b.TermAs[Set[Permutation[A]]](
						"fun_support(L.zero, λp:permutation(A). «evaluation»(x, p))")
					supported := b.Have(
						"the nonzero coordinates lie in H",
						"fun_support(L.zero, λp:permutation(A). «evaluation»(x, p)) ⊆ H",
						BySets())
					finiteSupport := b.Have(
						"the column has finite support",
						"finite(fun_support(L.zero, λp:permutation(A). «evaluation»(x, p)))",
						By(finite, supported, finite_set.FiniteSubset.At(support, H)))
					values := b.Have(
						"all column values lie in M",
						"∀p:permutation(A). «evaluation»(x, p) ∈ M",
						BySets(maps, xIn, sub, field.SubfieldZero.At(b.TermAs[FieldOps[A]]("L"), M)))
					b.Show(
						"a finitely supported column with values in M lies in the free module",
						By(
							finiteSupport,
							values,
							supported,
							function_module.FiniteSuppMember.At(
								b.TermAs[A]("L.zero"), M, H, b.TermAs[Fun[Permutation[A], A]]("«evaluation»(x)"))))
				}))
			idIn := a.Have(
				"the identity permutation lies in H",
				"permutation_identity⟨A:A⟩ ∈ H",
				By(group.SubgroupOne.Read(subgroup)))
			injective := a.Have(
				"the identity coordinate separates the evaluation columns",
				"injective_on(M, «evaluation»)",
				Derive(func(b *Argument) {
					b.Do(Simp(Fwd(
						functions.InjectiveOnDef.Inst(TypeBinder.BindA[A](), TypeBinder.BindB[Fun[Permutation[A], A]]()))))
					b.FixAs[A]("x")
					b.FixAs[A]("y")
					given := b.Conjuncts(
						b.Assume(),
						"x lies in M",
						"y lies in M",
						"their evaluation columns are equal")
					atIdentity := b.Have(
						"evaluate the equal columns at the identity",
						"«evaluation»(x, permutation_identity⟨A:A⟩) = «evaluation»(y, permutation_identity⟨A:A⟩)",
						By(Normalized, given[2]))
					b.Show(
						"the identity coordinate is the original element",
						By(atIdentity, idIn, symmetric_group.MapIdentity))
				}))
			a.Show(
				"the evaluation columns have the required carrier and separate points",
				By(carrier, injective))
		})

		evaluationIndependent := ctx.Lemma(Statement{
			Binders: "∀L:field_on(A). ∀M:set(A). ∀H:set(permutation(A)). ∀I:set(A).",
			Hypotheses: []string{
				"subfield(L, M)",
				"finite(H)",
				"subgroup(permutation_group, H)",
				"H ⊆ field_automorphisms(L, ∅, M)",
				"module_independent(restrict_ring(field_ring(L), fixed_field(M, H)), " +
					"    restrict_module(regular_module(field_ring(L)), M), " +
					"    I)",
			},
			Conclusion: "comm_ring_on(«evaluationScalars») ∧ " +
				"module_on(«evaluationScalars», «evaluationModule») ∧ " +
				"module_independent(«evaluationScalars», «evaluationModule», image(«evaluation», I)) ∧ " +
				"injective_on(I, «evaluation»)",
		}, func(
			a *Argument,
			L field.FieldFact[on.L],
			M *Expr[Set[A]],
			H *Expr[Set[Permutation[A]]],
			I *Expr[Set[A]],
			h Fact,
		) {
			ps := a.Conjuncts(
				h,
				"M is a subfield",
				"H is finite",
				"H is a subgroup",
				"H consists of automorphisms",
				"I is independent over the fixed field")
			sub, finite, subgroup, automorphisms, independent := ps[0], ps[1], ps[2], ps[3], ps[4]
			evaluation := a.TermAs[Fun2[A, Permutation[A], A]]("«evaluation»")
			scalars := a.TermAs[module_record.RingOps[A]]("«evaluationScalars»")
			scalarRing := a.Have(
				"M supplies the scalar ring",
				"comm_ring_on(«evaluationScalars»)",
				By(sub, field.SubfieldCommRing.Read(L).At(M)))
			inM := a.Have(
				"I lies in M",
				"I ⊆ M",
				By(
					independent,
					linear_independence.IndependentInCarrier.At(
						a.TermAs[module_record.RingOps[A]]("restrict_ring(field_ring(L), fixed_field(M, H))"),
						a.TermAs[module_record.ModuleOps[A, A]]("restrict_module(regular_module(field_ring(L)), M)"),
						I)))
			properties := a.Have(
				"the evaluation columns lie in the free module and separate points",
				"(∀x:A. x ∈ M ⇒ «evaluation»(x) ∈ «evaluationModule».carrier) ∧ injective_on(M, «evaluation»)",
				By(
					L,
					finite,
					sub,
					subgroup,
					automorphisms,
					At(evaluationColumns, a.TermAs[FieldOps[A]]("L"), M, H)))
			space := a.Have(
				"the columns are a module over M",
				"module_on(«evaluationScalars», «evaluationModule»)",
				By(scalarRing, free_module.FreeModuleOn.At(scalars, H)))
			injective := a.Have(
				"the identity coordinate separates the members of I",
				"injective_on(I, «evaluation»)",
				By(inM, properties, functions.InjectiveOnSubset.At(evaluation, I, M)))
			columnsOfI := a.Have(
				"the columns of I belong to the free module",
				"∀x:A. x ∈ I ⇒ «evaluation»(x) ∈ «evaluationModule».carrier",
				BySets(inM, properties))
			criterion := a.Have(
				"every finite vanishing combination of the columns of I has zero coefficients",
				Statement{
					Binders: "∀T:set(A). ∀c:(A → A).",
					Hypotheses: []string{
						"finite(T)",
						"T ⊆ I",
						"(∀x:A. x ∈ T ⇒ c(x) ∈ M)",
						"module_sum(«evaluationModule».add, " +
							"    «evaluationModule».zero, " +
							"    T, " +
							"    λx:A. «evaluationModule».smul(c(x), «evaluation»(x))) = " +
							"«evaluationModule».zero",
					},
					Conclusion: "∀x:A. x ∈ T ⇒ c(x) = L.zero",
				},
				Derive(func(b *Argument) {
					T := b.FixAs[Set[A]]("T")
					c := b.FixAs[Fun[A, A]]("c")
					given := b.Assume()
					columnsOfT := b.Have(
						"the columns of T belong to the free module",
						"∀x:A. x ∈ T ⇒ «evaluation»(x) ∈ «evaluationModule».carrier",
						BySets(given, columnsOfI))
					rows := b.Have(
						"each coordinate of the vector relation vanishes, and at p in H it is the row of p",
						Statement{
							Binders: "∀p:permutation(A).",
							Hypotheses: []string{
								"p ∈ H",
							},
							Conclusion: "module_sum(L.add, L.zero, T, λx:A. c(x) * permutation_map(p, x)) = L.zero",
						},
						Derive(func(d *Argument) {
							p := d.FixAs[Permutation[A]]("p")
							pIn := d.Assume()
							d.Show(
								"at p in H a column reads permutation_map(p, x)",
								By(
									columnsOfT,
									given,
									pIn,
									free_module.CoordinateRelation.Read(scalarRing).At(H, T, evaluation, c, p)))
						}))
					b.Show(
						"column independence, the least-support argument, clears the coefficients",
						By(
							L,
							given,
							rows,
							sub,
							subgroup,
							automorphisms,
							independent,
							inM,
							At(columnIndependence, a.TermAs[FieldOps[A]]("L"), M, H, I, T, c)))
				}))
			a.Show(
				"the evaluation image is independent over M",
				By(
					scalarRing,
					space,
					columnsOfI,
					injective,
					criterion,
					linear_independence.IndependentImageCriterion.Read(space).At(evaluation, I)))
		})

		return ctx.Theorem(headline, func(
			a *Argument,
			L field.FieldFact[on.L],
			M *Expr[Set[A]],
			H *Expr[Set[Permutation[A]]],
			I *Expr[Set[A]],
			h Fact,
		) {
			R := a.TermAs[module_record.RingOps[A]]("«evaluationScalars»")
			V := a.TermAs[module_record.ModuleOps[A, Fun[Permutation[A], A]]]("«evaluationModule»")
			evaluation := a.TermAs[Fun2[A, Permutation[A], A]]("«evaluation»")
			image := a.TermAs[Set[Fun[Permutation[A], A]]]("image(«evaluation», I)")
			inv := a.TermAs[Fun[A, A]]("L.inv")
			scalarField := a.Have(
				"the scalar ring is a field on its carrier",
				"ring_subfield(«evaluationScalars», L.inv, «evaluationScalars».carrier)",
				Derive(func(b *Argument) {
					carrier := b.Have(
						"the scalar ring has carrier M",
						"«evaluationScalars».carrier = M",
						Simp(Fwd(module_record.RestrictRingDef)),
						Basic())
					b.Show(
						"M inherits L's field operations",
						By(L, carrier, h, field.SubfieldRingSubfield.Read(L).At(M, M)))
				}))
			embedded := a.Have(
				"evaluation embeds I as independent columns of a module over M",
				"comm_ring_on(«evaluationScalars») ∧ "+
					"module_on(«evaluationScalars», «evaluationModule») ∧ "+
					"module_independent(«evaluationScalars», «evaluationModule», image(«evaluation», I)) ∧ "+
					"injective_on(I, «evaluation»)",
				By(L, h, At(evaluationIndependent, a.TermAs[FieldOps[A]]("L"), M, H, I)))
			finiteDim := a.Have(
				"the delta functions are a finite basis of the free module, so it is finite dimensional",
				"finite_dimensional(«evaluationScalars», «evaluationModule»)",
				By(
					h,
					embedded,
					scalarField,
					finite_set.FiniteImage.At(
						a.TermAs[Fun2[Permutation[A], Permutation[A], A]](
							"λp:permutation(A). delta_at(«evaluationScalars».zero, «evaluationScalars».one, p)"),
						H),
					free_module.DeltaAtBasis.At(R, H),
					module_dimension.FiniteBasisDim.At(
						R,
						V,
						inv,
						a.TermAs[Set[Fun[Permutation[A], A]]](
							"image(λp:permutation(A). delta_at(«evaluationScalars».zero, «evaluationScalars».one, p), H)"))))
			imageBound := a.Have(
				"bound the independent evaluation image by the dimension",
				"finite(image(«evaluation», I)) ∧ "+
					"card(image(«evaluation», I)) ≤ module_dim(«evaluationScalars», «evaluationModule»)",
				By(embedded, finiteDim, scalarField, module_dimension.IndependentBound.At(R, V, inv, image)))
			dimension := a.Have(
				"its dimension is the cardinality of H",
				"module_dim(«evaluationScalars», «evaluationModule») = card(H)",
				By(h, scalarField, module_dimension.FreeModuleDim.At(R, inv, H)))
			finiteI := a.Have(
				"the finite evaluation image makes I finite",
				"finite(I)",
				By(embedded, imageBound, finite_set.FiniteImageInjEq.At(evaluation, I)))
			sameCard := a.Have(
				"injectivity preserves the cardinality of I",
				"card(image(«evaluation», I)) = card(I)",
				By(finiteI, embedded, cardinality.CardImageInj.At(evaluation, I)))
			a.Show(
				"I is finite with at most card(H) elements",
				ByArith(finiteI, sameCard, dimension, imageBound))
		})
	}),
})}

// ArtinFixedField — Artin's theorem: a finite group H of automorphisms
// of M makes M a finite extension of the field H fixes, of degree the
// order of H. A basis of M over M^H is independent, so by Artin's lemma
// it is finite with at most |H| members, and it counts the degree; and H
// lies among the automorphisms of M fixing M^H, which are no more than
// the degree.
var ArtinFixedField = artinFixedFieldThm{family.Add(registry.ProofEntry{
	Name: "ArtinFixedField",
	Key:  "prop_ea897d29804b5fd6",
	Reading: "The subgroup hypothesis is load-bearing: H = {σ} with σ " +
		"of order two is no group, and [M : M^σ] = 2. So is finite(H): the " +
		"integer translations of ℚ(t) fix ℚ, and ℚ(t) is not finite over ℚ.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀M:set(A). ∀H:set(permutation(A)).",
		Hypotheses: []string{
			"subfield(L, M)",
			"finite(H)",
			"subgroup(permutation_group, H)",
			"H ⊆ field_automorphisms(L, ∅, M)",
		},
		Conclusion: "finite_extension(L, fixed_field(M, H), M) ∧ " +
			"extension_degree(L, fixed_field(M, H), M) = card(H)",
	},
		func(a *Argument, L field.FieldFact[on.L], M *Expr[Set[A]], H *Expr[Set[Permutation[A]]], h Fact) {
			parts := a.Conjuncts(
				h,
				"M is a subfield of L",
				"H is finite",
				"H is a group under composition",
				"the members of H are automorphisms of M")
			subM, finH, groupH, onAut := parts[0], parts[1], parts[2], parts[3]
			fixed := a.TermAs[Set[A]]("fixed_field(M, H)")
			subF := a.Have(
				"the field H fixes is a subfield of L",
				"subfield(L, fixed_field(M, H))",
				By(subM, onAut, FixedFieldSubfield.Read(L).At(M, H)))
			fInM := a.Have(
				"the field H fixes lies in M",
				"fixed_field(M, H) ⊆ M",
				Unfold(FixedFieldDef),
				BySets())
			space := a.Have(
				"M is a vector space over the field H fixes",
				"module_on(restrict_ring(field_ring(L), fixed_field(M, H)), "+
					"    restrict_module(regular_module(field_ring(L)), M))",
				By(subF, subM, fInM, field_extension.ExtensionModuleOn.Read(L).At(fixed, M)))
			inv := a.TermAs[Fun[A, A]]("L.inv")
			scalarsField := a.Have(
				"the field H fixes, a subfield, is a field under L's operations, with L's inverse",
				"ring_subfield(restrict_ring(field_ring(L), fixed_field(M, H)), L.inv, fixed_field(M, H))",
				By(subF, field.SubfieldRingSubfield.Read(L).At(fixed, fixed)))

			E, basis := a.ObtainAs[Set[A]](
				"M has a basis E over the field H fixes",
				"∃E:set(A). "+
					"    module_basis(restrict_ring(field_ring(L), fixed_field(M, H)), "+
					"        restrict_module(regular_module(field_ring(L)), M), "+
					"        E)",
				By(scalarsField, linear_independence.BasisExists.Read(space).At(inv)))
			independent := a.Conjuncts(
				a.Unfolded(basis, linear_independence.ModuleBasisDef),
				"E is independent over the field H fixes",
				"and spans M over it")[0]
			small := a.Have(
				"so, by Artin's lemma, E is finite with at most card(H) members",
				"finite(E) ∧ card(E) ≤ card(H)",
				By(subM, finH, groupH, onAut, independent, ArtinIndependentBound.Read(L).At(M, H, E)))
			finite := a.Have(
				"so M is finite over the field H fixes, and [M : M^H] is the size of the finite basis E",
				"finite_extension(L, fixed_field(M, H), M) ∧ extension_degree(L, fixed_field(M, H), M) = card(E)",
				By(subF, subM, fInM, small, basis, field_extension.BasisDegree.Read(L).At(fixed, M, E)))

			automorphisms := a.TermAs[Set[Permutation[A]]]("field_automorphisms(L, fixed_field(M, H), M)")
			bound := a.Have(
				"the automorphisms of M fixing the field H fixes are finitely many, no more than [M : M^H]",
				"finite(field_automorphisms(L, fixed_field(M, H), M)) ∧ "+
					"card(field_automorphisms(L, fixed_field(M, H), M)) ≤ extension_degree(L, fixed_field(M, H), M)",
				By(subF, subM, fInM, finite, AutomorphismsBound.Read(L).At(fixed, M)))
			lower := a.Have(
				"H lies among them, so it has no more members",
				"card(H) ≤ card(field_automorphisms(L, fixed_field(M, H), M))",
				By(
					bound,
					onAut,
					FixedFieldAutomorphisms.Read(L).At(M, H),
					cardinality.CardSubset.At(H, automorphisms)))

			a.Show(
				"M is finite over M^H, and [M : M^H] = card(E) ≤ "+
					"card(H) ≤ card(Aut_{M^H}(M)) ≤ [M : M^H] are all equal",
				ByArith(finite, small, lower, bound))
		}),
})}

// ArtinAutomorphisms — the automorphisms of M fixing the field a finite
// group H fixes are exactly H. H fixes its fixed field F, so H ⊆ Aut_F(M);
// Aut_F(M) has at most [M : F] members, which Artin's theorem counts as
// |H|, and a finite set holding H with no more members than H is H.
var ArtinAutomorphisms = artinAutomorphismsThm{family.Add(registry.ProofEntry{
	Name: "ArtinAutomorphisms",
	Key:  "prop_40bd8a78d0af8b5f",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀M:set(A). ∀H:set(permutation(A)).",
		Hypotheses: []string{
			"subfield(L, M)",
			"finite(H)",
			"subgroup(permutation_group, H)",
			"H ⊆ field_automorphisms(L, ∅, M)",
		},
		Conclusion: "field_automorphisms(L, fixed_field(M, H), M) = H",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			M *Expr[Set[A]],
			H *Expr[Set[Permutation[A]]],
			finiteGroup Fact,
		) {
			F := a.TermAs[Set[A]]("fixed_field(M, H)")
			autF := a.TermAs[Set[Permutation[A]]]("field_automorphisms(L, fixed_field(M, H), M)")
			subfieldF := a.Have(
				"the fixed field F of H is a subfield",
				"subfield(L, fixed_field(M, H))",
				By(finiteGroup, FixedFieldSubfield.Read(L).At(M, H)))
			inM := a.Have(
				"F lies in M",
				"fixed_field(M, H) ⊆ M",
				BySets(FixedFieldDef.At(M, H)))
			artin := a.Have(
				"Artin: M is finite over F, of degree |H|",
				"finite_extension(L, fixed_field(M, H), M) ∧ extension_degree(L, fixed_field(M, H), M) = card(H)",
				By(finiteGroup, ArtinFixedField.Read(L).At(M, H)))
			fixesF := a.Have(
				"H fixes F, so H ⊆ Aut_F(M)",
				"H ⊆ field_automorphisms(L, fixed_field(M, H), M)",
				By(finiteGroup, FixedFieldAutomorphisms.Read(L).At(M, H)))
			bound := a.Have(
				"Aut_F(M) is finite, with at most [M : F] = |H| members",
				"finite(field_automorphisms(L, fixed_field(M, H), M)) ∧ "+
					"card(field_automorphisms(L, fixed_field(M, H), M)) ≤ card(H)",
				By(Normalized, finiteGroup, subfieldF, inM, artin, AutomorphismsBound.Read(L).At(F, M)))
			a.Show(
				"H inside the finite Aut_F(M), with no fewer members, is all of it",
				By(Normalized, fixesF, bound, cardinality.CardSubsetLe.At(H, autF)))
		}),
})}
