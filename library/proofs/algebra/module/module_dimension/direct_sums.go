// direct_sums.go — dimensions across a direct sum: two finite-dimensional
// submodules meeting only in zero have the sum of their dimensions; a
// finite independent T inside U complementing W counts the dimension of
// U/W, every finite-dimensional U/W has such a complement, and so the
// quotient dimensions of two pairs (U₁, W₁) and (U₂, W₂) with U₁ and U₂
// meeting only in zero add.

package module_dimension

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/quotient_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/linear_independence"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// DirectSumDim — over a field, two finite-dimensional subspaces meeting
// only in zero have a finite-dimensional sum, of the sum of their
// dimensions: finite bases P of U and Q of W are disjoint, as zero lies in
// neither, their union is independent, as their spans U and W meet only
// in zero, and it spans U + W.
var DirectSumDim = directSumDimThm{family.Add(registry.ProofEntry{
	Name: "DirectSumDim",
	Key:  "prop_b3e76f0a84f622bc",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀inv:(A → A). ∀M:module_ops(A, B). ∀U W:set(B).",
		Hypotheses: []string{
			"ring_subfield(R, inv, R.carrier)",
			"module_on(R, M)",
			"submodule(R, M, U)",
			"submodule(R, M, W)",
			"U ∩ W ⊆ {M.zero}",
			"finite_dimensional(R, restrict_module(M, U))",
			"finite_dimensional(R, restrict_module(M, W))",
		},
		Conclusion: "finite_dimensional(R, restrict_module(M, set_mul(M.add, U, W))) ∧ " +
			"module_dim(R, restrict_module(M, set_mul(M.add, U, W))) = " +
			"module_dim(R, restrict_module(M, U)) + module_dim(R, restrict_module(M, W))",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			inv *Arrow[A, A],
			M *Expr[ModuleOps[A, B]],
			U, W *Expr[Set[B]],
			h Fact,
		) {
			given := a.Conjuncts(
				h,
				"the scalars form a field",
				"M is a module",
				"U is a submodule",
				"W is a submodule",
				"U and W meet only in zero",
				"U is finite-dimensional",
				"W is finite-dimensional")
			scalarsField, moduleM, subU, subW, meet, finU, finW :=
				given[0], given[1], given[2], given[3], given[4], given[5], given[6]
			fieldR := a.Unfolded(scalarsField, field.RingSubfieldDef)
			sum := a.TermAs[Set[B]]("set_mul(M.add, U, W)")
			subSum := a.Have(
				"U + W is a submodule",
				"submodule(R, M, set_mul(M.add, U, W))",
				By(subU, subW, submodule.SubmoduleSum.Read(moduleM).At(U, W)))
			additive := module.AddGroupOn.Read(moduleM)

			// Finite bases P of U and Q of W, independent in M with spans U and W.
			P, basisP := a.UnpackAs[Set[B]](a.Unfolded(finU, FiniteDimensionalDef), "P")
			aboutP := a.Conjuncts(
				basisP,
				"P is finite",
				"P is a basis of U")
			ofP := a.Conjuncts(
				a.Unfolded(aboutP[1], linear_independence.ModuleBasisDef),
				"P is independent in U",
				"P spans U")
			Q, basisQ := a.UnpackAs[Set[B]](a.Unfolded(finW, FiniteDimensionalDef), "Q")
			aboutQ := a.Conjuncts(
				basisQ,
				"Q is finite",
				"Q is a basis of W")
			ofQ := a.Conjuncts(
				a.Unfolded(aboutQ[1], linear_independence.ModuleBasisDef),
				"Q is independent in W",
				"Q spans W")
			uInM := a.Have(
				"U lies in M",
				"U ⊆ M.carrier",
				By(submodule.SubmoduleSubset.Read(subU)))
			wInM := a.Have(
				"W lies in M",
				"W ⊆ M.carrier",
				By(submodule.SubmoduleSubset.Read(subW)))
			freeP := a.Have(
				"P lies in U and is independent in M",
				"P ⊆ U ∧ module_independent(R, M, P)",
				By(uInM, ofP[0], linear_independence.IndependentRestrict.At(R, M, U, P)))
			freeQ := a.Have(
				"Q lies in W and is independent in M",
				"Q ⊆ W ∧ module_independent(R, M, Q)",
				By(wInM, ofQ[0], linear_independence.IndependentRestrict.At(R, M, W, Q)))
			spanP := a.Have(
				"P spans U in M",
				"module_span(R, M, P) = U",
				By(Normalized, ofP[1], subU, freeP, linear_independence.SpanRestrict.Read(moduleM).At(U, P)))
			spanQ := a.Have(
				"Q spans W in M",
				"module_span(R, M, Q) = W",
				By(Normalized, ofQ[1], subW, freeQ, linear_independence.SpanRestrict.Read(moduleM).At(W, Q)))

			// Their union is independent, disjoint and finite.
			spansMeet := a.Have(
				"the spans of P and Q meet only in zero",
				"module_span(R, M, P) ∩ module_span(R, M, Q) ⊆ {M.zero}",
				spanP.Rw(),
				spanQ.Rw(),
				By(meet))
			PQ := a.TermAs[Set[B]]("P ∪ Q")
			independent := a.Have(
				"so P ∪ Q is independent in M",
				"module_independent(R, M, P ∪ Q)",
				By(freeP, freeQ, spansMeet, linear_independence.IndependentUnion.Read(moduleM).At(P, Q)))
			zeroOut := a.Have(
				"zero lies in neither basis",
				"M.zero ∉ P ∧ M.zero ∉ Q",
				By(
					freeP,
					freeQ,
					field.OneNotZeroOn.Read(fieldR),
					linear_independence.IndependentZeroNotIn.Read(moduleM)))
			disjoint := a.Have(
				"so P and Q are disjoint, a common member lying in U ∩ W",
				"P ∩ Q = ∅",
				BySets(freeP, freeQ, meet, zeroOut))
			finiteUnion := a.Have(
				"P ∪ Q is finite",
				"finite(P ∪ Q)",
				By(aboutP[0], aboutQ[0], finite_set.FiniteUnion.At(P, Q)))
			counted := a.Have(
				"with card(P) + card(Q) members",
				"card(P ∪ Q) = card(P) + card(Q)",
				By(aboutP[0], aboutQ[0], disjoint, cardinality.CardUnion.At(P, Q)))

			// P ∪ Q spans U + W.
			uInSum := a.Have(
				"U lies in U + W, each u being u + 0",
				"U ⊆ set_mul(M.add, U, W)",
				Unfold(set_basic.SubsetDef),
				Derive(func(b *Argument) {
					u := b.FixAs[B]("u")
					inU := b.Assume()
					inM := b.Have(
						"u lies in M",
						"u ∈ M.carrier",
						BySets(inU, uInM))
					split := b.Have(
						"u is u + 0, with u in U and 0 in W",
						"∃x y:B. x ∈ U ∧ y ∈ W ∧ u = x + y",
						Derive(func(c *Argument) {
							c.Take(u)
							c.Take(c.Term("M.zero"))
							c.Show(
								"u and 0",
								By(
									inU,
									submodule.SubmoduleZero.Read(subW),
									group.RightIdentityOn.Read(additive).At(proof.MemberOf(u, inM))))
						}))
					b.Show(
						"so u lies in U + W",
						By(split, quotient_group.InSetMul.At(b.TermAs[Op[B]]("M.add"), U, W, u)))
				}))
			wInSum := a.Have(
				"W lies in U + W, each w being 0 + w",
				"W ⊆ set_mul(M.add, U, W)",
				Unfold(set_basic.SubsetDef),
				Derive(func(b *Argument) {
					w := b.FixAs[B]("w")
					inW := b.Assume()
					inM := b.Have(
						"w lies in M",
						"w ∈ M.carrier",
						BySets(inW, wInM))
					split := b.Have(
						"w is 0 + w, with 0 in U and w in W",
						"∃x y:B. x ∈ U ∧ y ∈ W ∧ w = x + y",
						Derive(func(c *Argument) {
							c.Take(c.Term("M.zero"))
							c.Take(w)
							c.Show(
								"0 and w",
								By(
									inW,
									submodule.SubmoduleZero.Read(subU),
									group.LeftIdentityOn.Read(additive).At(proof.MemberOf(w, inM))))
						}))
					b.Show(
						"so w lies in U + W",
						By(split, quotient_group.InSetMul.At(b.TermAs[Op[B]]("M.add"), U, W, w)))
				}))
			unionInSum := a.Have(
				"P ∪ Q lies in U + W",
				"P ∪ Q ⊆ set_mul(M.add, U, W)",
				By(
					freeP,
					freeQ,
					uInSum,
					wInSum,
					set_order.SubsetTrans.At(P, U, sum),
					set_order.SubsetTrans.At(Q, W, sum),
					set_order.UnionSubset.At(P, Q, sum)))
			sumInM := a.Have(
				"U + W lies in M",
				"set_mul(M.add, U, W) ⊆ M.carrier",
				By(submodule.SubmoduleSubset.Read(subSum)))
			unionInM := a.Have(
				"so P ∪ Q lies in M",
				"P ∪ Q ⊆ M.carrier",
				BySets(unionInSum, sumInM))
			spanSub := a.Have(
				"the span of P ∪ Q is a submodule",
				"submodule(R, M, module_span(R, M, P ∪ Q))",
				By(unionInM, submodule.SpanSubmodule.Read(moduleM).At(PQ)))
			uInSpan := a.Have(
				"U, the span of P, lies in the span of P ∪ Q",
				"U ⊆ module_span(R, M, P ∪ Q)",
				spanP.RwRev(),
				By(set_order.SubsetUnion.At(P, Q), submodule.SpanMono.At(R, M, P, PQ)))
			wInSpan := a.Have(
				"W, the span of Q, lies in the span of P ∪ Q",
				"W ⊆ module_span(R, M, P ∪ Q)",
				spanQ.RwRev(),
				By(set_order.SubsetUnion.At(Q, P), submodule.SpanMono.At(R, M, Q, PQ)))
			sumInSpan := a.Have(
				"so does U + W, the span being closed under addition",
				"set_mul(M.add, U, W) ⊆ module_span(R, M, P ∪ Q)",
				Unfold(set_basic.SubsetDef),
				Derive(func(b *Argument) {
					x := b.FixAs[B]("x")
					inSum := b.Assume()
					_, _, parts := b.Obtain2As[B, B](
						"x is u + w with u in U and w in W",
						"∃u w:B. u ∈ U ∧ w ∈ W ∧ x = u + w",
						By(inSum, quotient_group.InSetMul.At(b.TermAs[Op[B]]("M.add"), U, W, x)))
					split := b.Conjuncts(
						parts,
						"u lies in U",
						"w lies in W",
						"x is their sum")
					inSpan := b.Have(
						"both lie in the span of P ∪ Q",
						"u ∈ module_span(R, M, P ∪ Q) ∧ w ∈ module_span(R, M, P ∪ Q)",
						BySets(split[0], split[1], uInSpan, wInSpan))
					b.Show(
						"so does their sum",
						split[2].Rw(),
						By(inSpan, submodule.SubmoduleAdd.Read(spanSub)))
				}))
			spanLeast := a.Have(
				"the span of P ∪ Q lies in U + W",
				"module_span(R, M, P ∪ Q) ⊆ set_mul(M.add, U, W)",
				By(subSum, unionInSum, submodule.SpanLeast.At(R, M, PQ, sum)))
			spans := a.Have(
				"so P ∪ Q spans U + W in M",
				"module_span(R, M, P ∪ Q) = set_mul(M.add, U, W)",
				By(
					spanLeast,
					sumInSpan,
					set_order.SubsetAntisym.At(a.TermAs[Set[B]]("module_span(R, M, P ∪ Q)"), sum)))
			sumModule := a.Have(
				"U + W is a module of its own",
				"module_on(R, restrict_module(M, set_mul(M.add, U, W)))",
				By(subSum, submodule.SubmoduleModuleOn.Read(moduleM).At(sum)))
			sumRecord := a.TermAs[ModuleOps[A, B]]("restrict_module(M, set_mul(M.add, U, W))")
			freeInSum := a.Have(
				"P ∪ Q is independent in U + W",
				"module_independent(R, restrict_module(M, set_mul(M.add, U, W)), P ∪ Q)",
				By(sumInM, unionInSum, independent, linear_independence.IndependentRestrict.At(R, M, sum, PQ)))
			spansSum := a.Have(
				"and spans it",
				"module_span(R, restrict_module(M, set_mul(M.add, U, W)), P ∪ Q) = set_mul(M.add, U, W)",
				CalcEq(
					Leg(
						a.Term("module_span(R, M, P ∪ Q)"),
						"a span inside the submodule U + W is the span in M",
						By(subSum, unionInSum, linear_independence.SpanRestrict.Read(moduleM).At(sum, PQ))),
					FinalLeg(
						"which is U + W",
						By(spans)),
				))
			basis := a.Have(
				"so P ∪ Q is a basis of U + W",
				"module_basis(R, restrict_module(M, set_mul(M.add, U, W)), P ∪ Q)",
				By(freeInSum, spansSum, linear_independence.ModuleBasisDef.At(R, sumRecord, PQ)))
			whole := a.Have(
				"U + W is finite-dimensional, of dimension card(P ∪ Q)",
				"finite_dimensional(R, restrict_module(M, set_mul(M.add, U, W))) ∧ "+
					"module_dim(R, restrict_module(M, set_mul(M.add, U, W))) = card(P ∪ Q)",
				By(scalarsField, basis, finiteUnion, FiniteBasisDim.Read(sumModule).At(inv, PQ)))
			uModule := a.Have(
				"U is a module of its own",
				"module_on(R, restrict_module(M, U))",
				By(subU, submodule.SubmoduleModuleOn.Read(moduleM).At(U)))
			wModule := a.Have(
				"W is a module of its own",
				"module_on(R, restrict_module(M, W))",
				By(subW, submodule.SubmoduleModuleOn.Read(moduleM).At(W)))
			dimU := a.Have(
				"U has dimension card(P)",
				"module_dim(R, restrict_module(M, U)) = card(P)",
				By(scalarsField, aboutP[1], aboutP[0], DimBasis.Read(uModule).At(inv, P)))
			dimW := a.Have(
				"W has dimension card(Q)",
				"module_dim(R, restrict_module(M, W)) = card(Q)",
				By(scalarsField, aboutQ[1], aboutQ[0], DimBasis.Read(wModule).At(inv, Q)))
			a.Show(
				"so U + W is finite-dimensional, of dimension card(P) + card(Q)",
				By(whole, counted, dimU, dimW))
		}),
})}

// quotientFacts is U/W opened for submodules W ⊆ U of M: U/W is a module,
// the projection u ↦ u + W of U onto it is linear with kernel W, U lies
// in M, and the classes modulo W are the classes of the members of U.
type quotientFacts struct{ module, projection, kernel, uInM, classes Fact }

// quotientOf opens U/W, the opening a complement of W inside U is read
// through.
func quotientOf(
	a *Argument,
	moduleOn module.ModuleFact[on.R, on.M],
	U, W *Expr[Set[B]],
	subU, subW, wInU Fact,
) quotientFacts {
	R, M := a.TermAs[RingOps[A]]("R"), a.TermAs[ModuleOps[A, B]]("M")
	sub := a.TermAs[ModuleOps[A, B]]("restrict_module(M, U)")
	moduleU := a.Have(
		"U is a module under M's operations",
		"module_on(R, restrict_module(M, U))",
		By(subU, submodule.SubmoduleModuleOn.Read(moduleOn).At(U)))
	wInSub := a.Have(
		"W is a submodule of U",
		"submodule(R, restrict_module(M, U), W)",
		By(subW, wInU, submodule.SubmoduleRestrict.At(R, M, U, W)))
	var q quotientFacts
	q.module = a.Have(
		"U/W is a module",
		"module_on(R, quotient_module(restrict_module(M, U), W))",
		By(wInSub, submodule.QuotientModuleOn.Read(moduleU).At(W)))
	q.projection = a.Unfolded(a.Have(
		"the projection onto the classes modulo W is linear",
		"module_homomorphism(R, "+
			"    restrict_module(M, U), "+
			"    quotient_module(restrict_module(M, U), W), "+
			"    coset_map(M.add, W))",
		By(moduleU, wInSub, module_homomorphism.ProjectionHom.At(R, sub, W))), group.CosetMapDef)
	q.kernel = a.Unfolded(a.Have(
		"its kernel is W",
		"group_kernel(W, U, coset_map(M.add, W)) = W",
		By(moduleU, wInSub, module_homomorphism.ProjectionKernel.At(R, sub, W))), group.CosetMapDef)
	q.uInM = a.Have(
		"U lies in M",
		"U ⊆ M.carrier",
		By(submodule.SubmoduleSubset.Read(subU)))
	q.classes = a.Unfolded(a.Have(
		"the classes modulo W are the classes of the members of U",
		"left_cosets(M.add, U, W) = image(coset_map(M.add, W), U)",
		By(
			wInU,
			quotient_group.LeftCosetsImage.Read(module.AddGroupOn.Read(moduleU)).At(W))), group.CosetMapDef)
	return q
}

// QuotientComplementBasis — an independent T inside U whose span meets W
// only in zero and together with W spans U gives a basis of U/W: the
// classes of T, one for each member of T. The projection u ↦ u + W is
// linear with kernel W, so it is one to one on T and carries T to an
// independent set (linear_independence.IndependentImageKernel); and every
// class is the class of a member of the span of T, adding a member of W
// not moving a class, so the classes of T span U/W
// (linear_independence.HomSpan).
var QuotientComplementBasis = quotientComplementBasisThm{family.Add(registry.ProofEntry{
	Name: "QuotientComplementBasis",
	Key:  "prop_ea1f6ce8d1cb01e",
	Build: module.ModuleOn.Law(Statement{
		Binders: "∀U W T:set(B).",
		Hypotheses: []string{
			"submodule(R, M, U)",
			"submodule(R, M, W)",
			"W ⊆ U",
			"T ⊆ U",
			"module_independent(R, M, T)",
			"U ⊆ set_mul(M.add, module_span(R, M, T), W)",
			"module_span(R, M, T) ∩ W ⊆ {M.zero}",
		},
		Conclusion: "module_basis(R, «quotientUW», image(coset_map(M.add, W), T)) ∧ " +
			"injective_on(T, coset_map(M.add, W))",
	},
		func(a *Argument, moduleOn module.ModuleFact[on.R, on.M], U, W, T *Expr[Set[B]], hypotheses Fact) {
			given := a.Conjuncts(
				hypotheses,
				"U is a submodule",
				"W is a submodule",
				"W lies in U",
				"T lies in U",
				"T is independent",
				"U is the span of T plus W",
				"the span of T meets W only in zero")
			subU, subW, wInU, tInU, independentT, spanned, meets :=
				given[0], given[1], given[2], given[3], given[4], given[5], given[6]
			R, M := a.TermAs[RingOps[A]]("R"), a.TermAs[ModuleOps[A, B]]("M")
			sub := a.TermAs[ModuleOps[A, B]]("restrict_module(M, U)")
			quotient := a.TermAs[ModuleOps[A, Set[B]]]("«quotientUW»")
			projection := a.TermAs[Fun[B, Set[B]]]("λu:B. left_coset(M.add, u, W)")
			span := a.TermAs[Set[B]]("module_span(R, M, T)")
			classesOfT := a.TermAs[Set[Set[B]]]("image(λu:B. left_coset(M.add, u, W), T)")
			additive := module.AddGroupOn.Read(moduleOn)
			q := quotientOf(a, moduleOn, U, W, subU, subW, wInU)

			spanInU := a.Have(
				"the span of T lies in U",
				"module_span(R, M, T) ⊆ U",
				By(subU, tInU, submodule.SpanLeast.At(R, M, T, U)))
			sameSpan := a.Have(
				"the span of T in U is its span in M",
				"module_span(R, restrict_module(M, U), T) = module_span(R, M, T)",
				By(subU, tInU, linear_independence.SpanRestrict.Read(moduleOn).At(U, T)))
			independentInU := a.Have(
				"T is independent in U",
				"module_independent(R, restrict_module(M, U), T)",
				By(q.uInM, tInU, independentT, linear_independence.IndependentRestrict.At(R, M, U, T)))
			kernelMeets := a.Have(
				"the kernel meets the span of T in U only in zero",
				"group_kernel(W, U, λu:B. left_coset(M.add, u, W)) ∩ module_span(R, restrict_module(M, U), T) ⊆ "+
					"{M.zero}",
				q.kernel.Rw(),
				sameSpan.Rw(),
				BySets(meets))
			images := a.Conjuncts(
				a.Have(
					"so the projection is one to one on T, and the classes of T are independent",
					"injective_on(T, λu:B. left_coset(M.add, u, W)) ∧ "+
						"module_independent(R, «quotientUW», image(λu:B. left_coset(M.add, u, W), T))",
					By(
						q.projection,
						independentInU,
						kernelMeets,
						linear_independence.IndependentImageKernel.At(R, sub, quotient, projection, T))),
				"the projection is one to one on T",
				"the classes of T are independent")
			oneToOne, independentClasses := images[0], images[1]

			absorb := a.Have(
				"adding a member of W does not move a class",
				"∀s w:B. s ∈ M.carrier ∧ w ∈ W ⇒ left_coset(M.add, s, W) = left_coset(M.add, s + w, W)",
				Derive(func(b *Argument) {
					s := b.FixAs[B]("s")
					w := b.FixAs[B]("w")
					parts := b.Conjuncts(
						b.Assume(),
						"s lies in M",
						"w lies in W")
					wm := b.MemberOf[on.M](w, b.Have(
						"w lies in M",
						"w ∈ M.carrier",
						BySets(parts[1], submodule.SubmoduleSubset.Read(subW))))
					sm := b.MemberOf[on.M](s, parts[0])
					sw := group.MulIn.Read(additive).At(sm, wm)
					b.Show(
						"the difference -s + (s + w) is w, a member of W",
						By(
							parts[1],
							submodule.SubmoduleSubgroup.Read(subW),
							group.InvMulCancelLeftOn.Read(additive).At(sm, wm),
							group.LeftCosetEqOn.Read(additive).At(sm, sw, W)))
				}))
			reach := a.Have(
				"the class of a member of U is the class of a member of the span of T",
				"image(λu:B. left_coset(M.add, u, W), U) ⊆ "+
					"image(λu:B. left_coset(M.add, u, W), module_span(R, M, T))",
				Simp(Fwd(set_basic.SubsetDef)),
				Derive(func(b *Argument) {
					X := b.FixAs[Set[B]]("X")
					x, xIs := b.UnpackAs[B](b.Have(
						"X is the class of a member x of U",
						"∃x:B. X = left_coset(M.add, x, W) ∧ x ∈ U",
						By(b.Assume(), set_basic.InImage.At(projection, U, X))), "x")
					xParts := b.Conjuncts(
						xIs,
						"X is the class of x",
						"x lies in U")
					xInSum := b.Have(
						"x lies in the span of T plus W",
						"x ∈ set_mul(M.add, module_span(R, M, T), W)",
						BySets(xParts[1], spanned))
					s, w, split := b.Unpack2As[B, B](b.Have(
						"x is a member of the span of T plus a member of W",
						"∃s w:B. s ∈ module_span(R, M, T) ∧ w ∈ W ∧ x = s + w",
						By(xInSum, quotient_group.InSetMul.At(b.TermAs[Op[B]]("M.add"), span, W, x))), "s", "w")
					sParts := b.Conjuncts(
						split,
						"s lies in the span of T",
						"w lies in W",
						"x is their sum")
					sInM := b.Have(
						"s lies in M",
						"s ∈ M.carrier",
						BySets(sParts[0], spanInU, q.uInM))
					b.Show(
						"so X is the class of s",
						By(
							xParts[0],
							sParts[0],
							sParts[2],
							sInM,
							sParts[1],
							absorb.At(s, w),
							set_basic.InImage.At(projection, span, X)))
				}))
			classes := a.Have(
				"so every class modulo W is the class of a member of the span of T",
				"image(λu:B. left_coset(M.add, u, W), module_span(R, M, T)) = left_cosets(M.add, U, W)",
				q.classes.Rw(),
				By(
					reach,
					spanInU,
					set_image.ImageSubset.At(projection, span, U),
					set_order.SubsetAntisym.At(
						a.TermAs[Set[Set[B]]]("image(λu:B. left_coset(M.add, u, W), module_span(R, M, T))"),
						a.TermAs[Set[Set[B]]]("image(λu:B. left_coset(M.add, u, W), U)"))))
			spans := a.Have(
				"the classes of T span U/W",
				"module_span(R, «quotientUW», image(λu:B. left_coset(M.add, u, W), T)) = left_cosets(M.add, U, W)",
				By(
					q.projection,
					tInU,
					sameSpan,
					classes,
					linear_independence.HomSpan.At(R, sub, quotient, projection, T)))
			a.Show(
				"so the classes of T are a basis of U/W, one for each member of T",
				Simp(Fwd(group.CosetMapDef)),
				By(
					independentClasses,
					spans,
					oneToOne,
					linear_independence.ModuleBasisDef.At(R, quotient, classesOfT)))
		}),
})}

// QuotientComplementDim — a finite independent T inside U whose span
// meets W only in zero and together with W spans U counts the dimension
// of U/W: the classes of T are a basis of U/W, one for each member of T
// (QuotientComplementBasis), and over a field a finite basis counts the
// dimension.
var QuotientComplementDim = quotientComplementDimThm{family.Add(registry.ProofEntry{
	Name: "QuotientComplementDim",
	Key:  "prop_5b0a6dde6f4095b8",
	Build: module.ModuleOn.Law(Statement{
		Binders: "∀inv:(A → A). ∀U W T:set(B).",
		Hypotheses: []string{
			"ring_subfield(R, inv, R.carrier)",
			"submodule(R, M, U)",
			"submodule(R, M, W)",
			"W ⊆ U",
			"finite(T)",
			"T ⊆ U",
			"module_independent(R, M, T)",
			"U ⊆ set_mul(M.add, module_span(R, M, T), W)",
			"module_span(R, M, T) ∩ W ⊆ {M.zero}",
		},
		Conclusion: "finite_dimensional(R, «quotientUW») ∧ module_dim(R, «quotientUW») = card(T)",
	},
		func(
			a *Argument,
			moduleOn module.ModuleFact[on.R, on.M],
			inv *Arrow[A, A],
			U, W, T *Expr[Set[B]],
			hypotheses Fact,
		) {
			given := a.Conjuncts(
				hypotheses,
				"the scalars form a field",
				"U is a submodule",
				"W is a submodule",
				"W lies in U",
				"T is finite",
				"T lies in U",
				"T is independent",
				"U is the span of T plus W",
				"the span of T meets W only in zero")
			scalarsField, subU, subW, wInU, finiteT, tInU, independentT, spanned, meets :=
				given[0], given[1], given[2], given[3], given[4], given[5], given[6], given[7], given[8]
			R := a.TermAs[RingOps[A]]("R")
			quotient := a.TermAs[ModuleOps[A, Set[B]]]("«quotientUW»")
			projection := a.TermAs[Fun[B, Set[B]]]("λu:B. left_coset(M.add, u, W)")
			classesOfT := a.TermAs[Set[Set[B]]]("image(λu:B. left_coset(M.add, u, W), T)")
			q := quotientOf(a, moduleOn, U, W, subU, subW, wInU)
			basis := a.Conjuncts(
				a.Unfolded(a.Have(
					"the classes of T are a basis of U/W, one for each member of T",
					"module_basis(R, «quotientUW», image(coset_map(M.add, W), T)) ∧ "+
						"injective_on(T, coset_map(M.add, W))",
					By(
						subU,
						subW,
						wInU,
						tInU,
						independentT,
						spanned,
						meets,
						QuotientComplementBasis.Read(moduleOn).At(U, W, T))), group.CosetMapDef),
				"the classes of T are a basis of U/W",
				"the projection is one to one on T")
			counted := a.Have(
				"a finite basis counts the dimension",
				"finite_dimensional(R, «quotientUW») ∧ "+
					"module_dim(R, «quotientUW») = card(image(λu:B. left_coset(M.add, u, W), T))",
				By(
					basis[0],
					scalarsField,
					finite_set.FiniteImage.At(projection, T),
					finiteT,
					FiniteBasisDim.At(R, quotient, inv, classesOfT),
					q.module))
			a.Show(
				"and the projection, one to one on T, has as many classes as T has members",
				By(counted, basis[1], finiteT, cardinality.CardImageInj.At(projection, T)))
		}),
})}

// QuotientComplementLift — a finite-dimensional U/W has such a
// complement, with dim U/W members: a finite basis S of classes, each
// class lifted to a representative in U, chosen by inverse_on. The
// projection undoes the lift on S, so it is one to one on the
// representatives and carries them onto S
// (functions.TwoSidedInverseBijection); then they are independent with
// span meeting W only in zero (linear_independence.IndependentFromImage),
// and every class, a combination of S, is the class of a member of their
// span.
var QuotientComplementLift = quotientComplementLiftThm{family.Add(registry.ProofEntry{
	Name: "QuotientComplementLift",
	Key:  "prop_8bde8d3bab117dda",
	Build: module.ModuleOn.Law(Statement{
		Binders: "∀inv:(A → A). ∀U W:set(B).",
		Hypotheses: []string{
			"ring_subfield(R, inv, R.carrier)",
			"submodule(R, M, U)",
			"submodule(R, M, W)",
			"W ⊆ U",
			"finite_dimensional(R, «quotientUW»)",
		},
		Conclusion: "∃T:set(B). " +
			"    finite(T) ∧ " +
			"    T ⊆ U ∧ " +
			"    module_independent(R, M, T) ∧ " +
			"    U ⊆ set_mul(M.add, module_span(R, M, T), W) ∧ " +
			"    module_span(R, M, T) ∩ W ⊆ {M.zero} ∧ " +
			"    card(T) = module_dim(R, «quotientUW»)",
	},
		func(
			a *Argument,
			moduleOn module.ModuleFact[on.R, on.M],
			inv *Arrow[A, A],
			U, W *Expr[Set[B]],
			hypotheses Fact,
		) {
			given := a.Conjuncts(
				hypotheses,
				"the scalars form a field",
				"U is a submodule",
				"W is a submodule",
				"W lies in U",
				"U/W is finite-dimensional")
			scalarsField, subU, subW, wInU, finiteQuotient := given[0], given[1], given[2], given[3], given[4]
			R, M := a.TermAs[RingOps[A]]("R"), a.TermAs[ModuleOps[A, B]]("M")
			sub := a.TermAs[ModuleOps[A, B]]("restrict_module(M, U)")
			quotient := a.TermAs[ModuleOps[A, Set[B]]]("«quotientUW»")
			projection := a.TermAs[Fun[B, Set[B]]]("λu:B. left_coset(M.add, u, W)")
			lift := a.TermAs[Fun[Set[B], B]]("inverse_on(U, λu:B. left_coset(M.add, u, W))")
			additive := module.AddGroupOn.Read(moduleOn)

			q := quotientOf(a, moduleOn, U, W, subU, subW, wInU)

			S, basisFact := a.ObtainAs[Set[Set[B]]](
				"U/W has a finite basis S",
				"∃S:set(set(B)). finite(S) ∧ module_basis(R, «quotientUW», S)",
				By(finiteQuotient, FiniteDimensionalDef.At(R, quotient)))
			basisParts := a.Conjuncts(
				basisFact,
				"S is finite",
				"S is a basis")
			finiteS, basisS := basisParts[0], basisParts[1]
			dimension := a.Have(
				"the dimension of U/W is the size of S",
				"module_dim(R, «quotientUW») = card(S)",
				By(finiteS, basisS, scalarsField, DimBasis.Read(q.module).At(inv, S)))
			basisSays := a.Conjuncts(
				a.Have(
					"S is independent and spans U/W",
					"module_independent(R, «quotientUW», S) ∧ "+
						"module_span(R, «quotientUW», S) = left_cosets(M.add, U, W)",
					By(basisS, linear_independence.ModuleBasisDef.At(R, quotient, S))),
				"S is independent",
				"S spans U/W")
			independentS, spansS := basisSays[0], basisSays[1]
			sAmongClasses := a.Have(
				"S consists of classes of members of U",
				"S ⊆ image(λu:B. left_coset(M.add, u, W), U)",
				By(independentS, q.classes, linear_independence.IndependentInCarrier.At(R, quotient, S)))

			T := a.TermAs[Set[B]]("image(inverse_on(U, λu:B. left_coset(M.add, u, W)), S)")
			lifted := a.Have(
				"each class of S is the class of its chosen representative, a member of U",
				Statement{
					Binders: "∀X:set(B).",
					Hypotheses: []string{
						"X ∈ S",
					},
					Conclusion: "left_coset(M.add, inverse_on(U, λu:B. left_coset(M.add, u, W), X), W) = X ∧ " +
						"inverse_on(U, λu:B. left_coset(M.add, u, W), X) ∈ U",
				},
				Derive(func(b *Argument) {
					X := b.FixAs[Set[B]]("X")
					xIsClass := b.Have(
						"X is the class of a member of U",
						"X ∈ image(λu:B. left_coset(M.add, u, W), U)",
						BySets(b.Assume(), sAmongClasses))
					b.Show(
						"so its chosen preimage in U has class X",
						By(
							xIsClass,
							functions.InverseOnRight.At(U, projection, X),
							functions.InverseOnIn.At(U, projection, X)))
				}))
			tInU := a.Have(
				"the representatives lie in U",
				"image(inverse_on(U, λu:B. left_coset(M.add, u, W)), S) ⊆ U",
				BySets(lifted))
			bijection := a.Conjuncts(
				a.Have(
					"the projection is one to one on the representatives and carries them onto S",
					"injective_on(image(inverse_on(U, λu:B. left_coset(M.add, u, W)), S), "+
						"    λu:B. left_coset(M.add, u, W)) ∧ "+
						"image(λu:B. left_coset(M.add, u, W), image(inverse_on(U, λu:B. left_coset(M.add, u, W)), S)) = S",
					By(
						a.Have(
							"on S the projection undoes the lift",
							"∀X:set(B). X ∈ S ⇒ left_coset(M.add, inverse_on(U, λu:B. left_coset(M.add, u, W), X), W) = X",
							By(lifted)),
						a.Have(
							"the lift carries S into the representatives",
							Statement{
								Binders: "∀X:set(B).",
								Hypotheses: []string{
									"X ∈ S",
								},
								Conclusion: "inverse_on(U, λu:B. left_coset(M.add, u, W), X) ∈ " +
									"image(inverse_on(U, λu:B. left_coset(M.add, u, W)), S)",
							},
							By(set_image.FunInImage)),
						a.Have(
							"on the representatives the lift undoes the projection, which lands in S",
							Statement{
								Binders: "∀y:B.",
								Hypotheses: []string{
									"y ∈ image(inverse_on(U, λu:B. left_coset(M.add, u, W)), S)",
								},
								Conclusion: "inverse_on(U, λu:B. left_coset(M.add, u, W), left_coset(M.add, y, W)) = y ∧ " +
									"left_coset(M.add, y, W) ∈ S",
							},
							Derive(func(b *Argument) {
								y := b.FixAs[B]("y")
								X, yIs := b.UnpackAs[Set[B]](b.Have(
									"y is the representative of some X in S",
									"∃X:set(B). y = inverse_on(U, λu:B. left_coset(M.add, u, W), X) ∧ X ∈ S",
									By(b.Assume(), set_basic.InImage.At(lift, S, y))), "X")
								yParts := b.Conjuncts(
									yIs,
									"y is the representative of X",
									"X lies in S")
								liftedX := b.Conjuncts(
									b.Have(
										"the representative of X has class X and lies in U",
										"left_coset(M.add, inverse_on(U, λu:B. left_coset(M.add, u, W), X), W) = X ∧ "+
											"inverse_on(U, λu:B. left_coset(M.add, u, W), X) ∈ U",
										By(yParts[1], lifted.At(X))),
									"the representative of X has class X",
									"it lies in U")
								b.Show(
									"so the class of y is X, whose representative is y",
									yParts[0].Rw(),
									liftedX[0].Rw(),
									By(yParts[1]))
							})),
						functions.TwoSidedInverseBijection.At(T, S, projection, lift))),
				"the projection is one to one on the representatives",
				"it carries them onto S")
			oneToOne, ontoS := bijection[0], bijection[1]
			liftOneToOne := a.Have(
				"the lift is one to one on S",
				"injective_on(S, inverse_on(U, λu:B. left_coset(M.add, u, W)))",
				By(
					sAmongClasses,
					functions.InverseOnInjective.At(U, projection),
					functions.InjectiveOnSubset.At(
						lift, S, a.TermAs[Set[Set[B]]]("image(λu:B. left_coset(M.add, u, W), U)"))))
			finiteT := a.Have(
				"there are finitely many representatives",
				"finite(image(inverse_on(U, λu:B. left_coset(M.add, u, W)), S))",
				By(finiteS, finite_set.FiniteImage.At(lift, S)))
			countT := a.Have(
				"as many as S has members",
				"card(image(inverse_on(U, λu:B. left_coset(M.add, u, W)), S)) = card(S)",
				By(finiteS, liftOneToOne, cardinality.CardImageInj.At(lift, S)))

			imageIndependent := a.Have(
				"their classes, the members of S, are independent",
				"module_independent(R, "+
					"    «quotientUW», "+
					"    image(λu:B. left_coset(M.add, u, W), image(inverse_on(U, λu:B. left_coset(M.add, u, W)), S)))",
				ontoS.Rw(),
				By(independentS))
			fromImage := a.Conjuncts(
				a.Have(
					"so the representatives are independent in U, and their span there meets W only in zero",
					"module_independent(R, "+
						"    restrict_module(M, U), "+
						"    image(inverse_on(U, λu:B. left_coset(M.add, u, W)), S)) ∧ "+
						"group_kernel(W, U, λu:B. left_coset(M.add, u, W)) ∩ "+
						"module_span(R, restrict_module(M, U), image(inverse_on(U, λu:B. left_coset(M.add, u, W)), S)) ⊆ "+
						"{M.zero}",
					By(
						q.projection,
						tInU,
						oneToOne,
						imageIndependent,
						linear_independence.IndependentFromImage.At(R, sub, quotient, projection, T))),
				"the representatives are independent in U",
				"their span in U meets the kernel only in zero")
			independentT := a.Have(
				"the representatives are independent in M",
				"module_independent(R, M, image(inverse_on(U, λu:B. left_coset(M.add, u, W)), S))",
				By(fromImage[0], q.uInM, linear_independence.IndependentRestrict.At(R, M, U, T)))
			sameSpan := a.Have(
				"their span in U is their span in M",
				"module_span(R, restrict_module(M, U), image(inverse_on(U, λu:B. left_coset(M.add, u, W)), S)) = "+
					"module_span(R, M, image(inverse_on(U, λu:B. left_coset(M.add, u, W)), S))",
				By(subU, tInU, linear_independence.SpanRestrict.Read(moduleOn).At(U, T)))
			meets := a.Have(
				"so their span meets W only in zero",
				"module_span(R, M, image(inverse_on(U, λu:B. left_coset(M.add, u, W)), S)) ∩ W ⊆ {M.zero}",
				sameSpan.RwRev(),
				BySets(
					fromImage[1],
					a.Have(
						"a member of W lies in the kernel",
						"∀z:B. z ∈ W ⇒ z ∈ group_kernel(W, U, λu:B. left_coset(M.add, u, W))",
						By(Normalized, q.kernel))))

			spanInU := a.Have(
				"the span of the representatives lies in U",
				"module_span(R, M, image(inverse_on(U, λu:B. left_coset(M.add, u, W)), S)) ⊆ U",
				By(subU, tInU, submodule.SpanLeast.At(R, M, T, U)))
			spanClasses := a.Have(
				"the classes of the span of the representatives are all the classes",
				"image(λu:B. left_coset(M.add, u, W), "+
					"    module_span(R, M, image(inverse_on(U, λu:B. left_coset(M.add, u, W)), S))) = "+
					"left_cosets(M.add, U, W)",
				By(
					q.projection,
					tInU,
					sameSpan,
					ontoS,
					spansS,
					linear_independence.HomSpan.At(R, sub, quotient, projection, T)))
			spanned := a.Have(
				"U is the span of the representatives plus W",
				"U ⊆ set_mul(M.add, module_span(R, M, image(inverse_on(U, λu:B. left_coset(M.add, u, W)), S)), W)",
				Unfold(set_basic.SubsetDef),
				Derive(func(b *Argument) {
					x := b.FixAs[B]("x")
					xInU := b.Assume()
					xm := b.MemberOf[on.M](x, b.Have(
						"x lies in M",
						"x ∈ M.carrier",
						BySets(xInU, q.uInM)))
					xClass := b.Have(
						"the class of x is the class of a member of the span",
						"left_coset(M.add, x, W) ∈ "+
							"image(λu:B. left_coset(M.add, u, W), "+
							"    module_span(R, M, image(inverse_on(U, λu:B. left_coset(M.add, u, W)), S)))",
						By(xInU, spanClasses, q.classes, set_image.FunInImage.At(projection, U, x)))
					s, sIs := b.UnpackAs[B](b.Have(
						"a member s of the span with the class of x",
						"∃s:B. "+
							"    s ∈ module_span(R, M, image(inverse_on(U, λu:B. left_coset(M.add, u, W)), S)) ∧ "+
							"    left_coset(M.add, x, W) = left_coset(M.add, s, W)",
						By(
							xClass,
							set_basic.InImage.At(
								projection,
								b.TermAs[Set[B]]("module_span(R, M, image(inverse_on(U, λu:B. left_coset(M.add, u, W)), S))"),
								b.TermAs[Set[B]]("left_coset(M.add, x, W)")))), "s")
					sParts := b.Conjuncts(
						sIs,
						"s lies in the span",
						"s has the class of x")
					sInM := b.Have(
						"s lies in M",
						"s ∈ M.carrier",
						BySets(sParts[0], spanInU, q.uInM))
					sm := b.MemberOf[on.M](s, sInM)
					difference := b.Have(
						"so -s + x lies in W",
						"-s + x ∈ W",
						By(
							sParts[1],
							submodule.SubmoduleSubgroup.Read(subW),
							group.LeftCosetEqOn.Read(additive).At(sm, xm, W)))
					b.Show(
						"and x is s plus -s + x",
						By(
							sParts[0],
							difference,
							group.MulInvCancelLeftOn.Read(additive).At(sm, xm),
							quotient_group.InSetMul.At(
								b.TermAs[Op[B]]("M.add"),
								b.TermAs[Set[B]]("module_span(R, M, image(inverse_on(U, λu:B. left_coset(M.add, u, W)), S))"),
								W,
								x)))
				}))
			a.Take(T)
			a.Show(
				"the representatives are such a complement, with as many members as the dimension",
				By(finiteT, tInU, independentT, spanned, meets, countT, dimension))
		}),
})}

// QuotientDirectSumDim — when U₁ and U₂ meet only in zero, the
// dimension of (U₁ + U₂)/(W₁ + W₂) is the sum of the dimensions of U₁/W₁
// and U₂/W₂: complements T₁ and T₂ of the two (QuotientComplementLift)
// together make a complement T₁ ∪ T₂ of W₁ + W₂ in U₁ + U₂, a member of
// U₁ + U₂ being written uniquely as a member of U₁ plus a member of U₂,
// and QuotientComplementDim counts it.
var QuotientDirectSumDim = quotientDirectSumDimThm{family.Add(registry.ProofEntry{
	Name: "QuotientDirectSumDim",
	Key:  "prop_8972c68f33cb72ac",
	Build: module.ModuleOn.Law(Statement{
		Binders: "∀inv:(A → A). ∀U₁ U₂ W₁ W₂:set(B).",
		Hypotheses: []string{
			"ring_subfield(R, inv, R.carrier)",
			"submodule(R, M, U₁)",
			"submodule(R, M, U₂)",
			"submodule(R, M, W₁)",
			"submodule(R, M, W₂)",
			"W₁ ⊆ U₁",
			"W₂ ⊆ U₂",
			"U₁ ∩ U₂ ⊆ {M.zero}",
			"finite_dimensional(R, quotient_module(restrict_module(M, U₁), W₁))",
			"finite_dimensional(R, quotient_module(restrict_module(M, U₂), W₂))",
		},
		Conclusion: "finite_dimensional(R, «quotientSums») ∧ " +
			"module_dim(R, «quotientSums») = " +
			"module_dim(R, quotient_module(restrict_module(M, U₁), W₁)) + " +
			"module_dim(R, quotient_module(restrict_module(M, U₂), W₂))",
		Abbrev: Abbrev{
			{Name: "quotientSums", Text: "quotient_module(restrict_module(M, set_mul(M.add, U₁, U₂)), " +
				"    set_mul(M.add, W₁, W₂))"},
		},
	},
		func(
			a *Argument,
			moduleOn module.ModuleFact[on.R, on.M],
			inv *Arrow[A, A],
			U1, U2, W1, W2 *Expr[Set[B]],
			hypotheses Fact,
		) {
			given := a.Conjuncts(
				hypotheses,
				"the scalars form a field",
				"U₁ is a submodule",
				"U₂ is a submodule",
				"W₁ is a submodule",
				"W₂ is a submodule",
				"W₁ lies in U₁",
				"W₂ lies in U₂",
				"U₁ and U₂ meet only in zero",
				"U₁/W₁ is finite-dimensional",
				"U₂/W₂ is finite-dimensional")
			scalarsField, subU1, subU2, subW1, subW2, w1InU1, w2InU2, direct, finite1, finite2 :=
				given[0], given[1], given[2], given[3], given[4], given[5], given[6], given[7], given[8], given[9]
			fieldR := a.Unfolded(scalarsField, field.RingSubfieldDef)
			R, M := a.TermAs[RingOps[A]]("R"), a.TermAs[ModuleOps[A, B]]("M")
			add := a.TermAs[Op[B]]("M.add")
			additive := module.AddGroupOn.Read(moduleOn)
			u1InM := a.Have(
				"U₁ lies in M",
				"U₁ ⊆ M.carrier",
				By(submodule.SubmoduleSubset.Read(subU1)))
			u2InM := a.Have(
				"U₂ lies in M",
				"U₂ ⊆ M.carrier",
				By(submodule.SubmoduleSubset.Read(subU2)))

			T1, complement1 := a.ObtainAs[Set[B]](
				"W₁ has a complement T₁ in U₁ with dim U₁/W₁ members",
				"∃T₁:set(B). "+
					"    finite(T₁) ∧ "+
					"    T₁ ⊆ U₁ ∧ "+
					"    module_independent(R, M, T₁) ∧ "+
					"    U₁ ⊆ set_mul(M.add, module_span(R, M, T₁), W₁) ∧ "+
					"    module_span(R, M, T₁) ∩ W₁ ⊆ {M.zero} ∧ "+
					"    card(T₁) = module_dim(R, quotient_module(restrict_module(M, U₁), W₁))",
				By(
					scalarsField,
					subU1,
					subW1,
					w1InU1,
					finite1,
					moduleOn,
					QuotientComplementLift.At(R, M, inv, U1, W1)))
			first := a.Conjuncts(
				complement1,
				"T₁ is finite",
				"T₁ lies in U₁",
				"T₁ is independent",
				"U₁ is the span of T₁ plus W₁",
				"the span of T₁ meets W₁ only in zero",
				"T₁ has dim U₁/W₁ members")
			T2, complement2 := a.ObtainAs[Set[B]](
				"W₂ has a complement T₂ in U₂ with dim U₂/W₂ members",
				"∃T₂:set(B). "+
					"    finite(T₂) ∧ "+
					"    T₂ ⊆ U₂ ∧ "+
					"    module_independent(R, M, T₂) ∧ "+
					"    U₂ ⊆ set_mul(M.add, module_span(R, M, T₂), W₂) ∧ "+
					"    module_span(R, M, T₂) ∩ W₂ ⊆ {M.zero} ∧ "+
					"    card(T₂) = module_dim(R, quotient_module(restrict_module(M, U₂), W₂))",
				By(
					scalarsField,
					subU2,
					subW2,
					w2InU2,
					finite2,
					moduleOn,
					QuotientComplementLift.At(R, M, inv, U2, W2)))
			second := a.Conjuncts(
				complement2,
				"T₂ is finite",
				"T₂ lies in U₂",
				"T₂ is independent",
				"U₂ is the span of T₂ plus W₂",
				"the span of T₂ meets W₂ only in zero",
				"T₂ has dim U₂/W₂ members")
			T := a.TermAs[Set[B]]("T₁ ∪ T₂")
			span := a.TermAs[Set[B]]("module_span(R, M, T₁ ∪ T₂)")

			span1InU1 := a.Have(
				"the span of T₁ lies in U₁",
				"module_span(R, M, T₁) ⊆ U₁",
				By(subU1, first[1], submodule.SpanLeast.At(R, M, T1, U1)))
			span2InU2 := a.Have(
				"the span of T₂ lies in U₂",
				"module_span(R, M, T₂) ⊆ U₂",
				By(subU2, second[1], submodule.SpanLeast.At(R, M, T2, U2)))
			tInM := a.Have(
				"T₁ ∪ T₂ lies in M",
				"T₁ ∪ T₂ ⊆ M.carrier",
				BySets(first[1], second[1], u1InM, u2InM))
			spanSub := a.Have(
				"the span of T₁ ∪ T₂ is a submodule",
				"submodule(R, M, module_span(R, M, T₁ ∪ T₂))",
				By(tInM, submodule.SpanSubmodule.Read(moduleOn).At(T)))
			independentT := a.Have(
				"T₁ ∪ T₂ is independent, the spans of T₁ and T₂ meeting only in zero",
				"module_independent(R, M, T₁ ∪ T₂)",
				By(
					first[2],
					second[2],
					a.Have(
						"the spans of T₁ and T₂ meet only in zero",
						"module_span(R, M, T₁) ∩ module_span(R, M, T₂) ⊆ {M.zero}",
						BySets(span1InU1, span2InU2, direct)),
					linear_independence.IndependentUnion.Read(moduleOn).At(T1, T2)))
			disjoint := a.Have(
				"T₁ and T₂ are disjoint, zero lying in neither",
				"T₁ ∩ T₂ = ∅",
				BySets(
					first[1],
					second[1],
					direct,
					a.Have(
						"zero is not in T₁",
						"M.zero ∉ T₁",
						By(
							first[2],
							field.OneNotZeroOn.Read(fieldR),
							linear_independence.IndependentZeroNotIn.Read(moduleOn).At(T1)))))
			count := a.Have(
				"so T₁ ∪ T₂ has the members of T₁ and of T₂",
				"finite(T₁ ∪ T₂) ∧ card(T₁ ∪ T₂) = card(T₁) + card(T₂)",
				By(
					first[0],
					second[0],
					disjoint,
					finite_set.FiniteUnion.At(T1, T2),
					cardinality.CardUnion.At(T1, T2)))

			// A member of U₁ + U₂ splits uniquely, since U₁ and U₂ meet only in zero.
			unique := a.Have(
				"a sum of a member of U₁ and a member of U₂ determines both",
				"∀a₁ a₂ b₁ b₂:B. a₁ ∈ U₁ ∧ b₁ ∈ U₁ ∧ a₂ ∈ U₂ ∧ b₂ ∈ U₂ ∧ a₁ + a₂ = b₁ + b₂ ⇒ a₁ = b₁ ∧ a₂ = b₂",
				Derive(func(b *Argument) {
					b.FixAs[B]("a₁")
					b.FixAs[B]("a₂")
					b.FixAs[B]("b₁")
					b.FixAs[B]("b₂")
					parts := b.Conjuncts(
						b.Assume(),
						"a₁ lies in U₁",
						"b₁ lies in U₁",
						"a₂ lies in U₂",
						"b₂ lies in U₂",
						"the sums agree")
					inM := b.Have(
						"all four lie in M",
						"a₁ ∈ M.carrier ∧ b₁ ∈ M.carrier ∧ a₂ ∈ M.carrier ∧ b₂ ∈ M.carrier",
						BySets(parts[0], parts[1], parts[2], parts[3], u1InM, u2InM))
					moved := b.Have(
						"so a₁ − b₁ = b₂ − a₂",
						"a₁ + -b₁ = b₂ + -a₂",
						ByChase(Depth(0), moduleOn, inM, parts[4]))
					inU1 := b.Have(
						"a₁ − b₁ lies in U₁",
						"a₁ + -b₁ ∈ U₁",
						By(parts[0], parts[1], submodule.SubmoduleSub.Read(subU1)))
					inU2 := b.Have(
						"b₂ − a₂ lies in U₂",
						"b₂ + -a₂ ∈ U₂",
						By(parts[2], parts[3], submodule.SubmoduleSub.Read(subU2)))
					zero := b.Have(
						"so it lies in both, and is zero",
						"a₁ + -b₁ = M.zero",
						BySets(moved, inU1, inU2, direct))
					b.Show(
						"hence a₁ = b₁ and a₂ = b₂",
						ByChase(Depth(0), moduleOn, inM, moved, zero))
				}))

			sumSub := a.Have(
				"U₁ + U₂ is a submodule",
				"submodule(R, M, set_mul(M.add, U₁, U₂))",
				By(subU1, subU2, submodule.SubmoduleSum.Read(moduleOn).At(U1, U2)))
			wSub := a.Have(
				"W₁ + W₂ is a submodule",
				"submodule(R, M, set_mul(M.add, W₁, W₂))",
				By(subW1, subW2, submodule.SubmoduleSum.Read(moduleOn).At(W1, W2)))
			wInU := a.Have(
				"W₁ + W₂ lies in U₁ + U₂",
				"set_mul(M.add, W₁, W₂) ⊆ set_mul(M.add, U₁, U₂)",
				Simp(Fwd(set_basic.SubsetDef)),
				Derive(func(b *Argument) {
					z := b.FixAs[B]("z")
					_, _, sum := b.Unpack2As[B, B](b.Have(
						"z is a member of W₁ plus a member of W₂",
						"∃w₁ w₂:B. w₁ ∈ W₁ ∧ w₂ ∈ W₂ ∧ z = w₁ + w₂",
						By(b.Assume(), quotient_group.InSetMul.At(add, W1, W2, z))), "w₁", "w₂")
					sp := b.Conjuncts(
						sum,
						"w₁ lies in W₁",
						"w₂ lies in W₂",
						"z is their sum")
					inU := b.Have(
						"each lies in its U",
						"w₁ ∈ U₁ ∧ w₂ ∈ U₂",
						BySets(sp[0], sp[1], w1InU1, w2InU2))
					b.Show(
						"so z lies in U₁ + U₂",
						By(inU, sp[2], quotient_group.InSetMul.At(add, U1, U2, z)))
				}))
			// Two sets of vectors holding zero lie in their sum: x = x + 0 = 0 + x.
			unionInSum := a.Have(
				"two sets of vectors holding zero lie in their sum",
				Statement{
					Binders: "∀X Y:set(B).",
					Hypotheses: []string{
						"M.zero ∈ X",
						"M.zero ∈ Y",
						"X ⊆ M.carrier",
						"Y ⊆ M.carrier",
					},
					Conclusion: "X ∪ Y ⊆ set_mul(M.add, X, Y)",
				},
				Derive(func(b *Argument) {
					X := b.FixAs[Set[B]]("X")
					Y := b.FixAs[Set[B]]("Y")
					parts := b.Conjuncts(
						b.Assume(),
						"X holds zero",
						"Y holds zero",
						"X lies in M",
						"Y lies in M")
					b.Do(Simp(Fwd(set_basic.SubsetDef)))
					t := b.FixAs[B]("t")
					inUnion := b.Have(
						"t lies in X or in Y, and in M",
						"(t ∈ X ∨ t ∈ Y) ∧ t ∈ M.carrier",
						BySets(b.Assume(), parts[2], parts[3]))
					tm := b.MemberOf[on.M](t, b.Have(
						"t lies in M",
						"t ∈ M.carrier",
						By(inUnion)))
					b.Show(
						"t is t plus zero and zero plus t",
						By(
							inUnion,
							parts[0],
							parts[1],
							group.RightIdentityOn.Read(additive).At(tm),
							group.LeftIdentityOn.Read(additive).At(tm),
							quotient_group.InSetMul.At(add, X, Y, t)))
				}))
			tInU := a.Have(
				"T₁ ∪ T₂ lies in U₁ + U₂",
				"T₁ ∪ T₂ ⊆ set_mul(M.add, U₁, U₂)",
				By(
					first[1],
					second[1],
					submodule.SubmoduleZero.Read(subU1),
					submodule.SubmoduleZero.Read(subU2),
					u1InM,
					u2InM,
					unionInSum.At(U1, U2),
					set_order.SubsetTrans.At(
						T, a.TermAs[Set[B]]("U₁ ∪ U₂"), a.TermAs[Set[B]]("set_mul(M.add, U₁, U₂)")),
					a.Have(
						"T₁ ∪ T₂ lies in U₁ ∪ U₂",
						"T₁ ∪ T₂ ⊆ U₁ ∪ U₂",
						BySets(first[1], second[1]))))
			spansInSpan := a.Have(
				"the spans of T₁ and T₂ lie in the span of T₁ ∪ T₂",
				"module_span(R, M, T₁) ⊆ module_span(R, M, T₁ ∪ T₂) ∧ "+
					"module_span(R, M, T₂) ⊆ module_span(R, M, T₁ ∪ T₂)",
				By(
					submodule.SpanMono.At(R, M, T1, T),
					submodule.SpanMono.At(R, M, T2, T),
					set_order.SubsetUnion.At(T1, T2),
					set_order.SubsetUnion.At(T2, T1)))
			spanned := a.Have(
				"U₁ + U₂ is the span of T₁ ∪ T₂ plus W₁ + W₂",
				"set_mul(M.add, U₁, U₂) ⊆ set_mul(M.add, module_span(R, M, T₁ ∪ T₂), set_mul(M.add, W₁, W₂))",
				Simp(Fwd(set_basic.SubsetDef)),
				Derive(func(b *Argument) {
					x := b.FixAs[B]("x")
					u1, u2, xIs := b.Unpack2As[B, B](b.Have(
						"x is a member of U₁ plus a member of U₂",
						"∃u₁ u₂:B. u₁ ∈ U₁ ∧ u₂ ∈ U₂ ∧ x = u₁ + u₂",
						By(b.Assume(), quotient_group.InSetMul.At(add, U1, U2, x))), "u₁", "u₂")
					xParts := b.Conjuncts(
						xIs,
						"u₁ lies in U₁",
						"u₂ lies in U₂",
						"x is their sum")
					_, _, u1Is := b.Unpack2As[B, B](b.Have(
						"u₁ is a member of the span of T₁ plus a member of W₁",
						"∃s₁ w₁:B. s₁ ∈ module_span(R, M, T₁) ∧ w₁ ∈ W₁ ∧ u₁ = s₁ + w₁",
						By(
							b.Have(
								"u₁ lies in the span of T₁ plus W₁",
								"u₁ ∈ set_mul(M.add, module_span(R, M, T₁), W₁)",
								BySets(xParts[0], first[3])),
							quotient_group.InSetMul.At(add, b.TermAs[Set[B]]("module_span(R, M, T₁)"), W1, u1))), "s₁", "w₁")
					_, _, u2Is := b.Unpack2As[B, B](b.Have(
						"u₂ is a member of the span of T₂ plus a member of W₂",
						"∃s₂ w₂:B. s₂ ∈ module_span(R, M, T₂) ∧ w₂ ∈ W₂ ∧ u₂ = s₂ + w₂",
						By(
							b.Have(
								"u₂ lies in the span of T₂ plus W₂",
								"u₂ ∈ set_mul(M.add, module_span(R, M, T₂), W₂)",
								BySets(xParts[1], second[3])),
							quotient_group.InSetMul.At(add, b.TermAs[Set[B]]("module_span(R, M, T₂)"), W2, u2))), "s₂", "w₂")
					p1 := b.Conjuncts(
						u1Is,
						"s₁ lies in the span of T₁",
						"w₁ lies in W₁",
						"u₁ is their sum")
					p2 := b.Conjuncts(
						u2Is,
						"s₂ lies in the span of T₂",
						"w₂ lies in W₂",
						"u₂ is their sum")
					inM := b.Have(
						"the four parts lie in M",
						"s₁ ∈ M.carrier ∧ w₁ ∈ M.carrier ∧ s₂ ∈ M.carrier ∧ w₂ ∈ M.carrier",
						BySets(p1[0], p1[1], p2[0], p2[1], span1InU1, span2InU2, w1InU1, w2InU2, u1InM, u2InM))
					regroup := b.Have(
						"x regroups as (s₁ + s₂) + (w₁ + w₂)",
						"x = (s₁ + s₂) + (w₁ + w₂)",
						ByChase(Depth(0), moduleOn, inM, xParts[2], p1[2], p2[2]))
					parts := b.Have(
						"s₁ and s₂ lie in the span of T₁ ∪ T₂",
						"s₁ ∈ module_span(R, M, T₁ ∪ T₂) ∧ s₂ ∈ module_span(R, M, T₁ ∪ T₂)",
						BySets(p1[0], p2[0], spansInSpan))
					inW := b.Have(
						"w₁ + w₂ lies in W₁ + W₂",
						"w₁ + w₂ ∈ set_mul(M.add, W₁, W₂)",
						By(p1[1], p2[1], quotient_group.InSetMul.At(add, W1, W2, b.TermAs[B]("w₁ + w₂"))))
					b.Show(
						"so x lies in the span of T₁ ∪ T₂ plus W₁ + W₂",
						By(
							regroup,
							parts,
							submodule.SubmoduleAdd.Read(spanSub),
							inW,
							quotient_group.InSetMul.At(add, span, b.TermAs[Set[B]]("set_mul(M.add, W₁, W₂)"), x)))
				}))
			meets := a.Have(
				"the span of T₁ ∪ T₂ meets W₁ + W₂ only in zero",
				"module_span(R, M, T₁ ∪ T₂) ∩ set_mul(M.add, W₁, W₂) ⊆ {M.zero}",
				Derive(func(b *Argument) {
					span1 := b.TermAs[Set[B]]("module_span(R, M, T₁)")
					span2 := b.TermAs[Set[B]]("module_span(R, M, T₂)")
					sub1 := b.Have(
						"the span of T₁ is a submodule",
						"submodule(R, M, module_span(R, M, T₁))",
						By(
							b.Have(
								"T₁ lies in M",
								"T₁ ⊆ M.carrier",
								BySets(first[1], u1InM)),
							submodule.SpanSubmodule.Read(moduleOn).At(T1)))
					sub2 := b.Have(
						"the span of T₂ is a submodule",
						"submodule(R, M, module_span(R, M, T₂))",
						By(
							b.Have(
								"T₂ lies in M",
								"T₂ ⊆ M.carrier",
								BySets(second[1], u2InM)),
							submodule.SpanSubmodule.Read(moduleOn).At(T2)))
					sumSub := b.Have(
						"their sum is a submodule",
						"submodule(R, M, set_mul(M.add, module_span(R, M, T₁), module_span(R, M, T₂)))",
						By(sub1, sub2, submodule.SubmoduleSum.Read(moduleOn).At(span1, span2)))
					inSum := b.Have(
						"T₁ ∪ T₂ lies in the sum of the spans",
						"T₁ ∪ T₂ ⊆ set_mul(M.add, module_span(R, M, T₁), module_span(R, M, T₂))",
						By(
							submodule.SubmoduleZero.Read(sub1),
							submodule.SubmoduleZero.Read(sub2),
							submodule.SubmoduleSubset.Read(sub1),
							submodule.SubmoduleSubset.Read(sub2),
							unionInSum.At(span1, span2),
							set_order.SubsetTrans.At(T, b.TermAs[Set[B]]("module_span(R, M, T₁) ∪ module_span(R, M, T₂)"),
								b.TermAs[Set[B]]("set_mul(M.add, module_span(R, M, T₁), module_span(R, M, T₂))")),
							b.Have(
								"T₁ ∪ T₂ lies in the union of the spans",
								"T₁ ∪ T₂ ⊆ module_span(R, M, T₁) ∪ module_span(R, M, T₂)",
								BySets(submodule.SubsetSpan.At(R, M, T1), submodule.SubsetSpan.At(R, M, T2)))))
					splits := b.Have(
						"the span of T₁ ∪ T₂ lies in the span of T₁ plus the span of T₂",
						"module_span(R, M, T₁ ∪ T₂) ⊆ set_mul(M.add, module_span(R, M, T₁), module_span(R, M, T₂))",
						By(
							sumSub,
							inSum,
							submodule.SpanLeast.At(
								R, M, T, b.TermAs[Set[B]]("set_mul(M.add, module_span(R, M, T₁), module_span(R, M, T₂))"))))
					pointwise := b.Have(
						"a member of both is zero",
						Statement{
							Binders: "∀z:B.",
							Hypotheses: []string{
								"z ∈ set_mul(M.add, module_span(R, M, T₁), module_span(R, M, T₂))",
								"z ∈ set_mul(M.add, W₁, W₂)",
							},
							Conclusion: "z = M.zero",
						},
						Derive(func(c *Argument) {
							z := c.FixAs[B]("z")
							both := c.Conjuncts(
								c.Assume(),
								"z splits over the spans",
								"z splits over W₁ and W₂")
							_, _, viaSpans := c.Unpack2As[B, B](c.Have(
								"z = s₁ + s₂",
								"∃s₁ s₂:B. s₁ ∈ module_span(R, M, T₁) ∧ s₂ ∈ module_span(R, M, T₂) ∧ z = s₁ + s₂",
								By(
									both[0],
									quotient_group.InSetMul.At(
										add, c.TermAs[Set[B]]("module_span(R, M, T₁)"), c.TermAs[Set[B]]("module_span(R, M, T₂)"), z))),
								"s₁",
								"s₂")
							_, _, viaW := c.Unpack2As[B, B](c.Have(
								"z = w₁ + w₂",
								"∃w₁ w₂:B. w₁ ∈ W₁ ∧ w₂ ∈ W₂ ∧ z = w₁ + w₂",
								By(both[1], quotient_group.InSetMul.At(add, W1, W2, z))), "w₁", "w₂")
							sp := c.Conjuncts(
								viaSpans,
								"s₁ lies in the span of T₁",
								"s₂ lies in the span of T₂",
								"z = s₁ + s₂")
							wp := c.Conjuncts(
								viaW,
								"w₁ lies in W₁",
								"w₂ lies in W₂",
								"z = w₁ + w₂")
							equal := c.Conjuncts(
								c.Have(
									"the two splittings agree",
									"s₁ = w₁ ∧ s₂ = w₂",
									By(
										c.Have(
											"s₁ and w₁ lie in U₁, s₂ and w₂ in U₂",
											"s₁ ∈ U₁ ∧ w₁ ∈ U₁ ∧ s₂ ∈ U₂ ∧ w₂ ∈ U₂",
											BySets(sp[0], sp[1], wp[0], wp[1], span1InU1, span2InU2, w1InU1, w2InU2)),
										c.Have(
											"both sums are z",
											"s₁ + s₂ = w₁ + w₂",
											By(Normalized, sp[2], wp[2])),
										unique.At(c.TermAs[B]("s₁"), c.TermAs[B]("s₂"), c.TermAs[B]("w₁"), c.TermAs[B]("w₂")))),
								"s₁ = w₁",
								"s₂ = w₂")
							zeros := c.Have(
								"so s₁ and s₂ are zero",
								"s₁ = M.zero ∧ s₂ = M.zero",
								BySets(sp[0], sp[1], wp[0], wp[1], equal[0], equal[1], first[4], second[4]))
							c.Show(
								"and z is zero",
								By(zeros, sp[2], group.LeftIdentityOn.Read(additive), group.OneIn.Read(additive)))
						}))
					b.Show(
						"so the span meets W₁ + W₂ only in zero",
						BySets(splits, pointwise))
				}))
			counted := a.Have(
				"the complement counts the dimension of (U₁ + U₂)/(W₁ + W₂)",
				"finite_dimensional(R, «quotientSums») ∧ module_dim(R, «quotientSums») = card(T₁ ∪ T₂)",
				By(
					scalarsField,
					sumSub,
					wSub,
					wInU,
					count,
					tInU,
					independentT,
					spanned,
					meets,
					moduleOn,
					QuotientComplementDim.At(
						R,
						M,
						inv,
						a.TermAs[Set[B]]("set_mul(M.add, U₁, U₂)"),
						a.TermAs[Set[B]]("set_mul(M.add, W₁, W₂)"),
						T)))
			a.Show(
				"which is the sum of the two counts",
				By(counted, count, first[5], second[5]))
		}),
})}

// ProperSubmoduleDimLess — over a field, a proper subspace W of a subspace
// V of a finite-dimensional space has smaller dimension than V: its
// dimension is at most that of V (SubmoduleDim), and cannot reach it, a
// subspace of V of the same dimension being V (SubmoduleDimEq), which holds
// e outside W.
var ProperSubmoduleDimLess = properSubmoduleDimLessThm{family.Add(registry.ProofEntry{
	Name: "ProperSubmoduleDimLess",
	Key:  "prop_5e2e0c057c6a7a25",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀inv:(A → A). ∀M:module_ops(A, B). ∀W V:set(B). ∀e:B.",
		Hypotheses: []string{
			"ring_subfield(R, inv, R.carrier)",
			"module_on(R, M)",
			"finite_dimensional(R, M)",
			"submodule(R, M, W)",
			"submodule(R, M, V)",
			"W ⊆ V",
			"e ∈ V",
			"e ∉ W",
		},
		Conclusion: "module_dim(R, restrict_module(M, W)) + 1 ≤ module_dim(R, restrict_module(M, V))",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			inv *Arrow[A, A],
			M *Expr[ModuleOps[A, B]],
			W, V *Expr[Set[B]],
			e *Expr[B],
			scalarsField, moduleM, finiteM, subW, subV, wInV, eInV, outside Fact,
		) {
			onV := a.TermAs[ModuleOps[A, B]]("restrict_module(M, V)")
			moduleV := a.Have(
				"V is a module",
				"module_on(R, restrict_module(M, V))",
				By(moduleM, subV, submodule.SubmoduleModuleOn.At(R, M, V)))
			finiteV := a.Have(
				"V is finite-dimensional, a subspace of the finite-dimensional M",
				"finite_dimensional(R, restrict_module(M, V))",
				By(scalarsField, moduleM, finiteM, subV, SubmoduleDim.At(R, M, inv, V)))
			subWV := a.Have(
				"W is a subspace of V",
				"submodule(R, restrict_module(M, V), W)",
				By(subW, wInV, submodule.SubmoduleRestrict.At(R, M, V, W)))
			twice := module_record.RestrictModuleTwice.At(M, V, W)
			bound := a.Have(
				"so the dimension of W is at most that of V",
				"module_dim(R, restrict_module(M, W)) ≤ module_dim(R, restrict_module(M, V))",
				By(Normalized, scalarsField, moduleV, finiteV, subWV, twice, SubmoduleDim.At(R, onV, inv, W)))
			proper := a.Have(
				"and differs from it, a subspace of V of the same dimension being V, which holds e",
				"module_dim(R, restrict_module(M, W)) ≠ module_dim(R, restrict_module(M, V))",
				By(outside, eInV, scalarsField, moduleV, finiteV, subWV, twice, SubmoduleDimEq.At(R, onV, inv, W)))
			a.Show(
				"so it is less",
				ByArith(bound, proper))
		}),
	Reading: "finite_dimensional(R, M) keeps both dimensions finite, so " +
		"the + 1 is not absorbed by a junk value. At W = V no such e exists.",
})}
