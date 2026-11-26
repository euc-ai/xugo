// sections.go — sections are forms: for large j the meet of the chart of F
// with tʲ times the chart of G is the forms of degree r·j over F(x)ʲ, by a
// dimension count at three consecutive degrees and a descent in two exponents.

package projective_sections

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_extension"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/homogeneous_polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/scheme/projective_curve"
	"github.com/euc-ai/xugo/library/proofs/scheme/projective_form_pair"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_product"
	"github.com/euc-ai/xugo/library/registry"
)

// MultipliersIntoSubspace — for k-subspaces V, W, Z of M and f ≠ 0, g with
// f·V, g·V ⊆ W, f·W, g·W ⊆ Z, Z = f·W + g·W and dim V + dim Z = 2 dim W,
// an element u with f·u and g·u in W lies in V: the pairs (p, q) of W × W
// with g·p = f·q are the kernel of (p, q) ↦ g·p − f·q, onto Z, so of
// dimension 2 dim W − dim Z = dim V, and v ↦ (f·v, g·v) carries V one to
// one into that kernel, hence onto it; (f·u, g·u) lies there.
var MultipliersIntoSubspace = multipliersIntoSubspaceThm{family.Add(registry.ProofEntry{
	Name: "MultipliersIntoSubspace",
	Key:  "prop_325449129293ef27",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k V W Z:set(A). ∀f g u:A.",
		Hypotheses: []string{
			"subfield(M, k)",
			"submodule(«hilbertCoefficients», regular_module(field_ring(M)), V)",
			"submodule(«hilbertCoefficients», regular_module(field_ring(M)), W)",
			"submodule(«hilbertCoefficients», regular_module(field_ring(M)), Z)",
			"finite_dimensional(«hilbertCoefficients», «vectors»(V))",
			"finite_dimensional(«hilbertCoefficients», «vectors»(W))",
			"f ∈ M.carrier",
			"g ∈ M.carrier",
			"f ≠ M.zero",
			"∀v:A. v ∈ V ⇒ f * v ∈ W ∧ g * v ∈ W",
			"∀w:A. w ∈ W ⇒ f * w ∈ Z ∧ g * w ∈ Z",
			"∀z:A. z ∈ Z ⇒ ∃p q:A. p ∈ W ∧ q ∈ W ∧ z = f * p + g * q",
			"«dim»(«vectors»(V)) + «dim»(«vectors»(Z)) = «dim»(«vectors»(W)) + «dim»(«vectors»(W))",
			"u ∈ M.carrier",
			"f * u ∈ W",
			"g * u ∈ W",
		},
		Conclusion: "u ∈ V",
		Abbrev: Abbrev{
			{Name: "vectors", Text: "restrict_module(regular_module(field_ring(M)))"},
			{Name: "dim", Text: "module_dim(«hilbertCoefficients»)"},
			{Name: "pairs", Text: "product_module(«vectors»(W), «vectors»(W))"},
			{Name: "difference", Text: "λz:prod(A, A). g * fst(z) + -(f * snd(z))"},
			{Name: "kernel", Text: "group_kernel(M.zero, set_cross(W, W), «difference»)"},
			{Name: "multipliers", Text: "λv:A. (f * v, g * v)"},
		},
	},
		func(a *Argument, M field.FieldFact[on.M], k, V, W, Z *Expr[Set[A]], f, g, u *Expr[A], given Fact) {
			hyp := a.Conjuncts(
				given,
				"k is a subfield of M",
				"V is a k-subspace of M",
				"so is W",
				"so is Z",
				"V is finite-dimensional over k",
				"so is W",
				"f lies in M",
				"so does g",
				"f is not zero",
				"f and g carry V into W",
				"and W into Z",
				"every member of Z is f·p + g·q with p and q in W",
				"dim V + dim Z = 2 dim W",
				"u lies in M",
				"f·u lies in W",
				"so does g·u")
			subfieldK, subV, subW, subZ := hyp[0], hyp[1], hyp[2], hyp[3]
			finiteV, finiteW, fIn, gIn, fNonzero := hyp[4], hyp[5], hyp[6], hyp[7], hyp[8]
			intoW, intoZ, generated, dims := hyp[9], hyp[10], hyp[11], hyp[12]
			uIn, fuIn, guIn := hyp[13], hyp[14], hyp[15]
			fieldM := a.TermAs[FieldOps[A]]("M")
			scalars := a.TermAs[module_record.RingOps[A]]("«hilbertCoefficients»")
			regular := a.TermAs[module_record.ModuleOps[A, A]]("regular_module(field_ring(M))")
			inv := a.TermAs[Fun[A, A]]("M.inv")
			vectorsV := a.TermAs[module_record.ModuleOps[A, A]]("«vectors»(V)")
			vectorsW := a.TermAs[module_record.ModuleOps[A, A]]("«vectors»(W)")
			pairModule := a.TermAs[module_record.ModuleOps[A, Prod[A, A]]]("«pairs»")
			difference := a.TermAs[Fun[Prod[A, A], A]]("«difference»")
			kernel := a.TermAs[Set[Prod[A, A]]]("«kernel»")
			kernelModule := a.TermAs[module_record.ModuleOps[A, Prod[A, A]]](
				"restrict_module(«pairs», «kernel»)")
			multipliers := a.TermAs[Fun[A, Prod[A, A]]]("«multipliers»")
			space := a.Have(
				"over k, M is a vector space and k a field",
				"module_on(«hilbertCoefficients», regular_module(field_ring(M))) ∧ "+
					"ring_subfield(«hilbertCoefficients», M.inv, k)",
				By(
					M,
					subfieldK,
					field_extension.SubfieldScalars.At(fieldM, k),
					field.SubfieldRingSubfield.At(fieldM, k, k)))
			spaceParts := a.Conjuncts(
				space,
				"M is a k-vector space",
				"k is a field under M's operations")
			moduleM, fieldK := spaceParts[0], spaceParts[1]
			moduleW := a.Have(
				"W is a k-vector space",
				"module_on(«hilbertCoefficients», «vectors»(W))",
				By(moduleM, subW, submodule.SubmoduleModuleOn.At(scalars, regular, W)))
			moduleV := a.Have(
				"so is V",
				"module_on(«hilbertCoefficients», «vectors»(V))",
				By(moduleM, subV, submodule.SubmoduleModuleOn.At(scalars, regular, V)))
			product := a.Conjuncts(
				a.Have(
					"W × W is a k-vector space, finite-dimensional of dimension 2 dim W",
					"module_on(«hilbertCoefficients», «pairs») ∧ "+
						"finite_dimensional(«hilbertCoefficients», «pairs») ∧ "+
						"«dim»(«pairs») = «dim»(«vectors»(W)) + «dim»(«vectors»(W))",
					By(
						moduleW,
						fieldK,
						finiteW,
						module_homomorphism.ProductModuleOn.At(scalars, vectorsW, vectorsW),
						module_dimension.DimProduct.At(scalars, vectorsW, inv, vectorsW))),
				"W × W is a k-vector space",
				"finite-dimensional",
				"of dimension 2 dim W")
			inM := a.Have(
				"V, W, Z and k lie in M",
				"V ⊆ M.carrier ∧ W ⊆ M.carrier ∧ Z ⊆ M.carrier ∧ k ⊆ M.carrier",
				By(
					subV,
					subW,
					subZ,
					subfieldK,
					submodule.SubmoduleSubset.At(scalars, regular, V),
					submodule.SubmoduleSubset.At(scalars, regular, W),
					submodule.SubmoduleSubset.At(scalars, regular, Z),
					field.SubfieldSubset.At(fieldM, k)))
			// The difference map (p, q) ↦ g·p − f·q is k-linear on W × W.
			into := a.Have(
				"g·p − f·q lies in M for p, q in W",
				"∀z:prod(A, A). z ∈ set_cross(W, W) ⇒ «difference»(z) ∈ M.carrier",
				Derive(func(b *Argument) {
					z := b.FixAs[Prod[A, A]]("z")
					zIn := b.Assume()
					parts := b.Have(
						"both components of z lie in M",
						"fst(z) ∈ M.carrier ∧ snd(z) ∈ M.carrier",
						BySets(zIn, inM, set_product.InCrossProjections.At(W, W, z)))
					b.Show(
						"so does g·fst(z) − f·snd(z)",
						By(
							fIn,
							gIn,
							parts,
							comm_ring.AddIn.Read(field.RingOn.Read(M)),
							comm_ring.MulIn.Read(field.RingOn.Read(M)),
							comm_ring.NegIn.Read(field.RingOn.Read(M))))
				}))
			adds := a.Have(
				"the difference map is additive",
				Statement{
					Binders:    "∀z w:prod(A, A).",
					Hypotheses: []string{"z ∈ set_cross(W, W) ∧ w ∈ set_cross(W, W)"},
					Conclusion: "«difference»((fst(z) + fst(w), snd(z) + snd(w))) = «difference»(z) + «difference»(w)",
				},
				Derive(func(b *Argument) {
					z, w := b.FixAs[Prod[A, A]]("z"), b.FixAs[Prod[A, A]]("w")
					both := b.Assume()
					parts := b.Have(
						"the components of z and w lie in M",
						"fst(z) ∈ M.carrier ∧ snd(z) ∈ M.carrier ∧ fst(w) ∈ M.carrier ∧ snd(w) ∈ M.carrier",
						BySets(
							both,
							inM,
							set_product.InCrossProjections.At(W, W, z),
							set_product.InCrossProjections.At(W, W, w)))
					b.Show(
						"componentwise, g(p + p') − f(q + q') = (gp − fq) + (gp' − fq')",
						Simp(Fwd(pairs.Fst), Fwd(pairs.Snd)),
						ByArith(M, fIn, gIn, parts))
				}))
			scales := a.Have(
				"and k-homogeneous",
				Statement{
					Binders:    "∀c:A. ∀z:prod(A, A).",
					Hypotheses: []string{"c ∈ k ∧ z ∈ set_cross(W, W)"},
					Conclusion: "«difference»((c * fst(z), c * snd(z))) = c * «difference»(z)",
				},
				Derive(func(b *Argument) {
					b.FixAs[A]("c")
					z := b.FixAs[Prod[A, A]]("z")
					both := b.Assume()
					parts := b.Have(
						"c and the components of z lie in M",
						"c ∈ M.carrier ∧ fst(z) ∈ M.carrier ∧ snd(z) ∈ M.carrier",
						BySets(both, inM, set_product.InCrossProjections.At(W, W, z)))
					b.Show(
						"componentwise, g(cp) − f(cq) = c(gp − fq)",
						Simp(Fwd(pairs.Fst), Fwd(pairs.Snd)),
						ByArith(M, fIn, gIn, parts))
				}))
			linear := a.Have(
				"so (p, q) ↦ g·p − f·q is a k-linear map of W × W to M",
				"module_homomorphism(«hilbertCoefficients», «pairs», regular_module(field_ring(M)), «difference»)",
				By(
					module_homomorphism.ModuleHomomorphismDef.At(scalars, pairModule, regular, difference),
					product[0],
					moduleM,
					into,
					adds,
					scales))
			rankNullity := a.Have(
				"rank-nullity: dim of its kernel + dim of its image = dim W × W",
				"«dim»(restrict_module(«pairs», «kernel»)) + "+
					"«dim»(«vectors»(image(«difference», set_cross(W, W)))) = "+
					"«dim»(«pairs»)",
				By(
					module_dimension.RankNullity.At(scalars, pairModule, inv, regular, difference),
					product[0],
					product[1],
					fieldK,
					moduleM,
					linear))
			// Its image is Z: f·W and g·W lie in Z, and Z is f·W + g·W.
			reachesZ := a.Have(
				"g·p − f·q lies in Z",
				"∀z:prod(A, A). z ∈ set_cross(W, W) ⇒ «difference»(z) ∈ Z",
				Derive(func(b *Argument) {
					z := b.FixAs[Prod[A, A]]("z")
					zIn := b.Assume()
					parts := b.Have(
						"both components of z lie in W",
						"fst(z) ∈ W ∧ snd(z) ∈ W",
						By(zIn, set_product.InCrossProjections.At(W, W, z)))
					b.Show(
						"g·fst(z) and f·snd(z) lie in Z, and Z is a subspace",
						By(intoZ, parts, submodule.SubmoduleSub.Read(subZ)))
				}))
			fromZ := a.Have(
				"every member f·p + g·q of Z is g·q − f·(−p)",
				"∀x:A. x ∈ Z ⇒ ∃z:prod(A, A). z ∈ set_cross(W, W) ∧ x = «difference»(z)",
				Derive(func(b *Argument) {
					x := b.FixAs[A]("x")
					xIn := b.Assume()
					_, _, split := b.Unpack2As[A, A](GroupPremises(xIn, generated.At(x)), "p", "q")
					parts := b.Conjuncts(
						split,
						"p lies in W",
						"so does q",
						"x is f·p + g·q")
					members := b.Have(
						"x, p and q lie in M",
						"x ∈ M.carrier ∧ p ∈ M.carrier ∧ q ∈ M.carrier",
						BySets(xIn, parts[0], parts[1], inM))
					b.Take(b.TermAs[Prod[A, A]]("(q, -p)"))
					b.Do(SplitConj(
						Case(
							"(q, −p) is a pair of W",
							By(parts[0], parts[1], subW, set_product.InCross, submodule.SubmoduleNeg)),
						Case(
							"and g·q − f·(−p) is x",
							Simp(Fwd(pairs.Fst), Fwd(pairs.Snd)),
							ByArith(M, fIn, gIn, parts[2], members))))
				}))
			image := a.Have(
				"so the image of the difference map is Z",
				"image(«difference», set_cross(W, W)) = Z",
				BySets(fromZ, reachesZ))
			kernelFacts := a.Conjuncts(
				a.Have(
					"its kernel is a finite-dimensional k-subspace of W × W",
					"submodule(«hilbertCoefficients», «pairs», «kernel») ∧ "+
						"module_on(«hilbertCoefficients», restrict_module(«pairs», «kernel»)) ∧ "+
						"finite_dimensional(«hilbertCoefficients», restrict_module(«pairs», «kernel»))",
					By(
						module_homomorphism.KernelSubmodule.At(scalars, pairModule, regular, difference),
						linear,
						product[0],
						product[1],
						fieldK,
						submodule.SubmoduleModuleOn.At(scalars, pairModule, kernel),
						module_dimension.SubmoduleDim.At(scalars, pairModule, inv, kernel))),
				"the kernel is a subspace of W × W",
				"a k-vector space",
				"finite-dimensional")
			// v ↦ (f·v, g·v) carries V into the kernel, k-linearly and one to one.
			multipliersInto := a.Have(
				"(f·v, g·v) lies in the kernel for v in V",
				"∀v:A. v ∈ V ⇒ «multipliers»(v) ∈ «kernel»",
				Derive(func(b *Argument) {
					v := b.FixAs[A]("v")
					vIn := b.Assume()
					vM := b.Have(
						"v lies in M",
						"v ∈ M.carrier",
						BySets(vIn, inM))
					cancels := b.Have(
						"g·(f·v) − f·(g·v) is zero",
						"g * (f * v) + -(f * (g * v)) = M.zero",
						ByArith(M, fIn, gIn, vM))
					b.Show(
						"(f·v, g·v) is a pair of W killed by the difference map",
						Unfold(group_homomorphism.GroupKernelDef),
						By(intoW.At(v), vIn, cancels, set_product.InCross, pairs.Fst, pairs.Snd))
				}))
			multipliersAdd := a.Have(
				"v ↦ (f·v, g·v) is additive",
				Statement{
					Binders:    "∀v w:A.",
					Hypotheses: []string{"v ∈ V ∧ w ∈ V"},
					Conclusion: "«multipliers»(v + w) = " +
						"(fst(«multipliers»(v)) + fst(«multipliers»(w)), snd(«multipliers»(v)) + snd(«multipliers»(w)))",
				},
				Derive(func(b *Argument) {
					b.FixAs[A]("v")
					b.FixAs[A]("w")
					both := b.Assume()
					parts := b.Have(
						"v and w lie in M",
						"v ∈ M.carrier ∧ w ∈ M.carrier",
						BySets(both, inM))
					b.Show(
						"componentwise, f(v + w) = fv + fw and g(v + w) = gv + gw",
						Simp(Fwd(pairs.Fst), Fwd(pairs.Snd), Fwd(pairs.PairEq)),
						ByArith(M, fIn, gIn, parts))
				}))
			multipliersScale := a.Have(
				"and k-homogeneous",
				Statement{
					Binders:    "∀c v:A.",
					Hypotheses: []string{"c ∈ k ∧ v ∈ V"},
					Conclusion: "«multipliers»(c * v) = (c * fst(«multipliers»(v)), c * snd(«multipliers»(v)))",
				},
				Derive(func(b *Argument) {
					b.FixAs[A]("c")
					b.FixAs[A]("v")
					both := b.Assume()
					parts := b.Have(
						"c and v lie in M",
						"c ∈ M.carrier ∧ v ∈ M.carrier",
						BySets(both, inM))
					b.Show(
						"componentwise, f(cv) = c(fv) and g(cv) = c(gv)",
						Simp(Fwd(pairs.Fst), Fwd(pairs.Snd), Fwd(pairs.PairEq)),
						ByArith(M, fIn, gIn, parts))
				}))
			multipliersLinear := a.Have(
				"so v ↦ (f·v, g·v) is a k-linear map of V into the kernel",
				"module_homomorphism(«hilbertCoefficients», "+
					"    «vectors»(V), "+
					"    restrict_module(«pairs», «kernel»), "+
					"    «multipliers»)",
				By(
					module_homomorphism.ModuleHomomorphismDef.At(scalars, vectorsV, kernelModule, multipliers),
					moduleV,
					kernelFacts[1],
					multipliersInto,
					multipliersAdd,
					multipliersScale))
			cancelF := a.Have(
				"multiplication by f is one to one on M, f being nonzero",
				"injective_on(M.carrier, M.mul(f))",
				By(M, fIn, fNonzero, field.MulBijective.At(fieldM, f)))
			oneToOne := a.Have(
				"so is v ↦ (f·v, g·v) on V",
				"injective_on(V, «multipliers»)",
				Simp(Fwd(functions.InjectiveOnDef)),
				Derive(func(b *Argument) {
					b.FixAs[A]("v")
					b.FixAs[A]("w")
					same := b.Assume()
					parts := b.Have(
						"v and w lie in M, and f·v = f·w",
						"v ∈ M.carrier ∧ w ∈ M.carrier ∧ f * v = f * w",
						BySets(same, inM, pairs.PairEq))
					b.Show(
						"so v = w",
						By(
							functions.InjectiveOnDef.At(a.TermAs[Set[A]]("M.carrier"), a.TermAs[Fun[A, A]]("M.mul(f)")),
							cancelF,
							parts))
				}))
			imageV := a.Conjuncts(
				a.Have(
					"its image is a subspace of the kernel of dimension dim V",
					"finite_dimensional(«hilbertCoefficients», "+
						"    restrict_module(restrict_module(«pairs», «kernel»), image(«multipliers», V))) ∧ "+
						"«dim»(restrict_module(restrict_module(«pairs», «kernel»), image(«multipliers», V))) = "+
						"«dim»(«vectors»(V)) ∧ "+
						"submodule(«hilbertCoefficients», restrict_module(«pairs», «kernel»), image(«multipliers», V))",
					By(
						module_dimension.InjectiveImageDim.At(scalars, inv, vectorsV, kernelModule, multipliers),
						module_homomorphism.ImageSubmodule.At(scalars, vectorsV, kernelModule, multipliers),
						fieldK,
						multipliersLinear,
						oneToOne,
						finiteV)),
				"the image is finite-dimensional",
				"of dimension dim V",
				"a subspace of the kernel")
			equalDims := a.Have(
				"and the kernel has dimension 2 dim W − dim Z = dim V too",
				"«dim»(restrict_module(restrict_module(«pairs», «kernel»), image(«multipliers», V))) = "+
					"«dim»(restrict_module(«pairs», «kernel»))",
				ByArith(image, dims, rankNullity, product[2], imageV[1]))
			filled := a.Have(
				"so the image fills the kernel",
				"image(«multipliers», V) = «kernel»",
				By(
					module_dimension.SubmoduleDimEq.At(
						scalars, kernelModule, inv, a.TermAs[Set[Prod[A, A]]]("image(«multipliers», V)")),
					kernelFacts[1],
					fieldK,
					kernelFacts[2],
					imageV[2],
					equalDims))
			// (f·u, g·u) lies in the kernel, so it is (f·v, g·v) for a v in V, and v = u.
			cancelsU := a.Have(
				"g·(f·u) − f·(g·u) is zero",
				"g * (f * u) + -(f * (g * u)) = M.zero",
				ByArith(M, fIn, gIn, uIn))
			uKernel := a.Have(
				"(f·u, g·u) lies in the kernel",
				"(f * u, g * u) ∈ «kernel»",
				Unfold(group_homomorphism.GroupKernelDef),
				By(fuIn, guIn, cancelsU, set_product.InCross, pairs.Fst, pairs.Snd))
			_, preimage := a.UnpackAs[A](a.Have(
				"so (f·u, g·u) is (f·v, g·v) for some v in V",
				"∃v:A. v ∈ V ∧ (f * u, g * u) = «multipliers»(v)",
				By(
					uKernel,
					filled,
					set_basic.InImage.At(multipliers, V, a.TermAs[Prod[A, A]]("(f * u, g * u)")))), "v")
			found := a.Conjuncts(
				preimage,
				"v lies in V",
				"(f·u, g·u) = (f·v, g·v)")
			sameF := a.Have(
				"v lies in M and f·u = f·v",
				"v ∈ M.carrier ∧ f * u = f * v",
				BySets(found[0], found[1], inM, pairs.PairEq))
			equal := a.Have(
				"multiplication by f being one to one, u = v",
				"u = v",
				By(
					functions.InjectiveOnDef.At(a.TermAs[Set[A]]("M.carrier"), a.TermAs[Fun[A, A]]("M.mul(f)")),
					cancelF,
					uIn,
					sameF))
			a.Show(
				"hence u lies in V",
				By(Normalized, equal, found[0]))
		}),
})}

// PowerShiftsGrade — when multiplication by f carries each U(e) into
// U(e + r), multiplication by f^c carries U(d) into U(d + r·c): by
// induction on c, f^(c+1)·v = f·(f^c·v).
var PowerShiftsGrade = powerShiftsGradeThm{family.Add(registry.ProofEntry{
	Name: "PowerShiftsGrade",
	Key:  "prop_78defba975b5308b",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀U:num → set(A). ∀f v:A. ∀r d c:num.",
		Hypotheses: []string{
			"f ∈ M.carrier",
			"∀e:num. U(e) ⊆ M.carrier",
			"∀e:num. ∀w:A. w ∈ U(e) ⇒ f * w ∈ U(e + r)",
			"v ∈ U(d)",
		},
		Conclusion: "monoid_pow(M.mul, M.one, f, c) * v ∈ U(d + r * c)",
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			U *Arrow[Nat, Set[A]],
			f, v *Expr[A],
			r, d *Expr[Nat],
			given Fact,
		) {
			hyp := a.Conjuncts(
				given,
				"f lies in M",
				"every U(e) lies in M",
				"f raises the degree by r",
				"v lies in U(d)")
			fIn, inM, raise, vIn := hyp[0], hyp[1], hyp[2], hyp[3]
			vM := a.Have(
				"v lies in M",
				"v ∈ M.carrier",
				BySets(inM.At(d), vIn))
			a.Induct("c")
			a.Base(
				"f⁰·v is v, of degree d",
				func(b *Argument) {
					unit := b.Have(
						"f⁰·v = v and d + r·0 = d",
						"monoid_pow(M.mul, M.one, f, 0) * v = v ∧ d + r * 0 = d",
						ByArith(M, fIn, vM))
					b.Show(
						"so f⁰·v lies in U(d)",
						By(Normalized, unit, vIn))
				})
			a.Step(
				"f^(c+1)·v is f times f^c·v, one degree r higher",
				func(b *Argument, ih Fact) {
					shifted := b.TermAs[Nat]("d + r * c")
					power := b.TermAs[A]("monoid_pow(M.mul, M.one, f, c) * v")
					powerM := b.Have(
						"f^c·v lies in M",
						"monoid_pow(M.mul, M.one, f, c) * v ∈ M.carrier",
						BySets(inM.At(shifted), ih))
					regroup := b.Have(
						"f^(c+1)·v = f·(f^c·v)",
						"monoid_pow(M.mul, M.one, f, suc(c)) * v = f * (monoid_pow(M.mul, M.one, f, c) * v)",
						Simp(Fwd(comm_monoid.MonoidPowDef)),
						ByArith(M, fIn, vM, powerM))
					degree := b.Have(
						"d + r·c + r = d + r·(c + 1)",
						"d + r * c + r = d + r * suc(c)",
						ByArith())
					b.Show(
						"so f^(c+1)·v lies in U(d + r·(c + 1))",
						By(raise.At(shifted, power), ih, regroup, degree))
				})
		}),
})}

// TwoMultipliersDescend — when f and g raise the degree by r and, from N
// on, f·v and g·v in U(r(i + 1)) force v into U(r·i), an element u with
// f^a·u in U(r(j + a)) and g^b·u in U(r(j + b)), j ≥ N, lies in U(r·j): by
// induction on a and then b, f·u satisfies the hypotheses at (a − 1, b)
// one degree up and g·u at (a, b − 1), so both lie in U(r(j + 1)).
var TwoMultipliersDescend = twoMultipliersDescendThm{family.Add(registry.ProofEntry{
	Name: "TwoMultipliersDescend",
	Key:  "prop_c738138184de8cac",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀U:num → set(A). ∀f g:A. ∀r N a b j:num. ∀u:A.",
		Hypotheses: []string{
			"f ∈ M.carrier",
			"g ∈ M.carrier",
			"∀d:num. ∀v:A. v ∈ U(d) ⇒ f * v ∈ U(d + r) ∧ g * v ∈ U(d + r)",
			"∀i:num. ∀v:A. " +
				"    N ≤ i ∧ v ∈ M.carrier ∧ f * v ∈ U(r * (i + 1)) ∧ g * v ∈ U(r * (i + 1)) ⇒ v ∈ U(r * i)",
			"N ≤ j",
			"u ∈ M.carrier",
			"monoid_pow(M.mul, M.one, f, a) * u ∈ U(r * (j + a))",
			"monoid_pow(M.mul, M.one, g, b) * u ∈ U(r * (j + b))",
		},
		Conclusion: "u ∈ U(r * j)",
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			U *Arrow[Nat, Set[A]],
			f, g *Expr[A],
			r, N *Expr[Nat],
			given Fact,
		) {
			hyp := a.Conjuncts(
				given,
				"f lies in M",
				"so does g",
				"f and g raise the degree by r",
				"from N on, f·v and g·v one degree up force v down")
			fIn, gIn, raise, descend := hyp[0], hyp[1], hyp[2], hyp[3]
			a.Induct("a")
			a.Base(
				"with no power of f, u is already in U(r·j)",
				func(b *Argument) {
					b.FixAs[Nat]("b")
					b.FixAs[Nat]("j")
					b.FixAs[A]("u")
					parts := b.Conjuncts(
						b.Assume(),
						"N ≤ j",
						"u lies in M",
						"f⁰·u lies in U(r·j)",
						"g^b·u lies in U(r(j + b))")
					unit := b.Have(
						"f⁰·u = u",
						"monoid_pow(M.mul, M.one, f, 0) * u = u",
						ByArith(M, fIn, parts[1]))
					b.Show(
						"so u lies in U(r·j)",
						By(parts[2], unit, nat_arith.AddZero))
				})
			a.Step(
				"one more power of f",
				func(outerStep *Argument, outer Fact) {
					outerStep.Induct("b")
					outerStep.Base(
						"with no power of g, u is already in U(r·j)",
						func(c *Argument) {
							c.FixAs[Nat]("j")
							c.FixAs[A]("u")
							parts := c.Conjuncts(
								c.Assume(),
								"N ≤ j",
								"u lies in M",
								"f^(a+1)·u lies in U(r(j + a + 1))",
								"g⁰·u lies in U(r·j)")
							unit := c.Have(
								"g⁰·u = u",
								"monoid_pow(M.mul, M.one, g, 0) * u = u",
								ByArith(M, gIn, parts[1]))
							c.Show(
								"so u lies in U(r·j)",
								By(parts[3], unit, nat_arith.AddZero))
						})
					outerStep.Step(
						"one more power of g: f·u and g·u lie one degree up",
						func(innerStep *Argument, inner Fact) {
							j := innerStep.FixAs[Nat]("j")
							u := innerStep.FixAs[A]("u")
							parts := innerStep.Conjuncts(
								innerStep.Assume(),
								"N ≤ j",
								"u lies in M",
								"f^(a+1)·u lies in U(r(j + a + 1))",
								"g^(b+1)·u lies in U(r(j + b + 1))")
							regroup := innerStep.Conjuncts(
								innerStep.Have(
									"the powers regroup around f·u and g·u",
									"monoid_pow(M.mul, M.one, f, a) * (f * u) = monoid_pow(M.mul, M.one, f, suc(a)) * u ∧ "+
										"monoid_pow(M.mul, M.one, g, suc(b)) * (f * u) = f * (monoid_pow(M.mul, M.one, g, suc(b)) * u) ∧ "+
										"monoid_pow(M.mul, M.one, g, b) * (g * u) = monoid_pow(M.mul, M.one, g, suc(b)) * u ∧ "+
										"monoid_pow(M.mul, M.one, f, suc(a)) * (g * u) = g * (monoid_pow(M.mul, M.one, f, suc(a)) * u)",
									Simp(Fwd(comm_monoid.MonoidPowDef)),
									ByArith(M, fIn, gIn, parts[1])),
								"f^a·(f·u) = f^(a+1)·u",
								"g^(b+1)·(f·u) = f·(g^(b+1)·u)",
								"g^b·(g·u) = g^(b+1)·u",
								"f^(a+1)·(g·u) = g·(f^(a+1)·u)")
							raised := innerStep.Have(
								"f·(g^(b+1)·u) and g·(f^(a+1)·u) lie one degree r higher",
								"f * (monoid_pow(M.mul, M.one, g, suc(b)) * u) ∈ U(r * (j + suc(b)) + r) ∧ "+
									"g * (monoid_pow(M.mul, M.one, f, suc(a)) * u) ∈ U(r * (j + suc(a)) + r)",
								By(
									raise.At(
										innerStep.TermAs[Nat]("r * (j + suc(b))"),
										innerStep.TermAs[A]("monoid_pow(M.mul, M.one, g, suc(b)) * u")),
									raise.At(
										innerStep.TermAs[Nat]("r * (j + suc(a))"),
										innerStep.TermAs[A]("monoid_pow(M.mul, M.one, f, suc(a)) * u")),
									parts[2],
									parts[3]))
							degrees := innerStep.Conjuncts(
								innerStep.Have(
									"the degrees agree one step up",
									"r * (j + suc(b)) + r = r * (j + 1 + suc(b)) ∧ "+
										"r * (j + suc(a)) = r * (j + 1 + a) ∧ "+
										"r * (j + suc(a)) + r = r * (j + 1 + suc(a)) ∧ "+
										"r * (j + suc(b)) = r * (j + 1 + b) ∧ "+
										"N ≤ j + 1",
									ByArith(parts[0])),
								"r(j + b + 1) + r = r(j + 1 + b + 1)",
								"r(j + a + 1) = r(j + 1 + a)",
								"r(j + a + 1) + r = r(j + 1 + a + 1)",
								"r(j + b + 1) = r(j + 1 + b)",
								"j + 1 is past N")
							next := innerStep.TermAs[Nat]("j + 1")
							fu := innerStep.Have(
								"f·u lies in U(r(j + 1)), by the hypothesis for a at j + 1",
								"f * u ∈ U(r * (j + 1))",
								By(
									outer.At(innerStep.TermAs[Nat]("suc(b)"), next, innerStep.TermAs[A]("f * u")),
									regroup[0],
									regroup[1],
									raised,
									degrees[0],
									degrees[1],
									degrees[4],
									parts[1],
									parts[2],
									fIn,
									comm_ring.MulIn.Read(field.RingOn.Read(M))))
							gu := innerStep.Have(
								"g·u lies in U(r(j + 1)), by the hypothesis for b at j + 1",
								"g * u ∈ U(r * (j + 1))",
								By(
									inner.At(next, innerStep.TermAs[A]("g * u")),
									regroup[2],
									regroup[3],
									raised,
									degrees[2],
									degrees[3],
									degrees[4],
									parts[1],
									parts[3],
									gIn,
									comm_ring.MulIn.Read(field.RingOn.Read(M))))
							innerStep.Show(
								"so u lies in U(r·j), one step down from j ≥ N",
								By(descend.At(j, u), parts[0], parts[1], fu, gu))
						})
				})
		}),
})}

// SectionsAreForms — a function in the chart of F and in tʲ times the
// chart of G is, from some j on, the value of a form of degree r·j over
// F(x)^j: such a y has y·F(x)^a and z·G(x)^b values of forms for y = tʲ·z,
// so u = y·F(x)ʲ = z·G(x)ʲ has F(x)^a·u and G(x)^b·u values of forms of
// degrees r(j + a) and r(j + b), and TwoMultipliersDescend brings u down to
// degree r·j one step at a time, each step the dimension count of
// MultipliersIntoSubspace at three consecutive degrees; conversely
// H(x)/F(x)ʲ = tʲ·H(x)/G(x)ʲ lies in both.
var SectionsAreForms = sectionsAreFormsThm{family.Add(registry.ProofEntry{
	Name: "SectionsAreForms",
	Key:  "prop_ab3e7244fa09b8d3",
	Reading: "The bound is N₁ + N₂, past the linear range of the Hilbert function and the bound " +
		"of CoprimeValuesGenerate; below it the meet can be larger than the forms give, since a " +
		"curve need not be projectively normal in low degree (a smooth rational quartic in P³ has a " +
		"fifth section of degree one). The inclusion of the forms over F(x)ʲ holds at every j; the " +
		"other is the dimension count h(r·j) + h(r(j + 2)) = 2·h(r(j + 1)), made at each degree the " +
		"exponents of F and G step down through. F(x) and G(x) nonzero make t and 1/t elements of K.",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). " +
			"∀k K:set(A). " +
			"∀n r:num. " +
			"∀E:set((num → num) → A). " +
			"∀x:(num → A). " +
			"∀F G:((num → num) → A).",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"smooth_projective_equation_curve(M, k, n, E)",
			"subfield(M, K)",
			"«genericPoint»(x)",
			"homogeneous_polynomial(«hilbertCoefficients», n, r, F)",
			"homogeneous_polynomial(«hilbertCoefficients», n, r, G)",
			"0 < r",
			"«at»(F) ≠ M.zero",
			"«at»(G) ≠ M.zero",
			"«noCommonZero»",
		},
		Conclusion: "∃N:num. ∀j:num. N ≤ j ⇒ «chart»(F) ∩ «scaled»(j) = «formsOver»(j)",
		Abbrev: Abbrev{
			{Name: "values", Text: "λd:num. " +
				"    image(«at», {P:((num → num) → A) | homogeneous_polynomial(«hilbertCoefficients», n, d, P)})"},
			{Name: "vectors", Text: "restrict_module(regular_module(field_ring(M)))"},
			{Name: "dim", Text: "module_dim(«hilbertCoefficients»)"},
		},
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			k, K *Expr[Set[A]],
			n, r *Expr[Nat],
			E *Expr[Set[Fun[Fun[Nat, Nat], A]]],
			x *Arrow[Nat, A],
			F, G *Arrow[Fun[Nat, Nat], A],
			given Fact,
		) {
			hyp := a.Conjuncts(
				given,
				"M is algebraically closed",
				"the equations define a smooth projective curve",
				"K is a subfield of M",
				"x is a point of the curve over K",
				"K is generated over k by the coordinates of x",
				"a form vanishes at x exactly when it lies in the ideal",
				"F is a form of degree r",
				"so is G",
				"r is positive",
				"F does not vanish at x",
				"nor does G",
				"F and G have no common zero on the curve")
			closed, curve, subfieldBig, formF, formG := hyp[0], hyp[1], hyp[2], hyp[6], hyp[7]
			positive, fNonzero, gNonzero, coprime := hyp[8], hyp[9], hyp[10], hyp[11]
			genericParts := hyp[3:6]
			fieldM := a.TermAs[FieldOps[A]]("M")
			scalars := a.TermAs[module_record.RingOps[A]]("«hilbertCoefficients»")
			at := a.TermAs[Fun[Fun[Fun[Nat, Nat], A], A]]("«at»")
			values := a.TermAs[Fun[Nat, Set[A]]]("«values»")
			f := a.TermAs[A]("«at»(F)")
			g := a.TermAs[A]("«at»(G)")
			subfieldK := a.Have(
				"k is a subfield of M",
				"subfield(M, k)",
				By(projective_curve.CurveConstantsSubfield.Read(curve)))
			_, _, _, slope := a.Unpack3As[Nat, Nat, Nat](
				projective_curve.CurveHilbertEventuallyLinear.Read(curve), "c", "e", "N₁")
			linear := a.Conjuncts(
				slope,
				"the slope e is positive",
				"from N₁ on, h(d) + c = e·d + 1")
			coordinatesInK := a.Have(
				"the coordinates of x up to n lie in K",
				"∀i:num. i ≤ n ⇒ x(i) ∈ K",
				By(genericParts[0], projective_curve.PointCoordinatesIn))
			KInM := a.Have(
				"K lies in M",
				"K ⊆ M.carrier",
				By(subfieldBig, field.SubfieldSubset.At(fieldM, K)))
			coordinates := a.Have(
				"the coordinates of x up to n lie in M",
				"∀i:num. i ≤ n ⇒ x(i) ∈ M.carrier",
				BySets(coordinatesInK, KInM))
			evaluation := a.Have(
				"evaluation at x is a ring homomorphism",
				"ring_homomorphism(«polynomials», field_ring(M), «at»)",
				By(At(homogeneous_polynomial.EvaluationRingHom, fieldM, k, n, x), M, subfieldK, coordinates))
			ring := a.Have(
				"k is a commutative ring under M's operations",
				"comm_ring_on(«hilbertCoefficients»)",
				By(subfieldK, field.SubfieldCommRing.Read(M).At(k)))
			valuesInM := a.Have(
				"the values of forms lie in M",
				"∀d:num. «values»(d) ⊆ M.carrier",
				Derive(func(b *Argument) {
					b.FixAs[Nat]("d")
					inK := b.Conjuncts(
						GroupPremises(
							subfieldK,
							subfieldBig,
							genericParts[0],
							genericParts[1],
							genericParts[2],
							Read(projective_curve.FormValuesSubspace, M).At(k, K, n, b.TermAs[Nat]("d"), E, x)),
						"they are a subspace",
						"inside K",
						"finite-dimensional",
						"of dimension h(d)")
					b.Show(
						"and K lies in M",
						BySets(inK[1], KInM))
				}))
			multipliersIn := a.Have(
				"F(x) and G(x) lie in M",
				"«at»(F) ∈ M.carrier ∧ «at»(G) ∈ M.carrier",
				By(
					homogeneous_polynomial.FormPolynomial.Read(formF),
					homogeneous_polynomial.FormPolynomial.Read(formG),
					ring_homomorphism.MapIn.Read(evaluation)))
			multipliersParts := a.Conjuncts(
				multipliersIn,
				"F(x) lies in M",
				"so does G(x)")
			raise := a.Have(
				"F(x)·v and G(x)·v are values of forms of degree d + r when v is one of degree d",
				"∀d:num. ∀v:A. v ∈ «values»(d) ⇒ «at»(F) * v ∈ «values»(d + r) ∧ «at»(G) * v ∈ «values»(d + r)",
				Derive(func(b *Argument) {
					d := b.FixAs[Nat]("d")
					v := b.FixAs[A]("v")
					vIn := b.Assume()
					_, form := b.UnpackAs[Fun[Fun[Nat, Nat], A]](b.Have(
						"v is the value at x of a form P of degree d",
						"∃P:((num → num) → A). v = «at»(P) ∧ homogeneous_polynomial(«hilbertCoefficients», n, d, P)",
						By(
							vIn,
							set_basic.InImage.At(
								at,
								b.TermAs[Set[Fun[Fun[Nat, Nat], A]]](
									"{P:((num → num) → A) | homogeneous_polynomial(«hilbertCoefficients», n, d, P)}"),
								v))),
						"P")
					P := b.TermAs[Fun[Fun[Nat, Nat], A]]("P")
					formParts := b.Conjuncts(
						form,
						"v = P(x)",
						"P is a form of degree d")
					products := b.Have(
						"P·F and P·G are forms of degree d + r",
						"homogeneous_polynomial(«hilbertCoefficients», "+
							"    n, "+
							"    d + r, "+
							"    polynomial_algebra_mul(«hilbertCoefficients», P, F)) ∧ "+
							"homogeneous_polynomial(«hilbertCoefficients», "+
							"    n, "+
							"    d + r, "+
							"    polynomial_algebra_mul(«hilbertCoefficients», P, G))",
						By(
							At(homogeneous_polynomial.FormProduct, scalars, n, d, r, P, F),
							At(homogeneous_polynomial.FormProduct, scalars, n, d, r, P, G),
							ring,
							formParts[1],
							formF,
							formG))
					productValues := b.Conjuncts(
						b.Have(
							"their values are P(x)·F(x) and P(x)·G(x)",
							"«at»(polynomial_algebra_mul(«hilbertCoefficients», P, F)) = «at»(P) * «at»(F) ∧ "+
								"«at»(polynomial_algebra_mul(«hilbertCoefficients», P, G)) = «at»(P) * «at»(G) ∧ "+
								"«at»(P) ∈ M.carrier",
							By(
								homogeneous_polynomial.FormPolynomial.Read(formParts[1]),
								homogeneous_polynomial.FormPolynomial.Read(formF),
								homogeneous_polynomial.FormPolynomial.Read(formG),
								ring_homomorphism.MapMul.Read(evaluation).AsFact().At(P, F),
								ring_homomorphism.MapMul.Read(evaluation).AsFact().At(P, G),
								ring_homomorphism.MapIn.Read(evaluation))),
						"P·F has the value P(x)·F(x)",
						"P·G has the value P(x)·G(x)",
						"P(x) lies in M")
					swapped := b.Conjuncts(
						b.Have(
							"so F(x)·v and G(x)·v are those values",
							"«at»(F) * v = «at»(polynomial_algebra_mul(«hilbertCoefficients», P, F)) ∧ "+
								"«at»(G) * v = «at»(polynomial_algebra_mul(«hilbertCoefficients», P, G))",
							formParts[0].Rw(),
							productValues[0].Rw(),
							productValues[1].Rw(),
							ByArith(M, productValues[2], multipliersIn)),
						"F(x)·v is the value of P·F",
						"G(x)·v is the value of P·G")
					raised := b.TermAs[Set[Fun[Fun[Nat, Nat], A]]](
						"{P:((num → num) → A) | homogeneous_polynomial(«hilbertCoefficients», n, d + r, P)}")
					b.Show(
						"values of forms of degree d + r",
						swapped[0].Rw(),
						swapped[1].Rw(),
						By(
							products,
							set_image.FunInImage.At(
								at, raised, b.TermAs[Fun[Fun[Nat, Nat], A]]("polynomial_algebra_mul(«hilbertCoefficients», P, F)")),
							set_image.FunInImage.At(
								at,
								raised,
								b.TermAs[Fun[Fun[Nat, Nat], A]]("polynomial_algebra_mul(«hilbertCoefficients», P, G)"))))
				}))
			_, generate := a.UnpackAs[Nat](
				GroupPremises(
					closed,
					curve,
					subfieldBig,
					genericParts[0],
					formF,
					formG,
					coprime,
					projective_form_pair.CoprimeValuesGenerate.Read(M).At(k, K, n, r, E, x, F, G)),
				"N₂")
			descend := a.Have(
				"from N₁ + N₂ on, v lies in the values of degree r·i "+
					"once F(x)·v and G(x)·v lie in those of degree r(i + 1)",
				Statement{
					Binders: "∀i:num. ∀v:A.",
					Hypotheses: []string{
						"N₁ + N₂ ≤ i",
						"v ∈ M.carrier",
						"«at»(F) * v ∈ «values»(r * (i + 1))",
						"«at»(G) * v ∈ «values»(r * (i + 1))",
					},
					Conclusion: "v ∈ «values»(r * i)",
				},
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]("i")
					v := b.FixAs[A]("v")
					assumed := b.Conjuncts(
						b.Assume(),
						"i is past N₁ + N₂",
						"v lies in M",
						"F(x)·v lies in the values of degree r(i + 1)",
						"so does G(x)·v")
					degrees := b.Conjuncts(
						b.Have(
							"the degrees r·i, r(i + 1), r(i + 2) are past the bounds, each r more than the last",
							"N₁ ≤ r * i ∧ "+
								"N₂ ≤ r * (i + 1) ∧ "+
								"r * i + r = r * (i + 1) ∧ "+
								"r * (i + 1) + r = r * (i + 2) ∧ "+
								"N₁ ≤ r * (i + 1) ∧ "+
								"N₁ ≤ r * (i + 2)",
							ByArith(positive, assumed[0], nat_order.LessEqSelfMul.At(i, r))),
						"r·i is past N₁",
						"r(i + 1) is past N₂",
						"r(i + 1) = r·i + r",
						"r(i + 2) = r(i + 1) + r",
						"r(i + 1) is past N₁",
						"so is r(i + 2)")
					low := GroupPremises(
						subfieldK,
						subfieldBig,
						genericParts[0],
						genericParts[1],
						genericParts[2],
						Read(projective_curve.FormValuesSubspace, M).At(k, K, n, b.TermAs[Nat]("r * i"), E, x))
					middle := GroupPremises(
						subfieldK,
						subfieldBig,
						genericParts[0],
						genericParts[1],
						genericParts[2],
						Read(projective_curve.FormValuesSubspace, M).At(k, K, n, b.TermAs[Nat]("r * (i + 1)"), E, x))
					high := GroupPremises(
						subfieldK,
						subfieldBig,
						genericParts[0],
						genericParts[1],
						genericParts[2],
						Read(projective_curve.FormValuesSubspace, M).At(k, K, n, b.TermAs[Nat]("r * (i + 2)"), E, x))
					dims := b.Have(
						"h being linear there, h(r·i) + h(r(i + 2)) = 2 h(r(i + 1))",
						"«dim»(«vectors»(«values»(r * i))) + «dim»(«vectors»(«values»(r * (i + 2)))) = "+
							"«dim»(«vectors»(«values»(r * (i + 1)))) + «dim»(«vectors»(«values»(r * (i + 1))))",
						ByArith(
							low,
							middle,
							high,
							linear[1].At(b.TermAs[Nat]("r * i")),
							linear[1].At(b.TermAs[Nat]("r * (i + 1)")),
							linear[1].At(b.TermAs[Nat]("r * (i + 2)")),
							degrees[0],
							degrees[4],
							degrees[5]))
					closures := b.Have(
						"F(x) and G(x) carry the values of degree r·i into "+
							"those of degree r(i + 1), and those into degree r(i + 2)",
						"(∀w:A. "+
							"    w ∈ «values»(r * i) ⇒ "+
							"    «at»(F) * w ∈ «values»(r * (i + 1)) ∧ «at»(G) * w ∈ «values»(r * (i + 1))) ∧ "+
							"(∀w:A. "+
							"    w ∈ «values»(r * (i + 1)) ⇒ "+
							"    «at»(F) * w ∈ «values»(r * (i + 2)) ∧ «at»(G) * w ∈ «values»(r * (i + 2)))",
						degrees[3].RwRev(),
						degrees[2].RwRev(),
						By(raise))
					generated := b.Have(
						"and the values of degree r(i + 2) are F(x)·p + G(x)·q with p, q of degree r(i + 1)",
						Statement{
							Binders: "∀z:A.",
							Hypotheses: []string{
								"z ∈ «values»(r * (i + 2))",
							},
							Conclusion: "∃p q:A. " +
								"    p ∈ «values»(r * (i + 1)) ∧ q ∈ «values»(r * (i + 1)) ∧ z = «at»(F) * p + «at»(G) * q",
						},
						degrees[3].RwRev(),
						By(generate, degrees[1]))
					b.Show(
						"so the dimension count of MultipliersIntoSubspace puts v in the values of degree r·i",
						By(
							At(
								MultipliersIntoSubspace,
								fieldM,
								k,
								b.TermAs[Set[A]]("«values»(r * i)"),
								b.TermAs[Set[A]]("«values»(r * (i + 1))"),
								b.TermAs[Set[A]]("«values»(r * (i + 2))"),
								f,
								g,
								v),
							M,
							subfieldK,
							low,
							middle,
							high,
							multipliersIn,
							fNonzero,
							closures,
							generated,
							dims,
							assumed[1],
							assumed[2],
							assumed[3]))
				}))
			gInverse := a.Have(
				"1/G(x) lies in M",
				"M.inv(«at»(G)) ∈ M.carrier",
				By(M, multipliersParts[1], field.InvIn))
			fInverse := a.Have(
				"1/F(x) lies in M",
				"M.inv(«at»(F)) ∈ M.carrier",
				By(M, multipliersParts[0], field.InvIn))
			inverses := a.Conjuncts(
				a.Have(
					"F(x) and G(x), nonzero, are invertible",
					"M.inv(«at»(F)) * «at»(F) = M.one ∧ M.inv(«at»(G)) * «at»(G) = M.one",
					By(
						field.MulLeftInverseOn.Read(M).AsFact().At(f),
						field.MulLeftInverseOn.Read(M).AsFact().At(g),
						multipliersIn,
						fNonzero,
						gNonzero)),
				"1/F(x)·F(x) = 1",
				"1/G(x)·G(x) = 1")
			ratioIn := a.Conjuncts(
				a.Have(
					"t = G(x)/F(x) and 1/t = F(x)/G(x) lie in M",
					"«parameter» ∈ M.carrier ∧ «at»(F) * M.inv(«at»(G)) ∈ M.carrier",
					By(multipliersIn, gInverse, fInverse, comm_ring.MulIn.Read(field.RingOn.Read(M)))),
				"t lies in M",
				"so does 1/t")
			ratioEq := a.Conjuncts(
				a.Have(
					"t·F(x) = G(x), (1/t)·G(x) = F(x) and t·(1/t) = 1",
					"«parameter» * «at»(F) = «at»(G) ∧ "+
						"«at»(F) * M.inv(«at»(G)) * «at»(G) = «at»(F) ∧ "+
						"«parameter» * («at»(F) * M.inv(«at»(G))) = M.one",
					ByArith(
						M,
						multipliersIn,
						gInverse,
						fInverse,
						Scaled(g, inverses[0]),
						Scaled(f, inverses[1]),
						Scaled(a.TermAs[A]("«at»(G) * M.inv(«at»(G))"), inverses[0]),
						inverses[1])),
				"t·F(x) = G(x)",
				"(1/t)·G(x) = F(x)",
				"t·(1/t) = 1")
			a.Take(a.TermAs[Nat]("N₁ + N₂"))
			a.Show(
				"from N₁ + N₂ on, the meet of the chart of F with tʲ "+
					"times the chart of G is the forms of degree r·j over F(x)ʲ",
				Derive(func(b *Argument) {
					j := b.FixAs[Nat]("j")
					past := b.Assume()
					t := b.TermAs[A]("«parameter»")
					s := b.TermAs[A]("«at»(F) * M.inv(«at»(G))")
					monoid := comm_ring.MulMonoidOn.Read(field.RingOn.Read(M))
					powers := b.Have(
						"so tʲ·F(x)ʲ = G(x)ʲ, (1/t)ʲ·G(x)ʲ = F(x)ʲ and tʲ·(1/t)ʲ = 1",
						"monoid_pow(M.mul, M.one, «parameter», j) * monoid_pow(M.mul, M.one, «at»(F), j) = "+
							"monoid_pow(M.mul, M.one, «at»(G), j) ∧ "+
							"monoid_pow(M.mul, M.one, «at»(F) * M.inv(«at»(G)), j) * monoid_pow(M.mul, M.one, «at»(G), j) = "+
							"monoid_pow(M.mul, M.one, «at»(F), j) ∧ "+
							"monoid_pow(M.mul, M.one, «parameter», j) * "+
							"monoid_pow(M.mul, M.one, «at»(F) * M.inv(«at»(G)), j) = "+
							"M.one",
						By(
							ratioIn[0],
							ratioIn[1],
							ratioEq[0],
							ratioEq[1],
							ratioEq[2],
							multipliersIn,
							comm_monoid.MulPowOn.Read(monoid).AsFact().At(t, f, j),
							comm_monoid.MulPowOn.Read(monoid).AsFact().At(s, g, j),
							comm_monoid.MulPowOn.Read(monoid).AsFact().At(t, s, j),
							comm_monoid.IdentityPowOn.Read(monoid).At(j)))
					powerParts := b.Conjuncts(
						powers,
						"tʲ·F(x)ʲ = G(x)ʲ",
						"(1/t)ʲ·G(x)ʲ = F(x)ʲ",
						"tʲ·(1/t)ʲ = 1")
					powersIn := b.Have(
						"the powers of F(x), G(x), t and 1/t lie in M",
						"monoid_pow(M.mul, M.one, «at»(F), j) ∈ M.carrier ∧ "+
							"monoid_pow(M.mul, M.one, «at»(G), j) ∈ M.carrier ∧ "+
							"monoid_pow(M.mul, M.one, «parameter», j) ∈ M.carrier ∧ "+
							"monoid_pow(M.mul, M.one, «at»(F) * M.inv(«at»(G)), j) ∈ M.carrier",
						By(multipliersIn, ratioIn[0], ratioIn[1], comm_monoid.PowIn.Read(monoid)))
					forward := b.Have(
						"a member of both is the value of a form of degree r·j over F(x)ʲ",
						"∀y:A. y ∈ «chart»(F) ∩ «scaled»(j) ⇒ y ∈ «formsOver»(j)",
						Derive(func(c *Argument) {
							y := c.FixAs[A]("y")
							both := c.Conjuncts(
								c.Have(
									"y lies in both",
									"y ∈ «chart»(F) ∧ y ∈ «scaled»(j)",
									BySets(c.Assume())),
								"y lies in the chart of F",
								"y lies in tʲ times the chart of G")
							inChartF := c.Conjuncts(
								both[0],
								"y lies in K",
								"y·F(x)^a is the value of a form of degree r·a")
							aExp, _, repF := c.Unpack2As[Nat, Fun[Fun[Nat, Nat], A]](inChartF[1], "a", "P")
							P := c.TermAs[Fun[Fun[Nat, Nat], A]]("P")
							repFParts := c.Conjuncts(
								repF,
								"P is a form of degree r·a",
								"y·F(x)^a = P(x)")
							_, scaledRep := c.UnpackAs[A](c.Have(
								"y is tʲ·z for z in the chart of G",
								"∃z:A. y = monoid_pow(M.mul, M.one, «parameter», j) * z ∧ z ∈ «chart»(G)",
								By(
									both[1],
									set_basic.InImage.At(
										c.TermAs[Fun[A, A]]("M.mul(monoid_pow(M.mul, M.one, «parameter», j))"),
										c.TermAs[Set[A]]("«chart»(G)"),
										y))), "z")
							scaledParts := c.Conjuncts(
								scaledRep,
								"y = tʲ·z",
								"z lies in the chart of G")
							inChartG := c.Conjuncts(
								scaledParts[1],
								"z lies in K",
								"z·G(x)^b is the value of a form of degree r·b")
							bExp, _, repG := c.Unpack2As[Nat, Fun[Fun[Nat, Nat], A]](inChartG[1], "b", "Q")
							Q := c.TermAs[Fun[Fun[Nat, Nat], A]]("Q")
							repGParts := c.Conjuncts(
								repG,
								"Q is a form of degree r·b",
								"z·G(x)^b = Q(x)")
							members := c.Have(
								"y and z lie in M",
								"y ∈ M.carrier ∧ z ∈ M.carrier",
								BySets(inChartF[0], inChartG[0], KInM))
							u := c.TermAs[A]("y * monoid_pow(M.mul, M.one, «at»(F), j)")
							pValue := c.TermAs[A]("«at»(P)")
							qValue := c.TermAs[A]("«at»(Q)")
							pIn := c.Have(
								"P(x) is a value of degree r·a",
								"«at»(P) ∈ «values»(r * a)",
								By(
									repFParts[0],
									set_image.FunInImage.At(
										at,
										c.TermAs[Set[Fun[Fun[Nat, Nat], A]]](
											"{P:((num → num) → A) | homogeneous_polynomial(«hilbertCoefficients», n, r * a, P)}"),
										P)))
							qIn := c.Have(
								"Q(x) is a value of degree r·b",
								"«at»(Q) ∈ «values»(r * b)",
								By(
									repGParts[0],
									set_image.FunInImage.At(
										at,
										c.TermAs[Set[Fun[Fun[Nat, Nat], A]]](
											"{P:((num → num) → A) | homogeneous_polynomial(«hilbertCoefficients», n, r * b, P)}"),
										Q)))
							shiftedP := c.Have(
								"F(x)ʲ·P(x) is a value of degree r·a + r·j",
								"monoid_pow(M.mul, M.one, «at»(F), j) * «at»(P) ∈ «values»(r * a + r * j)",
								By(
									At(PowerShiftsGrade, fieldM, values, f, pValue, r, c.TermAs[Nat]("r * a"), j),
									M,
									multipliersParts[0],
									valuesInM,
									raise,
									pIn))
							shiftedQ := c.Have(
								"G(x)ʲ·Q(x) is a value of degree r·b + r·j",
								"monoid_pow(M.mul, M.one, «at»(G), j) * «at»(Q) ∈ «values»(r * b + r * j)",
								By(
									At(PowerShiftsGrade, fieldM, values, g, qValue, r, c.TermAs[Nat]("r * b"), j),
									M,
									multipliersParts[1],
									valuesInM,
									raise,
									qIn))
							pqInM := c.Have(
								"P(x) and Q(x) lie in M",
								"«at»(P) ∈ M.carrier ∧ «at»(Q) ∈ M.carrier",
								By(
									homogeneous_polynomial.FormPolynomial.Read(repFParts[0]),
									homogeneous_polynomial.FormPolynomial.Read(repGParts[0]),
									ring_homomorphism.MapIn.Read(evaluation)))
							fSide := c.Have(
								"F(x)^a·u = F(x)ʲ·P(x) for u = y·F(x)ʲ",
								"monoid_pow(M.mul, M.one, «at»(F), a) * (y * monoid_pow(M.mul, M.one, «at»(F), j)) = "+
									"monoid_pow(M.mul, M.one, «at»(F), j) * «at»(P)",
								ByArith(
									M,
									members,
									multipliersIn,
									pqInM,
									Scaled(c.TermAs[A]("monoid_pow(M.mul, M.one, «at»(F), j)"), repFParts[1])))
							gSide := c.Have(
								"G(x)^b·u = G(x)ʲ·Q(x), u being z·G(x)ʲ as well",
								"monoid_pow(M.mul, M.one, «at»(G), b) * (y * monoid_pow(M.mul, M.one, «at»(F), j)) = "+
									"monoid_pow(M.mul, M.one, «at»(G), j) * «at»(Q)",
								ByArith(
									M,
									members,
									multipliersIn,
									pqInM,
									ratioIn[0],
									Scaled(
										c.TermAs[A]("monoid_pow(M.mul, M.one, «at»(G), b) * monoid_pow(M.mul, M.one, «at»(F), j)"),
										scaledParts[0]),
									Scaled(c.TermAs[A]("monoid_pow(M.mul, M.one, «at»(G), b) * z"), powerParts[0]),
									Scaled(c.TermAs[A]("monoid_pow(M.mul, M.one, «at»(G), j)"), repGParts[1])))
							degrees := c.Conjuncts(
								c.Have(
									"r·a + r·j = r(j + a) and r·b + r·j = r(j + b)",
									"r * a + r * j = r * (j + a) ∧ r * b + r * j = r * (j + b)",
									ByArith()),
								"r·a + r·j = r(j + a)",
								"r·b + r·j = r(j + b)")
							fPower := c.Have(
								"so F(x)^a·u is a value of degree r(j + a)",
								"monoid_pow(M.mul, M.one, «at»(F), a) * (y * monoid_pow(M.mul, M.one, «at»(F), j)) ∈ "+
									"«values»(r * (j + a))",
								degrees[0].RwRev(),
								fSide.Rw(),
								By(shiftedP))
							gPower := c.Have(
								"and G(x)^b·u one of degree r(j + b)",
								"monoid_pow(M.mul, M.one, «at»(G), b) * (y * monoid_pow(M.mul, M.one, «at»(F), j)) ∈ "+
									"«values»(r * (j + b))",
								degrees[1].RwRev(),
								gSide.Rw(),
								By(shiftedQ))
							uM := c.Have(
								"u lies in M",
								"y * monoid_pow(M.mul, M.one, «at»(F), j) ∈ M.carrier",
								By(members, powersIn, comm_ring.MulIn.Read(field.RingOn.Read(M))))
							uIn := c.Have(
								"so u is a value of degree r·j, by TwoMultipliersDescend",
								"y * monoid_pow(M.mul, M.one, «at»(F), j) ∈ «values»(r * j)",
								By(
									At(TwoMultipliersDescend, fieldM, values, f, g, r, c.TermAs[Nat]("N₁ + N₂"), aExp, bExp, j, u),
									M,
									multipliersIn,
									raise,
									descend,
									past,
									uM,
									fPower,
									gPower))
							_, formH := c.UnpackAs[Fun[Fun[Nat, Nat], A]](c.Have(
								"u is the value at x of a form H of degree r·j",
								"∃H:((num → num) → A). "+
									"    y * monoid_pow(M.mul, M.one, «at»(F), j) = «at»(H) ∧ "+
									"    homogeneous_polynomial(«hilbertCoefficients», n, r * j, H)",
								By(
									uIn,
									set_basic.InImage.At(
										at,
										c.TermAs[Set[Fun[Fun[Nat, Nat], A]]](
											"{P:((num → num) → A) | homogeneous_polynomial(«hilbertCoefficients», n, r * j, P)}"),
										u))),
								"H")
							c.Show(
								"so y is H(x)/F(x)ʲ, a form of degree r·j over F(x)ʲ",
								BySets(inChartF[0], formH))
						}))
					backward := b.Have(
						"the value of a form of degree r·j over F(x)ʲ lies in both",
						"∀y:A. y ∈ «formsOver»(j) ⇒ y ∈ «chart»(F) ∩ «scaled»(j)",
						Derive(func(c *Argument) {
							y := c.FixAs[A]("y")
							inForms := c.Conjuncts(
								c.Assume(),
								"y lies in K",
								"y·F(x)ʲ is the value of a form of degree r·j")
							_, repH := c.UnpackAs[Fun[Fun[Nat, Nat], A]](inForms[1], "H")
							repHParts := c.Conjuncts(
								repH,
								"H is a form of degree r·j",
								"y·F(x)ʲ = H(x)")
							chartF := c.Have(
								"y lies in the chart of F, with exponent j and the form H",
								"y ∈ «chart»(F)",
								BySets(inForms[0], repH))
							w := c.TermAs[A]("monoid_pow(M.mul, M.one, «at»(F) * M.inv(«at»(G)), j) * y")
							sPower := c.TermAs[A]("monoid_pow(M.mul, M.one, «at»(F) * M.inv(«at»(G)), j)")
							raisedForms := c.TermAs[Set[Fun[Fun[Nat, Nat], A]]](
								"{P:((num → num) → A) | homogeneous_polynomial(«hilbertCoefficients», n, r, P)}")
							valuesK := c.Have(
								"F(x) and G(x) lie in K, as values of forms of degree r",
								"«at»(F) ∈ K ∧ «at»(G) ∈ K",
								By(
									c.Have(
										"the values of forms of degree r lie in K",
										"«values»(r) ⊆ K",
										By(
											At(projective_curve.FormValuesSubspace, fieldM, k, K, n, c.TermAs[Nat]("r"), E, x),
											M,
											subfieldK,
											subfieldBig,
											genericParts[0],
											genericParts[1],
											genericParts[2])),
									set_basic.SubsetDef,
									set_image.FunInImage.At(at, raisedForms, F),
									set_image.FunInImage.At(at, raisedForms, G),
									formF,
									formG))
							valuesKParts := c.Conjuncts(
								valuesK,
								"F(x) lies in K",
								"so does G(x)")
							sInK := c.Have(
								"so does 1/t = F(x)/G(x)",
								"«at»(F) * M.inv(«at»(G)) ∈ K",
								By(
									subfieldBig,
									valuesKParts[0],
									field.SubfieldInv.At(fieldM, K, g),
									valuesKParts[1],
									field.SubfieldMul.At(fieldM, K, f, c.TermAs[A]("M.inv(«at»(G))"))))
							wInK := c.Have(
								"and w = (1/t)ʲ·y",
								"monoid_pow(M.mul, M.one, «at»(F) * M.inv(«at»(G)), j) * y ∈ K",
								By(
									M,
									subfieldBig,
									sInK,
									inForms[0],
									field.SubfieldPowerIn.At(fieldM, K, s, j),
									field.SubfieldMul.At(fieldM, K, sPower, y)))
							yIn := c.Have(
								"y lies in M",
								"y ∈ M.carrier",
								BySets(inForms[0], KInM))
							hValue := c.Have(
								"H(x) lies in M",
								"«at»(H) ∈ M.carrier",
								By(
									homogeneous_polynomial.FormPolynomial.Read(repHParts[0]),
									ring_homomorphism.MapIn.Read(evaluation)))
							wForm := c.Have(
								"w·G(x)ʲ = (1/t)ʲ·G(x)ʲ·y = F(x)ʲ·y = H(x)",
								"monoid_pow(M.mul, M.one, «at»(F) * M.inv(«at»(G)), j) * "+
									"y * "+
									"monoid_pow(M.mul, M.one, «at»(G), j) = "+
									"«at»(H)",
								ByArith(M, yIn, powersIn, hValue, Scaled(y, powerParts[1]), repHParts[1]))
							wChart := c.Have(
								"so w lies in the chart of G, with exponent j and the form H",
								"monoid_pow(M.mul, M.one, «at»(F) * M.inv(«at»(G)), j) * y ∈ «chart»(G)",
								BySets(wInK, repHParts[0], wForm))
							yScaled := c.Have(
								"and y = tʲ·w lies in tʲ times the chart of G",
								"y ∈ «scaled»(j)",
								By(
									c.Have(
										"y is tʲ times a member of the chart of G",
										"∃z:A. y = monoid_pow(M.mul, M.one, «parameter», j) * z ∧ z ∈ «chart»(G)",
										Derive(func(d *Argument) {
											d.Take(w)
											d.Show(
												"tʲ·(1/t)ʲ·y = y",
												SplitConj(
													Case(
														"tʲ·w is y",
														ByArith(M, yIn, powersIn, Scaled(y, powerParts[2]))),
													Case(
														"w lies in the chart of G",
														By(wChart))))
										})),
									set_basic.InImage.At(
										c.TermAs[Fun[A, A]]("M.mul(monoid_pow(M.mul, M.one, «parameter», j))"),
										c.TermAs[Set[A]]("«chart»(G)"),
										y)))
							c.Show(
								"so y lies in both",
								BySets(chartF, yScaled))
						}))
					pointwise := b.Have(
						"so a point lies in both exactly when it is the value of a form of degree r·j over F(x)ʲ",
						"∀y:A. y ∈ «chart»(F) ∩ «scaled»(j) ⇔ y ∈ «formsOver»(j)",
						By(forward, backward))
					b.Show(
						"and the two sets are equal",
						By(pointwise, set_basic.Extension))
				}))
		}),
})}
