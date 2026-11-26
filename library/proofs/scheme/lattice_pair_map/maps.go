// maps.go — maps of lattice pairs: a map of lattice pairs is linear on the
// ambient of its source, over R and over any subring of R, and carries the
// ambient and the chart sum of M into those of N, and maps of lattice pairs
// compose; the maps of one lattice pair into another are a module over any
// subring of both charts; an isomorphism carries the ambient of M onto that
// of N, carries H⁰ and H¹ isomorphically and keeps the dimensions and χ;
// isomorphisms compose and invert, and an isomorphism of the target pairs
// acts on the maps by postcomposition. No statement about an isomorphism
// assumes its target a lattice pair: lattice_pair(M) and an isomorphism f
// out of M force N to be one.

package lattice_pair_map

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/quotient_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/function_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/hom_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/linear_independence"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/scheme/lattice_pair"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// ---------------------------------------------------------------------------
// The maps of lattice pairs
// ---------------------------------------------------------------------------

// PairMapHomomorphism — a map of lattice pairs is an R-linear map of the
// ambient of its source into W: the maps of lattice pairs are drawn from
// the R-linear maps of the ambient that are zero off it.
var PairMapHomomorphism = pairMapHomomorphismThm{family.Add(registry.ProofEntry{
	Name: "PairMapHomomorphism",
	Key:  "prop_3aa2fa6e3e8a5eba",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀V:module_ops(A, B). " +
			"∀W:module_ops(A, C). " +
			"∀M:prod(set(B), set(B)). " +
			"∀N:prod(set(C), set(C)). " +
			"∀f:(B → C).",
		Hypotheses: []string{
			"f ∈ lattice_pair_maps(R, V, M, W, N)",
		},
		Conclusion: "module_homomorphism(R, restrict_module(V, lattice_pair_ambient(R, V, M)), W, f)",
	},
		func(a *Argument, R *Expr[RingOps[A]], V *Expr[ModuleOps[A, B]], W *Expr[ModuleOps[A, C]],
			M *Expr[Prod[Set[B], Set[B]]], N *Expr[Prod[Set[C], Set[C]]], f *Arrow[B, C], pairMap Fact) {
			P := a.TermAs[ModuleOps[A, B]]("restrict_module(V, lattice_pair_ambient(R, V, M))")
			inHomSet := a.Have(
				"f is one of the R-linear maps of the ambient of M into W, zero off it",
				"f ∈ hom_set(R, restrict_module(V, lattice_pair_ambient(R, V, M)), W)",
				BySets(pairMap, LatticePairMapsDef))
			a.Show(
				"so f is R-linear on the ambient",
				By(inHomSet, hom_module.InHomSet.At(R, P, W, f)))
		}),
})}

// PairMapLinear — a map of lattice pairs is linear, on the ambient of its
// source, over any subring S of R: it is R-linear there
// (PairMapHomomorphism), and a homomorphism over R is one over S.
var PairMapLinear = pairMapLinearThm{family.Add(registry.ProofEntry{
	Name: "PairMapLinear",
	Key:  "prop_df9e9f38d5e3443d",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀S:set(A). " +
			"∀V:module_ops(A, B). " +
			"∀W:module_ops(A, C). " +
			"∀M:prod(set(B), set(B)). " +
			"∀N:prod(set(C), set(C)). " +
			"∀f:(B → C).",
		Hypotheses: []string{
			"subring(R, S)",
			"f ∈ lattice_pair_maps(R, V, M, W, N)",
		},
		Conclusion: "module_homomorphism(restrict_ring(R, S), " +
			"    restrict_module(V, lattice_pair_ambient(R, V, M)), " +
			"    W, " +
			"    f)",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			S *Expr[Set[A]],
			V *Expr[ModuleOps[A, B]],
			W *Expr[ModuleOps[A, C]],
			M *Expr[Prod[Set[B], Set[B]]],
			N *Expr[Prod[Set[C], Set[C]]],
			f *Arrow[B, C],
			given Fact,
		) {
			hypotheses := a.Conjuncts(
				given,
				"S is a subring of R",
				"f is a map of lattice pairs")
			subring, pairMap := hypotheses[0], hypotheses[1]
			linear := a.Have(
				"f is R-linear on the ambient of M",
				"module_homomorphism(R, restrict_module(V, lattice_pair_ambient(R, V, M)), W, f)",
				By(PairMapHomomorphism.At(R, V, W, M, N, f), pairMap))
			a.Show(
				"so it is linear over the subring S",
				By(module_homomorphism.HomRestrictScalars.Read(linear).At(S), subring))
		}),
})}

// PairMapsLinearSpace — the maps of a lattice pair M into a lattice pair
// N form a submodule of the module of R-linear maps from the ambient of M
// over any subring S of both charts, and so Hom(M, N) is a module over S:
// the R-linear maps are a module over R, so over S, and the zero map, a
// sum, a negative and an S-multiple carry each chart of M into the chart
// of N, a module over its chart ring, which holds S.
var PairMapsLinearSpace = pairMapsLinearSpaceThm{family.Add(registry.ProofEntry{
	Name: "PairMapsLinearSpace",
	Key:  "prop_f9fd0a4fe2187876",
	Reading: "Not an R-submodule: an R-multiple of a map need not carry chart 0 of M into " +
		"chart 0 of N, which is closed under A₀ only. S ⊆ A₀ ∩ A₁ is what keeps both charts; at S " +
		"= k the maps are a vector space over k, and Hom(M, N)'s dimension is its dimension there.",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀A₀ A₁:set(A). " +
			"∀S:set(A). " +
			"∀V:module_ops(A, B). " +
			"∀W:module_ops(A, C). " +
			"∀M:prod(set(B), set(B)). " +
			"∀N:prod(set(C), set(C)).",
		Hypotheses: []string{
			"subring(R, S)",
			"S ⊆ A₀",
			"S ⊆ A₁",
			"«waSource»",
			"lattice_pair(R, A₀, A₁, W, N)",
		},
		Conclusion: "submodule(restrict_ring(R, S), «waMapsModule», lattice_pair_maps(R, V, M, W, N)) ∧ " +
			"module_on(restrict_ring(R, S), lattice_pair_hom(R, V, M, W, N))",
		Abbrev: Abbrev{
			// The R-linear maps from the ambient of M into W, zero off the ambient: the carrier of the module of those maps.
			{Name: "waHomSet", Text: "hom_set(R, restrict_module(V, lattice_pair_ambient(R, V, M)), W)"},
		},
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			A0, A1 *Expr[Set[A]],
			S *Expr[Set[A]],
			V *Expr[ModuleOps[A, B]],
			W *Expr[ModuleOps[A, C]],
			M *Expr[Prod[Set[B], Set[B]]],
			N *Expr[Prod[Set[C], Set[C]]],
			given Fact,
		) {
			hypotheses := a.Conjuncts(
				given,
				"S is a subring of R",
				"S lies in chart 0",
				"and in chart 1",
				"M is a lattice pair in V",
				"N is a lattice pair in W")
			subring, inChart0, inChart1 := hypotheses[0], hypotheses[1], hypotheses[2]
			pairM := a.Unfolded(hypotheses[3], lattice_pair.LatticePairDef)
			pairN := a.Unfolded(hypotheses[4], lattice_pair.LatticePairDef)

			moduleV := a.Have(
				"V is a module over R",
				"module_on(R, V)",
				By(pairM))
			ambient := a.Conjuncts(
				GroupPremises(hypotheses[3], lattice_pair.AmbientContains.At(R, A0, A1, V, M)),
				"the ambient of M is a submodule of V over R",
				"holding chart 0",
				"and chart 1")[0]
			overR := a.Have(
				"the R-linear maps from the ambient, a module over R, into W are a module over R",
				"module_on(R, «waMapsModule»)",
				By(pairN, ambient, submodule.SubmoduleModuleOn.Read(moduleV), hom_module.HomSetModuleOn))
			overS := a.Have(
				"so they are a module over the subring S",
				"module_on(restrict_ring(R, S), «waMapsModule»)",
				By(overR, subring, module.ModuleRestrictScalars))
			additive := module.AddGroupOn.Read(overS)

			maps := a.Have(
				"a map of lattice pairs is an R-linear map carrying "+
					"chart 0 of M into chart 0 of N and chart 1 into chart 1",
				"∀f:(B → C). "+
					"    f ∈ lattice_pair_maps(R, V, M, W, N) ⇔ "+
					"    f ∈ «waHomSet» ∧ image(f, fst(M)) ⊆ fst(N) ∧ image(f, snd(M)) ⊆ snd(N)",
				Simp(Fwd(LatticePairMapsDef)),
				BySets())
			chart0N := a.Have(
				"chart 0 of N is a submodule of W over A₀",
				"submodule(restrict_ring(R, A₀), W, fst(N))",
				By(pairN))
			chart1N := a.Have(
				"chart 1 of N is a submodule of W over A₁",
				"submodule(restrict_ring(R, A₁), W, snd(N))",
				By(pairN))
			fstM, sndM := a.TermAs[Set[B]]("fst(M)"), a.TermAs[Set[B]]("snd(M)")
			fstN, sndN := a.TermAs[Set[C]]("fst(N)"), a.TermAs[Set[C]]("snd(N)")

			// For a submodule Y of W over a subring T, the maps carrying a set X
			// into Y are closed under the pointwise operations and scaling by T:
			// read point by point, image(f, X) ⊆ Y says f(x) ∈ Y for x ∈ X.
			zeroInto := a.Have(
				"the zero map sends X to W.zero, which lies in Y",
				Statement{
					Binders: "∀T:set(A). ∀X:set(B). ∀Y:set(C).",
					Hypotheses: []string{
						"submodule(restrict_ring(R, T), W, Y)",
					},
					Conclusion: "image(fun_zero(W.zero), X) ⊆ Y",
				},
				Derive(func(b *Argument) {
					b.FixAs[Set[A]]()
					b.FixAs[Set[B]]()
					b.FixAs[Set[C]]()
					sub := b.Assume()
					b.Show(
						"Y holds W.zero",
						Simp(Fwd(set_image.ImageSubsetIff), Fwd(function_module.FunZeroDef)),
						By(submodule.SubmoduleZero.Read(sub)))
				}))
			sumInto := a.Have(
				"f + g sends x to f(x) + g(x), a sum of two points of Y",
				Statement{
					Binders: "∀T:set(A). ∀X:set(B). ∀Y:set(C). ∀f g:(B → C).",
					Hypotheses: []string{
						"submodule(restrict_ring(R, T), W, Y)",
						"image(f, X) ⊆ Y",
						"image(g, X) ⊆ Y",
					},
					Conclusion: "image(fun_add(W.add, f, g), X) ⊆ Y",
				},
				Derive(func(b *Argument) {
					b.FixAs[Set[A]]()
					b.FixAs[Set[B]]()
					b.FixAs[Set[C]]()
					b.FixAs[Fun[B, C]]()
					b.FixAs[Fun[B, C]]()
					hypotheses := b.Conjuncts(
						b.Assume(),
						"Y is a submodule over T",
						"f carries X into Y",
						"so does g")
					fInto := b.Simplified(hypotheses[1], Fwd(set_image.ImageSubsetIff))
					gInto := b.Simplified(hypotheses[2], Fwd(set_image.ImageSubsetIff))
					b.Show(
						"Y is closed under the sum",
						Simp(Fwd(set_image.ImageSubsetIff), Fwd(function_module.FunAddDef)),
						By(submodule.SubmoduleAdd.Read(hypotheses[0]), fInto, gInto))
				}))
			negativeInto := a.Have(
				"-f sends x to -f(x), a point of Y",
				Statement{
					Binders: "∀T:set(A). ∀X:set(B). ∀Y:set(C). ∀f:(B → C).",
					Hypotheses: []string{
						"submodule(restrict_ring(R, T), W, Y)",
						"image(f, X) ⊆ Y",
					},
					Conclusion: "image(fun_neg(W.neg, f), X) ⊆ Y",
				},
				Derive(func(b *Argument) {
					b.FixAs[Set[A]]()
					b.FixAs[Set[B]]()
					b.FixAs[Set[C]]()
					b.FixAs[Fun[B, C]]()
					hypotheses := b.Conjuncts(
						b.Assume(),
						"Y is a submodule over T",
						"f carries X into Y")
					fInto := b.Simplified(hypotheses[1], Fwd(set_image.ImageSubsetIff))
					b.Show(
						"Y is closed under the negative",
						Simp(Fwd(set_image.ImageSubsetIff), Fwd(function_module.FunNegDef)),
						By(submodule.SubmoduleNeg.Read(hypotheses[0]), fInto))
				}))
			scaledInto := a.Have(
				"c • f sends x to c • f(x), a point of Y for c in T",
				Statement{
					Binders: "∀T:set(A). ∀X:set(B). ∀Y:set(C). ∀c:A. ∀f:(B → C).",
					Hypotheses: []string{
						"submodule(restrict_ring(R, T), W, Y)",
						"c ∈ T",
						"image(f, X) ⊆ Y",
					},
					Conclusion: "image(fun_smul(W.smul, c, f), X) ⊆ Y",
				},
				Derive(func(b *Argument) {
					b.FixAs[Set[A]]()
					b.FixAs[Set[B]]()
					b.FixAs[Set[C]]()
					b.FixAs[A]()
					b.FixAs[Fun[B, C]]()
					hypotheses := b.Conjuncts(
						b.Assume(),
						"Y is a submodule over T",
						"c lies in T",
						"f carries X into Y")
					fInto := b.Simplified(hypotheses[2], Fwd(set_image.ImageSubsetIff))
					b.Show(
						"Y is closed under scaling by T",
						Simp(Fwd(set_image.ImageSubsetIff), Fwd(function_module.FunSmulDef)),
						By(submodule.SubmoduleSmul.Read(hypotheses[0]), hypotheses[1], fInto))
				}))

			zero := a.TermAs[Fun[B, C]]("fun_zero(W.zero)")
			zeroIn := a.Have(
				"the zero map is a map of lattice pairs: the zero "+
					"of the R-linear maps, sending each chart to W.zero",
				"fun_zero(W.zero) ∈ lattice_pair_maps(R, V, M, W, N)",
				By(
					maps.At(zero),
					group.OneIn.Read(additive),
					zeroInto.At(A0, fstM, fstN),
					zeroInto.At(A1, sndM, sndN),
					chart0N,
					chart1N))
			addIn := a.Have(
				"a sum of maps of lattice pairs is one",
				Statement{
					Binders: "∀f g:(B → C).",
					Hypotheses: []string{
						"f ∈ lattice_pair_maps(R, V, M, W, N)",
						"g ∈ lattice_pair_maps(R, V, M, W, N)",
					},
					Conclusion: "fun_add(W.add, f, g) ∈ lattice_pair_maps(R, V, M, W, N)",
				},
				Derive(func(b *Argument) {
					f, g := b.FixAs[Fun[B, C]](), b.FixAs[Fun[B, C]]()
					both := b.Conjuncts(
						b.Assume(),
						"f is a map of lattice pairs",
						"so is g")
					fIs := b.Have(
						"f is R-linear and carries each chart into the chart of N",
						"f ∈ «waHomSet» ∧ image(f, fst(M)) ⊆ fst(N) ∧ image(f, snd(M)) ⊆ snd(N)",
						By(maps.At(f), both[0]))
					gIs := b.Have(
						"and so does g",
						"g ∈ «waHomSet» ∧ image(g, fst(M)) ⊆ fst(N) ∧ image(g, snd(M)) ⊆ snd(N)",
						By(maps.At(g), both[1]))
					b.Show(
						"so does f + g",
						By(
							maps.At(b.TermAs[Fun[B, C]]("fun_add(W.add, f, g)")),
							fIs,
							gIs,
							group.MulIn.Read(additive),
							sumInto.At(A0, fstM, fstN, f, g),
							sumInto.At(A1, sndM, sndN, f, g),
							chart0N,
							chart1N))
				}))
			negIn := a.Have(
				"the negative of a map of lattice pairs is one",
				Statement{
					Binders: "∀f:(B → C).",
					Hypotheses: []string{
						"f ∈ lattice_pair_maps(R, V, M, W, N)",
					},
					Conclusion: "fun_neg(W.neg, f) ∈ lattice_pair_maps(R, V, M, W, N)",
				},
				Derive(func(b *Argument) {
					f := b.FixAs[Fun[B, C]]()
					fIn := b.Assume()
					fIs := b.Have(
						"f is R-linear and carries each chart into the chart of N",
						"f ∈ «waHomSet» ∧ image(f, fst(M)) ⊆ fst(N) ∧ image(f, snd(M)) ⊆ snd(N)",
						By(maps.At(f), fIn))
					b.Show(
						"so does -f",
						By(
							maps.At(b.TermAs[Fun[B, C]]("fun_neg(W.neg, f)")),
							fIs,
							group.InvIn.Read(additive),
							negativeInto.At(A0, fstM, fstN, f),
							negativeInto.At(A1, sndM, sndN, f),
							chart0N,
							chart1N))
				}))
			smulIn := a.Have(
				"an S-multiple of a map of lattice pairs is one",
				Statement{
					Binders: "∀c:A. ∀f:(B → C).",
					Hypotheses: []string{
						"c ∈ S",
						"f ∈ lattice_pair_maps(R, V, M, W, N)",
					},
					Conclusion: "fun_smul(W.smul, c, f) ∈ lattice_pair_maps(R, V, M, W, N)",
				},
				Derive(func(b *Argument) {
					c := b.FixAs[A]()
					f := b.FixAs[Fun[B, C]]()
					hypotheses := b.Conjuncts(
						b.Assume(),
						"c is a scalar of S",
						"f is a map of lattice pairs")
					inCharts := b.Conjuncts(
						b.Have(
							"c lies in both charts, S lying in each",
							"c ∈ A₀ ∧ c ∈ A₁",
							BySets(hypotheses[0], inChart0, inChart1)),
						"c lies in chart 0",
						"and in chart 1")
					fIs := b.Have(
						"f is R-linear and carries each chart into the chart of N",
						"f ∈ «waHomSet» ∧ image(f, fst(M)) ⊆ fst(N) ∧ image(f, snd(M)) ⊆ snd(N)",
						By(maps.At(f), hypotheses[1]))
					b.Show(
						"so does c • f, c lying in both chart rings",
						By(
							maps.At(b.TermAs[Fun[B, C]]("fun_smul(W.smul, c, f)")),
							hypotheses[0],
							fIs,
							module.SmulIn.Read(overS),
							scaledInto.At(A0, fstM, fstN, c, f),
							scaledInto.At(A1, sndM, sndN, c, f),
							inCharts[0],
							inCharts[1],
							chart0N,
							chart1N))
				}))

			inHomSet := a.Have(
				"every map of lattice pairs is one of the R-linear maps of the ambient, zero off it",
				"∀f:(B → C). f ∈ lattice_pair_maps(R, V, M, W, N) ⇒ f ∈ «waHomSet»",
				a.ForEach(func(f *Expr[Fun[B, C]]) Action { return By(maps.At(f)) }))
			subgroup := a.Have(
				"so the maps of lattice pairs are a subgroup of the R-linear maps under the pointwise addition",
				"subgroup(mk_group(fun_add(W.add), fun_zero(W.zero), fun_neg(W.neg), «waHomSet»), "+
					"    lattice_pair_maps(R, V, M, W, N))",
				By(inHomSet, zeroIn, addIn, negIn, group.SubgroupDef, set_basic.SubsetDef))
			mapsModule := a.TermAs[ModuleOps[A, Fun[B, C]]]("«waMapsModule»")
			isSubmodule := a.Have(
				"closed under scaling by S, they are a submodule over S",
				"submodule(restrict_ring(R, S), «waMapsModule», lattice_pair_maps(R, V, M, W, N))",
				By(
					subgroup,
					smulIn,
					submodule.SubmoduleDef.At(
						a.TermAs[RingOps[A]]("restrict_ring(R, S)"),
						mapsModule,
						a.TermAs[Set[Fun[B, C]]]("lattice_pair_maps(R, V, M, W, N)")),
					module_record.ModuleAdditiveGroupDef.At(mapsModule)))
			a.Show(
				"a submodule over S is a module over S on its own, and Hom(M, N) is that module",
				Unfold(LatticePairHomDef),
				By(isSubmodule, submodule.SubmoduleModuleOn.Read(overS)))
		}),
})}

// PairMapAmbient — a map of lattice pairs carries the ambient of M into
// the ambient of N: inside the ambient of M chart 0 spans it, f carries a
// span onto the span of the image, and the image of chart 0 of M lies in
// chart 0 of N, whose span is the ambient of N.
var PairMapAmbient = pairMapAmbientThm{family.Add(registry.ProofEntry{
	Name: "PairMapAmbient",
	Key:  "prop_2b635ff7765817b6",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀A₀ A₁:set(A). " +
			"∀V:module_ops(A, B). " +
			"∀W:module_ops(A, C). " +
			"∀M:prod(set(B), set(B)). " +
			"∀N:prod(set(C), set(C)). " +
			"∀f:(B → C).",
		Hypotheses: []string{
			"«waSource»",
			"f ∈ lattice_pair_maps(R, V, M, W, N)",
		},
		Conclusion: "image(f, lattice_pair_ambient(R, V, M)) ⊆ lattice_pair_ambient(R, W, N)",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			A0, A1 *Expr[Set[A]],
			V *Expr[ModuleOps[A, B]],
			W *Expr[ModuleOps[A, C]],
			M *Expr[Prod[Set[B], Set[B]]],
			N *Expr[Prod[Set[C], Set[C]]],
			f *Arrow[B, C],
			given Fact,
		) {
			hypotheses := a.Conjuncts(
				given,
				"M is a lattice pair",
				"f is a map of lattice pairs")
			pair, pairMap := hypotheses[0], hypotheses[1]
			ambM, fstM := a.TermAs[Set[B]]("lattice_pair_ambient(R, V, M)"), a.TermAs[Set[B]]("fst(M)")
			P := a.TermAs[ModuleOps[A, B]]("restrict_module(V, lattice_pair_ambient(R, V, M))")
			moduleV := a.Have(
				"V is an R-module",
				"module_on(R, V)",
				By(pair, lattice_pair.PairModuleOn))
			contains := a.Conjuncts(
				GroupPremises(hypotheses[0], lattice_pair.AmbientContains.At(R, A0, A1, V, M)),
				"the ambient of M is an R-submodule of V",
				"holding chart 0",
				"and chart 1")
			chart0 := a.Have(
				"f carries chart 0 of M into chart 0 of N",
				"image(f, fst(M)) ⊆ fst(N)",
				BySets(pairMap, LatticePairMapsDef))
			onto := a.Have(
				"f carries the ambient of M onto the span of the image of chart 0",
				"image(f, lattice_pair_ambient(R, V, M)) = module_span(R, W, image(f, fst(M)))",
				CalcEq(
					Leg(
						a.TermAs[Set[C]](
							"image(f, module_span(R, restrict_module(V, lattice_pair_ambient(R, V, M)), fst(M)))"),
						"inside the ambient of M, chart 0 spans it",
						By(
							lattice_pair.LatticePairAmbientDef.At(R, V, M),
							linear_independence.SpanRestrict.Read(moduleV).At(ambM, fstM),
							contains[0],
							contains[1])),
					FinalLeg(
						"f carries a span onto the span of the image",
						By(
							linear_independence.HomSpan.At(R, P, W, f, fstM),
							PairMapHomomorphism.At(R, V, W, M, N, f),
							pairMap,
							contains[1])),
				))
			a.Show(
				"which lies in the span of chart 0 of N, the ambient of N",
				onto.Rw(),
				Simp(Fwd(lattice_pair.LatticePairAmbientDef)),
				By(
					chart0,
					submodule.SpanMono.At(R, W, a.TermAs[Set[C]]("image(f, fst(M))"), a.TermAs[Set[C]]("fst(N)"))))
		}),
})}

// PairMapChartSum — a map of lattice pairs carries the chart sum M₀ + M₁
// into the chart sum N₀ + N₁: a member x = m₀ + m₁ goes, f being additive
// on the ambient of M, which holds both charts, to f(m₀) + f(m₁), and f
// carries each chart of M into the chart of N.
var PairMapChartSum = pairMapChartSumThm{family.Add(registry.ProofEntry{
	Name: "PairMapChartSum",
	Key:  "prop_13c4d8857a226ea7",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀A₀ A₁:set(A). " +
			"∀V:module_ops(A, B). " +
			"∀W:module_ops(A, C). " +
			"∀M:prod(set(B), set(B)). " +
			"∀N:prod(set(C), set(C)). " +
			"∀f:(B → C). " +
			"∀x:B.",
		Hypotheses: []string{
			"«waSource»",
			"f ∈ lattice_pair_maps(R, V, M, W, N)",
			"x ∈ set_mul(V.add, fst(M), snd(M))",
		},
		Conclusion: "f(x) ∈ set_mul(W.add, fst(N), snd(N))",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			A0, A1 *Expr[Set[A]],
			V *Expr[ModuleOps[A, B]],
			W *Expr[ModuleOps[A, C]],
			M *Expr[Prod[Set[B], Set[B]]],
			N *Expr[Prod[Set[C], Set[C]]],
			f *Arrow[B, C],
			x *Expr[B],
			given Fact,
		) {
			hypotheses := a.Conjuncts(
				given,
				"M is a lattice pair",
				"f is a map of lattice pairs",
				"x lies in M₀ + M₁")
			pair, pairMap, xIn := hypotheses[0], hypotheses[1], hypotheses[2]
			fstM, sndM := a.TermAs[Set[B]]("fst(M)"), a.TermAs[Set[B]]("snd(M)")
			m0, m1, split := a.Obtain2As[B, B](
				"x is m₀ + m₁ with m₀ in M₀ and m₁ in M₁",
				"∃m₀ m₁:B. m₀ ∈ fst(M) ∧ m₁ ∈ snd(M) ∧ x = V.add(m₀, m₁)",
				By(xIn, quotient_group.InSetMul.At(a.TermAs[Op[B]]("V.add"), fstM, sndM, x)))
			pieces := a.Conjuncts(
				split,
				"m₀ lies in M₀",
				"m₁ lies in M₁",
				"x is m₀ + m₁")

			// f is R-linear on the ambient of M, which holds both charts, so it
			// splits over x = m₀ + m₁.
			linear := a.Have(
				"f is R-linear on the ambient of M",
				"module_homomorphism(R, restrict_module(V, lattice_pair_ambient(R, V, M)), W, f)",
				By(PairMapHomomorphism.At(R, V, W, M, N, f), pairMap))
			inAmbient := a.Conjuncts(
				a.Have(
					"m₀ and m₁ lie in the ambient, which holds both charts",
					"m₀ ∈ lattice_pair_ambient(R, V, M) ∧ m₁ ∈ lattice_pair_ambient(R, V, M)",
					BySets(pair, pieces[0], pieces[1], lattice_pair.AmbientContains.At(R, A0, A1, V, M))),
				"m₀ lies in the ambient",
				"m₁ lies in the ambient")
			sum := a.Have(
				"f is additive on the ambient, so f(x) = f(m₀) + f(m₁)",
				"f(x) = W.add(f(m₀), f(m₁))",
				By(
					Normalized,
					pieces[2],
					module_homomorphism.HomAdd.Read(linear).At(
						proof.MemberOf(m0, inAmbient[0]), proof.MemberOf(m1, inAmbient[1]))))

			// f(m₀) lies in N₀ and f(m₁) in N₁, so f(x) lies in N₀ + N₁.
			charts := a.Conjuncts(
				a.Have(
					"f carries each chart of M into that of N",
					"image(f, fst(M)) ⊆ fst(N) ∧ image(f, snd(M)) ⊆ snd(N)",
					BySets(pairMap, LatticePairMapsDef)),
				"f carries M₀ into N₀",
				"and M₁ into N₁")
			into0 := a.Simplified(charts[0], Fwd(set_image.ImageSubsetIff))
			into1 := a.Simplified(charts[1], Fwd(set_image.ImageSubsetIff))
			a.Show(
				"so f(x) is f(m₀) + f(m₁), a sum of a member of N₀ and one of N₁",
				Simp(Fwd(quotient_group.InSetMul)),
				Derive(func(b *Argument) {
					b.Take(f.Apply(m0))
					b.Take(f.Apply(m1))
					b.Show(
						"f(m₀) lies in N₀, f(m₁) in N₁, and the two sum to f(x)",
						By(into0.At(m0), into1.At(m1), pieces[0], pieces[1], sum))
				}))
		}),
})}

// PairMapCompose — maps of lattice pairs compose: g ∘ f is R-linear on the
// ambient of M, f carrying it into the ambient of N, where g is R-linear;
// it is zero off the ambient of M, where f is zero and g keeps zero; and it
// carries each chart of M through the chart of N into that of Q.
var PairMapCompose = pairMapComposeThm{family.Add(registry.ProofEntry{
	Name: "PairMapCompose",
	Key:  "prop_90d317d6e5e1d735",
	Reading: "lattice_pair(M) is load-bearing: with it the ambient of M is the R-span of " +
		"chart 0 inside V, so f, carrying chart 0 of M into chart 0 of N, carries the ambient " +
		"of M into the ambient of N, where g is R-linear (PairMapAmbient). N and Q need not " +
		"be lattice pairs: whatever pairs of sets they are, g ∘ f is a map of lattice pairs " +
		"from M to Q. g ∘ f keeps the maps' convention of being zero off the ambient of M: " +
		"there f is W.zero, which g, linear on the ambient of N, sends to X.zero.",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀A₀ A₁:set(A). " +
			"∀V:module_ops(A, B). " +
			"∀W:module_ops(A, C). " +
			"∀X:module_ops(A, D). " +
			"∀M:prod(set(B), set(B)). " +
			"∀N:prod(set(C), set(C)). " +
			"∀Q:prod(set(D), set(D)). " +
			"∀f:(B → C). " +
			"∀g:(C → D).",
		Hypotheses: []string{
			"«waSource»",
			"f ∈ lattice_pair_maps(R, V, M, W, N)",
			"g ∈ lattice_pair_maps(R, W, N, X, Q)",
		},
		Conclusion: "g ∘ f ∈ lattice_pair_maps(R, V, M, X, Q)",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			A0, A1 *Expr[Set[A]],
			V *Expr[ModuleOps[A, B]],
			W *Expr[ModuleOps[A, C]],
			X *Expr[ModuleOps[A, D]],
			M *Expr[Prod[Set[B], Set[B]]],
			N *Expr[Prod[Set[C], Set[C]]],
			Q *Expr[Prod[Set[D], Set[D]]],
			f *Arrow[B, C],
			g *Arrow[C, D],
			given Fact,
		) {
			hypotheses := a.Conjuncts(
				given,
				"M is a lattice pair",
				"f is a map of lattice pairs from M to N",
				"g is one from N to Q")
			fMap, gMap := hypotheses[1], hypotheses[2]
			P := a.TermAs[ModuleOps[A, B]]("restrict_module(V, lattice_pair_ambient(R, V, M))")
			onAmbientN := a.TermAs[ModuleOps[A, C]]("restrict_module(W, lattice_pair_ambient(R, W, N))")
			fstN, sndN := a.TermAs[Set[C]]("fst(N)"), a.TermAs[Set[C]]("snd(N)")
			fstQ, sndQ := a.TermAs[Set[D]]("fst(Q)"), a.TermAs[Set[D]]("snd(Q)")

			// g ∘ f is R-linear on the ambient of M: f carries it into the
			// ambient of N, where g is R-linear.
			fLinear := a.Have(
				"f is R-linear on the ambient of M",
				"module_homomorphism(R, restrict_module(V, lattice_pair_ambient(R, V, M)), W, f)",
				By(PairMapHomomorphism.At(R, V, W, M, N, f), fMap))
			gLinear := a.Have(
				"g is R-linear on the ambient of N",
				"module_homomorphism(R, restrict_module(W, lattice_pair_ambient(R, W, N)), X, g)",
				By(PairMapHomomorphism.At(R, W, X, N, Q, g), gMap))
			into := a.Simplified(
				GroupPremises(hypotheses[0], hypotheses[1], PairMapAmbient.At(R, A0, A1, V, W, M, N, f)),
				Fwd(set_image.ImageSubsetIff))
			// N need not be a lattice pair, so its ambient is not known to be an
			// R-submodule of W and HomCorestrict does not apply: f is read into
			// the ambient of N through ModuleHomomorphismDef, that ambient a
			// module as the source of g.
			corestricted := a.Have(
				"so f is R-linear from the ambient of M to the ambient of N",
				"module_homomorphism(R, "+
					"    restrict_module(V, lattice_pair_ambient(R, V, M)), "+
					"    restrict_module(W, lattice_pair_ambient(R, W, N)), "+
					"    f)",
				By(
					module_homomorphism.ModuleHomomorphismDef.At(R, P, onAmbientN, f),
					module_homomorphism.HomSource.Read(fLinear),
					module_homomorphism.HomSource.Read(gLinear),
					into,
					module_homomorphism.HomAdd.Read(fLinear),
					module_homomorphism.HomSmul.Read(fLinear)))
			composite := a.Have(
				"so g ∘ f is R-linear on the ambient of M",
				"module_homomorphism(R, restrict_module(V, lattice_pair_ambient(R, V, M)), X, g ∘ f)",
				By(module_homomorphism.HomCompose.At(R, P, onAmbientN, X, f, g), corestricted, gLinear))

			// Off the ambient of M, f is W.zero, which g sends to X.zero.
			fHomSet := a.Have(
				"f is one of the R-linear maps of the ambient of M into W, zero off it",
				"f ∈ hom_set(R, restrict_module(V, lattice_pair_ambient(R, V, M)), W)",
				BySets(fMap, LatticePairMapsDef.At(R, V, M, W, N)))
			fZero := a.Have(
				"so f is zero off the ambient of M",
				"∀u:B. u ∉ lattice_pair_ambient(R, V, M) ⇒ f(u) = W.zero",
				By(hom_module.InHomSet.At(R, P, W, f), fHomSet))
			compositeZero := a.Have(
				"so g ∘ f is zero off the ambient of M",
				"∀u:B. u ∉ lattice_pair_ambient(R, V, M) ⇒ (g ∘ f)(u) = X.zero",
				Derive(func(b *Argument) {
					u := b.FixAs[B]()
					uOutside := b.Assume()
					b.Show(
						"(g ∘ f)(u) = g(f(u)) = g(W.zero) = X.zero",
						Simp(Fwd(functions.ComposeApply)),
						GroupPremises(uOutside, fZero.At(u)).Rw(),
						By(module_homomorphism.HomZero.At(R, onAmbientN, X, g), gLinear))
				}))

			// Each chart of M goes through the chart of N into that of Q.
			fCharts := a.Conjuncts(
				a.Have(
					"f carries each chart of M into that of N",
					"image(f, fst(M)) ⊆ fst(N) ∧ image(f, snd(M)) ⊆ snd(N)",
					BySets(fMap, LatticePairMapsDef.At(R, V, M, W, N))),
				"f carries M₀ into N₀",
				"and M₁ into N₁")
			gCharts := a.Conjuncts(
				a.Have(
					"g carries each chart of N into that of Q",
					"image(g, fst(N)) ⊆ fst(Q) ∧ image(g, snd(N)) ⊆ snd(Q)",
					BySets(gMap, LatticePairMapsDef.At(R, W, N, X, Q))),
				"g carries N₀ into Q₀",
				"and N₁ into Q₁")
			chart0 := a.Have(
				"so g ∘ f carries M₀ through N₀ into Q₀",
				"image(g ∘ f, fst(M)) ⊆ fst(Q)",
				Simp(Fwd(set_image.ImageCompose)),
				By(
					fCharts[0],
					gCharts[0],
					set_image.ImageSubset.At(g, a.TermAs[Set[C]]("image(f, fst(M))"), fstN),
					set_order.SubsetTrans.At(
						a.TermAs[Set[D]]("image(g, image(f, fst(M)))"), a.TermAs[Set[D]]("image(g, fst(N))"), fstQ)))
			chart1 := a.Have(
				"and M₁ through N₁ into Q₁",
				"image(g ∘ f, snd(M)) ⊆ snd(Q)",
				Simp(Fwd(set_image.ImageCompose)),
				By(
					fCharts[1],
					gCharts[1],
					set_image.ImageSubset.At(g, a.TermAs[Set[C]]("image(f, snd(M))"), sndN),
					set_order.SubsetTrans.At(
						a.TermAs[Set[D]]("image(g, image(f, snd(M)))"), a.TermAs[Set[D]]("image(g, snd(N))"), sndQ)))
			a.Show(
				"so g ∘ f is a map of lattice pairs from M to Q",
				Simp(Fwd(LatticePairMapsDef), Fwd(hom_module.InHomSet)),
				BySets(composite, compositeZero, chart0, chart1))
		}),
})}

// ---------------------------------------------------------------------------
// What an isomorphism keeps
// ---------------------------------------------------------------------------

// IsomorphismAmbient — an isomorphism of lattice pairs carries the ambient
// of M onto the ambient of N: inside the ambient of M chart 0 spans it, f
// carries a span onto the span of the image, and the image of chart 0 of M
// is chart 0 of N, whose span is the ambient of N.
var IsomorphismAmbient = isomorphismAmbientThm{family.Add(registry.ProofEntry{
	Name: "IsomorphismAmbient",
	Key:  "prop_9c818c1a56e6927c",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀A₀ A₁:set(A). " +
			"∀V:module_ops(A, B). " +
			"∀W:module_ops(A, C). " +
			"∀M:prod(set(B), set(B)). " +
			"∀N:prod(set(C), set(C)). " +
			"∀f:(B → C).",
		Hypotheses: []string{
			"«waSource»",
			"«waIsomorphism»",
		},
		Conclusion: "image(f, lattice_pair_ambient(R, V, M)) = lattice_pair_ambient(R, W, N)",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			A0, A1 *Expr[Set[A]],
			V *Expr[ModuleOps[A, B]],
			W *Expr[ModuleOps[A, C]],
			M *Expr[Prod[Set[B], Set[B]]],
			N *Expr[Prod[Set[C], Set[C]]],
			f *Arrow[B, C],
			given Fact,
		) {
			hypotheses := a.Conjuncts(
				given,
				"M is a lattice pair",
				"f is an isomorphism of lattice pairs")
			pair := hypotheses[0]
			iso := a.Conjuncts(
				a.Unfolded(hypotheses[1], LatticePairIsomorphismDef),
				"f is a map of lattice pairs",
				"one-to-one on the ambient of M",
				"onto chart 0 of N",
				"and onto chart 1")
			ambM, fstM := a.TermAs[Set[B]]("lattice_pair_ambient(R, V, M)"), a.TermAs[Set[B]]("fst(M)")
			P := a.TermAs[ModuleOps[A, B]]("restrict_module(V, lattice_pair_ambient(R, V, M))")
			moduleV := a.Have(
				"V is an R-module",
				"module_on(R, V)",
				By(pair, lattice_pair.PairModuleOn))
			contains := a.Conjuncts(
				GroupPremises(hypotheses[0], lattice_pair.AmbientContains.At(R, A0, A1, V, M)),
				"the ambient of M is an R-submodule of V",
				"holding chart 0",
				"and chart 1")
			a.Show(
				"the ambient of M is what chart 0 spans, which f carries onto what chart 0 of N spans",
				CalcEq(
					Leg(
						a.TermAs[Set[C]](
							"image(f, module_span(R, restrict_module(V, lattice_pair_ambient(R, V, M)), fst(M)))"),
						"inside the ambient of M, chart 0 spans it",
						By(
							lattice_pair.LatticePairAmbientDef.At(R, V, M),
							linear_independence.SpanRestrict.Read(moduleV).At(ambM, fstM),
							contains[0],
							contains[1])),
					Leg(
						a.TermAs[Set[C]]("module_span(R, W, image(f, fst(M)))"),
						"f carries a span onto the span of the image",
						By(
							linear_independence.HomSpan.At(R, P, W, f, fstM),
							PairMapHomomorphism.At(R, V, W, M, N, f),
							iso[0],
							contains[1])),
					Leg(
						a.TermAs[Set[C]]("module_span(R, W, fst(N))"),
						"f carries chart 0 of M onto chart 0 of N",
						By(Normalized, iso[2])),
					FinalLeg(
						"the span of chart 0 of N is its ambient",
						Cite(lattice_pair.LatticePairAmbientDef)),
				))
		}),
})}

// IsomorphismSameH0 — an isomorphism of lattice pairs restricts to an
// isomorphism of H⁰ over any subring of both charts: f is S-linear on the
// ambient of M, which holds H⁰(M), and one-to-one there, so it carries the
// meet of the charts onto the meet of their images.
var IsomorphismSameH0 = isomorphismSameH0Thm{family.Add(registry.ProofEntry{
	Name: "IsomorphismSameH0",
	Key:  "prop_a3169d91c1a224ee",
	Reading: "lattice_pair(M) is load-bearing twice: it puts chart 1 " +
		"as well as chart 0 inside the ambient (AmbientContains), where " +
		"f is one-to-one, and it makes H⁰(M) an S-submodule (H0Submodule).",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀A₀ A₁:set(A). " +
			"∀S:set(A). " +
			"∀V:module_ops(A, B). " +
			"∀W:module_ops(A, C). " +
			"∀M:prod(set(B), set(B)). " +
			"∀N:prod(set(C), set(C)). " +
			"∀f:(B → C).",
		Hypotheses: []string{
			"subring(R, S)",
			"S ⊆ A₀",
			"S ⊆ A₁",
			"«waSource»",
			"«waIsomorphism»",
		},
		Conclusion: "module_isomorphism(restrict_ring(R, S), " +
			"    lattice_pair_h0(V, M), " +
			"    lattice_pair_h0(W, N), " +
			"    f)",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			A0, A1 *Expr[Set[A]],
			S *Expr[Set[A]],
			V *Expr[ModuleOps[A, B]],
			W *Expr[ModuleOps[A, C]],
			M *Expr[Prod[Set[B], Set[B]]],
			N *Expr[Prod[Set[C], Set[C]]],
			f *Arrow[B, C],
			given Fact,
		) {
			hypotheses := a.Conjuncts(
				given,
				"S is a subring of R",
				"S lies in chart 0",
				"and in chart 1",
				"M is a lattice pair in V",
				"f is an isomorphism of lattice pairs")
			subring, inChart0, inChart1, pair := hypotheses[0], hypotheses[1], hypotheses[2], hypotheses[3]
			iso := a.Conjuncts(
				a.Unfolded(hypotheses[4], LatticePairIsomorphismDef),
				"f is a map of lattice pairs",
				"one-to-one on the ambient of M",
				"carrying chart 0 of M onto chart 0 of N",
				"and chart 1 onto chart 1")
			pairMap, oneToOne, onto0, onto1 := iso[0], iso[1], iso[2], iso[3]
			ringS := a.TermAs[RingOps[A]]("restrict_ring(R, S)")
			ambient := a.TermAs[Set[B]]("lattice_pair_ambient(R, V, M)")
			P := a.TermAs[ModuleOps[A, B]]("restrict_module(V, lattice_pair_ambient(R, V, M))")
			fstM, sndM := a.TermAs[Set[B]]("fst(M)"), a.TermAs[Set[B]]("snd(M)")
			meetM, meetN := a.TermAs[Set[B]]("fst(M) ∩ snd(M)"), a.TermAs[Set[C]]("fst(N) ∩ snd(N)")

			// f is S-linear on the ambient of M, and H⁰(M) is an S-submodule
			// of it: the ambient holds both charts, which are modules over
			// chart rings holding S.
			linear := a.Have(
				"f is S-linear on the ambient of M",
				"module_homomorphism(restrict_ring(R, S), restrict_module(V, lattice_pair_ambient(R, V, M)), W, f)",
				By(PairMapLinear.At(R, S, V, W, M, N, f), subring, pairMap))
			contains := a.Conjuncts(
				GroupPremises(hypotheses[3], lattice_pair.AmbientContains.At(R, A0, A1, V, M)),
				"the ambient of M is an R-submodule of V",
				"holding chart 0",
				"and chart 1")
			inAmbient := a.Have(
				"H⁰(M) = M₀ ∩ M₁ lies in the ambient, inside chart 0",
				"fst(M) ∩ snd(M) ⊆ lattice_pair_ambient(R, V, M)",
				By(
					contains[1],
					set_order.InterSubset.At(fstM, sndM),
					set_order.SubsetTrans.At(meetM, fstM, ambient)))
			h0 := a.Have(
				"H⁰(M) is an S-submodule of V, S lying in both charts",
				"submodule(restrict_ring(R, S), V, fst(M) ∩ snd(M))",
				By(lattice_pair.H0Submodule.At(R, A0, A1, S, V, M), pair, inChart0, inChart1))
			h0InAmbient := a.Have(
				"and so an S-submodule of the ambient",
				"submodule(restrict_ring(R, S), "+
					"    restrict_module(V, lattice_pair_ambient(R, V, M)), "+
					"    fst(M) ∩ snd(M))",
				By(h0, inAmbient, submodule.SubmoduleRestrict.At(ringS, V, ambient, meetM)))

			// One-to-one on the ambient, f carries the meet of the charts onto
			// the meet of their images, which are the charts of N.
			meet := a.Have(
				"f, one-to-one on a set holding both charts, carries their meet onto the meet of their images",
				"image(f, fst(M) ∩ snd(M)) = image(f, fst(M)) ∩ image(f, snd(M))",
				By(set_image.ImageInterInjOn.At(f, fstM, sndM, ambient), oneToOne, contains[1], contains[2]))
			onto := a.Have(
				"so f carries H⁰(M) onto H⁰(N)",
				"image(f, fst(M) ∩ snd(M)) = fst(N) ∩ snd(N)",
				By(Normalized, meet, onto0, onto1))
			h0N := a.Have(
				"H⁰(N), the image of an S-submodule, is an S-submodule of W",
				"submodule(restrict_ring(R, S), W, fst(N) ∩ snd(N))",
				onto.RwRev(),
				By(module_homomorphism.HomImageSubmodule.At(ringS, P, W, f, meetM), linear, h0InAmbient))
			into := a.Have(
				"f carries H⁰(M) into H⁰(N)",
				"∀u:B. u ∈ fst(M) ∩ snd(M) ⇒ f(u) ∈ fst(N) ∩ snd(N)",
				onto.RwRev(),
				Cite(set_image.FunInImage))

			// The restriction of f to H⁰(M) is S-linear into H⁰(N), one-to-one
			// and onto.
			sameModule := a.Have(
				"H⁰(M) inside the ambient carries the operations of V",
				"restrict_module(restrict_module(V, lattice_pair_ambient(R, V, M)), fst(M) ∩ snd(M)) = "+
					"restrict_module(V, fst(M) ∩ snd(M))",
				Unfold(module_record.RestrictModuleDef))
			restricted := a.Have(
				"so f restricts to an S-linear map of H⁰(M) into H⁰(N)",
				"module_homomorphism(restrict_ring(R, S), "+
					"    restrict_module(V, fst(M) ∩ snd(M)), "+
					"    restrict_module(W, fst(N) ∩ snd(N)), "+
					"    f)",
				sameModule.RwRev(),
				By(
					module_homomorphism.HomRestrict.At(ringS, P, W, f, meetM, meetN),
					linear,
					h0InAmbient,
					h0N,
					into))
			a.Show(
				"one-to-one on H⁰(M), which lies in the ambient, and onto H⁰(N), it is an isomorphism",
				Unfold(lattice_pair.LatticePairH0Def),
				By(
					module_homomorphism.ModuleIsomorphismDef.At(
						ringS,
						a.TermAs[ModuleOps[A, B]]("restrict_module(V, fst(M) ∩ snd(M))"),
						a.TermAs[ModuleOps[A, C]]("restrict_module(W, fst(N) ∩ snd(N))"),
						f),
					restricted,
					functions.InjectiveOnSubset.At(f, meetM, ambient),
					oneToOne,
					inAmbient,
					onto))
		}),
})}

// IsomorphismSameH1 — an isomorphism of lattice pairs induces, by taking
// images of cosets, an isomorphism of H¹ over any subring of both charts:
// over S, f is an isomorphism of the ambient of M onto that of N, and being
// additive and onto each chart it carries M₀ + M₁ onto N₀ + N₁, so it
// passes to the quotients (module_homomorphism.QuotientIsomorphism).
var IsomorphismSameH1 = isomorphismSameH1Thm{family.Add(registry.ProofEntry{
	Name:    "IsomorphismSameH1",
	Key:     "prop_a0868a95b7d75698",
	Reading: "S ⊆ A₁ is what makes M₀ + M₁ an S-submodule: chart 1 is a module over A₁ only.",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀A₀ A₁:set(A). " +
			"∀t s:A. " +
			"∀S:set(A). " +
			"∀V:module_ops(A, B). " +
			"∀W:module_ops(A, C). " +
			"∀M:prod(set(B), set(B)). " +
			"∀N:prod(set(C), set(C)). " +
			"∀f:(B → C).",
		Hypotheses: []string{
			"«waBiaffine»",
			"subring(R, S)",
			"S ⊆ A₀",
			"S ⊆ A₁",
			"«waSource»",
			"«waIsomorphism»",
		},
		Conclusion: "module_isomorphism(restrict_ring(R, S), " +
			"    lattice_pair_h1(R, V, M), " +
			"    lattice_pair_h1(R, W, N), " +
			"    λx:set(B). image(f, x))",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			A0, A1 *Expr[Set[A]],
			t, s *Expr[A],
			S *Expr[Set[A]],
			V *Expr[ModuleOps[A, B]],
			W *Expr[ModuleOps[A, C]],
			M *Expr[Prod[Set[B], Set[B]]],
			N *Expr[Prod[Set[C], Set[C]]],
			f *Arrow[B, C],
			given Fact,
		) {
			hypotheses := a.Conjuncts(
				given,
				"the datum is biaffine",
				"S is a subring of R",
				"S lies in chart 0",
				"and in chart 1",
				"M is a lattice pair in V",
				"f is an isomorphism of lattice pairs")
			datum, subring, inChart0, inChart1, pair, isomorphism :=
				hypotheses[0], hypotheses[1], hypotheses[2], hypotheses[3], hypotheses[4], hypotheses[5]
			iso := a.Conjuncts(
				a.Unfolded(isomorphism, LatticePairIsomorphismDef),
				"f is a map of lattice pairs",
				"one-to-one on the ambient of M",
				"onto chart 0 of N",
				"and onto chart 1")
			ringS := a.TermAs[RingOps[A]]("restrict_ring(R, S)")
			ambM, ambN :=
				a.TermAs[Set[B]]("lattice_pair_ambient(R, V, M)"), a.TermAs[Set[C]]("lattice_pair_ambient(R, W, N)")
			P := a.TermAs[ModuleOps[A, B]]("restrict_module(V, lattice_pair_ambient(R, V, M))")
			Q := a.TermAs[ModuleOps[A, C]]("restrict_module(W, lattice_pair_ambient(R, W, N))")
			sumM := a.TermAs[Set[B]]("set_mul(V.add, fst(M), snd(M))")

			// Over S, f is an isomorphism of the ambient of M onto that of N.
			linear := a.Have(
				"f is S-linear on the ambient of M",
				"module_homomorphism(restrict_ring(R, S), restrict_module(V, lattice_pair_ambient(R, V, M)), W, f)",
				By(PairMapLinear.At(R, S, V, W, M, N, f), subring, iso[0]))
			onto := a.Have(
				"f carries the ambient of M onto that of N",
				"image(f, lattice_pair_ambient(R, V, M)) = lattice_pair_ambient(R, W, N)",
				By(IsomorphismAmbient.At(R, A0, A1, V, W, M, N, f), pair, isomorphism))
			ambientN := a.Have(
				"the ambient of N, the image of that of M, is an S-submodule of W",
				"submodule(restrict_ring(R, S), W, lattice_pair_ambient(R, W, N))",
				onto.RwRev(),
				Cite(module_homomorphism.ImageSubmodule.Read(linear)))
			into := a.Have(
				"f carries the ambient of M into that of N",
				"∀u:B. u ∈ lattice_pair_ambient(R, V, M) ⇒ f(u) ∈ lattice_pair_ambient(R, W, N)",
				onto.RwRev(),
				Cite(set_image.FunInImage))
			ambients := a.Have(
				"so f is S-linear from the ambient of M to that of N",
				"module_homomorphism(restrict_ring(R, S), "+
					"    restrict_module(V, lattice_pair_ambient(R, V, M)), "+
					"    restrict_module(W, lattice_pair_ambient(R, W, N)), "+
					"    f)",
				By(module_homomorphism.HomCorestrict.At(ringS, P, W, f, ambN), linear, ambientN, into))
			isoS := a.Have(
				"one-to-one and onto, it is an isomorphism of the ambients over S",
				"module_isomorphism(restrict_ring(R, S), "+
					"    restrict_module(V, lattice_pair_ambient(R, V, M)), "+
					"    restrict_module(W, lattice_pair_ambient(R, W, N)), "+
					"    f)",
				By(module_homomorphism.ModuleIsomorphismDef, ambients, iso[1], onto))

			// M₀ + M₁ is an S-submodule of the ambient of M, and f carries it
			// onto N₀ + N₁.
			sumS := a.Have(
				"M₀ + M₁ is an S-submodule of V, S lying in both charts",
				"submodule(restrict_ring(R, S), V, set_mul(V.add, fst(M), snd(M)))",
				By(
					lattice_pair.PairOverSubring.At(R, A0, A1, t, s, S, V, M),
					datum,
					subring,
					inChart0,
					inChart1,
					pair))
			sumIn := a.Conjuncts(
				GroupPremises(hypotheses[4], lattice_pair.ChartSumInAmbient.At(R, A0, A1, V, M)),
				"M₀ + M₁ lies in the ambient of M",
				"and holds zero")[0]
			sumSub := a.Have(
				"so it is an S-submodule of the ambient",
				"submodule(restrict_ring(R, S), "+
					"    restrict_module(V, lattice_pair_ambient(R, V, M)), "+
					"    set_mul(V.add, fst(M), snd(M)))",
				By(submodule.SubmoduleRestrict.At(ringS, V, ambM, sumM), sumS, sumIn))
			contains := a.Conjuncts(
				GroupPremises(hypotheses[4], lattice_pair.AmbientContains.At(R, A0, A1, V, M)),
				"the ambient of M is an R-submodule of V",
				"holding chart 0",
				"and chart 1")
			additive := a.Have(
				"f is additive on a point of M₀ and one of M₁",
				"∀x y:B. x ∈ fst(M) ∧ y ∈ snd(M) ⇒ f(x + y) = f(x) + f(y)",
				By(module_homomorphism.HomAdd.Read(linear), contains[1], contains[2], set_basic.SubsetDef))
			into0 := a.Have(
				"f carries chart 0 of M into chart 0 of N",
				"∀x:B. x ∈ fst(M) ⇒ f(x) ∈ fst(N)",
				iso[2].RwRev(),
				Cite(set_image.FunInImage))
			into1 := a.Have(
				"and chart 1 into chart 1",
				"∀y:B. y ∈ snd(M) ⇒ f(y) ∈ snd(N)",
				iso[3].RwRev(),
				Cite(set_image.FunInImage))
			from0 := a.Have(
				"a point of chart 0 of N is the image of one of chart 0 of M",
				"∀p:C. p ∈ fst(N) ⇔ ∃x:B. x ∈ fst(M) ∧ p = f(x)",
				BySets(iso[2]))
			from1 := a.Have(
				"and a point of chart 1 of one of chart 1",
				"∀q:C. q ∈ snd(N) ⇔ ∃y:B. y ∈ snd(M) ∧ q = f(y)",
				BySets(iso[3]))
			pointwise := a.Have(
				"the image of M₀ + M₁ and N₀ + N₁ have the same points",
				"∀z:C. z ∈ image(f, set_mul(V.add, fst(M), snd(M))) ⇔ z ∈ set_mul(W.add, fst(N), snd(N))",
				Derive(func(b *Argument) {
					b.FixAs[C]("z")
					b.Iff()
					b.Forward(
						"the image f(x + y) of a point of M₀ + M₁ is f(x) + f(y), with f(x) in N₀ and f(y) in N₁",
						func(d *Argument, member Fact) {
							_, point := d.UnpackAs[B](d.Simplified(member, Fwd(set_basic.InImage)), "v")
							value := d.Conjuncts(
								point,
								"z is f(v)",
								"v lies in M₀ + M₁")
							x, y, split := d.Unpack2As[B, B](d.Simplified(value[1], Fwd(quotient_group.InSetMul)), "x", "y")
							parts := d.Conjuncts(
								split,
								"x lies in M₀",
								"y lies in M₁",
								"v is x + y")
							d.Show(
								"z = f(x + y) = f(x) + f(y)",
								Simp(Fwd(quotient_group.InSetMul)),
								Witness(f.Apply(x)),
								Witness(f.Apply(y)),
								By(Normalized, value[0], parts[2], additive.At(x, y), parts[0], parts[1], into0.At(x), into1.At(y)))
						})
					b.Backward(
						"a sum p + q with p = f(x) in N₀ and q = f(y) in N₁ is the image f(x + y)",
						func(d *Argument, member Fact) {
							p, q, split := d.Unpack2As[C, C](d.Simplified(member, Fwd(quotient_group.InSetMul)), "p", "q")
							parts := d.Conjuncts(
								split,
								"p lies in N₀",
								"q lies in N₁",
								"z is p + q")
							x, px := d.ObtainAs[B](
								"p is f(x) for some x in M₀",
								"∃x:B. x ∈ fst(M) ∧ p = f(x)",
								By(from0.At(p), parts[0]))
							y, qy := d.ObtainAs[B](
								"q is f(y) for some y in M₁",
								"∃y:B. y ∈ snd(M) ∧ q = f(y)",
								By(from1.At(q), parts[1]))
							first := d.Conjuncts(
								px,
								"x lies in M₀",
								"p is f(x)")
							second := d.Conjuncts(
								qy,
								"y lies in M₁",
								"q is f(y)")
							sum := d.Have(
								"x + y lies in M₀ + M₁",
								"x + y ∈ set_mul(V.add, fst(M), snd(M))",
								Simp(Fwd(quotient_group.InSetMul)),
								Witness(x),
								Witness(y),
								By(first[0], second[0]))
							d.Show(
								"z = p + q = f(x) + f(y) = f(x + y)",
								Simp(Fwd(set_basic.InImage)),
								Witness(d.TermAs[B]("x + y")),
								By(Normalized, sum, parts[2], first[1], second[1], additive.At(x, y), first[0], second[0]))
						})
				}))
			sums := a.Have(
				"so f carries M₀ + M₁ onto N₀ + N₁",
				"image(f, set_mul(V.add, fst(M), snd(M))) = set_mul(W.add, fst(N), snd(N))",
				By(pointwise, set_basic.Extension))

			// H¹(M) and H¹(N) are the quotients of the two ambients by M₀ + M₁
			// and its image N₀ + N₁.
			a.Show(
				"so f passes to the quotients, H¹(M) onto H¹(N) over S",
				Unfold(lattice_pair.LatticePairH1Def),
				sums.RwRev(),
				By(module_homomorphism.QuotientIsomorphism.At(ringS, P, Q, f, sumM), isoS, sumSub))
		}),
})}

// IsomorphismSameEuler — a lattice pair N isomorphic to a lattice pair M
// with finite cohomology has finite cohomology, with the dimensions of H⁰
// and H¹ over k and the Euler characteristic of M. Over k, a field inside
// both charts, f restricts to an isomorphism of H⁰ and acts on the cosets
// of H¹ as one; an isomorphism of vector spaces carries finiteness and
// dimension across, and χ is h⁰ − h¹.
var IsomorphismSameEuler = isomorphismSameEulerThm{family.Add(registry.ProofEntry{
	Name:    "IsomorphismSameEuler",
	Key:     "prop_7cea663938c27d58",
	Reading: "Finiteness of M is assumed so that the dimensions compared are determined numbers.",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀A₀ A₁:set(A). " +
			"∀t s:A. " +
			"∀k:set(A). " +
			"∀inv:(A → A). " +
			"∀V:module_ops(A, B). " +
			"∀W:module_ops(A, C). " +
			"∀M:prod(set(B), set(B)). " +
			"∀N:prod(set(C), set(C)). " +
			"∀f:(B → C).",
		Hypotheses: []string{
			"«waBiaffine»",
			"ring_subfield(R, inv, k)",
			"k ⊆ A₀",
			"k ⊆ A₁",
			"«waSource»",
			"«waIsomorphism»",
			"lattice_pair_finite(R, k, V, M)",
		},
		Conclusion: "lattice_pair_finite(R, k, W, N) ∧ " +
			"lattice_pair_h0_dim(R, k, V, M) = lattice_pair_h0_dim(R, k, W, N) ∧ " +
			"lattice_pair_h1_dim(R, k, V, M) = lattice_pair_h1_dim(R, k, W, N) ∧ " +
			"lattice_pair_euler(R, k, V, M) = lattice_pair_euler(R, k, W, N)",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			A0, A1 *Expr[Set[A]],
			t, s *Expr[A],
			k *Expr[Set[A]],
			inv *Arrow[A, A],
			V *Expr[ModuleOps[A, B]],
			W *Expr[ModuleOps[A, C]],
			M *Expr[Prod[Set[B], Set[B]]],
			N *Expr[Prod[Set[C], Set[C]]],
			f *Arrow[B, C],
			given Fact,
		) {
			hypotheses := a.Conjuncts(
				given,
				"the datum is biaffine",
				"k is a field under R's operations",
				"k lies in chart 0",
				"and in chart 1",
				"M is a lattice pair in V",
				"f is an isomorphism of lattice pairs",
				"M has finite cohomology over k")
			datum, subfieldK, kIn0, kIn1, pair, isomorphism :=
				hypotheses[0], hypotheses[1], hypotheses[2], hypotheses[3], hypotheses[4], hypotheses[5]
			finiteM := a.Conjuncts(
				a.Unfolded(hypotheses[6], lattice_pair.LatticePairFiniteDef),
				"H⁰(M) is finite over k",
				"H¹(M) is finite over k")
			subringK := a.Have(
				"k is a subring of R",
				"subring(R, k)",
				By(lattice_pair.ChartFieldSubring.At(R, A0, A1, t, s, k, inv), datum, subfieldK, kIn0))
			scalars := a.TermAs[RingOps[A]]("restrict_ring(R, k)")
			h0M, h0N :=
				a.TermAs[ModuleOps[A, B]]("lattice_pair_h0(V, M)"),
				a.TermAs[ModuleOps[A, C]]("lattice_pair_h0(W, N)")
			h1M, h1N :=
				a.TermAs[ModuleOps[A, Set[B]]]("lattice_pair_h1(R, V, M)"),
				a.TermAs[ModuleOps[A, Set[C]]]("lattice_pair_h1(R, W, N)")
			onCosets := a.TermAs[Fun[Set[B], Set[C]]]("λx:set(B). image(f, x)")

			// Over k, f restricts to H⁰ and acts on the cosets of H¹ isomorphically.
			onH0 := a.Have(
				"f restricts to an isomorphism of H⁰(M) onto H⁰(N) over k",
				"module_isomorphism(restrict_ring(R, k), lattice_pair_h0(V, M), lattice_pair_h0(W, N), f)",
				By(
					IsomorphismSameH0.At(R, A0, A1, k, V, W, M, N, f),
					datum,
					subringK,
					kIn0,
					kIn1,
					pair,
					isomorphism))
			onH1 := a.Have(
				"and x ↦ image(f, x) is an isomorphism of H¹(M) onto H¹(N) over k",
				"module_isomorphism(restrict_ring(R, k), "+
					"    lattice_pair_h1(R, V, M), "+
					"    lattice_pair_h1(R, W, N), "+
					"    λx:set(B). image(f, x))",
				By(
					IsomorphismSameH1.At(R, A0, A1, t, s, k, V, W, M, N, f),
					datum,
					subringK,
					kIn0,
					kIn1,
					pair,
					isomorphism))

			// An isomorphism over the field k carries finiteness and dimension.
			fieldK := a.Have(
				"k is a field under the operations of R restricted to k, which are R's",
				"ring_subfield(restrict_ring(R, k), inv, k)",
				By(subfieldK, field.RingSubfieldRestrict.At(R, k, inv, k)))
			h0 := a.Have(
				"so H⁰(N) is finite over k, of the dimension of H⁰(M)",
				"«waFinite»(lattice_pair_h0(W, N)) ∧ "+
					"«waDim»(lattice_pair_h0(W, N)) = «waDim»(lattice_pair_h0(V, M))",
				By(fieldK, onH0, finiteM[0], module_dimension.IsomorphismDim.At(scalars, h0M, inv, h0N, f)))
			h1 := a.Have(
				"so H¹(N) is finite over k, of the dimension of H¹(M)",
				"«waFinite»(lattice_pair_h1(R, W, N)) ∧ "+
					"«waDim»(lattice_pair_h1(R, W, N)) = «waDim»(lattice_pair_h1(R, V, M))",
				By(fieldK, onH1, finiteM[1], module_dimension.IsomorphismDim.At(scalars, h1M, inv, h1N, onCosets)))

			a.Show(
				"so N has finite cohomology over k with M's h⁰ and h¹, and so the same χ = h⁰ − h¹",
				Simp(
					Fwd(lattice_pair.LatticePairFiniteDef),
					Fwd(lattice_pair.LatticePairEulerDef),
					Fwd(lattice_pair.LatticePairH0DimDef),
					Fwd(lattice_pair.LatticePairH1DimDef)),
				By(h0, h1))
		}),
})}

// ---------------------------------------------------------------------------
// Composing and inverting
// ---------------------------------------------------------------------------

// IsomorphismCompose — isomorphisms of lattice pairs compose.
var IsomorphismCompose = isomorphismComposeThm{family.Add(registry.ProofEntry{
	Name: "IsomorphismCompose",
	Key:  "prop_75022f856b06d8c9",
	Reading: "lattice_pair(M) is load-bearing: it makes the ambient of M the R-combinations " +
		"of chart 0, which f carries into the ambient of N, where g is linear and one-to-one.",
	Deps: []registry.EntryLike{
		LatticePairIsomorphismDef,
		PairMapCompose,
		PairMapAmbient,
		functions.InjectiveOnCompose,
		set_image.ImageCompose,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀A₀ A₁:set(A). " +
			"∀V:module_ops(A, B). " +
			"∀W:module_ops(A, C). " +
			"∀X:module_ops(A, D). " +
			"∀M:prod(set(B), set(B)). " +
			"∀N:prod(set(C), set(C)). " +
			"∀Q:prod(set(D), set(D)). " +
			"∀f:(B → C). " +
			"∀g:(C → D).",
		Hypotheses: []string{
			"«waSource»",
			"lattice_pair_isomorphism(R, V, M, W, N, f)",
			"lattice_pair_isomorphism(R, W, N, X, Q, g)",
		},
		Conclusion: "lattice_pair_isomorphism(R, V, M, X, Q, g ∘ f)",
	},
		"g ∘ f is a map of lattice pairs from M to Q (PairMapCompose, M a lattice pair), so what "+
			"remains is one-to-one and onto: f carries the ambient of M into that of N (PairMapAmbient), "+
			"where g is one-to-one, so g ∘ f is one-to-one on the ambient of M (InjectiveOnCompose); and "+
			"image(g ∘ f, ·) = image(g, image(f, ·)) (ImageCompose) carries each chart of M onto that of Q"),
})}

// IsomorphismInverse — the inverse of an isomorphism of lattice pairs,
// the preimage on the ambient of N and zero off it, is an isomorphism of
// lattice pairs back. f carries the ambient of M onto that of N
// (IsomorphismAmbient), so it is an isomorphism of the two ambients, and
// its preimage map is an isomorphism back; the inverse agrees with the
// preimage on the ambient of N and is zero off it, so it is an R-linear map
// of that ambient into V in the convention of the maps. Undoing f on the
// ambient of M, it carries each chart of N, the image of a chart of M,
// back onto that chart.
var IsomorphismInverse = isomorphismInverseThm{family.Add(registry.ProofEntry{
	Name: "IsomorphismInverse",
	Key:  "prop_3bf63b57ff31b2f0",
	Reading: "lattice_pair(M) is load-bearing twice: V must be a module, the inverse's target, and " +
		"the ambient of M must be the R-combinations of chart 0 for f to carry it onto the ambient of N.",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀A₀ A₁:set(A). " +
			"∀V:module_ops(A, B). " +
			"∀W:module_ops(A, C). " +
			"∀M:prod(set(B), set(B)). " +
			"∀N:prod(set(C), set(C)). " +
			"∀f:(B → C).",
		Hypotheses: []string{
			"«waSource»",
			"«waIsomorphism»",
		},
		Conclusion: "lattice_pair_isomorphism(R, W, N, V, M, «waInverse»)",
		Abbrev: Abbrev{
			{Name: "waInverse", Text: "λw:C. " +
				"    COND(w ∈ lattice_pair_ambient(R, W, N), " +
				"        inverse_on(lattice_pair_ambient(R, V, M), f, w), " +
				"        V.zero)"},
		},
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			A0, A1 *Expr[Set[A]],
			V *Expr[ModuleOps[A, B]],
			W *Expr[ModuleOps[A, C]],
			M *Expr[Prod[Set[B], Set[B]]],
			N *Expr[Prod[Set[C], Set[C]]],
			f *Arrow[B, C],
			given Fact,
		) {
			hypotheses := a.Conjuncts(
				given,
				"M is a lattice pair",
				"f is an isomorphism of lattice pairs")
			pair, isomorphism := hypotheses[0], hypotheses[1]
			iso := a.Conjuncts(
				a.Unfolded(isomorphism, LatticePairIsomorphismDef),
				"f is a map of lattice pairs",
				"one-to-one on the ambient of M",
				"onto chart 0 of N",
				"and onto chart 1")
			pairMap, oneToOne, onto0, onto1 := iso[0], iso[1], iso[2], iso[3]
			ambM, ambN :=
				a.TermAs[Set[B]]("lattice_pair_ambient(R, V, M)"), a.TermAs[Set[C]]("lattice_pair_ambient(R, W, N)")
			fstM, sndM := a.TermAs[Set[B]]("fst(M)"), a.TermAs[Set[B]]("snd(M)")
			P := a.TermAs[ModuleOps[A, B]]("restrict_module(V, lattice_pair_ambient(R, V, M))")
			Q := a.TermAs[ModuleOps[A, C]]("restrict_module(W, lattice_pair_ambient(R, W, N))")
			inverse := a.TermAs[Fun[C, B]]("«waInverse»")
			preimage := a.TermAs[Fun[C, B]]("inverse_on(lattice_pair_ambient(R, V, M), f)")

			// Over R, f is an isomorphism of the ambient of M onto that of N.
			contains := a.Conjuncts(
				GroupPremises(hypotheses[0], lattice_pair.AmbientContains.At(R, A0, A1, V, M)),
				"the ambient of M is an R-submodule of V",
				"holding chart 0",
				"and chart 1")
			linear := a.Have(
				"f is R-linear on the ambient of M",
				"module_homomorphism(R, restrict_module(V, lattice_pair_ambient(R, V, M)), W, f)",
				By(PairMapHomomorphism.At(R, V, W, M, N, f), pairMap))
			onto := a.Have(
				"f carries the ambient of M onto that of N",
				"image(f, lattice_pair_ambient(R, V, M)) = lattice_pair_ambient(R, W, N)",
				By(IsomorphismAmbient.At(R, A0, A1, V, W, M, N, f), pair, isomorphism))
			ambientN := a.Have(
				"the ambient of N, the image of that of M, is an R-submodule of W",
				"submodule(R, W, lattice_pair_ambient(R, W, N))",
				onto.RwRev(),
				Cite(module_homomorphism.ImageSubmodule.Read(linear)))
			into := a.Have(
				"f carries the ambient of M into that of N",
				"∀u:B. u ∈ lattice_pair_ambient(R, V, M) ⇒ f(u) ∈ lattice_pair_ambient(R, W, N)",
				onto.RwRev(),
				Cite(set_image.FunInImage))
			ambients := a.Have(
				"so f is R-linear from the ambient of M to that of N",
				"module_homomorphism(R, "+
					"    restrict_module(V, lattice_pair_ambient(R, V, M)), "+
					"    restrict_module(W, lattice_pair_ambient(R, W, N)), "+
					"    f)",
				By(module_homomorphism.HomCorestrict.At(R, P, W, f, ambN), linear, ambientN, into))
			forward := a.Have(
				"one-to-one and onto, it is an isomorphism of the ambients",
				"module_isomorphism(R, "+
					"    restrict_module(V, lattice_pair_ambient(R, V, M)), "+
					"    restrict_module(W, lattice_pair_ambient(R, W, N)), "+
					"    f)",
				By(module_homomorphism.ModuleIsomorphismDef, ambients, oneToOne, onto))

			// On the ambient of N the inverse is the preimage map.
			agree := a.Have(
				"on the ambient of N the inverse is the preimage",
				Statement{
					Binders: "∀w:C.",
					Hypotheses: []string{
						"w ∈ lattice_pair_ambient(R, W, N)",
					},
					Conclusion: "COND(w ∈ lattice_pair_ambient(R, W, N), " +
						"    inverse_on(lattice_pair_ambient(R, V, M), f, w), " +
						"    V.zero) = " +
						"inverse_on(lattice_pair_ambient(R, V, M), f, w)",
				},
				Derive(func(b *Argument) {
					b.FixAs[C]("w")
					b.Show(
						"w lies in the ambient of N, which selects the preimage",
						By(b.Assume()))
				}))
			inverseIso := a.Have(
				"so the inverse is an isomorphism of the ambient of N onto that of M",
				"module_isomorphism(R, "+
					"    restrict_module(W, lattice_pair_ambient(R, W, N)), "+
					"    restrict_module(V, lattice_pair_ambient(R, V, M)), "+
					"    «waInverse»)",
				By(
					module_homomorphism.IsomorphismCongruence.At(R, Q, P, preimage, inverse),
					module_homomorphism.IsomorphismInverse.At(R, P, Q, f),
					forward,
					agree))
			bijective := a.Conjuncts(
				a.Unfolded(inverseIso, module_homomorphism.ModuleIsomorphismDef),
				"the inverse is R-linear from the ambient of N to that of M",
				"one-to-one on the ambient of N",
				"and onto the ambient of M")
			linearBack := bijective[0]

			// It is an R-linear map of the ambient of N into V, zero off that
			// ambient: one of the maps hom_set gathers.
			intoV := a.Have(
				"its values on the ambient of N lie in the ambient of M, inside V",
				Statement{
					Binders: "∀w:C.",
					Hypotheses: []string{
						"w ∈ lattice_pair_ambient(R, W, N)",
					},
					Conclusion: "COND(w ∈ lattice_pair_ambient(R, W, N), " +
						"    inverse_on(lattice_pair_ambient(R, V, M), f, w), " +
						"    V.zero) ∈ " +
						"V.carrier",
				},
				By(
					module_homomorphism.HomIn.Read(linearBack),
					submodule.SubmoduleSubset.Read(contains[0]),
					set_basic.SubsetDef))
			linearV := a.Have(
				"so the inverse is an R-linear map of the ambient of N into V",
				"module_homomorphism(R, restrict_module(W, lattice_pair_ambient(R, W, N)), V, «waInverse»)",
				By(
					module_homomorphism.ModuleHomomorphismDef.At(R, Q, V, inverse),
					module_homomorphism.HomSource.Read(linearBack),
					pair,
					lattice_pair.PairModuleOn,
					intoV,
					module_homomorphism.HomAdd.Read(linearBack),
					module_homomorphism.HomSmul.Read(linearBack)))
			vanishes := a.Have(
				"off the ambient of N the inverse is V.zero",
				Statement{
					Binders: "∀w:C.",
					Hypotheses: []string{
						"w ∉ lattice_pair_ambient(R, W, N)",
					},
					Conclusion: "COND(w ∈ lattice_pair_ambient(R, W, N), " +
						"    inverse_on(lattice_pair_ambient(R, V, M), f, w), " +
						"    V.zero) = " +
						"V.zero",
				},
				Derive(func(b *Argument) {
					b.FixAs[C]("w")
					b.Show(
						"w lies off the ambient of N, which selects V.zero",
						By(b.Assume()))
				}))
			inHomSet := a.Have(
				"so the inverse is one of the R-linear maps of the ambient of N into V, zero off it",
				"«waInverse» ∈ hom_set(R, restrict_module(W, lattice_pair_ambient(R, W, N)), V)",
				By(hom_module.InHomSet.At(R, Q, V, inverse), linearV, vanishes))

			// Undoing f on the ambient of M, the inverse carries each chart of
			// N, the image of a chart of M, back onto it.
			undoes := a.Have(
				"the inverse undoes f on the ambient of M",
				Statement{
					Binders: "∀x:B.",
					Hypotheses: []string{
						"x ∈ lattice_pair_ambient(R, V, M)",
					},
					Conclusion: "COND(f(x) ∈ lattice_pair_ambient(R, W, N), " +
						"    inverse_on(lattice_pair_ambient(R, V, M), f, f(x)), " +
						"    V.zero) = " +
						"x",
				},
				Derive(func(b *Argument) {
					x := b.FixAs[B]("x")
					xIn := b.Assume()
					b.Show(
						"f(x) lies in the ambient of N, and f is one-to-one on the ambient of M",
						By(xIn, into.At(x), oneToOne, functions.InverseOnLeft.At(ambM, f, x)))
				}))
			restores := a.Have(
				"so the inverse carries the image under f of a part of the ambient of M back onto it",
				"∀X:set(B). X ⊆ lattice_pair_ambient(R, V, M) ⇒ image(«waInverse», image(f, X)) = X",
				Derive(func(b *Argument) {
					X := b.FixAs[Set[B]]("X")
					inAmbient := b.Assume()
					identity := b.Have(
						"on X the inverse after f is the identity",
						"∀x:B. x ∈ X ⇒ («waInverse» ∘ f)(x) = x",
						Derive(func(c *Argument) {
							c.FixAs[B]("x")
							c.Show(
								"x lies in the ambient of M, where the inverse undoes f",
								By(c.Assume(), inAmbient, undoes, functions.ComposeApply, set_basic.SubsetDef))
						}))
					composite := b.TermAs[Fun[B, B]]("«waInverse» ∘ f")
					b.Show(
						"the image of an image is the image under the composite, the identity on X",
						CalcEq(
							Leg(
								b.TermAs[Set[B]]("image(«waInverse» ∘ f, X)"),
								"an image of an image is the image under the composite",
								By(set_image.ImageCompose.At(inverse, f, X))),
							Leg(
								b.TermAs[Set[B]]("image(λx:B. x, X)"),
								"which on X is the identity",
								By(set_image.ImageCongruence.At(composite, b.TermAs[Fun[B, B]]("λx:B. x"), X), identity)),
							FinalLeg(
								"and the identity carries X onto itself",
								Cite(set_image.ImageIdentity)),
						))
				}))
			chart0 := a.Have(
				"the inverse carries chart 0 of N, the image of chart 0 of M, back onto it",
				"image(«waInverse», fst(N)) = fst(M)",
				onto0.RwRev(),
				By(restores.At(fstM), contains[1]))
			chart1 := a.Have(
				"and chart 1 of N onto chart 1 of M",
				"image(«waInverse», snd(N)) = snd(M)",
				onto1.RwRev(),
				By(restores.At(sndM), contains[2]))

			maps := a.Have(
				"a map of lattice pairs from N to M is an R-linear map of the "+
					"ambient of N into V carrying each chart into the same chart of M",
				"∀h:(C → B). "+
					"    h ∈ lattice_pair_maps(R, W, N, V, M) ⇔ "+
					"    h ∈ hom_set(R, restrict_module(W, lattice_pair_ambient(R, W, N)), V) ∧ "+
					"    image(h, fst(N)) ⊆ fst(M) ∧ "+
					"    image(h, snd(N)) ⊆ snd(M)",
				Simp(Fwd(LatticePairMapsDef)),
				BySets())
			pairMapBack := a.Have(
				"so the inverse is a map of lattice pairs from N to M",
				"«waInverse» ∈ lattice_pair_maps(R, W, N, V, M)",
				By(maps.At(inverse), inHomSet, chart0, chart1, set_order.SubsetRefl))
			a.Show(
				"one-to-one on the ambient of N and onto each chart of M, it is an isomorphism of lattice pairs",
				By(LatticePairIsomorphismDef.At(R, W, N, V, M, inverse), pairMapBack, bijective[1], chart0, chart1))
		}),
})}

// MapsPostcomposeIsomorphism — an isomorphism of target pairs induces, by
// postcomposition, an isomorphism of the modules of pair maps into them:
// composing after g keeps a map of lattice pairs one (PairMapCompose); it
// is S-linear and one-to-one, every map of lattice pairs into N being a
// homomorphism of the ambient of M into the ambient of N, where g is
// R-linear and one-to-one (hom_module.PostComposeHom,
// hom_module.PostComposeInjective); and it is onto, a map h into Q being
// g ∘ (g⁻¹ ∘ h) for the inverse isomorphism g⁻¹ of lattice pairs.
var MapsPostcomposeIsomorphism = mapsPostcomposeIsomorphismThm{family.Add(registry.ProofEntry{
	Name: "MapsPostcomposeIsomorphism",
	Key:  "prop_5f22522c0e211b37",
	Reading: "lattice_pair(M) is load-bearing: the maps out of M are linear on its ambient, " +
		"the span of chart 0. lattice_pair(N) makes the inverse g⁻¹ a map of pairs back and " +
		"puts W.zero in the ambient of N, where every map into N then takes its values. S " +
		"inside both charts makes both spaces of maps S-modules; Q is not assumed a lattice pair.",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀A₀ A₁ S:set(A). " +
			"∀t s:A. " +
			"∀V:module_ops(A, B). " +
			"∀W:module_ops(A, C). " +
			"∀X:module_ops(A, D). " +
			"∀M:prod(set(B), set(B)). " +
			"∀N:prod(set(C), set(C)). " +
			"∀Q:prod(set(D), set(D)). " +
			"∀g:(C → D).",
		Hypotheses: []string{
			"«waBiaffine»",
			"subring(R, S)",
			"S ⊆ A₀",
			"S ⊆ A₁",
			"«waSource»",
			"lattice_pair(R, A₀, A₁, W, N)",
			"lattice_pair_isomorphism(R, W, N, X, Q, g)",
		},
		Conclusion: "module_isomorphism(restrict_ring(R, S), " +
			"    lattice_pair_hom(R, V, M, W, N), " +
			"    lattice_pair_hom(R, V, M, X, Q), " +
			"    λf:(B → C). g ∘ f)",
		Abbrev: Abbrev{
			{Name: "mapsPostcomposeInverse", Text: "λw:D. " +
				"    COND(w ∈ lattice_pair_ambient(R, X, Q), " +
				"        inverse_on(lattice_pair_ambient(R, W, N), g, w), " +
				"        W.zero)"},
		},
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			A0, A1, S *Expr[Set[A]],
			t, s *Expr[A],
			V *Expr[ModuleOps[A, B]],
			W *Expr[ModuleOps[A, C]],
			X *Expr[ModuleOps[A, D]],
			M *Expr[Prod[Set[B], Set[B]]],
			N *Expr[Prod[Set[C], Set[C]]],
			Q *Expr[Prod[Set[D], Set[D]]],
			g *Arrow[C, D],
			given Fact,
		) {
			hypotheses := a.Conjuncts(
				given,
				"the datum is biaffine",
				"S is a subring of R",
				"S lies in chart 0",
				"and in chart 1",
				"M is a lattice pair in V",
				"N is a lattice pair in W",
				"g is an isomorphism of lattice pairs from N to Q")
			datum, subring, inChart0, inChart1 := hypotheses[0], hypotheses[1], hypotheses[2], hypotheses[3]
			pairM, pairN, isomorphism := hypotheses[4], hypotheses[5], hypotheses[6]
			iso := a.Conjuncts(
				a.Unfolded(isomorphism, LatticePairIsomorphismDef),
				"g is a map of lattice pairs",
				"one-to-one on the ambient of N",
				"onto chart 0 of Q",
				"and onto chart 1")
			gMap, gInjective := iso[0], iso[1]
			ringS := a.TermAs[RingOps[A]]("restrict_ring(R, S)")
			P := a.TermAs[ModuleOps[A, B]]("restrict_module(V, lattice_pair_ambient(R, V, M))")
			onAmbientN := a.TermAs[ModuleOps[A, C]]("restrict_module(W, lattice_pair_ambient(R, W, N))")
			ambM, ambN :=
				a.TermAs[Set[B]]("lattice_pair_ambient(R, V, M)"), a.TermAs[Set[C]]("lattice_pair_ambient(R, W, N)")
			mapsQ := a.TermAs[Set[Fun[B, D]]]("lattice_pair_maps(R, V, M, X, Q)")
			homsX := a.TermAs[ModuleOps[A, Fun[B, D]]](
				"hom_module(R, restrict_module(V, lattice_pair_ambient(R, V, M)), X)")
			source := a.TermAs[ModuleOps[A, Fun[B, C]]]("lattice_pair_hom(R, V, M, W, N)")
			target := a.TermAs[ModuleOps[A, Fun[B, D]]]("lattice_pair_hom(R, V, M, X, Q)")
			postcompose := a.TermAs[Fun[Fun[B, C], Fun[B, D]]]("λf:(B → C). g ∘ f")
			inverse := a.TermAs[Fun[D, C]]("«mapsPostcomposeInverse»")

			inR := a.Have(
				"S lies in R, chart 0 lying there",
				"S ⊆ R.carrier",
				By(lattice_pair.ChartSubsetInOverlap.At(R, A0, A1, t, s, S), datum, inChart0))
			sourceModule := a.Have(
				"the maps of M into N are an S-module, S lying in both charts",
				"module_on(restrict_ring(R, S), lattice_pair_hom(R, V, M, W, N))",
				By(
					PairMapsLinearSpace.At(R, A0, A1, S, V, W, M, N),
					datum,
					subring,
					inChart0,
					inChart1,
					pairM,
					pairN))
			gLinear := a.Have(
				"g is R-linear on the ambient of N",
				"module_homomorphism(R, restrict_module(W, lattice_pair_ambient(R, W, N)), X, g)",
				By(PairMapHomomorphism.At(R, W, X, N, Q, g), gMap))
			moduleV := a.Have(
				"V is an R-module",
				"module_on(R, V)",
				By(lattice_pair.PairModuleOn.At(R, A0, A1, V, M), pairM))
			ambientM := a.Conjuncts(
				GroupPremises(hypotheses[4], lattice_pair.AmbientContains.At(R, A0, A1, V, M)),
				"the ambient of M is an R-submodule of V",
				"holding chart 0",
				"and chart 1")[0]
			vectorsM := a.Have(
				"so the ambient of M is an R-module",
				"module_on(R, restrict_module(V, lattice_pair_ambient(R, V, M)))",
				By(submodule.SubmoduleModuleOn.Read(moduleV).At(ambM), ambientM))
			homsXModule := a.Have(
				"the R-linear maps of the ambient of M into X, an R-module as the target of g, are an R-module",
				"module_on(R, hom_module(R, restrict_module(V, lattice_pair_ambient(R, V, M)), X))",
				By(hom_module.HomSetModuleOn.At(R, P, X), vectorsM, module_homomorphism.HomTarget.Read(gLinear)))

			compose := a.Have(
				"composing after g carries a map of lattice pairs from M to N to one from M to Q",
				"∀f:(B → C). f ∈ lattice_pair_maps(R, V, M, W, N) ⇒ g ∘ f ∈ lattice_pair_maps(R, V, M, X, Q)",
				a.ForEach(func(f *Expr[Fun[B, C]]) Action {
					return By(PairMapCompose.At(R, A0, A1, V, W, X, M, N, Q, f, g), pairM, gMap)
				}))
			ambientNSub := a.Conjuncts(
				GroupPremises(hypotheses[5], lattice_pair.AmbientContains.At(R, A0, A1, W, N)),
				"the ambient of N is an R-submodule of W",
				"holding chart 0",
				"and chart 1")[0]
			zeroInN := a.Have(
				"W.zero lies in the ambient of N, an R-submodule of W",
				"W.zero ∈ lattice_pair_ambient(R, W, N)",
				Cite(submodule.SubmoduleZero.Read(ambientNSub)))
			corestricted := a.Have(
				"a map of lattice pairs into N is an R-linear map of the "+
					"ambient of M into the ambient of N, zero off the ambient of M",
				Statement{
					Binders: "∀f:(B → C).",
					Hypotheses: []string{
						"f ∈ lattice_pair_maps(R, V, M, W, N)",
					},
					Conclusion: "f ∈ " +
						"hom_set(R, " +
						"    restrict_module(V, lattice_pair_ambient(R, V, M)), " +
						"    restrict_module(W, lattice_pair_ambient(R, W, N)))",
				},
				Derive(func(b *Argument) {
					f := b.FixAs[Fun[B, C]]("f")
					fMap := b.Assume()
					homSet := b.Have(
						"f is one of the R-linear maps of the ambient of M into W, zero off it",
						"f ∈ hom_set(R, restrict_module(V, lattice_pair_ambient(R, V, M)), W)",
						BySets(fMap, LatticePairMapsDef.At(R, V, M, W, N)))
					member := b.Conjuncts(
						b.Simplified(homSet, Fwd(hom_module.InHomSet)),
						"f is R-linear on the ambient of M",
						"and zero off it")
					into := b.Have(
						"f carries the ambient of M into the ambient of N",
						"∀u:B. u ∈ lattice_pair_ambient(R, V, M) ⇒ f(u) ∈ lattice_pair_ambient(R, W, N)",
						By(
							PairMapAmbient.At(R, A0, A1, V, W, M, N, f),
							pairM,
							fMap,
							set_image.ImageSubsetIff.At(f, ambM, ambN)))
					corestriction := b.Have(
						"so f is R-linear into the ambient of N, an R-submodule of W",
						"module_homomorphism(R, "+
							"    restrict_module(V, lattice_pair_ambient(R, V, M)), "+
							"    restrict_module(W, lattice_pair_ambient(R, W, N)), "+
							"    f)",
						By(module_homomorphism.HomCorestrict.At(R, P, W, f, ambN), member[0], ambientNSub, into))
					b.Show(
						"zero off the ambient of M, f is one of the maps hom_set gathers there",
						By(hom_module.InHomSet.At(R, P, onAmbientN, f), corestriction, member[1]))
				}))

			postcomposeHom := a.Have(
				"composing after g is R-linear from the homomorphisms into the ambient of N to those into X",
				"module_homomorphism(R, "+
					"    hom_module(R, "+
					"        restrict_module(V, lattice_pair_ambient(R, V, M)), "+
					"        restrict_module(W, lattice_pair_ambient(R, W, N))), "+
					"    hom_module(R, restrict_module(V, lattice_pair_ambient(R, V, M)), X), "+
					"    λf:(B → C). g ∘ f)",
				By(hom_module.PostComposeHom.At(R, P, onAmbientN, X, g), vectorsM, gLinear))
			sum := a.Have(
				"so it is additive on the maps into N: g ∘ (f + h) = g ∘ f + g ∘ h",
				Statement{
					Binders: "∀f h:(B → C).",
					Hypotheses: []string{
						"f ∈ lattice_pair_maps(R, V, M, W, N)",
						"h ∈ lattice_pair_maps(R, V, M, W, N)",
					},
					Conclusion: "g ∘ fun_add(W.add, f, h) = fun_add(X.add, g ∘ f, g ∘ h)",
				},
				Derive(func(b *Argument) {
					f, h := b.FixAs[Fun[B, C]]("f"), b.FixAs[Fun[B, C]]("h")
					both := b.Conjuncts(
						b.Assume(),
						"f is a map of lattice pairs",
						"so is h")
					b.Show(
						"f and h are homomorphisms into the ambient of N",
						By(
							module_homomorphism.HomAdd.Read(postcomposeHom).AsFact().At(f, h),
							corestricted.At(f),
							corestricted.At(h),
							both[0],
							both[1]))
				}))
			scale := a.Have(
				"and commutes with scaling by S: g ∘ (c • f) = c • (g ∘ f)",
				Statement{
					Binders: "∀c:A. ∀f:(B → C).",
					Hypotheses: []string{
						"c ∈ S",
						"f ∈ lattice_pair_maps(R, V, M, W, N)",
					},
					Conclusion: "g ∘ fun_smul(W.smul, c, f) = fun_smul(X.smul, c, g ∘ f)",
				},
				Derive(func(b *Argument) {
					c, f := b.FixAs[A]("c"), b.FixAs[Fun[B, C]]("f")
					parts := b.Conjuncts(
						b.Assume(),
						"c is a scalar of S",
						"f is a map of lattice pairs")
					scalar := b.Have(
						"c lies in R, S lying there",
						"c ∈ R.carrier",
						BySets(parts[0], inR))
					b.Show(
						"f is a homomorphism into the ambient of N, and c a scalar of R",
						By(
							module_homomorphism.HomSmul.Read(postcomposeHom).AsFact().At(c, f),
							scalar,
							corestricted.At(f),
							parts[1]))
				}))
			into := a.Have(
				"so composing after g carries a map into N to an "+
					"R-linear map of the ambient of M into X, zero off it",
				Statement{
					Binders: "∀f:(B → C).",
					Hypotheses: []string{
						"f ∈ lattice_pair_maps(R, V, M, W, N)",
					},
					Conclusion: "g ∘ f ∈ hom_set(R, restrict_module(V, lattice_pair_ambient(R, V, M)), X)",
				},
				BySets(compose, LatticePairMapsDef.At(R, V, M, X, Q)))
			linear := a.Have(
				"composing after g is S-linear from the maps into N to the R-linear maps into X",
				"module_homomorphism(restrict_ring(R, S), "+
					"    lattice_pair_hom(R, V, M, W, N), "+
					"    hom_module(R, restrict_module(V, lattice_pair_ambient(R, V, M)), X), "+
					"    λf:(B → C). g ∘ f)",
				By(
					module_homomorphism.ModuleHomomorphismDef.At(ringS, source, homsX, postcompose),
					LatticePairHomDef.At(R, V, M, W, N),
					sourceModule,
					module.ModuleRestrictScalars.Read(homsXModule),
					subring,
					into,
					sum,
					scale))

			injective := a.Have(
				"composing after g is one-to-one on the maps into N",
				"injective_on(lattice_pair_maps(R, V, M, W, N), λf:(B → C). g ∘ f)",
				Simp(Fwd(functions.InjectiveOnDef)),
				Derive(func(b *Argument) {
					f, h := b.FixAs[Fun[B, C]]("f"), b.FixAs[Fun[B, C]]("h")
					parts := b.Conjuncts(
						b.Assume(),
						"f is a map of lattice pairs",
						"so is h",
						"g ∘ f = g ∘ h")
					b.Show(
						"f and h are homomorphisms into the ambient of N, where g is one-to-one",
						By(
							hom_module.PostComposeInjective.At(R, P, onAmbientN, g, f, h),
							gInjective,
							corestricted.At(f),
							corestricted.At(h),
							parts[0],
							parts[1],
							parts[2]))
				}))

			inverseIsomorphism := a.Have(
				"the inverse g⁻¹ of g, the preimage on the ambient of Q and "+
					"zero off it, is an isomorphism of lattice pairs from Q to N",
				"lattice_pair_isomorphism(R, X, Q, W, N, «mapsPostcomposeInverse»)",
				By(IsomorphismInverse.At(R, A0, A1, W, X, N, Q, g), pairN, isomorphism))
			inverseMap := a.Conjuncts(
				a.Unfolded(inverseIsomorphism, LatticePairIsomorphismDef),
				"g⁻¹ is a map of lattice pairs from Q to N",
				"one-to-one on the ambient of Q",
				"onto chart 0 of N",
				"and onto chart 1")[0]
			ambientImage := a.Have(
				"g carries the ambient of N onto the ambient of Q",
				"image(g, lattice_pair_ambient(R, W, N)) = lattice_pair_ambient(R, X, Q)",
				By(IsomorphismAmbient.At(R, A0, A1, W, X, N, Q, g), pairN, isomorphism))
			zeroInQ := a.Have(
				"so X.zero, the image of W.zero, lies in the ambient of Q",
				"X.zero ∈ lattice_pair_ambient(R, X, Q)",
				By(
					Normalized,
					module_homomorphism.HomZero.At(R, onAmbientN, X, g),
					gLinear,
					ambientImage,
					zeroInN,
					set_image.FunInImage.At(g, ambN, a.TermAs[C]("W.zero"))))
			valuesQ := a.Have(
				"a map of lattice pairs into Q takes all its values in the ambient of Q",
				"∀h:(B → D). h ∈ lattice_pair_maps(R, V, M, X, Q) ⇒ ∀u:B. h(u) ∈ lattice_pair_ambient(R, X, Q)",
				Derive(func(b *Argument) {
					h := b.FixAs[Fun[B, D]]()
					hMap := b.Assume()
					b.FixAs[B]()
					b.Cases(b.Term("u ∈ lattice_pair_ambient(R, V, M)"))
					b.When(
						"on the ambient of M, h carries it into the ambient of Q",
						func(c *Argument, inside Fact) {
							c.Show(
								"so h(u) lies in the ambient of Q",
								By(
									PairMapAmbient.At(R, A0, A1, V, X, M, Q, h),
									pairM,
									hMap,
									set_image.ImageSubsetIff.At(h, ambM, a.TermAs[Set[D]]("lattice_pair_ambient(R, X, Q)")),
									inside))
						})
					b.Otherwise(
						"off the ambient of M, h is X.zero",
						func(c *Argument, outside Fact) {
							homSet := c.Have(
								"h is one of the R-linear maps of the ambient of M into X, zero off it",
								"h ∈ hom_set(R, restrict_module(V, lattice_pair_ambient(R, V, M)), X)",
								BySets(hMap, LatticePairMapsDef.At(R, V, M, X, Q)))
							zero := c.Have(
								"so h(u) is X.zero",
								"h(u) = X.zero",
								By(hom_module.InHomSet.At(R, P, X, h), homSet, outside))
							c.Show(
								"which lies in the ambient of Q",
								zero.Rw(),
								By(zeroInQ))
						})
				}))
			undoes := a.Have(
				"g undoes g⁻¹ on the ambient of Q, the image of the ambient of N",
				"∀z:D. z ∈ lattice_pair_ambient(R, X, Q) ⇒ g(«mapsPostcomposeInverse»(z)) = z",
				a.ForEach(func(z *Expr[D]) Action {
					return By(Normalized, ambientImage, functions.InverseOnRight.At(ambN, g, z))
				}))
			splits := a.Have(
				"so a map h into Q is g ∘ (g⁻¹ ∘ h)",
				"∀h:(B → D). h ∈ lattice_pair_maps(R, V, M, X, Q) ⇒ g ∘ «mapsPostcomposeInverse» ∘ h = h",
				Derive(func(b *Argument) {
					h := b.FixAs[Fun[B, D]]()
					hMap := b.Assume()
					b.Show(
						"so g ∘ (g⁻¹ ∘ h) and h agree at every point",
						Funext(),
						Simp(Fwd(functions.ComposeApply)),
						Derive(func(c *Argument) {
							u := c.FixAs[B]("u")
							c.Show(
								"g(g⁻¹(h(u))) = h(u), h(u) lying in the ambient of Q",
								By(hMap, valuesQ.At(h, u), undoes.At(c.TermAs[D]("h(u)"))))
						}))
				}))
			pointwise := a.Have(
				"the maps g ∘ f for f a map into N are the maps into Q",
				"∀k:(B → D). "+
					"    k ∈ image(λf:(B → C). g ∘ f, lattice_pair_maps(R, V, M, W, N)) ⇔ "+
					"    k ∈ lattice_pair_maps(R, V, M, X, Q)",
				Derive(func(b *Argument) {
					k := b.FixAs[Fun[B, D]]("k")
					b.Iff()
					b.Forward(
						"g ∘ f is a map into Q for a map f into N",
						func(c *Argument, member Fact) {
							f, point := c.UnpackAs[Fun[B, C]](c.Simplified(member, Fwd(set_basic.InImage)), "f")
							parts := c.Conjuncts(
								point,
								"k is g ∘ f",
								"f is a map into N")
							c.Show(
								"so k is a map into Q",
								parts[0].Rw(),
								By(compose.At(f), parts[1]))
						})
					b.Backward(
						"a map k into Q is g ∘ (g⁻¹ ∘ k), and g⁻¹ ∘ k is a map into N",
						func(c *Argument, member Fact) {
							c.Show(
								"g⁻¹ ∘ k is a map of lattice pairs from M to N, composed of two",
								Simp(Fwd(set_basic.InImage)),
								Witness(c.TermAs[Fun[B, C]]("«mapsPostcomposeInverse» ∘ k")),
								By(
									splits.At(k),
									member,
									PairMapCompose.At(R, A0, A1, V, X, W, M, Q, N, k, inverse),
									pairM,
									inverseMap))
						})
				}))
			onto := a.Have(
				"so composing after g carries the maps into N onto the maps into Q",
				"image(λf:(B → C). g ∘ f, lattice_pair_maps(R, V, M, W, N)) = lattice_pair_maps(R, V, M, X, Q)",
				By(pointwise, set_basic.Extension))

			restricted := a.Have(
				"so composing after g is S-linear from the maps into N to the maps into Q",
				"module_homomorphism(restrict_ring(R, S), "+
					"    lattice_pair_hom(R, V, M, W, N), "+
					"    lattice_pair_hom(R, V, M, X, Q), "+
					"    λf:(B → C). g ∘ f)",
				By(
					module_homomorphism.HomCorestrict.At(ringS, source, homsX, postcompose, mapsQ),
					LatticePairHomDef.At(R, V, M, X, Q),
					linear,
					onto,
					module_homomorphism.ImageSubmodule.Read(linear),
					compose))
			a.Show(
				"one-to-one and onto, it is an isomorphism over S",
				By(
					module_homomorphism.ModuleIsomorphismDef.At(ringS, source, target, postcompose),
					LatticePairHomDef.At(R, V, M, W, N),
					LatticePairHomDef.At(R, V, M, X, Q),
					restricted,
					injective,
					onto))
		}),
})}

// LatticePairFromIsomorphism — a lattice pair N whose ambient is the whole of W,
// carried back along an isomorphism g of a part P of V onto W, is a lattice pair
// M in V, and the inverse of g is an isomorphism of lattice pairs from N to M. The
// inverse is R-linear into V and undoes g, so it takes the charts of N back onto
// those of M; and it carries the span of each chart of N, all of W, onto the span
// of the matching chart of M, so those two spans agree.
var LatticePairFromIsomorphism = latticePairFromIsomorphismThm{family.Add(registry.ProofEntry{
	Name: "LatticePairFromIsomorphism",
	Key:  "prop_f23d08d560e90bfa",
	Reading: "The charts of M are assumed submodules over A₀ and A₁: g is linear " +
		"only over R, and its charts' structure over the chart rings comes with M. " +
		"That the ambient of N is all of W is what lets the inverse be read on W itself.",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀A₀ A₁:set(A). " +
			"∀V:module_ops(A, B). " +
			"∀W:module_ops(A, C). " +
			"∀P:set(B). " +
			"∀M:prod(set(B), set(B)). " +
			"∀N:prod(set(C), set(C)). " +
			"∀g:(B → C).",
		Hypotheses: []string{
			"lattice_pair(R, A₀, A₁, W, N)",
			"lattice_pair_ambient(R, W, N) = W.carrier",
			"module_on(R, V)",
			"P ⊆ V.carrier",
			"submodule(restrict_ring(R, A₀), V, fst(M))",
			"submodule(restrict_ring(R, A₁), V, snd(M))",
			"fst(M) ⊆ P",
			"snd(M) ⊆ P",
			"module_isomorphism(R, restrict_module(V, P), W, g)",
			"image(g, fst(M)) = fst(N)",
			"image(g, snd(M)) = snd(N)",
		},
		Conclusion: "lattice_pair(R, A₀, A₁, V, M) ∧ lattice_pair_isomorphism(R, W, N, V, M, «inverse»)",
		Abbrev: Abbrev{
			{Name: "inverse", Text: "λw:C. COND(w ∈ W.carrier, inverse_on(P, g, w), V.zero)"},
		},
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			A0, A1 *Expr[Set[A]],
			V *Expr[module_record.ModuleOps[A, B]],
			W *Expr[module_record.ModuleOps[A, C]],
			P *Expr[Set[B]],
			M *Expr[Prod[Set[B], Set[B]]],
			N *Expr[Prod[Set[C], Set[C]]],
			g *Arrow[B, C],
			pair, ambient, moduleV, pInV, sub0, sub1, fstInP, sndInP, iso, onto0, onto1 Fact,
		) {
			source := a.TermAs[module_record.ModuleOps[A, B]]("restrict_module(V, P)")
			inverse := a.TermAs[Fun[C, B]]("«inverse»")
			preimage := a.TermAs[Fun[C, B]]("inverse_on(P, g)")
			fstM, sndM := a.TermAs[Set[B]]("fst(M)"), a.TermAs[Set[B]]("snd(M)")
			fstN, sndN := a.TermAs[Set[C]]("fst(N)"), a.TermAs[Set[C]]("snd(N)")
			bijection := a.Conjuncts(
				a.Unfolded(iso, module_homomorphism.ModuleIsomorphismDef),
				"g is R-linear",
				"one-to-one on P",
				"and onto W")
			forward, oneToOne := bijection[0], bijection[1]
			agree := a.Have(
				"on W the inverse is the preimage",
				"∀w:C. w ∈ W.carrier ⇒ COND(w ∈ W.carrier, inverse_on(P, g, w), V.zero) = inverse_on(P, g, w)",
				Derive(func(b *Argument) {
					b.FixAs[C]("w")
					b.Show(
						"w lies in W, which selects the preimage",
						By(b.Assume()))
				}))
			inverseIso := a.Have(
				"so the inverse is an isomorphism of W onto P",
				"module_isomorphism(R, W, restrict_module(V, P), «inverse»)",
				By(
					module_homomorphism.IsomorphismCongruence.At(R, W, source, preimage, inverse),
					module_homomorphism.IsomorphismInverse.At(R, source, W, g),
					iso,
					agree))
			back := a.Conjuncts(
				a.Unfolded(inverseIso, module_homomorphism.ModuleIsomorphismDef),
				"the inverse is R-linear from W to P",
				"one-to-one on W",
				"and onto P")
			linearBack := back[0]
			intoV := a.Have(
				"its values on W lie in P, inside V",
				"∀w:C. w ∈ W.carrier ⇒ «inverse»(w) ∈ V.carrier",
				Derive(func(b *Argument) {
					w := b.FixAs[C]("w")
					wIn := b.Assume()
					b.Show(
						"P lies in V",
						By(
							module_homomorphism.HomIn.Read(linearBack).At(proof.MemberOf(w, wIn)),
							pInV,
							set_basic.SubsetDef.At(P, a.TermAs[Set[B]]("V.carrier"))))
				}))
			linearV := a.Have(
				"so the inverse is an R-linear map of W into V",
				"module_homomorphism(R, W, V, «inverse»)",
				By(
					module_homomorphism.ModuleHomomorphismDef.At(R, W, V, inverse),
					module_homomorphism.HomSource.Read(linearBack),
					moduleV,
					intoV,
					module_homomorphism.HomAdd.Read(linearBack),
					module_homomorphism.HomSmul.Read(linearBack)))
			vanishes := a.Have(
				"off W the inverse is V.zero",
				"∀w:C. w ∉ W.carrier ⇒ «inverse»(w) = V.zero",
				Derive(func(b *Argument) {
					b.FixAs[C]("w")
					b.Show(
						"w lies off W, which selects V.zero",
						By(b.Assume()))
				}))
			undoes := a.Have(
				"the inverse undoes g on P",
				"∀x:B. x ∈ P ⇒ «inverse»(g(x)) = x",
				Derive(func(b *Argument) {
					x := b.FixAs[B]("x")
					xIn := b.Assume()
					b.Show(
						"g(x) lies in W, and g is one-to-one on P",
						By(
							module_homomorphism.HomIn.Read(forward).At(proof.MemberOf(x, xIn)),
							oneToOne,
							xIn,
							functions.InverseOnLeft.At(P, g, x)))
				}))
			restores := a.Have(
				"so the inverse carries the image under g of a part of P back onto it",
				"∀X:set(B). X ⊆ P ⇒ image(«inverse», image(g, X)) = X",
				Derive(func(b *Argument) {
					X := b.FixAs[Set[B]]("X")
					inP := b.Assume()
					identity := b.Have(
						"on X the inverse after g is the identity",
						"∀x:B. x ∈ X ⇒ («inverse» ∘ g)(x) = x",
						Derive(func(c *Argument) {
							x := c.FixAs[B]("x")
							xIn := c.Assume()
							inside := c.Have(
								"x lies in P",
								"x ∈ P",
								By(xIn, inP, set_basic.SubsetDef))
							c.Show(
								"where the inverse undoes g",
								Simp(Fwd(functions.ComposeApply)),
								By(undoes.At(x), inside))
						}))
					composite := b.TermAs[Fun[B, B]]("«inverse» ∘ g")
					b.Show(
						"the image of an image is the image under the composite, the identity on X",
						CalcEq(
							Leg(
								b.TermAs[Set[B]]("image(«inverse» ∘ g, X)"),
								"an image of an image is the image under the composite",
								By(set_image.ImageCompose.At(inverse, g, X))),
							Leg(
								b.TermAs[Set[B]]("image(λx:B. x, X)"),
								"which on X is the identity",
								By(set_image.ImageCongruence.At(composite, b.TermAs[Fun[B, B]]("λx:B. x"), X), identity)),
							FinalLeg(
								"and the identity carries X onto itself",
								Cite(set_image.ImageIdentity)),
						))
				}))
			chart0 := a.Have(
				"the inverse carries chart 0 of N back onto chart 0 of M",
				"image(«inverse», fst(N)) = fst(M)",
				onto0.RwRev(),
				By(restores.At(fstM), fstInP))
			chart1 := a.Have(
				"and chart 1 of N onto chart 1 of M",
				"image(«inverse», snd(N)) = snd(M)",
				onto1.RwRev(),
				By(restores.At(sndM), sndInP))
			contains := a.Conjuncts(
				GroupPremises(pair, lattice_pair.AmbientContains.At(R, A0, A1, W, N)),
				"the ambient of N is a submodule of W",
				"holding chart 0",
				"and chart 1")
			fstInW := a.Have(
				"chart 0 of N lies in W",
				"fst(N) ⊆ W.carrier",
				ambient.RwRev(),
				By(contains[1]))
			sndInW := a.Have(
				"and so does chart 1",
				"snd(N) ⊆ W.carrier",
				ambient.RwRev(),
				By(contains[2]))
			span0 := a.Have(
				"the inverse carries the span of chart 0 of N onto the span of chart 0 of M",
				"image(«inverse», module_span(R, W, fst(N))) = module_span(R, V, fst(M))",
				By(linearV, fstInW, chart0, linear_independence.HomSpan.At(R, W, V, inverse, fstN)))
			span1 := a.Have(
				"and the span of chart 1 of N onto the span of chart 1 of M",
				"image(«inverse», module_span(R, W, snd(N))) = module_span(R, V, snd(M))",
				By(linearV, sndInW, chart1, linear_independence.HomSpan.At(R, W, V, inverse, sndN)))
			clauses := a.Conjuncts(
				a.Unfolded(pair, lattice_pair.LatticePairDef),
				"W is a module",
				"chart 0 of N is a submodule",
				"chart 1 of N is a submodule",
				"the two charts of N span the same")
			spans := a.Have(
				"so the two charts of M span the same",
				"module_span(R, V, fst(M)) = module_span(R, V, snd(M))",
				By(span0, span1, clauses[3]))
			lattice := a.Have(
				"so M is a lattice pair",
				"lattice_pair(R, A₀, A₁, V, M)",
				Unfold(lattice_pair.LatticePairDef),
				By(moduleV, sub0, sub1, spans))
			inHomSet := a.Have(
				"the inverse is one of the R-linear maps of W into V, zero off W",
				"«inverse» ∈ hom_set(R, restrict_module(W, lattice_pair_ambient(R, W, N)), V)",
				ambient.Rw(),
				Simp(Fwd(module_record.RestrictModuleCarrier)),
				By(linearV, vanishes, hom_module.InHomSet.At(R, W, V, inverse)))
			maps := a.Have(
				"a map of lattice pairs from N to M is an R-linear map of the "+
					"ambient of N into V carrying each chart into the same chart of M",
				"∀h:(C → B). "+
					"    h ∈ lattice_pair_maps(R, W, N, V, M) ⇔ "+
					"    h ∈ hom_set(R, restrict_module(W, lattice_pair_ambient(R, W, N)), V) ∧ "+
					"    image(h, fst(N)) ⊆ fst(M) ∧ "+
					"    image(h, snd(N)) ⊆ snd(M)",
				Simp(Fwd(LatticePairMapsDef)),
				BySets())
			pairMap := a.Have(
				"so the inverse is a map of lattice pairs from N to M",
				"«inverse» ∈ lattice_pair_maps(R, W, N, V, M)",
				By(maps.At(inverse), inHomSet, chart0, chart1, set_order.SubsetRefl))
			oneToOneBack := a.Have(
				"and it is one-to-one on the ambient of N",
				"injective_on(lattice_pair_ambient(R, W, N), «inverse»)",
				ambient.Rw(),
				By(back[1]))
			a.Show(
				"M is a lattice pair and the inverse an isomorphism of lattice pairs onto it",
				By(
					lattice,
					LatticePairIsomorphismDef.At(R, W, N, V, M, inverse),
					pairMap,
					oneToOneBack,
					chart0,
					chart1))
		}),
})}
