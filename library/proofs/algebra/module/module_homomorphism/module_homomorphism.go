// module_homomorphism.go — linear maps between modules on sets over one
// ring: their laws, linearity over a subring of the scalars, the kernel,
// the image and the preimage of a submodule as submodules, restriction to
// a submodule at either end, composites, pointwise negatives, sums and
// multiples, and maps agreeing on the source, the projection onto a
// quotient, the product of two modules with its two inclusions and first
// projection, maps out of a quotient (a linear relation between
// representatives, an isomorphism passing to the quotients, the factor
// theorem), bilinear maps, and module isomorphisms — the inverse, the
// composite, a map agreeing with one, a one-to-one map onto its image, the
// isomorphic modules one witnesses, the first isomorphism theorem. A
// homomorphism includes both module structures, each held in a record. The
// kernel is the additive group's, group_kernel.

package module_homomorphism

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/quotient_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/proofs/sets/set_product"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// The records hold the operations and carriers; module_on supplies
// their laws. A map carries both endpoint structures in its hypothesis.
const endpoints = "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, C). "
const mapBinders = endpoints + "∀f:(B → C). "

// ModuleHomomorphismDef — f is a linear map from the R-module M to N.
var ModuleHomomorphismDef = moduleHomomorphismDefThm{family.DefineStructure(registry.DefEntry{
	Name:    "ModuleHomomorphismDef",
	Key:     "prop_45e031be0dbb2971",
	Const:   "module_homomorphism",
	Type:    "ring_ops(A) → module_ops(A, B) → module_ops(A, C) → (B → C) → bool",
	Subject: "f",
	Equations: []string{mapBinders + "module_homomorphism(R, M, N, f) ⇔ " +
		"module_on(R, M) ∧ module_on(R, N) ∧ " +
		"(∀u:B. u ∈ M.carrier ⇒ f(u) ∈ N.carrier) ∧ " +
		"(∀u v:B. u ∈ M.carrier ∧ v ∈ M.carrier ⇒ f(M.add(u, v)) = N.add(f(u), f(v))) ∧ " +
		"(∀c:A. ∀u:B. c ∈ R.carrier ∧ u ∈ M.carrier ⇒ f(M.smul(c, u)) = N.smul(c, f(u)))"},
})}

// HomSource — the source of a homomorphism is an R-module.
var HomSource = homSourceThm{family.Add(registry.ProofEntry{
	Name:  "HomSource",
	Key:   "prop_a02dc7fbac42aa76",
	Build: ModuleHomomorphismDef.Axiom("module_on(R, M)"),
})}

// HomTarget — the target of a homomorphism is an R-module.
var HomTarget = homTargetThm{family.Add(registry.ProofEntry{
	Name:  "HomTarget",
	Key:   "prop_d1966455a7b03ace",
	Build: ModuleHomomorphismDef.Axiom("module_on(R, N)"),
})}

// HomIn — a homomorphism carries its source into its target.
var HomIn = homInThm{family.Add(registry.ProofEntry{
	Name: "HomIn",
	Key:  "prop_4606481451c59e09",
	Build: ModuleHomomorphismDef.Axiom(Statement{
		Binders: "∀u:B.",
		Hypotheses: []string{
			"u ∈ M.carrier",
		},
		Conclusion: "f(u) ∈ N.carrier",
	}),
})}

// HomAdd — a homomorphism preserves addition.
var HomAdd = homAddThm{family.Add(registry.ProofEntry{
	Name: "HomAdd",
	Key:  "prop_b86950580665b50d",
	Build: ModuleHomomorphismDef.Axiom(Statement{
		Binders: "∀u v:B.",
		Hypotheses: []string{
			"u ∈ M.carrier",
			"v ∈ M.carrier",
		},
		Conclusion: "f(M.add(u, v)) = N.add(f(u), f(v))",
	}),
})}

// HomSmul — a homomorphism preserves scalar multiplication.
var HomSmul = homSmulThm{family.Add(registry.ProofEntry{
	Name: "HomSmul",
	Key:  "prop_3bb000dc71f7a3e5",
	Build: ModuleHomomorphismDef.Axiom(Statement{
		Binders: "∀c:A. ∀u:B.",
		Hypotheses: []string{
			"c ∈ R.carrier",
			"u ∈ M.carrier",
		},
		Conclusion: "f(M.smul(c, u)) = N.smul(c, f(u))",
	}),
})}

// HomGroup — forgetting the scalars, a linear map is a homomorphism of the
// additive groups: each module is a group under its addition, and the map
// carries the source carrier into the target and preserves sums.
var HomGroup = homGroupThm{family.Add(registry.ProofEntry{
	Name: "HomGroup",
	Key:  "prop_b42b6d1443cccb75",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, C). ∀f:(B → C).",
		Hypotheses: []string{
			"module_homomorphism(R, M, N, f)",
		},
		Conclusion: "group_homomorphism(module_additive_group(M), module_additive_group(N), f)",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			N *Expr[ModuleOps[A, C]],
			f *Arrow[B, C],
			hom Fact,
		) {
			a.Show(
				"both additive groups, the carrier map and additivity "+
					"are the four conditions on a group homomorphism",
				By(
					group_homomorphism.GroupHomomorphism,
					module.AddGroupOn.Read(HomSource.Read(hom)),
					module.AddGroupOn.Read(HomTarget.Read(hom)),
					HomIn.Read(hom),
					HomAdd.Read(hom)))
		}),
})}

// HomRestrictScalars — a homomorphism over R is one over any subring S of
// R, its scalars restricted: both modules are modules over S, and a
// multiple by a scalar of S is a multiple by a scalar of R, which f keeps.
var HomRestrictScalars = homRestrictScalarsThm{family.Add(registry.ProofEntry{
	Name: "HomRestrictScalars",
	Key:  "prop_7b53190ae65da4ff",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, C). ∀f:(B → C). ∀S:set(A).",
		Hypotheses: []string{
			"module_homomorphism(R, M, N, f)",
			"subring(R, S)",
		},
		Conclusion: "module_homomorphism(restrict_ring(R, S), M, N, f)",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			N *Expr[ModuleOps[A, C]],
			f *Arrow[B, C],
			S *Expr[Set[A]],
			hom, subring Fact,
		) {
			inR := a.Have(
				"S lies in R's carrier",
				"S ⊆ R.carrier",
				By(comm_ring.SubringSubset.Read(subring)))
			source := a.Have(
				"M, a module over R, is one over its subring S",
				"module_on(restrict_ring(R, S), M)",
				By(module.ModuleRestrictScalars.Read(HomSource.Read(hom)).At(S), subring))
			target := a.Have(
				"and so is N",
				"module_on(restrict_ring(R, S), N)",
				By(module.ModuleRestrictScalars.Read(HomTarget.Read(hom)).At(S), subring))
			a.Show(
				"f keeps sums and S-multiples, an S-multiple being an R-multiple",
				By(
					ModuleHomomorphismDef,
					source,
					target,
					HomIn.Read(hom),
					HomAdd.Read(hom),
					HomSmul.Read(hom),
					a.Unfolded(inR, set_basic.SubsetDef)))
		}),
})}

// HomRestrictSubring — a homomorphism over R restricted to K is one over R
// restricted to any subring S lying in K: S is a subring of the restriction
// to K, and restricting twice is restricting once.
var HomRestrictSubring = homRestrictSubringThm{family.Add(registry.ProofEntry{
	Name: "HomRestrictSubring",
	Key:  "prop_dd70ceca1724e33f",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, C). ∀f:(B → C). ∀K S:set(A).",
		Hypotheses: []string{
			"module_homomorphism(restrict_ring(R, K), M, N, f)",
			"subring(R, S)",
			"S ⊆ K",
		},
		Conclusion: "module_homomorphism(restrict_ring(R, S), M, N, f)",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			N *Expr[ModuleOps[A, C]],
			f *Arrow[B, C],
			K, S *Expr[Set[A]],
			hom, subring, inK Fact,
		) {
			a.Show(
				"S is a subring of R restricted to K, and restricting twice is restricting once",
				By(
					Normalized,
					hom,
					subring,
					inK,
					comm_ring.SubringRestrict.At(R, S, K),
					module_record.RestrictRingTwice.At(R, K, S),
					HomRestrictScalars.Read(hom).At(S)))
		}),
})}

// HomZero — a homomorphism carries the zero of M to the zero of N:
// f(M.zero) is f(M.zero + M.zero), which is f(M.zero) + f(M.zero) in N,
// so f(M.zero) is its own double in N's additive group.
var HomZero = homZeroThm{family.Add(registry.ProofEntry{
	Name: "HomZero",
	Key:  "prop_d9d616a9a9f66d1d",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, C). ∀f:(B → C).",
		Hypotheses: []string{
			"module_homomorphism(R, M, N, f)",
		},
		Conclusion: "f(M.zero) = N.zero",
	},
		func(
			a *Argument,
			R *Expr[module_record.RingOps[A]],
			M *Expr[module_record.ModuleOps[A, B]],
			N *Expr[module_record.ModuleOps[A, C]],
			f *Arrow[B, C],
			hom Fact,
		) {
			additive := a.Have(
				"the vectors of M are a group under +",
				"group_on(module_additive_group(M))",
				By(module.AddGroupOn, HomSource.Read(hom)))
			target := a.Have(
				"so are those of N",
				"group_on(module_additive_group(N))",
				By(module.AddGroupOn, HomTarget.Read(hom)))
			zeroIn := a.Have(
				"the zero of M is a vector of M",
				"M.zero ∈ M.carrier",
				By(group.OneIn.Read(additive)))
			image := a.Have(
				"its image is a vector of N",
				"f(M.zero) ∈ N.carrier",
				By(HomIn, hom, zeroIn))
			double := a.Have(
				"the image is its own double",
				"f(M.zero) + f(M.zero) = f(M.zero)",
				CalcEq(
					Leg(
						a.TermAs[C]("f(M.zero + M.zero)"),
						"f carries a sum to a sum",
						By(HomAdd, hom, zeroIn)),
					FinalLeg(
						"and zero + zero is zero in M",
						Simp(Fwd(group.LeftIdentityOn.Read(additive)), Fwd(group.OneIn.Read(additive))),
						Basic()),
				))
			a.Show(
				"an element of a group that is its own double is the identity",
				By(double, group.IdempotentIsOneOn.Read(target), image))
		}),
})}

// HomNeg — a homomorphism carries the negative of a vector of M to the
// negative of its image: forgetting the scalars, f is a homomorphism of the
// additive groups, and a group homomorphism carries an inverse to the
// inverse of the image.
var HomNeg = homNegThm{family.Add(registry.ProofEntry{
	Name: "HomNeg",
	Key:  "prop_70cd27fc6e807cd1",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, C). ∀f:(B → C). ∀u:B.",
		Hypotheses: []string{
			"module_homomorphism(R, M, N, f)",
			"u ∈ M.carrier",
		},
		Conclusion: "f(M.neg(u)) = N.neg(f(u))",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			N *Expr[ModuleOps[A, C]],
			f *Arrow[B, C],
			u *Expr[B],
			given Fact,
		) {
			parts := a.Conjuncts(
				given,
				"f is a homomorphism of M into N",
				"u is a vector of M")
			linear, um := parts[0], proof.MemberOf(u, parts[1])
			a.Show(
				"f is a homomorphism of the additive groups, and a group "+
					"homomorphism carries the inverse of u to the inverse of f(u)",
				By(group_homomorphism.MapInv.Read(HomGroup.Read(linear)).At(um)))
		}),
})}

// HomSum — a homomorphism carries a finite sum of vectors of M to the sum
// of their images in N: forgetting the scalars, f keeps the zero and
// carries a sum of two vectors of M to the sum of their images, and a map
// of the commutative monoid of M's vectors that does both carries every
// finite sum in it to the sum of the images.
var HomSum = homSumThm{family.Add(registry.ProofEntry{
	Name: "HomSum",
	Key:  "prop_3f193f69a22f72b2",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀M:module_ops(A, B). " +
			"∀N:module_ops(A, C). " +
			"∀f:(B → C). " +
			"∀s:set(D). " +
			"∀F:(D → B).",
		Hypotheses: []string{
			"module_homomorphism(R, M, N, f)",
			"finite(s) ∧ ∀x:D. x ∈ s ⇒ F(x) ∈ M.carrier",
		},
		Conclusion: "f(module_sum(M.add, M.zero, s, F)) = module_sum(N.add, N.zero, s, λx:D. f(F(x)))",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			N *Expr[ModuleOps[A, C]],
			f *Arrow[B, C],
			s *Expr[Set[D]],
			F *Arrow[D, B],
			hom, summable Fact,
		) {
			a.Show(
				"f keeps the zero and the sum of two vectors of M, so it keeps every finite sum of M's vectors",
				By(
					summable,
					HomZero.Read(hom),
					HomAdd.Read(hom),
					module.ModuleSumMonoidHomomorphism.Read(module.AddMonoidOn.Read(HomSource.Read(hom)))))
		}),
})}

// HomCombination — a homomorphism carries a finite combination of an
// indexed family of vectors of M to the combination of their images with
// the same coefficients: each term c(x) • F(x) is a vector of M, so f
// carries the sum of the terms to the sum of their images, and it carries
// each term to c(x) • f(F(x)).
var HomCombination = homCombinationThm{family.Add(registry.ProofEntry{
	Name: "HomCombination",
	Key:  "prop_badc6b3ea82149",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀M:module_ops(A, B). " +
			"∀N:module_ops(A, C). " +
			"∀f:(B → C). " +
			"∀s:set(D). " +
			"∀c:(D → A). " +
			"∀F:(D → B).",
		Hypotheses: []string{
			"module_homomorphism(R, M, N, f)",
			"finite(s) ∧ (∀x:D. x ∈ s ⇒ F(x) ∈ M.carrier) ∧ ∀x:D. x ∈ s ⇒ c(x) ∈ R.carrier",
		},
		Conclusion: "f(module_sum(M.add, M.zero, s, λx:D. c(x) • F(x))) = " +
			"module_sum(N.add, N.zero, s, λx:D. c(x) • f(F(x)))",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			N *Expr[ModuleOps[A, C]],
			f *Arrow[B, C],
			s *Expr[Set[D]],
			c *Arrow[D, A],
			F *Arrow[D, B],
			hom, given Fact,
		) {
			parts := a.Conjuncts(
				given,
				"s is finite",
				"F lies in M on s",
				"c is a scalar on s")
			finite, inM, scalars := parts[0], parts[1], parts[2]
			terms := a.Have(
				"each term c(x) • F(x) is a vector of M",
				"∀x:D. x ∈ s ⇒ c(x) • F(x) ∈ M.carrier",
				By(inM, scalars, module.SmulIn.Read(HomSource.Read(hom))))
			termwise := a.Have(
				"f carries each term c(x) • F(x) to c(x) • f(F(x))",
				"∀x:D. x ∈ s ⇒ f(c(x) • F(x)) = c(x) • f(F(x))",
				By(inM, scalars, HomSmul.Read(hom)))
			a.Show(
				"f carries the sum of the terms to the sum of their images, which are c(x) • f(F(x))",
				CalcEq(
					Leg(
						a.TermAs[C]("module_sum(N.add, N.zero, s, λx:D. f(c(x) • F(x)))"),
						"f keeps a finite sum of vectors of M",
						By(finite, terms, HomSum.Read(hom).At(s, a.TermAs[Fun[D, B]]("λx:D. c(x) • F(x)")))),
					FinalLeg(
						"and the sums agree term by term",
						By(termwise, module.ModuleSumCongruence)),
				))
		}),
})}

// KernelSubmodule — the kernel of a module homomorphism is a submodule of
// its source: it is the kernel of the homomorphism of additive groups, so a
// subgroup, and for a vector u that f sends to zero and a scalar c, the
// multiple c • u is a vector of M with f(c • u) = c • f(u) = c • 0 = 0.
var KernelSubmodule = kernelSubmoduleThm{family.Add(registry.ProofEntry{
	Name: "KernelSubmodule",
	Key:  "prop_b7c03cf6e9161528",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, C). ∀f:(B → C).",
		Hypotheses: []string{
			"module_homomorphism(R, M, N, f)",
		},
		Conclusion: "submodule(R, M, group_kernel(N.zero, M.carrier, f))",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			N *Expr[ModuleOps[A, C]],
			f *Arrow[B, C],
			hom Fact,
		) {
			additive := a.Have(
				"the kernel of the additive homomorphism is a subgroup of M",
				"subgroup(module_additive_group(M), group_kernel(N.zero, M.carrier, f))",
				By(group_homomorphism.KernelSubgroup.Read(HomGroup.Read(hom))))
			scalings := a.Have(
				"the kernel is closed under scaling",
				Statement{
					Binders: "∀c:A. ∀u:B.",
					Hypotheses: []string{
						"c ∈ R.carrier",
						"u ∈ group_kernel(N.zero, M.carrier, f)",
					},
					Conclusion: "c • u ∈ group_kernel(N.zero, M.carrier, f)",
				},
				Derive(func(b *Argument) {
					c, u := b.FixAs[A]("c"), b.FixAs[B]("u")
					given := b.Conjuncts(
						b.Assume(),
						"c is a scalar",
						"u lies in the kernel")
					point := b.Conjuncts(
						b.Simplified(given[1], Fwd(group_homomorphism.InKernel)),
						"u lies in M",
						"f sends u to zero")
					cm, um := proof.MemberOf(c, given[0]), proof.MemberOf(u, point[0])
					scaled := module.SmulIn.Read(HomSource.Read(hom)).At(cm, um)
					value := b.Have(
						"f sends c • u to zero",
						"f(c • u) = N.zero",
						CalcEq(
							Leg(
								b.TermAs[C]("c • f(u)"),
								"f is linear",
								By(HomSmul.Read(hom).At(cm, um))),
							FinalLeg(
								"f(u) is zero, and a multiple of zero is zero",
								point[1].Rw(),
								By(module.SmulZero.Read(HomTarget.Read(hom)).At(cm))),
						))
					b.Show(
						"c • u is a vector of M that f sends to zero",
						By(scaled, value, group_homomorphism.InKernel))
				}))
			a.Show(
				"a subgroup of M closed under scaling is a submodule",
				By(additive, scalings, submodule.SubmoduleDef))
		}),
})}

// ImageSubmodule — the image of a module homomorphism is a submodule of its
// target: it is the image of the homomorphism of additive groups, so a
// subgroup, and a multiple c • v of a point v = f(u) of the image is
// c • f(u) = f(c • u), the image of the vector c • u of M.
var ImageSubmodule = imageSubmoduleThm{family.Add(registry.ProofEntry{
	Name: "ImageSubmodule",
	Key:  "prop_e8cad132e3934bbb",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, C). ∀f:(B → C).",
		Hypotheses: []string{
			"module_homomorphism(R, M, N, f)",
		},
		Conclusion: "submodule(R, N, image(f, M.carrier))",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			N *Expr[ModuleOps[A, C]],
			f *Arrow[B, C],
			hom Fact,
		) {
			additive := a.Have(
				"the image of the additive homomorphism is a subgroup of N",
				"subgroup(module_additive_group(N), image(f, M.carrier))",
				By(group_homomorphism.ImageSubgroup.Read(HomGroup.Read(hom))))
			scalings := a.Have(
				"the image is closed under scaling",
				"∀c:A. ∀v:C. c ∈ R.carrier ∧ v ∈ image(f, M.carrier) ⇒ c • v ∈ image(f, M.carrier)",
				Derive(func(b *Argument) {
					c := b.FixAs[A]("c")
					b.FixAs[C]("v")
					given := b.Conjuncts(
						b.Assume(),
						"c is a scalar",
						"v lies in the image")
					u, preimage := b.UnpackAs[B](b.Simplified(given[1], Fwd(set_basic.InImage)), "u")
					point := b.Conjuncts(
						preimage,
						"v is f(u)",
						"u lies in M")
					cm, um := proof.MemberOf(c, given[0]), proof.MemberOf(u, point[1])
					scaled := module.SmulIn.Read(HomSource.Read(hom)).At(cm, um)
					value := b.Have(
						"f sends c • u to c • v",
						"f(c • u) = c • v",
						CalcEq(
							Leg(
								b.TermAs[C]("c • f(u)"),
								"f is linear",
								By(HomSmul.Read(hom).At(cm, um))),
							FinalLeg(
								"and f(u) is v",
								point[0].Rw(),
								Basic()),
						))
					b.Show(
						"c • v is the image of c • u, a vector of M",
						value.RwRev(),
						By(set_image.FunInImage, scaled))
				}))
			a.Show(
				"a subgroup of N closed under scaling is a submodule",
				By(additive, scalings, submodule.SubmoduleDef))
		}),
})}

// HomImageSubmodule — a homomorphism carries a submodule of M to a
// submodule of N: restricted to S, f is a homomorphism out of S under M's
// operations, and the image of a homomorphism is a submodule of its
// target.
var HomImageSubmodule = homImageSubmoduleThm{family.Add(registry.ProofEntry{
	Name: "HomImageSubmodule",
	Key:  "prop_de9ce6afb83f2fe9",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, C). ∀f:(B → C). ∀S:set(B).",
		Hypotheses: []string{
			"module_homomorphism(R, M, N, f)",
			"submodule(R, M, S)",
		},
		Conclusion: "submodule(R, N, image(f, S))",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			N *Expr[ModuleOps[A, C]],
			f *Arrow[B, C],
			S *Expr[Set[B]],
			given Fact,
		) {
			restricted := a.Have(
				"restricted to S, f is a homomorphism out of S under M's operations",
				"module_homomorphism(R, restrict_module(M, S), N, f)",
				By(given, HomRestrictSource.At(R, M, N, f, S)))
			a.Show(
				"its image of S, the restriction's carrier, is a submodule of N",
				By(ImageSubmodule.Read(restricted)))
		}),
})}

// HomPreimageSubmodule — a homomorphism pulls a submodule T of N back to
// a submodule of M: the vectors of M that f sends into T hold M.zero,
// which f sends to N.zero, a member of T; and with u and v they hold u + v
// and c • u, which f sends to f(u) + f(v) and c • f(u), again in T.
var HomPreimageSubmodule = homPreimageSubmoduleThm{family.Add(registry.ProofEntry{
	Name: "HomPreimageSubmodule",
	Key:  "prop_cac7a077b40ec1da",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, C). ∀f:(B → C). ∀T:set(C).",
		Hypotheses: []string{
			"module_homomorphism(R, M, N, f)",
			"submodule(R, N, T)",
		},
		Conclusion: "submodule(R, M, preimage_on(M.carrier, f, T))",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			N *Expr[ModuleOps[A, C]],
			f *Arrow[B, C],
			T *Expr[Set[C]],
			given Fact,
		) {
			parts := a.Conjuncts(
				given,
				"f is a homomorphism of M into N",
				"T is a submodule of N")
			linear, subT := parts[0], parts[1]
			source := HomSource.Read(linear)
			additive := module.AddGroupOn.Read(source)
			preimage := a.TermAs[Set[B]]("preimage_on(M.carrier, f, T)")
			inPreimage := a.Have(
				"the preimage holds the vectors of M that f sends into T",
				"∀v:B. v ∈ preimage_on(M.carrier, f, T) ⇔ v ∈ M.carrier ∧ f(v) ∈ T",
				Unfold(functions.PreimageOnDef),
				BySets())
			inM := a.Have(
				"so it lies in M",
				"preimage_on(M.carrier, f, T) ⊆ M.carrier",
				By(inPreimage, set_basic.SubsetDef.At(preimage, a.TermAs[Set[B]]("M.carrier"))))
			zeroIn := a.Have(
				"it holds M.zero, which f sends to N.zero, a member of T",
				"M.zero ∈ preimage_on(M.carrier, f, T)",
				By(
					inPreimage.At(a.TermAs[B]("M.zero")),
					HomZero.Read(linear),
					submodule.SubmoduleZero.Read(subT),
					group.OneIn.Read(additive)))
			addClosed := a.Have(
				"with u and v it holds u + v, which f sends to f(u) + f(v), in T",
				Statement{
					Binders: "∀u v:B.",
					Hypotheses: []string{
						"u ∈ preimage_on(M.carrier, f, T)",
						"v ∈ preimage_on(M.carrier, f, T)",
					},
					Conclusion: "u + v ∈ preimage_on(M.carrier, f, T)",
				},
				Derive(func(b *Argument) {
					u, v := b.FixAs[B]("u"), b.FixAs[B]("v")
					both := b.Assume()
					members := b.Have(
						"u and v lie in M and their images in T",
						"u ∈ M.carrier ∧ v ∈ M.carrier ∧ f(u) ∈ T ∧ f(v) ∈ T",
						By(both, inPreimage.At(u), inPreimage.At(v)))
					b.Show(
						"f(u + v) is f(u) + f(v), a sum of members of T",
						By(
							members,
							inPreimage.At(b.TermAs[B]("u + v")),
							At(HomAdd.Read(linear), u, v),
							At(group.MulIn.Read(additive), u, v),
							At(submodule.SubmoduleAdd.Read(subT), f.Apply(u), f.Apply(v))))
				}))
			smulClosed := a.Have(
				"and with u it holds c • u, which f sends to c • f(u), in T",
				Statement{
					Binders: "∀c:A. ∀u:B.",
					Hypotheses: []string{
						"c ∈ R.carrier",
						"u ∈ preimage_on(M.carrier, f, T)",
					},
					Conclusion: "c • u ∈ preimage_on(M.carrier, f, T)",
				},
				Derive(func(b *Argument) {
					c, u := b.FixAs[A]("c"), b.FixAs[B]("u")
					scaled := b.Assume()
					members := b.Have(
						"u lies in M and its image in T",
						"u ∈ M.carrier ∧ f(u) ∈ T",
						By(scaled, inPreimage.At(u)))
					b.Show(
						"f(c • u) is c • f(u), a multiple of a member of T",
						By(
							scaled,
							members,
							inPreimage.At(b.TermAs[B]("c • u")),
							At(HomSmul.Read(linear), c, u),
							At(module.SmulIn.Read(source), c, u),
							At(submodule.SubmoduleSmul.Read(subT), c, f.Apply(u))))
				}))
			a.Show(
				"so it is a submodule of M",
				By(inM, zeroIn, addClosed, smulClosed, submodule.SubmoduleCriterion.Read(source).At(preimage)))
		}),
})}

// HomIdentity — the identity map of an R-module is a homomorphism of the
// module into itself: the source and the target are both M, and since the
// identity sends each vector to itself, keeping the carrier, sums and scalar
// multiples is trivial.
var HomIdentity = homIdentityThm{family.Add(registry.ProofEntry{
	Name: "HomIdentity",
	Key:  "prop_df348627c6cbf6e3",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B).",
		Hypotheses: []string{
			"module_on(R, M)",
		},
		Conclusion: "module_homomorphism(R, M, M, identity_map)",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			moduleOn module.ModuleFact[on.R, on.M],
		) {
			a.Show(
				"the identity sends each vector to itself, so its three "+
					"map laws are trivial, and M is the module at both ends",
				Simp(Fwd(ModuleHomomorphismDef), Fwd(functions.IdentityApply)),
				By(moduleOn))
		}),
})}

// HomCompose — a composite of two module homomorphisms is a module
// homomorphism: g ∘ f runs from M, the source of f, to L, the target of g,
// both R-modules; it carries M into L through N; and a sum or a scalar
// multiple passes through f, landing among the vectors of N, where g's own
// laws carry it on to L.
var HomCompose = homComposeThm{family.Add(registry.ProofEntry{
	Name: "HomCompose",
	Key:  "prop_89887818bdb8d5e6",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀M:module_ops(A, B). " +
			"∀N:module_ops(A, C). " +
			"∀L:module_ops(A, D). " +
			"∀f:(B → C). " +
			"∀g:(C → D).",
		Hypotheses: []string{
			"module_homomorphism(R, M, N, f)",
			"module_homomorphism(R, N, L, g)",
		},
		Conclusion: "module_homomorphism(R, M, L, g ∘ f)",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			N *Expr[ModuleOps[A, C]],
			L *Expr[ModuleOps[A, D]],
			f *Arrow[B, C],
			g *Arrow[C, D],
			both Fact,
		) {
			homs := a.Conjuncts(
				both,
				"f is a homomorphism of M into N",
				"g is a homomorphism of N into L")
			first, second := homs[0], homs[1]
			into := a.Have(
				"g ∘ f carries M into L, f carrying M into N and g carrying N into L",
				"∀u:B. u ∈ M.carrier ⇒ g(f(u)) ∈ L.carrier",
				By(HomIn.Read(first), HomIn.Read(second)))
			sums := a.Have(
				"g ∘ f carries a sum to the sum of the values",
				"∀u v:B. u ∈ M.carrier ∧ v ∈ M.carrier ⇒ g(f(M.add(u, v))) = L.add(g(f(u)), g(f(v)))",
				Derive(func(b *Argument) {
					u, v := b.FixAs[B]("u"), b.FixAs[B]("v")
					members := b.Conjuncts(
						b.Assume(),
						"u lies in M",
						"v lies in M")
					um, vm := proof.MemberOf(u, members[0]), proof.MemberOf(v, members[1])
					fu := proof.MemberOf(f.Apply(u), b.Have(
						"f carries u into N",
						"f(u) ∈ N.carrier",
						By(HomIn.Read(first).At(um))))
					fv := proof.MemberOf(f.Apply(v), b.Have(
						"f carries v into N",
						"f(v) ∈ N.carrier",
						By(HomIn.Read(first).At(vm))))
					b.Show(
						"the sum passes through f, then through g",
						CalcEq(
							Leg(
								b.TermAs[D]("g(N.add(f(u), f(v)))"),
								"f carries u + v to f(u) + f(v)",
								By(Normalized, HomAdd.Read(first).At(um, vm))),
							FinalLeg(
								"g is additive at f(u) and f(v), which f puts in N",
								By(HomAdd.Read(second).At(fu, fv))),
						))
				}))
			multiples := a.Have(
				"g ∘ f carries a multiple to the multiple of the value",
				"∀c:A. ∀u:B. c ∈ R.carrier ∧ u ∈ M.carrier ⇒ g(f(M.smul(c, u))) = L.smul(c, g(f(u)))",
				Derive(func(b *Argument) {
					c, u := b.FixAs[A]("c"), b.FixAs[B]("u")
					members := b.Conjuncts(
						b.Assume(),
						"c is a scalar",
						"u lies in M")
					cm, um := proof.MemberOf(c, members[0]), proof.MemberOf(u, members[1])
					fu := proof.MemberOf(f.Apply(u), b.Have(
						"f carries u into N",
						"f(u) ∈ N.carrier",
						By(HomIn.Read(first).At(um))))
					b.Show(
						"the multiple passes through f, then through g",
						CalcEq(
							Leg(
								b.TermAs[D]("g(N.smul(c, f(u)))"),
								"f carries c • u to c • f(u)",
								By(Normalized, HomSmul.Read(first).At(cm, um))),
							FinalLeg(
								"g carries c • f(u) to c • g(f(u)), f(u) lying in N",
								By(HomSmul.Read(second).At(cm, fu))),
						))
				}))
			a.Show(
				"g ∘ f is the map u ↦ g(f(u)), and both modules, the "+
					"carrier map, additivity and linearity make it a homomorphism",
				Unfold(functions.ComposeApply),
				By(ModuleHomomorphismDef, HomSource.Read(first), HomTarget.Read(second), into, sums, multiples))
		}),
})}

// ScalingLinearOverSubring — scaling by a scalar c of S is linear over
// every subring T inside S: M is a module over T, its scalars restricted
// (module.ModuleRestrictScalars read over S), and scaling by c keeps the
// carrier, distributes over sums, and commutes with the scalars of T,
// since c commutes with them in S.
var ScalingLinearOverSubring = scalingLinearOverSubringThm{family.Add(registry.ProofEntry{
	Name: "ScalingLinearOverSubring",
	Key:  "prop_c5c8408cd84b6a86",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀S T:set(A). ∀M:module_ops(A, B). ∀c:A.",
		Hypotheses: []string{
			"module_on(restrict_ring(R, S), M)",
			"subring(R, T)",
			"T ⊆ S",
			"c ∈ S",
		},
		Conclusion: "module_homomorphism(restrict_ring(R, T), M, M, λu:B. c • u)",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			S, T *Expr[Set[A]],
			M *Expr[ModuleOps[A, B]],
			c *Expr[A],
			given Fact,
		) {
			parts := a.Conjuncts(
				given,
				"M is a module over S",
				"T is a subring of R",
				"T lies in S",
				"c is a scalar of S")
			overS, subringT, inS, cS := parts[0], parts[1], parts[2], parts[3]
			overT := a.Have(
				"M is a module over T, a subring of the scalars S",
				"module_on(restrict_ring(R, T), M)",
				By(
					Normalized,
					module.ModuleRestrictScalars.Read(overS).At(T),
					module_record.RestrictRingTwice.At(R, S, T),
					subringT,
					inS,
					comm_ring.SubringRestrict.At(R, T, S)))
			keeps := a.Have(
				"scaling by c keeps M's carrier",
				"∀u:B. u ∈ M.carrier ⇒ c • u ∈ M.carrier",
				By(module.SmulIn.Read(overS), cS))
			distributes := a.Have(
				"scaling by c distributes over a sum of vectors",
				"∀u v:B. u ∈ M.carrier ∧ v ∈ M.carrier ⇒ c • (u + v) = c • u + c • v",
				By(module.SmulAddLeft.Read(overS), cS))
			inside := a.Unfolded(inS, set_basic.SubsetDef)
			scalars := comm_ring.MulMonoidOn.Read(module.RingOn.Read(overS))
			commutes := a.Have(
				"scaling by c commutes with scaling by a scalar of T",
				"∀d:A. ∀u:B. d ∈ T ∧ u ∈ M.carrier ⇒ c • (d • u) = d • (c • u)",
				Derive(func(b *Argument) {
					d := b.FixAs[A]("d")
					u := b.FixAs[B]("u")
					guards := b.Conjuncts(
						b.Assume(),
						"d is a scalar of T",
						"u is a vector")
					dS := b.Have(
						"d is a scalar of S",
						"d ∈ S",
						By(inside, guards[0]))
					cm, dm, um := proof.MemberOf(c, cS), proof.MemberOf(d, dS), proof.MemberOf(u, guards[1])
					b.Show(
						"c • (d • u) = (c * d) • u = (d * c) • u = d • (c • u)",
						By(
							module.SmulMul.Read(overS).At(cm, dm, um),
							module.SmulMul.Read(overS).At(dm, cm, um),
							comm_monoid.CommOn.Read(scalars).At(cm, dm)))
				}))
			a.Show(
				"so scaling by c is a homomorphism over T: M is a module over "+
					"T, and scaling keeps the carrier, sums and the scalars of T",
				By(ModuleHomomorphismDef, overT, keeps, distributes, commutes))
		}),
})}

// HomCongruence — a map agreeing with a homomorphism on the source carrier is
// a homomorphism: sums and multiples of vectors of M lie in M, so wherever a
// law evaluates the map its values are the homomorphism's, and each law
// becomes the homomorphism's own.
var HomCongruence = homCongruenceThm{family.Add(registry.ProofEntry{
	Name: "HomCongruence",
	Key:  "prop_de7890b49ad95c3b",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, C). ∀f g:(B → C).",
		Hypotheses: []string{
			"module_homomorphism(R, M, N, f)",
			"∀x:B. x ∈ M.carrier ⇒ g(x) = f(x)",
		},
		Conclusion: "module_homomorphism(R, M, N, g)",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			N *Expr[ModuleOps[A, C]],
			f, g *Arrow[B, C],
			given Fact,
		) {
			parts := a.Conjuncts(
				given,
				"f is a homomorphism",
				"g agrees with f on M")
			linear, agree := parts[0], parts[1]
			source := HomSource.Read(linear)
			into := a.Have(
				"g carries M into N",
				"∀u:B. u ∈ M.carrier ⇒ g(u) ∈ N.carrier",
				Derive(func(b *Argument) {
					u := b.FixAs[B]("u")
					um := proof.MemberOf(u, b.Assume())
					atU := b.Have(
						"g is f at u",
						"g(u) = f(u)",
						By(agree.At(u), um))
					b.Show(
						"g(u) is f(u), a vector of N",
						atU.Rw(),
						By(HomIn.Read(linear).At(um)))
				}))
			sums := a.Have(
				"g carries a sum to the sum of the values",
				"∀u v:B. u ∈ M.carrier ∧ v ∈ M.carrier ⇒ g(M.add(u, v)) = N.add(g(u), g(v))",
				Derive(func(b *Argument) {
					u, v := b.FixAs[B]("u"), b.FixAs[B]("v")
					members := b.Conjuncts(
						b.Assume(),
						"u lies in M",
						"v lies in M")
					um, vm := proof.MemberOf(u, members[0]), proof.MemberOf(v, members[1])
					sum := group.MulIn.Read(module.AddGroupOn.Read(source)).At(um, vm)
					atSum := b.Have(
						"g is f at u + v, a vector of M",
						"g(M.add(u, v)) = f(M.add(u, v))",
						By(agree.At(sum), sum))
					atU := b.Have(
						"g is f at u",
						"g(u) = f(u)",
						By(agree.At(u), um))
					atV := b.Have(
						"g is f at v",
						"g(v) = f(v)",
						By(agree.At(v), vm))
					b.Show(
						"with g read as f at u + v, u and v, this is the additivity of f",
						atSum.Rw(),
						atU.Rw(),
						atV.Rw(),
						By(HomAdd.Read(linear).At(um, vm)))
				}))
			multiples := a.Have(
				"g carries a multiple to the multiple of the value",
				"∀c:A. ∀u:B. c ∈ R.carrier ∧ u ∈ M.carrier ⇒ g(M.smul(c, u)) = N.smul(c, g(u))",
				Derive(func(b *Argument) {
					c, u := b.FixAs[A]("c"), b.FixAs[B]("u")
					members := b.Conjuncts(
						b.Assume(),
						"c is a scalar",
						"u lies in M")
					cm, um := proof.MemberOf(c, members[0]), proof.MemberOf(u, members[1])
					multiple := module.SmulIn.Read(source).At(cm, um)
					atMultiple := b.Have(
						"g is f at c • u, a vector of M",
						"g(M.smul(c, u)) = f(M.smul(c, u))",
						By(agree.At(multiple), multiple))
					atU := b.Have(
						"g is f at u",
						"g(u) = f(u)",
						By(agree.At(u), um))
					b.Show(
						"with g read as f at c • u and u, this is the linearity of f",
						atMultiple.Rw(),
						atU.Rw(),
						By(HomSmul.Read(linear).At(cm, um)))
				}))
			a.Show(
				"both modules, the carrier map, additivity and linearity make g a homomorphism",
				By(ModuleHomomorphismDef, source, HomTarget.Read(linear), into, sums, multiples))
		}),
})}

// HomPointwiseNeg — the pointwise negative of a homomorphism is a
// homomorphism: -f(u) lies in N, the negative of f(u) + f(v) regroups in N
// into -f(u) + -f(v), and c • -f(u) is -(c • f(u)).
var HomPointwiseNeg = homPointwiseNegThm{family.Add(registry.ProofEntry{
	Name: "HomPointwiseNeg",
	Key:  "prop_eaaa1d1aeb4c0da2",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, C). ∀f:(B → C).",
		Hypotheses: []string{
			"module_homomorphism(R, M, N, f)",
		},
		Conclusion: "module_homomorphism(R, M, N, λu:B. -f(u))",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			N *Expr[ModuleOps[A, C]],
			f *Arrow[B, C],
			hom Fact,
		) {
			a.Show(
				"both modules hold, and the three map laws of the negative follow in N from those of f",
				Simp(Fwd(ModuleHomomorphismDef)),
				ByChase(Depth(0), HomSource.Read(hom), HomTarget.Read(hom), hom))
		}),
})}

// HomDiff — the difference of two linear maps is linear: it is the
// pointwise sum of f and the pointwise negative of g.
var HomDiff = homDiffThm{family.Add(registry.ProofEntry{
	Name: "HomDiff",
	Key:  "prop_180f05d9a4f7de37",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, C). ∀f g:(B → C).",
		Hypotheses: []string{
			"module_homomorphism(R, M, N, f)",
			"module_homomorphism(R, M, N, g)",
		},
		Conclusion: "module_homomorphism(R, M, N, λu:B. N.add(f(u), N.neg(g(u))))",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			N *Expr[ModuleOps[A, C]],
			f, g *Arrow[B, C],
			both Fact,
		) {
			homs := a.Conjuncts(
				both,
				"f is a homomorphism of M into N",
				"so is g")
			a.Show(
				"the pointwise sum of f and the negative of g is linear",
				By(HomPointwiseNeg.Read(homs[1]), HomPointwiseSum.Read(homs[0])))
		}),
})}

// HomPointwiseSum — the pointwise sum of two homomorphisms is a
// homomorphism: f(u) + g(u) lies in N, the sum at u + v regroups in N into
// the sum at u plus the sum at v, and c distributes over f(u) + g(u).
var HomPointwiseSum = homPointwiseSumThm{family.Add(registry.ProofEntry{
	Name: "HomPointwiseSum",
	Key:  "prop_d697af096432bf3d",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, C). ∀f g:(B → C).",
		Hypotheses: []string{
			"module_homomorphism(R, M, N, f)",
			"module_homomorphism(R, M, N, g)",
		},
		Conclusion: "module_homomorphism(R, M, N, λu:B. f(u) + g(u))",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			N *Expr[ModuleOps[A, C]],
			f, g *Arrow[B, C],
			both Fact,
		) {
			homs := a.Conjuncts(
				both,
				"f is a homomorphism of M into N",
				"so is g")
			a.Show(
				"both modules hold, and the three map laws of the sum follow in N from those of f and g",
				Simp(Fwd(ModuleHomomorphismDef)),
				ByChase(Depth(0), HomSource.Read(homs[0]), HomTarget.Read(homs[0]), homs[0], homs[1]))
		}),
})}

// HomScalarMultiple — a scalar multiple of a homomorphism is a
// homomorphism: c • f(u) lies in N, c distributes over f(u) + f(v), and
// c • (d • f(u)) is d • (c • f(u)), the scalars commuting.
var HomScalarMultiple = homScalarMultipleThm{family.Add(registry.ProofEntry{
	Name: "HomScalarMultiple",
	Key:  "prop_3cafbcefb0581f00",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, C). ∀f:(B → C). ∀c:A.",
		Hypotheses: []string{
			"module_homomorphism(R, M, N, f)",
			"c ∈ R.carrier",
		},
		Conclusion: "module_homomorphism(R, M, N, λu:B. c • f(u))",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			N *Expr[ModuleOps[A, C]],
			f *Arrow[B, C],
			c *Expr[A],
			given Fact,
		) {
			parts := a.Conjuncts(
				given,
				"f is a homomorphism of M into N",
				"c is a scalar")
			hom, scalar := parts[0], parts[1]
			a.Show(
				"both modules hold, and the three map laws of the multiple follow in N from those of f",
				Simp(Fwd(ModuleHomomorphismDef)),
				ByChase(Depth(0), HomSource.Read(hom), HomTarget.Read(hom), hom, scalar))
		}),
})}

// HomRestrictSource — a homomorphism restricted to a submodule S of M is
// a homomorphism out of S, under M's operations: S is then a module, a
// submodule being a module under the ambient operations, and S lies in
// M's carrier, so f carries it into N and is additive and linear on it.
var HomRestrictSource = homRestrictSourceThm{family.Add(registry.ProofEntry{
	Name: "HomRestrictSource",
	Key:  "prop_f780ac5cb2e29ce8",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, C). ∀f:(B → C). ∀S:set(B).",
		Hypotheses: []string{
			"module_homomorphism(R, M, N, f)",
			"submodule(R, M, S)",
		},
		Conclusion: "module_homomorphism(R, restrict_module(M, S), N, f)",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			N *Expr[ModuleOps[A, C]],
			f *Arrow[B, C],
			S *Expr[Set[B]],
			given Fact,
		) {
			parts := a.Conjuncts(
				given,
				"f is a homomorphism of M into N",
				"S is a submodule of M")
			hom, sub := parts[0], parts[1]
			source := a.Have(
				"S under M's operations is an R-module",
				"module_on(R, restrict_module(M, S))",
				By(submodule.SubmoduleModuleOn.Read(HomSource.Read(hom)), sub))
			within := a.Unfolded(submodule.SubmoduleSubset.Read(sub).AsFact(), set_basic.SubsetDef)
			into := a.Have(
				"f carries S into N, S lying in M's carrier",
				"∀u:B. u ∈ S ⇒ f(u) ∈ N.carrier",
				By(HomIn.Read(hom), within))
			sums := a.Have(
				"f carries a sum of vectors of S to the sum of the values",
				"∀u v:B. u ∈ S ∧ v ∈ S ⇒ f(M.add(u, v)) = N.add(f(u), f(v))",
				By(HomAdd.Read(hom), within))
			multiples := a.Have(
				"f carries a multiple of a vector of S to the multiple of the value",
				"∀c:A. ∀u:B. c ∈ R.carrier ∧ u ∈ S ⇒ f(M.smul(c, u)) = N.smul(c, f(u))",
				By(HomSmul.Read(hom), within))
			a.Show(
				"S and N are modules, f carries S into N, and f is additive and linear on S",
				By(ModuleHomomorphismDef, source, HomTarget.Read(hom), into, sums, multiples))
		}),
})}

// HomCorestrict — a homomorphism whose values lie in a submodule T of N
// is a homomorphism into T, under N's operations: T is then a module, a
// submodule being a module under the ambient operations, and a sum or a
// multiple in T is the one in N.
var HomCorestrict = homCorestrictThm{family.Add(registry.ProofEntry{
	Name: "HomCorestrict",
	Key:  "prop_3d12a32284c64547",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, C). ∀f:(B → C). ∀T:set(C).",
		Hypotheses: []string{
			"module_homomorphism(R, M, N, f)",
			"submodule(R, N, T)",
			"∀u:B. u ∈ M.carrier ⇒ f(u) ∈ T",
		},
		Conclusion: "module_homomorphism(R, M, restrict_module(N, T), f)",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			N *Expr[ModuleOps[A, C]],
			f *Arrow[B, C],
			T *Expr[Set[C]],
			given Fact,
		) {
			parts := a.Conjuncts(
				given,
				"f is a homomorphism of M into N",
				"T is a submodule of N",
				"f carries M into T")
			hom, sub, into := parts[0], parts[1], parts[2]
			target := a.Have(
				"T under N's operations is an R-module",
				"module_on(R, restrict_module(N, T))",
				By(submodule.SubmoduleModuleOn.Read(HomTarget.Read(hom)), sub))
			a.Show(
				"M and T are modules, f carries M into T, and its sums and multiples are N's",
				By(ModuleHomomorphismDef, HomSource.Read(hom), target, into, HomAdd.Read(hom), HomSmul.Read(hom)))
		}),
})}

// HomRestrict — a homomorphism carrying a submodule S of its source into a
// submodule T of its target is a homomorphism from S to T, each under its
// module's operations: restricted to S it is a homomorphism out of S, and
// its values on S lie in T.
var HomRestrict = homRestrictThm{family.Add(registry.ProofEntry{
	Name: "HomRestrict",
	Key:  "prop_6e89a692b242848c",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀M:module_ops(A, B). " +
			"∀N:module_ops(A, C). " +
			"∀f:(B → C). " +
			"∀S:set(B). " +
			"∀T:set(C).",
		Hypotheses: []string{
			"module_homomorphism(R, M, N, f)",
			"submodule(R, M, S)",
			"submodule(R, N, T)",
			"∀u:B. u ∈ S ⇒ f(u) ∈ T",
		},
		Conclusion: "module_homomorphism(R, restrict_module(M, S), restrict_module(N, T), f)",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			N *Expr[ModuleOps[A, C]],
			f *Arrow[B, C],
			S *Expr[Set[B]],
			T *Expr[Set[C]],
			given Fact,
		) {
			parts := a.Conjuncts(
				given,
				"f is a homomorphism of M into N",
				"S is a submodule of M",
				"T is a submodule of N",
				"f carries S into T")
			hom, sourceSubmodule, targetSubmodule, into := parts[0], parts[1], parts[2], parts[3]
			restricted := a.Have(
				"restricted to S, f is a homomorphism out of S",
				"module_homomorphism(R, restrict_module(M, S), N, f)",
				By(hom, sourceSubmodule, HomRestrictSource.At(R, M, N, f, S)))
			a.Show(
				"its values on S lie in T, so it is a homomorphism into T",
				By(
					restricted,
					targetSubmodule,
					into,
					HomCorestrict.At(R, a.TermAs[ModuleOps[A, B]]("restrict_module(M, S)"), N, f, T)))
		}),
})}

// ProjectionHom — the projection u ↦ u + K of an R-module onto its
// quotient by a submodule K is a module homomorphism: the cosets of K form
// an R-module; the coset of a vector of M is its image under the coset
// map, so a coset of K in M; the sum of the cosets of u and v is the coset
// of u + v, K being normal in the additive group of M; and c times the
// coset of u is the coset of c • u.
var ProjectionHom = projectionHomThm{family.Add(registry.ProofEntry{
	Name: "ProjectionHom",
	Key:  "prop_bccc72ae9bf31f0f",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀K:set(B).",
		Hypotheses: []string{
			"module_on(R, M)",
			"submodule(R, M, K)",
		},
		Conclusion: "module_homomorphism(R, M, quotient_module(M, K), coset_map(M.add, K))",
	},
		func(a *Argument, R *Expr[RingOps[A]], M *Expr[ModuleOps[A, B]], K *Expr[Set[B]], given Fact) {
			parts := a.Conjuncts(
				given,
				"M is an R-module",
				"K is a submodule of M")
			ambient, sub := parts[0], parts[1]
			additive := module.AddGroupOn.Read(ambient)
			a.Have(
				"K lies in M's carrier",
				"K ⊆ M.carrier",
				By(submodule.SubmoduleSubset.Read(sub)))
			into := a.Have(
				"the cosets of K are the image of M's carrier under "+
					"the coset map, so the coset of a vector of M is one",
				"∀u:B. u ∈ M.carrier ⇒ left_coset(M.add, u, K) ∈ left_cosets(M.add, M.carrier, K)",
				Simp(Fwd(quotient_group.LeftCosetsImage.Read(additive)), Fwd(group.CosetMapDef)),
				By(set_image.FunInImage))
			sums := a.Have(
				"the sum of two cosets is the coset of the sum, K being normal in the additive group of M",
				Statement{
					Binders: "∀u v:B.",
					Hypotheses: []string{
						"u ∈ M.carrier",
						"v ∈ M.carrier",
					},
					Conclusion: "set_mul(M.add, left_coset(M.add, u, K), left_coset(M.add, v, K)) = " +
						"left_coset(M.add, u + v, K)",
				},
				By(sub, submodule.SubmoduleNormal.Read(ambient), quotient_group.LeftCosetMulOn.Read(additive)))
			multiples := a.Have(
				"a scaled coset is the coset of the scaled vector",
				Statement{
					Binders: "∀c:A. ∀u:B.",
					Hypotheses: []string{
						"c ∈ R.carrier",
						"u ∈ M.carrier",
					},
					Conclusion: "quotient_smul(M.add, M.smul, K, c, left_coset(M.add, u, K)) = " +
						"left_coset(M.add, c • u, K)",
				},
				By(sub, submodule.QuotientSmulCoset.Read(ambient)))
			a.Show(
				"M and the quotient module by K, the carrier map, "+
					"additivity and linearity make the projection a homomorphism",
				Simp(Fwd(group.CosetMapDef)),
				By(
					ModuleHomomorphismDef,
					ambient,
					sub,
					submodule.QuotientModuleOn.Read(ambient),
					into,
					sums,
					multiples))
		}),
})}

// ProductModuleOn — the product of two modules is a module, with the two
// inclusions u ↦ (u, 0), n ↦ (0, n) and the first projection
// homomorphisms. A pair is some (x, y); it lies in M × N when x lies in M
// and y in N, two pairs are equal when their components are, and every
// operation acts on each component, so each module condition on the pairs
// is that condition on x in M beside the same condition on y in N. The
// inclusions keep sums and multiples because 0 + 0 and c • 0 are 0, and
// the projection reads off the first component.
var ProductModuleOn = productModuleOnThm{family.Add(registry.ProofEntry{
	Name: "ProductModuleOn",
	Key:  "prop_d05d42243bff3e79",
	Reading: "The direct sum M ⊕ N of two modules over the same ring: its " +
		"zero is (M.zero, N.zero), and each inclusion pads with the other " +
		"factor's zero. Of the two projections only z ↦ fst(z) is stated.",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, C).",
		Hypotheses: []string{
			"module_on(R, M)",
			"module_on(R, N)",
		},
		Conclusion: "module_on(R, product_module(M, N)) ∧ " +
			"module_homomorphism(R, M, product_module(M, N), λu:B. (u, N.zero)) ∧ " +
			"module_homomorphism(R, N, product_module(M, N), λn:C. (M.zero, n)) ∧ " +
			"module_homomorphism(R, product_module(M, N), M, λz:prod(B, C). fst(z))",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			N *Expr[ModuleOps[A, C]],
			given Fact,
		) {
			parts := a.Conjuncts(
				given,
				"M is an R-module",
				"N is an R-module")
			left, right := parts[0], parts[1]
			groupM, groupN := module.AddGroupOn.Read(left), module.AddGroupOn.Read(right)
			// A condition on pairs reads as the same condition on their
			// components: every pair is (x, y), membership in M × N and
			// equality of pairs go component by component, and fst and snd
			// read the components off — each pair law taken at the pairs of
			// a vector of M and one of N. componentwise closes the condition
			// so read by the laws of M and of N it names.
			atM, atN := TypeBinder.BindA[B](), TypeBinder.BindB[C]()
			components := Simp(
				Fwd(pairs.ForallPair.Inst(atM, atN)),
				Fwd(pairs.Fst.Inst(atM, atN)),
				Fwd(pairs.Snd.Inst(atM, atN)),
				Fwd(set_product.InCross.Inst(atM, atN)),
				Fwd(pairs.PairEq.Inst(atM, atN)))
			componentwise := func(laws ...any) Action { return Chain(components, By(laws...)) }
			product := a.Have(
				"the pairs form an R-module under the componentwise operations",
				"module_on(R, product_module(M, N))",
				Simp(Fwd(module.ModuleOn.Inst(TypeBinder.BindA[A](), TypeBinder.BindB[Prod[B, C]]()))),
				Unfold(group.GroupOn),
				SplitConjAll(
					Case(
						"the scalars are M's ring",
						By(module.RingOn.Read(left))),
					Case(
						"the zero pair lies in M × N",
						componentwise(group.OneIn.Read(groupM), group.OneIn.Read(groupN))),
					Case(
						"a sum of pairs lies in M × N",
						componentwise(group.MulIn.Read(groupM), group.MulIn.Read(groupN))),
					Case(
						"so does a negative",
						componentwise(group.InvIn.Read(groupM), group.InvIn.Read(groupN))),
					Case(
						"the sum associates componentwise",
						componentwise(group.AssocOn.Read(groupM), group.AssocOn.Read(groupN))),
					Case(
						"the zero pair is a left identity componentwise",
						componentwise(group.LeftIdentityOn.Read(groupM), group.LeftIdentityOn.Read(groupN))),
					Case(
						"the negative is a left inverse componentwise",
						componentwise(group.LeftInverseOn.Read(groupM), group.LeftInverseOn.Read(groupN))),
					Case(
						"the sum commutes componentwise",
						componentwise(module.AddComm.Read(left), module.AddComm.Read(right))),
					Case(
						"a scaled pair lies in M × N",
						componentwise(module.SmulIn.Read(left), module.SmulIn.Read(right))),
					Case(
						"a scalar distributes over a sum componentwise",
						componentwise(module.SmulAddLeft.Read(left), module.SmulAddLeft.Read(right))),
					Case(
						"a sum of scalars distributes componentwise",
						componentwise(module.SmulAddRight.Read(left), module.SmulAddRight.Read(right))),
					Case(
						"scaling by a product is scaling twice componentwise",
						componentwise(module.SmulMul.Read(left), module.SmulMul.Read(right))),
					Case(
						"and one fixes every pair",
						componentwise(module.SmulOne.Read(left), module.SmulOne.Read(right))),
				))
			first := a.Have(
				"u ↦ (u, 0) keeps sums and multiples, the second "+
					"components being 0 + 0 and c • 0, which are 0 in N",
				"module_homomorphism(R, M, product_module(M, N), λu:B. (u, N.zero))",
				Unfold(ModuleHomomorphismDef),
				componentwise(
					left,
					product,
					group.OneIn.Read(groupN),
					group.LeftIdentityOn.Read(groupN),
					module.SmulZero.Read(right)))
			second := a.Have(
				"n ↦ (0, n) keeps them likewise, 0 + 0 and c • 0 being 0 in M",
				"module_homomorphism(R, N, product_module(M, N), λn:C. (M.zero, n))",
				Unfold(ModuleHomomorphismDef),
				componentwise(
					right,
					product,
					group.OneIn.Read(groupM),
					group.LeftIdentityOn.Read(groupM),
					module.SmulZero.Read(left)))
			projection := a.Have(
				"z ↦ fst(z) reads off the first component, which lies in M and is added and scaled in M",
				"module_homomorphism(R, product_module(M, N), M, λz:prod(B, C). fst(z))",
				Unfold(ModuleHomomorphismDef),
				By(product, left, set_product.InCrossProjections, pairs.Fst))
			a.Show(
				"so the product is a module, the two inclusions and the first projection homomorphisms",
				By(product, first, second, projection))
		}),
})}

// ProjectionKernel — the projection of an R-module M onto its quotient by
// a submodule K has kernel K: the vectors of M whose coset is K itself are
// the vectors of K. A submodule is a subgroup of the additive group of M,
// and this is ProjectionKernelOn at the additive group.
var ProjectionKernel = projectionKernelThm{family.Add(registry.ProofEntry{
	Name: "ProjectionKernel",
	Key:  "prop_b69108c8ab432b90",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀K:set(B).",
		Hypotheses: []string{
			"module_on(R, M)",
			"submodule(R, M, K)",
		},
		Conclusion: "group_kernel(K, M.carrier, coset_map(M.add, K)) = K",
	},
		func(a *Argument, R *Expr[RingOps[A]], M *Expr[ModuleOps[A, B]], K *Expr[Set[B]], given Fact) {
			parts := a.Conjuncts(
				given,
				"M is an R-module",
				"K is a submodule of M")
			ambient, sub := parts[0], parts[1]
			a.Show(
				"K is a subgroup of the additive group of M, whose coset map has kernel K",
				By(
					quotient_group.ProjectionKernelOn.Read(module.AddGroupOn.Read(ambient)).At(K),
					submodule.SubmoduleSubgroup.Read(sub)))
		}),
})}

// QuotientRelationHom — related representatives compute a map on quotient
// classes, and closure of the relation makes that map linear.
var QuotientRelationHom = quotientRelationHomThm{family.Add(registry.ProofEntry{
	Name: "QuotientRelationHom",
	Key:  "prop_c3c2458512c81ab6",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀M:module_ops(A, B). " +
			"∀N:module_ops(A, C). " +
			"∀K:set(B). " +
			"∀L:set(C). " +
			"∀T:(B → C → bool). " +
			"∀f:(set(B) → set(C)).",
		Hypotheses: []string{
			"module_on(R, M)",
			"module_on(R, N)",
			"submodule(R, M, K)",
			"submodule(R, N, L)",
			"∀u:B. u ∈ M.carrier ⇒ ∃v:C. v ∈ N.carrier ∧ T(u, v)",
			"∀u v:B. ∀x y:C. " +
				"    u ∈ M.carrier ∧ v ∈ M.carrier ∧ x ∈ N.carrier ∧ y ∈ N.carrier ∧ T(u, x) ∧ T(v, y) ⇒ " +
				"    T(M.add(u, v), N.add(x, y))",
			"∀c:A. ∀u:B. ∀v:C. " +
				"    c ∈ R.carrier ∧ u ∈ M.carrier ∧ v ∈ N.carrier ∧ T(u, v) ⇒ T(M.smul(c, u), N.smul(c, v))",
			"∀u:B. ∀v:C. " +
				"    u ∈ M.carrier ∧ v ∈ N.carrier ∧ T(u, v) ⇒ " +
				"    f(left_coset(M.add, u, K)) = left_coset(N.add, v, L)",
		},
		Conclusion: "module_homomorphism(R, quotient_module(M, K), quotient_module(N, L), f)",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			N *Expr[ModuleOps[A, C]],
			K *Expr[Set[B]],
			L *Expr[Set[C]],
			T *Arrow2[B, C, Bool],
			f *Arrow[Set[B], Set[C]],
			given Fact,
		) {
			a.Do(Simp(Fwd(ModuleHomomorphismDef.Inst(
				TypeBinder.BindA[A](), TypeBinder.BindB[Set[B]](), TypeBinder.BindC[Set[C]]()))))
			parts := a.Conjuncts(
				given,
				"M is an R-module",
				"N is an R-module",
				"K is a submodule of M",
				"L is a submodule of N",
				"every source element has a related target element",
				"related pairs are closed under addition",
				"related pairs are closed under scaling",
				"related pairs give the values on classes")
			source, target, sourceSubmodule, targetSubmodule := parts[0], parts[1], parts[2], parts[3]
			total, add, scale, value := parts[4], parts[5], parts[6], parts[7]
			// A class is read from a representative: K and L lie in the
			// carriers, so the classes are the images of the carriers under
			// the coset maps of the two additive groups.
			sourceAdditive, targetAdditive := module.AddGroupOn.Read(source), module.AddGroupOn.Read(target)
			a.Have(
				"K lies in M's carrier",
				"K ⊆ M.carrier",
				By(submodule.SubmoduleSubset.Read(sourceSubmodule)))
			a.Have(
				"L lies in N's carrier",
				"L ⊆ N.carrier",
				By(submodule.SubmoduleSubset.Read(targetSubmodule)))
			a.Do(SplitConjAll(
				Case(
					"the source quotient is an R-module",
					By(sourceSubmodule, submodule.QuotientModuleOn.Read(source))),
				Case(
					"the target quotient is an R-module",
					By(targetSubmodule, submodule.QuotientModuleOn.Read(target))),
				Case(
					"the map carries a source class to a target class",
					Derive(func(b *Argument) {
						b.Do(Simp(Fwd(quotient_group.ForallInLeftCosets.Read(sourceAdditive))))
						u := b.FixAs[B]("u")
						uIn := b.Assume()
						v, related := b.ObtainAs[C](
							"u has a related element v in N",
							"∃v:C. v ∈ N.carrier ∧ T(u, v)",
							By(uIn, total))
						image := b.Have(
							"f sends u + K to the class of v",
							"f(left_coset(M.add, u, K)) = left_coset(N.add, v, L)",
							By(uIn, related, value.At(u, v)))
						b.Do(Simp(Fwd(quotient_group.InLeftCosets.Read(targetAdditive))))
						b.Take(v)
						b.Show(
							"the image is represented by v in N",
							By(image, related))
					})),
				Case(
					"the map preserves addition of classes",
					Derive(func(b *Argument) {
						b.Do(Simp(Fwd(quotient_group.ForallInLeftCosetsPair.Read(sourceAdditive))))
						u := b.FixAs[B]("u")
						v := b.FixAs[B]("v")
						representatives := b.Conjuncts(
							b.Assume(),
							"u lies in M",
							"v lies in M")
						uIn, vIn := representatives[0], representatives[1]
						x, relatedU := b.ObtainAs[C](
							"u has a related element x in N",
							"∃x:C. x ∈ N.carrier ∧ T(u, x)",
							By(uIn, total))
						y, relatedV := b.ObtainAs[C](
							"v has a related element y in N",
							"∃y:C. y ∈ N.carrier ∧ T(v, y)",
							By(vIn, total))
						sourceNormal := b.Have(
							"K is normal in the additive group of M",
							"normal_subgroup(module_additive_group(M), K)",
							By(sourceSubmodule, submodule.SubmoduleNormal.Read(source)))
						targetNormal := b.Have(
							"L is normal in the additive group of N",
							"normal_subgroup(module_additive_group(N), L)",
							By(targetSubmodule, submodule.SubmoduleNormal.Read(target)))
						sourceSum := b.Have(
							"u plus v lies in M",
							"M.add(u, v) ∈ M.carrier",
							By(uIn, vIn, group.MulIn.Read(sourceAdditive)))
						targetSum := b.Have(
							"x plus y lies in N",
							"N.add(x, y) ∈ N.carrier",
							By(relatedU, relatedV, group.MulIn.Read(targetAdditive)))
						relatedSum := b.Have(
							"the sums are related",
							"T(M.add(u, v), N.add(x, y))",
							By(uIn, vIn, relatedU, relatedV, add))
						imageU := b.Have(
							"f sends u + K to the class of x",
							"f(left_coset(M.add, u, K)) = left_coset(N.add, x, L)",
							By(uIn, relatedU, value.At(u, x)))
						imageV := b.Have(
							"f sends v + K to the class of y",
							"f(left_coset(M.add, v, K)) = left_coset(N.add, y, L)",
							By(vIn, relatedV, value.At(v, y)))
						imageSum := b.Have(
							"f sends the class of the source sum to the class of the target sum",
							"f(left_coset(M.add, M.add(u, v), K)) = left_coset(N.add, N.add(x, y), L)",
							By(sourceSum, targetSum, relatedSum, value))
						sumClass := b.Have(
							"the sum of u + K and v + K is represented by u plus v",
							"set_mul(M.add, left_coset(M.add, u, K), left_coset(M.add, v, K)) = "+
								"left_coset(M.add, M.add(u, v), K)",
							By(uIn, vIn, sourceNormal, quotient_group.LeftCosetMulOn.Read(sourceAdditive)))
						sumImages := b.Have(
							"the sum of the image classes is represented by x plus y",
							"set_mul(N.add, left_coset(N.add, x, L), left_coset(N.add, y, L)) = "+
								"left_coset(N.add, N.add(x, y), L)",
							By(relatedU, relatedV, targetNormal, quotient_group.LeftCosetMulOn.Read(targetAdditive)))
						b.Show(
							"the two sums have the same target class",
							sumClass.Rw(),
							imageSum.Rw(),
							imageU.Rw(),
							imageV.Rw(),
							sumImages.Rw(),
							Basic())
					})),
				Case(
					"the map preserves scalar multiplication of classes",
					Derive(func(b *Argument) {
						curried := b.Have(
							"for each scalar c, the map carries c times a class to c times its image",
							"∀c:A. "+
								"    c ∈ R.carrier ⇒ "+
								"    ∀s:set(B). "+
								"        s ∈ left_cosets(M.add, M.carrier, K) ⇒ "+
								"        f(quotient_smul(M.add, M.smul, K, c, s)) = quotient_smul(N.add, N.smul, L, c, f(s))",
							Derive(func(d *Argument) {
								d.FixAs[A]("c")
								scalar := d.Assume()
								d.Do(Simp(Fwd(quotient_group.ForallInLeftCosets.Read(sourceAdditive))))
								u := d.FixAs[B]("u")
								uIn := d.Assume()
								v, related := d.ObtainAs[C](
									"u has a related element v in N",
									"∃v:C. v ∈ N.carrier ∧ T(u, v)",
									By(uIn, total))
								sourceScaled := d.Have(
									"the scaled representative lies in M",
									"M.smul(c, u) ∈ M.carrier",
									By(scalar, uIn, module.SmulIn.Read(source)))
								targetScaled := d.Have(
									"the scaled related element lies in N",
									"N.smul(c, v) ∈ N.carrier",
									By(scalar, related, module.SmulIn.Read(target)))
								relatedScaled := d.Have(
									"the scaled elements are related",
									"T(M.smul(c, u), N.smul(c, v))",
									By(scalar, uIn, related, scale))
								image := d.Have(
									"f sends u + K to the class of v",
									"f(left_coset(M.add, u, K)) = left_coset(N.add, v, L)",
									By(uIn, related, value.At(u, v)))
								imageScaled := d.Have(
									"f sends the scaled source class to the scaled target class",
									"f(left_coset(M.add, M.smul(c, u), K)) = left_coset(N.add, N.smul(c, v), L)",
									By(sourceScaled, targetScaled, relatedScaled, value))
								scaledClass := d.Have(
									"c times u + K is represented by c times u",
									"quotient_smul(M.add, M.smul, K, c, left_coset(M.add, u, K)) = left_coset(M.add, M.smul(c, u), K)",
									By(scalar, uIn, sourceSubmodule, submodule.QuotientSmulCoset.Read(source)))
								scaledImage := d.Have(
									"the scalar multiple of the image class is represented by c times v",
									"quotient_smul(N.add, N.smul, L, c, left_coset(N.add, v, L)) = left_coset(N.add, N.smul(c, v), L)",
									By(scalar, related, targetSubmodule, submodule.QuotientSmulCoset.Read(target)))
								d.Show(
									"the scalar multiples have the same target class",
									scaledClass.Rw(),
									imageScaled.Rw(),
									image.Rw(),
									scaledImage.Rw(),
									Basic())
							}))
						b.Show(
							"the claim is the curried one with its two guards joined",
							By(curried))
					})),
			))
		}),
})}

// QuotientInclusionHom — for submodules K ⊆ X and L ⊆ Y of V with
// X ⊆ Y and K ⊆ L, the map X/K → Y/L sending a class to the class it
// lies in, u + K ↦ u + L, is linear: the relation u = v between
// representatives is total, closed under sums and scaling, and computes
// the map on cosets, L absorbing K (quotient_group.LeftCosetSetMulAbsorb).
var QuotientInclusionHom = quotientInclusionHomThm{family.Add(registry.ProofEntry{
	Name: "QuotientInclusionHom",
	Key:  "prop_37ad2e6430254662",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀V:module_ops(A, B). ∀X Y K L:set(B).",
		Hypotheses: []string{
			"module_on(R, V)",
			"submodule(R, V, X) ∧ " +
				"submodule(R, V, Y) ∧ " +
				"submodule(R, V, K) ∧ " +
				"submodule(R, V, L) ∧ " +
				"K ⊆ X ∧ " +
				"L ⊆ Y ∧ " +
				"X ⊆ Y ∧ " +
				"K ⊆ L",
		},
		Conclusion: "module_homomorphism(R, " +
			"    quotient_module(restrict_module(V, X), K), " +
			"    quotient_module(restrict_module(V, Y), L), " +
			"    λx:set(B). set_mul(V.add, x, L))",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			V *Expr[ModuleOps[A, B]],
			X, Y, K, L *Expr[Set[B]],
			moduleV module.ModuleFact[on.R, on.V],
			given Fact,
		) {
			parts := a.Conjuncts(
				given,
				"X is a submodule of V",
				"so is Y",
				"so is K",
				"so is L",
				"K lies in X",
				"L lies in Y",
				"X lies in Y",
				"K lies in L")
			source := a.Have(
				"X is a module",
				"module_on(R, restrict_module(V, X))",
				By(submodule.SubmoduleModuleOn.Read(moduleV).At(X), parts[0]))
			target := a.Have(
				"so is Y",
				"module_on(R, restrict_module(V, Y))",
				By(submodule.SubmoduleModuleOn.Read(moduleV).At(Y), parts[1]))
			sourceSub := a.Have(
				"K is a submodule of X",
				"submodule(R, restrict_module(V, X), K)",
				By(submodule.SubmoduleRestrict.At(R, V, X, K), parts[2], parts[4]))
			targetSub := a.Have(
				"L is a submodule of Y",
				"submodule(R, restrict_module(V, Y), L)",
				By(submodule.SubmoduleRestrict.At(R, V, Y, L), parts[3], parts[5]))
			inY := a.Unfolded(parts[6], set_basic.SubsetDef)
			total := a.Have(
				"every member of X is a member of Y",
				"∀u:B. u ∈ X ⇒ ∃v:B. v ∈ Y ∧ u = v",
				Derive(func(b *Argument) {
					u := b.FixAs[B]("u")
					inX := b.Assume()
					b.Take(u)
					b.Show(
						"u itself, X lying in Y",
						By(inY, inX))
				}))
			sums := a.Have(
				"equal representatives have equal sums",
				"∀u v x y:B. u ∈ X ∧ v ∈ X ∧ x ∈ Y ∧ y ∈ Y ∧ u = x ∧ v = y ⇒ u + v = x + y",
				Derive(func(b *Argument) {
					b.FixAs[B]("u")
					b.FixAs[B]("v")
					b.FixAs[B]("x")
					b.FixAs[B]("y")
					same := b.Conjuncts(
						b.Assume(),
						"u lies in X",
						"so does v",
						"x lies in Y",
						"so does y",
						"u is x",
						"v is y")
					b.Show(
						"substitute x for u and y for v",
						same[4].Rw(),
						same[5].Rw(),
						Basic())
				}))
			multiples := a.Have(
				"and equal multiples",
				"∀c:A. ∀u v:B. c ∈ R.carrier ∧ u ∈ X ∧ v ∈ Y ∧ u = v ⇒ c • u = c • v",
				Derive(func(b *Argument) {
					b.FixAs[A]("c")
					b.FixAs[B]("u")
					b.FixAs[B]("v")
					same := b.Conjuncts(
						b.Assume(),
						"c is a scalar",
						"u lies in X",
						"v lies in Y",
						"u is v")
					b.Show(
						"substitute v for u",
						same[3].Rw(),
						Basic())
				}))
			inV := a.Unfolded(a.Have(
				"X lies in V",
				"X ⊆ V.carrier",
				By(submodule.SubmoduleSubset.At(R, V, X), parts[0])), set_basic.SubsetDef)
			additive := module.AddGroupOn.Read(moduleV)
			subgroupL := a.Have(
				"L is a subgroup of V",
				"subgroup(module_additive_group(V), L)",
				By(submodule.SubmoduleSubgroup.At(R, V, L), parts[3]))
			zeroInK := a.Have(
				"K holds zero",
				"V.zero ∈ K",
				By(submodule.SubmoduleZero.At(R, V, K), parts[2]))
			value := a.Have(
				"the class u + K, enlarged by L, is u + L",
				Statement{
					Binders: "∀u v:B.",
					Hypotheses: []string{
						"u ∈ X",
						"v ∈ Y",
						"u = v",
					},
					Conclusion: "set_mul(V.add, left_coset(V.add, u, K), L) = left_coset(V.add, v, L)",
				},
				Derive(func(b *Argument) {
					u := b.FixAs[B]("u")
					b.FixAs[B]("v")
					same := b.Conjuncts(
						b.Assume(),
						"u lies in X",
						"v lies in Y",
						"u is v")
					vector := b.MemberOf[on.V](u, b.Have(
						"u is a vector, X lying in V",
						"u ∈ V.carrier",
						By(inV, same[0])))
					b.Show(
						"L, holding K and zero, absorbs K: u + K, enlarged by L, is u + L, and u is v",
						same[2].RwRev(),
						By(
							quotient_group.LeftCosetSetMulAbsorb.Read(additive).At(vector, K, L),
							subgroupL,
							parts[7],
							zeroInK))
				}))
			// The relation is a binder no goal determines, so Where pins it, and
			// the law is read with both modules' vectors at B (Inst): X/K and Y/L
			// are quotients of submodules of the one V.
			a.Show(
				"the relation u = v induces the map on the quotients",
				By(
					source,
					target,
					sourceSub,
					targetSub,
					total,
					sums,
					multiples,
					value,
					Where(
						QuotientRelationHom.Inst(TypeBinder.BindA[A](), TypeBinder.BindB[B](), TypeBinder.BindC[B]()),
						"T",
						a.TermAs[Fun2[B, B, Bool]]("λu:B. λv:B. u = v"))))
		}),
})}

// QuotientIsomorphism — an isomorphism f of modules M ≅ N carries the
// quotient by a submodule K onto the quotient by its image f(K), a class
// going to its image: f(u + K) = f(u) + f(K), f being additive, so the
// class map is the map of quotients that u ↦ f(u) induces; it is one-to-one
// as f is on M, which holds every class, and onto as f is.
var QuotientIsomorphism = quotientIsomorphismThm{family.Add(registry.ProofEntry{
	Name: "QuotientIsomorphism",
	Key:  "prop_b060302d1b7d1cdc",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, C). ∀f:(B → C). ∀K:set(B).",
		Hypotheses: []string{
			"module_isomorphism(R, M, N, f)",
			"submodule(R, M, K)",
		},
		Conclusion: "module_isomorphism(R, " +
			"    quotient_module(M, K), " +
			"    quotient_module(N, image(f, K)), " +
			"    λx:set(B). image(f, x))",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			N *Expr[ModuleOps[A, C]],
			f *Arrow[B, C],
			K *Expr[Set[B]],
			given Fact,
		) {
			hypotheses := a.Conjuncts(
				given,
				"f is an isomorphism of M onto N",
				"K is a submodule of M")
			sub := hypotheses[1]
			iso := a.Conjuncts(
				a.Unfolded(hypotheses[0], ModuleIsomorphismDef),
				"f is R-linear",
				"one-to-one on M",
				"onto N")
			linear, injective, onto := iso[0], iso[1], iso[2]
			image := a.Have(
				"f(K) is a submodule of N",
				"submodule(R, N, image(f, K))",
				By(HomImageSubmodule.At(R, M, N, f, K), linear, sub))
			source, target := HomSource.Read(linear), HomTarget.Read(linear)

			// A class goes to a class: f(u + K) = f(u) + f(K).
			classes := a.Have(
				"f carries the class u + K onto f(u) + f(K)",
				"∀u:B. u ∈ M.carrier ⇒ image(f, left_coset(M.add, u, K)) = left_coset(N.add, f(u), image(f, K))",
				Derive(func(b *Argument) {
					b.FixAs[B]("u")
					inM := b.Assume()
					b.Show(
						"f(u + k) = f(u) + f(k) for k in K, a point of M",
						Simp(Fwd(group.LeftCosetDef), Rev(set_image.ImageCompose), Fwd(functions.ComposeApply)),
						By(
							set_image.ImageCongruence,
							HomAdd.Read(linear),
							submodule.SubmoduleSubset.Read(sub),
							set_basic.SubsetDef,
							inM))
				}))

			// The class map is the map of quotients that the relation f(u) = v
			// induces: f is linear, and carries the class of u to that of f(u).
			images := a.Have(
				"every vector of M has its image in N",
				"∀u:B. u ∈ M.carrier ⇒ ∃v:C. v ∈ N.carrier ∧ f(u) = v",
				a.ForEach(func(u *Expr[B]) Action { return By(HomIn.Read(linear).AsFact().At(u)) }))
			sums := a.Have(
				"the images of two vectors add to the image of their sum",
				Statement{
					Binders: "∀u v:B. ∀x y:C.",
					Hypotheses: []string{
						"u ∈ M.carrier",
						"v ∈ M.carrier",
						"x ∈ N.carrier",
						"y ∈ N.carrier",
						"f(u) = x",
						"f(v) = y",
					},
					Conclusion: "f(M.add(u, v)) = N.add(x, y)",
				},
				Derive(func(b *Argument) {
					u, v := b.FixAs[B]("u"), b.FixAs[B]("v")
					b.Show(
						"f is additive",
						By(Normalized, HomAdd.Read(linear).AsFact().At(u, v)))
				}))
			multiples := a.Have(
				"and the image of a multiple is the multiple of the image",
				Statement{
					Binders: "∀c:A. ∀u:B. ∀v:C.",
					Hypotheses: []string{
						"c ∈ R.carrier",
						"u ∈ M.carrier",
						"v ∈ N.carrier",
						"f(u) = v",
					},
					Conclusion: "f(M.smul(c, u)) = N.smul(c, v)",
				},
				Derive(func(b *Argument) {
					c, u := b.FixAs[A]("c"), b.FixAs[B]("u")
					b.Show(
						"f is linear",
						By(Normalized, HomSmul.Read(linear).AsFact().At(c, u)))
				}))
			cosets := a.Have(
				"the class of a vector goes to the class of its image",
				Statement{
					Binders: "∀u:B. ∀v:C.",
					Hypotheses: []string{
						"u ∈ M.carrier",
						"v ∈ N.carrier",
						"f(u) = v",
					},
					Conclusion: "image(f, left_coset(M.add, u, K)) = left_coset(N.add, v, image(f, K))",
				},
				a.ForEach(func(u *Expr[B]) Action { return By(Normalized, classes.At(u)) }))
			linearQ := a.Have(
				"so the class map is an R-linear map of M/K to N/f(K)",
				"module_homomorphism(R, "+
					"    quotient_module(M, K), "+
					"    quotient_module(N, image(f, K)), "+
					"    λx:set(B). image(f, x))",
				By(
					Where(QuotientRelationHom, "T", a.Term("λu:B. λv:C. f(u) = v")),
					source,
					target,
					sub,
					image,
					images,
					sums,
					multiples,
					cosets))

			// One-to-one: the classes lie in M, where f is one-to-one.
			additive := module.AddGroupOn.Read(source)
			inside := a.Have(
				"a class of K lies in M",
				"∀X:set(B). X ∈ left_cosets(M.add, M.carrier, K) ⇒ X ⊆ M.carrier",
				By(
					quotient_group.ForallInLeftCosets.Read(additive).At(
						K, a.TermAs[Set[Set[B]]]("λX:set(B). X ⊆ M.carrier")),
					group.LeftCosetIn.Read(additive),
					submodule.SubmoduleSubset.Read(sub)))
			separated := a.Have(
				"two classes with one image are one class",
				Statement{
					Binders: "∀X Y:set(B).",
					Hypotheses: []string{
						"X ∈ left_cosets(M.add, M.carrier, K)",
						"Y ∈ left_cosets(M.add, M.carrier, K)",
						"image(f, X) = image(f, Y)",
					},
					Conclusion: "X = Y",
				},
				By(set_image.InjectiveOnImage.At(f, a.TermAs[Set[B]]("M.carrier")), injective, inside))
			oneToOne := a.Have(
				"so the class map is one-to-one",
				"injective_on(left_cosets(M.add, M.carrier, K), λx:set(B). image(f, x))",
				By(functions.InjectiveOnDef, separated))

			// Onto: the classes of f(K) are those of the f(u), u in M, N being f(M).
			everyClass := a.Have(
				"and onto: a class of f(K) is the class of some f(u), the image of the class of u",
				"image(λx:set(B). image(f, x), left_cosets(M.add, M.carrier, K)) = "+
					"left_cosets(N.add, N.carrier, image(f, K))",
				Simp(
					Fwd(quotient_group.LeftCosetsImage.Read(additive)),
					Fwd(quotient_group.LeftCosetsImage.Read(module.AddGroupOn.Read(target))),
					Fwd(submodule.SubmoduleSubset.Read(sub)),
					Fwd(submodule.SubmoduleSubset.Read(image)),
					Fwd(group.CosetMapDef)),
				Simp(Rev(onto), Rev(set_image.ImageCompose), Fwd(functions.ComposeApply)),
				By(set_image.ImageCongruence, classes))
			a.Show(
				"a linear map of the quotients, one-to-one and onto",
				By(ModuleIsomorphismDef, linearQ, oneToOne, everyClass))
		}),
})}

// IsomorphismQuotientFinite — an isomorphism f of modules M ≅ P keeps a
// quotient finite both ways: M/N is finite exactly when P/f(N) is, the
// induced map of quotients (QuotientIsomorphism) being a bijection of their
// carriers.
var IsomorphismQuotientFinite = isomorphismQuotientFiniteThm{family.Add(registry.ProofEntry{
	Name: "IsomorphismQuotientFinite",
	Key:  "prop_f9396e40f4153059",
	Build: family.Theorem(Statement{
		Binders:    "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀P:module_ops(A, C). ∀f:(B → C). ∀N:set(B).",
		Hypotheses: []string{"module_isomorphism(R, M, P, f)", "submodule(R, M, N)"},
		Conclusion: "finite(left_cosets(M.add, M.carrier, N)) ⇔ " +
			"finite(left_cosets(P.add, P.carrier, image(f, N)))",
	}, func(
		a *Argument,
		R *Expr[RingOps[A]],
		M *Expr[ModuleOps[A, B]],
		P *Expr[ModuleOps[A, C]],
		f *Arrow[B, C],
		N *Expr[Set[B]],
		assumptions Fact,
	) {
		quotient := a.Have(
			"the module isomorphism induces a quotient isomorphism",
			"module_isomorphism(R, "+
				"    quotient_module(M, N), "+
				"    quotient_module(P, image(f, N)), "+
				"    λX:set(B). image(f, X))",
			By(assumptions, QuotientIsomorphism.At(R, M, P, f, N)))
		quotientMap := a.TermAs[Fun[Set[B], Set[C]]]("λX:set(B). image(f, X)")
		bijection := a.Have(
			"the induced map is a bijection between quotient carriers",
			"injective_on(left_cosets(M.add, M.carrier, N), λX:set(B). image(f, X)) ∧ "+
				"image(λX:set(B). image(f, X), left_cosets(M.add, M.carrier, N)) = "+
				"left_cosets(P.add, P.carrier, image(f, N))",
			By(
				quotient,
				ModuleIsomorphismDef.At(
					R,
					a.TermAs[ModuleOps[A, Set[B]]]("quotient_module(M, N)"),
					a.TermAs[ModuleOps[A, Set[C]]]("quotient_module(P, image(f, N))"),
					quotientMap)))
		a.Show(
			"a bijection preserves finiteness of the quotient carrier",
			By(
				bijection,
				finite_set.FiniteImageInjEq.At(
					quotientMap, a.TermAs[Set[Set[B]]]("left_cosets(M.add, M.carrier, N)"))))
	}),
})}

// QuotientRelationDescends — unite the target cosets related to a source
// class; compatibility identifies this set with each related target class.
var QuotientRelationDescends = quotientRelationDescendsThm{family.Add(registry.ProofEntry{
	Name: "QuotientRelationDescends",
	Key:  "prop_c6ecaf7dae2025ea",
	Build: family.Theorem(
		Statement{
			Binders: "∀R:ring_ops(A). " +
				"∀M:module_ops(A, B). " +
				"∀N:module_ops(A, C). " +
				"∀K:set(B). " +
				"∀L:set(C). " +
				"∀T:(B → C → bool).",
			Hypotheses: []string{
				"module_on(R, M)",
				"module_on(R, N)",
				"submodule(R, M, K)",
				"submodule(R, N, L)",
				"∀u:B. u ∈ M.carrier ⇒ ∃v:C. v ∈ N.carrier ∧ T(u, v)",
				"∀u v:B. ∀x y:C. " +
					"    u ∈ M.carrier ∧ " +
					"    v ∈ M.carrier ∧ " +
					"    x ∈ N.carrier ∧ " +
					"    y ∈ N.carrier ∧ " +
					"    T(u, x) ∧ " +
					"    T(v, y) ∧ " +
					"    left_coset(M.add, u, K) = left_coset(M.add, v, K) ⇒ " +
					"    left_coset(N.add, x, L) = left_coset(N.add, y, L)",
				"∀u v:B. ∀x y:C. " +
					"    u ∈ M.carrier ∧ v ∈ M.carrier ∧ x ∈ N.carrier ∧ y ∈ N.carrier ∧ T(u, x) ∧ T(v, y) ⇒ " +
					"    T(M.add(u, v), N.add(x, y))",
				"∀c:A. ∀u:B. ∀v:C. " +
					"    c ∈ R.carrier ∧ u ∈ M.carrier ∧ v ∈ N.carrier ∧ T(u, v) ⇒ T(M.smul(c, u), N.smul(c, v))",
			},
			Conclusion: "∃f:(set(B) → set(C)). " +
				"    module_homomorphism(R, quotient_module(M, K), quotient_module(N, L), f) ∧ " +
				"    (∀u:B. ∀v:C. " +
				"        u ∈ M.carrier ∧ v ∈ N.carrier ∧ T(u, v) ⇒ " +
				"        f(left_coset(M.add, u, K)) = left_coset(N.add, v, L))",
		},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			N *Expr[ModuleOps[A, C]],
			K *Expr[Set[B]],
			L *Expr[Set[C]],
			T *Arrow2[B, C, Bool],
			given Fact,
		) {
			compatible := a.Have(
				"related representatives of one source class have one target class",
				Statement{
					Binders: "∀u v:B. ∀x y:C.",
					Hypotheses: []string{
						"u ∈ M.carrier",
						"v ∈ M.carrier",
						"x ∈ N.carrier",
						"y ∈ N.carrier",
						"T(u, x)",
						"T(v, y)",
						"left_coset(M.add, u, K) = left_coset(M.add, v, K)",
					},
					Conclusion: "left_coset(N.add, x, L) = left_coset(N.add, y, L)",
				},
				By(given))
			q, definition := a.LetAs[Fun2[Set[B], C, Bool]](
				"q",
				"λs:set(B). "+
					"    {y:C | "+
					"        ∃u:B. ∃v:C. "+
					"            u ∈ M.carrier ∧ "+
					"            v ∈ N.carrier ∧ "+
					"            T(u, v) ∧ "+
					"            s = left_coset(M.add, u, K) ∧ "+
					"            y ∈ left_coset(N.add, v, L)}")
			membership := a.Have(
				"membership in q is witnessed by a related carrier pair",
				"∀s:set(B). ∀z:C. "+
					"    z ∈ q(s) ⇔ "+
					"    ∃x:B. ∃y:C. "+
					"        x ∈ M.carrier ∧ "+
					"        y ∈ N.carrier ∧ "+
					"        T(x, y) ∧ "+
					"        s = left_coset(M.add, x, K) ∧ "+
					"        z ∈ left_coset(N.add, y, L)",
				definition.Rw(),
				BySets())
			graph := a.Have(
				"q sends the class of u to the class of every related v",
				Statement{
					Binders: "∀u:B. ∀v:C.",
					Hypotheses: []string{
						"u ∈ M.carrier",
						"v ∈ N.carrier",
						"T(u, v)",
					},
					Conclusion: "q(left_coset(M.add, u, K)) = left_coset(N.add, v, L)",
				},
				Derive(func(b *Argument) {
					u := b.FixAs[B]("u")
					v := b.FixAs[C]("v")
					related := b.Assume()
					pointwise := b.Have(
						"the image and target class have the same members",
						"∀z:C. z ∈ q(left_coset(M.add, u, K)) ⇔ z ∈ left_coset(N.add, v, L)",
						Derive(func(c *Argument) {
							z := c.FixAs[C]("z")
							sourceClass := c.TermAs[Set[B]]("left_coset(M.add, u, K)")
							c.Iff()
							c.Forward(
								"any witnessing pair gives the same target class",
								func(d *Argument, member Fact) {
									x, y, witness := d.Obtain2As[B, C](
										"write the image membership using a related pair",
										"∃x:B. ∃y:C. "+
											"    x ∈ M.carrier ∧ "+
											"    y ∈ N.carrier ∧ "+
											"    T(x, y) ∧ "+
											"    left_coset(M.add, u, K) = left_coset(M.add, x, K) ∧ "+
											"    z ∈ left_coset(N.add, y, L)",
										By(member, membership.At(sourceClass, z)))
									sameClass := d.Have(
										"compatibility identifies the two target cosets",
										"left_coset(N.add, v, L) = left_coset(N.add, y, L)",
										By(related, witness, compatible.At(u, x, v, y)))
									d.Show(
										"z belongs to the target class",
										sameClass.Rw(),
										By(witness))
								})
							c.Backward(
								"the given related pair witnesses every target-class member",
								func(d *Argument, member Fact) {
									witness := d.Have(
										"u and v witness membership in q",
										"∃x:B. ∃y:C. "+
											"    x ∈ M.carrier ∧ "+
											"    y ∈ N.carrier ∧ "+
											"    T(x, y) ∧ "+
											"    left_coset(M.add, u, K) = left_coset(M.add, x, K) ∧ "+
											"    z ∈ left_coset(N.add, y, L)",
										Derive(func(e *Argument) {
											e.Take(u)
											e.Take(v)
											e.Show(
												"the given pair has the required class and member",
												By(member, related))
										}))
									d.Show(
										"z belongs to the image",
										By(witness, membership.At(sourceClass, z)))
								})
						}))
					b.Show(
						"the image is the target class",
						By(pointwise, set_basic.Extension.Inst[C]()))
				}))
			linear := a.Have(
				"the quotient relation criterion makes q linear",
				"module_homomorphism(R, quotient_module(M, K), quotient_module(N, L), q)",
				By(given, graph, QuotientRelationHom.At(R, M, N, K, L, T, q)))
			a.Take(q)
			a.Show(
				"q has the required linearity and graph law",
				By(linear, graph))
		}),
})}

// InducedMapHom — the factor theorem: a homomorphism f of R-modules that
// kills a submodule K descends to the quotient by K, taking the value f(x)
// on the coset of x. Forgetting the scalars, f is a homomorphism of the
// additive groups, whose induced map takes the value f(x) on the coset of
// x for any subgroup inside its kernel; the sum and the scalar multiple of
// cosets are the cosets of the sum and of the scaled representative, so
// f's own linearity is the linearity of the induced map.
var InducedMapHom = inducedMapHomThm{family.Add(registry.ProofEntry{
	Name: "InducedMapHom",
	Key:  "prop_468878cbf60cf3fd",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, C). ∀K:set(B). ∀f:(B → C).",
		Hypotheses: []string{
			"submodule(R, M, K)",
			"module_homomorphism(R, M, N, f)",
			"K ⊆ group_kernel(N.zero, M.carrier, f)",
		},
		Conclusion: "module_homomorphism(R, quotient_module(M, K), N, induced_map(f)) ∧ " +
			"(∀x:B. x ∈ M.carrier ⇒ induced_map(f, left_coset(M.add, x, K)) = f(x))",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			N *Expr[ModuleOps[A, C]],
			K *Expr[Set[B]],
			f *Arrow[B, C],
			given Fact,
		) {
			parts := a.Conjuncts(
				given,
				"K is a submodule of M",
				"f is a homomorphism of R-modules",
				"f kills K")
			submoduleK, hom, kills := parts[0], parts[1], parts[2]
			source := HomSource.Read(hom)
			additive := module.AddGroupOn.Read(source)
			// A coset is read from a representative: K lies in M's carrier,
			// so the cosets are the image of the carrier under the coset map.
			a.Have(
				"K lies in M's carrier",
				"K ⊆ M.carrier",
				By(submodule.SubmoduleSubset.Read(submoduleK)))
			subgroup := a.Have(
				"K is a subgroup of the additive group of M",
				"subgroup(module_additive_group(M), K)",
				By(submodule.SubmoduleSubgroup.Read(submoduleK)))
			groupHom := a.Have(
				"forgetting the scalars, f is a homomorphism of the additive groups",
				"group_homomorphism(module_additive_group(M), module_additive_group(N), f)",
				By(HomGroup, hom))
			value := a.Have(
				"K is a subgroup inside the kernel of f, so induced_map(f) "+
					"reads f at any representative of a coset of K",
				"∀x:B. x ∈ M.carrier ⇒ induced_map(f, left_coset(M.add, x, K)) = f(x)",
				By(subgroup, kills, quotient_group.InducedMapCosetWithin.Read(groupHom)))

			linear := a.Have(
				"so induced_map(f) is a homomorphism out of the quotient",
				"module_homomorphism(R, quotient_module(M, K), N, induced_map(f))",
				Simp(Fwd(ModuleHomomorphismDef.Inst(
					TypeBinder.BindA[A](), TypeBinder.BindB[Set[B]](), TypeBinder.BindC[C]()))),
				SplitConjAll(
					Case(
						"the quotient is an R-module",
						By(submoduleK, submodule.QuotientModuleOn.Read(source))),
					Case(
						"N is an R-module",
						By(HomTarget.Read(hom))),
					Case(
						"induced_map(f) carries a coset into N",
						Derive(func(b *Argument) {
							b.Do(Simp(Fwd(quotient_group.ForallInLeftCosets.Read(additive))))
							x := b.FixAs[B]("x")
							xM := proof.MemberOf(x, b.Assume())
							b.Show(
								"its value at the coset of x is f(x), a member of N",
								By(Normalized, value.At(x), HomIn.Read(hom).At(xM)))
						})),
					Case(
						"induced_map(f) carries a sum of cosets to the sum of its values",
						Derive(func(b *Argument) {
							b.Do(Simp(Fwd(quotient_group.ForallInLeftCosetsPair.Read(additive))))
							x := b.FixAs[B]("x")
							y := b.FixAs[B]("y")
							members := b.Conjuncts(
								b.Assume(),
								"x lies in M",
								"y lies in M")
							normal := b.Have(
								"K is a normal subgroup of the additive group of M",
								"normal_subgroup(module_additive_group(M), K)",
								By(submoduleK, submodule.SubmoduleNormal.Read(source)))
							sumClass := b.Have(
								"the sum of the cosets of x and y is the coset of x + y",
								"set_mul(M.add, left_coset(M.add, x, K), left_coset(M.add, y, K)) = left_coset(M.add, x + y, K)",
								By(members[0], members[1], normal, quotient_group.LeftCosetMulOn.Read(additive)))
							b.Show(
								"induced_map(f) reads f at x + y, at x and at y, and f is additive",
								sumClass.Rw(),
								ByChase(
									Depth(0),
									hom,
									members[0],
									members[1],
									value.At(b.TermAs[B]("x + y")),
									value.At(x),
									value.At(y)))
						})),
					Case(
						"induced_map(f) carries a scalar multiple of a coset to the scaled value",
						Derive(func(b *Argument) {
							curried := b.Have(
								"for each scalar c, induced_map(f) carries c times a coset to c times its value",
								"∀c:A. "+
									"    c ∈ R.carrier ⇒ "+
									"    ∀s:set(B). "+
									"        s ∈ left_cosets(M.add, M.carrier, K) ⇒ "+
									"        induced_map(f, quotient_smul(M.add, M.smul, K, c, s)) = c • induced_map(f, s)",
								Derive(func(d *Argument) {
									d.FixAs[A]("c")
									scalar := d.Assume()
									d.Do(Simp(Fwd(quotient_group.ForallInLeftCosets.Read(additive))))
									x := d.FixAs[B]("x")
									xIn := d.Assume()
									scaledClass := d.Have(
										"c times the coset of x is the coset of c • x",
										"quotient_smul(M.add, M.smul, K, c, left_coset(M.add, x, K)) = left_coset(M.add, c • x, K)",
										By(scalar, xIn, submoduleK, submodule.QuotientSmulCoset.Read(source)))
									d.Show(
										"induced_map(f) reads f at c • x and at x, and f carries the scalar out",
										scaledClass.Rw(),
										ByChase(Depth(0), hom, scalar, xIn, value.At(d.TermAs[B]("c • x")), value.At(x)))
								}))
							b.Show(
								"the claim is the curried one with its two guards joined",
								By(curried))
						})),
				))
			a.Show(
				"the induced map is linear and takes the value f(x) on the coset of x",
				By(linear, value))
		}),
})}

// BilinearMapDef — `bilinear_map(R, M, N, L, phi)`: phi is linear in each
// argument, every slice phi(u, -) at a vector of M being a homomorphism of N
// into L and every slice phi(-, v) at a vector of N a homomorphism of M
// into L.
var BilinearMapDef = bilinearMapDefThm{family.Define(registry.DefEntry{
	Name:  "BilinearMapDef",
	Key:   "prop_526e7a9fcb0c1158",
	Const: "bilinear_map",
	Type: "ring_ops(A) → " +
		"module_ops(A, B) → " +
		"module_ops(A, C) → " +
		"module_ops(A, D) → " +
		"(B → C → D) → " +
		"bool",
	Equations: []string{
		"∀R:ring_ops(A). " +
			"∀M:module_ops(A, B). " +
			"∀N:module_ops(A, C). " +
			"∀L:module_ops(A, D). " +
			"∀phi:(B → C → D). " +
			"    bilinear_map(R, M, N, L, phi) ⇔ " +
			"    (∀u:B. u ∈ M.carrier ⇒ module_homomorphism(R, N, L, phi(u))) ∧ " +
			"    (∀v:C. v ∈ N.carrier ⇒ module_homomorphism(R, M, L, λu:B. phi(u, v)))",
	},
	Deps: []registry.EntryLike{ModuleHomomorphismDef},
})}

// BilinearMapOfClauses — a map on the pairs of two modules is bilinear when
// it takes them into the target and is additive and homogeneous in each
// argument: fixing an argument leaves a homomorphism, whose clauses are
// these.
var BilinearMapOfClauses = bilinearMapOfClausesThm{family.Add(registry.ProofEntry{
	Name: "BilinearMapOfClauses",
	Key:  "prop_fa7175bfbb5d4f20",
	Build: family.Theorem(module.ModuleOn.Statement(Statement{
		Binders: "∀N:module_ops(A, C). ∀L:module_ops(A, D). ∀phi:(B → C → D).",
		Hypotheses: []string{
			"module_on(R, N)",
			"module_on(R, L)",
			"∀u:B. ∀v:C. u ∈ M.carrier ∧ v ∈ N.carrier ⇒ phi(u, v) ∈ L.carrier",
			"∀u u':B. ∀v:C. " +
				"    u ∈ M.carrier ∧ u' ∈ M.carrier ∧ v ∈ N.carrier ⇒ phi(u + u', v) = phi(u, v) + phi(u', v)",
			"∀u:B. ∀v v':C. " +
				"    u ∈ M.carrier ∧ v ∈ N.carrier ∧ v' ∈ N.carrier ⇒ phi(u, v + v') = phi(u, v) + phi(u, v')",
			"∀c:A. ∀u:B. ∀v:C. c ∈ R.carrier ∧ u ∈ M.carrier ∧ v ∈ N.carrier ⇒ phi(c • u, v) = c • phi(u, v)",
			"∀c:A. ∀u:B. ∀v:C. c ∈ R.carrier ∧ u ∈ M.carrier ∧ v ∈ N.carrier ⇒ phi(u, c • v) = c • phi(u, v)",
		},
		Conclusion: "bilinear_map(R, M, N, L, phi)",
	}),
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			N *Expr[ModuleOps[A, C]],
			L *Expr[ModuleOps[A, D]],
			phi *Arrow2[B, C, D],
			mModule module.ModuleFact[on.R, on.M],
			nModule module.ModuleFact[on.R, on.N],
			lModule module.ModuleFact[on.R, on.L],
			into, addLeft, addRight, smulLeft, smulRight Fact,
		) {
			rightSlices := a.Have(
				"with its first argument fixed in M, phi is a homomorphism of N into L",
				"∀u:B. u ∈ M.carrier ⇒ module_homomorphism(R, N, L, phi(u))",
				Derive(func(b *Argument) {
					b.FixAs[B]("u")
					uIn := b.Assume()
					b.Show(
						"its clauses are those of phi at this u",
						Simp(Fwd(ModuleHomomorphismDef)),
						By(nModule, lModule, uIn, into, addRight, smulRight))
				}))
			leftSlices := a.Have(
				"with its second argument fixed in N, phi is a homomorphism of M into L",
				"∀v:C. v ∈ N.carrier ⇒ module_homomorphism(R, M, L, λu:B. phi(u, v))",
				Derive(func(b *Argument) {
					b.FixAs[C]("v")
					vIn := b.Assume()
					b.Show(
						"its clauses are those of phi at this v",
						Simp(Fwd(ModuleHomomorphismDef)),
						By(mModule, lModule, vIn, into, addLeft, smulLeft))
				}))
			a.Show(
				"so both families of slices are homomorphisms",
				Simp(Fwd(BilinearMapDef)),
				By(rightSlices, leftSlices))
		}),
})}

// BilinearMapClauses — the converse of BilinearMapOfClauses: a bilinear map
// goes between modules, takes the pairs of its two sources into its target and
// is additive and homogeneous in each argument. Each clause is a homomorphism's,
// read at the slice that fixes the other argument.
var BilinearMapClauses = bilinearMapClausesThm{family.Add(registry.ProofEntry{
	Name: "BilinearMapClauses",
	Key:  "prop_10df82ce42e61c40",
	Build: family.Theorem(module.ModuleOn.Statement(Statement{
		Binders:    "∀N:module_ops(A, C). ∀L:module_ops(A, D). ∀phi:(B → C → D).",
		Hypotheses: []string{"bilinear_map(R, M, N, L, phi)"},
		Conclusion: "module_on(R, N) ∧ " +
			"module_on(R, L) ∧ " +
			"(∀u:B. ∀v:C. u ∈ M.carrier ∧ v ∈ N.carrier ⇒ phi(u, v) ∈ L.carrier) ∧ " +
			"(∀u u':B. ∀v:C. " +
			"    u ∈ M.carrier ∧ u' ∈ M.carrier ∧ v ∈ N.carrier ⇒ phi(u + u', v) = phi(u, v) + phi(u', v)) ∧ " +
			"(∀u:B. ∀v v':C. " +
			"    u ∈ M.carrier ∧ v ∈ N.carrier ∧ v' ∈ N.carrier ⇒ phi(u, v + v') = phi(u, v) + phi(u, v')) ∧ " +
			"(∀c:A. ∀u:B. ∀v:C. " +
			"    c ∈ R.carrier ∧ u ∈ M.carrier ∧ v ∈ N.carrier ⇒ phi(c • u, v) = c • phi(u, v)) ∧ " +
			"(∀c:A. ∀u:B. ∀v:C. c ∈ R.carrier ∧ u ∈ M.carrier ∧ v ∈ N.carrier ⇒ phi(u, c • v) = c • phi(u, v))",
	}),
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			N *Expr[ModuleOps[A, C]],
			L *Expr[ModuleOps[A, D]],
			phi *Arrow2[B, C, D],
			mModule module.ModuleFact[on.R, on.M],
			bilinear Fact,
		) {
			slices := a.Conjuncts(
				a.Unfolded(bilinear, BilinearMapDef),
				"each slice phi(u, -) at a vector of M is a homomorphism of N into L",
				"each slice phi(-, v) at a vector of N is a homomorphism of M into L")
			rightSlices, leftSlices := slices[0], slices[1]
			zeroSlice := a.Have(
				"the slice at the zero of M is a homomorphism of N into L",
				"module_homomorphism(R, N, L, phi(M.zero))",
				By(rightSlices, group.OneIn.Read(module.AddGroupOn.Read(mModule))))
			a.Show(
				"the modules are that slice's ends, and each clause is read off a slice",
				SplitConjAll(
					Case(
						"N is the source of the slice",
						By(HomSource.Read(zeroSlice))),
					Case(
						"L is its target",
						By(HomTarget.Read(zeroSlice))),
					Case(
						"phi takes the pairs of M × N into L",
						Derive(func(b *Argument) {
							u, v := b.FixAs[B]("u"), b.FixAs[C]("v")
							members := b.Assume()
							b.Show(
								"the slice at u carries N into L",
								By(members, rightSlices.At(u), HomIn.At(R, N, L, b.TermAs[Fun[C, D]]("phi(u)"), v)))
						})),
					Case(
						"phi is additive in its first argument",
						Derive(func(b *Argument) {
							u, uPrime, v := b.FixAs[B]("u"), b.FixAs[B]("u'"), b.FixAs[C]("v")
							members := b.Assume()
							b.Show(
								"the slice at v preserves the sum",
								By(
									members,
									leftSlices.At(v),
									HomAdd.At(R, M, L, b.TermAs[Fun[B, D]]("λx:B. phi(x, v)"), u, uPrime)))
						})),
					Case(
						"and in its second",
						Derive(func(b *Argument) {
							u, v, vPrime := b.FixAs[B]("u"), b.FixAs[C]("v"), b.FixAs[C]("v'")
							members := b.Assume()
							b.Show(
								"the slice at u preserves the sum",
								By(members, rightSlices.At(u), HomAdd.At(R, N, L, b.TermAs[Fun[C, D]]("phi(u)"), v, vPrime)))
						})),
					Case(
						"a scalar on the first argument comes out of phi",
						Derive(func(b *Argument) {
							c, u, v := b.FixAs[A]("c"), b.FixAs[B]("u"), b.FixAs[C]("v")
							members := b.Assume()
							b.Show(
								"the slice at v carries the scalar out",
								By(members, leftSlices.At(v), HomSmul.At(R, M, L, b.TermAs[Fun[B, D]]("λx:B. phi(x, v)"), c, u)))
						})),
					Case(
						"and so does one on the second",
						Derive(func(b *Argument) {
							c, u, v := b.FixAs[A]("c"), b.FixAs[B]("u"), b.FixAs[C]("v")
							members := b.Assume()
							b.Show(
								"the slice at u carries the scalar out",
								By(members, rightSlices.At(u), HomSmul.At(R, N, L, b.TermAs[Fun[C, D]]("phi(u)"), c, v)))
						}))))
		}),
})}

// ModuleIsomorphismDef — a homomorphism bijective on its carriers.
var ModuleIsomorphismDef = moduleIsomorphismDefThm{family.Define(registry.DefEntry{
	Name: "ModuleIsomorphismDef", Const: "module_isomorphism",
	Key:  "prop_9a99ec155e032441",
	Type: "ring_ops(A) → module_ops(A, B) → module_ops(A, C) → (B → C) → bool",
	Equations: []string{
		mapBinders + "module_isomorphism(R, M, N, f) ⇔ module_homomorphism(R, M, N, f) ∧ injective_on(M.carrier, f) ∧ image(f, M.carrier) = N.carrier",
	},
	Deps: []registry.EntryLike{ModuleHomomorphismDef},
})}

// IsomorphismInverse — apply the original map to sums and scalar multiples,
// then recover them with its left inverse.
var IsomorphismInverse = isomorphismInverseThm{family.Add(registry.ProofEntry{
	Name: "IsomorphismInverse",
	Key:  "prop_72f456396df3cffd",
	Build: family.Theorem(
		Statement{
			Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, C). ∀f:(B → C).",
			Hypotheses: []string{
				"module_isomorphism(R, M, N, f)",
			},
			Conclusion: "module_isomorphism(R, N, M, inverse_on(M.carrier, f))",
		},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			N *Expr[ModuleOps[A, C]],
			f *Arrow[B, C],
			iso Fact,
		) {
			sourceCarrier := a.TermAs[Set[B]]("M.carrier")
			targetCarrier := a.TermAs[Set[C]]("N.carrier")
			inverse := a.TermAs[Fun[C, B]]("inverse_on(M.carrier, f)")
			forward := a.Have(
				"the given map is linear and bijective",
				"module_homomorphism(R, M, N, f) ∧ injective_on(M.carrier, f) ∧ image(f, M.carrier) = N.carrier",
				By(iso, ModuleIsomorphismDef))
			linear := a.Have(
				"the given map is linear",
				"module_homomorphism(R, M, N, f)",
				By(forward))
			source := a.Have(
				"the source is a module",
				"module_on(R, M)",
				By(HomSource.Read(linear)))
			target := a.Have(
				"the target is a module",
				"module_on(R, N)",
				By(HomTarget.Read(linear)))

			rightInverse := a.Have(
				"the inverse takes target elements back to their preimages",
				Statement{
					Binders: "∀y:C.",
					Hypotheses: []string{
						"y ∈ N.carrier",
					},
					Conclusion: "inverse_on(M.carrier, f, y) ∈ M.carrier ∧ f(inverse_on(M.carrier, f, y)) = y",
				},
				Derive(func(b *Argument) {
					y := b.FixAs[C]("y")
					member := b.Assume()
					inImage := b.Have(
						"surjectivity puts the target element in the image",
						"y ∈ image(f, M.carrier)",
						By(Normalized, member, forward))
					b.Show(
						"the chosen preimage lies in the source and maps to y",
						By(
							inImage,
							functions.InverseOnIn.At(sourceCarrier, f, y),
							functions.InverseOnRight.At(sourceCarrier, f, y)))
				}))
			leftInverse := a.Have(
				"the inverse recovers every source element",
				"∀x:B. x ∈ M.carrier ⇒ f(x) ∈ N.carrier ∧ inverse_on(M.carrier, f, f(x)) = x",
				Derive(func(b *Argument) {
					x := b.FixAs[B]("x")
					member := b.Assume()
					b.Show(
						"linearity gives the target membership and injectivity recovers x",
						By(
							forward,
							HomIn.Read(linear).At(proof.MemberOf(x, member)),
							functions.InverseOnLeft.At(sourceCarrier, f, x)))
				}))

			add := a.Have(
				"the inverse preserves addition",
				Statement{
					Binders: "∀u v:C.",
					Hypotheses: []string{
						"u ∈ N.carrier",
						"v ∈ N.carrier",
					},
					Conclusion: "inverse_on(M.carrier, f, N.add(u, v)) = " +
						"M.add(inverse_on(M.carrier, f, u), inverse_on(M.carrier, f, v))",
				},
				Derive(func(b *Argument) {
					u := b.FixAs[C]("u")
					v := b.FixAs[C]("v")
					members := b.Assume()
					preimages := b.Have(
						"both preimages lie in the source and map back to u and v",
						"inverse_on(M.carrier, f, u) ∈ M.carrier ∧ "+
							"inverse_on(M.carrier, f, v) ∈ M.carrier ∧ "+
							"f(inverse_on(M.carrier, f, u)) = u ∧ "+
							"f(inverse_on(M.carrier, f, v)) = v",
						By(members, rightInverse.At(u), rightInverse.At(v)))
					sumIn := b.Have(
						"the sum of the preimages lies in the source",
						"M.add(inverse_on(M.carrier, f, u), inverse_on(M.carrier, f, v)) ∈ M.carrier",
						By(group.MulIn.Read(module.AddGroupOn.Read(source)), preimages))
					parts := b.Conjuncts(
						preimages,
						"the preimage of u lies in M",
						"the preimage of v lies in M",
						"the first preimage maps to u",
						"the second preimage maps to v")
					preimageU := proof.MemberOf(b.TermAs[B]("inverse_on(M.carrier, f, u)"), parts[0])
					preimageV := proof.MemberOf(b.TermAs[B]("inverse_on(M.carrier, f, v)"), parts[1])
					mappedSum := b.Have(
						"the original map takes this sum to the target sum",
						"f(M.add(inverse_on(M.carrier, f, u), inverse_on(M.carrier, f, v))) = N.add(u, v)",
						By(parts[2], parts[3], HomAdd.Read(linear).At(preimageU, preimageV)))
					sum := b.TermAs[B]("M.add(inverse_on(M.carrier, f, u), inverse_on(M.carrier, f, v))")
					b.Show(
						"the left inverse recovers the sum",
						By(mappedSum, sumIn, leftInverse.At(sum)))
				}))
			smul := a.Have(
				"the inverse preserves scalar multiplication",
				Statement{
					Binders: "∀c:A. ∀u:C.",
					Hypotheses: []string{
						"c ∈ R.carrier",
						"u ∈ N.carrier",
					},
					Conclusion: "inverse_on(M.carrier, f, N.smul(c, u)) = M.smul(c, inverse_on(M.carrier, f, u))",
				},
				Derive(func(b *Argument) {
					c := b.FixAs[A]("c")
					u := b.FixAs[C]("u")
					members := b.Assume()
					preimage := b.Have(
						"the preimage lies in the source and maps back to u",
						"inverse_on(M.carrier, f, u) ∈ M.carrier ∧ f(inverse_on(M.carrier, f, u)) = u",
						By(members, rightInverse.At(u)))
					given := b.Conjuncts(
						members,
						"c lies in the ring",
						"u lies in the target")
					parts := b.Conjuncts(
						preimage,
						"the preimage lies in M",
						"the preimage maps to u")
					cR := proof.MemberOf(c, given[0])
					preimageU := proof.MemberOf(b.TermAs[B]("inverse_on(M.carrier, f, u)"), parts[0])
					scaledIn := b.Have(
						"the scalar multiple of the preimage lies in the source",
						"M.smul(c, inverse_on(M.carrier, f, u)) ∈ M.carrier",
						By(module.SmulIn.Read(source).At(cR, preimageU)))
					mappedScalar := b.Have(
						"the original map takes this multiple to the target multiple",
						"f(M.smul(c, inverse_on(M.carrier, f, u))) = N.smul(c, u)",
						By(parts[1], HomSmul.Read(linear).At(cR, preimageU)))
					scaled := b.TermAs[B]("M.smul(c, inverse_on(M.carrier, f, u))")
					b.Show(
						"the left inverse recovers the scalar multiple",
						By(mappedScalar, scaledIn, leftInverse.At(scaled)))
				}))

			bijection := a.Have(
				"the two inverse laws give the reverse bijection",
				"injective_on(N.carrier, inverse_on(M.carrier, f)) ∧ "+
					"image(inverse_on(M.carrier, f), N.carrier) = M.carrier",
				By(
					leftInverse,
					rightInverse,
					functions.TwoSidedInverseBijection.At(targetCarrier, sourceCarrier, inverse, f)))
			inverseLinear := a.Have(
				"the inverse is a module homomorphism",
				"module_homomorphism(R, N, M, inverse_on(M.carrier, f))",
				By(smul, add, rightInverse, source, target, ModuleHomomorphismDef.At(R, N, M, inverse)))
			a.Show(
				"the inverse is a module isomorphism",
				By(bijection, inverseLinear, ModuleIsomorphismDef.At(R, N, M, inverse)))
		}),
})}

// IsomorphismCompose — a composite of two module isomorphisms is a module
// isomorphism: g ∘ f is linear as a composite of linear maps, one-to-one on
// M because f is one-to-one there and carries M into N, where g is
// one-to-one, and onto L because its image is g's image of f's image.
var IsomorphismCompose = isomorphismComposeThm{family.Add(registry.ProofEntry{
	Name: "IsomorphismCompose",
	Key:  "prop_de0f687c987b0a17",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀M:module_ops(A, B). " +
			"∀N:module_ops(A, C). " +
			"∀L:module_ops(A, D). " +
			"∀f:(B → C). " +
			"∀g:(C → D).",
		Hypotheses: []string{
			"module_isomorphism(R, M, N, f)",
			"module_isomorphism(R, N, L, g)",
		},
		Conclusion: "module_isomorphism(R, M, L, g ∘ f)",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			N *Expr[ModuleOps[A, C]],
			L *Expr[ModuleOps[A, D]],
			f *Arrow[B, C],
			g *Arrow[C, D],
			both Fact,
		) {
			isos := a.Conjuncts(
				both,
				"f is an isomorphism of M onto N",
				"g is an isomorphism of N onto L")
			first := a.Conjuncts(
				a.Unfolded(isos[0], ModuleIsomorphismDef),
				"f is a homomorphism",
				"f is one-to-one on M",
				"f is onto N")
			second := a.Conjuncts(
				a.Unfolded(isos[1], ModuleIsomorphismDef),
				"g is a homomorphism",
				"g is one-to-one on N",
				"g is onto L")
			linear := a.Have(
				"g ∘ f is a homomorphism",
				"module_homomorphism(R, M, L, g ∘ f)",
				By(HomCompose, first[0], second[0]))
			oneToOne := a.Have(
				"g ∘ f is one-to-one on M, f carrying M into N",
				"injective_on(M.carrier, g ∘ f)",
				By(functions.InjectiveOnCompose, first[1], second[1], HomIn.Read(first[0])))
			onto := a.Have(
				"g ∘ f is onto L",
				"image(g ∘ f, M.carrier) = L.carrier",
				CalcEq(
					Leg(
						a.TermAs[Set[D]]("image(g, image(f, M.carrier))"),
						"an image under g ∘ f is the image under g of the image under f",
						Cite(set_image.ImageCompose)),
					Leg(
						a.TermAs[Set[D]]("image(g, N.carrier)"),
						"f is onto N",
						first[2].Rw(),
						Basic()),
					FinalLeg(
						"g is onto L",
						By(second[2])),
				))
			a.Show(
				"so g ∘ f is an isomorphism",
				By(ModuleIsomorphismDef, linear, oneToOne, onto))
		}),
})}

// IsomorphismCongruence — a map agreeing with a module isomorphism on the
// source carrier is a module isomorphism: it is a homomorphism by
// HomCongruence, one-to-one on M because its values there are those of the
// one-to-one f, and onto N because its image of M is f's.
var IsomorphismCongruence = isomorphismCongruenceThm{family.Add(registry.ProofEntry{
	Name: "IsomorphismCongruence",
	Key:  "prop_4618541eaa75e18d",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, C). ∀f g:(B → C).",
		Hypotheses: []string{
			"module_isomorphism(R, M, N, f)",
			"∀x:B. x ∈ M.carrier ⇒ g(x) = f(x)",
		},
		Conclusion: "module_isomorphism(R, M, N, g)",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			N *Expr[ModuleOps[A, C]],
			f, g *Arrow[B, C],
			given Fact,
		) {
			parts := a.Conjuncts(
				given,
				"f is an isomorphism of M onto N",
				"g agrees with f on M")
			agree := parts[1]
			iso := a.Conjuncts(
				a.Unfolded(parts[0], ModuleIsomorphismDef),
				"f is a homomorphism",
				"f is one-to-one on M",
				"f is onto N")
			linear := a.Have(
				"g is a homomorphism, agreeing on M with the homomorphism f",
				"module_homomorphism(R, M, N, g)",
				By(HomCongruence.At(R, M, N, f, g), iso[0], agree))
			oneToOne := a.Have(
				"g is one-to-one on M",
				"injective_on(M.carrier, g)",
				Simp(Fwd(functions.InjectiveOnDef)),
				Derive(func(b *Argument) {
					x, y := b.FixAs[B]("x"), b.FixAs[B]("y")
					equal := b.Conjuncts(
						b.Assume(),
						"x lies in M",
						"y lies in M",
						"g(x) = g(y)")
					same := b.Have(
						"through g, f takes one value at x and y",
						"f(x) = f(y)",
						CalcEq(
							Leg(
								b.TermAs[C]("g(x)"),
								"g is f at x",
								By(agree.At(x), equal[0])),
							Leg(
								b.TermAs[C]("g(y)"),
								"as assumed",
								By(equal[2])),
							FinalLeg(
								"g is f at y",
								By(agree.At(y), equal[1])),
						))
					b.Show(
						"so x = y, f being one-to-one on M",
						By(b.Simplified(iso[1], Fwd(functions.InjectiveOnDef)).At(x, y), equal[0], equal[1], same))
				}))
			onto := a.Have(
				"g is onto N",
				"image(g, M.carrier) = N.carrier",
				CalcEq(
					Leg(
						a.TermAs[Set[C]]("image(f, M.carrier)"),
						"on M the values of g are f's",
						BySets(agree)),
					FinalLeg(
						"f is onto N",
						By(iso[2])),
				))
			a.Show(
				"so g is an isomorphism",
				By(ModuleIsomorphismDef, linear, oneToOne, onto))
		}),
})}

// IsomorphismOntoImage — a one-to-one homomorphism is an isomorphism of its
// source onto its image: the image is a submodule of the target, the map
// takes its source into it and so corestricts to a homomorphism onto it.
var IsomorphismOntoImage = isomorphismOntoImageThm{family.Add(registry.ProofEntry{
	Name: "IsomorphismOntoImage",
	Key:  "prop_c6b42e4db6535b88",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, C). ∀f:(B → C).",
		Hypotheses: []string{
			"module_homomorphism(R, M, N, f)",
			"injective_on(M.carrier, f)",
		},
		Conclusion: "module_isomorphism(R, M, restrict_module(N, image(f, M.carrier)), f)",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			N *Expr[ModuleOps[A, C]],
			f *Arrow[B, C],
			linear, oneToOne Fact,
		) {
			corestriction := a.Have(
				"the image being a submodule of N, f is a homomorphism of M into it",
				"module_homomorphism(R, M, restrict_module(N, image(f, M.carrier)), f)",
				By(
					linear,
					ImageSubmodule.Read(linear),
					set_image.FunInImage,
					HomCorestrict.At(R, M, N, f, a.TermAs[Set[C]]("image(f, M.carrier)"))))
			a.Show(
				"f is one-to-one on M and onto its image, the carrier of the restriction",
				By(ModuleIsomorphismDef, corestriction, oneToOne))
		}),
})}

// ModuleIsomorphicDef — there exists an isomorphism of the R-modules.
var ModuleIsomorphicDef = moduleIsomorphicDefThm{family.Define(registry.DefEntry{
	Name: "ModuleIsomorphicDef", Const: "module_isomorphic",
	Key:  "prop_5fc9f58a26681f9a",
	Type: "ring_ops(A) → module_ops(A, B) → module_ops(A, C) → bool",
	Equations: []string{
		endpoints + "module_isomorphic(R, M, N) ⇔ ∃f:(B → C). module_isomorphism(R, M, N, f)",
	},
	Deps: []registry.EntryLike{ModuleIsomorphismDef},
})}

// IsomorphicOfIsomorphism — modules with an isomorphism between them are
// isomorphic: the isomorphism is the witness.
var IsomorphicOfIsomorphism = isomorphicOfIsomorphismThm{family.Add(registry.ProofEntry{
	Name: "IsomorphicOfIsomorphism",
	Key:  "prop_b69f6d780bcbcb0f",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, C). ∀f:(B → C).",
		Hypotheses: []string{
			"module_isomorphism(R, M, N, f)",
		},
		Conclusion: "module_isomorphic(R, M, N)",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			N *Expr[ModuleOps[A, C]],
			f *Arrow[B, C],
			iso Fact,
		) {
			a.Show(
				"f is an isomorphism of M onto N",
				Unfold(ModuleIsomorphicDef),
				Witness(f),
				By(iso))
		}),
})}

// KernelTrivialIffInjective — a module homomorphism is one-to-one on its
// source exactly when its kernel holds the zero vector alone: forgetting
// the scalars, it is a homomorphism of the additive groups, and a group
// homomorphism is one-to-one exactly when its kernel is trivial.
var KernelTrivialIffInjective = kernelTrivialIffInjectiveThm{family.Add(registry.ProofEntry{
	Name: "KernelTrivialIffInjective",
	Key:  "prop_1f1a3b50cf9f8d0d",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, C). ∀f:(B → C).",
		Hypotheses: []string{
			"module_homomorphism(R, M, N, f)",
		},
		Conclusion: "group_kernel(N.zero, M.carrier, f) = {M.zero} ⇔ injective_on(M.carrier, f)",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			N *Expr[ModuleOps[A, C]],
			f *Arrow[B, C],
			hom Fact,
		) {
			a.Show(
				"f is a homomorphism of the additive groups, one-to-one exactly when its kernel is trivial",
				By(group_homomorphism.KernelTrivialIffInjective.Read(HomGroup.Read(hom))))
		}),
})}

// FirstIsomorphism — the quotient of the source by the kernel is isomorphic
// to the image: the factor theorem at the kernel makes the induced map
// linear, its values lie in the image, a submodule of N, so it is linear
// into the image, and the additive first isomorphism theorem makes it
// one-to-one on the cosets and onto the image.
var FirstIsomorphism = firstIsomorphismThm{family.Add(registry.ProofEntry{
	Name: "FirstIsomorphism",
	Key:  "prop_d9204563d592cff6",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, C). ∀f:(B → C).",
		Hypotheses: []string{
			"module_homomorphism(R, M, N, f)",
		},
		Conclusion: "module_isomorphism(R, " +
			"    quotient_module(M, group_kernel(N.zero, M.carrier, f)), " +
			"    restrict_module(N, image(f, M.carrier)), " +
			"    induced_map(f))",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			N *Expr[ModuleOps[A, C]],
			f *Arrow[B, C],
			hom Fact,
		) {
			quotient := a.TermAs[ModuleOps[A, Set[B]]]("quotient_module(M, group_kernel(N.zero, M.carrier, f))")
			induced := a.TermAs[Fun[Set[B], C]]("induced_map(f)")
			fImage := a.TermAs[Set[C]]("image(f, M.carrier)")

			linear := a.Have(
				"the kernel is a submodule of M inside itself, so f descends "+
					"to a linear map from the quotient by its kernel into N",
				"module_homomorphism(R, quotient_module(M, group_kernel(N.zero, M.carrier, f)), N, induced_map(f))",
				By(KernelSubmodule.Read(hom), hom, set_order.SubsetRefl, InducedMapHom))
			additive := quotient_group.FirstIsomorphism.Read(HomGroup.Read(hom))
			onto := a.Have(
				"forgetting the scalars, the first isomorphism theorem "+
					"for groups carries the cosets of the kernel onto the image",
				"image(induced_map(f), left_cosets(M.add, M.carrier, group_kernel(N.zero, M.carrier, f))) = "+
					"image(f, M.carrier)",
				By(group_homomorphism.IsomorphismSurjective.Read(additive)))
			oneToOne := a.Have(
				"and makes the induced map one-to-one on them",
				"injective_on(left_cosets(M.add, M.carrier, group_kernel(N.zero, M.carrier, f)), induced_map(f))",
				By(group_homomorphism.IsomorphismInjective.Read(additive)))
			into := a.Have(
				"so the induced map sends every coset of the kernel into the image",
				Statement{
					Binders: "∀u:set(B).",
					Hypotheses: []string{
						"u ∈ left_cosets(M.add, M.carrier, group_kernel(N.zero, M.carrier, f))",
					},
					Conclusion: "induced_map(f, u) ∈ image(f, M.carrier)",
				},
				onto.RwRev(),
				By(set_image.FunInImage))
			intoImage := a.Have(
				"the image is a submodule of N, so the induced map is linear from the quotient into the image",
				"module_homomorphism(R, "+
					"    quotient_module(M, group_kernel(N.zero, M.carrier, f)), "+
					"    restrict_module(N, image(f, M.carrier)), "+
					"    induced_map(f))",
				By(linear, ImageSubmodule.Read(hom), into, HomCorestrict.At(R, quotient, N, induced, fImage)))
			a.Show(
				"linear, one-to-one on the cosets of the kernel and "+
					"onto the image, the induced map is an isomorphism",
				By(ModuleIsomorphismDef, intoImage, oneToOne, onto))
		}),
})}
