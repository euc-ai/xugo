// Exact sequences, short exact sequences of modules over one ring, splittings
// (an idempotent splitting its module into image and kernel, a retraction
// onto the kernel from an inner inverse, a cokernel read off a split
// sequence), and transport across commuting module isomorphisms.

package module_homomorphism

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// ExactAtDef identifies the image of the incoming map with the kernel
// of the outgoing map, using the zero of the outgoing map's target.
var ExactAtDef = exactAtDefThm{family.Define(registry.DefEntry{
	Name:  "ExactAtDef",
	Key:   "prop_f44b61691b3c4ad",
	Const: "exact_at",
	Type:  "D → set(B) → set(C) → (B → C) → (C → D) → bool",
	Equations: []string{
		"∀e:D. ∀M:set(B). ∀M':set(C). ∀f:(B → C). ∀g:(C → D). " +
			"    exact_at(e, M, M', f, g) ⇔ image(f, M) = group_kernel(e, M', g)",
	},
})}

// ShortExactModules — the two self-contained homomorphisms carry the
// three module laws; i is injective, its image is the kernel of p,
// and p is onto. The sequence has no distinguished subject.
var ShortExactModules = shortExactModulesThm{family.DefineStructure(registry.DefEntry{
	Name: "ShortExactModules", Const: "short_exact_modules",
	Key: "prop_8a652995bc04b143",
	Type: "ring_ops(A) → " +
		"module_ops(A, C) → " +
		"module_ops(A, D) → " +
		"module_ops(A, E) → " +
		"(C → D) → " +
		"(D → E) → " +
		"bool",
	Letter: "S",
	Equations: []string{
		"∀R:ring_ops(A). " +
			"∀N':module_ops(A, C). " +
			"∀N:module_ops(A, D). " +
			"∀N'':module_ops(A, E). " +
			"∀i:(C → D). " +
			"∀p:(D → E). " +
			"    short_exact_modules(R, N', N, N'', i, p) ⇔ " +
			"    module_homomorphism(R, N', N, i) ∧ " +
			"    module_homomorphism(R, N, N'', p) ∧ " +
			"    injective_on(N'.carrier, i) ∧ " +
			"    exact_at(N''.zero, N'.carrier, N.carrier, i, p) ∧ " +
			"    image(p, N.carrier) = N''.carrier",
	},
	Deps: []registry.EntryLike{ModuleHomomorphismDef, ExactAtDef},
})}

// ExactComposeZero — at an exact spot, g after f is zero on M.
var ExactComposeZero = exactComposeZeroThm{family.Add(registry.ProofEntry{
	Name: "ExactComposeZero",
	Key:  "prop_a728e6bd96e9ac5c",
	Build: family.Theorem(Statement{
		Binders: "∀e:D. ∀M:set(B). ∀M':set(C). ∀f:(B → C). ∀g:(C → D). ∀u:B.",
		Hypotheses: []string{
			"exact_at(e, M, M', f, g)",
			"u ∈ M",
		},
		Conclusion: "g(f(u)) = e",
	},
		func(a *Argument, e *Expr[D], M *Expr[Set[B]], MPrime *Expr[Set[C]],
			f *Arrow[B, C], g *Arrow[C, D], u *Expr[B], given Fact) {
			a.Show(
				"exactness puts the image of u in the kernel of g",
				By(
					given,
					ExactAtDef.At(e, M, MPrime, f, g),
					set_basic.InImage.At(f, M, f.Apply(u)),
					group_homomorphism.InKernel.At(e, MPrime, g, f.Apply(u))))
		}),
})}

// ExactAtIsomorphism — the commuting squares carry kernels and images
// between the two rows; surjectivity supplies lifts and injectivity
// identifies their images.
var ExactAtIsomorphism = exactAtIsomorphismThm{family.Add(registry.ProofEntry{
	Name: "ExactAtIsomorphism",
	Key:  "prop_a8e664f961d50dac",
	Build: family.Theorem(
		Statement{
			Binders: "∀R:ring_ops(A). " +
				"∀M₁:module_ops(A, B). " +
				"∀M₂:module_ops(A, C). " +
				"∀M₃:module_ops(A, D). " +
				"∀N₁:module_ops(A, E). " +
				"∀N₂:module_ops(A, F). " +
				"∀N₃:module_ops(A, G). " +
				"∀f:(B → C). " +
				"∀g:(C → D). " +
				"∀f':(E → F). " +
				"∀g':(F → G). " +
				"∀u:(B → E). " +
				"∀v:(C → F). " +
				"∀w:(D → G).",
			Hypotheses: []string{
				"module_homomorphism(R, M₁, M₂, f)",
				"module_homomorphism(R, M₂, M₃, g)",
				"module_homomorphism(R, N₁, N₂, f')",
				"module_homomorphism(R, N₂, N₃, g')",
				"module_isomorphism(R, M₁, N₁, u)",
				"module_isomorphism(R, M₂, N₂, v)",
				"module_isomorphism(R, M₃, N₃, w)",
				"∀x:B. x ∈ M₁.carrier ⇒ v(f(x)) = f'(u(x))",
				"∀x:C. x ∈ M₂.carrier ⇒ w(g(x)) = g'(v(x))",
			},
			Conclusion: "exact_at(M₃.zero, M₁.carrier, M₂.carrier, f, g) ⇔ " +
				"exact_at(N₃.zero, N₁.carrier, N₂.carrier, f', g')",
		},
		func(a *Argument, R *Expr[RingOps[A]],
			M1 *Expr[ModuleOps[A, B]], M2 *Expr[ModuleOps[A, C]], M3 *Expr[ModuleOps[A, D]],
			N1 *Expr[ModuleOps[A, E]], N2 *Expr[ModuleOps[A, F]], N3 *Expr[ModuleOps[A, G]],
			f *Arrow[B, C], g *Arrow[C, D], f_ *Arrow[E, F], g_ *Arrow[F, G],
			u *Arrow[B, E], v *Arrow[C, F], w *Arrow[D, G], _ Fact) {
			// Read the three isomorphisms as homomorphisms and carrier bijections.
			a.Do(Unfold(ModuleIsomorphismDef))
			fHom := a.Hyp("module_homomorphism(R, M₁, M₂, f)")
			gHom := a.Hyp("module_homomorphism(R, M₂, M₃, g)")
			fPrimeHom := a.Hyp("module_homomorphism(R, N₁, N₂, f')")
			gPrimeHom := a.Hyp("module_homomorphism(R, N₂, N₃, g')")
			uHom := a.Hyp("module_homomorphism(R, M₁, N₁, u)")
			vHom := a.Hyp("module_homomorphism(R, M₂, N₂, v)")
			wHom := a.Hyp("module_homomorphism(R, M₃, N₃, w)")
			leftSquare := a.Hyp("∀x:B. x ∈ M₁.carrier ⇒ v(f(x)) = f'(u(x))")
			rightSquare := a.Hyp("∀x:C. x ∈ M₂.carrier ⇒ w(g(x)) = g'(v(x))")
			uOnto := a.Hyp("image(u, M₁.carrier) = N₁.carrier")
			vOnto := a.Hyp("image(v, M₂.carrier) = N₂.carrier")
			vInjective := a.Hyp("injective_on(M₂.carrier, v)")
			wInjective := a.Hyp("injective_on(M₃.carrier, w)")

			a.Iff()
			a.Forward(
				"Lift through v, use exactness in the top row, and carry the preimage through u",
				func(b *Argument, topExact Fact) {
					b.Show(
						"The bottom row is exact",
						ByChase(
							Depth(3),
							leftSquare,
							rightSquare,
							uOnto,
							vOnto,
							wInjective,
							fHom,
							uHom,
							gHom,
							vHom,
							wHom,
							fPrimeHom,
							gPrimeHom,
							topExact))
				})
			a.Backward(
				"Lift the bottom preimage through u and identify its image by injectivity of v",
				func(b *Argument, bottomExact Fact) {
					b.Show(
						"The top row is exact",
						ByChase(
							Depth(2),
							leftSquare,
							rightSquare,
							uOnto,
							vInjective,
							wInjective,
							fHom,
							uHom,
							gHom,
							vHom,
							wHom,
							fPrimeHom,
							gPrimeHom,
							bottomExact))
				})
		}),
})}

// IdempotentSplits — an idempotent endomorphism of a module splits it into its image and
// its kernel: a vector in both is fixed by f and killed by it, so it is zero, and each v
// is f(v) + (−f(v) + v), a value of f plus a vector that f kills.
var IdempotentSplits = idempotentSplitsThm{family.Add(registry.ProofEntry{
	Name: "IdempotentSplits",
	Key:  "prop_e67c5bdc86d81d1d",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀f:(B → B).",
		Hypotheses: []string{
			"module_homomorphism(R, M, M, f)",
			"∀v:B. v ∈ M.carrier ⇒ f(f(v)) = f(v)",
		},
		Conclusion: "image(f, M.carrier) ∩ group_kernel(M.zero, M.carrier, f) = {M.zero} ∧ " +
			"(∀v:B. " +
			"    v ∈ M.carrier ⇒ " +
			"    ∃u w:B. u ∈ image(f, M.carrier) ∧ w ∈ group_kernel(M.zero, M.carrier, f) ∧ M.add(u, w) = v)",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			f *Arrow[B, B],
			linear, idempotent Fact,
		) {
			additive := module.AddGroupOn.Read(HomSource.Read(linear))
			a.Do(SplitConj(
				Case(
					"a value of f that f kills is fixed by f, so zero; and zero is such a value",
					Unfold(group_homomorphism.GroupKernelDef),
					BySets(idempotent, HomZero.Read(linear), group.OneIn.Read(additive))),
				Case(
					"each v is f(v) + (−f(v) + v), a value of f plus a vector that f kills",
					Derive(func(b *Argument) {
						v := b.FixAs[B]("v")
						vM := b.MemberOf[on.Any](v, b.Assume())
						fvM := b.MemberOf[on.Any](f.Apply(v), HomIn.Read(linear).At(vM))
						negM := group.InvIn.Read(additive).At(fvM)
						w := b.TermAs[B]("-f(v) + v")
						wM := group.MulIn.Read(additive).At(negM, vM)
						b.Take(f.Apply(v))
						b.Take(w)
						kills := b.Have(
							"f kills −f(v) + v, since it fixes f(v)",
							"f(-f(v) + v) = M.zero",
							CalcEq(
								Leg(
									b.TermAs[B]("f(-f(v)) + f(v)"),
									"f is additive",
									By(HomAdd.Read(linear).At(negM, vM))),
								Leg(
									b.TermAs[B]("-f(f(v)) + f(v)"),
									"f commutes with negation",
									By(Normalized, HomNeg.Read(linear).At(fvM))),
								Leg(
									b.TermAs[B]("-f(v) + f(v)"),
									"f fixes f(v)",
									By(Normalized, idempotent.At(v), vM)),
								FinalLeg(
									"−f(v) cancels f(v)",
									By(group.LeftInverseOn.Read(additive).At(fvM))),
							))
						b.Show(
							"f(v) is a value of f, −f(v) + v a vector of M that f kills, and the two add up to v",
							By(
								set_image.FunInImage.At(f, b.TermAs[Set[B]]("M.carrier"), v),
								wM,
								kills,
								group_homomorphism.InKernel.At(b.TermAs[B]("M.zero"), b.TermAs[Set[B]]("M.carrier"), f, w),
								group.MulInvCancelLeftOn.Read(additive).At(fvM, vM)))
					})),
			))
		}),
})}

// KernelRetractionFromInnerInverse — an inner inverse gives a linear retraction
// onto the kernel: subtract g ∘ f from the identity. The resulting difference
// maps into the kernel and fixes each kernel vector.
var KernelRetractionFromInnerInverse = kernelRetractionFromInnerInverseThm{family.Add(registry.ProofEntry{
	Name: "KernelRetractionFromInnerInverse",
	Key:  "prop_7ac06b729ff22fb4",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, C). ∀f:(B → C). ∀g:(C → B).",
		Hypotheses: []string{
			"module_homomorphism(R, M, N, f)",
			"module_homomorphism(R, N, M, g)",
			"∀v:B. v ∈ M.carrier ⇒ f(g(f(v))) = f(v)",
		},
		Conclusion: "module_homomorphism(R, " +
			"    M, " +
			"    restrict_module(M, group_kernel(N.zero, M.carrier, f)), " +
			"    «P») ∧ " +
			"(∀v:B. v ∈ group_kernel(N.zero, M.carrier, f) ⇒ «P»(v) = v)",
		Abbrev: Abbrev{
			{Name: "P", Text: "λv:B. M.add(v, M.neg(g(f(v))))"},
		},
	}, func(
		a *Argument,
		R *Expr[RingOps[A]],
		M *Expr[ModuleOps[A, B]],
		N *Expr[ModuleOps[A, C]],
		f *Arrow[B, C],
		g *Arrow[C, B],
		hf, hg, inner Fact,
	) {
		source := HomSource.Read(hf)
		sourceGroup := module.AddGroupOn.Read(source)
		targetGroup := module.AddGroupOn.Read(HomTarget.Read(hf))
		composite := a.Have(
			"the inner inverse composed with f is linear",
			"module_homomorphism(R, M, M, g ∘ f)",
			By(hf, hg, HomCompose),
		)
		identity := a.TermAs[Fun[B, B]]("identity_map")
		gf := a.TermAs[Fun[B, B]]("g ∘ f")
		p := a.TermAs[Fun[B, B]]("«P»")
		difference := a.TermAs[Fun[B, B]]("λv:B. M.add(identity_map(v), M.neg((g ∘ f)(v)))")
		linear := a.Have(
			"subtracting the composite from the identity is linear",
			"module_homomorphism(R, M, M, «P»)",
			By(
				source,
				composite,
				HomIdentity.At(R, M),
				HomDiff.At(R, M, M, identity, gf),
				functions.IdentityApply,
				functions.ComposeApply.At(g, f),
				HomCongruence.At(R, M, M, difference, p)),
		)
		inKernel := a.Have(
			"the difference takes values in the kernel",
			"∀v:B. v ∈ M.carrier ⇒ «P»(v) ∈ group_kernel(N.zero, M.carrier, f)",
			Derive(func(b *Argument) {
				v := b.FixAs[B]("v")
				member := b.Assume()
				vm := proof.MemberOf(v, member)
				fv := proof.MemberOf(f.Apply(v), b.Have(
					"f carries v into N",
					"f(v) ∈ N.carrier",
					By(HomIn.Read(hf).At(vm))))
				gfv := proof.MemberOf(g.Apply(f.Apply(v)), b.Have(
					"and g carries f(v) back into M",
					"g(f(v)) ∈ M.carrier",
					By(HomIn.Read(hg).At(fv))))
				zeroImage := b.Have(
					"the two images cancel by the inner inverse identity",
					"f(«P»(v)) = N.zero",
					CalcEq(
						Leg(
							b.TermAs[C]("f(v) + f(-g(f(v)))"),
							"f carries the sum to the sum of the images",
							By(HomAdd.Read(hf).At(vm, group.InvIn.Read(sourceGroup).At(gfv)))),
						Leg(
							b.TermAs[C]("f(v) + -f(g(f(v)))"),
							"and the negative to the negative of the image",
							By(Normalized, HomNeg.Read(hf).At(gfv))),
						Leg(
							b.TermAs[C]("f(v) + -f(v)"),
							"the inner inverse identity at v",
							By(Normalized, inner.At(v), member)),
						FinalLeg(
							"which is N.zero",
							By(group.RightInverseOn.Read(targetGroup).At(fv))),
					))
				b.Show(
					"the difference belongs to the kernel",
					By(
						member,
						zeroImage,
						HomIn.Read(linear).AsFact().At(v),
						group_homomorphism.InKernel.At(b.TermAs[C]("N.zero"),
							b.TermAs[Set[B]]("M.carrier"), f, b.TermAs[B]("«P»(v)"))),
				)
			}),
		)
		a.Show(
			"the difference is linear into the kernel and fixes its vectors",
			SplitConj(
				Case(
					"corestricting the difference gives the kernel homomorphism",
					By(KernelSubmodule.Read(hf), inKernel, linear, HomCorestrict),
				),
				Case(
					"the difference fixes the kernel",
					Derive(func(b *Argument) {
						v := b.FixAs[B]("v")
						member := b.Assume()
						b.Show(
							"the difference fixes each kernel vector",
							By(
								HomZero.Read(hg),
								group.InvOneOn.Read(sourceGroup),
								member,
								group_homomorphism.InKernel.At(b.TermAs[C]("N.zero"),
									b.TermAs[Set[B]]("M.carrier"), f, v),
								group.RightIdentityOn.Read(sourceGroup).AsFact().At(v)),
						)
					}),
				),
			),
		)
	}),
})}

// ModuleCokernelOfSplitting — a split sequence identifies N with the cokernel
// of f: q kills the image of f and s is a section of q, so q is onto N; where
// f(h(w)) + s(q(w)) = w, a vector w of the kernel of q is f(h(w)), so the
// kernel of q is exactly the image of f; and the first isomorphism theorem,
// inverted, carries N onto the quotient of M by that image.
var ModuleCokernelOfSplitting = moduleCokernelOfSplittingThm{family.Add(registry.ProofEntry{
	Name: "ModuleCokernelOfSplitting",
	Key:  "prop_35ff1c20d7ae037",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀U:module_ops(A, B). " +
			"∀M:module_ops(A, C). " +
			"∀N:module_ops(A, D). " +
			"∀f:(B → C). " +
			"∀q:(C → D). " +
			"∀s:(D → C). " +
			"∀h:(C → B).",
		Hypotheses: []string{
			"module_homomorphism(R, U, M, f)",
			"module_homomorphism(R, M, N, q)",
			"module_homomorphism(R, N, M, s)",
			"module_homomorphism(R, M, U, h)",
			"∀v:B. v ∈ U.carrier ⇒ q(f(v)) = N.zero",
			"∀z:D. z ∈ N.carrier ⇒ q(s(z)) = z",
			"∀w:C. w ∈ M.carrier ⇒ M.add(f(h(w)), s(q(w))) = w",
		},
		Conclusion: "module_isomorphic(R, N, quotient_module(M, image(f, U.carrier)))",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			U *Expr[ModuleOps[A, B]],
			M *Expr[ModuleOps[A, C]],
			N *Expr[ModuleOps[A, D]],
			f *Arrow[B, C],
			q *Arrow[C, D],
			s *Arrow[D, C],
			h *Arrow[C, B],
			fLinear, qLinear, sLinear, hLinear, killed, section, splitting Fact,
		) {
			onto := a.Have(
				"the section makes q onto N",
				"image(q, M.carrier) = N.carrier",
				BySets(HomIn.Read(qLinear), HomIn.Read(sLinear), section))
			preimages := a.Have(
				"the splitting equation supplies a preimage of every kernel vector",
				"∀w:C. w ∈ group_kernel(N.zero, M.carrier, q) ⇒ h(w) ∈ U.carrier ∧ f(h(w)) = w",
				Derive(func(b *Argument) {
					w := b.FixAs[C]("w")
					member := b.Assume()
					b.Show(
						"on the kernel the section term vanishes, leaving f(h(w)) = w",
						By(
							HomZero.Read(sLinear),
							member,
							splitting.At(w),
							group_homomorphism.InKernel,
							HomIn.Read(hLinear).AsFact().At(w),
							HomIn.Read(fLinear).AsFact().At(h.Apply(w)),
							group.RightIdentityOn.Read(module.AddGroupOn.Read(HomSource.Read(hLinear))).AsFact().At(
								f.Apply(h.Apply(w)))))
				}))
			kernel := a.Have(
				"the kernel of q is exactly the image of f",
				"image(f, U.carrier) = group_kernel(N.zero, M.carrier, q)",
				BySets(HomIn.Read(fLinear), killed, preimages, group_homomorphism.InKernel))
			Q := a.TermAs[ModuleOps[A, Set[C]]]("quotient_module(M, image(f, U.carrier))")
			induced := a.TermAs[Fun[Set[C], D]]("induced_map(q)")
			quotientIso := a.Have(
				"the first isomorphism theorem identifies the quotient with N",
				"module_isomorphism(R, quotient_module(M, image(f, U.carrier)), N, induced_map(q))",
				By(FirstIsomorphism.Read(qLinear), kernel, onto, module_record.RestrictModuleCarrier.At(N)))
			a.Show(
				"inverted, this isomorphism carries N onto the quotient",
				Simp(Fwd(ModuleIsomorphicDef)),
				Witness(a.TermAs[Fun[D, Set[C]]](
					"inverse_on(quotient_module(M, image(f, U.carrier)).carrier, induced_map(q))")),
				By(quotientIso, IsomorphismInverse.At(R, Q, N, induced)))
		}),
})}
