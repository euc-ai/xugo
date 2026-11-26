// annihilator.go — the standard pairing ⟨v, a⟩ = Σ_{i∈S} v(i) * a(i) on the
// coordinate space R^S of a finite set S, and the dimension of an
// annihilator. The pairing is bilinear and nondegenerate, and a vector
// pairing to zero with a set pairs to zero with its span. Pairing against a
// finite set X of vectors is a linear map into the coordinates on X, onto
// them when X is independent; its kernel is the annihilator of X, so the
// span of a set and its annihilator have dimensions adding to |S|. Over the
// reals, a homogeneous system with fewer rows than unknowns has a nonzero
// solution, and a vector supported on a strict majority H of a finite V can
// be chosen so that the rows indexed outside H kill it.

package module_dimension

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/abelian_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/free_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/function_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/linear_independence"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	"github.com/euc-ai/xugo/library/proofs/real/real_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// StandardPairingBilinear — over a commutative ring R and a finite set S,
// the standard pairing of R^S with itself is bilinear. Pairing with a fixed
// vector a is the linear extension of a from the points of S (FreeLiftHom),
// its sum over the support read over all of S (FreeLiftOver); pairing with a
// fixed u in the other argument is the same map at u, the products commuting.
var StandardPairingBilinear = standardPairingBilinearThm{family.Add(registry.ProofEntry{
	Name: "StandardPairingBilinear",
	Key:  "prop_81ab388d9936a724",
	Build: family.Theorem(Statement{
		Binders:    "∀R:comm_ring_on(A). ∀S:set(D).",
		Hypotheses: []string{"finite(S)"},
		Conclusion: "bilinear_map(R, " +
			"    free_module_record(R, S), " +
			"    free_module_record(R, S), " +
			"    regular_module(R), " +
			"    λv:D → A. λa:D → A. module_sum(R.add, R.zero, S, λi:D. v(i) * a(i)))",
	}, func(arg *Argument, R comm_ring.CommRingFact[on.R], S *Expr[Set[D]], finiteS Fact) {
		ring := arg.TermAs[RingOps[A]]("R")
		regular := arg.TermAs[ModuleOps[A, A]]("regular_module(R)")
		regularOn := module.RegularModuleOn.Read(R)
		firstSlot := arg.Have(
			"pairing against a vector a of R^S is linear in the first argument",
			Statement{
				Binders:    "∀a:D → A.",
				Hypotheses: []string{"a ∈ free_module_record(R, S).carrier"},
				Conclusion: "module_homomorphism(R, " +
					"    free_module_record(R, S), " +
					"    regular_module(R), " +
					"    λv:D → A. module_sum(R.add, R.zero, S, λi:D. v(i) * a(i)))",
			},
			Derive(func(b *Argument) {
				a := b.FixAs[Fun[D, A]]("a")
				aIn := b.Assume()
				values := b.Have(
					"a takes its values in R",
					"∀x:D. a(x) ∈ R.carrier",
					By(aIn, function_module.FiniteSuppMember))
				extension := b.Have(
					"on R^S the pairing against a is the linear extension of a, its sum over the support read over S",
					Statement{
						Binders:    "∀v:D → A.",
						Hypotheses: []string{"v ∈ free_module_record(R, S).carrier"},
						Conclusion: "module_sum(R.add, R.zero, S, λi:D. v(i) * a(i)) = " +
							"free_lift(R.zero, R.add, R.zero, R.mul, a, v)",
					},
					Derive(func(c *Argument) {
						v := c.FixAs[Fun[D, A]]("v")
						vIn := c.Assume()
						c.Show(
							"v is supported in the finite S, and v and a take values in R",
							By(
								regularOn,
								finiteS,
								vIn,
								aIn,
								free_module.FreeLiftOver.At(ring, regular, S, a, v),
								function_module.FiniteSuppMember))
					}))
				b.Show(
					"the linear extension of a is linear, and the pairing agrees with it on R^S",
					By(
						regularOn,
						values,
						extension,
						Where(module_homomorphism.HomCongruence, "f", b.Term("free_lift(R.zero, R.add, R.zero, R.mul, a)")),
						free_module.FreeLiftHom.At(ring, regular, S, a)))
			}))
		secondSlot := arg.Have(
			"pairing against a vector u of R^S is linear in the second argument",
			Statement{
				Binders:    "∀u:D → A.",
				Hypotheses: []string{"u ∈ free_module_record(R, S).carrier"},
				Conclusion: "module_homomorphism(R, " +
					"    free_module_record(R, S), " +
					"    regular_module(R), " +
					"    λa:D → A. module_sum(R.add, R.zero, S, λi:D. u(i) * a(i)))",
			},
			Derive(func(b *Argument) {
				u := b.FixAs[Fun[D, A]]("u")
				uIn := b.Assume()
				commute := b.Have(
					"the products commute termwise, so on R^S the pairing "+
						"against u in the second argument is the pairing in the first",
					Statement{
						Binders:    "∀a:D → A.",
						Hypotheses: []string{"a ∈ free_module_record(R, S).carrier"},
						Conclusion: "module_sum(R.add, R.zero, S, λi:D. u(i) * a(i)) = " +
							"module_sum(R.add, R.zero, S, λi:D. a(i) * u(i))",
					},
					Derive(func(c *Argument) {
						c.FixAs[Fun[D, A]]("a")
						aIn := c.Assume()
						c.Show(
							"u(i) and a(i) lie in R, whose product commutes",
							By(
								aIn,
								uIn,
								module.ModuleSumCongruence,
								comm_monoid.CommOn.Read(comm_ring.MulMonoidOn.Read(R)),
								function_module.FiniteSuppMember))
					}))
				b.Show(
					"a map agreeing on R^S with a linear one is linear",
					By(commute, firstSlot.At(u), uIn, module_homomorphism.HomCongruence))
			}))
		arg.Show(
			"both families of slices are linear",
			By(firstSlot, secondSlot, module_homomorphism.BilinearMapDef))
	}),
})}

// StandardPairingNondegenerate — over a commutative ring R and a finite set
// S, the only vector of R^S pairing to zero with every vector of R^S is
// zero. At a point j of S, pairing with the point mass at j reads the
// coordinate a(j) (FreeLiftDelta, the pairing being the linear extension of
// a), so a(j) is zero; off S every vector of R^S is zero already.
var StandardPairingNondegenerate = standardPairingNondegenerateThm{family.Add(registry.ProofEntry{
	Name: "StandardPairingNondegenerate",
	Key:  "prop_5e98514d37ca7ad4",
	Build: family.Theorem(Statement{
		Binders: "∀R:comm_ring_on(A). ∀S:set(D). ∀a:D → A.",
		Hypotheses: []string{
			"finite(S)",
			"a ∈ free_module_record(R, S).carrier",
			"∀x:D → A. " +
				"    x ∈ free_module_record(R, S).carrier ⇒ " +
				"    module_sum(R.add, R.zero, S, λi:D. x(i) * a(i)) = R.zero",
		},
		Conclusion: "a = free_module_record(R, S).zero",
	}, func(
		arg *Argument,
		R comm_ring.CommRingFact[on.R],
		S *Expr[Set[D]],
		a *Arrow[D, A],
		finiteS, aIn, orthogonal Fact,
	) {
		ring := arg.TermAs[RingOps[A]]("R")
		regular := arg.TermAs[ModuleOps[A, A]]("regular_module(R)")
		values := arg.Have(
			"a takes its values in R",
			"∀x:D. a(x) ∈ R.carrier",
			By(aIn, function_module.FiniteSuppMember))
		coordinates := arg.Have(
			"every coordinate of a is zero",
			"∀j:D. a(j) = R.zero",
			Derive(func(b *Argument) {
				j := b.FixAs[D]("j")
				b.Cases(b.Term("j ∈ S"))
				b.When(
					"at a point j of S, a(j) is the pairing of the point mass at j with a",
					func(c *Argument, jIn Fact) {
						mass := c.TermAs[Fun[D, A]]("delta_at(R.zero, R.one, j)")
						massIn := free_module.DeltaAtIn.Read(R).At(S, j)
						massParts := c.Have(
							"the point mass at j is supported in S, with values in R",
							"fun_support(R.zero, delta_at(R.zero, R.one, j)) ⊆ S ∧ "+
								"(∀x:D. delta_at(R.zero, R.one, j, x) ∈ R.carrier)",
							By(jIn, massIn, function_module.FiniteSuppMember))
						reads := c.Have(
							"pairing the point mass at j with a reads the coordinate at j",
							"module_sum(R.add, R.zero, S, λi:D. delta_at(R.zero, R.one, j, i) * a(i)) = a(j)",
							By(
								finiteS,
								values,
								jIn,
								massParts,
								free_module.FreeLiftOver.At(ring, regular, S, a, mass),
								free_module.FreeLiftDelta.At(ring, regular, S, a, j),
								module.RegularModuleOn.Read(R)))
						c.Show(
							"and the point mass, a vector of R^S, pairs to zero with a",
							By(reads, jIn, orthogonal.At(mass), massIn))
					})
				b.Otherwise(
					"off S, a vector of R^S vanishes",
					func(c *Argument, jOut Fact) {
						c.Show(
							"a lies in R^S",
							By(
								jOut,
								c.Simplified(aIn, Fwd(free_module.FreeModuleRecordDef), Fwd(function_module.FiniteSuppDef))))
					})
			}))
		arg.Show(
			"so a is the zero vector, the zero function",
			Simp(Fwd(free_module.FreeModuleRecordDef)),
			Funext(),
			By(coordinates, function_module.FunZeroDef))
	}),
})}

// StandardPairingVanishesOnSpan — over a commutative ring R and a finite set
// S, a vector a of R^S pairing to zero with every member of a set X of
// vectors pairs to zero with every vector of the span of X. The pairing
// against a is linear in its first argument (StandardPairingBilinear), so the
// vectors pairing to zero with a are its kernel, a submodule holding X and so
// the span of X (SpanLeast).
var StandardPairingVanishesOnSpan = standardPairingVanishesOnSpanThm{family.Add(registry.ProofEntry{
	Name: "StandardPairingVanishesOnSpan",
	Key:  "prop_43363541bb0a20fa",
	Build: family.Theorem(Statement{
		Binders: "∀R:comm_ring_on(A). ∀S:set(D). ∀X:set(D → A). ∀a x:D → A.",
		Hypotheses: []string{
			"finite(S)",
			"X ⊆ free_module_record(R, S).carrier",
			"a ∈ free_module_record(R, S).carrier",
			"∀y:D → A. y ∈ X ⇒ module_sum(R.add, R.zero, S, λi:D. y(i) * a(i)) = R.zero",
			"x ∈ module_span(R, free_module_record(R, S), X)",
		},
		Conclusion: "module_sum(R.add, R.zero, S, λi:D. x(i) * a(i)) = R.zero",
		Abbrev: Abbrev{
			{Name: "orthogonal", Text: "group_kernel(R.zero, " +
				"    free_module_record(R, S).carrier, " +
				"    λv:D → A. module_sum(R.add, R.zero, S, λi:D. v(i) * a(i)))"},
		},
	}, func(
		arg *Argument,
		R comm_ring.CommRingFact[on.R],
		S *Expr[Set[D]],
		X *Expr[Set[Fun[D, A]]],
		a, x *Arrow[D, A],
		finiteS, inSpace, aIn, vanishes, xInSpan Fact,
	) {
		bilinear := arg.Have(
			"the pairing is bilinear",
			"bilinear_map(R, "+
				"    free_module_record(R, S), "+
				"    free_module_record(R, S), "+
				"    regular_module(R), "+
				"    λv:D → A. λw:D → A. module_sum(R.add, R.zero, S, λi:D. v(i) * w(i)))",
			By(finiteS, StandardPairingBilinear.Read(R).At(S)))
		slices := arg.Conjuncts(
			arg.Unfolded(bilinear, module_homomorphism.BilinearMapDef),
			"pairing against a vector is linear in the second argument",
			"pairing against a vector is linear in the first argument")
		linear := arg.Have(
			"pairing against a is linear in the first argument",
			"module_homomorphism(R, "+
				"    free_module_record(R, S), "+
				"    regular_module(R), "+
				"    λv:D → A. module_sum(R.add, R.zero, S, λi:D. v(i) * a(i)))",
			By(slices[1].At(a), aIn))
		inside := arg.Have(
			"X lies in the kernel of the pairing against a",
			"X ⊆ «orthogonal»",
			BySets(inSpace, vanishes, group_homomorphism.GroupKernelDef))
		spanInside := arg.Have(
			"and so does the span of X, the kernel being a submodule",
			"module_span(R, free_module_record(R, S), X) ⊆ «orthogonal»",
			By(inside, submodule.SpanLeast, module_homomorphism.KernelSubmodule.Read(linear)))
		arg.Show(
			"x lies in the span of X, inside that kernel",
			By(xInSpan, spanInside, group_homomorphism.InKernel, set_basic.SubsetDef))
	}),
})}

// PairingMapLinear — over a commutative ring R, for a finite set S and a
// finite set X of vectors of R^S, pairing a vector a against the members of
// X is a linear map of R^S into R^X: a goes to the function u ↦ ⟨u, a⟩ on X,
// zero off X. Its values lie in R and vanish off the finite X, and it adds
// and scales pointwise, the pairing against each u of X being linear in its
// second argument (StandardPairingBilinear); off X both sides are zero.
var PairingMapLinear = pairingMapLinearThm{family.Add(registry.ProofEntry{
	Name: "PairingMapLinear",
	Key:  "prop_9daf637cb60bc4b5",
	Build: family.Theorem(Statement{
		Binders: "∀R:comm_ring_on(A). ∀S:set(D). ∀X:set(D → A).",
		Hypotheses: []string{
			"finite(S)",
			"finite(X)",
			"X ⊆ free_module_record(R, S).carrier",
		},
		Conclusion: "module_homomorphism(R, " +
			"    free_module_record(R, S), " +
			"    free_module_record(R, X), " +
			"    «pairings»)",
		Abbrev: Abbrev{
			{Name: "pairings", Text: "λa:D → A. λu:D → A. " +
				"    COND(u ∈ X, module_sum(R.add, R.zero, S, λi:D. u(i) * a(i)), R.zero)"},
		},
	}, func(
		arg *Argument,
		R comm_ring.CommRingFact[on.R],
		S *Expr[Set[D]],
		X *Expr[Set[Fun[D, A]]],
		finiteS, finiteX, inSpace Fact,
	) {
		ring := arg.TermAs[RingOps[A]]("R")
		space := arg.TermAs[ModuleOps[A, Fun[D, A]]]("free_module_record(R, S)")
		regular := arg.TermAs[ModuleOps[A, A]]("regular_module(R)")
		pairing := arg.TermAs[Fun2[Fun[D, A], Fun[D, A], A]](
			"λv:D → A. λw:D → A. module_sum(R.add, R.zero, S, λi:D. v(i) * w(i))")
		bilinear := arg.Have(
			"the pairing is bilinear",
			"bilinear_map(R, "+
				"    free_module_record(R, S), "+
				"    free_module_record(R, S), "+
				"    regular_module(R), "+
				"    λv:D → A. λw:D → A. module_sum(R.add, R.zero, S, λi:D. v(i) * w(i)))",
			By(finiteS, StandardPairingBilinear.Read(R).At(S)))
		clauses := arg.Conjuncts(
			GroupPremises(
				free_module.FreeModuleOn.Read(R).At(S),
				bilinear,
				module_homomorphism.BilinearMapClauses.At(ring, space, space, regular, pairing)),
			"R^S is a module",
			"R is a module over itself",
			"the pairing of two vectors lies in R",
			"it adds in the first argument",
			"and in the second",
			"it scales in the first argument",
			"and in the second")
		inR, addsSecond, scalesSecond := clauses[2], clauses[4], clauses[6]
		vectorsOfX := func(b *Argument, uInX Fact) Fact {
			return b.Have(
				"u is a vector of R^S",
				"u ∈ free_module_record(R, S).carrier",
				By(uInX, inSpace, set_basic.SubsetDef))
		}
		arg.Show(
			"the pairing map is a linear map of R^S into R^X",
			module_homomorphism.ModuleHomomorphismDef.Intro(
				Case(
					"R^S is a module",
					By(free_module.FreeModuleOn.Read(R).At(S))),
				Case(
					"so is R^X",
					By(free_module.FreeModuleOn.Read(R).At(X))),
				Case(
					"pairing a vector of R^S against X gives a function on X with values in R",
					Derive(func(b *Argument) {
						a := b.FixAs[Fun[D, A]]("a")
						aIn := b.Assume()
						values := b.Have(
							"its values lie in R",
							"∀u:D → A. COND(u ∈ X, module_sum(R.add, R.zero, S, λi:D. u(i) * a(i)), R.zero) ∈ R.carrier",
							Derive(func(c *Argument) {
								u := c.FixAs[Fun[D, A]]("u")
								c.Cases(c.Term("u ∈ X"))
								c.When(
									"at u in X the value is the pairing of two vectors of R^S",
									func(d *Argument, uInX Fact) {
										d.Show(
											"which lies in R",
											By(vectorsOfX(d, uInX), aIn, uInX, inR.At(u, a)))
									})
								c.Otherwise(
									"off X the value is zero",
									func(d *Argument, uOut Fact) {
										d.Show(
											"which lies in R",
											By(uOut, comm_ring.ZeroIn.Read(R)))
									})
							}))
						support := b.Have(
							"it vanishes off X",
							"fun_support(R.zero, "+
								"    λu:D → A. COND(u ∈ X, module_sum(R.add, R.zero, S, λi:D. u(i) * a(i)), R.zero)) ⊆ "+
								"X",
							BySets())
						b.Show(
							"so its support, a part of the finite X, is finite",
							By(values, support, finiteX, finite_set.FiniteSubset, function_module.FiniteSuppMember))
					})),
				Case(
					"the pairings of a sum are the sums of the pairings",
					Derive(func(b *Argument) {
						v := b.FixAs[Fun[D, A]]("v")
						w := b.FixAs[Fun[D, A]]("w")
						both := b.Assume()
						b.Do(Funext())
						u := b.FixAs[Fun[D, A]]("u")
						b.Cases(b.Term("u ∈ X"))
						b.When(
							"at u in X, the pairing against u adds",
							func(d *Argument, uInX Fact) {
								d.Show(
									"⟨u, v + w⟩ = ⟨u, v⟩ + ⟨u, w⟩",
									GroupPremises(vectorsOfX(d, uInX), both, addsSecond.At(u, v, w)).Rw(),
									Simp(Fwd(function_module.FunAddDef)),
									Refl())
							})
						b.Otherwise(
							"off X both sides are zero",
							func(d *Argument, uOut Fact) {
								d.Show(
									"zero is zero plus zero",
									Simp(Fwd(function_module.FunAddDef)),
									By(comm_monoid.LeftIdentityOn.Read(comm_ring.AddMonoidOn.Read(R)), comm_ring.ZeroIn.Read(R)))
							})
					})),
				Case(
					"the pairings of a multiple are the multiples of the pairings",
					Derive(func(b *Argument) {
						c := b.FixAs[A]("c")
						v := b.FixAs[Fun[D, A]]("v")
						both := b.Assume()
						b.Do(Funext())
						u := b.FixAs[Fun[D, A]]("u")
						b.Cases(b.Term("u ∈ X"))
						b.When(
							"at u in X, the pairing against u scales",
							func(d *Argument, uInX Fact) {
								d.Show(
									"⟨u, c • v⟩ = c * ⟨u, v⟩",
									GroupPremises(vectorsOfX(d, uInX), both, scalesSecond.At(c, u, v)).Rw(),
									Simp(Fwd(function_module.FunSmulDef)),
									Refl())
							})
						b.Otherwise(
							"off X both sides are zero",
							func(d *Argument, uOut Fact) {
								d.Show(
									"c times zero is zero",
									Simp(Fwd(function_module.FunSmulDef)),
									By(both, comm_ring.MulRightZeroOn.Read(R)))
							})
					}))))
	}),
})}

// IndependentPairingsOnto — over a field F, for a finite set S and an
// independent set B of vectors of F^S, every function on B is the pairing
// against B of some vector: pairing against B maps F^S onto F^B. For a basis
// B this is a count: a vector pairing to zero with B pairs to zero with its
// span, all of F^S (StandardPairingVanishesOnSpan), and so is zero
// (StandardPairingNondegenerate); the pairing map is one-to-one between two
// spaces of dimension |S|, hence onto. An independent B extends to a basis E
// (BasisExtends); a function on B, extended by zero to E, is the pairing
// against E of some a, and the pairing of a against B is the function itself.
var IndependentPairingsOnto = independentPairingsOntoThm{family.Add(registry.ProofEntry{
	Name: "IndependentPairingsOnto",
	Key:  "prop_833991be59b11fa9",
	Build: family.Sections(Statement{
		Binders: "∀F:field_on(A). ∀S:set(D). ∀B:set(D → A).",
		Hypotheses: []string{
			"finite(S)",
			"module_independent(field_ring(F), «space», B)",
		},
		Conclusion: "image(«pairings», «space».carrier) = free_module_record(field_ring(F), B).carrier",
		Abbrev: Abbrev{
			{Name: "space", Text: "free_module_record(field_ring(F), S)"},
			{Name: "pairings", Text: "λa:D → A. λu:D → A. " +
				"    COND(u ∈ B, module_sum(F.add, F.zero, S, λi:D. u(i) * a(i)), F.zero)"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		basisOnto := ctx.Lemma(Statement{
			Binders: "∀F:field_on(A). ∀S:set(D). ∀B:set(D → A).",
			Hypotheses: []string{
				"finite(S)",
				"module_basis(field_ring(F), «space», B)",
			},
			Conclusion: "image(«pairings», finite_supp(F.zero, F.carrier, S)) = " +
				"finite_supp(F.zero, F.carrier, B)",
		}, func(
			arg *Argument,
			F field.FieldFact[on.F],
			S *Expr[Set[D]],
			B *Expr[Set[Fun[D, A]]],
			finiteS, basis Fact,
		) {
			ring := field.RingOn.Read(F)
			R := arg.TermAs[RingOps[A]]("field_ring(F)")
			inv := arg.TermAs[Fun[A, A]]("F.inv")
			space := arg.TermAs[ModuleOps[A, Fun[D, A]]]("«space»")
			coordinates := arg.TermAs[ModuleOps[A, Fun[Fun[D, A], A]]]("free_module_record(field_ring(F), B)")
			pairings := arg.TermAs[Fun2[Fun[D, A], Fun[D, A], A]]("«pairings»")
			scalarsField := arg.Have(
				"F is a field on its own carrier",
				"ring_subfield(field_ring(F), F.inv, field_ring(F).carrier)",
				By(field.FieldRingSubfield.Read(F)))
			moduleS := arg.Have(
				"F^S is a module over F",
				"module_on(field_ring(F), «space»)",
				By(free_module.FreeModuleOn.Read(ring).At(S)))
			dimensionS := arg.Conjuncts(
				GroupPremises(scalarsField, finiteS, FreeModuleFiniteDim.At(R, inv, S)),
				"F^S is finite-dimensional",
				"of dimension |S|")
			size := arg.Conjuncts(
				GroupPremises(
					moduleS, scalarsField, dimensionS[0], basis, FiniteDimensionalBasis.At(R, space, inv, B)),
				"the basis B is finite",
				"of the dimension of F^S")
			parts := arg.Conjuncts(
				arg.Unfolded(basis, linear_independence.ModuleBasisDef),
				"B is independent",
				"B spans F^S")
			inSpace := arg.Have(
				"B lies in F^S",
				"B ⊆ «space».carrier",
				By(parts[0], linear_independence.IndependentInCarrier))
			linear := arg.Have(
				"pairing against B is a linear map of F^S into F^B",
				"module_homomorphism(field_ring(F), «space», free_module_record(field_ring(F), B), «pairings»)",
				By(ring, finiteS, size[0], inSpace, PairingMapLinear.Read(ring).At(S, B)))
			trivial := arg.Have(
				"only zero pairs to zero with every member of B",
				Statement{
					Binders: "∀a:D → A.",
					Hypotheses: []string{
						"a ∈ group_kernel(fun_zero(F.zero), finite_supp(F.zero, F.carrier, S), «pairings»)",
					},
					Conclusion: "a = fun_zero(F.zero)",
				},
				Derive(func(b *Argument) {
					a := b.FixAs[Fun[D, A]]("a")
					kernelParts := b.Conjuncts(
						b.Simplified(b.Assume(), Fwd(group_homomorphism.GroupKernelDef)),
						"a lies in F^S",
						"its pairings against B are zero")
					vanishes := b.Have(
						"a pairs to zero with every member of B",
						"∀u:(D → A). u ∈ B ⇒ module_sum(F.add, F.zero, S, λi:D. u(i) * a(i)) = F.zero",
						By(kernelParts[1], function_module.FunZeroDef))
					everywhere := b.Have(
						"so a pairs to zero with the span of B, all of F^S",
						"∀x:(D → A). x ∈ «space».carrier ⇒ module_sum(F.add, F.zero, S, λi:D. x(i) * a(i)) = F.zero",
						Derive(func(c *Argument) {
							x := c.FixAs[Fun[D, A]]("x")
							inSpan := c.Have(
								"x lies in the span of B, which is F^S",
								"x ∈ module_span(field_ring(F), «space», B)",
								By(c.Assume(), parts[1]))
							c.Show(
								"the pairing against a vanishes on the span of B",
								By(
									ring,
									finiteS,
									inSpace,
									kernelParts[0],
									vanishes,
									inSpan,
									StandardPairingVanishesOnSpan.Read(ring).At(S, B, a, x)))
						}))
					b.Show(
						"a is zero, the pairing being nondegenerate",
						By(ring, finiteS, kernelParts[0], everywhere, StandardPairingNondegenerate.Read(ring).At(S, a)))
				}))
			zeroIn := arg.Have(
				"the zero vector lies in the kernel, a subspace of F^S",
				"fun_zero(F.zero) ∈ group_kernel(fun_zero(F.zero), finite_supp(F.zero, F.carrier, S), «pairings»)",
				By(submodule.SubmoduleZero.Read(module_homomorphism.KernelSubmodule.Read(linear))))
			kernelZero := arg.Have(
				"so the kernel of the pairing map is zero",
				"group_kernel(fun_zero(F.zero), finite_supp(F.zero, F.carrier, S), «pairings») = "+
					"{fun_zero(F.zero)}",
				BySets(trivial, zeroIn))
			injective := arg.Have(
				"so the pairing map is one-to-one",
				"injective_on(finite_supp(F.zero, F.carrier, S), «pairings»)",
				By(kernelZero, module_homomorphism.KernelTrivialIffInjective.Read(linear)))
			dimensionB := arg.Conjuncts(
				GroupPremises(scalarsField, size[0], FreeModuleFiniteDim.At(R, inv, B)),
				"F^B is finite-dimensional",
				"of dimension |B|")
			image := arg.TermAs[Set[Fun[Fun[D, A], A]]]("image(«pairings», finite_supp(F.zero, F.carrier, S))")
			full := arg.Have(
				"its image has the dimension of F^S, |S| = |B|, which is that of F^B",
				"module_dim(field_ring(F), "+
					"    restrict_module(free_module_record(field_ring(F), B), "+
					"        image(«pairings», finite_supp(F.zero, F.carrier, S)))) = "+
					"module_dim(field_ring(F), free_module_record(field_ring(F), B))",
				ByArith(
					dimensionS[0],
					dimensionS[1],
					dimensionB[1],
					size[1],
					injective,
					linear,
					scalarsField,
					InjectiveImageDim.At(R, inv, space, coordinates, pairings)))
			arg.Show(
				"a subspace of F^B of the full dimension is F^B",
				By(
					full,
					free_module.FreeModuleOn.Read(ring).At(B),
					dimensionB[0],
					scalarsField,
					module_homomorphism.ImageSubmodule.Read(linear),
					SubmoduleDimEq.At(R, coordinates, inv, image)))
		})
		return ctx.Theorem(headline, func(
			arg *Argument,
			F field.FieldFact[on.F],
			S *Expr[Set[D]],
			B *Expr[Set[Fun[D, A]]],
			finiteS, independent Fact,
		) {
			ring := field.RingOn.Read(F)
			R := arg.TermAs[RingOps[A]]("field_ring(F)")
			inv := arg.TermAs[Fun[A, A]]("F.inv")
			space := arg.TermAs[ModuleOps[A, Fun[D, A]]]("«space»")
			pairings := arg.TermAs[Fun2[Fun[D, A], Fun[D, A], A]]("«pairings»")
			scalarsField := arg.Have(
				"F is a field on its own carrier",
				"ring_subfield(field_ring(F), F.inv, field_ring(F).carrier)",
				By(field.FieldRingSubfield.Read(F)))
			moduleS := arg.Have(
				"F^S is a module over F",
				"module_on(field_ring(F), «space»)",
				By(free_module.FreeModuleOn.Read(ring).At(S)))
			dimensionS := arg.Conjuncts(
				GroupPremises(scalarsField, finiteS, FreeModuleFiniteDim.At(R, inv, S)),
				"F^S is finite-dimensional",
				"of dimension |S|")
			finiteB := arg.Conjuncts(
				GroupPremises(
					moduleS, scalarsField, dimensionS[0], independent, IndependentBound.At(R, space, inv, B)),
				"B is finite",
				"no larger than the dimension of F^S")
			inSpace := arg.Have(
				"B lies in F^S",
				"B ⊆ «space».carrier",
				By(independent, linear_independence.IndependentInCarrier))
			linear := arg.Have(
				"pairing against B is a linear map of F^S into F^B",
				"module_homomorphism(field_ring(F), «space», free_module_record(field_ring(F), B), «pairings»)",
				By(ring, finiteS, finiteB[0], inSpace, PairingMapLinear.Read(ring).At(S, B)))
			into := arg.Have(
				"so it maps F^S into F^B",
				"image(«pairings», finite_supp(F.zero, F.carrier, S)) ⊆ finite_supp(F.zero, F.carrier, B)",
				By(submodule.SubmoduleSubset.Read(module_homomorphism.ImageSubmodule.Read(linear))))
			_, extension := arg.ObtainAs[Set[Fun[D, A]]](
				"B extends to a basis E of F^S",
				"∃E:set(D → A). B ⊆ E ∧ module_basis(field_ring(F), «space», E)",
				By(moduleS, scalarsField, independent, linear_independence.BasisExtends))
			parts := arg.Conjuncts(
				extension,
				"B lies in E",
				"E is a basis of F^S")
			ontoE := arg.Have(
				"pairing against the basis E maps F^S onto F^E",
				"image(λa:D → A. λu:D → A. COND(u ∈ E, module_sum(F.add, F.zero, S, λi:D. u(i) * a(i)), F.zero), "+
					"    finite_supp(F.zero, F.carrier, S)) = "+
					"finite_supp(F.zero, F.carrier, E)",
				By(F, finiteS, parts[1], basisOnto))
			onto := arg.Have(
				"and every function on B is the pairing against B of a vector of F^S",
				"finite_supp(F.zero, F.carrier, B) ⊆ image(«pairings», finite_supp(F.zero, F.carrier, S))",
				Derive(func(b *Argument) {
					b.Do(Simp(Fwd(set_basic.SubsetDef)))
					b.FixAs[Fun[Fun[D, A], A]]("c")
					cIn := b.Assume()
					onE := b.Have(
						"c, vanishing off B, vanishes off E",
						"c ∈ finite_supp(F.zero, F.carrier, E)",
						By(cIn, parts[0], function_module.FiniteSuppMember, set_order.SubsetTrans))
					attained := b.Have(
						"so c is attained by pairing against E",
						"c ∈ "+
							"image(λa:D → A. λu:D → A. COND(u ∈ E, module_sum(F.add, F.zero, S, λi:D. u(i) * a(i)), F.zero), "+
							"    finite_supp(F.zero, F.carrier, S))",
						By(ontoE, onE))
					a, preimage := b.ObtainAs[Fun[D, A]](
						"c is the pairing against E of some vector a of F^S",
						"∃a:D → A. "+
							"    c = (λu:D → A. COND(u ∈ E, module_sum(F.add, F.zero, S, λi:D. u(i) * a(i)), F.zero)) ∧ "+
							"    a ∈ finite_supp(F.zero, F.carrier, S)",
						By(attained, set_basic.InImage))
					pieces := b.Conjuncts(
						preimage,
						"c is the pairing against E of a",
						"a lies in F^S")
					agree := b.Have(
						"the pairing of a against B is c",
						"«pairings»(a) = c",
						Derive(func(d *Argument) {
							d.Do(Funext())
							d.FixAs[Fun[D, A]]("u")
							d.Cases(d.Term("u ∈ B"))
							d.When(
								"at u in B, a member of E, both are the pairing of u with a",
								func(e *Argument, uInB Fact) {
									e.Show(
										"c(u) is the pairing of u with a",
										By(pieces[0], uInB, parts[0], set_basic.SubsetDef))
								})
							d.Otherwise(
								"off B both vanish",
								func(e *Argument, uOut Fact) {
									e.Show(
										"c vanishes off B",
										By(uOut, e.Simplified(cIn, Fwd(function_module.FiniteSuppDef))))
								})
						}))
					b.Show(
						"so c is the pairing against B of a vector of F^S",
						By(
							agree,
							pieces[1],
							set_image.FunInImage.At(
								pairings, arg.TermAs[Set[Fun[D, A]]]("finite_supp(F.zero, F.carrier, S)"), a)))
				}))
			arg.Show(
				"pairing against B maps F^S onto F^B",
				By(into, onto, set_order.SubsetAntisym))
		})
	}),
})}

// AnnihilatorSubspace — over a commutative ring R and a finite set S, the
// vectors of R^S pairing to zero with every member of a set V of vectors
// form a submodule. Pairing against each v of V is linear in the second
// argument (StandardPairingBilinear), so it sends the zero vector to zero,
// and the sum and the scalar multiples of vectors it sends to zero to zero
// again (SubmoduleCriterion).
var AnnihilatorSubspace = annihilatorSubspaceThm{family.Add(registry.ProofEntry{
	Name: "AnnihilatorSubspace",
	Key:  "prop_36b361929cb2297b",
	Build: family.Theorem(Statement{
		Binders: "∀R:comm_ring_on(A). ∀S:set(D). ∀V:set(D → A).",
		Hypotheses: []string{
			"finite(S)",
			"V ⊆ free_module_record(R, S).carrier",
		},
		Conclusion: "submodule(R, free_module_record(R, S), «annihilator»)",
		Abbrev: Abbrev{
			{Name: "annihilator", Text: "{a:D → A | " +
				"    a ∈ free_module_record(R, S).carrier ∧ " +
				"    (∀v:D → A. v ∈ V ⇒ module_sum(R.add, R.zero, S, λi:D. v(i) * a(i)) = R.zero)}"},
			{Name: "pairing", Text: "λv:D → A. λa:D → A. module_sum(R.add, R.zero, S, λi:D. v(i) * a(i))"},
		},
	}, func(
		arg *Argument,
		R comm_ring.CommRingFact[on.R],
		S *Expr[Set[D]],
		V *Expr[Set[Fun[D, A]]],
		finiteS, inSpace Fact,
	) {
		ring := arg.TermAs[RingOps[A]]("R")
		space := arg.TermAs[ModuleOps[A, Fun[D, A]]]("free_module_record(R, S)")
		annihilator := arg.TermAs[Set[Fun[D, A]]]("«annihilator»")
		moduleS := arg.Have(
			"R^S is a module over R",
			"module_on(R, free_module_record(R, S))",
			By(free_module.FreeModuleOn.Read(R).At(S)))
		additive := module.AddGroupOn.Read(moduleS)
		linear := arg.Have(
			"pairing against each v of V is linear",
			Statement{
				Binders: "∀v:D → A.",
				Hypotheses: []string{
					"v ∈ V",
				},
				Conclusion: "module_homomorphism(R, free_module_record(R, S), regular_module(R), «pairing»(v))",
			},
			By(
				finiteS,
				inSpace,
				StandardPairingBilinear.Read(R).At(S),
				module_homomorphism.BilinearMapDef,
				set_basic.SubsetDef))
		zero := arg.Have(
			"the zero vector pairs to zero with every v, each pairing being linear",
			"fun_zero(R.zero) ∈ free_module_record(R, S).carrier ∧ "+
				"(∀v:D → A. v ∈ V ⇒ «pairing»(v, fun_zero(R.zero)) = R.zero)",
			Derive(func(b *Argument) {
				origin := b.Have(
					"the zero vector lies in R^S",
					"fun_zero(R.zero) ∈ free_module_record(R, S).carrier",
					By(group.OneIn.Read(additive)))
				pairs := b.Have(
					"and pairs to zero with every v",
					"∀v:D → A. v ∈ V ⇒ «pairing»(v, fun_zero(R.zero)) = R.zero",
					Derive(func(c *Argument) {
						v := c.FixAs[Fun[D, A]]("v")
						vIn := c.Assume()
						hom := c.Have(
							"pairing against v is linear",
							"module_homomorphism(R, free_module_record(R, S), regular_module(R), «pairing»(v))",
							By(vIn, linear.At(v)))
						c.Show(
							"a linear map sends zero to zero",
							By(module_homomorphism.HomZero.Read(hom)))
					}))
				b.Show(
					"the zero vector pairs to zero with V",
					By(origin, pairs))
			}))
		sums := arg.Have(
			"so does the sum of two vectors that do, each pairing being additive",
			Statement{
				Binders: "∀x y:D → A.",
				Hypotheses: []string{
					"x ∈ «annihilator»",
					"y ∈ «annihilator»",
				},
				Conclusion: "fun_add(R.add, x, y) ∈ free_module_record(R, S).carrier ∧ " +
					"(∀v:D → A. v ∈ V ⇒ «pairing»(v, fun_add(R.add, x, y)) = R.zero)",
			},
			Derive(func(b *Argument) {
				b.FixAs[Fun[D, A]]("x")
				b.FixAs[Fun[D, A]]("y")
				both := b.Conjuncts(
					b.Assume(),
					"x pairs to zero with V",
					"so does y")
				onX := b.Conjuncts(
					both[0],
					"x lies in R^S",
					"x pairs to zero with every v")
				onY := b.Conjuncts(
					both[1],
					"y lies in R^S",
					"y pairs to zero with every v")
				sum := b.Have(
					"x + y lies in R^S",
					"fun_add(R.add, x, y) ∈ free_module_record(R, S).carrier",
					By(onX[0], onY[0], group.MulIn.Read(additive)))
				pairs := b.Have(
					"and pairs to zero with every v",
					"∀v:D → A. v ∈ V ⇒ «pairing»(v, fun_add(R.add, x, y)) = R.zero",
					Derive(func(c *Argument) {
						v := c.FixAs[Fun[D, A]]("v")
						vIn := c.Assume()
						hom := c.Have(
							"pairing against v is linear",
							"module_homomorphism(R, free_module_record(R, S), regular_module(R), «pairing»(v))",
							By(vIn, linear.At(v)))
						c.Show(
							"the pairing of x + y against v is the sum of two zeros",
							By(
								vIn,
								onX[0],
								onY[0],
								onX[1].At(v),
								onY[1].At(v),
								module_homomorphism.HomAdd.Read(hom),
								group.RightIdentityOn.Read(abelian_group.GroupOn.Read(comm_ring.AddGroupOn.Read(R))),
								comm_ring.ZeroIn.Read(R)))
					}))
				b.Show(
					"x + y pairs to zero with V",
					By(sum, pairs))
			}))
		multiples := arg.Have(
			"and so does a scalar multiple of one, each pairing being homogeneous",
			Statement{
				Binders: "∀c:A. ∀x:D → A.",
				Hypotheses: []string{
					"c ∈ R.carrier",
					"x ∈ «annihilator»",
				},
				Conclusion: "fun_smul(R.mul, c, x) ∈ free_module_record(R, S).carrier ∧ " +
					"(∀v:D → A. v ∈ V ⇒ «pairing»(v, fun_smul(R.mul, c, x)) = R.zero)",
			},
			Derive(func(b *Argument) {
				b.FixAs[A]("c")
				b.FixAs[Fun[D, A]]("x")
				given := b.Conjuncts(
					b.Assume(),
					"c is a scalar",
					"x pairs to zero with V")
				onX := b.Conjuncts(
					given[1],
					"x lies in R^S",
					"x pairs to zero with every v")
				multiple := b.Have(
					"c • x lies in R^S",
					"fun_smul(R.mul, c, x) ∈ free_module_record(R, S).carrier",
					By(given[0], onX[0], module.SmulIn.Read(moduleS)))
				pairs := b.Have(
					"and pairs to zero with every v",
					"∀v:D → A. v ∈ V ⇒ «pairing»(v, fun_smul(R.mul, c, x)) = R.zero",
					Derive(func(d *Argument) {
						v := d.FixAs[Fun[D, A]]("v")
						vIn := d.Assume()
						hom := d.Have(
							"pairing against v is linear",
							"module_homomorphism(R, free_module_record(R, S), regular_module(R), «pairing»(v))",
							By(vIn, linear.At(v)))
						d.Show(
							"the pairing of c • x against v is c times zero",
							By(
								vIn,
								given[0],
								onX[0],
								onX[1].At(v),
								module_homomorphism.HomSmul.Read(hom),
								comm_ring.MulRightZeroOn.Read(R)))
					}))
				b.Show(
					"c • x pairs to zero with V",
					By(multiple, pairs))
			}))
		within := arg.Have(
			"the annihilator lies in R^S",
			"«annihilator» ⊆ free_module_record(R, S).carrier",
			BySets())
		arg.Show(
			"so it is a submodule of R^S",
			By(
				moduleS,
				within,
				zero,
				sums,
				multiples,
				submodule.SubmoduleCriterion.At(ring, space, annihilator)))
	}),
})}

// AnnihilatorDimension — in the coordinate space F^S over a finite set S,
// the span U of a set V of vectors and the vectors pairing to zero with every
// member of V have dimensions adding to |S|. U has a finite basis B, and a
// vector pairs to zero with V exactly when it pairs to zero with B, both
// spanning U (StandardPairingVanishesOnSpan). So the annihilator is the
// kernel of pairing against B, a linear map of F^S (PairingMapLinear) onto
// F^B (IndependentPairingsOnto), and rank–nullity counts |S| as the
// annihilator's dimension plus |B|, which is U's.
var AnnihilatorDimension = annihilatorDimensionThm{family.Add(registry.ProofEntry{
	Name: "AnnihilatorDimension",
	Key:  "prop_2948cd15040a5241",
	Build: family.Theorem(Statement{
		Binders: "∀F:field_on(A). ∀S:set(D). ∀V:set(D → A).",
		Hypotheses: []string{
			"finite(S)",
			"V ⊆ «space».carrier",
		},
		Conclusion: "module_dim(field_ring(F), restrict_module(«space», «span»)) + " +
			"module_dim(field_ring(F), restrict_module(«space», «annihilator»)) = " +
			"card(S)",
		Abbrev: Abbrev{
			{Name: "space", Text: "free_module_record(field_ring(F), S)"},
			{Name: "span", Text: "module_span(field_ring(F), «space», V)"},
			{Name: "annihilator", Text: "{a:D → A | " +
				"    a ∈ «space».carrier ∧ " +
				"    (∀v:D → A. v ∈ V ⇒ module_sum(F.add, F.zero, S, λi:D. v(i) * a(i)) = F.zero)}"},
			{Name: "pairings", Text: "λa:D → A. λu:D → A. " +
				"    COND(u ∈ B, module_sum(F.add, F.zero, S, λi:D. u(i) * a(i)), F.zero)"},
		},
	}, func(
		arg *Argument,
		F field.FieldFact[on.F],
		S *Expr[Set[D]],
		V *Expr[Set[Fun[D, A]]],
		finiteS, inSpace Fact,
	) {
		ring := field.RingOn.Read(F)
		R := arg.TermAs[RingOps[A]]("field_ring(F)")
		inv := arg.TermAs[Fun[A, A]]("F.inv")
		space := arg.TermAs[ModuleOps[A, Fun[D, A]]]("«space»")
		span := arg.TermAs[Set[Fun[D, A]]]("«span»")
		scalarsField := arg.Have(
			"F is a field on its own carrier",
			"ring_subfield(field_ring(F), F.inv, field_ring(F).carrier)",
			By(field.FieldRingSubfield.Read(F)))
		moduleS := arg.Have(
			"F^S is a module over F",
			"module_on(field_ring(F), «space»)",
			By(free_module.FreeModuleOn.Read(ring).At(S)))
		dimensionS := arg.Conjuncts(
			GroupPremises(scalarsField, finiteS, FreeModuleFiniteDim.At(R, inv, S)),
			"F^S is finite-dimensional",
			"of dimension |S|")
		subspace := arg.Have(
			"the span U of V is a subspace of F^S",
			"submodule(field_ring(F), «space», «span»)",
			By(moduleS, inSpace, submodule.SpanSubmodule))
		B, basis := arg.ObtainAs[Set[Fun[D, A]]](
			"U, a subspace of the finite-dimensional F^S, has a finite basis B",
			"∃B:set(D → A). finite(B) ∧ module_basis(field_ring(F), restrict_module(«space», «span»), B)",
			By(
				moduleS,
				scalarsField,
				dimensionS[0],
				subspace,
				SubmoduleDim.At(R, space, inv, span),
				FiniteDimensionalDef))
		basisParts := arg.Conjuncts(
			basis,
			"B is finite",
			"B is a basis of U")
		dimensionU := arg.Have(
			"U has dimension |B|",
			"module_dim(field_ring(F), restrict_module(«space», «span»)) = card(B)",
			By(
				basisParts[0],
				basisParts[1],
				moduleS,
				subspace,
				scalarsField,
				submodule.SubmoduleModuleOn.At(R, space, span),
				DimBasis.At(R, arg.TermAs[ModuleOps[A, Fun[D, A]]]("restrict_module(«space», «span»)"), inv, B)))
		inSpaceB := arg.Conjuncts(
			arg.Have(
				"B is independent in F^S and spans U there",
				"module_independent(field_ring(F), «space», B) ∧ module_span(field_ring(F), «space», B) = «span»",
				By(moduleS, subspace, basisParts[1], linear_independence.BasisRestrict)),
			"B is independent in F^S",
			"B spans U in F^S")
		independent, spansU := inSpaceB[0], inSpaceB[1]
		bInSpace := arg.Have(
			"B lies in F^S",
			"B ⊆ «space».carrier",
			By(independent, linear_independence.IndependentInCarrier))
		linear := arg.Have(
			"pairing against B is a linear map of F^S into F^B",
			"module_homomorphism(field_ring(F), «space», free_module_record(field_ring(F), B), «pairings»)",
			By(ring, finiteS, basisParts[0], bInSpace, PairingMapLinear.Read(ring).At(S, B)))
		onto := arg.Have(
			"and onto F^B, B being independent",
			"image(«pairings», finite_supp(F.zero, F.carrier, S)) = finite_supp(F.zero, F.carrier, B)",
			By(F, finiteS, independent, IndependentPairingsOnto.Read(F).At(S, B)))
		annihilates := arg.Have(
			"a vector of F^S pairs to zero with B exactly when it does with V, the two spanning U",
			Statement{
				Binders:    "∀a:D → A.",
				Hypotheses: []string{"a ∈ «space».carrier"},
				Conclusion: "(∀u:D → A. u ∈ B ⇒ module_sum(F.add, F.zero, S, λi:D. u(i) * a(i)) = F.zero) ⇔ " +
					"(∀v:D → A. v ∈ V ⇒ module_sum(F.add, F.zero, S, λi:D. v(i) * a(i)) = F.zero)",
			},
			Derive(func(b *Argument) {
				a := b.FixAs[Fun[D, A]]("a")
				aIn := b.Assume()
				b.Iff()
				b.Forward(
					"pairing to zero with B, a pairs to zero with the span U of B, which holds V",
					func(c *Argument, onB Fact) {
						v := c.FixAs[Fun[D, A]]("v")
						vIn := c.Assume()
						inU := c.Have(
							"v lies in U, the span of B",
							"v ∈ module_span(field_ring(F), «space», B)",
							BySets(vIn, spansU, submodule.SubsetSpan.At(R, space, V)))
						c.Show(
							"the pairing against a vanishes on the span of B",
							By(ring, finiteS, bInSpace, aIn, onB, inU, StandardPairingVanishesOnSpan.Read(ring).At(S, B, a, v)))
					})
				b.Backward(
					"pairing to zero with V, a pairs to zero with U, which holds B",
					func(c *Argument, onV Fact) {
						u := c.FixAs[Fun[D, A]]("u")
						uIn := c.Assume()
						inU := c.Have(
							"u lies in U, the span of V",
							"u ∈ «span»",
							BySets(uIn, spansU, submodule.SubsetSpan.At(R, space, B)))
						c.Show(
							"the pairing against a vanishes on the span of V",
							By(ring, finiteS, inSpace, aIn, onV, inU, StandardPairingVanishesOnSpan.Read(ring).At(S, V, a, u)))
					})
			}))
		zeroMap := arg.Have(
			"the pairings of a against B vanish exactly when a pairs to zero with every member of B",
			"∀a:D → A. "+
				"    «pairings»(a) = fun_zero(F.zero) ⇔ "+
				"    (∀u:D → A. u ∈ B ⇒ module_sum(F.add, F.zero, S, λi:D. u(i) * a(i)) = F.zero)",
			By(function_module.FunZeroDef))
		members := arg.Have(
			"so a vector lies in the kernel of the pairing map exactly when it annihilates V",
			"∀a:D → A. "+
				"    a ∈ group_kernel(fun_zero(F.zero), finite_supp(F.zero, F.carrier, S), «pairings») ⇔ "+
				"    a ∈ finite_supp(F.zero, F.carrier, S) ∧ "+
				"    (∀v:D → A. v ∈ V ⇒ module_sum(F.add, F.zero, S, λi:D. v(i) * a(i)) = F.zero)",
			arg.ForEach(func(a *Expr[Fun[D, A]]) Action {
				return By(zeroMap.At(a), annihilates.At(a), group_homomorphism.InKernel)
			}))
		kernel := arg.Have(
			"the kernel of the pairing map is the annihilator of V",
			"group_kernel(fun_zero(F.zero), finite_supp(F.zero, F.carrier, S), «pairings») = «annihilator»",
			BySets(members))
		coordinates := arg.TermAs[ModuleOps[A, Fun[Fun[D, A], A]]]("free_module_record(field_ring(F), B)")
		counted := arg.Have(
			"rank–nullity for the pairing map: its kernel is the annihilator and its image all of F^B",
			"module_dim(field_ring(F), restrict_module(«space», «annihilator»)) + "+
				"module_dim(field_ring(F), "+
				"    restrict_module(free_module_record(field_ring(F), B), finite_supp(F.zero, F.carrier, B))) = "+
				"module_dim(field_ring(F), «space»)",
			kernel.RwRev(),
			onto.RwRev(),
			By(
				moduleS,
				free_module.FreeModuleOn.Read(ring).At(B),
				scalarsField,
				dimensionS[0],
				linear,
				RankNullity.At(
					R, space, inv, coordinates, arg.TermAs[Fun2[Fun[D, A], Fun[D, A], A]]("«pairings»"))))
		arg.Show(
			"the annihilator has dimension |S| − |B|, and U has dimension |B|",
			ByArith(
				counted,
				dimensionS[1],
				dimensionU,
				basisParts[0],
				scalarsField,
				module_record.RestrictModuleCarrier.At(coordinates),
				FreeModuleDim.At(R, inv, B)))
	}),
})}

// PairingKernelVector gives a nonzero vector annihilated by fewer than
// |S| rows. Pairing with the rows maps the coordinate space on S to a
// strictly smaller coordinate space.
var PairingKernelVector = pairingKernelVectorThm{family.Add(registry.ProofEntry{
	Name: "PairingKernelVector",
	Key:  "prop_ed59016f1a7e74b7",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀inv:(A → A). ∀S:set(D). ∀X:set(D → A).",
		Hypotheses: []string{
			"comm_ring_on(R)", "ring_subfield(R, inv, R.carrier)", "finite(S)", "finite(X)",
			"X ⊆ free_module_record(R, S).carrier", "card(X) < card(S)",
		},
		Conclusion: "∃a:D → A. " +
			"    a ∈ free_module_record(R, S).carrier ∧ " +
			"    a ≠ free_module_record(R, S).zero ∧ " +
			"    «pairings»(a) = free_module_record(R, X).zero",
		Abbrev: Abbrev{
			{Name: "pairings", Text: "λa:D → A. λu:D → A. " +
				"    COND(u ∈ X, module_sum(R.add, R.zero, S, λi:D. R.mul(u(i), a(i))), R.zero)"},
		},
	}, func(
		a *Argument,
		R *Expr[RingOps[A]],
		inv *Arrow[A, A],
		S *Expr[Set[D]],
		X *Expr[Set[Fun[D, A]]],
		ring, fieldScalars, finiteS, finiteX, rows, fewer Fact,
	) {
		source := a.Have(
			"the source has dimension |S|",
			"finite_dimensional(R, free_module_record(R, S)) ∧ "+
				"module_dim(R, free_module_record(R, S)) = card(S)",
			By(finiteS, fieldScalars, FreeModuleFiniteDim.At(R, inv, S)))
		target := a.Have(
			"the target has dimension |X|",
			"finite_dimensional(R, free_module_record(R, X)) ∧ "+
				"module_dim(R, free_module_record(R, X)) = card(X)",
			By(finiteX, fieldScalars, FreeModuleFiniteDim.At(R, inv, X)))
		linear := a.Have(
			"pairing against the rows is a linear map",
			"module_homomorphism(R, free_module_record(R, S), free_module_record(R, X), «pairings»)",
			By(ring, finiteS, finiteX, rows, PairingMapLinear.At(R, S, X)))
		smaller := a.Have(
			"the target has smaller dimension",
			"module_dim(R, free_module_record(R, X)) < module_dim(R, free_module_record(R, S))",
			By(Normalized, fewer, source, target))
		a.Show(
			"rank-nullity supplies a nonzero vector in the kernel",
			By(
				smaller,
				source,
				target,
				fieldScalars,
				linear,
				LinearKernelVector.At(R, a.TermAs[ModuleOps[A, Fun[D, A]]]("free_module_record(R, S)"), inv,
					a.TermAs[ModuleOps[A, Fun[Fun[D, A], A]]]("free_module_record(R, X)"),
					a.TermAs[Fun2[Fun[D, A], Fun[D, A], A]]("«pairings»"))))
	}),
})}

// SmallRowsKernel solves a homogeneous system with fewer rows than
// unknowns. Rows may repeat, and the two finite index sets may have
// different element types.
var SmallRowsKernel = smallRowsKernelThm{family.Add(registry.ProofEntry{
	Name: "SmallRowsKernel", Key: "prop_c21bb4e67d14a0ce",
	Build: family.Sections(Statement{
		Binders:    "∀H:set(A). ∀K:set(B). ∀M:B → A → real.",
		Hypotheses: []string{"finite(H)", "finite(K)", "card(K) < card(H)"},
		Conclusion: "∃v:A → real. " +
			"    (∃i:A. i ∈ H ∧ v(i) ≠ &0) ∧ " +
			"    (∀i:A. i ∉ H ⇒ v(i) = &0) ∧ " +
			"    (∀j:B. j ∈ K ⇒ Σ_{i∈H} M(j, i) * v(i) = &0)",
		Abbrev: Abbrev{
			{Name: "row", Text: "λj:B. λi:A. COND(i ∈ H, M(j,i), &0)"},
			{Name: "rows", Text: "image(«row», K)"},
			{Name: "target", Text: "free_module_record(real_ring,«rows»)"},
			{Name: "pair", Text: "λv:A → real. λu:A → real. " +
				"    COND(u ∈ «rows», " +
				"        module_sum(real_ring.add,real_ring.zero,H, λi:A. real_ring.mul(u(i),v(i))),real_ring.zero)"},
			// «product» spells the kernel vector v the body obtains and the row index j it fixes per row.
			{Name: "product", Text: "λi:A. «row»(j,i) * v(i)"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		supported := ctx.Lemma(Statement{
			Binders:    "∀S:set(A). ∀v:A → real.",
			Hypotheses: []string{"finite(S)"},
			Conclusion: "v ∈ free_module_record(real_ring, S).carrier ⇔ ∀i:A. i ∉ S ⇒ v(i) = &0",
		},
			func(a *Argument, S *Expr[Set[A]], v *Arrow[A, Real], finite Fact) {
				a.Show(
					"a function supported on the finite set S is a coordinate vector",
					Unfold(free_module.FreeModuleRecordDef),
					Unfold(function_module.FiniteSuppDef),
					Unfold(function_module.FiniteSupportDef),
					BySets(finite, finite_set.FiniteSubset.At(a.TermAs[Set[A]]("fun_support(&0,v)"), S)))
			})
		zeroVector := ctx.Lemma("∀S:set(A). free_module_record(real_ring, S).zero = (λi:A. real_of_num(0))",
			func(a *Argument, S *Expr[Set[A]]) {
				a.Show(
					"the zero vector is zero at every coordinate",
					By(
						Normalized,
						free_module.FreeModuleRecordDef.At(a.TermAs[module_record.RingOps[Real]]("real_ring"), S),
						real_ring.RealRingDef,
						function_module.FunZeroDef))
			})
		scalars := ctx.Lemma("ring_subfield(real_ring, "+
			"    real_field_ops.inv, "+
			"    real_ring.carrier)", func(a *Argument) {
			F := a.TermAs[field.FieldOps[Real]]("real_field_ops")
			on := a.Have(
				"the real field laws hold on the whole real line",
				"field_on(restrict_field(real_field_ops,𝕌))",
				By(real_field.Field, field.FieldOnUniverse.At(F)))
			same := a.Have(
				"restricting the real field to its entire carrier gives the same field",
				"restrict_field(real_field_ops,𝕌) = real_field_ops",
				By(field.RestrictFieldDef.At(F, a.TermAs[Set[Real]]("𝕌")), real_field.RealFieldOpsDef))
			a.Show(
				"the scalars form a field on the real ring",
				By(Normalized, on, same, field.FieldRingSubfield.At(F), real_field.RealFieldRing))
		})
		return ctx.Theorem(headline, func(
			a *Argument,
			H *Expr[Set[A]],
			K *Expr[Set[B]],
			M *Arrow2[B, A, Real],
			finiteH, finiteK, fewer Fact,
		) {
			row := a.TermAs[Fun2[B, A, Real]]("«row»")
			rows := a.TermAs[Set[Fun[A, Real]]]("«rows»")
			R := a.TermAs[module_record.RingOps[Real]]("real_ring")
			finiteRows := a.Have(
				"there are finitely many distinct rows",
				"finite(«rows»)",
				By(finiteK, finite_set.FiniteImage.At(row, K)))
			fewerRows := a.Have(
				"identifying duplicate rows only decreases their number",
				"card(«rows») < card(H)",
				ByArith(finiteK, fewer, cardinality.CardImageLe.At(row, K)))
			eachRow := a.Have(
				"extending a row by zero puts it in the coordinate space on H",
				"∀j:B. j ∈ K ⇒ «row»(j) ∈ free_module_record(real_ring, H).carrier",
				By(finiteH, At(supported, H)))
			inSpace := a.Have(
				"the row image lies in that space",
				"«rows» ⊆ free_module_record(real_ring, H).carrier",
				By(
					eachRow,
					set_image.ImageSubsetIff.At(
						row, K, a.TermAs[Set[Fun[A, Real]]]("free_module_record(real_ring, H).carrier"))))
			v, kernel := a.ObtainAs[Fun[A, Real]](
				"a nonzero vector pairs to zero against all rows",
				"∃v:A → real. "+
					"    v ∈ free_module_record(real_ring, H).carrier ∧ "+
					"    v ≠ free_module_record(real_ring, H).zero ∧ "+
					"    «pair»(v) = «target».zero",
				By(
					finiteH,
					finiteRows,
					fewerRows,
					inSpace,
					scalars,
					real_ring.CommRingOn,
					PairingKernelVector.At(
						R, a.TermAs[Fun[Real, Real]]("real_field_ops.inv"), H, rows)))
			parts := a.Conjuncts(
				kernel,
				"vector in the domain",
				"nonzero vector",
				"all row pairings vanish")
			inDomain, nonzeroVector, pairingsVanish := parts[0], parts[1], parts[2]
			outside := a.Have(
				"the vector vanishes off H",
				"∀i:A. i ∉ H ⇒ v(i) = &0",
				By(finiteH, inDomain, At(supported, H, v)))
			nonzero := a.Have(
				"some coordinate in H is nonzero",
				"∃i:A. i ∈ H ∧ v(i) ≠ &0",
				By(nonzeroVector, outside, At(zeroVector, H)))
			zeroOnRows := ctx.AtTypeVars(zeroVector, TypeBinder.BindA[Fun[A, Real]]())
			annihilates := a.Have(
				"each original matrix row annihilates the vector",
				"∀j:B. j ∈ K ⇒ Σ_{i∈H} M(j,i)*v(i) = &0",
				Derive(func(b *Argument) {
					j := b.FixAs[B]("j")
					member := b.Assume()
					rowIn := b.Have(
						"the restricted row is among the pairings",
						"«row»(j) ∈ «rows»",
						By(member, set_image.FunInImage.At(row, K, j)))
					atRow := b.Have(
						"evaluate the pairing vector at this row",
						"«pair»(v,«row»(j)) = «target».zero(«row»(j))",
						By(pairingsVanish))
					sumZero := b.Have(
						"the coordinate pairing is zero",
						"module_sum(real_add,&0,H,«product») = &0",
						By(At(zeroOnRows, rows), atRow, rowIn, real_ring.RealRingDef))
					product := b.TermAs[Fun[A, Real]]("«product»")
					ordinary := b.Have(
						"over real scalars this is the usual sum",
						"sum(H,«product») = &0",
						By(finiteH, sumZero, real_sum.RealModuleSum.At(product, H)))
					agree := b.Have(
						"the restriction agrees with M on H",
						"∀i:A. i ∈ H ⇒ «product»(i) = M(j, i) * v(i)",
						ByArith())
					b.Show(
						"the same sum annihilates the original row",
						By(
							agree,
							ordinary,
							real_sum.Congruence.At(H, product, b.TermAs[Fun[A, Real]]("λi:A. M(j,i)*v(i)"))))
				}))
			a.Show(
				"the vector has every requested property",
				Witness(v),
				By(nonzero, outside, annihilates))
		})
	}),
})}

// MajorityKernelVector chooses v supported on H so that Mv is also
// supported on H within V. The rows indexed outside H give fewer
// equations than the number of coordinates available inside H.
var MajorityKernelVector = majorityKernelVectorThm{family.Add(registry.ProofEntry{
	Name: "MajorityKernelVector", Key: "prop_7455838e9c8613ea",
	Build: family.Theorem(Statement{
		Binders:    "∀V H:set(A). ∀M:A → A → real.",
		Hypotheses: []string{"finite(V)", "H ⊆ V", "card(V) < 2 * card(H)"},
		Conclusion: "∃v:A → real. " +
			"    (∃i:A. i ∈ H ∧ v(i) ≠ &0) ∧ " +
			"    (∀i:A. i ∉ H ⇒ v(i) = &0) ∧ " +
			"    (∀j:A. j ∈ V ∧ j ∉ H ⇒ Σ_{i∈V} M(j, i) * v(i) = &0)",
		Abbrev: Abbrev{{Name: "outside", Text: "V ∖ H"}},
	}, func(a *Argument, V, H *Expr[Set[A]], M *Arrow2[A, A, Real], finite, subset, majority Fact) {
		K := a.TermAs[Set[A]]("«outside»")
		finiteH := a.Have(
			"H is finite",
			"finite(H)",
			By(finite, subset, finite_set.FiniteSubset.At(H, V)))
		finiteK := a.Have(
			"the omitted vertices form a finite set",
			"finite(«outside»)",
			By(finite, finite_set.FiniteDiff.At(V, H)))
		smaller := a.Have(
			"there are fewer omitted vertices than retained ones",
			"card(«outside») < card(H)",
			ByArith(finite, subset, majority, cardinality.CardDiff.At(V, H), cardinality.CardSubset.At(H, V)))
		v, kernel := a.ObtainAs[Fun[A, Real]](
			"solve the homogeneous equations for the omitted rows",
			"∃v:A → real. "+
				"    (∃i:A. i ∈ H ∧ v(i) ≠ &0) ∧ "+
				"    (∀i:A. i ∉ H ⇒ v(i) = &0) ∧ "+
				"    (∀j:A. j ∈ «outside» ⇒ Σ_{i∈H} M(j,i)*v(i) = &0)",
			By(finiteH, finiteK, smaller, SmallRowsKernel.At(H, K, M)))
		parts := a.Conjuncts(
			kernel,
			"nonzero on H",
			"zero off H",
			"each omitted row kills v")
		nonzero, zeroOff, omittedRowsKill := parts[0], parts[1], parts[2]
		allRows := a.Have(
			"sum over all vertices for each omitted row",
			"∀j:A. j ∈ V ∧ j ∉ H ⇒ Σ_{i∈V} M(j, i) * v(i) = &0",
			Derive(func(b *Argument) {
				j := b.FixAs[A]("j")
				out := b.Assume()
				inK := b.Have(
					"j indexes an omitted row",
					"j ∈ «outside»",
					By(out, set_basic.InDiff.At(V, H, j)))
				vanishes := b.Have(
					"the added terms vanish off H",
					"∀i:A. i ∈ V ∧ i ∉ H ⇒ M(j, i) * v(i) = &0",
					ByArith(zeroOff))
				b.Show(
					"extending the sum preserves its zero value",
					By(
						inK,
						omittedRowsKill,
						subset,
						vanishes,
						real_sum.Superset.At(H, V, b.TermAs[Fun[A, Real]]("λi:A. M(j,i)*v(i)"))))
			}))
		a.Show(
			"the same nonzero vector has the required support before and after applying M",
			Witness(v),
			By(nonzero, zeroOff, allRows))
	}),
})}
