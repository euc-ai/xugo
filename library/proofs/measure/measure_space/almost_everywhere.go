package measure_space

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/real/extended_nonneg_real"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/proofs/sets/sigma_algebra"
	"github.com/euc-ai/xugo/library/registry"
)

var NullCountableUnion = nullCountableUnionThm{family.Add(registry.ProofEntry{
	Name: "NullCountableUnion",
	Key:  "prop_7fe05d788397fdd2",
	Build: family.Theorem(MeasureOn.Statement(Statement{
		Binders:    "∀E:(num → set(A)).",
		Hypotheses: []string{"∀n:num. measure_null(Ω, S, μ, E(n))"},
		Conclusion: "measure_null(Ω, S, μ, ⋃image(E, 𝕌))",
	}), func(a *Argument, Ω *Expr[Set[A]], S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal], measure Fact,
		E *Arrow[Nat, Set[A]], nulls Fact) {
		laws := a.Conjuncts(
			a.Unfolded(measure, MeasureOn),
			"the measurable sets form a sigma algebra",
			"the empty set has measure zero",
			"countable disjoint unions have the series of their measures")
		closure := a.Unfolded(laws[0], sigma_algebra.SigmaAlgebraOnDef)
		covered := a.Unfolded(nulls, NullSetDef)
		N, covers := a.ObtainAs[Fun[Nat, Set[A]]](
			"choose for each n a measurable set N(n) of measure zero holding E(n)",
			"∃N:(num → set(A)). ∀n:num. N(n) ∈ S ∧ μ(N(n)) = &0 ∧ E(n) ⊆ N(n)",
			By(covered))
		measurable := a.Have(
			"the union of the N(n) is measurable",
			"⋃image(N, 𝕌) ∈ S",
			By(closure, covers))
		zero := a.Have(
			"and its measure is at most the series of their zero measures",
			"μ(⋃image(N, 𝕌)) = &0",
			By(
				measure,
				covers,
				MeasureCountableSubadditive.At(Ω, S, μ, N),
				extended_nonneg_real.SeriesZero,
				extended_nonneg_real.ZeroLe,
				extended_nonneg_real.LeAntisym))
		inside := a.Have(
			"each E(n) lies in Ω",
			"∀n:num. E(n) ⊆ Ω",
			By(covered))
		within := a.Have(
			"the union of the E(n) lies in Ω and in the union of the N(n)",
			"⋃image(E, 𝕌) ⊆ Ω ∧ ⋃image(E, 𝕌) ⊆ ⋃image(N, 𝕌)",
			BySets(inside, covers))
		a.Show(
			"so it is null",
			By(zero, measurable, within, NullSetDef))
	}),
})}

// AECountable — countably many assertions, each holding almost everywhere,
// hold together almost everywhere. A point of Ω where one of them fails lies
// in the exceptional set of that one, so the exceptional set of their
// conjunction is the union of theirs, a countable union of null sets.
var AECountable = aECountableThm{family.Add(registry.ProofEntry{
	Name: "AECountable",
	Key:  "prop_9403e5c75a036639",
	Build: family.Theorem(MeasureOn.Statement(Statement{
		Binders:    "∀P:(num → A → bool).",
		Hypotheses: []string{"∀n:num. measure_ae(Ω, S, μ, P(n))"},
		Conclusion: "measure_ae(Ω, S, μ, λx:A. ∀n:num. P(n, x))",
		Abbrev: Abbrev{
			{Name: "exceptional", Text: "λn:num. {x:A | x ∈ Ω ∧ ¬P(n, x)}"},
		},
	}), func(a *Argument, Ω *Expr[Set[A]], S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal], measure Fact,
		P *Arrow2[Nat, A, Bool], ae Fact) {
		exceptional := a.Have(
			"the exceptional set of each P(n) is null",
			"∀n:num. measure_null(Ω, S, μ, «exceptional»(n))",
			By(ae, AlmostEverywhereDef))
		union := a.Have(
			"a point of Ω fails some P(n) exactly when it lies in the exceptional set of that P(n)",
			"{x:A | x ∈ Ω ∧ ¬(∀n:num. P(n, x))} = ⋃image(«exceptional», 𝕌)",
			BySets())
		a.Show(
			"so the exceptional set of their conjunction is a countable union of null sets",
			Simp(Fwd(AlmostEverywhereDef), Fwd(union)),
			By(
				measure,
				exceptional,
				NullCountableUnion.At(Ω, S, μ, a.TermAs[Fun[Nat, Set[A]]]("«exceptional»"))))
	}),
})}

// AEConjunction — two assertions holding almost everywhere hold together
// almost everywhere. Read them as a sequence of assertions, P at 0 and Q
// after: countably many assertions holding almost everywhere hold together
// almost everywhere, and wherever the sequence holds, so do P and Q.
var AEConjunction = aEConjunctionThm{family.Add(registry.ProofEntry{
	Name: "AEConjunction",
	Key:  "prop_15b27a81ea0274e2",
	Build: family.Theorem(MeasureOn.Statement(Statement{
		Binders:    "∀P Q:(A → bool).",
		Hypotheses: []string{"measure_ae(Ω, S, μ, P)", "measure_ae(Ω, S, μ, Q)"},
		Conclusion: "measure_ae(Ω, S, μ, λx:A. P(x) ∧ Q(x))",
		Abbrev: Abbrev{
			{Name: "pair", Text: "λn:num. λx:A. COND(n = 0, P(x), Q(x))"},
		},
	}), func(a *Argument, Ω *Expr[Set[A]], S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal], measure Fact,
		P, Q *Arrow[A, Bool], first, second Fact) {
		each := a.Have(
			"read as a sequence of assertions, P and then Q, each holds almost everywhere",
			"∀n:num. measure_ae(Ω, S, μ, «pair»(n))",
			By(first, second))
		together := a.Have(
			"so they hold together almost everywhere",
			"measure_ae(Ω, S, μ, λx:A. ∀n:num. «pair»(n, x))",
			By(measure, each, AECountable.At(Ω, S, μ, a.TermAs[Fun[Nat, Set[A]]]("«pair»"))))
		both := a.Have(
			"wherever the sequence holds, so do P and Q",
			"∀x:A. x ∈ Ω ∧ (∀n:num. «pair»(n, x)) ⇒ P(x) ∧ Q(x)",
			By(Normalized, nat_arith.OneNotZero))
		a.Show(
			"so P and Q hold together almost everywhere",
			By(
				together,
				both,
				AEMono.At(
					Ω,
					S,
					μ,
					a.TermAs[Set[A]]("λx:A. ∀n:num. «pair»(n, x)"),
					a.TermAs[Set[A]]("λx:A. P(x) ∧ Q(x)"))))
	}),
})}

// AEMono — an assertion implied on Ω by one holding almost everywhere holds
// almost everywhere itself: where Q fails on Ω so does P, so the exceptional
// set of Q lies in the measurable set of measure zero holding that of P. No
// measure law is read, only the definition of a null set.
var AEMono = aEMonoThm{family.Add(registry.ProofEntry{
	Name: "AEMono",
	Key:  "prop_54fe6ca868bf1d7a",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). ∀P Q:(A → bool).",
		Hypotheses: []string{
			"measure_ae(Ω, S, μ, P)",
			"∀x:A. x ∈ Ω ∧ P(x) ⇒ Q(x)",
		},
		Conclusion: "measure_ae(Ω, S, μ, Q)",
	}, func(a *Argument, Ω *Expr[Set[A]], S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal], P, Q *Arrow[A, Bool], ae, implies Fact) {
		exceptional := a.Conjuncts(
			a.Unfolded(a.Unfolded(ae, AlmostEverywhereDef), NullSetDef),
			"the exceptional set of P lies in Ω",
			"and in a measurable set of measure zero")
		_, null := a.UnpackAs[Set[A]](exceptional[1], "N")
		within := a.Have(
			"where Q fails on Ω so does P, so the exceptional set of Q lies in Ω and in N",
			"{x:A | x ∈ Ω ∧ ¬Q(x)} ⊆ Ω ∧ {x:A | x ∈ Ω ∧ ¬Q(x)} ⊆ N",
			BySets(implies, null))
		a.Show(
			"so the exceptional set of Q is null",
			By(null, within, AlmostEverywhereDef, NullSetDef))
	}),
})}

// AEEqualEquivalence — equality almost everywhere is an equivalence
// relation. Nothing is exceptional for f against itself, and the empty set
// is null; f(x) = g(x) and g(x) = f(x) fail at the same points; and the two
// equations f(x) = g(x) and g(x) = h(x) hold together almost everywhere, and
// wherever both hold, f(x) = h(x).
var AEEqualEquivalence = aEEqualEquivalenceThm{family.Add(registry.ProofEntry{
	Name: "AEEqualEquivalence",
	Key:  "prop_40aff0601d83a249",
	Build: family.Theorem(MeasureOn.Statement(Statement{
		Conclusion: "(∀f:(A → B). measure_ae_eq(Ω, S, μ, f, f)) ∧ " +
			"(∀f g:(A → B). measure_ae_eq(Ω, S, μ, f, g) ⇒ measure_ae_eq(Ω, S, μ, g, f)) ∧ " +
			"(∀f g h:(A → B). " +
			"    measure_ae_eq(Ω, S, μ, f, g) ∧ measure_ae_eq(Ω, S, μ, g, h) ⇒ measure_ae_eq(Ω, S, μ, f, h))",
	}), func(a *Argument, Ω *Expr[Set[A]], S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal], measure Fact) {
		laws := a.Conjuncts(
			a.Unfolded(measure, MeasureOn),
			"the measurable sets form a sigma algebra",
			"the empty set has measure zero",
			"countable disjoint unions have the series of their measures")
		sigma, emptyMass := laws[0], laws[1]
		nullEmpty := a.Have(
			"the empty set is null, a measurable set of measure zero",
			"measure_null(Ω, S, μ, ∅)",
			By(
				sigma,
				emptyMass,
				sigma_algebra.SigmaFiniteOperations.At(Ω, S),
				set_order.EmptySubset,
				NullSetDef))
		a.Show(
			"equality almost everywhere is reflexive, symmetric and transitive",
			SplitConjAll(
				Case(
					"no point is exceptional for f against itself",
					Simp(Fwd(AEEqualDef), Fwd(AlmostEverywhereDef)),
					BySets(nullEmpty)),
				Case(
					"f(x) = g(x) and g(x) = f(x) fail at the same points",
					By(AEEqualDef)),
				Case(
					"where f agrees with g and g with h, f agrees with h",
					Derive(func(b *Argument) {
						b.FixAs[Fun[A, B]]("f")
						b.FixAs[Fun[A, B]]("g")
						b.FixAs[Fun[A, B]]("h")
						given := b.Conjuncts(
							b.Assume(),
							"f = g almost everywhere",
							"g = h almost everywhere")
						both := b.Have(
							"the two equations hold together almost everywhere",
							"measure_ae(Ω, S, μ, λx:A. f(x) = g(x) ∧ g(x) = h(x))",
							By(
								measure,
								b.Unfolded(given[0], AEEqualDef),
								b.Unfolded(given[1], AEEqualDef),
								AEConjunction.At(
									Ω,
									S,
									μ,
									b.TermAs[Set[A]]("λx:A. f(x) = g(x)"),
									b.TermAs[Set[A]]("λx:A. g(x) = h(x)"))))
						chained := b.Have(
							"and wherever both hold, f(x) = h(x)",
							"∀x:A. x ∈ Ω ∧ f(x) = g(x) ∧ g(x) = h(x) ⇒ f(x) = h(x)",
							Derive(func(c *Argument) {
								c.FixAs[A]("x")
								equations := c.Conjuncts(
									c.Assume(),
									"x lies in Ω",
									"f(x) = g(x)",
									"g(x) = h(x)")
								c.Show(
									"chain the two equations",
									By(Normalized, equations[1], equations[2]))
							}))
						b.Show(
							"so f = h almost everywhere",
							Simp(Fwd(AEEqualDef)),
							By(
								both,
								chained,
								AEMono.At(
									Ω,
									S,
									μ,
									b.TermAs[Set[A]]("λx:A. f(x) = g(x) ∧ g(x) = h(x)"),
									b.TermAs[Set[A]]("λx:A. f(x) = h(x)"))))
					}))))
	}),
})}

// AEOfEverywhere — what holds at every point of the carrier holds almost
// everywhere. Almost-everywhere equality is reflexive, so x = x holds almost
// everywhere, and AEMono carries that to any predicate true on Ω.
var AEOfEverywhere = aEOfEverywhereThm{family.Add(registry.ProofEntry{
	Name: "AEOfEverywhere",
	Key:  "prop_543073d338a36512",
	Build: family.Theorem(MeasureOn.Statement(Statement{
		Binders:    "∀P:(A → bool).",
		Hypotheses: []string{"∀x:A. x ∈ Ω ⇒ P(x)"},
		Conclusion: "measure_ae(Ω, S, μ, P)",
	}), func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal],
		P *Arrow[A, Bool],
		premises Fact,
	) {
		reflexive := a.Have(
			"reflexive equality holds almost everywhere",
			"measure_ae(Ω, S, μ, λx:A. x = x)",
			By(
				premises,
				AEEqualEquivalence.At[A, A](Ω, S, μ),
				AEEqualDef.At(Ω, S, μ,
					a.TermAs[Fun[A, A]]("λx:A. x"), a.TermAs[Fun[A, A]]("λx:A. x"))))
		a.Show(
			"pointwise truth on the carrier implies almost-everywhere truth",
			By(premises, reflexive, Where(AEMono, "P", a.TermAs[Fun[A, Bool]]("λx:A. x = x"))))
	}),
})}

// AEOffNullSet — almost every point lies off a measurable set of measure
// zero. The points of Ω where x ∉ N fails are the points of Ω in N, a subset
// of Ω and of N, so the exceptional set is null. No measure law is read, only
// the definition of a null set.
var AEOffNullSet = aEOffNullSetThm{family.Add(registry.ProofEntry{
	Name: "AEOffNullSet",
	Key:  "prop_c980537235795f7f",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). ∀N:set(A).",
		Hypotheses: []string{
			"N ∈ S",
			"μ(N) = &0",
		},
		Conclusion: "measure_ae(Ω, S, μ, λx:A. x ∉ N)",
	}, func(a *Argument, Ω *Expr[Set[A]], S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal], N *Expr[Set[A]], null Fact) {
		within := a.Have(
			"the points of Ω in N lie in Ω and in N",
			"{x:A | x ∈ Ω ∧ x ∈ N} ⊆ Ω ∧ {x:A | x ∈ Ω ∧ x ∈ N} ⊆ N",
			BySets())
		a.Show(
			"so the points of Ω where x ∉ N fails form a null set",
			By(null, within, AlmostEverywhereDef, NullSetDef))
	}),
})}

// AEOperation — an operation applied to functions equal almost everywhere
// gives functions equal almost everywhere. The two equations f(x) = g(x) and
// h(x) = k(x) hold together almost everywhere, and wherever both hold, the
// two combinations agree.
var AEOperation = aEOperationThm{family.Add(registry.ProofEntry{
	Name: "AEOperation",
	Key:  "prop_5edd394a28fad82f",
	Build: family.Theorem(MeasureOn.Statement(Statement{
		Binders: "∀f g:(A → B). ∀h k:(A → C). ∀op:(B → C → D).",
		Hypotheses: []string{
			"measure_ae_eq(Ω, S, μ, f, g)",
			"measure_ae_eq(Ω, S, μ, h, k)",
		},
		Conclusion: "measure_ae_eq(Ω, S, μ, λx:A. op(f(x), h(x)), λx:A. op(g(x), k(x)))",
	}), func(a *Argument, Ω *Expr[Set[A]], S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal], measure Fact,
		f, g *Arrow[A, B], h, k *Arrow[A, C], op *Arrow2[B, C, D], first, second Fact) {
		both := a.Have(
			"the two equations hold together almost everywhere",
			"measure_ae(Ω, S, μ, λx:A. f(x) = g(x) ∧ h(x) = k(x))",
			By(
				measure,
				a.Unfolded(first, AEEqualDef),
				a.Unfolded(second, AEEqualDef),
				AEConjunction.At(
					Ω,
					S,
					μ,
					a.TermAs[Set[A]]("λx:A. f(x) = g(x)"),
					a.TermAs[Set[A]]("λx:A. h(x) = k(x)"))))
		agree := a.Have(
			"wherever both hold, the two combinations agree",
			"∀x:A. x ∈ Ω ∧ f(x) = g(x) ∧ h(x) = k(x) ⇒ op(f(x), h(x)) = op(g(x), k(x))",
			Derive(func(b *Argument) {
				b.FixAs[A]("x")
				equations := b.Conjuncts(
					b.Assume(),
					"x lies in Ω",
					"f(x) = g(x)",
					"h(x) = k(x)")
				b.Show(
					"replace the arguments of op",
					By(equations[1], equations[2]))
			}))
		a.Show(
			"so they agree almost everywhere",
			Simp(Fwd(AEEqualDef)),
			By(
				both,
				agree,
				AEMono.At(
					Ω,
					S,
					μ,
					a.TermAs[Set[A]]("λx:A. f(x) = g(x) ∧ h(x) = k(x)"),
					a.TermAs[Set[A]]("λx:A. op(f(x), h(x)) = op(g(x), k(x))"))))
	}),
})}
