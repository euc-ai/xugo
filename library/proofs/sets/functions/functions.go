// functions.go — the chapter: maps, and what their properties amount to.
//
// Eight parts, marked by banners:
//
// - The identity and composition
// - Injectivity, and what a left inverse is worth
// - Surjectivity, the two things it amounts to, and the map that cannot
// exist
// - Choosing a value at every point of a set
// - Being injective and surjective at once, and the one map that says
// so
// - Injectivity as a predicate: the identity, restriction, and composites
// - Factoring a map through another map
// - The sets a map names: its preimages and its support

package functions

import (
	"github.com/euc-ai/xugo/ext"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/sets/internal/setvocab"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The identity and composition
// ---------------------------------------------------------------------------
//
// Before the chapter can say anything about a map it needs two names
// for maps built from other maps: `identity_map`, which returns its argument, and
// `f ∘ g`, which runs `g` and then `f`. Both are defined here outright
// — `identity_map = λx. x` and `f ∘ g = λx. f(g(x))`, the second spelled
// `compose` in its equation since the DSL reads `∘` as notation — so
// nothing here has content beyond those two equations, and every proof
// in the file is one of them being read.
//
// The two composition laws are stated POINT-FREE, as equations between
// maps; the two application laws are pointwise, because what happens at
// a point is their whole content. The point-free form is available
// because normalization η-expands, so `f ∘ identity_map = f` and its pointwise
// reading are one theorem rather than two.

// IdentityApply — `identity_map` returns its argument: the definition of `identity_map`
// (`identity_map = λx. x`), whose closure IS this pointwise reading
// since normalization η-expands. The reason `identity_map` can stand wherever a
// map is expected without changing what is said.
var IdentityApply = identityApplyThm{family.Define(registry.DefEntry{
	Name:      "IdentityApply",
	Key:       "prop_71448e4aaa9a7a02",
	Const:     "identity_map",
	Type:      "A → A",
	Equations: []string{"identity_map = λx:A. x"},
})}

// ComposeApply — what a composite does to a point: the definition of
// `∘` (`f ∘ g = λx. f(g(x))`, spelled `compose`), read pointwise the
// same way. Everything else in the file follows from reading this
// equation in one direction or the other.
var ComposeApply = composeApplyThm{family.Define(registry.DefEntry{
	Name:      "ComposeApply",
	Key:       "prop_75bb407026b9e6bc",
	Const:     "o",
	Spelled:   "compose",
	Type:      "(B → C) → (A → B) → A → C",
	Equations: []string{"∀f:(B → C). ∀g:(A → B). compose(f, g) = λx:A. f(g(x))"},
})}

// ComposeAssoc — composition associates. A point's route through three
// maps is the same however the composites are grouped, so the chapter
// never has to write the brackets.
var ComposeAssoc = composeAssocThm{family.Add(registry.ProofEntry{
	Name: "ComposeAssoc",
	Key:  "prop_79db81d91bf5b83f",
	Build: family.Theorem(
		"∀f:(C → D). ∀g:(B → C). ∀h:(A → B). f ∘ (g ∘ h) = (f ∘ g) ∘ h",
		func(a *Argument) {
			// Unfolding every `∘` turns both sides into the same λ,
			// `λx. f(g(h(x)))` — the associativity is λ-application's,
			// and `o` inherits it.
			a.Do(Unfold(ComposeApply))
		}),
})}

// ComposeIdentity — `identity_map` is a unit for composition on both sides.
//
// The two conjuncts state `identity_map` at DIFFERENT type instances: composing on
// the left it is the identity of the target type, on the right that of
// the source. A Script binds a name at one instance, so the left
// occurrence carries the DSL's type-substitution annotation `identity_map⟨A:B⟩` —
// "instantiate `identity_map`'s declared type variable `A` to `B`" — without which
// the two occurrences are forced to agree and the law silently narrows
// to endomaps.
var ComposeIdentity = composeIdentityThm{family.Add(registry.ProofEntry{
	Name: "ComposeIdentity",
	Key:  "prop_ec3b03a62e7a7f3d",
	Build: family.Theorem(
		"∀f:(A → B). identity_map⟨A:B⟩ ∘ f = f ∧ f ∘ identity_map = f",
		func(a *Argument) {
			// Two unfoldings, in the order the reading goes: `∘` first,
			// which turns each conjunct into a λ that applies `identity_map` at one
			// end or the other, then `identity_map`, after which both λs are `λx.
			// f(x)` and η-collapse to `f`.
			a.Do(Unfold(ComposeApply), Unfold(IdentityApply))
		}),
})}

// ---------------------------------------------------------------------------
// Injectivity, and what a left inverse is worth
// ---------------------------------------------------------------------------
//
// A map `f : A → B` is injective on a set `s` when it separates the
// points of `s`: `injective_on(s, f)`, defined here, and injective
// outright when it does so on `𝕌`. Two things are said about it, each
// said twice: that the implication it abbreviates may be read as a
// biconditional, and that injectivity IS a left inverse.
//
// The second pair is presented relativized first. That is not the
// chapter's usual order — it is forced, because the unrestricted member
// is proved by citing the relativized one.
//
// The predicate is a name and not an abbreviation the closers see
// through: a fact `injective_on(s, f)` is one atom in a proof's
// context, where the formula is a wide ∀ whose conclusion `x = y`
// matches every equation a proof is after. A proof that needs the
// points opens it — `Unfold(InjectiveOnDef)` on the whole leaf,
// `a.Unfolded(h, InjectiveOnDef)` on one fact.

// InjectiveOnDef — `injective_on(s, f)`: `f` identifies no two points
// of `s`. Where `f` sends points outside `s` the predicate says
// nothing, so a map that is injective on `s` may fold the rest of its
// source freely.
var InjectiveOnDef = injectiveOnDefThm{family.Define(registry.DefEntry{
	Name:  "InjectiveOnDef",
	Key:   "prop_855f10237d87f751",
	Const: "injective_on",
	Type:  "set(A) → (A → B) → bool",
	Equations: []string{
		"∀s:set(A). ∀f:(A → B). injective_on(s, f) ⇔ ∀x y:A. x ∈ s ∧ y ∈ s ∧ f(x) = f(y) ⇒ x = y",
	},
})}

// InjectiveAlt — injectivity may be read with `⇔`. The converse
// implication is congruence, true of every map, so the stronger-looking
// form is the same statement — and it is the one a rewrite can use,
// which is why it is worth stating.
var InjectiveAlt = injectiveAltThm{family.Add(registry.ProofEntry{
	Name: "InjectiveAlt",
	Key:  "prop_77961b16957b25b7",
	Build: family.Theorem(
		"∀f:(A → B). injective_on(𝕌, f) ⇔ ∀x y:A. f(x) = f(y) ⇔ x = y",
		Chain(Unfold(InjectiveOnDef), BySets())),
})}

// InjectiveOnAlt — the same upgrade, restricted to the points of `s`.
// The restriction is asked of one point at a time, so the guards stay
// outside the biconditional they license.
var InjectiveOnAlt = injectiveOnAltThm{family.Add(registry.ProofEntry{
	Name: "InjectiveOnAlt",
	Key:  "prop_e03cdcc0ab028a75",
	Build: family.Theorem(
		"∀s:set(A). ∀f:(A → B). injective_on(s, f) ⇔ ∀x y:A. x ∈ s ∧ y ∈ s ⇒ (f(x) = f(y) ⇔ x = y)",
		Chain(Unfold(InjectiveOnDef), BySets())),
})}

// InjectiveOnLeftInverse — `f` separates the points of `s` exactly when
// some `g` undoes it there. `g` is unconstrained off `f`'s image, so a
// total map can stand in for an inverse that exists only where a source
// does.
//
// The proof passes through a third form, stated below as `fibres`.
var InjectiveOnLeftInverse = injectiveOnLeftInverseThm{family.Add(registry.ProofEntry{
	Name: "InjectiveOnLeftInverse",
	Key:  "prop_6d41fb11600dd73c",
	Build: family.Sections(
		"∀f:(A → B). ∀s:set(A). injective_on(s, f) ⇔ ∃g:(B → A). ∀x:A. x ∈ s ⇒ g(f(x)) = x",
		func(ctx *Script, headline string) *GoalStackNode {
			// Injectivity on `s`, read one fibre at a time. That `f`
			// separates the points of `s` is the claim, made of each `y : B`
			// separately, that the points of `s` lying above `y` are all one
			// point — which is what a `c` they must each equal asserts.
			// Where no point of `s` lies above `y` the claim is vacuous and
			// `c` is arbitrary; that is why the nominee is bound by `∃` here
			// rather than produced by a partial function.
			fibres := ctx.Lemma(
				"∀f:(A → B). ∀s:set(A). injective_on(s, f) ⇔ ∀y:B. ∃c:A. ∀x:A. x ∈ s ∧ y = f(x) ⇒ c = x",
				Chain(Unfold(InjectiveOnDef), BySets()))

			// Where CHOICE enters, and the only place it does. The left side
			// nominates a `c` for each `y` independently; the right side
			// names ONE map making every nomination at once. Trading the
			// first for the second is Skolemization, which over an arbitrary
			// type IS the axiom of choice — and it is the entire distance
			// between "each fibre holds at most one point of `s`" and "there
			// is a left inverse".
			choice := ctx.Lemma(
				"∀f:(A → B). ∀s:set(A). "+
					"    (∀y:B. ∃c:A. ∀x:A. x ∈ s ∧ y = f(x) ⇒ c = x) ⇔ ∃g:(B → A). ∀x:A. x ∈ s ⇒ g(f(x)) = x",
				BySets())

			return ctx.Theorem(headline, func(a *Argument) {
				a.Show(
					"injectivity on s and a left inverse on s are each "+
						"equivalent to the fibre form, hence to each other",
					By(fibres, choice))
			})
		}),
})}

// InjectiveLeftInverse — injectivity outright is a left inverse
// outright: the relativized law read at the set every point belongs to.
// On `𝕌` the restriction constrains nothing, so the two statements
// differ only by membership guards.
var InjectiveLeftInverse = injectiveLeftInverseThm{family.Add(registry.ProofEntry{
	Name: "InjectiveLeftInverse",
	Key:  "prop_c26a2bca2a4495a7",
	Build: family.Theorem(
		"∀f:(A → B). injective_on(𝕌, f) ⇔ ∃g:(B → A). ∀x:A. g(f(x)) = x",
		func(a *Argument, f *Arrow[A, B]) {
			// `𝕌` is a witness of this proof and not a word of its
			// statement, so it is not in the chapter's vocabulary; it is
			// pinned here from the sets domain's shared table, which is
			// where every set name the domain uses is declared.
			univ := ext.As[Set[A]](setvocab.Pinned(a.Ctx(), "universe"))

			a.Show(
				"the relativized law at s := 𝕌, whose membership guards set_basic.InUniv discharges",
				By(InjectiveOnLeftInverse.At(f, univ), set_basic.InUniv))
		}),
})}

// ---------------------------------------------------------------------------
// Surjectivity, the two things it amounts to, and the map that cannot exist
// ---------------------------------------------------------------------------
//
// A map `f : A → B` is surjective when every point of `B` is `f` of
// something. This file states that four times; the four are one notion
// approached from two sides. A fifth member then says which map is NOT
// surjective.
//
// The first side is a RIGHT INVERSE. Surjectivity puts an `x` under
// every `y`, and a right inverse `g` picks one, so that `f(g(y)) = y`
// everywhere. Trading the one for the other trades `∀y. ∃x` for
// `∃g. ∀y` — it is Skolemization, which is why a refuter closes it
// outright rather than having to build the `g`. It is stated twice:
// unrestricted, and relativized to a source set `s` and a target set
// `t`.
//
// The second side is TRANSFER. If every point of `B` is some `f(x)`,
// then asking a question of every point of `B` and asking it of every
// point of `A` through `f` are the same question — for `∀` and for `∃`
// alike. Each transfer principle is stated as a biconditional because
// each one CHARACTERIZES surjectivity: its right-hand side quantifies
// over every predicate on `B`, which is strong enough to give the
// property back.
//
// The part closes with the one map the chapter says does not exist: a
// map from `s` to the subsets of `s` never reaches them all. That is
// Cantor's theorem, and the README carries the diagonal argument.
//
// All five close with the chapter's set-side closer. Only the
// relativized member and the diagonal set give its unfolding pass
// anything to do; for the other three it finds nothing and the closer
// is a refute, which is all they need.

// SurjectiveRightInverse — every point of the target has a preimage
// exactly when some map picks one for it. Such a `g` is a section of
// `f`: nothing here makes it unique, and where preimages are not unique
// it is not.
var SurjectiveRightInverse = surjectiveRightInverseThm{family.Add(registry.ProofEntry{
	Name: "SurjectiveRightInverse",
	Key:  "prop_b7782a3ac3c2f050",
	Build: family.Theorem(
		"∀f:(A → B). (∀y:B. ∃x:A. f(x) = y) ⇔ ∃g:(B → A). ∀y:B. f(g(y)) = y",
		BySets()),
})}

// SurjectiveOnRightInverse — the same trade relativized. `f` carries
// part of `s` onto all of `t` exactly when some `g` sends each point of
// `t` back into `s` and forward through `f` to itself. `g` is left
// unconstrained off `t`, which is what lets one total map stand in for
// a section defined only where it is needed.
var SurjectiveOnRightInverse = surjectiveOnRightInverseThm{family.Add(registry.ProofEntry{
	Name: "SurjectiveOnRightInverse",
	Key:  "prop_c7dec2e4c53729a9",
	Build: family.Theorem(
		"∀f:(A → B). ∀s:set(A). ∀t:set(B). "+
			"    (∀y:B. y ∈ t ⇒ ∃x:A. x ∈ s ∧ f(x) = y) ⇔ ∃g:(B → A). ∀y:B. y ∈ t ⇒ g(y) ∈ s ∧ f(g(y)) = y",
		BySets()),
})}

// SurjectiveForall — surjectivity as transfer for `∀`. Read `f` as a
// naming of `B` by `A`: every point of `B` has a name exactly when
// checking a predicate at every name is checking it at every point.
var SurjectiveForall = surjectiveForallThm{family.Add(registry.ProofEntry{
	Name: "SurjectiveForall",
	Key:  "prop_412bf204025c2070",
	Build: family.Theorem(
		"∀f:(A → B). (∀y:B. ∃x:A. f(x) = y) ⇔ ∀P:(B → bool). (∀x:A. P(f(x))) ⇔ ∀y:B. P(y)",
		BySets()),
})}

// SurjectiveExists — the `∃` twin, under the same reading: a witness
// among the names is a witness among the points, and conversely,
// exactly when every point has a name.
var SurjectiveExists = surjectiveExistsThm{family.Add(registry.ProofEntry{
	Name: "SurjectiveExists",
	Key:  "prop_ccd3ec7eec0d897f",
	Build: family.Theorem(
		"∀f:(A → B). (∀y:B. ∃x:A. f(x) = y) ⇔ ∀P:(B → bool). (∃x:A. P(f(x))) ⇔ ∃y:B. P(y)",
		BySets()),
})}

// Cantor — no map from `s` reaches every subset of `s`. The witness is
// the diagonal set; both halves of the claim — that it lies in `s`, and
// that no `x ∈ s` has `f(x)` equal to it — are its membership read at a
// point, which the set-side closer unfolds on its own, so the close
// needs no premise.
var Cantor = cantorThm{family.Add(registry.ProofEntry{
	Name: "Cantor",
	Key:  "prop_80fbd2fcc2dc3ca1",
	Build: family.Theorem(
		"∀s:set(A). ∀f:(A → set(A)). ∃t:set(A). t ⊆ s ∧ ∀x:A. x ∈ s ⇒ f(x) ≠ t",
		// s and f are bound so the witness text can spell them by name.
		func(a *Argument, s *Expr[Set[A]], f *Arrow[A, Set[A]]) {
			// The points of s that f sends to a set not containing them.
			diagonal := a.TermAs[Set[A]]("{x:A | x ∈ s ∧ x ∉ f(x)}")

			a.Take(diagonal)
			a.Show(
				"the diagonal set lies in s by construction, and "+
					"f(x) = it would put x in f(x) exactly when x is not",
				BySets())
		}),
})}

// ---------------------------------------------------------------------------
// Choosing a value at every point of a set
// ---------------------------------------------------------------------------
//
// The right inverse above is one instance of a trade made here for any
// relation: a relation that holds for some value at each point of a set
// is met by one function, `∀s ∈ S. ∃x. P(s, x)` traded for
// `∃f. ∀s ∈ S. P(s, f(s))`. It is Skolemization again, and the refuter
// closes it at a relation it cannot see into. A proof that makes the
// trade at a relation of its own cites the law there, rather than asking
// the refuter to unfold the relation's λ.

// ChooseOn — a choice function on a set: what holds for some value at each
// point is met by one function.
var ChooseOn = chooseOnThm{family.Add(registry.ProofEntry{
	Name: "ChooseOn",
	Key:  "prop_5b96eb4b8345e3ee",
	Build: family.Theorem(Statement{
		Binders: "∀P:(A → B → bool). ∀S:set(A).",
		Hypotheses: []string{
			"∀s:A. s ∈ S ⇒ ∃x:B. P(s, x)",
		},
		Conclusion: "∃f:(A → B). ∀s:A. s ∈ S ⇒ P(s, f(s))",
	}, func(a *Argument, P, S Term, given Fact) {
		a.Show(
			"choose a value at each point",
			By(given))
	}),
})}

// ChooseThreeOn — three choice functions at once: choose the first value at
// each point, then the second, then the third.
var ChooseThreeOn = chooseThreeOnThm{family.Add(registry.ProofEntry{
	Name: "ChooseThreeOn",
	Key:  "prop_ec6ee7282b8c51a7",
	Build: family.Theorem(Statement{
		Binders: "∀P:(A → B → C → D → bool). ∀S:set(A).",
		Hypotheses: []string{
			"∀s:A. s ∈ S ⇒ ∃x:B. ∃y:C. ∃w:D. P(s, x, y, w)",
		},
		Conclusion: "∃f:(A → B). ∃g:(A → C). ∃h:(A → D). ∀s:A. s ∈ S ⇒ P(s, f(s), g(s), h(s))",
	}, func(a *Argument, P, S Term, given Fact) {
		a.Show(
			"choose the three values at each point",
			By(given))
	}),
})}

// ---------------------------------------------------------------------------
// Being injective and surjective at once, and the one map that says so
// ---------------------------------------------------------------------------
//
// The mathematics is in the chapter README; what follows is what only this
// file can say.
//
// The collapse of the two one-sided inverses into a single map is what
// removes the slack on both sides: a section that is also a retraction
// has no freedom left to choose with, and a retraction that is also a
// section has nothing left to invent off the image. That is why the
// right-hand side binds ONE `g` rather than recording two.

// BijectiveLeftRightInverse — a map is injective and surjective exactly
// when some `g` is at once its section and its retraction.
var BijectiveLeftRightInverse = bijectiveLeftRightInverseThm{family.Add(registry.ProofEntry{
	Name: "BijectiveLeftRightInverse",
	Key:  "prop_54674229b9576ff5",
	Build: family.Theorem(
		"∀f:(A → B). "+
			"    injective_on(𝕌, f) ∧ (∀y:B. ∃x:A. f(x) = y) ⇔ "+
			"    ∃g:(B → A). (∀y:B. f(g(y)) = y) ∧ (∀x:A. g(f(x)) = x)",
		Chain(Unfold(InjectiveOnDef), BySets())),
})}

// BijectiveOnLeftRightInverse — the same collapse relativized. `f`
// carries `s` into `t`; it separates the points of `s` and covers `t`
// exactly when one `g` sends `t` back into `s` and inverts `f` on both
// sides there. Away from `t` and away from `f`'s image `g` is
// unconstrained, so a total map stands in for an inverse that exists
// only where a source does.
//
// What lets one `g` answer a demand that reads like two is the
// carrying condition. A `g` assembled from preimages is asked about
// `f(x)` for each `x` of `s`, and `f(x)` lies in `t`, where `g` has an
// answer; injectivity on `s` leaves it nothing to answer but `x`.
var BijectiveOnLeftRightInverse = bijectiveOnLeftRightInverseThm{family.Add(registry.ProofEntry{
	Name: "BijectiveOnLeftRightInverse",
	Key:  "prop_fdd44b0c7ea0a8c7",
	// `f`, `s`, `t` and the carrying condition are bound to reach the `⇔`;
	// neither direction needs to name them again.
	Build: family.Theorem(
		Statement{
			Binders: "∀f:(A → B). ∀s:set(A). ∀t:set(B).",
			Hypotheses: []string{
				"∀x:A. x ∈ s ⇒ f(x) ∈ t",
			},
			Conclusion: "injective_on(s, f) ∧ (∀y:B. y ∈ t ⇒ ∃x:A. x ∈ s ∧ f(x) = y) ⇔ " +
				"∃g:(B → A). " +
				"    (∀y:B. y ∈ t ⇒ g(y) ∈ s) ∧ ((∀y:B. y ∈ t ⇒ f(g(y)) = y) ∧ (∀x:A. x ∈ s ⇒ g(f(x)) = x))",
		},
		func(a *Argument, f *Arrow[A, B], s *Expr[Set[A]], t *Expr[Set[B]], carries Fact) {
			a.Iff()
			a.Forward(
				"the section surjectivity supplies is already a retraction: carrying "+
					"puts f(x) in t, where injectivity on s leaves g nothing but x",
				func(a *Argument, injAndSurj Fact) {
					// The two halves are wanted apart, and injectivity read
					// at its points: the closer works from injectivity and
					// surjectivity as separate facts, which the Normalized
					// shaping splits out.
					a.Do(BySets(Normalized, carries, a.Unfolded(injAndSurj, InjectiveOnDef)))
				})
			a.Backward(
				"both halves are read off g: g(y) ∈ s is a preimage of y ∈ "+
					"t, and g undoing f on s equates points of s with equal images",
				func(a *Argument, section Fact) {
					a.Do(Simp(Fwd(InjectiveOnDef)), BySets(section))
				})
		}),
})}

// ---------------------------------------------------------------------------
// Injectivity as a predicate: the identity, restriction, and composites
// ---------------------------------------------------------------------------
//
// A proof that keeps injectivity as a HYPOTHESIS holds the atom
// `injective_on(s, f)` and asks three things of it beyond its reading:
// where it comes from when the map is the identity, whether it survives
// restriction to a part of the set, and whether it survives
// composition. Each member below unfolds the predicate and,
// where a combinator stands in the statement, the combinator, and
// leaves the set-side closer a first-order argument.

// IdentityInjective — the identity separates the points of any set:
// two points it identifies are already one point.
var IdentityInjective = identityInjectiveThm{family.Add(registry.ProofEntry{
	Name: "IdentityInjective",
	Key:  "prop_ccefa1406bc462a5",
	Build: family.Theorem("∀s:set(A). injective_on(s, identity_map)",
		Chain(Unfold(InjectiveOnDef), Unfold(IdentityApply), BySets())),
})}

// InjectiveOnSubset — injectivity restricts: a map that separates the
// points of `t` separates those of any part of `t`, the pairs drawn
// from `s` being among the pairs drawn from `t`. Read at `t := 𝕌` it
// passes from a map injective outright to its restriction to a set.
var InjectiveOnSubset = injectiveOnSubsetThm{family.Add(registry.ProofEntry{
	Name: "InjectiveOnSubset",
	Key:  "prop_5445c5c3269e8b51",
	Build: family.Theorem(Statement{
		Binders: "∀f:(A → B). ∀s t:set(A).",
		Hypotheses: []string{
			"injective_on(t, f)",
			"s ⊆ t",
		},
		Conclusion: "injective_on(s, f)",
	},
		Chain(Unfold(InjectiveOnDef), BySets())),
})}

// InjectiveOnCompose — a composite of injective maps is injective,
// relativized: if `g` separates the points of `s` and sends them into
// `t`, where `f` separates points, then `f ∘ g` identifies two points
// of `s` only if `f` identifies their images in `t`, and then `g`
// identifies the points themselves.
var InjectiveOnCompose = injectiveOnComposeThm{family.Add(registry.ProofEntry{
	Name: "InjectiveOnCompose",
	Key:  "prop_b71dd0fcb4b4f483",
	Build: family.Theorem(Statement{
		Binders: "∀f:(B → C). ∀g:(A → B). ∀s:set(A). ∀t:set(B).",
		Hypotheses: []string{
			"injective_on(t, f)",
			"injective_on(s, g)",
			"∀x:A. x ∈ s ⇒ g(x) ∈ t",
		},
		Conclusion: "injective_on(s, f ∘ g)",
	},
		Chain(Unfold(InjectiveOnDef), Unfold(ComposeApply), BySets())),
})}

// ---------------------------------------------------------------------------
// Factoring a map through another map
// ---------------------------------------------------------------------------
//
// The mathematics is in the chapter README; what follows is what only this
// file can say.
//
// **Relativized first, in both pairs.** Each question is asked over the
// points a predicate `P` admits and again over all of them, and the
// unrestricted member comes second because it is proved from the
// relativized one — as in the injectivity part, and here for both pairs
// rather than one. The suffix for this flavour is `Gen` where the
// inverse laws use `On`; the difference is that these restrict by a
// bare predicate and those by a set, so there is no set to name and
// the suffix is `Gen`.
//
// **On the arm that names the factor, the unrestricted members are
// point-free** (`f = g ∘ h`) where the relativized ones are pointwise
// (`f(x) = g(h(x))`) — a composite is what the unrestricted question is
// about. The other arm, the condition on `f` and `g`, is pointwise
// throughout; it has to be, since it quantifies over points.
//
// **`FactorsLeftGen` is `InjectiveOnLeftInverse`'s architecture, read at
// the fibres of `g` instead of `f`** — a fibre section, a choice
// section, and a two-fact `Show` chaining them. The two members'
// comments run parallel deliberately; read either one and the other is
// the same argument with `g` in place of `f`.
//
// **The two pairs are proved differently, and that is not mathematics.**
// `FactorsLeft` cites its `Gen`; `FactorsRight` settles its unrestricted
// form directly and declares no deps, because the right-hand question's
// whole content is the trade of quantifiers and nothing is saved by
// going through the guard. The measurements are in PLAN.

// FactorsRightGen — `f = g ∘ h` is solvable for `h`, over the points `P`
// admits, exactly when every value `f` takes there is already a value of
// `g`. One direction reads `y := h(x)` off the factor; the other collects
// a choice of `y` per admitted `x` into a single map. That collection is
// Skolemization, which is why no `h` is ever constructed here.
var FactorsRightGen = factorsRightGenThm{family.Add(registry.ProofEntry{
	Name: "FactorsRightGen",
	Key:  "prop_f8aeffe35b96a9d2",
	Build: family.Theorem(
		"∀P:(A → bool). ∀f:(A → B). ∀g:(C → B). "+
			"    (∀x:A. P(x) ⇒ ∃y:C. g(y) = f(x)) ⇔ ∃h:(A → C). ∀x:A. P(x) ⇒ f(x) = g(h(x))",
		BySets()),
})}

// FactorsRight — the same question with no restriction, and stated
// point-free, which is the form it is usually asked in: `f` runs through
// `g` exactly when `f`'s values are among `g`'s.
var FactorsRight = factorsRightThm{family.Add(registry.ProofEntry{
	Name: "FactorsRight",
	Key:  "prop_f99784d4f0c37f28",
	Build: family.Theorem(
		"∀f:(A → B). ∀g:(C → B). (∀x:A. ∃y:C. g(y) = f(x)) ⇔ (∃h:(A → C). f = g ∘ h)",
		func(a *Argument) {
			// `g ∘ h` says nothing about points until it is applied to one,
			// so the composite is unfolded before anything else: the right
			// side becomes `f = λx. g(h(x))`, and what is left is the trade
			// of quantifiers with no guard on it.
			a.Do(Unfold(ComposeApply), BySets())
		}),
})}

// FactorsLeftGen — `f = h ∘ g` is solvable for `h`, over the points `P`
// admits, exactly when `f` cannot separate two points that `g` identifies.
// The `h` produced is unconstrained off `g`'s image, so a total map can
// stand in for one defined only where `g` lands.
//
// The proof passes through a third form, stated below as `fibres`, in
// the shape the header describes.
var FactorsLeftGen = factorsLeftGenThm{family.Add(registry.ProofEntry{
	Name: "FactorsLeftGen",
	Key:  "prop_bfb3e775268f2a89",
	Build: family.Sections(
		"∀P:(A → bool). ∀f:(A → B). ∀g:(A → C). "+
			"    (∀x y:A. P(x) ∧ P(y) ∧ g(x) = g(y) ⇒ f(x) = f(y)) ⇔ ∃h:(C → B). ∀x:A. P(x) ⇒ f(x) = h(g(x))",
		func(ctx *Script, headline string) *GoalStackNode {
			// The separation condition, read one fibre of `g` at a time.
			// That `f` identifies whatever `g` identifies is the claim, made
			// of each `z : C` separately, that `f` is constant on the
			// admitted points `g` sends to `z` — which is what a `b` they
			// must each equal asserts. Where no admitted point lies over `z`
			// the claim is vacuous and `b` is arbitrary; that is why the
			// nominee is bound by `∃` here rather than produced by a partial
			// function.
			fibres := ctx.Lemma(
				"∀P:(A → bool). ∀f:(A → B). ∀g:(A → C). "+
					"    (∀x y:A. P(x) ∧ P(y) ∧ g(x) = g(y) ⇒ f(x) = f(y)) ⇔ "+
					"    ∀z:C. ∃b:B. ∀x:A. P(x) ∧ z = g(x) ⇒ b = f(x)",
				BySets())

			// Where CHOICE enters, and the only place it does — the same
			// step `InjectiveOnLeftInverse` takes, between these two
			// endpoints: "`f` is constant on each fibre of `g`" on the left,
			// "`f` factors through `g`" on the right.
			choice := ctx.Lemma(
				"∀P:(A → bool). ∀f:(A → B). ∀g:(A → C). "+
					"    (∀z:C. ∃b:B. ∀x:A. P(x) ∧ z = g(x) ⇒ b = f(x)) ⇔ ∃h:(C → B). ∀x:A. P(x) ⇒ f(x) = h(g(x))",
				BySets())

			return ctx.Theorem(headline, func(a *Argument) {
				a.Show(
					"separation and factoring are each equivalent to the fibre form, hence to each other",
					By(fibres, choice))
			})
		}),
})}

// FactorsLeft — the same, unrestricted and point-free: the relativized
// law read at the predicate every point satisfies. On that guard the
// restriction asks nothing, so the two statements differ only by the
// guard and by `∘`, and the proof is the pair of those two differences.
var FactorsLeft = factorsLeftThm{family.Add(registry.ProofEntry{
	Name: "FactorsLeft",
	Key:  "prop_c86deca9ba1be7db",
	Build: family.Theorem(
		"∀f:(A → B). ∀g:(A → C). (∀x y:A. g(x) = g(y) ⇒ f(x) = f(y)) ⇔ (∃h:(C → B). f = h ∘ g)",
		func(a *Argument, f *Arrow[A, B], g *Arrow[A, C]) {

			// Unfold `∘` so this member's point-free right side becomes
			// pointwise, which is the form `FactorsLeftGen` states.
			a.Do(Unfold(ComposeApply))

			// `λx. ⊤` admits every point. It is a bare predicate and not a
			// set, so what discharges the guard below is β-reduction, and no
			// membership law — hence no `set_basic` dep, where the
			// injectivity pair's unrestricted member needs one.
			everywhere := a.TermAs[Fun[A, Bool]]("λx:A. ⊤")

			// The cite is ground in all three slots because it is a fact
			// about THIS `f` and `g`, not about every pair.
			a.Show(
				"the relativized law at the guard that admits every point",
				By(Normalized, FactorsLeftGen.At(everywhere, f, g)))
		}),
})}

// ---------------------------------------------------------------------------
// The sets a map names: its preimages and its support
// ---------------------------------------------------------------------------
//
// Two set terms every chapter reading a map spells: the preimage of a
// set, cut to a source set, and the support of the map relative to a
// value. Both are definitions whose membership the closers read as its
// condition. What pulling back says about `f` — injective exactly when
// `f` is surjective, surjective exactly when `f` is injective — is
// set_image's, beside the same two questions asked of `image(f, ·)`.

// PreimageOnDef — `preimage_on(s, f, t)`: the points of s that f sends
// into t, the preimage of t restricted to s. At s := 𝕌 it is the whole
// preimage.
var PreimageOnDef = preimageOnDefThm{family.Define(registry.DefEntry{
	Name:  "PreimageOnDef",
	Key:   "prop_87b325674723f80e",
	Const: "preimage_on",
	Type:  "set(A) → (A → B) → set(B) → set(A)",
	Equations: []string{
		"∀s:set(A). ∀f:(A → B). ∀t:set(B). preimage_on(s, f, t) = {x:A | x ∈ s ∧ f(x) ∈ t}",
	},
	// The closers read x ∈ preimage_on(s, f, t) as x ∈ s ∧ f(x) ∈ t.
	MembershipRead: true,
})}

// FunSupportDef — `fun_support(zero, f)`: the points where f does not
// take the value zero, the support of f relative to zero.
var FunSupportDef = funSupportDefThm{family.Define(registry.DefEntry{
	Name:  "FunSupportDef",
	Key:   "prop_95dbb7a555b2eb7",
	Const: "fun_support",
	Type:  "B → (A → B) → set(A)",
	Equations: []string{
		"∀zero:B. ∀f:(A → B). fun_support(zero, f) = {x:A | f(x) ≠ zero}",
	},
	// The closers read x ∈ fun_support(zero, f) as f(x) ≠ zero.
	MembershipRead: true,
})}

// InFunSupport — a point lies in the support of f exactly when f does
// not take the value zero there: the definition read at a point.
var InFunSupport = inFunSupportThm{family.Add(registry.ProofEntry{
	Name: "InFunSupport",
	Key:  "prop_6d1fa65b53166876",
	Build: family.Theorem("∀zero:B. ∀f:(A → B). ∀x:A. x ∈ fun_support(zero, f) ⇔ f(x) ≠ zero",
		func(a *Argument, zero *Expr[B], f *Arrow[A, B], x *Expr[A]) {
			a.Show(
				"a point of the comprehension is one where f is not zero",
				Unfold(FunSupportDef),
				BySets())
		}),
})}
