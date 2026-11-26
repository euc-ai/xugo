package continuous

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/registry"
)

// ContinuousHomSetDef — continuous maps with a fixed value off the source
// space, so each map on that space has a single representative.
var ContinuousHomSetDef = continuousHomSetDefThm{family.Define(registry.DefEntry{
	Name:  "ContinuousHomSetDef",
	Key:   "prop_b2318f10ad0ab836",
	Const: "continuous_hom_set",
	Type:  "set(set(A)) → set(set(B)) → set(A → B)",
	Equations: []string{
		"∀T:set(set(A)). ∀S:set(set(B)). " +
			"    continuous_hom_set(T, S) = " +
			"    {f:(A → B) | continuous_map(T, S, f) ∧ normalize_on(⋃T, junk, f) = f}",
	},
	Deps: []registry.EntryLike{ContinuousMap},
})}

// NormalizeHomSetIff — a map has a representative in the continuous
// hom-set exactly when it is continuous: normalization preserves its
// source values and is idempotent.
var NormalizeHomSetIff = normalizeHomSetIffThm{family.Add(registry.ProofEntry{
	Name: "NormalizeHomSetIff",
	Key:  "prop_2b252745d163a83b",
	Build: family.Theorem("∀T:set(set(A)). ∀S:set(set(B)). ∀f:(A → B). "+
		"    normalize_on(⋃T, junk, f) ∈ continuous_hom_set(T, S) ⇔ continuous_map(T, S, f)",
		func(a *Argument, T *Expr[Set[Set[A]]], S *Expr[Set[Set[B]]], f *Arrow[A, B]) {
			normalized := a.TermAs[Fun[A, B]]("normalize_on(⋃T, junk, f)")
			agree := a.Have(
				"normalization preserves every value in the source space",
				"∀x:A. x ∈ ⋃T ⇒ normalize_on(⋃T, junk, f, x) = f(x)",
				By(functions.NormalizeOnIn))
			a.Do(Unfold(ContinuousHomSetDef))
			a.Iff()
			a.Forward(
				"continuity passes from the representative to the original map",
				func(b *Argument, representative Fact) {
					b.Show(
						"the maps agree everywhere continuity reads them",
						By(agree, representative, Eq.At(T, S, normalized, f)))
				})
			a.Backward(
				"a continuous map normalizes to a continuous representative",
				func(b *Argument, continuous Fact) {
					normalizedContinuous := b.Have(
						"normalization preserves continuity",
						"continuous_map(T, S, normalize_on(⋃T, junk, f))",
						By(agree, continuous, Eq.At(T, S, f, normalized)))
					b.Show(
						"idempotence makes the normalized map a hom-set representative",
						BySets(
							normalizedContinuous,
							functions.NormalizeOnIdempotent.At(b.TermAs[Set[A]]("⋃T"), b.TermAs[B]("junk"), f)))
				})
		}),
})}

// HomSetExt — two continuous hom-set representatives are equal exactly
// when they agree on the source space: both are fixed by normalization.
var HomSetExt = homSetExtThm{family.Add(registry.ProofEntry{
	Name: "HomSetExt",
	Key:  "prop_ac24a4050f952c6b",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀S:set(set(B)). ∀f g:(A → B).",
		Hypotheses: []string{
			"f ∈ continuous_hom_set(T, S)",
			"g ∈ continuous_hom_set(T, S)",
		},
		Conclusion: "f = g ⇔ ∀x:A. x ∈ ⋃T ⇒ f(x) = g(x)",
	},
		func(a *Argument, T *Expr[Set[Set[A]]], S *Expr[Set[Set[B]]], f, g *Arrow[A, B], members Fact) {
			membership := a.Unfolded(members, ContinuousHomSetDef)
			a.Show(
				"both representatives are fixed by normalization, so they are equal exactly when they agree on ⋃T",
				BySets(membership, functions.NormalizedEqIff.At(a.TermAs[Set[A]]("⋃T"), a.TermAs[B]("junk"), f, g)))
		}),
})}

// HomSetIdentity — the normalized identity is a continuous hom-set
// representative: the identity is continuous, and normalization preserves continuity.
var HomSetIdentity = homSetIdentityThm{family.Add(registry.ProofEntry{
	Name: "HomSetIdentity",
	Key:  "prop_9b9b1ce6f0c5830f",
	Build: family.Theorem("∀T:set(set(A)). "+
		"    normalize_on(⋃T, junk, identity_map) ∈ continuous_hom_set(T, T)",
		func(a *Argument, T *Expr[Set[Set[A]]]) {
			a.Show(
				"the continuous identity has a canonical hom-set representative",
				By(Identity.At(T), NormalizeHomSetIff.At(T, T, a.TermAs[Fun[A, A]]("identity_map"))))
		}),
})}

// HomSetCompose — the normalized composite of continuous hom-set
// representatives is a representative: continuity composes and survives normalization.
var HomSetCompose = homSetComposeThm{family.Add(registry.ProofEntry{
	Name: "HomSetCompose",
	Key:  "prop_eaa9792189171d8f",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀S:set(set(B)). ∀R:set(set(C)). ∀f:(A → B). ∀g:(B → C).",
		Hypotheses: []string{
			"f ∈ continuous_hom_set(T, S)",
			"g ∈ continuous_hom_set(S, R)",
		},
		Conclusion: "normalize_on(⋃T, junk, g ∘ f) ∈ continuous_hom_set(T, R)",
	},
		func(
			a *Argument,
			T *Expr[Set[Set[A]]],
			S *Expr[Set[Set[B]]],
			R *Expr[Set[Set[C]]],
			f *Arrow[A, B],
			g *Arrow[B, C],
			members Fact,
		) {
			membership := a.Unfolded(members, ContinuousHomSetDef)
			continuous := a.Have(
				"both representatives are continuous",
				"continuous_map(T, S, f) ∧ continuous_map(S, R, g)",
				BySets(membership))
			composite := a.Have(
				"continuity composes through the middle space",
				"continuous_map(T, R, g ∘ f)",
				By(continuous, Compose.At(T, S, f, R, g)))
			a.Show(
				"the continuous composite has a canonical hom-set representative",
				By(composite, NormalizeHomSetIff.At(T, R, a.TermAs[Fun[A, C]]("g ∘ f"))))
		}),
})}
