// normalize.go — a map normalized off a set. A map on a type carries
// values outside the set it is meant on, and two maps meant on the
// same set differ there without differing in substance. `normalize_on(S,
// z, f)` pins a map to one default value z off S, so that the maps
// meant on S, normalized, are equal exactly when they agree on S: the
// device by which a class of maps on a set becomes a set of maps whose
// equality is extensional. The default is the caller's — `junk`, minted
// here for the purpose, or a zero — and the laws below hold for any.
//
// A composite of two normalized maps need not be normalized: g ∘ f off
// S is g at the default, not the default. So a composite is normalized
// again, and NormalizeOnComposeInner says that normalizing the inner
// map first changes nothing on S.

package functions

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// Normalizing a map off a set
// ---------------------------------------------------------------------------

// JunkDef — `junk`: an inhabitant of the type with no property beyond
// existing, the default a normalized map takes off its set when no
// other value is meant; maps normalized with it agree off the set.
var JunkDef = junkDefThm{family.Define(registry.DefEntry{
	Name:      "JunkDef",
	Key:       "prop_67e36d394836e31c",
	Const:     "junk",
	Type:      "A",
	Equations: []string{"junk = εx:A. ⊤"},
})}

// NormalizeOnDef — `normalize_on(S, z, f)`: f on S and z off it.
var NormalizeOnDef = normalizeOnDefThm{family.Define(registry.DefEntry{
	Name:  "NormalizeOnDef",
	Key:   "prop_c1408d925a1b900b",
	Const: "normalize_on",
	Type:  "set(A) → B → (A → B) → A → B",
	Equations: []string{
		"∀S:set(A). ∀z:B. ∀f:(A → B). normalize_on(S, z, f) = λx:A. COND(x ∈ S, f(x), z)",
	},
})}

// NormalizeOnIn — on S the normalized map is f: membership selects
// the conditional's first branch.
var NormalizeOnIn = normalizeOnInThm{family.Add(registry.ProofEntry{
	Name: "NormalizeOnIn",
	Key:  "prop_fae23c9defb28b79",
	Build: family.Theorem(Statement{
		Binders: "∀S:set(A). ∀z:B. ∀f:(A → B). ∀x:A.",
		Hypotheses: []string{
			"x ∈ S",
		},
		Conclusion: "normalize_on(S, z, f, x) = f(x)",
	},
		func(a *Argument, S *Expr[Set[A]], z *Expr[B], f *Arrow[A, B], x *Expr[A], inS Fact) {
			a.Show(
				"membership selects the conditional's first branch",
				Unfold(NormalizeOnDef),
				By(inS))
		}),
})}

// NormalizeOnOut — off S the normalized map is the default:
// nonmembership selects the conditional's second branch.
var NormalizeOnOut = normalizeOnOutThm{family.Add(registry.ProofEntry{
	Name: "NormalizeOnOut",
	Key:  "prop_215b05189f04cdc3",
	Build: family.Theorem(Statement{
		Binders: "∀S:set(A). ∀z:B. ∀f:(A → B). ∀x:A.",
		Hypotheses: []string{
			"x ∉ S",
		},
		Conclusion: "normalize_on(S, z, f, x) = z",
	},
		func(a *Argument, S *Expr[Set[A]], z *Expr[B], f *Arrow[A, B], x *Expr[A], offS Fact) {
			a.Show(
				"nonmembership selects the conditional's second branch",
				Unfold(NormalizeOnDef),
				By(offS))
		}),
})}

// NormalizeOnEqIff — two normalized maps are equal exactly when the
// maps agree on S: read equality on S, then use the common default off S.
var NormalizeOnEqIff = normalizeOnEqIffThm{family.Add(registry.ProofEntry{
	Name: "NormalizeOnEqIff",
	Key:  "prop_96b789d8bd012405",
	Build: family.Theorem("∀S:set(A). ∀z:B. ∀f g:(A → B). "+
		"    normalize_on(S, z, f) = normalize_on(S, z, g) ⇔ (∀x:A. x ∈ S ⇒ f(x) = g(x))",
		func(a *Argument, S *Expr[Set[A]], z *Expr[B], f, g *Arrow[A, B]) {
			a.Iff()
			a.Forward(
				"equality of the normalized maps gives agreement on S",
				func(b *Argument, equal Fact) {
					b.FixAs[A]("x")
					b.Assume()
					atPoint := b.Have(
						"evaluate the equality at x",
						"normalize_on(S, z, f, x) = normalize_on(S, z, g, x)",
						By(Normalized, equal))
					b.Show(
						"on S the normalized values are the original values",
						atPoint.Simp(Fwd(NormalizeOnIn)),
						By(atPoint))
				})
			a.Backward(
				"agreement on S determines both normalized maps",
				func(b *Argument, agree Fact) {
					b.Do(Funext())
					y := b.FixAs[A]("y")
					b.Cases(b.TermAs[Bool]("y ∈ S"))
					b.When(
						"on S the original values agree",
						func(c *Argument, inS Fact) {
							c.Show(
								"normalization preserves the equal values",
								Simp(Fwd(NormalizeOnIn)),
								By(inS, agree.At(y)))
						})
					b.Otherwise(
						"off S both values are the default",
						Simp(Fwd(NormalizeOnOut)),
						Refl())
				})
		}),
})}

// NormalizedEqIff — two maps already normalized on S with the same
// default are equal exactly when they agree on S: each map is its own
// normalization, so their equality is that of their normalizations.
var NormalizedEqIff = normalizedEqIffThm{family.Add(registry.ProofEntry{
	Name: "NormalizedEqIff",
	Key:  "prop_5188e9bb6169b3db",
	Build: family.Theorem(Statement{
		Binders: "∀S:set(A). ∀z:B. ∀f g:(A → B).",
		Hypotheses: []string{
			"normalize_on(S, z, f) = f",
			"normalize_on(S, z, g) = g",
		},
		Conclusion: "f = g ⇔ ∀x:A. x ∈ S ⇒ f(x) = g(x)",
	},
		func(a *Argument, S *Expr[Set[A]], z *Expr[B], f, g *Arrow[A, B], fixed Fact) {
			a.Show(
				"each map is its own normalization, whose equality is agreement on S",
				By(Normalized, fixed, NormalizeOnEqIff.At(S, z, f, g)))
		}),
})}

// NormalizeOnIdempotent — normalizing twice is normalizing once:
// the normalized map agrees with the original map on S.
var NormalizeOnIdempotent = normalizeOnIdempotentThm{family.Add(registry.ProofEntry{
	Name: "NormalizeOnIdempotent",
	Key:  "prop_70996348879bd326",
	Build: family.Theorem("∀S:set(A). ∀z:B. ∀f:(A → B). "+
		"    normalize_on(S, z, normalize_on(S, z, f)) = normalize_on(S, z, f)",
		func(a *Argument, S *Expr[Set[A]], z *Expr[B], f *Arrow[A, B]) {
			normalized := a.TermAs[Fun[A, B]]("normalize_on(S, z, f)")
			a.Show(
				"agreement on S makes the normalizations equal",
				By(NormalizeOnIn, NormalizeOnEqIff.At(S, z, normalized, f)))
		}),
})}

// NormalizeOnComposeInner — inner normalization does not change the
// normalized composite: the composites agree on S, so their normalizations
// with the same default agree everywhere.
var NormalizeOnComposeInner = normalizeOnComposeInnerThm{family.Add(registry.ProofEntry{
	Name: "NormalizeOnComposeInner",
	Key:  "prop_69b91a774a6cb1ac",
	Build: family.Theorem("∀S:set(A). ∀z:B. ∀w:C. ∀f:(A → B). ∀g:(B → C). "+
		"    normalize_on(S, w, g ∘ normalize_on(S, z, f)) = normalize_on(S, w, g ∘ f)",
		func(a *Argument, S *Expr[Set[A]], z *Expr[B], w *Expr[C], f *Arrow[A, B], g *Arrow[B, C]) {
			agree := a.Have(
				"the composites agree on S",
				"∀x:A. x ∈ S ⇒ (g ∘ normalize_on(S, z, f))(x) = (g ∘ f)(x)",
				Derive(func(b *Argument) {
					b.FixAs[A]("x")
					b.Assume()
					b.Show(
						"both composites have value g applied to f at x",
						Simp(Fwd(ComposeApply), Fwd(NormalizeOnIn)),
						Refl())
				}))
			withNormalized := a.TermAs[Fun[A, C]]("g ∘ normalize_on(S, z, f)")
			composite := a.TermAs[Fun[A, C]]("g ∘ f")
			a.Show(
				"agreement on S determines the normalized composites",
				By(agree, NormalizeOnEqIff.At(S, w, withNormalized, composite)))
		}),
})}
