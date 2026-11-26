// fibre_quotient.go — the quotient of a space by the fibres of a continuous
// map. The map factors through the class map as a continuous one-to-one map
// of the classes onto its own image; and when the map is onto a Hausdorff
// space, already onto from a compact part of its domain, that factor is a
// homeomorphism, so the target is the quotient of the domain by the fibres.

package continuous

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/topology/compact"
	"github.com/euc-ai/xugo/library/proofs/topology/topological_space"
	"github.com/euc-ai/xugo/library/registry"
)

// FibreQuotientFactor — a continuous map factors through the class map onto
// the quotient of its space by its fibres, as a continuous one-to-one map of
// the classes with the map's own image. The factor h sends a class to the
// value of f at a point chosen in it, which is f's value at every point of
// the class. Its composite with the class map agrees with f on the space, so
// is continuous, and so is h, by the universal property of the quotient map;
// the fibre of f over h's value at a class is that class, which undoes h; and
// the classes are the image of the space under the class map, so h carries
// them onto the values of f.
var FibreQuotientFactor = fibreQuotientFactorThm{family.Add(registry.ProofEntry{
	Name: "FibreQuotientFactor",
	Key:  "prop_9da94f5a54ce2f19",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀S:set(set(B)). ∀f:(A → B).",
		Hypotheses: []string{
			"is_topology(T)",
			"continuous_map(T, S, f)",
		},
		Conclusion: "∃h:(set(A) → B). " +
			"    (∀x:A. x ∈ ⋃T ⇒ h(«fibre»(x)) = f(x)) ∧ " +
			"    continuous_map(quotient_topology(T, «fibre»), S, h) ∧ " +
			"    injective_on(⋃quotient_topology(T, «fibre»), h) ∧ " +
			"    image(h, ⋃quotient_topology(T, «fibre»)) = image(f, ⋃T)",
		Abbrev: Abbrev{
			{Name: "fibre", Text: "λx:A. {y:A | y ∈ ⋃T ∧ f(y) = f(x)}"},
		},
	},
		func(
			a *Argument,
			T *Expr[Set[Set[A]]],
			S *Expr[Set[Set[B]]],
			f *Arrow[A, B],
			topology topological_space.IsTopologyFact[on.T],
			continuous ContinuousMapFact[on.T, on.S],
		) {
			quotient := a.Have(
				"the class map is a quotient map onto the quotient topology",
				"quotient_map(T, quotient_topology(T, «fibre»), «fibre»)",
				By(QuotientTopologyQuotientMap, topology))
			h, hDef := a.LetAs[Fun[Set[A], B]]("h", "λc:set(A). f(εx:A. x ∈ c)")
			a.Take(h)
			composite := a.TermAs[Fun[A, B]]("h ∘ «fibre»")
			factor := a.Have(
				"h takes f's value on the class of x: the class "+
					"holds x, so the point chosen in it has f's value at x",
				"∀x:A. x ∈ ⋃T ⇒ h(«fibre»(x)) = f(x)",
				BySets(hDef))
			agree := a.Have(
				"so h ∘ «fibre» agrees with f on the space",
				"∀x:A. x ∈ ⋃T ⇒ f(x) = (h ∘ «fibre»)(x)",
				Simp(Fwd(functions.ComposeApply)),
				By(factor))
			hContinuous := a.Have(
				"h is continuous on the quotient: its composite with "+
					"the quotient map agrees with f, so is continuous",
				"continuous_map(quotient_topology(T, «fibre»), S, h)",
				By(agree, Eq.Read(continuous).At(composite), QuotientUniversal.Read(quotient)))
			injective := a.Have(
				"h is one-to-one on the classes: the fibre of f over h's value at a class is that class",
				"injective_on(image(«fibre», ⋃T), h)",
				Simp(Fwd(functions.InjectiveOnLeftInverse)),
				Witness(a.TermAs[Fun[B, Set[A]]]("λb:B. {y:A | y ∈ ⋃T ∧ f(y) = b}")),
				Simp(Fwd(set_image.ForallInImage)),
				Derive(func(b *Argument) {
					x := b.FixAs[A]("x")
					xIn := b.Assume()
					b.Show(
						"at the class of x, h takes the value f(x), whose fibre is the class of x",
						// Rewritten by that value the two sides are one set, an
						// identity closed as it stands, with nothing to refute.
						GroupPremises(xIn, factor.At(x)).Rw(),
						Basic())
				}))
			space := a.TermAs[Set[A]]("⋃T")
			sameImage := a.Have(
				"h has f's image: the classes are the image of the space, on which h ∘ «fibre» agrees with f",
				"image(h, ⋃quotient_topology(T, «fibre»)) = image(f, ⋃T)",
				By(
					QuotientOnto.Read(quotient),
					set_image.ImageCompose.At(h, a.TermAs[Fun[A, Set[A]]]("«fibre»"), space),
					set_image.ImageCongruence.At(f, composite, space),
					agree))
			a.Show(
				"h is the factor sought, the classes being the image of the space under the class map",
				By(QuotientOnto.Read(quotient), factor, hContinuous, injective, sameImage))
		}),
})}

// FibreQuotientHomeomorphic — a continuous map onto a Hausdorff space that is
// already onto from a compact part k of its domain identifies the target with
// the quotient of the domain by its fibres. The map factors through the class
// map as a continuous one-to-one map h of the classes with the map's own
// image, which is the whole second space: f carries the space into it, and k
// already onto it. The classes of the points of a set are the fibres of f over
// its values, and the space and k have the same values; so every class is the
// class of a point of k, and the quotient space is compact, the image of k
// under the continuous class map. A continuous bijection from a compact space
// onto a Hausdorff space is a homeomorphism.
var FibreQuotientHomeomorphic = fibreQuotientHomeomorphicThm{family.Add(registry.ProofEntry{
	Name: "FibreQuotientHomeomorphic",
	Key:  "prop_4a6fa477c19ef06e",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀S:set(set(B)). ∀f:(A → B). ∀k:set(A).",
		Hypotheses: []string{
			"is_topology(T)",
			"is_topology(S)",
			"hausdorff(S)",
			"continuous_map(T, S, f)",
			"compact_in(T, k)",
			"image(f, k) = ⋃S",
		},
		Conclusion: "homeomorphic(quotient_topology(T, «fibre»), S)",
		Abbrev: Abbrev{
			{Name: "fibre", Text: "λx:A. {y:A | y ∈ ⋃T ∧ f(y) = f(x)}"},
		},
	},
		func(
			a *Argument,
			T *Expr[Set[Set[A]]],
			S *Expr[Set[Set[B]]],
			f *Arrow[A, B],
			k *Expr[Set[A]],
			topologyT topological_space.IsTopologyFact[on.T],
			topologyS topological_space.IsTopologyFact[on.S],
			hausdorff Fact,
			continuous ContinuousMapFact[on.T, on.S],
			compactK, onto Fact,
		) {
			h, induced := a.UnpackAs[Fun[Set[A], B]](
				GroupPremises(topologyT, continuous, FibreQuotientFactor.At(T, S, f)), "h")
			parts := a.Conjuncts(
				induced,
				"h takes f's value on the class of every point",
				"h is continuous on the quotient",
				"h is one-to-one on the classes",
				"and h has f's image")
			hContinuous, injective, sameImage := parts[1], parts[2], parts[3]
			quotient := a.Have(
				"the class map is a quotient map onto the quotient topology",
				"quotient_map(T, quotient_topology(T, «fibre»), «fibre»)",
				By(QuotientTopologyQuotientMap, topologyT))
			kIn := a.Have(
				"k lies in the space, being compact there",
				"k ⊆ ⋃T",
				By(compactK, compact.CompactInDef))
			fOnto := a.Have(
				"f carries the space onto the second space: into it, being continuous, and onto it already from k",
				"image(f, ⋃T) = ⋃S",
				BySets(MapsInto.Read(continuous), onto, kIn))
			fibresOver := a.Have(
				"the classes of the points of a set are the fibres of f over its values",
				"∀s:set(A). image(«fibre», s) = image(λb:B. {y:A | y ∈ ⋃T ∧ f(y) = b}, image(f, s))",
				By(set_image.ImageCompose, functions.ComposeApply))
			classes := a.Have(
				"every class is the class of a point of k: both are the fibres over the points of the second space",
				"⋃quotient_topology(T, «fibre») = image(«fibre», k)",
				By(
					QuotientOnto.Read(quotient),
					fibresOver.At(a.TermAs[Set[A]]("⋃T")),
					fibresOver.At(k),
					onto,
					fOnto))
			compactQuotient := a.Have(
				"so the quotient space is compact, the image of k under the continuous class map",
				"compact_in(quotient_topology(T, «fibre»), ⋃quotient_topology(T, «fibre»))",
				By(classes, compactK, ImageCompact.Read(QuotientImpContinuous.Read(quotient)).At(k)))
			a.Show(
				"h is a continuous bijection from the compact quotient "+
					"onto the Hausdorff second space, a homeomorphism",
				Simp(Fwd(HomeomorphicDef)),
				Witness(h),
				By(
					CompactHausdorffHomeomorphism.Read(hContinuous),
					topologyS,
					hausdorff,
					compactQuotient,
					sameImage,
					fOnto,
					injective))
		}),
})}
