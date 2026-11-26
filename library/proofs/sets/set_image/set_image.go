// set_image.go — the chapter: the image of a set under a map.
//
// Seven parts, marked by banners:
//
// - What taking images preserves, and the notation it replaces
// - What it takes to be a point of an image
// - What taking an image does to the set constructions
// - Arbitrary unions and intersections through a map
// - The image as a statement about the map
// - Inclusion and the image
// - The preimage as a statement about the map

package set_image

import (
	"github.com/euc-ai/xugo/ext"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/internal/setvocab"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// What taking images preserves, and the notation it replaces
// ---------------------------------------------------------------------------
//
// Two of the members here are the functor laws proper: the identity map
// leaves a set alone, and a composite map takes images one factor at a
// time. The other three say that `image` is not a new idea at all — it
// is the comprehension `{f(x) | x ∈ s}` given a name, which is why
// nothing in the chapter has to choose between the two notations.
//
// `ImageIdentity` and `ImageI` are the same theorem written through the
// two spellings of the identity map — the λ and the combinator `identity_map`.
// Both are here because later chapters cite both, and because the
// difference is exactly one definitional unfolding, which is visible in
// their proofs and nowhere else.

// ImageIdentity — the identity map moves nothing, so a set is its own
// image under it.
var ImageIdentity = imageIdentityThm{family.Add(registry.ProofEntry{
	Name: "ImageIdentity",
	Key:  "prop_be42f303e6c34091",
	Build: family.Theorem(
		"∀s:set(A). image(λx:A. x, s) = s",
		BySets()),
})}

// ImageI — the same statement about the identity COMBINATOR. `identity_map` is a
// name for the λ above, and unfolding it is the whole of the difference.
var ImageI = imageIThm{family.Add(registry.ProofEntry{
	Name: "ImageI",
	Key:  "prop_9090e763ef6c0ffa",
	Build: family.Theorem(
		"∀s:set(A). image(identity_map, s) = s",
		func(a *Argument) {
			// `identity_map` is opaque to the closer: its vocabulary is the set
			// constructors, so the membership residual has nothing to say
			// about a function constant. Unfolding it to the λ is what
			// leaves a goal about points.
			a.Do(Unfold(functions.IdentityApply), BySets())
		}),
})}

// ImageCompose — functoriality. Taking the image under a composite is
// taking it twice, and the two factors can be applied in either grouping
// because a point's route through them is the same either way.
var ImageCompose = imageComposeThm{family.Add(registry.ProofEntry{
	Name: "ImageCompose",
	Key:  "prop_efbceaa0412189af",
	Build: family.Theorem(
		"∀f:(B → C). ∀g:(A → B). ∀s:set(A). image(f ∘ g, s) = image(f, image(g, s))",
		func(a *Argument) {
			// Same reason as ImageI: `∘` has to become an application
			// before the residual is about points at all.
			a.Do(Unfold(functions.ComposeApply), BySets())
		}),
})}

// SimpleImage — the image IS the comprehension. Everything the chapter
// says about `image(f, s)` could be said about `{f(x) | x ∈ s}`, and
// this is the equation that licenses moving between them.
var SimpleImage = simpleImageThm{family.Add(registry.ProofEntry{
	Name: "SimpleImage",
	Key:  "prop_9d262d3f197d301a",
	Build: family.Theorem(
		"∀f:(A → B). ∀s:set(A). {f(x) | x:A | x ∈ s} = image(f, s)",
		BySets()),
})}

// SimpleImageGen — the same equation with an arbitrary guard in place of
// membership. Collecting `f(x)` over the points satisfying P is the image
// of the set those points form, so a comprehension never needs to mention
// both a guard and a map at once.
var SimpleImageGen = simpleImageGenThm{family.Add(registry.ProofEntry{
	Name: "SimpleImageGen",
	Key:  "prop_1598fd966355209b",
	Build: family.Theorem(
		"∀f:(A → B). ∀P:(A → bool). {f(x) | x:A | P(x)} = image(f, {x:A | P(x)})",
		BySets()),
})}

// ---------------------------------------------------------------------------
// What it takes to be a point of an image
// ---------------------------------------------------------------------------
//
// Every law in this chapter is read through one fact — `set_basic.InImage`,
// which says which points an image has. This part draws out what that
// fact costs to use, and in one direction it costs nothing: producing a
// member of an image asks for no search (`FunInImage`). The other
// direction is what makes a quantifier over an image collapse into a
// quantifier over the source set — for one point (`ForallInImage`,
// `ExistsInImage`) or for two at once (`ForallInImagePair`) — so that an
// argument about images never has to name an image point.
// `ImageEqEmpty` is the limiting case: the points of the image answer to
// the points of the source, so one side runs out exactly when the other
// does.

// FunInImage — the half of membership that needs no search. A point of
// the source is its own witness, so landing a point in an image requires
// knowing nothing about the map, and this is the form every later
// argument uses to move into one.
var FunInImage = funInImageThm{family.Add(registry.ProofEntry{
	Name: "FunInImage",
	Key:  "prop_99acec274a51456b",
	Build: family.Theorem(
		Statement{
			Binders: "∀f:(A → B). ∀s:set(A). ∀x:A.",
			Hypotheses: []string{
				"x ∈ s",
			},
			Conclusion: "f(x) ∈ image(f, s)",
		},
		BySets()),
})}

// InRange — membership in the range, the image of the whole source: a
// point lies in it exactly when it is a value of the map. The source
// guard of `set_basic.InImage` is `x ∈ 𝕌`, which asks nothing, so it
// drops out.
var InRange = inRangeThm{family.Add(registry.ProofEntry{
	Name: "InRange",
	Key:  "prop_c8dd92b0b8e588c5",
	Build: family.Theorem(
		"∀f:(A → B). ∀y:B. y ∈ image(f, 𝕌) ⇔ ∃x:A. y = f(x)",
		Chain(Simp(Fwd(set_basic.InImage), Fwd(set_basic.InUniv)), Basic())),
})}

// FunInRange — every value of the map lies in its range: FunInImage at
// the whole source, whose guard is always met.
var FunInRange = funInRangeThm{family.Add(registry.ProofEntry{
	Name: "FunInRange",
	Key:  "prop_162daa6699ec532a",
	Build: family.Theorem(
		"∀f:(A → B). ∀x:A. f(x) ∈ image(f, 𝕌)",
		func(a *Argument, f *Arrow[A, B], x *Expr[A]) {
			a.Show(
				"x is a point of 𝕌, so its value lies in the image of 𝕌",
				By(FunInImage, set_basic.InUniv.At(x)))
		}),
})}

// ForallInImage — universal quantification pulls back along the map. An
// image holds nothing that the source did not send there, so a property
// required throughout it is under exactly the obligation the pulled-back
// property is under on the source — and the image itself is never named.
var ForallInImage = forallInImageThm{family.Add(registry.ProofEntry{
	Name: "ForallInImage",
	Key:  "prop_4dcbebc7610b01f",
	Build: family.Theorem(
		"∀f:(A → B). ∀s:set(A). ∀P:(B → bool). (∀y:B. y ∈ image(f, s) ⇒ P(y)) ⇔ ∀x:A. x ∈ s ⇒ P(f(x))",
		BySets()),
})}

// ImageSubsetIff — an image lies inside a set exactly when the map sends
// every point of the source into it. Inclusion is a universal statement
// over the points of the image, and ForallInImage pulls it back to the
// source.
var ImageSubsetIff = imageSubsetIffThm{family.Add(registry.ProofEntry{
	Name: "ImageSubsetIff",
	Key:  "prop_6515d887efeaaef4",
	Build: family.Theorem(
		"∀f:(A → B). ∀s:set(A). ∀t:set(B). image(f, s) ⊆ t ⇔ ∀x:A. x ∈ s ⇒ f(x) ∈ t",
		Chain(Simp(Fwd(set_basic.SubsetDef), Fwd(ForallInImage)), Basic())),
})}

// ExistsInImage — the same transfer for existence, where the two
// directions use the map opposite ways round: a witness in the source is
// carried forward by it, and a witness in the image is already of the
// form f(x), so it hands its own source back.
var ExistsInImage = existsInImageThm{family.Add(registry.ProofEntry{
	Name: "ExistsInImage",
	Key:  "prop_76e14c311e09cc97",
	Build: family.Theorem(
		"∀f:(A → B). ∀s:set(A). ∀P:(B → bool). (∃y:B. y ∈ image(f, s) ∧ P(y)) ⇔ ∃x:A. x ∈ s ∧ P(f(x))",
		BySets()),
})}

// ForallInImagePair — a property of two image points at once transfers
// no differently, because the two sources may be chosen independently of
// one another. What the map might fail to be — injective — costs nothing
// here: the pulled-back property is asked about every PAIR of sources,
// including the pairs the map identifies.
var ForallInImagePair = forallInImagePairThm{family.Add(registry.ProofEntry{
	Name: "ForallInImagePair",
	Key:  "prop_6df2ea036e4b03cc",
	Build: family.Theorem(
		"∀f:(A → B). ∀P:(B → B → bool). ∀s:set(A). "+
			"    (∀x y:B. x ∈ image(f, s) ∧ y ∈ image(f, s) ⇒ P(x, y)) ⇔ ∀x y:A. x ∈ s ∧ y ∈ s ⇒ P(f(x), f(y))",
		BySets()),
})}

// ForallInImageTriple — three image points at once, for the same reason
// as two: each source is chosen independently of the others. An
// associativity or distributivity law at the points of an image is
// pulled back here to the same law at three points of the source. One
// way the values of three points of s are three image points; the other
// way each image point is the value of a point of s (set_basic.InImage).
var ForallInImageTriple = forallInImageTripleThm{family.Add(registry.ProofEntry{
	Name: "ForallInImageTriple",
	Key:  "prop_27f3097e49beabb",
	Build: family.Theorem(
		"∀f:(A → B). ∀P:(B → B → B → bool). ∀s:set(A). "+
			"    (∀x y z:B. x ∈ image(f, s) ∧ y ∈ image(f, s) ∧ z ∈ image(f, s) ⇒ P(x, y, z)) ⇔ "+
			"    ∀x y z:A. x ∈ s ∧ y ∈ s ∧ z ∈ s ⇒ P(f(x), f(y), f(z))",
		func(a *Argument, f *Arrow[A, B], P *Expr[Fun3[B, B, B, Bool]], s *Expr[Set[A]]) {
			a.Iff()
			a.Forward(
				"the values of three points of s are three image points",
				func(b *Argument, every Fact) {
					x, y, z := b.FixAs[A]("x"), b.FixAs[A]("y"), b.FixAs[A]("z")
					points := b.Conjuncts(
						b.Assume(),
						"x lies in s",
						"y lies in s",
						"z lies in s")
					b.Show(
						"so P holds of f(x), f(y) and f(z)",
						By(
							every.At(f.Apply(x), f.Apply(y), f.Apply(z)),
							FunInImage.At(f, s, x),
							FunInImage.At(f, s, y),
							FunInImage.At(f, s, z),
							points[0],
							points[1],
							points[2]))
				})
			a.Backward(
				"three image points are the values of three points of s",
				func(b *Argument, every Fact) {
					b.FixAs[B]("u")
					b.FixAs[B]("v")
					b.FixAs[B]("w")
					parts := b.Conjuncts(
						b.Assume(),
						"u is an image point",
						"v is an image point",
						"w is an image point")
					_, uIs := b.ObtainAs[A](
						"u is f(x) for some x of s",
						"∃x:A. u = f(x) ∧ x ∈ s",
						By(parts[0], set_basic.InImage))
					_, vIs := b.ObtainAs[A](
						"v is f(y) for some y of s",
						"∃y:A. v = f(y) ∧ y ∈ s",
						By(parts[1], set_basic.InImage))
					_, wIs := b.ObtainAs[A](
						"w is f(z) for some z of s",
						"∃z:A. w = f(z) ∧ z ∈ s",
						By(parts[2], set_basic.InImage))
					uParts := b.Conjuncts(
						uIs,
						"u is f(x)",
						"x lies in s")
					vParts := b.Conjuncts(
						vIs,
						"v is f(y)",
						"y lies in s")
					wParts := b.Conjuncts(
						wIs,
						"w is f(z)",
						"z lies in s")
					b.Show(
						"so P holds of u, v and w, the values of x, y and z",
						uParts[0].Rw(),
						vParts[0].Rw(),
						wParts[0].Rw(),
						By(every, uParts[1], vParts[1], wParts[1]))
				})
		}),
})}

// ImageEqEmpty — a map can neither manufacture a point nor lose the last
// one. Only one direction carries content, and it says no more than
// FunInImage does read backwards: had the source kept a point, the image
// would have kept that point's value.
var ImageEqEmpty = imageEqEmptyThm{family.Add(registry.ProofEntry{
	Name: "ImageEqEmpty",
	Key:  "prop_39b72f6e86e9d413",
	Build: family.Theorem(
		"∀f:(A → B). ∀s:set(A). image(f, s) = ∅ ⇔ s = ∅",
		BySets()),
})}

// ---------------------------------------------------------------------------
// What taking an image does to the set constructions
// ---------------------------------------------------------------------------
//
// A point of an image has at least one source, but need not have only
// one, and that single asymmetry decides everything in this part. A
// source lying in `s ∪ t` lies in `s` or in `t`, so the union side passes
// through exactly. A value lying in both `image(f, s)` and `image(f, t)`
// has a source in each, and nothing makes those two sources the same
// point — so the intersection side yields one inclusion and no more.
//
// What buys back the other inclusion is a hypothesis forcing the two
// sources to coincide, and the last four members each state only as much
// of one as they use: injectivity outright, injectivity on a set holding
// both, injectivity between the two sets, injectivity at the deleted
// point.

// ImageClauses — the two recursion clauses. A map carries nothing out of
// the empty set, and one more point in the source contributes exactly its
// own value; between them they compute the image of any set presented by
// ∅ and insert.
var ImageClauses = imageClausesThm{family.Add(registry.ProofEntry{
	Name: "ImageClauses",
	Key:  "prop_c34df730f50b873a",
	Build: family.Theorem(
		"∀f:(A → B). ∀x:A. ∀s:set(A). image(f, ∅) = ∅ ∧ image(f, insert(x, s)) = insert(f(x), image(f, s))",
		BySets()),
})}

// ImageUnion — union passes through the image exactly. A point of the
// image of a union has a source, and that source lies in one of the two
// sets; read the other way it is the same sentence.
var ImageUnion = imageUnionThm{family.Add(registry.ProofEntry{
	Name: "ImageUnion",
	Key:  "prop_2975a6d36b6af997",
	Build: family.Theorem(
		"∀f:(A → B). ∀s t:set(A). image(f, s ∪ t) = image(f, s) ∪ image(f, t)",
		BySets()),
})}

// ImageInterSubset — intersection does not, and this inclusion is all
// that holds of an arbitrary map. The reverse fails as soon as `f` sends
// some point of `s` and some OTHER point of `t` to a common value: that
// value belongs to both images while nothing in the intersection reaches
// it.
var ImageInterSubset = imageInterSubsetThm{family.Add(registry.ProofEntry{
	Name: "ImageInterSubset",
	Key:  "prop_e50417047261c1cb",
	Build: family.Theorem(
		"∀f:(A → B). ∀s t:set(A). image(f, s ∩ t) ⊆ image(f, s) ∩ image(f, t)",
		BySets()),
})}

// ImageInterInj — injectivity restores the equation ImageInterSubset
// leaves as an inclusion. A value in both images has a source in each; if
// `f` identifies no two points then those sources are one point, and it
// lies in both sets.
var ImageInterInj = imageInterInjThm{family.Add(registry.ProofEntry{
	Name: "ImageInterInj",
	Key:  "prop_e4628c665024aa4a",
	Build: family.Theorem(
		Statement{
			Binders: "∀f:(A → B). ∀s t:set(A).",
			Hypotheses: []string{
				"injective_on(𝕌, f)",
			},
			Conclusion: "image(f, s ∩ t) = image(f, s) ∩ image(f, t)",
		},
		func(a *Argument, f, s, t Term, inj Fact) {
			// Measured, not derived: the close needs the injectivity
			// premise. Having an antecedent is not by itself the reason —
			// ImageDeleteInj below has one and closes bare — so which
			// members need theirs is a fact about the residual each
			// leaves, and only running both settles it. The premise is
			// read at its points, which the set driver does not do for a
			// predicate it does not own.
			a.Do(BySets(a.Unfolded(inj, functions.InjectiveOnDef)))
		}),
})}

// ImageInterInjOn — the same equation under injectivity on a set u holding
// both s and t. A value in both images has a source in s and one in t;
// both lie in u, where f identifies no two points, so they are one point,
// lying in both sets.
var ImageInterInjOn = imageInterInjOnThm{family.Add(registry.ProofEntry{
	Name: "ImageInterInjOn",
	Key:  "prop_64700ce9bd6f0276",
	Build: family.Theorem(
		Statement{
			Binders: "∀f:(A → B). ∀s t u:set(A).",
			Hypotheses: []string{
				"injective_on(u, f)",
				"s ⊆ u",
				"t ⊆ u",
			},
			Conclusion: "image(f, s ∩ t) = image(f, s) ∩ image(f, t)",
		},
		func(a *Argument, f *Arrow[A, B], s, t, u *Expr[Set[A]], given Fact) {
			hypotheses := a.Conjuncts(
				given,
				"f is one-to-one on u",
				"s lies in u",
				"and so does t")
			a.Show(
				"the two sources of a value in both images lie in u, where f identifies no two points",
				BySets(a.Unfolded(hypotheses[0], functions.InjectiveOnDef), hypotheses[1], hypotheses[2]))
		}),
})}

// ImageDiffInj — the same for set difference, under less than
// injectivity. Only a collision between a point of `s` and a point of `t`
// can put a value of the difference back into the image of `t`, so those
// are the only collisions the hypothesis has to rule out.
var ImageDiffInj = imageDiffInjThm{family.Add(registry.ProofEntry{
	Name: "ImageDiffInj",
	Key:  "prop_d7a0ea6b76374bcf",
	Build: family.Theorem(
		Statement{
			Binders: "∀f:(A → B). ∀s t:set(A).",
			Hypotheses: []string{
				"∀x y:A. x ∈ s ∧ y ∈ t ∧ f(x) = f(y) ⇒ x = y",
			},
			Conclusion: "image(f, s ∖ t) = image(f, s) ∖ image(f, t)",
		},
		func(a *Argument, f, s, t Term, noCollision Fact) {
			// Same as ImageInterInj, and measured the same way.
			a.Do(BySets(noCollision))
		}),
})}

// ImageDeleteInj — deleting a point commutes with taking the image when
// that point is the only thing in `s` carrying its value. Otherwise a
// twin carries the value into the image of the smaller set anyway, while
// deleting the value from the whole image removes it, and the two
// constructions part company at exactly that value.
var ImageDeleteInj = imageDeleteInjThm{family.Add(registry.ProofEntry{
	Name: "ImageDeleteInj",
	Key:  "prop_712b50e4a04d1d78",
	Build: family.Theorem(
		Statement{
			Binders: "∀f:(A → B). ∀s:set(A). ∀a:A.",
			Hypotheses: []string{
				"∀x:A. x ∈ s ∧ f(x) = f(a) ⇒ x = a",
			},
			Conclusion: "image(f, delete(s, a)) = delete(image(f, s), f(a))",
		},
		func(a *Argument) {
			// No strips here, though the shape matches the two above — this
			// one closes on the ∀-closed goal. The difference is in the
			// residual, not in the statement.
			a.Do(BySets())
		}),
})}

// ---------------------------------------------------------------------------
// Arbitrary unions and intersections through a map
// ---------------------------------------------------------------------------
//
// The two big operators meet `image` from opposite sides, and the part
// is the two encounters. In the first pair the operator is INSIDE the
// map: `s` is a family of sets over A, collapsed and then carried
// across. In the last three it is OUTSIDE: `f` sends each point of `s`
// to a set of B's, and it is the family so indexed that gets collapsed.
//
// The first pair needs the functor one level up. `image(f)` is itself a
// map — from sets of A's to sets of B's — so `image(image(f), s)` is the
// family `s` carried across member by member. That partial application
// is the content of the two statements, not shorthand for a λ.
//
// There the chapter's standing asymmetry appears. A union survives the
// map as an equation; an intersection survives only one way. The reason
// is the one that recurs wherever this chapter states a ⊆: `f` may send
// points drawn from DIFFERENT members of the family to one value, and
// that value then lies in every image without lying in the image of
// anything the members share.
//
// The last three do not repeat it — `IntersImage` is an equation as
// much as `UnionsImage` is. Nothing is being pushed through the map
// there: the intersection is taken over the family after `f` has
// already produced it, so no two members' points ever have to be told
// apart.

// ImageUnions — pooling a family and mapping the result is mapping each
// member and pooling: a point of either side is `f` of a point lying in
// some member, and nothing else.
var ImageUnions = imageUnionsThm{family.Add(registry.ProofEntry{
	Name: "ImageUnions",
	Key:  "prop_601be82c9eb4164d",
	Build: family.Theorem(
		"∀f:(A → B). ∀s:set(set(A)). image(f, ⋃s) = ⋃image(image(f), s)",
		BySets()),
})}

// ImageIntersSubset — the intersection half, and only an inclusion. A
// value that `f` takes somewhere in every member of the family need not
// be taken at a single point common to all of them.
var ImageIntersSubset = imageIntersSubsetThm{family.Add(registry.ProofEntry{
	Name: "ImageIntersSubset",
	Key:  "prop_57bb6d925868e576",
	Build: family.Theorem(
		"∀f:(A → B). ∀g:set(set(A)). image(f, ⋂g) ⊆ ⋂image(image(f), g)",
		BySets()),
})}

// UnionsImage — an indexed family, joined. Read `f` as assigning a set
// to each index: the join collects a point as soon as ONE index of `s`
// admits it, which is what the comprehension on the right says with no
// big operator at all.
var UnionsImage = unionsImageThm{family.Add(registry.ProofEntry{
	Name: "UnionsImage",
	Key:  "prop_34326198258eddb3",
	Build: family.Theorem(
		"∀f:(A → set(B)). ∀s:set(A). ⋃image(f, s) = {y:B | ∃x:A. x ∈ s ∧ y ∈ f(x)}",
		BySets()),
})}

// IntersImage — the same family met instead of joined: the meet keeps a
// point only when EVERY index of `s` admits it. The pair is the reason
// an indexed family never needs `⋃` or `⋂` to be spelled — either one
// is a quantifier over the index set.
var IntersImage = intersImageThm{family.Add(registry.ProofEntry{
	Name: "IntersImage",
	Key:  "prop_4deb35a36eb2716c",
	Build: family.Theorem(
		"∀f:(A → set(B)). ∀s:set(A). ⋂image(f, s) = {y:B | ∀x:A. x ∈ s ⇒ y ∈ f(x)}",
		func(a *Argument, f, s Term) {
			// The bound binders are the ⋃/⋂ difference showing up in the
			// closer, not a size problem. Membership in a join unfolds to
			// an ∃ over a conjunction, which the driver's one-point rule
			// fuses away on the spot — that is why `UnionsImage` just above
			// needs nothing. Membership in a meet unfolds to a ∀ over an
			// implication, which fuses nothing, so the residual keeps
			// whatever the outer binders leave standing unless they are
			// gone first.
			a.Do(BySets())
		}),
})}

// UnionsImageMonotone — joining is monotone in the family. Dominating
// `f` pointwise on `s` is already enough: no point of the join has more
// than one index behind it, so widening the sets one index at a time
// widens the join.
var UnionsImageMonotone = unionsImageMonotoneThm{family.Add(registry.ProofEntry{
	Name: "UnionsImageMonotone",
	Key:  "prop_9248279bcf97264d",
	Build: family.Theorem(
		Statement{
			Binders: "∀f g:(A → set(B)). ∀s:set(A).",
			Hypotheses: []string{
				"∀x:A. x ∈ s ⇒ f(x) ⊆ g(x)",
			},
			Conclusion: "⋃image(f, s) ⊆ ⋃image(g, s)",
		},
		BySets()),
})}

// ---------------------------------------------------------------------------
// The image as a statement about the map
// ---------------------------------------------------------------------------
//
// Every earlier part says what `image(f, ·)` does to sets. Here the
// reading is turned around. `image(f, ·)` is itself a map — from sets of
// A's to sets of B's — and each member says that a property of that map
// is exactly the same property of `f`. Surjective sets-to-sets means
// surjective points-to-points, and injective means injective. Nothing
// about `image` is stated that is not already a fact about `f`.
//
// Going from the SET side to the POINT side, all one has is a law about
// arbitrary sets, so one applies it to the smallest sets there are: the
// one-point sets `{x}`, whose image is `{f(x)}`. That move carries every
// characterization here in that direction.
//
// The other direction is not uniform, and the difference is worth
// noticing. For surjectivity a set has to be PRODUCED, and it is always
// the preimage — the points whose values land where they are wanted. For
// injectivity nothing has to be produced at all: the hypothesis already
// speaks about two arbitrary sets, so once its binders are stripped and
// its antecedent is resident the closer has everything, and the branch is
// the strips and nothing else.
//
// `SurjectiveOnImage` and `InjectiveOnImage` are the relative forms, in
// which both sides are confined to a set `u` of sources. They are the
// forms an argument about a map defined on part of its type actually
// needs, and they are proved by the same two moves, since a one-point
// set `{x}` sits inside `u` exactly when `x` is a point of `u`.
//
// `SurjectiveImageEq` opens the part because it is the criterion the
// surjectivity members are read through: a set IS the image of another
// as soon as membership matches pointwise. `SurjectiveImageThm` follows
// it as the same characterization `SurjectiveImage` gives, said with
// comprehensions in place of arbitrary sets. `BijectionRestricts` closes
// the part: a bijection of s onto t restricts to one of u onto v when a
// point lies in u exactly as its image lies in v.
//
// On mechanics, the chapter's default is one `BySets()` and the two
// opening members keep it; the four characterizations spell a case body
// per direction. Each body is what its Case label names, surrounded by
// the prefix work that puts it in front of the closer, since a
// hypothesis does not count as one until it is stripped and a law under
// ∀ says nothing until it is applied.

// SurjectiveImageEq — when a set is the image of another. Membership in
// `t` has to be reachable from `s` at all, and `f` has to send exactly
// the points of `s` into `t`; together those two say that `t` and
// `image(f, s)` have the same points, which for sets is being equal.
var SurjectiveImageEq = surjectiveImageEqThm{family.Add(registry.ProofEntry{
	Name: "SurjectiveImageEq",
	Key:  "prop_47e5da157854385e",
	Build: family.Theorem(
		Statement{
			Binders: "∀f:(A → B). ∀s:set(A). ∀t:set(B).",
			Hypotheses: []string{
				"∀y:B. y ∈ t ⇒ ∃x:A. f(x) = y",
				"∀x:A. f(x) ∈ t ⇔ x ∈ s",
			},
			Conclusion: "image(f, s) = t",
		},
		BySets()),
})}

// SurjectiveImageThm — surjectivity as a statement about comprehensions.
// If every B is a value of `f` then a property of B's can be pulled back
// along `f`, collected, and pushed forward again without loss; and if
// the two comprehensions always agree then taking P to be "is a value of
// f" says every B is one. The `x` on the two sides of the equation is
// bound at DIFFERENT types — A on the left, B on the right — which is
// what "pulled back along f" means here.
var SurjectiveImageThm = surjectiveImageThmThm{family.Add(registry.ProofEntry{
	Name: "SurjectiveImageThm",
	Key:  "prop_ae35767151b28a3e",
	Build: family.Theorem(
		"∀f:(A → B). (∀y:B. ∃x:A. f(x) = y) ⇔ ∀P:(B → bool). image(f, {x:A | P(f(x))}) = {x:B | P(x)}",
		BySets()),
})}

// SurjectiveImage — `f` is surjective exactly when `image(f, ·)` is.
// Every set of B's being an image is the same demand as every point of B
// being a value: a point is recovered from the one-point set it forms,
// and a set is assembled from the points it holds. This is
// SurjectiveOnImage with no restriction on the sources, and it is proved
// by the same two moves in the same two places.
var SurjectiveImage = surjectiveImageThm{family.Add(registry.ProofEntry{
	Name: "SurjectiveImage",
	Key:  "prop_bdd00f288b45a6fe",
	Build: family.Theorem(
		"∀f:(A → B). (∀t:set(B). ∃s:set(A). image(f, s) = t) ⇔ ∀y:B. ∃x:A. f(x) = y",
		func(a *Argument, f Term) {
			a.Iff()
			a.Forward(
				"the one-point set {y} is an image, and any source for it is a source for y",
				func(a *Argument, everySetIsAnImage Fact) {
					a.Fix() // y — the instance text spells it by name
					a.Do(BySets(everySetIsAnImage, everySetIsAnImage.At(a.Term("{y}"))))
				})
			a.Backward(
				"the preimage of t is a set whose image is t — pointwise surjectivity is what makes it ALL of t",
				func(a *Argument, pointwise Fact) { // pointwise: ∀y. ∃x. f₀(x) = y
					a.Fix() // t — the witness text spells it by name
					a.Take(a.Term("preimage_on(𝕌, f, t)"))
					a.Do(BySets(pointwise))
				})
		}),
})}

// SurjectiveOnImage — the relative form of SurjectiveImage: `f` carries
// `u` onto `v` exactly when every part of `v` is the image of a part of
// `u`. Both moves of the part appear here, one per direction, and each
// direction is one of them and then nothing.
//
// It is also `SubsetImage` below read one level up: that law
// rewrites this member's set-side arm to `∀t. t ⊆ v ⇒ t ⊆ image(f, u)`,
// which is `v ⊆ image(f, u)` — the point-side arm unfolded. The proof
// below does not go that way, because the driver settles each side
// directly, but the two statements are one fact.
var SurjectiveOnImage = surjectiveOnImageThm{family.Add(registry.ProofEntry{
	Name: "SurjectiveOnImage",
	Key:  "prop_34e5ca56e99f4854",
	Build: family.Theorem(
		"∀f:(A → B). ∀u:set(A). ∀v:set(B). "+
			"    (∀t:set(B). t ⊆ v ⇒ ∃s:set(A). s ⊆ u ∧ image(f, s) = t) ⇔ "+
			"    ∀y:B. y ∈ v ⇒ ∃x:A. x ∈ u ∧ f(x) = y",
		func(a *Argument, f, u, v Term) {
			// `f` and `u` are named below, in the set the ⇐ direction
			// exhibits; `v` is bound because the ⇔ stands under it.
			a.Iff()
			a.Forward(
				"the one-point set {y} is a part of v, so it is the image of "+
					"a part of u — and every point of that part is a source for y",
				func(a *Argument, partsOfVAreImages Fact) {
					a.Fix()           // y — the instance text spells it by name
					inV := a.Assume() // y ∈ v₀
					a.Do(BySets(partsOfVAreImages, partsOfVAreImages.At(a.Term("{y}")), inV))
				})
			a.Backward(
				"the part of u that f sends into t is a part of u whose image "+
					"is t — pointwise surjectivity onto v is what makes it ALL of t",
				func(a *Argument, pointwise Fact) { // pointwise: ∀y. y ∈ v₀ ⇒ ∃x. x ∈ u₀ ∧ f₀(x) = y
					a.Fix()               // t — the witness text spells it by name
					insideV := a.Assume() // t ⊆ v₀
					a.Take(a.Term("preimage_on(u, f, t)"))
					a.Do(BySets(pointwise, insideV))
				})
		}),
})}

// InjectiveImage — `f` is injective exactly when `image(f, ·)` is. One
// direction is the reason images of intersections misbehave for general
// maps (the constructions part above): distinct sets with a common image are exactly
// a pair of points `f` fails to tell apart.
var InjectiveImage = injectiveImageThm{family.Add(registry.ProofEntry{
	Name: "InjectiveImage",
	Key:  "prop_d161cbd8979e9591",
	Build: family.Theorem(
		"∀f:(A → B). (∀s t:set(A). image(f, s) = image(f, t) ⇒ s = t) ⇔ injective_on(𝕌, f)",
		func(a *Argument, f Term) {
			a.Iff()
			a.Forward(
				"run the set law on the one-point sets {x} and {y}: their "+
					"images are {f(x)} and {f(y)}, so {x} = {y}, so x = y",
				func(a *Argument, setsWithCommonImageAgree Fact) {
					a.Do(Simp(Fwd(functions.InjectiveOnDef))) // injectivity read at its points
					a.Fix()                                   // x — the instance texts spell both by name
					a.Fix()                                   // y
					valuesAgree := a.Assume()                 // x₀ ∈ 𝕌 ∧ y₀ ∈ 𝕌 ∧ f₀(x₀) = f₀(y₀)
					// The instance is what the close uses; the ∀-law
					// stays behind rather than reaching the refuter,
					// which By's clear-first guarantees. Here that is
					// hygiene — the leaf closes either way — but
					// InjectiveOnImage, whose leaf is this one with u in
					// it, does not close until the law is gone.
					a.Do(BySets(setsWithCommonImageAgree.At(a.Term("{x}"), a.Term("{y}")), valuesAgree))
				})
			a.Backward(
				"two sets with a common image agree pointwise: a point of s is "+
					"the image of a point of t, and injectivity makes them one point",
				func(a *Argument, injective Fact) {
					// The driver declines while `s`, `t` and the image
					// equation are still under a quantifier and an arrow —
					// the ImageInterInj phenomenon above —
					// so take them apart and hand both facts to the close.
					a.Fix()                   // s
					a.Fix()                   // t
					imagesAgree := a.Assume() // image(f₀, s₀) = image(f₀, t₀)
					a.Do(BySets(a.Unfolded(injective, functions.InjectiveOnDef), imagesAgree))
				})
		}),
})}

// InjectiveOnImage — the relative form of InjectiveImage: `f` is
// injective on `u` exactly when `image(f, ·)` is injective on the parts
// of `u`. The one-point sets carry the argument across again, since
// `{x} ⊆ u` says exactly that `x` is a point of `u`.
var InjectiveOnImage = injectiveOnImageThm{family.Add(registry.ProofEntry{
	Name: "InjectiveOnImage",
	Key:  "prop_5cb6438418f803ad",
	Build: family.Theorem(
		"∀f:(A → B). ∀u:set(A). "+
			"    (∀s t. s ⊆ u ∧ t ⊆ u ∧ image(f, s) = image(f, t) ⇒ s = t) ⇔ injective_on(u, f)",
		func(a *Argument, f, u Term) {
			a.Iff()
			a.Forward(
				"run the set law on {x} and {y}: each is a part of u because x "+
					"and y are points of u, and their images agree because f(x) = f(y)",
				func(a *Argument, partsOfUWithCommonImageAgree Fact) {
					a.Do(Simp(Fwd(functions.InjectiveOnDef))) // injectivity on u read at its points
					a.Fix()                                   // x — the instance texts spell both by name
					a.Fix()                                   // y
					agree := a.Assume()                       // x₀ ∈ u₀ ∧ y₀ ∈ u₀ ∧ f₀(x₀) = f₀(y₀)
					// The instance, not the ∀-law: with the law still
					// resident the residual does not refute, and By's
					// clear-first keeps exactly what is listed.
					a.Do(BySets(partsOfUWithCommonImageAgree.At(a.Term("{x}"), a.Term("{y}")), agree))
				})
			a.Backward(
				// Same reason as InjectiveImage's ⇐ branch.
				"parts of u with a common image agree pointwise: a point of s is the "+
					"image of a point of t, both in u, so injectivity on u makes them one",
				func(a *Argument, injectiveOnU Fact) {
					a.Fix()              // s
					a.Fix()              // t
					bounds := a.Assume() // s₀ ⊆ u₀ ∧ t₀ ⊆ u₀ ∧ image(f₀, s₀) = image(f₀, t₀)
					a.Do(BySets(a.Unfolded(injectiveOnU, functions.InjectiveOnDef), bounds))
				})
		}),
})}

// BijectionRestricts — a bijection of s onto t restricts to a bijection of u onto
// v when a point of s lies in u exactly as its image lies in v: every point of v
// comes from a point of s, which lies in u, and the points of u go into v.
var BijectionRestricts = bijectionRestrictsThm{family.Add(registry.ProofEntry{
	Name: "BijectionRestricts",
	Key:  "prop_27e90b5b5660f9ba",
	Build: family.Theorem(Statement{
		Binders: "∀f:(A → B). ∀s u:set(A). ∀t v:set(B).",
		Hypotheses: []string{
			"injective_on(s, f)",
			"image(f, s) = t",
			"u ⊆ s",
			"v ⊆ t",
			"∀x:A. x ∈ s ⇒ (x ∈ u ⇔ f(x) ∈ v)",
		},
		Conclusion: "injective_on(u, f) ∧ image(f, u) = v",
	}, func(
		a *Argument,
		f *Arrow[A, B],
		s, u *Expr[Set[A]],
		t, v *Expr[Set[B]],
		injective, onto, uInS, vInT, matches Fact,
	) {
		preimages := a.Have(
			"every point of v is the image of a point of u",
			"∀y:B. y ∈ v ⇒ ∃x:A. x ∈ u ∧ f(x) = y",
			BySets(onto, vInT, matches))
		into := a.Have(
			"the image of u lies in v",
			"image(f, u) ⊆ v",
			BySets(uInS, matches))
		covered := a.Have(
			"and holds v",
			"v ⊆ image(f, u)",
			BySets(preimages))
		a.Show(
			"f is injective on u, which lies in s, and the two inclusions make the image v",
			By(
				injective,
				uInS,
				into,
				covered,
				functions.InjectiveOnSubset.At(f, u, s),
				set_order.SubsetAntisym.At(a.TermAs[Set[B]]("image(f, u)"), v)))
	}),
})}

// ---------------------------------------------------------------------------
// Inclusion and the image
// ---------------------------------------------------------------------------
//
// The rest of the chapter asks what image does to a set. This part asks
// what it does to the ORDERING, and its four members answer in one
// direction each.
//
// `ImageSubset` is the easy half: a larger source has a larger image,
// because a point's source does not stop being a source when the set
// around it grows. Nothing about the map is needed, and the driver
// settles it. `ImageCongruence` is the same unfolding at one source and
// two maps that agree on it.
//
// The last two run the other way, and their proofs, like those of the
// surjectivity members above, must EXHIBIT a set rather than unfold
// one. Lying inside `image(f, t)` is the same as BEING the image of a
// piece of `t`, and there is a canonical piece to offer: the part of
// `t` that `f` sends into `s`, which is the largest piece that could
// work. That is `SubsetImage`. `SubsetImageInj` asks for a piece `f`
// does not fold, and the largest one is the wrong answer — it folds the
// moment two of its points share a value. So ONE source is picked per
// point of `s` instead, and the piece is the set of picked sources.
// Picking is where the part leaves the driver behind and cites the
// choice of a section.

// ImageSubset — taking images is monotone. A point of `image(f, s)` has
// a source in `s`, and that source lies in `t` as soon as `s` does.
var ImageSubset = imageSubsetThm{family.Add(registry.ProofEntry{
	Name: "ImageSubset",
	Key:  "prop_6bc34489a0f27568",
	Build: family.Theorem(
		Statement{
			Binders: "∀f:(A → B). ∀s t:set(A).",
			Hypotheses: []string{
				"s ⊆ t",
			},
			Conclusion: "image(f, s) ⊆ image(f, t)",
		},
		BySets()),
})}

// ImageCongruence — two maps that agree on s have one image of s: a value
// of the one at a point of s is the value of the other there.
var ImageCongruence = imageCongruenceThm{family.Add(registry.ProofEntry{
	Name: "ImageCongruence",
	Key:  "prop_5a779fa6ed6f9cae",
	Build: family.Theorem(
		Statement{
			Binders: "∀f g:(A → B). ∀s:set(A).",
			Hypotheses: []string{
				"∀x:A. x ∈ s ⇒ f(x) = g(x)",
			},
			Conclusion: "image(f, s) = image(g, s)",
		},
		BySets()),
})}

// SubsetImage — a subset of an image is an image of a subset. One
// direction is monotonicity; the other has to produce the subset. Any
// `u ⊆ t` with `image(f, u) = s` holds nothing outside the part of `t`
// that `f` sends into `s`, so that part is the largest candidate — and
// it covers `s` exactly when `s ⊆ image(f, t)`, which is the
// hypothesis. So the largest candidate is a candidate.
//
// This is the law `SurjectiveOnImage` is the relativized reading of
// (above): substituting the ∃ below into that member's set-side
// arm turns it into `∀t. t ⊆ v ⇒ t ⊆ image(f, u)`, which is
// `v ⊆ image(f, u)` — its point-side arm unfolded. The two members are
// proved independently, since the driver reaches each on its own.
var SubsetImage = subsetImageThm{family.Add(registry.ProofEntry{
	Name: "SubsetImage",
	Key:  "prop_3ac83b3660937ca8",
	Build: family.Theorem(
		"∀f:(A → B). ∀s:set(B). ∀t:set(A). s ⊆ image(f, t) ⇔ ∃u. u ⊆ t ∧ s = image(f, u)",
		func(a *Argument, f, s, t Term) {
			// The largest candidate: the part of t that f sends into s —
			// any other `u ⊆ t` with `image(f, u) = s` is contained in it.
			candidate := a.Term("preimage_on(t, f, s)")

			a.Iff()
			// The driver reaches this without ImageSubset above.
			a.Forward(
				"offer the largest candidate: the part of t that f sends into s",
				func(a *Argument, covered Fact) { // covered: s₀ ⊆ image(f₀, t₀)
					a.Take(candidate)
					a.Do(SplitConj(
						Case(
							"that part is carved out of t, so it lies in t",
							BySets()),
						Case(
							"and f carries it exactly onto s: it holds only sources "+
								"of s-points, and the covering supplies one per point",
							BySets(covered)),
					))
				})
			a.Backward(
				"s is the image of some u inside t, and a larger source has a larger image",
				func(a *Argument, imaged Fact) { // imaged: ∃u. u ⊆ t₀ ∧ s₀ = image(f₀, u)
					a.Do(BySets(imaged))
				})
		}),
})}

// SubsetImageInj — the subset can moreover be chosen so that `f` is
// injective on it. `SubsetImage`'s witness will not do: the full
// preimage folds as soon as two of its points share a value. Choosing
// one source `g(x)` per point `x` of `s` gives a set that cannot fold,
// because `f` sends `g(x)` back to `x` and so tells its points apart by
// name.
//
// Choice enters once, in the `rightInverse` section below: a covering
// of s by the image of t is a section g on s, which the set driver
// finds from the covering alone.
var SubsetImageInj = subsetImageInjThm{family.Add(registry.ProofEntry{
	Name: "SubsetImageInj",
	Key:  "prop_ea9992b6edd47398",
	Build: family.Sections(
		"∀f:(A → B). ∀s:set(B). ∀t:set(A). "+
			"    s ⊆ image(f, t) ⇔ ∃u. u ⊆ t ∧ s = image(f, u) ∧ injective_on(u, f)",
		func(ctx *Script, headline string) *GoalStackNode {
			// Containment in an image says of each point of s separately that
			// it has a source in t; this section says it once, of a function.
			// The exchange is choice, and the cited row is the form of it
			// stated for a map onto a set — the only thing between the two
			// phrasings is the unfolding of image.
			rightInverse := ctx.Lemma(
				Statement{
					Binders: "∀f:(A → B). ∀s:set(B). ∀t:set(A).",
					Hypotheses: []string{
						"s ⊆ image(f, t)",
					},
					Conclusion: "∃g:(B → A). ∀x:B. x ∈ s ⇒ g(x) ∈ t ∧ f(g(x)) = x",
				},
				func(a *Argument, f, s, t Term, covered Fact) {
					a.Show(
						"f maps t onto s, so it has a section on s",
						BySets(covered))
				})

			return ctx.Theorem(headline, func(a *Argument, f, s, t Term) {
				a.Iff()
				a.Forward(
					"pick one source per point of s, and take u to be the set of picked sources",
					func(a *Argument, sCoveredByImageOfT Fact) {
						// Obtain mints g₀ into the parse scope, which is
						// what the witness term below is read against.
						_, picked := a.Obtain(
							"pick a source g(x) ∈ t for each x ∈ s, one that f sends back to x",
							"∃g:(B → A). ∀x:B. x ∈ s₀ ⇒ g(x) ∈ t₀ ∧ f₀(g(x)) = x",
							By(sCoveredByImageOfT, At(rightInverse, f, s, t)))

						// Wanted at (B → A), the reverse of the instance the
						// statements use — so no shared helper fits and the
						// term is written here.
						a.Take(a.Ctx().TermText("image(g₀, s₀)"))
						a.Do(SplitConjAll(
							Case(
								"the picked sources lie in t, each having been picked there",
								BySets(picked)),
							Case(
								"f carries them exactly onto s, since f sends each picked source back to its own point",
								BySets(picked)),
							Case(
								"and f cannot fold them: a picked source is carried to the point it was picked for",
								Simp(Fwd(functions.InjectiveOnDef)),
								BySets(picked)),
						))
					})
				a.Backward(
					"s is the image of some u inside t; injectivity is not needed for this half",
					func(a *Argument, imaged Fact) { // imaged: ∃u. u ⊆ t₀ ∧ s₀ = image(f₀, u) ∧ …
						a.Do(BySets(imaged))
					})
			})
		}),
})}

// ---------------------------------------------------------------------------
// The preimage as a statement about the map
// ---------------------------------------------------------------------------
//
// `image(f, ·)` is one map `f` induces on subsets; pulling back,
// `t ↦ preimage_on(s, f, t)`, is the other, and it runs backwards. Asked
// the questions the map-side part asks of `image(f, ·)`, it answers with
// the variance turned over. Pulling back is INJECTIVE exactly when `f` is
// SURJECTIVE (distinct test sets stay distinct only if `f` reaches every
// point that could tell them apart), and SURJECTIVE exactly when `f` is
// INJECTIVE (every subset of the source is a preimage only if `f` never
// folds two points together): what the induced map gains is what `f`
// gives up.
//
// Each law is stated twice, relativized to a source set `s` and a
// target set `u` and then unrestricted, and the unrestricted member is
// the relativized one read at `𝕌`.
//
// The relativized statements are where the work is. Both are proved by
// splitting the `⇔`, and in both the interesting direction turns on a
// single well-chosen set: separation is tested by one pair of subsets of
// `u`, and every subset of `s` is recovered as a preimage of its own
// image.

// --- The sets these proofs build --------------------------------------
//
// Four sets are WITNESSES here. The relativized injectivity law is asked
// of arbitrary subsets of `u` and only ever used at one pair of them,
// `{y}` against `∅`; the relativized surjectivity law needs the image of
// a set to answer with; and the two unrestricted members read their
// relativized siblings at `𝕌`, which they need on both sides of the map
// at once. `{y}` and the image are text, read through the vocabulary as
// the earlier parts' witnesses are.
//
// `∅` and `𝕌` are taken from the domain table, and at a type asked for
// (`setvocab.PinnedAt`): the map's source and its target are different
// types and both are in play, so the one instance `setvocab.Pinned`
// would give is not enough.
var (
	elemSource = ext.HolTypeOf[A]() // the map's source
	elemTarget = ext.HolTypeOf[B]() // and its target
)

// emptyTarget is `∅` among the subsets of the map's target: what `{y}`
// is measured against.
func emptyTarget(a *Argument) *Expr[Set[B]] {
	return ext.As[Set[B]](setvocab.PinnedAt(a.Ctx(), "empty_set", elemTarget))
}

// univSource and univTarget are `𝕌` on each side of the map — the
// restrictions that restrict nothing, one for the source set and one for
// the target set.
func univSource(a *Argument) *Expr[Set[A]] {
	return ext.As[Set[A]](setvocab.PinnedAt(a.Ctx(), "universe", elemSource))
}

func univTarget(a *Argument) *Expr[Set[B]] {
	return ext.As[Set[B]](setvocab.PinnedAt(a.Ctx(), "universe", elemTarget))
}

// InjectiveOnPreimage — pulling subsets of `u` back into `s` keeps them
// apart exactly when `s` already covers `u`. A point of `u` that `f`
// misses on `s` is invisible to preimages, and one such point is enough
// to collapse a test set onto a smaller one.
//
// The two directions are proved through two auxiliary statements rather
// than against the headline's arms directly, because each is the honest
// content of its direction and neither mentions the other: the covering
// as an inclusion, and the covering point by point.
var InjectiveOnPreimage = injectiveOnPreimageThm{family.Add(registry.ProofEntry{
	Name: "InjectiveOnPreimage",
	Key:  "prop_45a6acc627458881",
	Build: family.Sections(
		"∀f:(A → B). ∀s:set(A). ∀u:set(B). "+
			"    (∀t t':set(B). t ⊆ u ∧ t' ⊆ u ∧ preimage_on(s, f, t) = preimage_on(s, f, t') ⇒ t = t') ⇔ "+
			"    u ⊆ image(f, s)",
		func(ctx *Script, headline string) *GoalStackNode {
			// The easy half, in the direction the covering is given. Two
			// subsets of `u` that differ do so at some point of `u`; that
			// point is `f(x)` for an `x` of `s`, and `x` then lies in one
			// preimage and not the other.
			separates := ctx.Lemma(
				"∀f:(A → B). ∀s:set(A). ∀u:set(B). "+
					"    u ⊆ image(f, s) ⇒ "+
					"    ∀t t':set(B). t ⊆ u ∧ t' ⊆ u ∧ preimage_on(s, f, t) = preimage_on(s, f, t') ⇒ t = t'",
				BySets())

			// What the covering AMOUNTS to, point by point: `u ⊆ image(f, s)`
			// says of each `y` in `u` that some `x` of `s` is carried to it.
			// The other half of the proof produces exactly that, one `y` at a
			// time, and this section is what turns it back into an inclusion.
			covers := ctx.Lemma(
				Statement{
					Binders: "∀f:(A → B). ∀s:set(A). ∀u:set(B).",
					Hypotheses: []string{
						"∀y:B. y ∈ u ⇒ ∃x:A. x ∈ s ∧ f(x) = y",
					},
					Conclusion: "u ⊆ image(f, s)",
				},
				BySets())

			return ctx.Theorem(headline, func(a *Argument, f *Arrow[A, B], s *Expr[Set[A]], u *Expr[Set[B]]) {
				a.Iff()
				a.Forward(
					"separation forces the covering, and {y} against ∅ is the only test it takes",
					func(a *Argument, separated Fact) {
						reached := a.Have(
							"each point of u is a value of f on s",
							"∀y:B. y ∈ u₀ ⇒ (∃x:A. x ∈ s₀ ∧ f₀(x) = y)",
							Derive(func(a *Argument) {
								a.FixAs[B]() // y — the instance text spells it by name
								// If no point of `s` were carried to `y`,
								// the two would pull back to the same
								// subset of `s` and separation would
								// equate them — but `y` is in one and in
								// nothing.
								a.Show(
									"separation at the pair ({y}, ∅)",
									BySets(separated, separated.At(a.TermAs[Set[B]]("{y}"), emptyTarget(a))))
							}))

						a.Show(
							"which is the covering",
							By(reached, covers))
					})
				a.Backward(
					"a covered u is separated by its preimages",
					func(a *Argument, covered Fact) {
						a.Show(
							"the covering is all this direction needs",
							By(covered, At(separates, f, s, u)))
					})
			})
		}),
})}

// SurjectiveOnPreimage — every subset of `s` is a preimage of some
// subset of `u` exactly when `f` carries `s` into `u` and separates the
// points of `s`. The subset that is hard to hit is `k` itself: the only
// candidate `t` is the image of `k`, and `f` must neither send it out of
// `u` nor pull anything back into it from outside `k`.
var SurjectiveOnPreimage = surjectiveOnPreimageThm{family.Add(registry.ProofEntry{
	Name: "SurjectiveOnPreimage",
	Key:  "prop_509c62419e472922",
	Build: family.Sections(
		"∀f:(A → B). ∀s:set(A). ∀u:set(B). "+
			"    (∀k:set(A). k ⊆ s ⇒ ∃t:set(B). t ⊆ u ∧ preimage_on(s, f, t) = k) ⇔ "+
			"    image(f, s) ⊆ u ∧ injective_on(s, f)",
		func(ctx *Script, headline string) *GoalStackNode {
			// The candidate, and why the two conditions are exactly what it
			// needs. `image(f, k)` is a legal choice of `t` because `k` lies
			// in `s` and `f` carries `s` into `u`; and it pulls back to `k`
			// on the nose because separation stops any point of `s` outside
			// `k` from sharing a value with one inside it.
			//
			// All three sections here BIND their premise: `BySets()` unfolds
			// a member's hypotheses alongside its goal, so a premise left
			// standing inside the statement is not yet where it looks. The
			// typed parameters ahead of it are bound to REACH the premise —
			// the closure signature consumes the statement's slots left to
			// right — and no body here names them.
			imageRecovers := ctx.Lemma(
				Statement{
					Binders: "∀f:(A → B). ∀s:set(A). ∀u:set(B). ∀k:set(A).",
					Hypotheses: []string{
						"k ⊆ s",
						"image(f, s) ⊆ u",
						"injective_on(s, f)",
					},
					Conclusion: "image(f, k) ⊆ u ∧ preimage_on(s, f, image(f, k)) = k",
				},
				func(a *Argument, f *Arrow[A, B], s *Expr[Set[A]], u *Expr[Set[B]], k *Expr[Set[A]], pulled Fact) {
					a.Do(BySets(a.Unfolded(pulled, functions.InjectiveOnDef)))
				})

			// Read at `k := s`: the whole of `s` is some `t` pulled back, and
			// a preimage taken inside `s` cannot reach past `t`, so every
			// value `f` takes on `s` already lies in `u`.
			imageInside := ctx.Lemma(
				Statement{
					Binders: "∀f:(A → B). ∀s:set(A). ∀u:set(B).",
					Hypotheses: []string{
						"∀k:set(A). k ⊆ s ⇒ ∃t:set(B). t ⊆ u ∧ preimage_on(s, f, t) = k",
					},
					Conclusion: "image(f, s) ⊆ u",
				},
				func(a *Argument, f *Arrow[A, B], s *Expr[Set[A]], u *Expr[Set[B]], pulled Fact) {
					a.Do(BySets(pulled))
				})

			// Read at a one-point `k`: a preimage cannot tell two points of
			// `s` apart if `f` gives them the same value, so no one-point
			// subset of `s` would be a preimage at all if `f` folded.
			noFolding := ctx.Lemma(
				Statement{
					Binders: "∀f:(A → B). ∀s:set(A). ∀u:set(B).",
					Hypotheses: []string{
						"∀k:set(A). k ⊆ s ⇒ ∃t:set(B). t ⊆ u ∧ preimage_on(s, f, t) = k",
					},
					Conclusion: "injective_on(s, f)",
				},
				func(a *Argument, f *Arrow[A, B], s *Expr[Set[A]], u *Expr[Set[B]], pulled Fact) {
					a.Do(Simp(Fwd(functions.InjectiveOnDef)), BySets(pulled))
				})

			return ctx.Theorem(headline, func(a *Argument, f *Arrow[A, B], s *Expr[Set[A]], u *Expr[Set[B]]) {
				a.Iff()
				a.Forward(
					"both conditions are instances of the hypothesis",
					func(a *Argument, everySubsetIsAPreimage Fact) {
						a.Do(SplitConj(
							Case(
								"at k := s, which bounds f's values on s by u",
								By(everySubsetIsAPreimage, At(imageInside, f, s, u))),
							Case(
								"at a one-point k, which leaves f nothing to fold",
								By(everySubsetIsAPreimage, At(noFolding, f, s, u))),
						))
					})
				a.Backward(
					"the image of k is the subset of u that pulls back to it",
					func(a *Argument, carriedAndSeparating Fact) {
						a.FixAs[Set[A]]() // k — the witness text below spells it by name
						kInS := a.Assume()
						// The image of k — everything f reaches from it, and
						// the only candidate for a subset of the target that
						// pulls back to k.
						a.Take(a.TermAs[Set[B]]("image(f₀, k₀)"))
						a.Show(
							"and both halves of that are what the two conditions buy",
							By(kInS, carriedAndSeparating, imageRecovers))
					})
			})
		}),
})}

// InjectivePreimage — pulling back keeps ALL subsets of the target apart
// exactly when `f` is onto. The relativized law read on both sides at
// `𝕌`, where the guards constrain nothing — `set_order.SubsetUniv` for
// the two inclusions in `𝕌` — and where `set_order.UnivSubset` does
// something else: it turns the relativized conclusion `𝕌 ⊆ image(f, 𝕌)`
// into the equation this statement asserts.
var InjectivePreimage = injectivePreimageThm{family.Add(registry.ProofEntry{
	Name: "InjectivePreimage",
	Key:  "prop_100f2a5d2ab1f070",
	Build: family.Theorem(
		"∀f:(A → B). "+
			"    (∀t t':set(B). preimage_on(𝕌, f, t) = preimage_on(𝕌, f, t') ⇒ t = t') ⇔ image(f, 𝕌) = 𝕌",
		func(a *Argument, f *Arrow[A, B]) {
			a.Show(
				"the relativized law at s := 𝕌 and u := 𝕌, its guards "+
					"discharged and its inclusion read as an equation",
				By(
					Normalized,
					InjectiveOnPreimage.At(f, univSource(a), univTarget(a)),
					set_order.SubsetUniv,
					set_order.UnivSubset))
		}),
})}

// SurjectivePreimage — every subset of the source is a preimage exactly
// when `f` separates points. The relativized law at `𝕌` again, and here
// one of the two conditions on the right goes with the guards: carrying
// the source into `𝕌` asks nothing of a map, so separation is all that
// survives.
//
// This one names no `𝕌` law where the member above names two, and the
// difference is the closer rather than the statement. `BySets()` unfolds
// `𝕌` on its way to closing, so the guards dissolve without being cited;
// a `By` ends in a refutation, which does no unfolding, and there the
// laws have to be handed over.
var SurjectivePreimage = surjectivePreimageThm{family.Add(registry.ProofEntry{
	Name: "SurjectivePreimage",
	Key:  "prop_ced39fd3c184ced0",
	Build: family.Theorem(
		"∀f:(A → B). (∀k:set(A). ∃t:set(B). preimage_on(𝕌, f, t) = k) ⇔ injective_on(𝕌, f)",
		func(a *Argument, f *Arrow[A, B]) {
			// The instance is the whole premise list: the goal still wants
			// the set driver's unfolding pass, which a refutation-ending By
			// does not perform — and that pass reaches the recorded leaf
			// from the canonical form the typed cite serves.
			a.Show(
				"the relativized law at s := 𝕌 and u := 𝕌, whose guards are inclusions in 𝕌",
				BySets(SurjectiveOnPreimage.At(f, univSource(a), univTarget(a))))
		}),
})}
