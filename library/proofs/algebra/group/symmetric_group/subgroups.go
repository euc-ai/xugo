// subgroups.go — the symmetric group on a set, as a subgroup of the
// permutations of the whole type.

package symmetric_group

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/registry"
)

// InSymmetricGroup — a permutation lies in the symmetric group on s
// exactly when it moves no point outside s: the definition, read as
// membership.
var InSymmetricGroup = inSymmetricGroupThm{family.Add(registry.ProofEntry{
	Name: "InSymmetricGroup",
	Key:  "prop_439ffbe2859839aa",
	Build: family.Theorem(
		"∀s:set(A). ∀p:permutation(A). p ∈ symmetric_group(s) ⇔ (∀x:A. x ∉ s ⇒ permutation_map(p, x) = x)",
		Chain(Unfold(SymmetricGroupDef), BySets())),
})}

// SymmetricGroupSubgroup — the permutations that move no point outside s
// form a subgroup. The identity moves nothing. A product moves a point
// by its second factor and then its first, and a point outside s is
// moved by neither. The inverse sends each point back to where the
// permutation found it, and a point outside s was found where it is.
var SymmetricGroupSubgroup = symmetricGroupSubgroupThm{family.Add(registry.ProofEntry{
	Name: "SymmetricGroupSubgroup",
	Key:  "prop_f48660f5eb41b45d",
	Build: family.Theorem("∀s:set(A). subgroup(permutation_group, symmetric_group(s))",
		func(arg *Argument, s *Expr[Set[A]]) {
			arg.Do(Unfold(group.SubgroupDef), Simp(Fwd(InSymmetricGroup)), SplitConjAll(
				Case(
					"the permutations lie in the whole type",
					BySets()),
				Case(
					"the identity moves nothing",
					Simp(Fwd(MapIdentity)),
					Basic()),
				Case(
					"a product moves no point outside s: neither factor moves it",
					Derive(func(b *Argument) {
						b.FixAs[Permutation[A]]("x")
						b.FixAs[Permutation[A]]("y")
						both := b.Assume()
						still := b.Conjuncts(
							both,
							"x moves no point outside s",
							"and neither does y")
						b.Show(
							"the product moves a point by y, then by x, and neither moves it",
							Simp(Fwd(MapCompose)),
							By(Normalized, still[0], still[1]))
					})),
				Case(
					"an inverse moves no point outside s: it sends each point back to where the permutation found it",
					Derive(func(b *Argument) {
						b.FixAs[Permutation[A]]("x")
						still := b.Assume()
						b.Show(
							"x leaves a point outside s where it is, so the inverse returns it there",
							By(Normalized, still, MapInverse))
					})),
			))
		}),
})}

// SymmetricGroupMono — a permutation moving no point outside s moves no
// point outside a larger set either.
var SymmetricGroupMono = symmetricGroupMonoThm{family.Add(registry.ProofEntry{
	Name: "SymmetricGroupMono",
	Key:  "prop_8f9f31bf709e0365",
	Build: family.Theorem(Statement{
		Binders: "∀s t:set(A).",
		Hypotheses: []string{
			"s ⊆ t",
		},
		Conclusion: "symmetric_group(s) ⊆ symmetric_group(t)",
	},
		func(arg *Argument, s, t *Expr[Set[A]], inside Fact) {
			outside := arg.Have(
				"a point outside t lies outside s",
				"∀x:A. x ∉ t ⇒ x ∉ s",
				By(inside, set_basic.SubsetDef))
			arg.Show(
				"so what fixes every point outside s fixes every point outside t",
				Simp(Fwd(set_basic.SubsetDef.Inst[Permutation[A]]()), Fwd(InSymmetricGroup)),
				By(outside))
		}),
})}

// SymmetricGroupMapsInto — a permutation moving no point outside t
// keeps t in t. Were a point x of t sent outside t, its image would stay
// where it is, so the permutation would send x and its image to one
// point; a permutation separates points, so x would be its own image,
// and lie outside t.
var SymmetricGroupMapsInto = symmetricGroupMapsIntoThm{family.Add(registry.ProofEntry{
	Name: "SymmetricGroupMapsInto",
	Key:  "prop_f6e3b4bc7a498b62",
	Build: family.Theorem(Statement{
		Binders: "∀t:set(A). ∀q:permutation(A). ∀x:A.",
		Hypotheses: []string{
			"q ∈ symmetric_group(t)",
			"x ∈ t",
		},
		Conclusion: "permutation_map(q, x) ∈ t",
	},
		func(arg *Argument, t *Expr[Set[A]], q *Expr[Permutation[A]], x *Expr[A], given Fact) {
			parts := arg.Conjuncts(
				given,
				"q moves no point outside t",
				"x lies in t")
			fixes := arg.Have(
				"q leaves every point outside t where it is",
				"∀y:A. y ∉ t ⇒ permutation_map(q, y) = y",
				By(parts[0], InSymmetricGroup))
			separates := arg.Have(
				"and q separates points",
				"∀u v:A. permutation_map(q, u) = permutation_map(q, v) ⇒ u = v",
				By(MapBijective.At(q), functions.InjectiveOnDef, set_basic.InUniv))
			arg.Show(
				"an image outside t would stay put, making x its own image",
				By(
					parts[1],
					fixes.At(arg.TermAs[A]("permutation_map(q, x)")),
					separates.At(arg.TermAs[A]("permutation_map(q, x)"), x)))
		}),
})}

// FiniteInjectionPermutation — a one-to-one map of a finite set into
// itself that fixes every point outside the set is the map of a
// permutation of that set. It maps s into s one-to-one, and a one-to-one
// map of a finite set into itself is onto. The map then separates the
// points of the whole type, and reaches each point: a point of s from s,
// a point outside s as its own image. A bijection of the type is the map
// of its own permutation, which moves no point outside s.
var FiniteInjectionPermutation = finiteInjectionPermutationThm{family.Add(registry.ProofEntry{
	Name: "FiniteInjectionPermutation",
	Key:  "prop_328e4e43284b7b0d",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(A). ∀f:(A → A).",
		Hypotheses: []string{
			"finite(s)",
			"∀x:A. x ∈ s ⇒ f(x) ∈ s",
			"injective_on(s, f)",
			"∀x:A. x ∉ s ⇒ f(x) = x",
		},
		Conclusion: "∃p:permutation(A). p ∈ symmetric_group(s) ∧ permutation_map(p) = f",
	},
		func(a *Argument, s *Expr[Set[A]], f *Arrow[A, A], h Fact) {
			given := a.Conjuncts(
				h,
				"s is finite",
				"f keeps s in s",
				"f separates the points of s",
				"f fixes every point outside s")
			finite, keeps, oneToOne, fixes := given[0], given[1], given[2], given[3]
			into := a.Have(
				"f's image of s lies in s",
				"image(f, s) ⊆ s",
				By(keeps, set_image.ImageSubsetIff))
			onto := a.Have(
				"a one-to-one map of a finite set into itself is onto: f reaches every point of s",
				"∀y:A. y ∈ s ⇒ ∃x:A. x ∈ s ∧ f(x) = y",
				By(finite, into, oneToOne, cardinality.SurjectiveIffInjective.At(s, f)))
			separates := a.Have(
				"f separates the points of the whole type",
				"injective_on(𝕌, f)",
				Simp(Fwd(functions.InjectiveOnDef)),
				Derive(func(b *Argument) {
					x, y := b.FixAs[A]("x"), b.FixAs[A]("y")
					same := b.Assume()
					b.Cases(b.Term("x ∈ s"))
					b.When(
						"x lies in s, and so does f(y) = f(x): y is no point outside "+
							"s, which f would fix, and f separates the points of s",
						func(c *Argument, xIn Fact) {
							pointsOfS := c.Have(
								"f separates the points of s",
								"∀u v:A. u ∈ s ∧ v ∈ s ∧ f(u) = f(v) ⇒ u = v",
								By(oneToOne, functions.InjectiveOnDef))
							c.Show(
								"x = y",
								By(Normalized, xIn, same, keeps.At(x), fixes.At(y), pointsOfS.At(x, y)))
						})
					b.Otherwise(
						"x lies outside s and f fixes it: f(y) = x lies outside s, so y does too, and f fixes y",
						func(c *Argument, xOut Fact) {
							c.Show(
								"x = y",
								By(Normalized, xOut, same, fixes.At(x), fixes.At(y), keeps.At(y)))
						})
				}))
			reaches := a.Have(
				"and reaches every point: a point of s from s, a point outside s as its own image",
				"image(f, 𝕌) = 𝕌",
				BySets(fixes, onto))
			survives := a.Have(
				"so f is a bijection of the type, the map of its own permutation",
				"permutation_map(permutation_of_map(f)) = f",
				By(separates, reaches, PermutationMembership))
			a.Take(a.TermAs[Permutation[A]]("permutation_of_map(f)"))
			a.Show(
				"that permutation's map is f, so it moves a point outside s as f does, which is not at all",
				Simp(Fwd(InSymmetricGroup)),
				survives.Rw(),
				By(fixes))
		}),
})}

// TranspositionInSymmetricGroup — a transposition of two points of s
// moves no point outside s: such a point is neither of the two.
var TranspositionInSymmetricGroup = transpositionInSymmetricGroupThm{family.Add(registry.ProofEntry{
	Name: "TranspositionInSymmetricGroup",
	Key:  "prop_a15b1d96dcf9ab0",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(A). ∀a b:A.",
		Hypotheses: []string{
			"a ∈ s",
			"b ∈ s",
		},
		Conclusion: "transposition(a, b) ∈ symmetric_group(s)",
	},
		Chain(Simp(Fwd(InSymmetricGroup), Fwd(MapTransposition)), BySets())),
})}

// SymmetricGroupEmpty — on the empty set the symmetric group is the
// identity alone: a permutation moving no point at all moves each point
// as the identity does.
var SymmetricGroupEmpty = symmetricGroupEmptyThm{family.Add(registry.ProofEntry{
	Name: "SymmetricGroupEmpty",
	Key:  "prop_96a2f8d6894e2a01",
	Build: family.Theorem("symmetric_group⟨A:A⟩(∅) = {permutation_identity⟨A:A⟩}",
		func(arg *Argument) {
			// ↦ for each p: p moves no point outside ∅ exactly when p is the identity
			arg.Do(Simp(
				Fwd(set_basic.Extension.Inst[Permutation[A]]()),
				Fwd(set_basic.InSing.Inst[Permutation[A]]()),
				Fwd(InSymmetricGroup)))
			arg.Show(
				"moving no point at all is moving each point as the identity does",
				BySets(PermutationEq, MapIdentity))
		}),
})}

// SymmetricGroupUniverse — on the whole type the symmetric group is every
// permutation: no point lies outside 𝕌, so the condition asks nothing.
var SymmetricGroupUniverse = symmetricGroupUniverseThm{family.Add(registry.ProofEntry{
	Name: "SymmetricGroupUniverse",
	Key:  "prop_d867eae524b4e376",
	Build: family.Theorem("symmetric_group⟨A:A⟩(𝕌) = 𝕌",
		func(arg *Argument) {
			arg.Show(
				"a permutation lies in it when it moves no point outside 𝕌, and there is none",
				Simp(Fwd(set_basic.Extension.Inst[Permutation[A]]()), Fwd(InSymmetricGroup)),
				BySets())
		}),
})}

// PermutationAdjacentDescent — a permutation q of the points below n other
// than the identity descends somewhere: some k with k + 1 below n has
// q(k + 1) < q(k). Otherwise q, being one-to-one, climbs at every step below
// n, and a map of the points below n into themselves that climbs at every
// step fixes them all (num_segment.IncreasingSelfMapIsIdentity); q moves no
// point outside them either, so q would be the identity.
var PermutationAdjacentDescent = permutationAdjacentDescentThm{family.Add(registry.ProofEntry{
	Name: "PermutationAdjacentDescent",
	Key:  "prop_4435752e9cf4c1f2",
	Build: family.Theorem(Statement{
		Binders: "∀n:num. ∀q:permutation(num).",
		Hypotheses: []string{
			"q ∈ symmetric_group({i:num | i < n})",
			"q ≠ permutation_identity",
		},
		Conclusion: "∃k:num. suc(k) < n ∧ permutation_map(q, suc(k)) < permutation_map(q, k)",
	}, func(a *Argument, n *Expr[Nat], q *Expr[Permutation[Nat]], h Fact) {
		given := a.Conjuncts(
			h,
			"q permutes the points below n",
			"q is not the identity")
		qIn, moves := given[0], given[1]
		segment := a.TermAs[Set[Nat]]("{i:num | i < n}")
		noDescent := a.SupposeNot()
		injective := a.Unfolded(a.Have(
			"q is one-to-one",
			"injective_on(𝕌, permutation_map(q))",
			By(MapBijective.At(q))), functions.InjectiveOnDef)
		climbs := a.Have(
			"with no descent, q climbs at every step below n",
			"∀k:num. suc(k) < n ⇒ permutation_map(q, k) < permutation_map(q, suc(k))",
			Derive(func(b *Argument) {
				k := b.FixAs[Nat]("k")
				inside := b.Assume()
				sk := b.TermAs[Nat]("suc(k)")
				level := b.Have(
					"q does not descend at k",
					"¬(permutation_map(q, suc(k)) < permutation_map(q, k))",
					By(noDescent, inside))
				b.Show(
					"and, one-to-one, it does not stand still",
					ByArith(level, injective.At(k, sk), set_basic.InUniv.At(k), set_basic.InUniv.At(sk)))
			}))
		into := a.Have(
			"q keeps the points below n below n",
			"∀i:num. i < n ⇒ permutation_map(q, i) < n",
			Derive(func(b *Argument) {
				i := b.FixAs[Nat]("i")
				inside := b.Assume()
				b.Show(
					"q permutes them",
					By(qIn, inside, SymmetricGroupMapsInto.At(segment, q, i)))
			}))
		fixed := a.Have(
			"so q fixes every point below n",
			"∀i:num. i < n ⇒ permutation_map(q, i) = i",
			By(
				At(num_segment.IncreasingSelfMapIsIdentity, n, a.TermAs[Fun[Nat, Nat]]("permutation_map(q)")),
				into,
				climbs))
		identity := a.Have(
			"and q, moving no point outside them, is the identity",
			"q = permutation_identity",
			Derive(func(b *Argument) {
				b.Do(Simp(Fwd(PermutationEq), Fwd(MapIdentity)))
				x := b.FixAs[Nat]("x")
				b.Cases(b.Term("x < n"))
				b.When(
					"x lies below n, where q fixes it",
					func(c *Argument, inside Fact) {
						c.Show(
							"q(x) = x",
							By(fixed.At(x), inside))
					})
				b.Otherwise(
					"x lies outside the points q permutes, so q leaves it",
					func(c *Argument, outside Fact) {
						c.Show(
							"q(x) = x",
							By(outside, qIn, InSymmetricGroup.At(segment, q)))
					})
			}))
		a.Show(
			"contradicting that q is not the identity",
			By(moves, identity))
	}),
})}

// PermutationMovesSomePointDown — a permutation p of the points below n
// other than the identity sends some point below n strictly below itself.
// p fixes every point from n on and moves some point, so the points it
// moves are bounded and have a greatest one, m, which lies below n. Being
// one-to-one, p moves p(m) as well, so p(m) ≤ m by the choice of m, and
// p(m) ≠ m.
var PermutationMovesSomePointDown = permutationMovesSomePointDownThm{family.Add(registry.ProofEntry{
	Name: "PermutationMovesSomePointDown",
	Key:  "prop_731c05d3f9889f80",
	Build: family.Theorem(Statement{
		Binders: "∀n:num. ∀p:permutation(num).",
		Hypotheses: []string{
			"p ∈ symmetric_group({i:num | i < n})",
			"p ≠ permutation_identity",
		},
		Conclusion: "∃i:num. i < n ∧ permutation_map(p, i) < i",
	}, func(a *Argument, n *Expr[Nat], p *Expr[Permutation[Nat]], nonidentity Fact) {
		fixedOutside := a.Have(
			"the permutation fixes every index outside its support",
			"∀i:num. n ≤ i ⇒ permutation_map(p, i) = i",
			ByArith(nonidentity, InSymmetricGroup.At(a.TermAs[Set[Nat]]("{i:num | i < n}"), p)))
		moved := a.Have(
			"a nonidentity permutation moves some index",
			"∃i:num. permutation_map(p, i) ≠ i",
			By(
				nonidentity,
				PermutationEq.At(p, a.TermAs[Permutation[Nat]]("permutation_identity")),
				MapIdentity.Inst[Nat]()))
		bounded := a.Have(
			"the moved indices are bounded by n",
			"∃M:num. ∀i:num. permutation_map(p, i) ≠ i ⇒ i ≤ M",
			Derive(func(b *Argument) {
				b.Take(n)
				i := b.FixAs[Nat]()
				moves := b.Assume()
				b.Show(
					"an index at least n would be fixed",
					ByArith(moves, fixedOutside.At(i)))
			}))
		m, maximal := a.ObtainAs[Nat](
			"choose the greatest moved index",
			"∃m:num. permutation_map(p, m) ≠ m ∧ (∀i:num. permutation_map(p, i) ≠ i ⇒ i ≤ m)",
			By(
				moved,
				bounded,
				nat_order.MaximumExists.At(a.TermAs[Set[Nat]]("λi:num. permutation_map(p, i) ≠ i"))))
		parts := a.Conjuncts(
			maximal,
			"m is moved",
			"every moved index is at most m")
		imageMoves := a.Have(
			"the image of m is also moved, by injectivity",
			"permutation_map(p, permutation_map(p, m)) ≠ permutation_map(p, m)",
			By(
				parts[0],
				MapBijective.At(p),
				functions.InjectiveOnDef.At(a.TermAs[Set[Nat]]("𝕌"), a.TermAs[Fun[Nat, Nat]]("permutation_map(p)")),
				set_basic.InUniv.Inst[Nat]()))
		a.Take(m)
		a.Show(
			"maximality puts the image strictly below m and support puts m below n",
			ByArith(
				parts[0],
				imageMoves,
				parts[1].At(a.TermAs[Nat]("permutation_map(p, m)")),
				fixedOutside.At(m)))
	}),
})}
