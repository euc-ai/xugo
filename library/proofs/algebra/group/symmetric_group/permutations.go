// permutations.go — what a permutation is as a map: the map is
// bijective, a permutation is determined by its map, and each operation
// on permutations is the matching operation on maps.

package symmetric_group

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// A permutation and its map
// ---------------------------------------------------------------------------

// MapBijective — the map of a permutation is bijective. Membership, read
// at p's own map, says the map is bijective exactly when it survives the
// round trip through the type; the retraction at p is that survival.
var MapBijective = mapBijectiveThm{family.Add(registry.ProofEntry{
	Name: "MapBijective",
	Key:  "prop_3ceede45929f51cb",
	Build: family.Theorem("∀p:permutation(A). "+
		"    injective_on(𝕌, permutation_map(p)) ∧ image(permutation_map(p), 𝕌) = 𝕌",
		func(a *Argument, p *Expr[Permutation[A]]) {
			retraction := a.Have(
				"p is the permutation of its own map",
				"permutation_of_map(permutation_map(p)) = p",
				By(PermutationRetraction.At(p)))
			survives := a.Have(
				"so p's map survives the round trip",
				"permutation_map(permutation_of_map(permutation_map(p))) = permutation_map(p)",
				retraction.Rw(),
				Basic())
			a.Show(
				"and a map that survives it is bijective",
				By(survives, PermutationMembership))
		}),
})}

// MapOfBijection — the permutation made from a bijective map moves each
// point as the map does. Membership, read from right to left, says the
// bijection survives the round trip through the type; the rest is that
// equation of maps read at a point.
var MapOfBijection = mapOfBijectionThm{family.Add(registry.ProofEntry{
	Name: "MapOfBijection",
	Key:  "prop_2c16f9bca54ff4ae",
	Build: family.Theorem(Statement{
		Binders: "∀f:(A → A). ∀x:A.",
		Hypotheses: []string{
			"injective_on(𝕌, f)",
			"image(f, 𝕌) = 𝕌",
		},
		Conclusion: "permutation_map(permutation_of_map(f), x) = f(x)",
	},
		func(a *Argument, f *Expr[Fun[A, A]], x *Expr[A], bijective Fact) {
			survives := a.Have(
				"a bijection survives the round trip: the claim is membership's right side, read back to its left",
				"permutation_map(permutation_of_map(f)) = f",
				Simp(Rev(PermutationMembership)),
				By(bijective))
			a.Show(
				"so the two maps agree at x",
				survives.Rw(),
				Basic())
		}),
})}

// PermutationEq — two permutations are equal exactly when they move every
// point alike. One way is congruence; the other is extensionality for
// the maps, carried back into the type by the retraction.
var PermutationEq = permutationEqThm{family.Add(registry.ProofEntry{
	Name: "PermutationEq",
	Key:  "prop_3f3af093d08642ac",
	Build: family.Theorem("∀p q:permutation(A). "+
		"    p = q ⇔ (∀x:A. permutation_map(p, x) = permutation_map(q, x))",
		func(a *Argument, p, q *Expr[Permutation[A]]) {
			a.Iff()
			a.Forward(
				"equal permutations have equal maps",
				func(b *Argument, eq Fact) {
					b.Do(eq.Rw(), Basic())
				})
			a.Backward(
				"equal maps make equal permutations",
				func(b *Argument, pointwise Fact) {
					maps := b.Have(
						"the two maps are one map",
						"permutation_map(p) = permutation_map(q)",
						Funext(),
						By(pointwise))
					b.Show(
						"each permutation is the permutation of its map",
						CalcEq(
							Leg(
								b.Term("permutation_of_map(permutation_map(p))"),
								"p is the permutation of its own map",
								By(PermutationRetraction.At(p))),
							Leg(
								b.Term("permutation_of_map(permutation_map(q))"),
								"which is q's map",
								maps.Rw(),
								Basic()),
							FinalLeg(
								"and that is q",
								By(PermutationRetraction.At(q))),
						))
				})
		}),
})}

// ---------------------------------------------------------------------------
// The operations, read on the maps
// ---------------------------------------------------------------------------

// MapCompose — the product of two permutations moves a point by q and
// then by p. The composite of two bijections is a bijection, so the
// composite map survives the round trip through the type.
var MapCompose = mapComposeThm{family.Add(registry.ProofEntry{
	Name: "MapCompose",
	Key:  "prop_3ac39a35d0876b7d",
	Build: family.Theorem("∀p q:permutation(A). ∀x:A. "+
		"    permutation_map(p * q, x) = permutation_map(p, permutation_map(q, x))",
		func(a *Argument, p, q *Expr[Permutation[A]], x *Expr[A]) {
			// ↦ the product read as the permutation of the composite map
			a.Do(Unfold(PermutationComposeDef))
			pBijective := a.Have(
				"p's map is bijective",
				"injective_on(𝕌, permutation_map(p)) ∧ image(permutation_map(p), 𝕌) = 𝕌",
				By(MapBijective.At(p)))
			qBijective := a.Have(
				"and so is q's",
				"injective_on(𝕌, permutation_map(q)) ∧ image(permutation_map(q), 𝕌) = 𝕌",
				By(MapBijective.At(q)))
			separates := a.Have(
				"the composite separates points: each map separates "+
					"the points of the whole type, where q sends them",
				"injective_on(𝕌, permutation_map(p) ∘ permutation_map(q))",
				By(pBijective, qBijective, functions.InjectiveOnCompose, set_basic.InUniv))
			onto := a.Have(
				"and sends the type onto itself: its image is p's image of q's",
				"image(permutation_map(p) ∘ permutation_map(q), 𝕌) = 𝕌",
				By(pBijective, qBijective, set_image.ImageCompose))
			survives := a.Have(
				"so the composite map survives the round trip",
				"permutation_map(permutation_of_map(permutation_map(p) ∘ permutation_map(q)), x) = "+
					"(permutation_map(p) ∘ permutation_map(q))(x)",
				By(separates, onto, MapOfBijection))
			a.Show(
				"and the composite map moves x by q, then by p",
				survives.Rw(),
				Unfold(functions.ComposeApply))
		}),
})}

// MapIdentity — the identity permutation moves no point: the identity
// map is bijective, and so survives the round trip.
var MapIdentity = mapIdentityThm{family.Add(registry.ProofEntry{
	Name: "MapIdentity",
	Key:  "prop_78f03d4294e4c113",
	Build: family.Theorem("∀x:A. permutation_map(permutation_identity, x) = x",
		func(a *Argument, x *Expr[A]) {
			a.Do(Unfold(PermutationIdentityDef))
			survives := a.Have(
				"the identity map is a bijection, so it survives the round trip",
				"permutation_map(permutation_of_map(identity_map), x) = identity_map(x)",
				By(functions.IdentityInjective, set_image.ImageI, MapOfBijection))
			a.Show(
				"and the identity map returns x",
				survives.Rw(),
				Unfold(functions.IdentityApply))
		}),
})}

// MapInverse — the named carrier inverse is bijective on the whole type,
// so its map survives the round trip through the permutation type. The
// left inverse law then returns the original point.
var MapInverse = mapInverseThm{family.Add(registry.ProofEntry{
	Name: "MapInverse",
	Key:  "prop_478208da09eb355f",
	Build: family.Theorem("∀p:permutation(A). ∀x:A. "+
		"    permutation_map(permutation_inverse(p), permutation_map(p, x)) = x",
		func(a *Argument, p *Expr[Permutation[A]], x *Expr[A]) {
			a.Do(Unfold(PermutationInverseDef))
			universe := a.TermAs[Set[A]]("𝕌")
			mapOfP := a.TermAs[Fun[A, A]]("permutation_map(p)")
			inverseMap := a.TermAs[Fun[A, A]]("inverse_on(𝕌, permutation_map(p))")
			image := a.TermAs[A]("permutation_map(p, x)")
			bijective := a.Have(
				"p's map is bijective",
				"injective_on(𝕌, permutation_map(p)) ∧ image(permutation_map(p), 𝕌) = 𝕌",
				Cite(MapBijective))
			separates := a.Have(
				"the carrier inverse separates points of the whole type",
				"injective_on(𝕌, inverse_on(𝕌, permutation_map(p)))",
				By(Normalized, bijective, functions.InverseOnInjective.At(universe, mapOfP)))
			reaches := a.Have(
				"and its image is the whole type",
				"image(inverse_on(𝕌, permutation_map(p)), 𝕌) = 𝕌",
				By(Normalized, bijective, functions.InverseOnImage.At(universe, mapOfP)))
			survives := a.Have(
				"so the inverse map survives the round trip",
				"permutation_map(permutation_of_map(inverse_on(𝕌, permutation_map(p))), permutation_map(p, x)) = "+
					"inverse_on(𝕌, permutation_map(p), permutation_map(p, x))",
				By(reaches, separates, MapOfBijection.At(inverseMap, image)))
			a.Show(
				"the carrier inverse sends p's image of x back to x",
				survives.Rw(),
				By(bijective, set_basic.InUniv, functions.InverseOnLeft.At(universe, mapOfP, x)))
		}),
})}

// MapInverseRight — a permutation undoes its own inverse: p is the inverse
// of its inverse, and MapInverse read at that inverse returns the point.
var MapInverseRight = mapInverseRightThm{family.Add(registry.ProofEntry{
	Name: "MapInverseRight",
	Key:  "prop_dfb73214c65669f5",
	Build: family.Theorem("∀p:permutation(A). ∀x:A. "+
		"    permutation_map(p, permutation_map(permutation_inverse(p), x)) = x",
		func(a *Argument, p *Expr[Permutation[A]], x *Expr[A]) {
			a.Show(
				"p is the inverse of its inverse, whose left inverse law returns x",
				By(
					Normalized,
					group.InvInv.Read(SymmetricGroup).At(p),
					MapInverse.At(a.TermAs[Permutation[A]]("permutation_inverse(p)"), x)))
		}),
})}

// MapTransposition — the transposition of a and b sends a to b, b to a,
// and every other point to itself. The swap separates points and
// reaches every point — each point is the image of its own swap — so it
// survives the round trip through the type.
var MapTransposition = mapTranspositionThm{family.Add(registry.ProofEntry{
	Name: "MapTransposition",
	Key:  "prop_498a85f0a400343a",
	Build: family.Theorem(Statement{
		Binders:    "∀a b x:A.",
		Conclusion: "permutation_map(transposition(a, b), x) = COND(x = a, b, COND(x = b, a, x))",
		Abbrev: Abbrev{
			{Name: "swapMap", Text: "λx:A. COND(x = a, b, COND(x = b, a, x))"},
		},
	},
		func(arg *Argument, a, b, x *Expr[A]) {
			// ↦ the transposition read as the permutation of the swap
			arg.Do(Unfold(TranspositionDef))
			swapBijective := arg.Have(
				"the swap is a bijection: read case by case, it sends "+
					"distinct points apart and each point is the image of its swap",
				"injective_on(𝕌, «swapMap») ∧ image(«swapMap», 𝕌) = 𝕌",
				Simp(Fwd(functions.InjectiveOnDef.Inst(TypeBinder.BindA[A](), TypeBinder.BindB[A]()))),
				BySets())
			arg.Show(
				"and survives the round trip",
				By(swapBijective, MapOfBijection))
		}),
})}
