package presheaf

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/topology/continuous"
	"github.com/euc-ai/xugo/library/proofs/topology/topological_space"
	"github.com/euc-ai/xugo/library/registry"
)

// BijectionOnBase — a map ψ of sections over a continuous map f, taking
// the sections of G over V to those of F over the preimage of V and
// commuting with restriction, is bijective over every open set once it is
// bijective over each basic open: injective by locality on the basic
// opens inside V, onto by gluing the lifts of a section's restrictions to
// them. Two lifts agree on an overlap by the injectivity over that open
// intersection, so the basis need not be closed under intersection.
var BijectionOnBase = bijectionOnBaseThm{family.Add(registry.ProofEntry{
	Name: "BijectionOnBase",
	Key:  "prop_6e126caf1446c01",
	Build: family.Theorem(Statement{
		Binders: "∀F:sheaf(A, B). " +
			"∀G:sheaf(C, D). " +
			"∀base:set(set(C)). " +
			"∀f:(A → C). " +
			"∀ψ:(set(C) → D → B). " +
			"∀U:set(C).",
		Hypotheses: []string{
			"continuous_map(F.T, G.T, f)",
			"topology_base(G.T, base)",
			"∀V:set(C). ∀s:D. V ∈ G.T ∧ s ∈ G(V) ⇒ ψ(V, s) ∈ F(preimage_on(⋃F.T, f, V))",
			"∀V W:set(C). ∀s:D. " +
				"    V ∈ G.T ∧ W ∈ G.T ∧ W ⊆ V ∧ s ∈ G(V) ⇒ " +
				"    F.res(preimage_on(⋃F.T, f, V), preimage_on(⋃F.T, f, W), ψ(V, s)) = ψ(W, G.res(V, W, s))",
			"∀V:set(C). V ∈ base ⇒ injective_on(G(V), ψ(V)) ∧ image(ψ(V), G(V)) = F(preimage_on(⋃F.T, f, V))",
			"U ∈ G.T",
		},
		Conclusion: "injective_on(G(U), ψ(U)) ∧ image(ψ(U), G(U)) = F(preimage_on(⋃F.T, f, U))",
	},
		func(
			a *Argument,
			F, G Fact,
			base *Expr[Set[Set[C]]],
			f *Arrow[A, C],
			ψ *Arrow2[Set[C], D, B],
			hypotheses Fact,
		) {
			parts := a.Conjuncts(
				hypotheses,
				"f is continuous",
				"base is a basis of the topology of G",
				"ψ takes sections to sections",
				"ψ commutes with restriction",
				"ψ is bijective over each basic open")
			continuity, isBase, mapsInto, natural, basisBijective :=
				parts[0], parts[1], parts[2], parts[3], parts[4]
			baseParts := a.Conjuncts(
				a.Unfolded(isBase, topological_space.TopologyBaseDef),
				"basic opens are open",
				"the basic opens refine every open neighbourhood")
			basicOpen, refines := baseParts[0], baseParts[1]
			preimageOpen := a.Conjuncts(
				a.Unfolded(continuity, continuous.ContinuousMap),
				"f maps the space of F into the space of G",
				"preimages of opens are open")[1]
			injective := a.Have(
				"locality on the basic opens inside V makes ψ injective over every open V",
				"∀V:set(C). V ∈ G.T ⇒ injective_on(G(V), ψ(V))",
				Derive(func(b *Argument) {
					V := b.FixAs[Set[C]]("V")
					open := b.Assume()
					criterion := b.Have(
						"sections with the same image agree on every basic open inside V, hence on V",
						"∀x y:D. x ∈ G(V) ∧ y ∈ G(V) ∧ ψ(V, x) = ψ(V, y) ⇒ x = y",
						Derive(func(c *Argument) {
							x := c.FixAs[D]("x")
							y := c.FixAs[D]("y")
							equalImages := c.Assume()
							cover, coverEq := c.LetAs[Set[Set[C]]]("cover", "{W:set(C) | W ∈ base ∧ W ⊆ V}")
							covers := c.Have(
								"the basic opens inside V cover V",
								"cover ⊆ G.T ∧ ⋃cover = V",
								BySets(refines, coverEq, open, basicOpen))
							agree := c.Have(
								"injectivity over each basic open identifies the two restrictions",
								"∀W:set(C). W ∈ cover ⇒ G.res(V, W, x) = G.res(V, W, y)",
								Derive(func(d *Argument) {
									W := d.FixAs[Set[C]]("W")
									member := d.Assume()
									contained := d.Have(
										"W is a basic open inside V",
										"W ∈ base ∧ W ∈ G.T ∧ W ⊆ V",
										BySets(coverEq, member, basicOpen))
									sections := d.Have(
										"the restrictions are sections on W",
										"G.res(V, W, x) ∈ G(W) ∧ G.res(V, W, y) ∈ G(W)",
										By(RestrictIn.Read(SheafPresheaf.Read(G)), contained, open, equalImages))
									images := d.Have(
										"naturality carries equality of the images to W",
										"ψ(W, G.res(V, W, x)) = ψ(W, G.res(V, W, y))",
										By(contained, open, equalImages, natural.At(V, W, x), natural.At(V, W, y)))
									injectiveW := d.Have(
										"ψ is injective over the basic open W",
										"injective_on(G(W), ψ(W))",
										By(contained, basisBijective.At(W)))
									d.Show(
										"injectivity over W identifies the restrictions",
										By(
											images,
											sections,
											injectiveW,
											functions.InjectiveOnDef.At(d.TermAs[Set[D]]("G(W)"), d.TermAs[Fun[D, B]]("ψ(W)"))))
								}))
							c.Show(
								"locality identifies the sections on V",
								By(agree, open, covers, equalImages, Locality.Read(G).AsFact().At(V, cover, x, y)))
						}))
					b.Show(
						"this is injectivity on G(V)",
						By(criterion, functions.InjectiveOnDef))
				}))
			surjective := a.Have(
				"a section over the preimage of V lifts, glued from its lifts over the basic opens inside V",
				"∀V:set(C). ∀u:B. V ∈ G.T ∧ u ∈ F(preimage_on(⋃F.T, f, V)) ⇒ ∃s:D. s ∈ G(V) ∧ ψ(V, s) = u",
				Derive(func(b *Argument) {
					V := b.FixAs[Set[C]]("V")
					u := b.FixAs[B]("u")
					section := b.Assume()
					open := b.Conjuncts(
						section,
						"V is open",
						"u is a section over the preimage of V")[0]
					preV := b.TermAs[Set[A]]("preimage_on(⋃F.T, f, V)")
					cover, coverEq := b.LetAs[Set[Set[C]]]("cover", "{W:set(C) | W ∈ base ∧ W ⊆ V}")
					covers := b.Have(
						"the basic opens inside V form an open cover of V",
						"cover ⊆ G.T ∧ ⋃cover = V",
						BySets(refines, coverEq, open, basicOpen))
					coverInfo := b.Have(
						"members of the cover are basic opens inside V",
						"∀W:set(C). W ∈ cover ⇒ W ∈ base ∧ W ∈ G.T ∧ W ⊆ V",
						BySets(coverEq, basicOpen))
					g, gEq := b.LetAs[Fun[Set[C], D]](
						"g",
						"λW:set(C). inverse_on(G(W), ψ(W), F.res(preimage_on(⋃F.T, f, V), preimage_on(⋃F.T, f, W), u))")
					lifts := b.Have(
						"over each basic open the inverse lifts the restriction of u",
						Statement{
							Binders: "∀W:set(C).",
							Hypotheses: []string{
								"W ∈ cover",
							},
							Conclusion: "g(W) ∈ G(W) ∧ ψ(W, g(W)) = F.res(preimage_on(⋃F.T, f, V), preimage_on(⋃F.T, f, W), u)",
						},
						Derive(func(c *Argument) {
							W := c.FixAs[Set[C]]("W")
							member := c.Assume()
							contained := c.Have(
								"W is a basic open inside V",
								"W ∈ base ∧ W ∈ G.T ∧ W ⊆ V",
								By(member, coverInfo.At(W)))
							preSubset := c.Have(
								"taking preimages preserves containment",
								"preimage_on(⋃F.T, f, W) ⊆ preimage_on(⋃F.T, f, V)",
								BySets(contained))
							opens := c.Have(
								"both preimages are open",
								"preimage_on(⋃F.T, f, V) ∈ F.T ∧ preimage_on(⋃F.T, f, W) ∈ F.T",
								By(contained, section, preimageOpen.At(V), preimageOpen.At(W)))
							restricted := c.Have(
								"restricting u gives a section on the smaller preimage",
								"F.res(preimage_on(⋃F.T, f, V), preimage_on(⋃F.T, f, W), u) ∈ F(preimage_on(⋃F.T, f, W))",
								By(RestrictIn.Read(SheafPresheaf.Read(F)), section, preSubset, opens))
							inImage := c.Have(
								"surjectivity over W places the restricted section in the image",
								"F.res(preimage_on(⋃F.T, f, V), preimage_on(⋃F.T, f, W), u) ∈ image(ψ(W), G(W))",
								By(restricted, contained, basisBijective.At(W)))
							fiber := c.TermAs[Set[D]]("G(W)")
							mapW := c.TermAs[Fun[D, B]]("ψ(W)")
							restriction := c.TermAs[B]("F.res(preimage_on(⋃F.T, f, V), preimage_on(⋃F.T, f, W), u)")
							c.Show(
								"the inverse belongs to G(W) and maps to the restricted section",
								gEq.Rw(),
								By(
									inImage,
									functions.InverseOnIn.At(fiber, mapW, restriction),
									functions.InverseOnRight.At(fiber, mapW, restriction)))
						}))
					restrictedLift := b.Have(
						"a lift restricted to a smaller open maps to the corresponding restriction of u",
						Statement{
							Binders: "∀K L:set(C).",
							Hypotheses: []string{
								"K ∈ cover",
								"L ∈ G.T",
								"L ⊆ K",
							},
							Conclusion: "G.res(K, L, g(K)) ∈ G(L) ∧ " +
								"ψ(L, G.res(K, L, g(K))) = F.res(preimage_on(⋃F.T, f, V), preimage_on(⋃F.T, f, L), u)",
						},
						Derive(func(c *Argument) {
							K := c.FixAs[Set[C]]("K")
							L := c.FixAs[Set[C]]("L")
							smaller := c.Assume()
							liftK := c.Have(
								"g(K) is a section on the open K inside V",
								"K ∈ G.T ∧ K ⊆ V ∧ g(K) ∈ G(K)",
								By(smaller, coverInfo.At(K), lifts.At(K)))
							subsets := c.Have(
								"the three preimages are nested",
								"preimage_on(⋃F.T, f, L) ⊆ preimage_on(⋃F.T, f, K) ∧ "+
									"preimage_on(⋃F.T, f, K) ⊆ preimage_on(⋃F.T, f, V)",
								BySets(smaller, liftK))
							opens := c.Have(
								"the three preimages are open",
								"preimage_on(⋃F.T, f, V) ∈ F.T ∧ preimage_on(⋃F.T, f, K) ∈ F.T ∧ preimage_on(⋃F.T, f, L) ∈ F.T",
								By(section, liftK, smaller, preimageOpen.At(V), preimageOpen.At(K), preimageOpen.At(L)))
							naturalRestriction := c.Have(
								"naturality compares the restricted lift and its image",
								"F.res(preimage_on(⋃F.T, f, K), preimage_on(⋃F.T, f, L), ψ(K, g(K))) = ψ(L, G.res(K, L, g(K)))",
								By(liftK, smaller, natural.At(K, L, c.TermAs[D]("g(K)"))))
							twice := c.Have(
								"restricting u twice is its restriction to the smallest preimage",
								"F.res(preimage_on(⋃F.T, f, K), "+
									"    preimage_on(⋃F.T, f, L), "+
									"    F.res(preimage_on(⋃F.T, f, V), preimage_on(⋃F.T, f, K), u)) = "+
									"F.res(preimage_on(⋃F.T, f, V), preimage_on(⋃F.T, f, L), u)",
								By(RestrictTwice.Read(SheafPresheaf.Read(F)), section, subsets, opens))
							c.Show(
								"the restriction is a section whose image is the required restriction of u",
								By(RestrictIn.Read(SheafPresheaf.Read(G)), naturalRestriction, twice, liftK, smaller, lifts.At(K)))
						}))
					compatible := b.Have(
						"the lifts agree on overlaps",
						"∀W W':set(C). W ∈ cover ∧ W' ∈ cover ⇒ G.res(W, W ∩ W', g(W)) = G.res(W', W ∩ W', g(W'))",
						Derive(func(c *Argument) {
							W := c.FixAs[Set[C]]("W")
							Wprime := c.FixAs[Set[C]]("W'")
							members := c.Assume()
							opens := c.Have(
								"both basic opens are open",
								"W ∈ G.T ∧ W' ∈ G.T",
								By(members, coverInfo.At(W), coverInfo.At(Wprime)))
							overlapOpen := c.Have(
								"their intersection is open",
								"W ∩ W' ∈ G.T",
								By(topological_space.InterOpen.Read(Topology.Read(SheafPresheaf.Read(G))), opens))
							overlapSubsets := c.Have(
								"the intersection lies in both opens",
								"W ∩ W' ⊆ W ∧ W ∩ W' ⊆ W'",
								BySets())
							overlap := c.TermAs[Set[C]]("W ∩ W'")
							restrictedW := c.Have(
								"the lift from W restricts to a section with the prescribed image",
								"G.res(W, W ∩ W', g(W)) ∈ G(W ∩ W') ∧ "+
									"ψ(W ∩ W', G.res(W, W ∩ W', g(W))) = "+
									"F.res(preimage_on(⋃F.T, f, V), preimage_on(⋃F.T, f, W ∩ W'), u)",
								By(overlapOpen, members, overlapSubsets, restrictedLift.At(W, overlap)))
							restrictedWprime := c.Have(
								"the lift from W' restricts to a section with the same prescribed image",
								"G.res(W', W ∩ W', g(W')) ∈ G(W ∩ W') ∧ "+
									"ψ(W ∩ W', G.res(W', W ∩ W', g(W'))) = "+
									"F.res(preimage_on(⋃F.T, f, V), preimage_on(⋃F.T, f, W ∩ W'), u)",
								By(overlapOpen, members, overlapSubsets, restrictedLift.At(Wprime, overlap)))
							bothRestricted := c.Have(
								"the two restrictions are sections with equal images",
								"G.res(W, W ∩ W', g(W)) ∈ G(W ∩ W') ∧ "+
									"G.res(W', W ∩ W', g(W')) ∈ G(W ∩ W') ∧ "+
									"ψ(W ∩ W', G.res(W, W ∩ W', g(W))) = ψ(W ∩ W', G.res(W', W ∩ W', g(W')))",
								By(restrictedW, restrictedWprime))
							overlapInjective := c.Have(
								"ψ is injective over the open intersection",
								"injective_on(G(W ∩ W'), ψ(W ∩ W'))",
								By(overlapOpen, injective.At(overlap)))
							c.Show(
								"injectivity over the intersection identifies the restricted lifts",
								By(
									bothRestricted,
									overlapInjective,
									functions.InjectiveOnDef.At(c.TermAs[Set[D]]("G(W ∩ W')"), c.TermAs[Fun[D, B]]("ψ(W ∩ W')"))))
						}))
					s, glued := b.ObtainAs[D](
						"glue the compatible lifts to a section on V",
						"∃s:D. s ∈ G(V) ∧ (∀W:set(C). W ∈ cover ⇒ G.res(V, W, s) = g(W))",
						By(compatible, lifts, section, covers, Gluing.Read(G).AsFact().At(V, cover, g)))
					pulled, pulledEq := b.LetAs[Set[Set[A]]](
						"pulled", "image(λW:set(C). preimage_on(⋃F.T, f, W), cover)")
					preimages := b.TermAs[Fun[Set[C], Set[A]]]("λW:set(C). preimage_on(⋃F.T, f, W)")
					pulledCovers := b.Have(
						"preimages of the basic cover cover the preimage of V",
						"⋃pulled = preimage_on(⋃F.T, f, V)",
						pulledEq.Rw(),
						BySets(covers))
					pulledMembers := b.Have(
						"each member of the pulled back cover is an open preimage on which ψ(V, s) and u restrict alike",
						Statement{
							Binders: "∀Q:set(A).",
							Hypotheses: []string{
								"Q ∈ pulled",
							},
							Conclusion: "Q ∈ F.T ∧ " +
								"F.res(preimage_on(⋃F.T, f, V), Q, ψ(V, s)) = F.res(preimage_on(⋃F.T, f, V), Q, u)",
						},
						pulledEq.Rw(),
						Derive(func(c *Argument) {
							Q := c.FixAs[Set[A]]("Q")
							member := c.Assume()
							W, represented := c.ObtainAs[Set[C]](
								"Q is the preimage of a member W of the basic cover",
								"∃W:set(C). Q = preimage_on(⋃F.T, f, W) ∧ W ∈ cover",
								By(member, set_basic.InImage.At(preimages, cover, Q)))
							representation := c.Conjuncts(
								represented,
								"Q is the preimage of W",
								"W lies in the cover")
							equation, inCover := representation[0], representation[1]
							c.Do(equation.Rw())
							contained := c.Have(
								"W is open and lies in V",
								"W ∈ G.T ∧ W ⊆ V",
								By(inCover, coverInfo.At(W)))
							restriction := c.Have(
								"the glued section restricts to the lift over W",
								"G.res(V, W, s) = g(W)",
								By(inCover, glued))
							c.Show(
								"the preimage of W is open, and ψ(V, s) and u restrict alike to it",
								SplitConj(
									Case(
										"continuity makes the preimage of W open",
										By(contained, preimageOpen.At(W))),
									Case(
										"naturality identifies both restrictions with the image of the lift over W",
										By(restriction, inCover, glued, section, contained, natural.At(V, W, s), lifts.At(W))),
								))
						}))
					pulledOpen := b.Have(
						"the pulled back cover consists of opens",
						"pulled ⊆ F.T",
						BySets(pulledMembers))
					target := b.Have(
						"the image of s is a section on the open preimage of V",
						"preimage_on(⋃F.T, f, V) ∈ F.T ∧ ψ(V, s) ∈ F(preimage_on(⋃F.T, f, V))",
						By(section, glued, preimageOpen.At(V), mapsInto.At(V, s)))
					image := b.Have(
						"locality identifies the image of s with u",
						"ψ(V, s) = u",
						By(
							pulledMembers,
							pulledCovers,
							pulledOpen,
							target,
							section,
							Locality.Read(F).AsFact().At(preV, pulled, b.TermAs[B]("ψ(V, s)"), u)))
					b.Take(s)
					b.Show(
						"s is the required lift",
						By(glued, image))
				}))
			V := a.FixAs[Set[C]]("V")
			open := a.Assume()
			a.Show(
				"ψ is injective over V and its image is the sections over the preimage of V",
				SplitConj(
					Case(
						"locality gives injectivity over V",
						By(open, injective.At(V))),
					Case(
						"the image consists of precisely the sections on the preimage",
						Simp(Fwd(set_basic.Extension)),
						Derive(func(b *Argument) {
							z := b.FixAs[B]("z")
							b.Iff()
							b.Backward(
								"every target section has a lift",
								func(c *Argument, member Fact) {
									_, lifted := c.ObtainAs[D](
										"surjectivity supplies a preimage of z",
										"∃s:D. s ∈ G(V) ∧ ψ(V, s) = z",
										By(member, open, surjective.At(V, z)))
									c.Show(
										"therefore z belongs to the image",
										BySets(lifted))
								})
							b.Forward(
								"ψ maps each source section into the target",
								func(c *Argument, inImage Fact) {
									s, represented := c.ObtainAs[D](
										"an image element has a source section",
										"∃s:D. s ∈ G(V) ∧ z = ψ(V, s)",
										BySets(inImage))
									representation := c.Conjuncts(
										represented,
										"s is a source section",
										"z is the image of s")
									c.Show(
										"so z, the image of a source section, is a target section",
										representation[1].Rw(),
										By(open, representation[0], mapsInto.At(V, s)))
								})
						})),
				))
		}),
})}
