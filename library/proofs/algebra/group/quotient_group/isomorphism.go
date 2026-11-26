// isomorphism.go — the first isomorphism theorem: a homomorphism f
// induces a map on the cosets of its kernel, x·K ↦ f(x), and that map is
// an isomorphism of the quotient onto the image. The map is defined by
// choosing a point of the coset, so the theorem opens with its
// well-definedness: f takes the same value at every point of a coset of
// its kernel, whichever point is chosen.

package quotient_group

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/relations/equivalence"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The first isomorphism theorem
// ---------------------------------------------------------------------------

// InducedMapCosetWithin — the induced map is well defined on the cosets
// of any subgroup K inside the kernel: on the coset of a point x of c it
// takes the value f(x). This is the relations chapter's
// equivalence.InducedMapClass read at the coset relation of K: the relation
// is an equivalence on c (group.CosetEquivalenceOn); f respects it, since
// two points of c one of which lies in the coset of the other differ by a
// point of K, which lies in the kernel (group_homomorphism.EqIffInKernel);
// and the class of x inside c is its coset (group.LeftCosetClassOn).
var InducedMapCosetWithin = inducedMapCosetWithinThm{family.Add(registry.ProofEntry{
	Name: "InducedMapCosetWithin",
	Key:  "prop_186b752896e9bd59",

	Build: group_homomorphism.GroupHomomorphism.Law(Statement{
		Binders: "∀K:set(A). ∀x:A.",
		Hypotheses: []string{
			"subgroup(G, K)",
			"K ⊆ group_kernel(H.one, G.carrier, f)",
			"x ∈ G.carrier",
		},
		Conclusion: "induced_map(f, left_coset(x, K)) = f(x)",
	},
		func(
			a *Argument,
			hom group_homomorphism.GroupHomomorphismFact[on.G, on.H],
			K *Expr[Set[A]],
			x *Member[A, on.G],
			given Fact,
		) {
			parts := a.Conjuncts(
				given,
				"K is a subgroup of the source",
				"and lies inside the kernel")
			subgroup, withinKernel := parts[0], parts[1]
			source := group_homomorphism.Source.Read(hom)
			kInC := a.Have(
				"K lies in G.carrier",
				"K ⊆ G.carrier",
				By(group.SubgroupSubset, subgroup))
			cosets := a.Have(
				"lying in a point's coset of K is an equivalence on G.carrier",
				"equivalence_on(G.carrier, λu:A. λv:A. v ∈ left_coset(u, K))",
				By(group.CosetEquivalenceOn, source, subgroup))
			respects := a.Have(
				"f respects it: a point of G.carrier in the coset of another "+
					"differs from it by a point of K, which lies in the kernel",
				"respects_on(G.carrier, λu:A. λv:A. v ∈ left_coset(u, K), f)",
				Unfold(equivalence.RespectsOnDef),
				Derive(func(b *Argument) {
					u := b.FixAs[A]("u")
					v := b.FixAs[A]("v")
					points := b.Conjuncts(
						b.Assume(),
						"u lies in G.carrier",
						"so does v",
						"v lies in the coset of u")
					uM, vM := b.MemberOf[on.G](u, points[0]), b.MemberOf[on.G](v, points[1])
					inK := b.Have(
						"read through the inverse, G.inv(u) * v lies in K",
						"G.inv(u) * v ∈ K",
						By(points[2], group.InLeftCosetOn.Read(source).At(uM, vM, K), kInC))
					inKernel := b.Have(
						"which lies in the kernel",
						"G.inv(u) * v ∈ group_kernel(H.one, G.carrier, f)",
						BySets(inK, withinKernel))
					b.Show(
						"so f takes one value at u and at v",
						By(inKernel, group_homomorphism.EqIffInKernel.Read(hom).At(uM, vM)))
				}))
			class := a.Have(
				"the class of x inside G.carrier is its coset",
				"equivalence_class(relation_on(G.carrier, λu:A. λv:A. v ∈ left_coset(u, K)), x) = left_coset(x, K)",
				By(group.LeftCosetClassOn.Read(source), x, kInC))
			a.Show(
				"so the induced map on the coset of x is its value on the class of x, which is f(x)",
				class.RwRev(),
				By(equivalence.InducedMapClass.Read(cosets), respects, x))
		}),
})}

// InducedMapCoset — the induced map is well defined on the cosets of the
// kernel: on the coset of a point x of c it takes the value f(x). The
// kernel is a subgroup inside itself, so this is InducedMapCosetWithin
// at K = the kernel.
var InducedMapCoset = inducedMapCosetThm{family.Add(registry.ProofEntry{
	Name: "InducedMapCoset",
	Key:  "prop_96bbc79901ea931",

	Build: group_homomorphism.GroupHomomorphism.Law(Statement{
		Binders: "∀x:A.",
		Hypotheses: []string{
			"x ∈ G.carrier",
		},
		Conclusion: "induced_map(f, left_coset(x, group_kernel(H.one, G.carrier, f))) = f(x)",
	},
		func(a *Argument, hom group_homomorphism.GroupHomomorphismFact[on.G, on.H], x *Member[A, on.G]) {
			kernel := a.TermAs[Set[A]]("group_kernel(H.one, G.carrier, f)")
			subgroup := a.Have(
				"the kernel is a subgroup of the source",
				"subgroup(G, group_kernel(H.one, G.carrier, f))",
				By(group_homomorphism.KernelSubgroup, hom))
			a.Show(
				"the kernel is a subgroup of the source lying inside itself",
				By(InducedMapCosetWithin.Read(hom).At(kernel, x), subgroup, set_order.SubsetRefl.At(kernel)))
		}),
})}

// ImageLeftCosetMul — multiplying the image of a source coset by K
// absorbs the image of N into K. Map a representative u * v and
// reassociate; conversely, u itself belongs to the source coset.
var ImageLeftCosetMul = imageLeftCosetMulThm{family.Add(registry.ProofEntry{
	Name: "ImageLeftCosetMul",
	Key:  "prop_556d898f07103e6f",

	Build: group_homomorphism.GroupHomomorphism.Law(
		Statement{
			Binders: "∀N:set(A). ∀K:set(B). ∀u:A.",
			Hypotheses: []string{
				"subgroup(G, N)",
				"subgroup(H, K)",
				"∀v:A. v ∈ N ⇒ f(v) ∈ K",
				"u ∈ G.carrier",
			},
			Conclusion: "set_mul(image(f, left_coset(u, N)), K) = left_coset(f(u), K)",
		},
		func(
			a *Argument,
			hom group_homomorphism.GroupHomomorphismFact[on.G, on.H],
			N *Expr[Set[A]],
			K *Expr[Set[B]],
			u *Expr[A],
			hypotheses Fact,
		) {
			source := a.Have(
				"the source is a group on G.carrier",
				"group_on(G)",
				By(hom, group_homomorphism.Source))
			target := a.Have(
				"the target is a group on H.carrier",
				"group_on(H)",
				By(hom, group_homomorphism.Target))
			sourceSubset := a.Have(
				"N lies in the source carrier",
				"N ⊆ G.carrier",
				By(hypotheses, group.SubgroupSubset))
			targetSubset := a.Have(
				"K lies in the target carrier",
				"K ⊆ H.carrier",
				By(hypotheses, group.SubgroupSubset))
			pointwise := a.Have(
				"the two sets have the same elements",
				"∀z:B. z ∈ set_mul(image(f, left_coset(u, N)), K) ⇔ z ∈ left_coset(f(u), K)",
				Derive(func(b *Argument) {
					b.FixAs[B]("z")
					b.Iff()
					b.Forward(
						"map the source representative and absorb its N part into K",
						func(b *Argument, inProduct Fact) {
							_, _, product := b.Obtain2As[B, B](
								"write a point of the product using an image point and an element of K",
								"∃y k:B. y ∈ image(f, left_coset(u, N)) ∧ k ∈ K ∧ z = y * k",
								By(inProduct, InSetMul.Inst[B]()))
							_, imagePoint := b.ObtainAs[A](
								"choose a source point mapping to y",
								"∃x:A. y = f(x) ∧ x ∈ left_coset(u, N)",
								By(product, set_basic.InImage))
							_, sourcePoint := b.ObtainAs[A](
								"write that source point as u times a point of N",
								"∃v:A. v ∈ N ∧ x = u * v",
								BySets(imagePoint, group.LeftCosetDef.At(b.TermAs[Fun2[A, A, A]]("G.mul"), u, N)))
							b.Have(
								"the source factor lies in G.carrier",
								"v ∈ G.carrier",
								BySets(sourceSubset, sourcePoint))
							imageInK := b.Have(
								"its image lies in K",
								"f(v) ∈ K",
								By(hypotheses, sourcePoint))
							imageInTarget := b.Have(
								"f maps u into the target carrier",
								"f(u) ∈ H.carrier",
								By(hypotheses, group_homomorphism.MapIn.Read(hom)))
							b.Have(
								"the three target factors lie in H.carrier",
								"f(u) ∈ H.carrier ∧ f(v) ∈ H.carrier ∧ k ∈ H.carrier",
								BySets(targetSubset, imageInK, product, imageInTarget))
							absorbed := b.Have(
								"K is closed under the remaining product",
								"f(v) * k ∈ K",
								By(hypotheses, imageInK, product, group.SubgroupMul))
							productForm := b.Have(
								"substitute the two representatives",
								"z = f(u * v) * k",
								By(Normalized, sourcePoint, imagePoint, product))
							cosetForm := b.Have(
								"map the source product and associate the target product",
								"z = f(u) * (f(v) * k)",
								productForm.Rw(),
								Simp(Fwd(group_homomorphism.MapMul.Read(hom)), Rev(group.AssocOn.Read(target))),
								Refl())
							b.Do(Simp(Fwd(group.LeftCosetDef.Inst[B]()), Fwd(set_basic.InImage)))
							b.Take(b.TermAs[B]("f(v) * k"))
							b.Show(
								"the remaining product witnesses membership in f(u)K",
								By(absorbed, cosetForm))
						})
					b.Backward(
						"use u itself as the source-coset representative",
						func(b *Argument, inCoset Fact) {
							uInCoset := b.Have(
								"u belongs to its own coset",
								"u ∈ left_coset(u, N)",
								By(hypotheses, source, group.InOwnLeftCosetOn))
							k, representative := b.ObtainAs[B](
								"write the target point as f(u) times a point of K",
								"∃k:B. k ∈ K ∧ z = f(u) * k",
								BySets(inCoset, group.LeftCosetDef.At(b.TermAs[Fun2[B, B, B]]("H.mul"), b.TermAs[B]("f(u)"), K)))
							imagePoint := b.Have(
								"f(u) is in the image of the source coset",
								"f(u) ∈ image(f, left_coset(u, N))",
								Derive(func(d *Argument) {
									d.Do(Simp(Fwd(set_basic.InImage)))
									d.Take(u)
									d.Show(
										"u supplies its own image",
										By(uInCoset))
								}))
							b.Do(Simp(Fwd(InSetMul.Inst[B]())))
							b.Take(b.TermAs[B]("f(u)"))
							b.Take(k)
							b.Show(
								"f(u) and k supply the two product factors",
								By(imagePoint, representative))
						})
				}))
			a.Show(
				"set extensionality identifies the cosets",
				By(pointwise, set_basic.Extension.Inst[B]()))
		}),
})}

// FirstIsomorphism — the first isomorphism theorem: the map x·K ↦ f(x)
// the homomorphism induces on the cosets of its kernel is an isomorphism
// of the quotient group onto the image. A homomorphism first: the
// quotient is a group on the cosets (QuotientGroupOn, the kernel being
// normal) and the image a group on its set (ImageSubgroup); the induced
// map carries a coset x·K, with x in c, to f(x), a point of the image;
// and it is multiplicative on cosets — the product of x·K and y·K is
// (x * y)·K (LeftCosetMulOn), the induced values are f(x * y), f(x) and
// f(y) (InducedMapCoset), and the map respects the product (MapMul).
// One-to-one on cosets: if the induced values of x·K and y·K agree then
// f(x) = f(y), so inv(x) * y lies in the kernel (EqIffInKernel) and x
// and y determine the same coset (LeftCosetEqOn). And onto the image: a
// point f(x) of it is the induced value of the coset x·K.
var FirstIsomorphism = firstIsomorphismThm{family.Add(registry.ProofEntry{
	Name: "FirstIsomorphism",
	Key:  "prop_6fc740c07f5f238",

	Build: group_homomorphism.GroupHomomorphism.Law(
		"group_isomorphism(quotient_group(G, group_kernel(H.one, G.carrier, f)), "+
			"    restrict_group(H, image(f, G.carrier)), "+
			"    induced_map(f))",
		func(a *Argument, hom group_homomorphism.GroupHomomorphismFact[on.G, on.H]) {
			source := a.Have(
				"the source is a group on G.carrier",
				"group_on(G)",
				By(group_homomorphism.Source, hom))
			target := a.Have(
				"the target is a group on H.carrier",
				"group_on(H)",
				By(group_homomorphism.Target, hom))
			normal := a.Have(
				"the kernel is normal in the source",
				"normal_subgroup(G, group_kernel(H.one, G.carrier, f))",
				By(group_homomorphism.KernelNormal, hom))
			kernel := a.Have(
				"and a subgroup",
				"subgroup(G, group_kernel(H.one, G.carrier, f))",
				By(group_homomorphism.KernelSubgroup, hom))
			K := a.TermAs[Set[A]]("group_kernel(H.one, G.carrier, f)")
			kInC := a.Have(
				"which lies in G.carrier",
				"group_kernel(H.one, G.carrier, f) ⊆ G.carrier",
				By(group.SubgroupSubset, kernel))
			imageSubgroup := a.Have(
				"the image is a subgroup of the target",
				"subgroup(H, image(f, G.carrier))",
				By(group_homomorphism.ImageSubgroup, hom))
			imageParts := a.Conjuncts(
				a.Have(
					"so it lies in H.carrier and is a group on its own set",
					"image(f, G.carrier) ⊆ H.carrier ∧ group_on(restrict_group(H, image(f, G.carrier)))",
					By(Read(group.SubgroupGroupOn, target), imageSubgroup)),
				"the image lies in H.carrier",
				"and is a group on its set")
			imageGroup := imageParts[1]
			quotient := a.Have(
				"the cosets of the kernel are a group on a set",
				"group_on(quotient_group(G, group_kernel(H.one, G.carrier, f)))",
				By(QuotientGroupOn, source, normal))
			carries := a.Have(
				"the induced map carries a coset into the image: the coset of a point x of G.carrier goes to f(x)",
				Statement{
					Binders: "∀s:set(A).",
					Hypotheses: []string{
						"s ∈ left_cosets(G.carrier, group_kernel(H.one, G.carrier, f))",
					},
					Conclusion: "induced_map(f, s) ∈ image(f, G.carrier)",
				},
				Simp(Fwd(ForallInLeftCosets.Read(source))),
				Derive(func(b *Argument) {
					b.FixAs[A]("x")
					xIn := b.Assume()
					b.Do(Simp(Fwd(set_basic.InImage)))
					b.Take(b.TermAs[A]("x"))
					b.Do(SplitConj(
						Case(
							"the induced value of the coset of x is f(x)",
							By(InducedMapCoset, hom, xIn)),
						Case(
							"and x is a point of G.carrier",
							By(xIn)),
					))
				}))
			multiplicative := a.Have(
				"multiplicative on cosets: the induced value of a "+
					"product of cosets is the product of the induced values",
				Statement{
					Binders: "∀s t:set(A).",
					Hypotheses: []string{
						"s ∈ left_cosets(G.carrier, group_kernel(H.one, G.carrier, f))",
						"t ∈ left_cosets(G.carrier, group_kernel(H.one, G.carrier, f))",
					},
					Conclusion: "induced_map(f, set_mul(s, t)) = induced_map(f, s) * induced_map(f, t)",
				},
				Simp(Fwd(ForallInLeftCosetsPair.Read(source))),
				Derive(func(b *Argument) {
					b.FixAs[A]("x")
					b.FixAs[A]("y")
					points := b.Conjuncts(
						b.Assume(),
						"x lies in G.carrier",
						"y lies in G.carrier")
					product := b.Have(
						"the product of the cosets of x and y is the coset of x * y",
						"set_mul(left_coset(x, group_kernel(H.one, G.carrier, f)), "+
							"    left_coset(y, group_kernel(H.one, G.carrier, f))) = "+
							"left_coset(x * y, group_kernel(H.one, G.carrier, f))",
						By(LeftCosetMulOn, source, normal, points[0], points[1]))
					b.Show(
						"the induced values are f(x * y), f(x) and f(y), and the map respects the product",
						product.Rw(),
						Simp(Fwd(InducedMapCoset), Fwd(group.MulIn)),
						By(group_homomorphism.MapMul, hom, points[0], points[1]))
				}))
			a.Do(Unfold(group_homomorphism.GroupIsomorphismDef), SplitConjAll(
				// The homomorphism's four conjuncts are the four facts in hand —
				// the quotient, the image's group on its set, the carrying and
				// the multiplicativity — named in the close once the predicate
				// is unfolded; the unfolding opens the resident homomorphism as
				// well, which is why the facts were had first.
				Case(
					"a homomorphism from the quotient to the image",
					Unfold(group_homomorphism.GroupHomomorphism),
					By(quotient, imageGroup, carries, multiplicative)),
				Case(
					"one-to-one on cosets: cosets whose induced values agree are equal",
					Simp(Fwd(functions.InjectiveOnDef.Inst(TypeBinder.BindA[Set[A]](), TypeBinder.BindB[B]()))),
					Derive(func(b *Argument) {
						s := b.FixAs[Set[A]]("s")
						t := b.FixAs[Set[A]]("t")
						parts := b.Conjuncts(
							b.Assume(),
							"s is a coset",
							"t is a coset",
							"the induced values agree")
						x, sIs := b.ObtainAs[A](
							"s is the coset of some x of G.carrier",
							"∃x:A. s = left_coset(x, group_kernel(H.one, G.carrier, f)) ∧ x ∈ G.carrier",
							By(parts[0], InLeftCosets.Read(source).At(K, s), kInC))
						y, tIs := b.ObtainAs[A](
							"t is the coset of some y of G.carrier",
							"∃y:A. t = left_coset(y, group_kernel(H.one, G.carrier, f)) ∧ y ∈ G.carrier",
							By(parts[1], InLeftCosets.Read(source).At(K, t), kInC))
						sParts := b.Conjuncts(
							sIs,
							"s is x·K",
							"x lies in G.carrier")
						tParts := b.Conjuncts(
							tIs,
							"t is y·K",
							"y lies in G.carrier")
						// Normalized: the agreement is a HYPOTHESIS about s and t, which
						// the goal rewrites above never reach, so the two coset equations
						// and the two induced values are substituted into it before the
						// close.
						agree := b.Have(
							"the induced values are f(x) and f(y), which agree",
							"f(x) = f(y)",
							By(
								Normalized,
								parts[2],
								sParts[0],
								tParts[0],
								At(Read(InducedMapCoset, hom), x),
								At(Read(InducedMapCoset, hom), y),
								sParts[1],
								tParts[1]))
						inKernel := b.Have(
							"so G.inv(x) * y lies in the kernel",
							"G.inv(x) * y ∈ group_kernel(H.one, G.carrier, f)",
							By(agree, Read(group_homomorphism.EqIffInKernel, hom), sParts[1], tParts[1]))
						b.Show(
							"x and y then determine the same coset, so s = t",
							sParts[0].Rw(),
							tParts[0].Rw(),
							By(group.LeftCosetEqOn, source, sParts[1], tParts[1], kernel, inKernel))
					})),
				Case(
					"onto the image: the cosets go into it, and a point "+
						"f(x) of it is the induced value of the coset of x",
					Derive(func(b *Argument) {
						reaches := b.Have(
							"a point f(x) of the image is the induced value of the coset of x",
							Statement{
								Binders: "∀z:B.",
								Hypotheses: []string{
									"z ∈ image(f, G.carrier)",
								},
								Conclusion: "∃s:set(A). " +
									"    s ∈ left_cosets(G.carrier, group_kernel(H.one, G.carrier, f)) ∧ induced_map(f, s) = z",
							},
							Derive(func(b *Argument) {
								b.FixAs[B]("z")
								zIn := b.Assume()
								_, fromX := b.UnpackAs[A](b.Have(
									"z is f(x) for some x of G.carrier",
									"∃x:A. z = f(x) ∧ x ∈ G.carrier",
									By(zIn, set_basic.InImage)), "x")
								zParts := b.Conjuncts(
									fromX,
									"z is f(x)",
									"x lies in G.carrier")
								b.Take(b.TermAs[Set[A]]("left_coset(x, group_kernel(H.one, G.carrier, f))"))
								b.Do(SplitConj(
									Case(
										"the coset of x is a coset of the kernel by G.carrier",
										Simp(Fwd(InLeftCosets)),
										Derive(func(d *Argument) {
											d.Take(d.TermAs[A]("x"))
											d.Show(
												"by x itself, a point of G.carrier",
												By(zParts[1]))
										})),
									Case(
										"and its induced value is f(x), which is z",
										zParts[0].Rw(),
										By(InducedMapCoset, hom, zParts[1])),
								))
							}))
						b.Show(
							"so the image of the cosets is the image of G.carrier",
							BySets(carries, reaches))
					})),
			))
		}),
})}
