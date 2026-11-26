// field_automorphism.go — the chapter: the automorphisms of a subfield M
// fixing a subfield K, as permutations of the field's type that move no
// point outside M; the group they form, where over a finite extension each
// member has an order dividing the group's size, a map of a finite extension
// that keeps its operations and fixes the base is one of them, and two of
// them that agree on generators are equal; and the field a set of them
// fixes.

package field_automorphism

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_extension"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/finite_group/finite_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/symmetric_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The definitions
// ---------------------------------------------------------------------------

// FieldAutomorphismsDef — `field_automorphisms(L, K, M)`, Aut_K(M): the
// permutations of the type that move no point outside M (the symmetric
// group of M), keep the sum and the product of members of M, and fix
// every member of K. A permutation fixing the complement of M carries M
// onto itself, so these are the automorphisms of M fixing K, each made a
// permutation of the whole type by the identity outside M.
var FieldAutomorphismsDef = fieldAutomorphismsDefThm{family.Define(registry.DefEntry{
	Name:  "FieldAutomorphismsDef",
	Key:   "prop_edccfa909457a95e",
	Const: "field_automorphisms",
	Type:  "field_ops(A) → set(A) → set(A) → set(permutation(A))",
	Equations: []string{
		"∀L:field_ops(A). ∀K M:set(A). " +
			"    field_automorphisms(L, K, M) = " +
			"    {p:permutation(A) | " +
			"        p ∈ symmetric_group(M) ∧ " +
			"        (∀x y:A. " +
			"            x ∈ M ∧ y ∈ M ⇒ " +
			"            permutation_map(p, L.add(x, y)) = " +
			"            L.add(permutation_map(p, x), permutation_map(p, y))) ∧ " +
			"        (∀x y:A. " +
			"            x ∈ M ∧ y ∈ M ⇒ " +
			"            permutation_map(p, L.mul(x, y)) = " +
			"            L.mul(permutation_map(p, x), permutation_map(p, y))) ∧ " +
			"        (∀x:A. x ∈ K ⇒ permutation_map(p, x) = x)}",
	},
})}

// GaloisGroupDef — `galois_group(L, K, M)`: the automorphisms of M fixing K
// as a group of permutations, under composition. It is Aut_K(M) for any
// K ⊆ M, whether or not M is Galois over K.
var GaloisGroupDef = galoisGroupDefThm{family.Define(registry.DefEntry{
	Name:  "GaloisGroupDef",
	Key:   "prop_e76ac631412bbd8a",
	Const: "galois_group",
	Type:  "field_ops(A) → set(A) → set(A) → group_ops(permutation(A))",
	Equations: []string{
		"∀L:field_ops(A). ∀K M:set(A). " +
			"    galois_group(L, K, M) = restrict_group(permutation_group, field_automorphisms(L, K, M))",
	},
	Deps: []registry.EntryLike{FieldAutomorphismsDef},
})}

// FixedFieldDef — `fixed_field(M, H)`: the members of M every
// permutation of H fixes.
var FixedFieldDef = fixedFieldDefThm{family.Define(registry.DefEntry{
	Name:  "FixedFieldDef",
	Key:   "prop_2ebe0d53db330207",
	Const: "fixed_field",
	Type:  "set(A) → set(permutation(A)) → set(A)",
	Equations: []string{
		"∀M:set(A). ∀H:set(permutation(A)). " +
			"    fixed_field(M, H) = {x:A | x ∈ M ∧ (∀p:permutation(A). p ∈ H ⇒ permutation_map(p, x) = x)}",
	},
})}

// ---------------------------------------------------------------------------
// The automorphisms form a group
// ---------------------------------------------------------------------------

// AutomorphismsSubgroup — Aut_K(M) is a subgroup of the permutations of
// the type, inside the symmetric group of M. Composition preserves the
// defining laws; for the inverse, apply them to inverse images in M.
var AutomorphismsSubgroup = automorphismsSubgroupThm{family.Add(registry.ProofEntry{
	Name: "AutomorphismsSubgroup",
	Key:  "prop_2d8c5317c79e1cb5",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀K M:set(A).",
		Conclusion: "subgroup(permutation_group, field_automorphisms(L, K, M)) ∧ " +
			"field_automorphisms(L, K, M) ⊆ symmetric_group(M)",
	},
		func(a *Argument, L field.FieldFact[on.L], K, M *Expr[Set[A]]) {
			permutationGroup := a.TermAs[group.GroupOps[Permutation[A]]]("permutation_group")
			symmetric := a.TermAs[Set[Permutation[A]]]("symmetric_group(M)")
			inside := a.Have(
				"an automorphism of M lies in its symmetric group",
				"field_automorphisms(L, K, M) ⊆ symmetric_group(M)",
				Unfold(FieldAutomorphismsDef),
				BySets())
			identity := a.Have(
				"the identity preserves the operations and fixes K",
				"permutation_identity ∈ field_automorphisms(L, K, M)",
				Unfold(FieldAutomorphismsDef),
				Unfold(symmetric_group.SymmetricGroupDef),
				By(symmetric_group.MapIdentity))
			compose := a.Have(
				"the composite of two automorphisms fixing K is another",
				Statement{
					Binders: "∀p q:permutation(A).",
					Hypotheses: []string{
						"p ∈ field_automorphisms(L, K, M)",
						"q ∈ field_automorphisms(L, K, M)",
					},
					Conclusion: "permutation_compose(p, q) ∈ field_automorphisms(L, K, M)",
				},
				Derive(func(b *Argument) {
					p, q := b.FixAs[Permutation[A]]("p"), b.FixAs[Permutation[A]]("q")
					both := b.Assume()
					unfolded := b.Unfolded(both, FieldAutomorphismsDef)
					laws := b.Have(
						"p and q permute M, preserve its operations and fix K",
						"p ∈ symmetric_group(M) ∧ "+
							"(∀u v:A. "+
							"    u ∈ M ∧ v ∈ M ⇒ "+
							"    permutation_map(p, u + v) = permutation_map(p, u) + permutation_map(p, v)) ∧ "+
							"(∀u v:A. "+
							"    u ∈ M ∧ v ∈ M ⇒ "+
							"    permutation_map(p, u * v) = permutation_map(p, u) * permutation_map(p, v)) ∧ "+
							"(∀u:A. u ∈ K ⇒ permutation_map(p, u) = u) ∧ "+
							"q ∈ symmetric_group(M) ∧ "+
							"(∀u v:A. "+
							"    u ∈ M ∧ v ∈ M ⇒ "+
							"    permutation_map(q, u + v) = permutation_map(q, u) + permutation_map(q, v)) ∧ "+
							"(∀u v:A. "+
							"    u ∈ M ∧ v ∈ M ⇒ "+
							"    permutation_map(q, u * v) = permutation_map(q, u) * permutation_map(q, v)) ∧ "+
							"(∀u:A. u ∈ K ⇒ permutation_map(q, u) = u)",
						BySets(unfolded))
					parts := b.Conjuncts(
						laws,
						"p permutes M",
						"p preserves sums",
						"p preserves products",
						"p fixes K",
						"q permutes M",
						"q preserves sums",
						"q preserves products",
						"q fixes K")
					pSym, pSum, pProduct, pFix := parts[0], parts[1], parts[2], parts[3]
					qSym, qSum, qProduct, qFix := parts[4], parts[5], parts[6], parts[7]
					composed := b.Have(
						"the composite satisfies the four automorphism conditions",
						"permutation_compose(p, q) ∈ symmetric_group(M) ∧ "+
							"(∀x y:A. "+
							"    x ∈ M ∧ y ∈ M ⇒ "+
							"    permutation_map(permutation_compose(p, q), x + y) = "+
							"    permutation_map(permutation_compose(p, q), x) + "+
							"    permutation_map(permutation_compose(p, q), y)) ∧ "+
							"(∀x y:A. "+
							"    x ∈ M ∧ y ∈ M ⇒ "+
							"    permutation_map(permutation_compose(p, q), x * y) = "+
							"    permutation_map(permutation_compose(p, q), x) * "+
							"    permutation_map(permutation_compose(p, q), y)) ∧ "+
							"(∀x:A. x ∈ K ⇒ permutation_map(permutation_compose(p, q), x) = x)",
						SplitConjAll(
							Case(
								"the composite still permutes M",
								By(
									pSym,
									qSym,
									symmetric_group.SymmetricGroupSubgroup.At(M),
									group.SubgroupMul.At(permutationGroup, symmetric, p, q))),
							Case(
								"the composite preserves sums",
								Derive(func(c *Argument) {
									x, y := c.FixAs[A]("x"), c.FixAs[A]("y")
									points := c.Assume()
									qx, qy := c.TermAs[A]("permutation_map(q, x)"), c.TermAs[A]("permutation_map(q, y)")
									c.Show(
										"q preserves the sum and p preserves the sum of its images in M",
										Simp(Fwd(symmetric_group.MapCompose)),
										By(
											qSym,
											points,
											qSum.At(x, y),
											pSum.At(qx, qy),
											symmetric_group.SymmetricGroupMapsInto.At(M, q, x),
											symmetric_group.SymmetricGroupMapsInto.At(M, q, y)))
								})),
							Case(
								"the composite preserves products",
								Derive(func(c *Argument) {
									x, y := c.FixAs[A]("x"), c.FixAs[A]("y")
									points := c.Assume()
									qx, qy := c.TermAs[A]("permutation_map(q, x)"), c.TermAs[A]("permutation_map(q, y)")
									c.Show(
										"q preserves the product and p preserves the product of its images in M",
										Simp(Fwd(symmetric_group.MapCompose)),
										By(
											qSym,
											points,
											qProduct.At(x, y),
											pProduct.At(qx, qy),
											symmetric_group.SymmetricGroupMapsInto.At(M, q, x),
											symmetric_group.SymmetricGroupMapsInto.At(M, q, y)))
								})),
							Case(
								"the composite fixes K",
								Derive(func(c *Argument) {
									x := c.FixAs[A]("x")
									inK := c.Assume()
									c.Show(
										"both factors fix x",
										Simp(Fwd(symmetric_group.MapCompose)),
										By(Normalized, inK, pFix.At(x), qFix.At(x)))
								}))))
					conditions := b.Conjuncts(
						composed,
						"the composite permutes M",
						"the composite preserves sums",
						"the composite preserves products",
						"the composite fixes K")
					b.Show(
						"the composite is an automorphism fixing K",
						Unfold(FieldAutomorphismsDef),
						BySets(conditions[0], conditions[1], conditions[2], conditions[3]))
				}))
			inverse := a.Have(
				"the inverse of an automorphism fixing K is another",
				Statement{
					Binders: "∀p:permutation(A).",
					Hypotheses: []string{
						"p ∈ field_automorphisms(L, K, M)",
					},
					Conclusion: "permutation_inverse(p) ∈ field_automorphisms(L, K, M)",
				},
				Derive(func(b *Argument) {
					p := b.FixAs[Permutation[A]]("p")
					aut := b.Assume()
					unfolded := b.Unfolded(aut, FieldAutomorphismsDef)
					laws := b.Have(
						"p permutes M, preserves its operations and fixes K",
						"p ∈ symmetric_group(M) ∧ "+
							"(∀u v:A. "+
							"    u ∈ M ∧ v ∈ M ⇒ "+
							"    permutation_map(p, u + v) = permutation_map(p, u) + permutation_map(p, v)) ∧ "+
							"(∀u v:A. "+
							"    u ∈ M ∧ v ∈ M ⇒ "+
							"    permutation_map(p, u * v) = permutation_map(p, u) * permutation_map(p, v)) ∧ "+
							"(∀u:A. u ∈ K ⇒ permutation_map(p, u) = u)",
						BySets(unfolded))
					parts := b.Conjuncts(
						laws,
						"p permutes M",
						"p preserves sums",
						"p preserves products",
						"p fixes K")
					pSym, pSum, pProduct, pFix := parts[0], parts[1], parts[2], parts[3]
					q := b.TermAs[Permutation[A]]("permutation_inverse(p)")
					qSym := b.Have(
						"the inverse still permutes M",
						"permutation_inverse(p) ∈ symmetric_group(M)",
						By(
							pSym,
							symmetric_group.SymmetricGroupSubgroup.At(M),
							group.SubgroupInv.At(permutationGroup, symmetric, p)))
					preserved := b.Have(
						"the inverse preserves the operations and fixes K",
						"(∀x y:A. "+
							"    x ∈ M ∧ y ∈ M ⇒ "+
							"    permutation_map(permutation_inverse(p), x + y) = "+
							"    permutation_map(permutation_inverse(p), x) + permutation_map(permutation_inverse(p), y)) ∧ "+
							"(∀x y:A. "+
							"    x ∈ M ∧ y ∈ M ⇒ "+
							"    permutation_map(permutation_inverse(p), x * y) = "+
							"    permutation_map(permutation_inverse(p), x) * permutation_map(permutation_inverse(p), y)) ∧ "+
							"(∀x:A. x ∈ K ⇒ permutation_map(permutation_inverse(p), x) = x)",
						SplitConjAll(
							Case(
								"the inverse preserves sums",
								Derive(func(c *Argument) {
									x, y := c.FixAs[A]("x"), c.FixAs[A]("y")
									points := c.Assume()
									qx, qy :=
										c.TermAs[A]("permutation_map(permutation_inverse(p), x)"),
										c.TermAs[A]("permutation_map(permutation_inverse(p), y)")
									forward := c.Have(
										"p sends the sum of inverse images to x + y",
										"permutation_map(p, "+
											"    permutation_map(permutation_inverse(p), x) + permutation_map(permutation_inverse(p), y)) = "+
											"x + y",
										By(
											qSym,
											points,
											symmetric_group.MapInverseRight.At(p, x),
											symmetric_group.MapInverseRight.At(p, y),
											pSum.At(qx, qy),
											symmetric_group.SymmetricGroupMapsInto.At(M, q, x),
											symmetric_group.SymmetricGroupMapsInto.At(M, q, y)))
									c.Show(
										"the left inverse returns the sum of inverse images",
										By(
											forward,
											symmetric_group.MapInverse.At(
												p,
												c.TermAs[A](
													"permutation_map(permutation_inverse(p), x) + permutation_map(permutation_inverse(p), y)"))))
								})),
							Case(
								"the inverse preserves products",
								Derive(func(c *Argument) {
									x, y := c.FixAs[A]("x"), c.FixAs[A]("y")
									points := c.Assume()
									qx, qy :=
										c.TermAs[A]("permutation_map(permutation_inverse(p), x)"),
										c.TermAs[A]("permutation_map(permutation_inverse(p), y)")
									forward := c.Have(
										"p sends the product of inverse images to x * y",
										"permutation_map(p, "+
											"    permutation_map(permutation_inverse(p), x) * permutation_map(permutation_inverse(p), y)) = "+
											"x * y",
										By(
											qSym,
											points,
											symmetric_group.MapInverseRight.At(p, x),
											symmetric_group.MapInverseRight.At(p, y),
											pProduct.At(qx, qy),
											symmetric_group.SymmetricGroupMapsInto.At(M, q, x),
											symmetric_group.SymmetricGroupMapsInto.At(M, q, y)))
									c.Show(
										"the left inverse returns the product of inverse images",
										By(
											forward,
											symmetric_group.MapInverse.At(
												p,
												c.TermAs[A](
													"permutation_map(permutation_inverse(p), x) * permutation_map(permutation_inverse(p), y)"))))
								})),
							Case(
								"the inverse fixes K",
								Derive(func(c *Argument) {
									x := c.FixAs[A]("x")
									inK := c.Assume()
									c.Show(
										"the inverse returns a point already fixed by p",
										By(Normalized, inK, pFix.At(x), symmetric_group.MapInverse.At(p, x)))
								}))))
					conditions := b.Conjuncts(
						preserved,
						"the inverse preserves sums",
						"the inverse preserves products",
						"the inverse fixes K")
					b.Show(
						"the inverse is an automorphism fixing K",
						Unfold(FieldAutomorphismsDef),
						BySets(conditions[0], conditions[1], conditions[2], qSym))
				}))
			a.Show(
				"the defining subgroup conditions hold, inside the symmetric group of M",
				Unfold(group.SubgroupDef),
				BySets(compose, inverse, identity, inside))
		}),
})}

// GaloisGroupCarrier — the Galois group's carrier is the set of
// automorphisms it is made of.
var GaloisGroupCarrier = galoisGroupCarrierThm{family.Add(registry.ProofEntry{
	Name: "GaloisGroupCarrier",
	Key:  "prop_49361f4cfe25afa1",
	Build: family.Theorem("∀L:field_ops(A). ∀K M:set(A). "+
		"    galois_group(L, K, M).carrier = field_automorphisms(L, K, M)",
		func(a *Argument, L *Expr[FieldOps[A]], K, M *Expr[Set[A]]) {
			a.Show(
				"restricting the permutation group to the automorphisms gives them as its carrier",
				Simp(Fwd(GaloisGroupDef)),
				Basic())
		}),
})}

// GaloisGroupOn — the Galois group Aut_K(M) is a group on its set, under
// composition: it is a subgroup of the permutation group on the universe.
var GaloisGroupOn = galoisGroupOnThm{family.Add(registry.ProofEntry{
	Name: "GaloisGroupOn",
	Key:  "prop_e0ae9e5b24bc146d",
	Build: family.Theorem(Statement{
		Binders:    "∀L:field_on(A). ∀K M:set(A).",
		Conclusion: "group_on(galois_group(L, K, M))",
	},
		func(a *Argument, L field.FieldFact[on.L], K, M *Expr[Set[A]]) {
			permutations := a.TermAs[group.GroupOps[Permutation[A]]]("permutation_group")
			automorphisms := a.TermAs[Set[Permutation[A]]]("field_automorphisms(L, K, M)")
			ambient := a.Have(
				"the permutations form a group on their universe carrier",
				"group_on⟨A:permutation(A)⟩(permutation_group)",
				Derive(func(b *Argument) {
					onUniverse := b.Have(
						"the whole-type permutation group is a group on the universe",
						"group_on(restrict_group(permutation_group, 𝕌⟨A:permutation(A)⟩))",
						By(symmetric_group.SymmetricGroup.Inst[A](), group.GroupOnUniverse))
					unrestricted := b.Simplified(onUniverse, Fwd(symmetric_group.RestrictPermutationGroupUniverse))
					b.Show(
						"restricting this group to the universe preserves its carrier",
						By(unrestricted))
				}))
			subgroup := a.Have(
				"the automorphisms fixing K form a subgroup",
				"subgroup(permutation_group, field_automorphisms(L, K, M))",
				By(L, AutomorphismsSubgroup))
			a.Show(
				"the subgroup is a group on its own set",
				By(
					Normalized,
					ambient,
					subgroup,
					GaloisGroupDef.At(a.TermAs[FieldOps[A]]("L"), K, M),
					group.SubgroupGroupOn.At(permutations, automorphisms)))
		}),
})}

// GaloisGroupSubgroup — the subgroups of the Galois group Aut_K(M) are the
// groups of permutations made of automorphisms of M fixing K. Both sides say
// that H holds the identity and is closed under composition and inverse; the
// Galois group's carrier is Aut_K(M), and the permutation group's is every
// permutation.
var GaloisGroupSubgroup = galoisGroupSubgroupThm{family.Add(registry.ProofEntry{
	Name: "GaloisGroupSubgroup",
	Key:  "prop_785bb63211a8ea72",
	Build: family.Theorem("∀L:field_ops(A). ∀K M:set(A). ∀H:set(permutation(A)). "+
		"    subgroup(galois_group(L, K, M), H) ⇔ "+
		"    subgroup(permutation_group, H) ∧ H ⊆ field_automorphisms(L, K, M)",
		func(a *Argument, L *Expr[FieldOps[A]], K, M *Expr[Set[A]], H *Expr[Set[Permutation[A]]]) {
			a.Show(
				"both sides ask that H hold the identity and be "+
					"closed under composition and inverse, inside Aut_K(M)",
				Simp(Fwd(group.SubgroupDef), Fwd(GaloisGroupDef)),
				By(set_order.SubsetUniv.At(H)))
		}),
})}

// AutomorphismsTowerSubgroup — for K ⊆ E, the automorphisms fixing E form a
// subgroup of the Galois group of M over K: they fix K too, and they form a
// group of permutations.
var AutomorphismsTowerSubgroup = automorphismsTowerSubgroupThm{family.Add(registry.ProofEntry{
	Name: "AutomorphismsTowerSubgroup",
	Key:  "prop_fd9a8bafd43a97aa",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀K E M:set(A).",
		Hypotheses: []string{
			"K ⊆ E",
		},
		Conclusion: "subgroup(galois_group(L, K, M), field_automorphisms(L, E, M))",
	},
		func(a *Argument, L field.FieldFact[on.L], K, E, M *Expr[Set[A]], smaller Fact) {
			autE := a.TermAs[Set[Permutation[A]]]("field_automorphisms(L, E, M)")
			a.Show(
				"Aut_E(M) lies in Aut_K(M) and is a subgroup of the permutations",
				By(
					smaller,
					AutomorphismsAntitone.Read(L).At(K, E, M),
					AutomorphismsSubgroup.Read(L).At(E, M),
					GaloisGroupSubgroup.At(a.TermAs[FieldOps[A]]("L"), K, M, autE)))
		}),
})}

// AutomorphismOrderFacts — an automorphism of a finite extension has an order,
// and the order divides the size of the automorphism group. The group is
// finite, so two powers of s below |G| + 1 coincide and some positive power is
// the identity (symmetric_group.PermutationPowerRepeat); a least one exists and
// is the order (symmetric_group.PermutationOrderUnique), and Lagrange divides
// |G| by the size of the cyclic subgroup, which is the order
// (symmetric_group.PowersSubgroup).
var AutomorphismOrderFacts = automorphismOrderFactsThm{family.Add(registry.ProofEntry{
	Name: "AutomorphismOrderFacts",
	Key:  "prop_d7fa58dfda9a80fe",
	Build: family.Theorem(Statement{
		Abbrev: Abbrev{
			{Name: "power", Text: "λs:permutation(A). λd:num. " +
				"    monoid_pow⟨A:permutation(A)⟩( " +
				"        (λp:permutation(A). λq:permutation(A). permutation_compose(p, q)), " +
				"        permutation_identity⟨A:A⟩, " +
				"        s, " +
				"        d)"},
		},
		Binders: "∀M:field_on(A). ∀K L:set(A). ∀s:permutation(A).",
		Hypotheses: []string{
			"subfield(M, K)",
			"subfield(M, L)",
			"K ⊆ L",
			"finite_extension(M, K, L)",
			"s ∈ field_automorphisms(M, K, L)",
		},
		Conclusion: "0 < permutation_order(s) ∧ " +
			"«power»(s, permutation_order(s)) = permutation_identity ∧ " +
			"(∀d:num. 0 < d ∧ «power»(s, d) = permutation_identity ⇒ permutation_order(s) ≤ d) ∧ " +
			"permutation_order(s) ∣ card(field_automorphisms(M, K, L))",
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			K, L *Expr[Set[A]],
			s *Expr[Permutation[A]],
			subK, subL, KInL, finiteL, inG Fact,
		) {
			G := a.TermAs[Set[Permutation[A]]]("field_automorphisms(M, K, L)")
			powerMap := a.TermAs[Fun[Nat, Permutation[A]]]("«power»(s)")
			bound := a.TermAs[Nat]("card(field_automorphisms(M, K, L))")
			finiteG := a.Have(
				"the automorphism group is finite",
				"finite(field_automorphisms(M, K, L))",
				By(subK, subL, KInL, finiteL, AutomorphismsBound.Read(M).At(K, L)))
			groupOfL := a.Have(
				"the automorphisms are a subgroup of the permutations",
				"subgroup(permutation_group, field_automorphisms(M, K, L))",
				By(AutomorphismsSubgroup.Read(M).At(K, L)))
			powersIn := a.Have(
				"the powers of s stay in the group",
				"∀n:num. «power»(s, n) ∈ field_automorphisms(M, K, L)",
				a.ForEach(func(n *Expr[Nat]) Action {
					return By(groupOfL, inG, At(symmetric_group.PermutationPowerIn, G, s, n))
				}))
			annihilatorExists := a.Have(
				"some positive power of s is the identity",
				"∃d:num. 0 < d ∧ «power»(s, d) = permutation_identity",
				Derive(func(b *Argument) {
					none := b.SupposeNot()
					distinct := b.Have(
						"the exponents up to |G| give distinct powers",
						"injective_on({i:num | i ≤ card(field_automorphisms(M, K, L))}, «power»(s))",
						Derive(func(c *Argument) {
							repeats := c.Have(
								"a repeat of powers would give a positive annihilator",
								"∀i j:num. i < j ∧ «power»(s, i) = «power»(s, j) ⇒ ⊥",
								Derive(func(d *Argument) {
									i, j := d.FixAs[Nat]("i"), d.FixAs[Nat]("j")
									repeat := d.Assume()
									d.Show(
										"the gap annihilates s",
										By(repeat, none, At(symmetric_group.PermutationPowerRepeat, s, i, j)))
								}))
							c.Do(Unfold(functions.InjectiveOnDef))
							i, j := c.FixAs[Nat]("i"), c.FixAs[Nat]("j")
							same := c.Assume()
							c.Show(
								"neither exponent is below the other",
								ByArith(same, repeats.At(i, j), repeats.At(j, i)))
						}))
					segment := b.TermAs[Set[Nat]]("{i:num | i ≤ card(field_automorphisms(M, K, L))}")
					sized := b.Have(
						"their powers number |G| + 1",
						"has_size(image(«power»(s), {i:num | i ≤ card(field_automorphisms(M, K, L))}), "+
							"    card(field_automorphisms(M, K, L)) + 1)",
						By(
							distinct,
							num_segment.HasSizeBelow.At(bound),
							cardinality.HasSizeImageInj.At(
								powerMap, segment, b.TermAs[Nat]("card(field_automorphisms(M, K, L)) + 1"))))
					inside := b.Have(
						"their powers lie in the group",
						"image(«power»(s), {i:num | i ≤ card(field_automorphisms(M, K, L))}) ⊆ "+
							"field_automorphisms(M, K, L)",
						BySets(powersIn))
					b.Show(
						"a subset of G has at most |G| members",
						ByArith(
							sized,
							cardinality.HasSizeDef,
							inside,
							finiteG,
							cardinality.BoundedCountOfSubset.At(
								b.TermAs[Set[Permutation[A]]](
									"image(«power»(s), {i:num | i ≤ card(field_automorphisms(M, K, L))})"),
								G,
								bound)))
				}))
			annihilator := a.TermAs[Fun[Nat, Bool]]("λd:num. 0 < d ∧ «power»(s, d) = permutation_identity")
			e, leastAnnihilator := a.ObtainAs[Nat](
				"take the least positive annihilating exponent",
				"∃e:num. "+
					"    (0 < e ∧ «power»(s, e) = permutation_identity) ∧ "+
					"    (∀m:num. m < e ⇒ ¬(0 < m ∧ «power»(s, m) = permutation_identity))",
				By(annihilatorExists, At(nat_order.WellOrdering, annihilator)))
			parts := a.Conjuncts(
				leastAnnihilator,
				"e is positive",
				"s^e is the identity",
				"no smaller exponent is one")
			least := a.Have(
				"e is at most every positive annihilator",
				"∀d:num. 0 < d ∧ «power»(s, d) = permutation_identity ⇒ e ≤ d",
				Derive(func(b *Argument) {
					d := b.FixAs[Nat]("d")
					annihilates := b.Assume()
					b.Show(
						"a smaller one is excluded",
						ByArith(annihilates, parts[2].At(d)))
				}))
			order := a.Have(
				"e is the order of s",
				"permutation_order(s) = e",
				By(parts[0], parts[1], least, At(symmetric_group.PermutationOrderUnique, s, e)))
			cyclic := a.TermAs[Set[Permutation[A]]]("{«power»(s, j) | j:num | j < e}")
			subgroupOfPowers := a.Have(
				"the powers below e are a subgroup of e members",
				"subgroup(permutation_group, {«power»(s, j) | j:num | j < e}) ∧ "+
					"has_size({«power»(s, j) | j:num | j < e}, e)",
				By(parts[0], parts[1], least, At(symmetric_group.PowersSubgroup, s, e)))
			cyclicInG := a.Have(
				"they lie in the group",
				"{«power»(s, j) | j:num | j < e} ⊆ field_automorphisms(M, K, L)",
				BySets(powersIn))
			cyclicData := a.Conjuncts(
				subgroupOfPowers,
				"the powers below e are a subgroup",
				"there are e of them")
			divides := a.Have(
				"Lagrange divides |G| by the size of the cyclic subgroup",
				"e ∣ card(field_automorphisms(M, K, L))",
				By(
					cyclicData[0],
					cyclicInG,
					groupOfL,
					finiteG,
					symmetric_group.RestrictPermutationGroupUniverse,
					cyclicData[1],
					cardinality.CardOfSized.At(cyclic, e),
					finite_group.LagrangeDivides.Read(symmetric_group.SymmetricGroup).At(cyclic, G)))
			a.Do(order.Rw())
			a.Show(
				"e is positive, s^e is the identity, no smaller positive power is, and e divides |G|",
				By(parts[0], parts[1], least, divides))
		}),
})}

// EmbeddingPermutation — an embedding of M in L that fixes K and maps M
// onto M is represented on M by an automorphism of M over K: extend it by
// the identity off M and take the permutation of that bijection.
var EmbeddingPermutation = embeddingPermutationThm{family.Add(registry.ProofEntry{
	Name: "EmbeddingPermutation",
	Key:  "prop_179619e2803daf90",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀K M:set(A). ∀f:(A → A).",
		Hypotheses: []string{
			"subfield(L, M)",
			"ring_homomorphism(restrict_ring(field_ring(L), M), field_ring(L), f)",
			"∀x:A. x ∈ K ⇒ f(x) = x",
			"image(f, M) = M",
		},
		Conclusion: "∃p:permutation(A). " +
			"    p ∈ field_automorphisms(L, K, M) ∧ (∀x:A. x ∈ M ⇒ permutation_map(p, x) = f(x))",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			K, M *Expr[Set[A]],
			f *Arrow[A, A],
			subfield, hom, fixesK, onto Fact,
		) {
			w, wDef := a.LetAs[Fun[A, A]]("w", "λx:A. COND(x ∈ M, f(x), x)")
			h, hDef := a.LetAs[Fun[A, A]]("h", "λy:A. COND(y ∈ M, inverse_on(M, f, y), y)")
			r, rDef := a.LetAs[Permutation[A]]("r", "permutation_of_map(w)")
			embeddingInjective := a.Have(
				"the field embedding is injective, as every homomorphism out of a subfield is",
				"injective_on(M, f)",
				By(
					L,
					subfield,
					hom,
					ring_homomorphism.SubfieldHomomorphismEmbedding.Read(L).At(a.TermAs[FieldOps[A]]("L"), M, f)))
			embeddingStable := a.Have(
				"the embedding maps M into itself",
				"∀x:A. x ∈ M ⇒ f(x) ∈ M",
				BySets(onto))
			mutualInverses := a.Have(
				"the extended map and its chosen inverse are mutual inverses",
				"∀x:A. h(w(x)) = x ∧ w(h(x)) = x",
				Derive(func(b *Argument) {
					x := b.FixAs[A]("x")
					b.Cases(b.TermAs[Bool]("x ∈ M"))
					b.When(
						"x lies in M, where w is f and h inverts it",
						func(c *Argument, inM Fact) {
							c.Show(
								"f and its inverse on M undo each other at x",
								By(
									Normalized,
									embeddingStable.At(x),
									hDef,
									wDef,
									onto,
									embeddingInjective,
									inM,
									functions.InverseOnLeft.At(M, f, x),
									functions.InverseOnRight.At(M, f, x),
									functions.InverseOnIn.At(M, f, x)))
						})
					b.Otherwise(
						"x lies off M, where w and h are the identity",
						func(c *Argument, outside Fact) {
							c.Show(
								"neither map moves x",
								By(Normalized, outside, hDef, wDef))
						})
				}))
			globalBijection := a.Have(
				"extending by the identity gives a bijection of the ambient type",
				"injective_on(𝕌, w) ∧ image(w, 𝕌) = 𝕌",
				By(
					mutualInverses,
					functions.TwoSidedInverseBijection.At(a.TermAs[Set[A]]("𝕌"), a.TermAs[Set[A]]("𝕌"), w, h),
					set_basic.InUniv))
			permutationRepresentsMap := a.Have(
				"the canonical permutation represents the extended map",
				"permutation_map(r) = w",
				By(Normalized, rDef, globalBijection, symmetric_group.PermutationMembership.At(w)))
			permutationValues := a.Have(
				"the permutation is the embedding on M and the identity outside it",
				"∀x:A. (x ∈ M ⇒ permutation_map(r, x) = f(x)) ∧ (x ∉ M ⇒ permutation_map(r, x) = x)",
				By(Normalized, wDef, permutationRepresentsMap))
			fieldPermutation := a.Have(
				"the permutation belongs to the symmetric group of M",
				"r ∈ symmetric_group(M)",
				By(permutationValues, symmetric_group.InSymmetricGroup.At(M, r)))
			permutationOperations := a.Have(
				"the permutation preserves field addition and multiplication",
				Statement{
					Binders: "∀x y:A.",
					Hypotheses: []string{
						"x ∈ M",
						"y ∈ M",
					},
					Conclusion: "permutation_map(r, x + y) = permutation_map(r, x) + permutation_map(r, y) ∧ " +
						"permutation_map(r, x * y) = permutation_map(r, x) * permutation_map(r, y)",
				},
				Derive(func(b *Argument) {
					x := b.FixAs[A]("x")
					y := b.FixAs[A]("y")
					bothIn := b.Assume()
					b.Show(
						"on M the permutation is f, which preserves both operations",
						By(
							Normalized,
							permutationValues.At(x),
							permutationValues.At(y),
							permutationValues.At(b.TermAs[A]("x + y")),
							permutationValues.At(b.TermAs[A]("x * y")),
							bothIn,
							subfield,
							field.SubfieldAdd.At(b.TermAs[FieldOps[A]]("L"), M, x, y),
							field.SubfieldMul.At(b.TermAs[FieldOps[A]]("L"), M, x, y),
							ring_homomorphism.MapAdd.Read(hom).AsFact().At(x, y),
							ring_homomorphism.MapMul.Read(hom).AsFact().At(x, y)))
				}))
			permutationFixesK := a.Have(
				"the permutation fixes K",
				"∀x:A. x ∈ K ⇒ permutation_map(r, x) = x",
				BySets(fixesK, permutationValues))
			automorphism := a.Have(
				"the permutation is an automorphism over K",
				"r ∈ field_automorphisms(L, K, M)",
				Unfold(FieldAutomorphismsDef),
				BySets(permutationOperations, permutationFixesK, fieldPermutation))
			a.Take(r)
			a.Show(
				"r is an automorphism over K and agrees with f on M",
				By(automorphism, permutationValues))
		}),
})}

// FiniteSubfieldAutomorphism — a map on l that keeps sums, products and one,
// fixes k and carries l into itself is an automorphism of l over k, when l is
// finite over k: it is a k-linear injection of a finite-dimensional space, so
// onto (field_extension.FiniteEmbeddingOnto).
var FiniteSubfieldAutomorphism = finiteSubfieldAutomorphismThm{family.Add(registry.ProofEntry{
	Name: "FiniteSubfieldAutomorphism",
	Key:  "prop_9bbb89d3353e7304",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k l:set(A). ∀f:(A → A).",
		Hypotheses: []string{
			"subfield(M, k)",
			"subfield(M, l)",
			"k ⊆ l",
			"finite_extension(M, k, l)",
			"∀x y:A. x ∈ l ∧ y ∈ l ⇒ f(x + y) = f(x) + f(y)",
			"∀x y:A. x ∈ l ∧ y ∈ l ⇒ f(x * y) = f(x) * f(y)",
			"f(M.one) = M.one",
			"∀x:A. x ∈ k ⇒ f(x) = x",
			"∀x:A. x ∈ l ⇒ f(x) ∈ l",
		},
		Conclusion: "∃p:permutation(A). " +
			"    p ∈ field_automorphisms(M, k, l) ∧ (∀x:A. x ∈ l ⇒ permutation_map(p, x) = f(x))",
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			k, l *Expr[Set[A]],
			f *Expr[Fun[A, A]],
			subK, subL, kInL, finiteL, sums, products, unit, fixesK, into Fact,
		) {
			m := a.TermAs[FieldOps[A]]("M")
			lInCarrier := a.Have(
				"l lies in M",
				"l ⊆ M.carrier",
				By(subL, field.SubfieldSubset.At(m, l)))
			rings := a.Have(
				"l and M are commutative rings",
				"comm_ring_on(restrict_ring(field_ring(M), l)) ∧ comm_ring_on(field_ring(M))",
				By(subL, field.RingOn.Read(M), field.SubfieldCommRing.Read(M).At(l)))
			values := a.Have(
				"f carries l into M",
				"∀x:A. x ∈ l ⇒ f(x) ∈ M.carrier",
				BySets(into, lInCarrier))
			ringsSpelled := a.Simplified(rings, Fwd(module_record.RestrictRingDef), Fwd(field.FieldRingDef))
			homomorphism := a.Have(
				"f is a ring homomorphism from l to M",
				"ring_homomorphism(restrict_ring(field_ring(M), l), field_ring(M), f)",
				Simp(
					Fwd(ring_homomorphism.RingHomomorphism),
					Fwd(module_record.RestrictRingDef),
					Fwd(field.FieldRingDef)),
				By(ringsSpelled, values, sums, products, unit))
			inside := a.Have(
				"its image lies in l",
				"image(f, l) ⊆ l",
				BySets(into))
			onto := a.Have(
				"a k-linear embedding of a finite extension is onto",
				"image(f, l) = l",
				By(
					subK,
					subL,
					kInL,
					finiteL,
					homomorphism,
					fixesK,
					inside,
					field_extension.FiniteEmbeddingOnto.Read(M).At(k, l, f)))
			a.Show(
				"so it comes from an automorphism of l over k",
				By(subL, homomorphism, fixesK, onto, EmbeddingPermutation.Read(M).At(k, l, f)))
		}),
})}

// AutomorphismFixesUnits — an automorphism of a subfield M fixes zero and
// one: p(zero) is its own double, so zero; p(one) is its own square, and
// not zero since p is one-to-one, so one.
var AutomorphismFixesUnits = automorphismFixesUnitsThm{family.Add(registry.ProofEntry{
	Name: "AutomorphismFixesUnits",
	Key:  "prop_aa69fad0ded70b61",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀K M:set(A). ∀p:permutation(A).",
		Hypotheses: []string{
			"subfield(L, M)",
			"p ∈ field_automorphisms(L, K, M)",
		},
		Conclusion: "permutation_map(p, L.zero) = L.zero ∧ permutation_map(p, L.one) = L.one",
	},
		func(a *Argument, L field.FieldFact[on.L], K, M *Expr[Set[A]], p *Expr[Permutation[A]], h Fact) {
			parts := a.Conjuncts(
				h,
				"M is a subfield of L",
				"p is an automorphism of M fixing K")
			subfield, aut := parts[0], parts[1]
			ring := field.RingOn.Read(L)
			laws := a.Have(
				"p permutes M and keeps its sums and products",
				"p ∈ symmetric_group(M) ∧ "+
					"(∀u v:A. "+
					"    u ∈ M ∧ v ∈ M ⇒ "+
					"    permutation_map(p, u + v) = permutation_map(p, u) + permutation_map(p, v)) ∧ "+
					"(∀u v:A. "+
					"    u ∈ M ∧ v ∈ M ⇒ permutation_map(p, u * v) = permutation_map(p, u) * permutation_map(p, v))",
				BySets(a.Unfolded(aut, FieldAutomorphismsDef)))
			kept := a.Conjuncts(
				laws,
				"p permutes M",
				"p keeps sums on M",
				"p keeps products on M")
			permutes, sums, products := kept[0], kept[1], kept[2]
			inL := a.Have(
				"M lies in L",
				"M ⊆ L.carrier",
				By(subfield, field.SubfieldSubset))
			units := a.Have(
				"zero and one lie in the subfield M",
				"L.zero ∈ M ∧ L.one ∈ M",
				By(subfield, field.SubfieldZero, field.SubfieldOne))
			zero, one := a.TermAs[A]("L.zero"), a.TermAs[A]("L.one")
			values := a.Have(
				"so p(zero) and p(one) lie in M, and in L",
				"permutation_map(p, L.zero) ∈ L.carrier ∧ permutation_map(p, L.one) ∈ L.carrier",
				BySets(
					permutes,
					units,
					inL,
					symmetric_group.SymmetricGroupMapsInto.At(M, p, zero),
					symmetric_group.SymmetricGroupMapsInto.At(M, p, one)))
			sumAtZero := a.Have(
				"p keeps the sum zero + zero",
				"permutation_map(p, L.zero + L.zero) = permutation_map(p, L.zero) + permutation_map(p, L.zero)",
				By(units, sums.At(zero, zero)))
			zeroDoubled := a.Have(
				"zero is its own double",
				"L.zero + L.zero = L.zero",
				ByArith(ring))
			doubled := a.Have(
				"so p(zero) is its own double",
				"permutation_map(p, L.zero) = permutation_map(p, L.zero) + permutation_map(p, L.zero)",
				By(Normalized, sumAtZero, zeroDoubled))
			fixesZero := a.Have(
				"so p(zero) = zero",
				"permutation_map(p, L.zero) = L.zero",
				ByArith(ring, doubled, values))
			nonzero := a.Have(
				"p is one-to-one and one ≠ zero, so p(one) ≠ p(zero) = zero",
				"permutation_map(p, L.one) ≠ L.zero",
				By(
					Normalized,
					fixesZero,
					symmetric_group.MapInverse.At(p, one),
					symmetric_group.MapInverse.At(p, zero),
					field.OneNotZeroOn.Read(L)))
			oneSquared := a.Have(
				"one is its own square",
				"L.one * L.one = L.one",
				ByArith(ring))
			idempotent := a.Have(
				"p keeps the product one · one, so p(one) p(one) = p(one)",
				"permutation_map(p, L.one) * permutation_map(p, L.one) = permutation_map(p, L.one)",
				By(Normalized, oneSquared, units, products.At(one, one)))
			inverse := a.Have(
				"p(one) ≠ zero has an inverse in L",
				"L.inv(permutation_map(p, L.one)) * permutation_map(p, L.one) = L.one",
				By(nonzero, values, field.MulLeftInverseOn.Read(L)))
			inverseIn := a.Have(
				"which lies in L",
				"L.inv(permutation_map(p, L.one)) ∈ L.carrier",
				By(values, field.InvIn.Read(L)))
			pOne := a.TermAs[A]("permutation_map(p, L.one)")
			fixesOne := a.Have(
				"cancel p(one) from p(one) p(one) = p(one)",
				"permutation_map(p, L.one) = L.one",
				ByArith(
					ring,
					Scaled(a.TermAs[A]("L.inv(permutation_map(p, L.one))"), idempotent),
					Scaled(pOne, inverse),
					inverse,
					inverseIn,
					values))
			a.Show(
				"p fixes zero and one",
				By(fixesZero, fixesOne))
		}),
})}

// AutomorphismRingHomomorphism — an automorphism of M is a ring
// homomorphism of the field M: it keeps M, sums and products by its
// definition, and it fixes one.
var AutomorphismRingHomomorphism = automorphismRingHomomorphismThm{family.Add(registry.ProofEntry{
	Name: "AutomorphismRingHomomorphism",
	Key:  "prop_51533e61e51cdc4d",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀K M:set(A). ∀q:permutation(A).",
		Hypotheses: []string{
			"subfield(L, M)",
			"q ∈ field_automorphisms(L, K, M)",
		},
		Conclusion: "ring_homomorphism(field_ring(restrict_field(L, M)), " +
			"    field_ring(restrict_field(L, M)), " +
			"    permutation_map(q))",
	},
		func(a *Argument, L field.FieldFact[on.L], K, M *Expr[Set[A]], q *Expr[Permutation[A]], h Fact) {
			restricted := a.Have(
				"M carries the restricted field",
				"field_on(restrict_field(L, M))",
				By(h, field.SubfieldFieldOn.Read(L).At(M)))
			laws := a.Have(
				"q permutes M and preserves its sums and products",
				"q ∈ symmetric_group(M) ∧ "+
					"(∀u v:A. "+
					"    u ∈ M ∧ v ∈ M ⇒ "+
					"    permutation_map(q, u + v) = permutation_map(q, u) + permutation_map(q, v)) ∧ "+
					"(∀u v:A. "+
					"    u ∈ M ∧ v ∈ M ⇒ permutation_map(q, u * v) = permutation_map(q, u) * permutation_map(q, v))",
				BySets(a.Unfolded(h, FieldAutomorphismsDef)))
			into := a.Have(
				"q maps M into M",
				"∀y:A. y ∈ M ⇒ permutation_map(q, y) ∈ M",
				By(laws, symmetric_group.SymmetricGroupMapsInto))
			units := a.Have(
				"q fixes zero and one",
				"permutation_map(q, L.zero) = L.zero ∧ permutation_map(q, L.one) = L.one",
				By(h, AutomorphismFixesUnits.Read(L).At(K, M, q)))
			a.Show(
				"these are the unital ring homomorphism laws on the restricted field",
				Simp(Fwd(ring_homomorphism.RingHomomorphism)),
				By(field.RingOn.Read(restricted), into, units, laws))
		}),
})}

// AutomorphismPermutesRoots — an automorphism of M fixing K carries a
// root in M of a polynomial over K to another root of it: polynomial
// evaluation commutes with its ring map, and its coefficients are fixed.
var AutomorphismPermutesRoots = automorphismPermutesRootsThm{family.Add(registry.ProofEntry{
	Name: "AutomorphismPermutesRoots",
	Key:  "prop_2e62c07a5628e436",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀K M:set(A). ∀f:(num → A). ∀p:permutation(A). ∀x:A.",
		Hypotheses: []string{
			"subfield(L, M)",
			"K ⊆ M",
			"p ∈ field_automorphisms(L, K, M)",
			"polynomial_over(K, f)",
			"x ∈ M",
			"polynomial_eval(f, x) = L.zero",
		},
		Conclusion: "polynomial_eval(f, permutation_map(p, x)) = L.zero",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			K, M *Expr[Set[A]],
			f *Arrow[Nat, A],
			p *Expr[Permutation[A]],
			x *Expr[A],
			h Fact,
		) {
			restricted := a.Have(
				"M carries the restricted field",
				"field_on(restrict_field(L, M))",
				By(h, field.SubfieldFieldOn.Read(L).At(M)))
			parts := a.Conjuncts(
				h,
				"M is a subfield of L",
				"K lies in M",
				"p is an automorphism of M fixing K",
				"f is a polynomial over K",
				"x lies in M",
				"f vanishes at x")
			subM, nested, aut, over, inM, root := parts[0], parts[1], parts[2], parts[3], parts[4], parts[5]
			fixesK := a.Have(
				"p fixes every coefficient in K",
				"∀u:A. u ∈ K ⇒ permutation_map(p, u) = u",
				BySets(a.Unfolded(aut, FieldAutomorphismsDef)))
			units := a.Have(
				"p fixes zero and one",
				"permutation_map(p, L.zero) = L.zero ∧ permutation_map(p, L.one) = L.one",
				By(subM, aut, AutomorphismFixesUnits.Read(L).At(K, M, p)))
			F := a.TermAs[FieldOps[A]]("restrict_field(L, M)")
			π := a.TermAs[Fun[A, A]]("permutation_map(p)")
			coefficientsFixed := a.Have(
				"mapping the coefficients leaves f unchanged",
				"(λi:num. permutation_map(p, f(i))) = f",
				Derive(func(b *Argument) {
					b.Do(Funext())
					i := b.FixAs[Nat]("i")
					b.Show(
						"the coefficient lies in K and is fixed by p",
						By(polynomial.CoefficientIn.Read(over).At(i), fixesK.At(f.Apply(i))))
				}))
			xInRestricted := a.Have(
				"x is a point of the restricted field",
				"x ∈ restrict_field(L, M).carrier",
				Simp(Fwd(field.RestrictFieldDef)),
				By(inM))
			xM := a.MemberOf[on.Any](x, xInRestricted)
			naturality := a.Have(
				"polynomial evaluation commutes with p",
				"permutation_map(p, polynomial_eval(f, x)) = "+
					"polynomial_eval(λi:num. permutation_map(p, f(i)), permutation_map(p, x))",
				By(
					restricted,
					field.CarrierSubfield.Read(restricted),
					over,
					nested,
					polynomial.PolynomialOverMono.At(a.TermAs[A]("L.zero"), K, M, f),
					subM,
					aut,
					AutomorphismRingHomomorphism.Read(L).At(K, M, p),
					xM,
					algebraic_element.FieldEmbeddingPolynomials.At(F, F, π, M, f)))
			a.Show(
				"fixed coefficients and zero transport the root",
				naturality.Simp(Fwd(coefficientsFixed), Fwd(root), Fwd(units)),
				By(naturality))
		}),
})}

// ---------------------------------------------------------------------------
// Fixed fields
// ---------------------------------------------------------------------------

// FixedFieldSubfield — the members of M fixed by a set of automorphisms
// of M form a subfield. Preservation gives closure under sums and
// products; a homomorphism of fields keeps negatives and inverses, which
// gives closure under those.
var FixedFieldSubfield = fixedFieldSubfieldThm{family.Add(registry.ProofEntry{
	Name: "FixedFieldSubfield",
	Key:  "prop_81584d91a0817989",
	Reading: "H ⊆ field_automorphisms(L, ∅, M) is load-bearing: the set H " +
		"holding only the swap of zero and one fixes exactly the points of M " +
		"other than those two, and a set missing zero and one is no subfield.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀M:set(A). ∀H:set(permutation(A)).",
		Hypotheses: []string{
			"subfield(L, M)",
			"H ⊆ field_automorphisms(L, ∅, M)",
		},
		Conclusion: "subfield(L, fixed_field(M, H))",
	},
		func(a *Argument, L field.FieldFact[on.L], M *Expr[Set[A]], H *Expr[Set[Permutation[A]]], h Fact) {
			given := a.Conjuncts(
				h,
				"M is a subfield of L",
				"the members of H are automorphisms of M")
			subfield, onAut := given[0], given[1]
			empty := a.TermAs[Set[A]]("∅")
			inL := a.Have(
				"M lies in L",
				"M ⊆ L.carrier",
				By(subfield, field.SubfieldSubset))
			actions := a.Have(
				"each member of H permutes M and preserves its operations",
				Statement{
					Binders:    "∀p:permutation(A).",
					Hypotheses: []string{"p ∈ H"},
					Conclusion: "p ∈ symmetric_group(M) ∧ " +
						"(∀x y:A. " +
						"    x ∈ M ∧ y ∈ M ⇒ " +
						"    permutation_map(p, x + y) = permutation_map(p, x) + permutation_map(p, y)) ∧ " +
						"(∀x y:A. " +
						"    x ∈ M ∧ y ∈ M ⇒ permutation_map(p, x * y) = permutation_map(p, x) * permutation_map(p, y))",
				},
				Derive(func(b *Argument) {
					b.FixAs[Permutation[A]]("p")
					pIn := b.Assume()
					aut := b.Have(
						"p is an automorphism of M",
						"p ∈ field_automorphisms(L, ∅, M)",
						By(pIn, onAut, set_basic.SubsetDef))
					b.Show(
						"the defining permutation and preservation laws",
						BySets(b.Unfolded(aut, FieldAutomorphismsDef)))
				}))
			units := a.Have(
				"each member of H fixes zero and one",
				Statement{
					Binders:    "∀p:permutation(A).",
					Hypotheses: []string{"p ∈ H"},
					Conclusion: "permutation_map(p, L.zero) = L.zero ∧ permutation_map(p, L.one) = L.one",
				},
				Derive(func(b *Argument) {
					p := b.FixAs[Permutation[A]]("p")
					pIn := b.Assume()
					aut := b.Have(
						"p is an automorphism of the subfield M",
						"p ∈ field_automorphisms(L, ∅, M)",
						By(pIn, onAut, set_basic.SubsetDef))
					b.Show(
						"an automorphism of a subfield fixes its units",
						By(aut, subfield, AutomorphismFixesUnits.Read(L).At(empty, M, p)))
				}))
			restricted := a.Have(
				"M carries the restricted field",
				"field_on(restrict_field(L, M))",
				By(subfield, field.SubfieldFieldOn.Read(L).At(M)))
			F := a.TermAs[FieldOps[A]]("restrict_field(L, M)")
			a.Show(
				"the fixed points satisfy the subfield conditions",
				Simp(Fwd(field.SubfieldDef)),
				SplitConjAll(
					Case(
						"the fixed points lie in L",
						Unfold(FixedFieldDef),
						BySets(inL)),
					Case(
						"zero is fixed and lies in M",
						Unfold(FixedFieldDef),
						BySets(units, subfield, field.SubfieldZero)),
					Case(
						"one is fixed and lies in M",
						Unfold(FixedFieldDef),
						BySets(units, subfield, field.SubfieldOne)),
					Case(
						"the sum of fixed points is fixed",
						Derive(func(b *Argument) {
							x, y := b.FixAs[A]("x"), b.FixAs[A]("y")
							both := b.Assume()
							properties := b.Have(
								"x and y lie in M and are fixed by H",
								"x ∈ M ∧ "+
									"y ∈ M ∧ "+
									"(∀p:permutation(A). p ∈ H ⇒ permutation_map(p, x) = x) ∧ "+
									"(∀p:permutation(A). p ∈ H ⇒ permutation_map(p, y) = y)",
								BySets(b.Unfolded(both, FixedFieldDef)))
							parts := b.Conjuncts(
								properties,
								"x lies in M",
								"y lies in M",
								"H fixes x",
								"H fixes y")
							xIn, yIn, fixesX, fixesY := parts[0], parts[1], parts[2], parts[3]
							sumIn := b.Have(
								"the sum lies in M",
								"x + y ∈ M",
								By(xIn, yIn, subfield, field.SubfieldAdd))
							fixed := b.Have(
								"H fixes the sum",
								"∀p:permutation(A). p ∈ H ⇒ permutation_map(p, x + y) = x + y",
								Derive(func(c *Argument) {
									p := c.FixAs[Permutation[A]]("p")
									pIn := c.Assume()
									sums := c.Have(
										"p preserves sums on M",
										"∀u v:A. u ∈ M ∧ v ∈ M ⇒ permutation_map(p, u + v) = permutation_map(p, u) + permutation_map(p, v)",
										By(Normalized, pIn, actions.At(p)))
									c.Show(
										"p preserves the sum and fixes both summands",
										By(Normalized, pIn, xIn, yIn, fixesX.At(p), fixesY.At(p), sums.At(x, y)))
								}))
							b.Show(
								"the sum belongs to the fixed field",
								Unfold(FixedFieldDef),
								BySets(fixed, sumIn))
						})),
					Case(
						"the negative of a fixed point is fixed",
						Derive(func(b *Argument) {
							x := b.FixAs[A]("x")
							xFixed := b.Assume()
							properties := b.Have(
								"x lies in M and is fixed by H",
								"x ∈ M ∧ (∀p:permutation(A). p ∈ H ⇒ permutation_map(p, x) = x)",
								BySets(b.Unfolded(xFixed, FixedFieldDef)))
							parts := b.Conjuncts(
								properties,
								"x lies in M",
								"H fixes x")
							xIn, fixesX := parts[0], parts[1]
							negIn := b.Have(
								"the negative lies in M",
								"-x ∈ M",
								By(xIn, subfield, field.SubfieldNeg))
							xMember := b.MemberOf[on.Any](x, xIn)
							fixed := b.Have(
								"H fixes the negative",
								"∀p:permutation(A). p ∈ H ⇒ permutation_map(p, -x) = -x",
								Derive(func(c *Argument) {
									p := c.FixAs[Permutation[A]]("p")
									pIn := c.Assume()
									hom := c.Have(
										"p is a ring homomorphism of the field M",
										"ring_homomorphism(field_ring(restrict_field(L, M)), "+
											"    field_ring(restrict_field(L, M)), "+
											"    permutation_map(p))",
										By(pIn, onAut, subfield, set_basic.SubsetDef, AutomorphismRingHomomorphism.Read(L).At(empty, M, p)))
									c.Show(
										"a homomorphism keeps negatives, and p fixes x",
										By(Normalized, pIn, fixesX.At(p), ring_homomorphism.MapNeg.Read(hom).At(xMember)))
								}))
							b.Show(
								"the negative belongs to the fixed field",
								Unfold(FixedFieldDef),
								BySets(fixed, negIn))
						})),
					Case(
						"the product of fixed points is fixed",
						Derive(func(b *Argument) {
							x, y := b.FixAs[A]("x"), b.FixAs[A]("y")
							both := b.Assume()
							properties := b.Have(
								"x and y lie in M and are fixed by H",
								"x ∈ M ∧ "+
									"y ∈ M ∧ "+
									"(∀p:permutation(A). p ∈ H ⇒ permutation_map(p, x) = x) ∧ "+
									"(∀p:permutation(A). p ∈ H ⇒ permutation_map(p, y) = y)",
								BySets(b.Unfolded(both, FixedFieldDef)))
							parts := b.Conjuncts(
								properties,
								"x lies in M",
								"y lies in M",
								"H fixes x",
								"H fixes y")
							xIn, yIn, fixesX, fixesY := parts[0], parts[1], parts[2], parts[3]
							productIn := b.Have(
								"the product lies in M",
								"x * y ∈ M",
								By(xIn, yIn, subfield, field.SubfieldMul))
							fixed := b.Have(
								"H fixes the product",
								"∀p:permutation(A). p ∈ H ⇒ permutation_map(p, x * y) = x * y",
								Derive(func(c *Argument) {
									p := c.FixAs[Permutation[A]]("p")
									pIn := c.Assume()
									products := c.Have(
										"p preserves products on M",
										"∀u v:A. u ∈ M ∧ v ∈ M ⇒ permutation_map(p, u * v) = permutation_map(p, u) * permutation_map(p, v)",
										By(Normalized, pIn, actions.At(p)))
									c.Show(
										"p preserves the product and fixes both factors",
										By(Normalized, pIn, xIn, yIn, fixesX.At(p), fixesY.At(p), products.At(x, y)))
								}))
							b.Show(
								"the product belongs to the fixed field",
								Unfold(FixedFieldDef),
								BySets(fixed, productIn))
						})),
					Case(
						"the inverse of a fixed point is fixed",
						Derive(func(b *Argument) {
							x := b.FixAs[A]("x")
							xFixed := b.Assume()
							properties := b.Have(
								"x lies in M and is fixed by H",
								"x ∈ M ∧ (∀p:permutation(A). p ∈ H ⇒ permutation_map(p, x) = x)",
								BySets(b.Unfolded(xFixed, FixedFieldDef)))
							parts := b.Conjuncts(
								properties,
								"x lies in M",
								"H fixes x")
							xIn, fixesX := parts[0], parts[1]
							invIn := b.Have(
								"the inverse lies in M",
								"L.inv(x) ∈ M",
								By(xIn, subfield, field.SubfieldInv))
							xMember := b.MemberOf[on.Any](x, xIn)
							fixed := b.Have(
								"H fixes the inverse",
								"∀p:permutation(A). p ∈ H ⇒ permutation_map(p, L.inv(x)) = L.inv(x)",
								Derive(func(c *Argument) {
									p := c.FixAs[Permutation[A]]("p")
									pIn := c.Assume()
									hom := c.Have(
										"p is a ring homomorphism of the field M",
										"ring_homomorphism(field_ring(restrict_field(L, M)), "+
											"    field_ring(restrict_field(L, M)), "+
											"    permutation_map(p))",
										By(pIn, onAut, subfield, set_basic.SubsetDef, AutomorphismRingHomomorphism.Read(L).At(empty, M, p)))
									c.Show(
										"a map keeping zero, one and products keeps inverses, and p fixes x",
										By(
											Normalized,
											pIn,
											fixesX.At(p),
											restricted,
											ring_homomorphism.MapIn.Read(hom),
											ring_homomorphism.MapZero.Read(hom),
											ring_homomorphism.MapOne.Read(hom),
											ring_homomorphism.MapMul.Read(hom),
											field.MapInv.Read(restricted).At(F, c.TermAs[Fun[A, A]]("permutation_map(p)"), xMember)))
								}))
							b.Show(
								"the inverse belongs to the fixed field",
								Unfold(FixedFieldDef),
								BySets(fixed, invIn))
						}))))
		}),
})}

// AutomorphismsAgreeOnGenerators — two automorphisms of K(S) that agree on K
// and on S are equal. The points of K(S) fixed by q⁻¹ ∘ p form a subfield
// holding K and S, so all of K(S); off K(S) both maps are the identity.
var AutomorphismsAgreeOnGenerators = automorphismsAgreeOnGeneratorsThm{family.Add(registry.ProofEntry{
	Name: "AutomorphismsAgreeOnGenerators",
	Key:  "prop_23d58d443726c34b",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀K S:set(A). ∀p q:permutation(A).",
		Hypotheses: []string{
			"K ⊆ M.carrier",
			"S ⊆ M.carrier",
			"p ∈ field_automorphisms(M, ∅, field_adjoin(M, K, S))",
			"q ∈ field_automorphisms(M, ∅, field_adjoin(M, K, S))",
			"∀x:A. x ∈ K ⇒ permutation_map(p, x) = permutation_map(q, x)",
			"∀x:A. x ∈ S ⇒ permutation_map(p, x) = permutation_map(q, x)",
		},
		Conclusion: "p = q",
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			K, S *Expr[Set[A]],
			p, q *Expr[Permutation[A]],
			KIn, SIn, pAuto, qAuto, onK, onS Fact,
		) {
			adjoined := a.TermAs[Set[A]]("field_adjoin(M, K, S)")
			nothing := a.TermAs[Set[A]]("∅")
			automorphisms := a.TermAs[Set[Permutation[A]]]("field_automorphisms(M, ∅, field_adjoin(M, K, S))")
			permutations := a.TermAs[group.GroupOps[Permutation[A]]]("permutation_group")
			inverse := a.TermAs[Permutation[A]]("permutation_inverse(q)")
			quotient := a.TermAs[Set[Permutation[A]]]("{permutation_compose(permutation_inverse(q), p)}")
			fixed := a.TermAs[Set[A]](
				"fixed_field(field_adjoin(M, K, S), {permutation_compose(permutation_inverse(q), p)})")
			adjoin := a.Have(
				"K(S) is a subfield holding K and S",
				"subfield(M, field_adjoin(M, K, S)) ∧ K ⊆ field_adjoin(M, K, S) ∧ S ⊆ field_adjoin(M, K, S)",
				By(KIn, SIn, algebraic_element.AdjoinSubfield.Read(M).At(K, S)))
			subgroupData := a.Have(
				"its automorphisms are a subgroup of permutations of K(S)",
				"subgroup(permutation_group, field_automorphisms(M, ∅, field_adjoin(M, K, S))) ∧ "+
					"field_automorphisms(M, ∅, field_adjoin(M, K, S)) ⊆ symmetric_group(field_adjoin(M, K, S))",
				By(AutomorphismsSubgroup.Read(M).At(nothing, adjoined)))
			quotientAuto := a.Have(
				"q⁻¹ ∘ p is an automorphism of K(S)",
				"{permutation_compose(permutation_inverse(q), p)} ⊆ "+
					"field_automorphisms(M, ∅, field_adjoin(M, K, S))",
				BySets(
					pAuto,
					qAuto,
					subgroupData,
					group.SubgroupInv.At(permutations, automorphisms, q),
					group.SubgroupMul.At(permutations, automorphisms, inverse, p)))
			fixedSubfield := a.Have(
				"the points it fixes form a subfield",
				"subfield(M, fixed_field(field_adjoin(M, K, S), {permutation_compose(permutation_inverse(q), p)}))",
				By(adjoin, quotientAuto, FixedFieldSubfield.Read(M).At(adjoined, quotient)))
			fixedWhereEqual := a.Have(
				"a point of K(S) where p and q agree is one of them",
				Statement{
					Binders: "∀x:A.",
					Hypotheses: []string{
						"x ∈ field_adjoin(M, K, S)",
						"permutation_map(p, x) = permutation_map(q, x)",
					},
					Conclusion: "x ∈ " +
						"fixed_field(field_adjoin(M, K, S), {permutation_compose(permutation_inverse(q), p)})",
				},
				Derive(func(b *Argument) {
					x := b.FixAs[A]("x")
					agreement := b.Assume()
					value := b.Have(
						"q⁻¹ undoes q at x",
						"permutation_map(permutation_compose(permutation_inverse(q), p), x) = x",
						By(agreement, symmetric_group.MapCompose.At(inverse, p, x), symmetric_group.MapInverse.At(q, x)))
					b.Show(
						"so q⁻¹ ∘ p fixes x",
						Simp(Fwd(FixedFieldDef)),
						BySets(agreement, value))
				}))
			generators := a.Have(
				"K and S are fixed",
				"K ⊆ fixed_field(field_adjoin(M, K, S), {permutation_compose(permutation_inverse(q), p)}) ∧ "+
					"S ⊆ fixed_field(field_adjoin(M, K, S), {permutation_compose(permutation_inverse(q), p)})",
				BySets(adjoin, onK, onS, fixedWhereEqual))
			allFixed := a.Have(
				"so the fixed subfield is all of K(S)",
				"field_adjoin(M, K, S) ⊆ "+
					"fixed_field(field_adjoin(M, K, S), {permutation_compose(permutation_inverse(q), p)})",
				By(fixedSubfield, generators, algebraic_element.AdjoinLeast.Read(M).At(K, S, fixed)))
			agreeEverywhere := a.Have(
				"p and q agree at every point",
				"∀x:A. permutation_map(p, x) = permutation_map(q, x)",
				Derive(func(b *Argument) {
					x := b.FixAs[A]("x")
					b.Cases(b.Term("x ∈ field_adjoin(M, K, S)"))
					b.When(
						"a point of K(S) is fixed by q⁻¹ ∘ p",
						func(c *Argument, inside Fact) {
							value := c.Have(
								"q⁻¹ ∘ p fixes x",
								"permutation_map(permutation_compose(permutation_inverse(q), p), x) = x",
								BySets(inside, allFixed, FixedFieldDef))
							c.Show(
								"apply q to both sides",
								By(
									Normalized,
									value,
									symmetric_group.MapCompose.At(inverse, p, x),
									symmetric_group.MapInverseRight.At(q, c.TermAs[A]("permutation_map(p, x)"))))
						})
					b.Otherwise(
						"off K(S) both are the identity",
						func(c *Argument, outside Fact) {
							c.Show(
								"each moves no point off K(S)",
								BySets(
									outside,
									pAuto,
									qAuto,
									subgroupData,
									symmetric_group.InSymmetricGroup.At(adjoined, p),
									symmetric_group.InSymmetricGroup.At(adjoined, q)))
						})
				}))
			a.Show(
				"permutations with the same values are equal",
				By(agreeEverywhere, symmetric_group.PermutationEq.At(p, q)))
		}),
})}

// FixedFieldAntitone — more automorphisms fix fewer points: a point of M
// fixed by every member of H' is fixed by every member of its subset H.
var FixedFieldAntitone = fixedFieldAntitoneThm{family.Add(registry.ProofEntry{
	Name: "FixedFieldAntitone",
	Key:  "prop_605225b1d0fac23a",
	Build: family.Theorem(Statement{
		Binders: "∀M:set(A). ∀H H':set(permutation(A)).",
		Hypotheses: []string{
			"H ⊆ H'",
		},
		Conclusion: "fixed_field(M, H') ⊆ fixed_field(M, H)",
	},
		func(a *Argument, M *Expr[Set[A]], H, HPrime *Expr[Set[Permutation[A]]], smaller Fact) {
			a.Show(
				"a point of M fixed by every member of H' is fixed by every member of H",
				Unfold(FixedFieldDef),
				BySets(smaller))
		}),
})}

// AutomorphismsAntitone — fixing more points leaves fewer
// automorphisms: a permutation fixing K' fixes its subset K.
var AutomorphismsAntitone = automorphismsAntitoneThm{family.Add(registry.ProofEntry{
	Name: "AutomorphismsAntitone",
	Key:  "prop_bb2e6332aaab8d30",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀K K' M:set(A).",
		Hypotheses: []string{
			"K ⊆ K'",
		},
		Conclusion: "field_automorphisms(L, K', M) ⊆ field_automorphisms(L, K, M)",
	},
		func(a *Argument, L field.FieldFact[on.L], K, KPrime, M *Expr[Set[A]], smaller Fact) {
			a.Show(
				"an automorphism fixing K' keeps its permutation "+
					"and preservation laws, and fixes every member of K",
				Unfold(FieldAutomorphismsDef),
				BySets(smaller))
		}),
})}

// SubfieldFixed — the automorphisms fixing K fix at least K: members
// of K lie in M and every such automorphism fixes them.
var SubfieldFixed = subfieldFixedThm{family.Add(registry.ProofEntry{
	Name: "SubfieldFixed",
	Key:  "prop_dab87cd3d138a5a8",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀K M:set(A).",
		Hypotheses: []string{
			"K ⊆ M",
		},
		Conclusion: "K ⊆ fixed_field(M, field_automorphisms(L, K, M))",
	},
		func(a *Argument, L field.FieldFact[on.L], K, M *Expr[Set[A]], inM Fact) {
			a.Show(
				"members of K lie in M and every automorphism fixing K fixes them",
				Unfold(FixedFieldDef),
				Unfold(FieldAutomorphismsDef),
				BySets(inM))
		}),
})}

// FixedFieldAutomorphisms — each automorphism in H fixes every point that
// all of H fixes, so H lies among the automorphisms of M fixing its fixed
// field: the unit of the Galois connection on the side of the groups, as
// SubfieldFixed is on the side of the fields.
var FixedFieldAutomorphisms = fixedFieldAutomorphismsThm{family.Add(registry.ProofEntry{
	Name: "FixedFieldAutomorphisms",
	Key:  "prop_db8e1c331a1cbb3a",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀M:set(A). ∀H:set(permutation(A)).",
		Hypotheses: []string{
			"H ⊆ field_automorphisms(L, ∅, M)",
		},
		Conclusion: "H ⊆ field_automorphisms(L, fixed_field(M, H), M)",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			M *Expr[Set[A]],
			H *Expr[Set[Permutation[A]]],
			onAut Fact,
		) {
			fixing := a.Have(
				"each member of H is an automorphism of M fixing the field H fixes",
				"∀p:permutation(A). p ∈ H ⇒ p ∈ field_automorphisms(L, fixed_field(M, H), M)",
				Derive(func(b *Argument) {
					b.FixAs[Permutation[A]]("p")
					pIn := b.Assume()
					aut := b.Have(
						"p is an automorphism of M",
						"p ∈ field_automorphisms(L, ∅, M)",
						By(pIn, onAut, set_basic.SubsetDef))
					b.Show(
						"p permutes M keeping sums and products, and fixes what every member of H fixes",
						Unfold(FieldAutomorphismsDef),
						Unfold(FixedFieldDef),
						BySets(pIn, b.Unfolded(aut, FieldAutomorphismsDef)))
				}))
			a.Show(
				"so H lies among them",
				By(fixing, set_basic.SubsetDef))
		}),
})}
