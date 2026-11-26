// group.go — the permutations of a type form a group, and it is not
// commutative once the type has three points; the powers of a permutation:
// their exponents add, a subgroup holds them, a repeated power returns to
// the identity, the least positive exponent that returns to the identity is
// the order, and the powers below it form a subgroup with that many members.

package symmetric_group

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/abelian_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/registry"
)

// SymmetricGroup — the permutations of A form a group under composition,
// with the identity permutation and the inverse. Each axiom is an
// equation between permutations, so each is read point by point
// (PermutationEq), where the operations are the operations on maps: the
// composite runs one map after the other, the identity moves nothing,
// and the inverse sends each point back.
var SymmetricGroup = symmetricGroupThm{family.Add(registry.ProofEntry{
	Name: "SymmetricGroup",
	Key:  "prop_6397ccf3fc600511",
	Build: family.Instance(group.Group, "group(permutation_group⟨A:A⟩)",
		Case(
			"composition associates: both sides move a point by z, then y, then x",
			Derive(func(b *Argument) {
				b.FixAs[Permutation[A]]("x")
				b.FixAs[Permutation[A]]("y")
				b.FixAs[Permutation[A]]("z")
				pointwise := b.Have(
					"the two sides agree at every point",
					"∀u:A. permutation_map(x * (y * z), u) = permutation_map(x * y * z, u)",
					Simp(Fwd(MapCompose)),
					Basic())
				b.Show(
					"so they are one permutation",
					By(pointwise, PermutationEq))
			})),
		Case(
			"the identity is a left identity: it moves nothing after x has moved a point",
			Derive(func(b *Argument) {
				b.FixAs[Permutation[A]]("x")
				pointwise := b.Have(
					"the two sides agree at every point",
					"∀u:A. permutation_map(permutation_identity * x, u) = permutation_map(x, u)",
					Simp(Fwd(MapCompose), Fwd(MapIdentity)),
					Basic())
				b.Show(
					"so they are one permutation",
					By(pointwise, PermutationEq))
			})),
		Case(
			"the inverse is a left inverse: it sends back each point x has moved",
			Derive(func(b *Argument) {
				b.FixAs[Permutation[A]]("x")
				pointwise := b.Have(
					"the two sides agree at every point",
					"∀u:A. permutation_map(permutation_inverse(x) * x, u) = permutation_map(permutation_identity, u)",
					Simp(Fwd(MapCompose), Fwd(MapInverse), Fwd(MapIdentity)),
					Basic())
				b.Show(
					"so they are one permutation",
					By(pointwise, PermutationEq))
			}))),
})}

// RestrictPermutationGroupUniverse — the permutation group restricted to
// the whole type is the permutation group: its carrier is already 𝕌. A
// law of subgroups, such as Lagrange's theorem, asks for the group
// restricted to the carrier it is read at, and at 𝕌 that is this group.
var RestrictPermutationGroupUniverse = restrictPermutationGroupUniverseThm{family.Add(registry.ProofEntry{
	Name: "RestrictPermutationGroupUniverse",
	Key:  "prop_3d630d7688437896",
	Build: family.Theorem("restrict_group(permutation_group⟨A:A⟩, 𝕌) = permutation_group⟨A:A⟩",
		func(a *Argument) {
			a.Show(
				"both sides are composition, the identity and the inverse on 𝕌",
				Simp(
					Fwd(PermutationGroupDef),
					Fwd(group.RestrictGroupDef),
					Fwd(group.GroupMulDef),
					Fwd(group.GroupOneDef),
					Fwd(group.GroupInvDef)),
				Refl())
		}),
})}

// TranspositionSelfInverse — a transposition undoes itself: swapping a
// and b twice returns every point, a and b included.
var TranspositionSelfInverse = transpositionSelfInverseThm{family.Add(registry.ProofEntry{
	Name: "TranspositionSelfInverse",
	Key:  "prop_2260f0885d88c8f0",
	Build: family.Theorem("∀a b:A. transposition(a, b) * transposition(a, b) = permutation_identity",
		func(arg *Argument, a, b *Expr[A]) {
			pointwise := arg.Have(
				"swapping twice moves every point as the identity does",
				"∀u:A. "+
					"    permutation_map(transposition(a, b) * transposition(a, b), u) = "+
					"    permutation_map(permutation_identity, u)",
				Simp(Fwd(MapCompose), Fwd(MapTransposition), Fwd(MapIdentity)),
				BySets())
			arg.Show(
				"so it is the identity",
				By(pointwise, PermutationEq))
		}),
})}

// TranspositionsDoNotCommute — two transpositions sharing a point do not
// commute: (a b)(b c) sends a to b, and (b c)(a b) sends it to c. Were
// the two products one permutation, they would send a to one point.
var TranspositionsDoNotCommute = transpositionsDoNotCommuteThm{family.Add(registry.ProofEntry{
	Name: "TranspositionsDoNotCommute",
	Key:  "prop_c1d4976c3a8e97ad",
	Build: family.Theorem(Statement{
		Binders: "∀a b c:A.",
		Hypotheses: []string{
			"a ≠ b",
			"b ≠ c",
			"a ≠ c",
		},
		Conclusion: "transposition(a, b) * transposition(b, c) ≠ transposition(b, c) * transposition(a, b)",
	},
		func(arg *Argument, a, b, c *Expr[A], distinct Fact) {
			left := arg.Have(
				"(a b)(b c) sends a to b: (b c) leaves a where it is, and (a b) moves it to b",
				"permutation_map(transposition(a, b) * transposition(b, c), a) = b",
				Simp(Fwd(MapCompose), Fwd(MapTransposition)),
				By(distinct))
			right := arg.Have(
				"(b c)(a b) sends a to c: (a b) moves it to b, and (b c) moves b on to c",
				"permutation_map(transposition(b, c) * transposition(a, b), a) = c",
				Simp(Fwd(MapCompose), Fwd(MapTransposition)),
				By(distinct))
			arg.Show(
				"so the two products send a to different points: equal "+
					"products would send it to one point, and b is not c",
				By(distinct, left, right))
		}),
})}

// TranspositionConjugate — conjugating the transposition of a and b by
// the transposition of b and c gives the transposition of a and c, when
// a differs from b and from c. Read from the right, the product sends a
// to a, then b, then c, and c to b, then a, then a; it sends b, where b
// is not c, to c and back, and returns every other point to itself.
var TranspositionConjugate = transpositionConjugateThm{family.Add(registry.ProofEntry{
	Name: "TranspositionConjugate",
	Key:  "prop_97f0d70d28a3fab3",
	Build: family.Theorem(Statement{
		Binders: "∀a b c:A.",
		Hypotheses: []string{
			"a ≠ b",
			"a ≠ c",
		},
		Conclusion: "transposition(a, c) = transposition(b, c) * transposition(a, b) * transposition(b, c)",
	}, func(arg *Argument, a, b, c *Expr[A], apart Fact) {
		pointwise := arg.Have(
			"the two sides move every point alike",
			"∀u:A. "+
				"    permutation_map(transposition(a, c), u) = "+
				"    permutation_map(transposition(b, c) * transposition(a, b) * transposition(b, c), u)",
			Derive(func(d *Argument) {
				d.FixAs[A]("u")
				d.Unless(
					d.Term("u = a"),
					"a stays at a, goes to b, then to c, where (a c) sends it",
					Given(func(e *Argument, atA Fact) {
						e.Show(
							"both sides send a to c",
							atA.Rw(),
							Simp(Fwd(MapCompose), Fwd(MapTransposition)),
							Basic())
					}))
				d.Unless(
					d.Term("u = c"),
					"c goes to b, then to a, and stays at a, where (a c) sends it",
					Given(func(e *Argument, atC Fact) {
						e.Show(
							"both sides send c to a",
							atC.Rw(),
							Simp(Fwd(MapCompose), Fwd(MapTransposition)),
							By(apart))
					}))
				d.Unless(
					d.Term("u = b"),
					"b, here not c, goes to c, stays at c and comes back to b, which (a c) fixes",
					Given(func(e *Argument, atB Fact) {
						e.Show(
							"both sides fix b",
							atB.Rw(),
							Simp(Fwd(MapCompose), Fwd(MapTransposition)),
							Basic())
					}))
				d.Show(
					"every other point stays put on both sides",
					Simp(Fwd(MapCompose), Fwd(MapTransposition)),
					Basic())
			}))
		arg.Show(
			"so they are one permutation",
			By(pointwise, PermutationEq))
	}),
})}

// TranspositionSymmetric — the transposition of a and b is the
// transposition of b and a: both exchange the two points and fix every
// other.
var TranspositionSymmetric = transpositionSymmetricThm{family.Add(registry.ProofEntry{
	Name: "TranspositionSymmetric",
	Key:  "prop_50a9980032a401bf",
	Build: family.Theorem("∀a b:A. transposition(a, b) = transposition(b, a)",
		func(arg *Argument, a, b *Expr[A]) {
			pointwise := arg.Have(
				"the two sides move every point alike",
				"∀u:A. permutation_map(transposition(a, b), u) = permutation_map(transposition(b, a), u)",
				Simp(Fwd(MapTransposition)),
				BySets())
			arg.Show(
				"so they are one permutation",
				By(pointwise, PermutationEq))
		}),
})}

// NotAbelian — on a type with three distinct points the symmetric group
// is not abelian: an abelian group's operation commutes, and two
// transpositions sharing a point do not.
var NotAbelian = notAbelianThm{family.Add(registry.ProofEntry{
	Name: "NotAbelian",
	Key:  "prop_405751ec9a2eba4e",
	Build: family.Theorem(Statement{
		Binders: "∀a b c:A.",
		Hypotheses: []string{
			"a ≠ b",
			"b ≠ c",
			"a ≠ c",
		},
		Conclusion: "¬abelian_group(permutation_group⟨A:A⟩)",
	},
		func(arg *Argument, a, b, c *Expr[A], distinct Fact) {
			commute := arg.Have(
				"in an abelian group (a b) and (b c) would commute",
				Statement{
					Hypotheses: []string{
						"abelian_group(permutation_group⟨A:A⟩)",
					},
					Conclusion: "transposition(a, b) * transposition(b, c) = transposition(b, c) * transposition(a, b)",
				},
				By(abelian_group.Comm))
			arg.Show(
				"and they do not",
				By(distinct, commute, TranspositionsDoNotCommute.At(a, b, c)))
		}),
})}

// PermutationPowerAdd — the exponents of a permutation add: by induction on
// i, one more factor of s associates across the product.
var PermutationPowerAdd = permutationPowerAddThm{family.Add(registry.ProofEntry{
	Name: "PermutationPowerAdd",
	Key:  "prop_d31e69e940db31d3",
	Build: family.Theorem(Statement{
		Abbrev: Abbrev{
			{Name: "power", Text: "λs:permutation(A). λd:num. " +
				"    monoid_pow⟨A:permutation(A)⟩( " +
				"        (λp:permutation(A). λq:permutation(A). permutation_compose(p, q)), " +
				"        permutation_identity⟨A:A⟩, " +
				"        s, " +
				"        d)"},
		},
		Binders:    "∀s:permutation(A). ∀i j:num.",
		Conclusion: "«power»(s, i + j) = permutation_compose(«power»(s, i), «power»(s, j))",
	},
		func(a *Argument, s *Expr[Permutation[A]], i, j *Expr[Nat]) {
			a.Induct(i)
			a.Base(
				"the zeroth power is the identity",
				Simp(Fwd(comm_monoid.MonoidPowDef), Fwd(group.LeftIdentity.Read(SymmetricGroup))),
				ByArith())
			a.Step(
				"one more factor of s associates across the product",
				func(b *Argument, sum Fact) {
					b.Do(Simp(Fwd(nat_arith.Add), Fwd(comm_monoid.MonoidPowDef)))
					b.Show(
						"regroup the extra factor",
						By(sum, group.Assoc.Read(SymmetricGroup)))
				})
		}),
})}

// PermutationPowerIn — a subgroup of permutations holds the powers of its
// members: the identity at 0, and one more factor of s at each step.
var PermutationPowerIn = permutationPowerInThm{family.Add(registry.ProofEntry{
	Name: "PermutationPowerIn",
	Key:  "prop_ac879b1bae0c0477",
	Build: family.Theorem(Statement{
		Abbrev: Abbrev{
			{Name: "power", Text: "λs:permutation(A). λd:num. " +
				"    monoid_pow⟨A:permutation(A)⟩( " +
				"        (λp:permutation(A). λq:permutation(A). permutation_compose(p, q)), " +
				"        permutation_identity⟨A:A⟩, " +
				"        s, " +
				"        d)"},
		},
		Binders: "∀h:set(permutation(A)). ∀s:permutation(A). ∀n:num.",
		Hypotheses: []string{
			"subgroup(permutation_group, h)",
			"s ∈ h",
		},
		Conclusion: "«power»(s, n) ∈ h",
	},
		func(
			a *Argument,
			h *Expr[Set[Permutation[A]]],
			s *Expr[Permutation[A]],
			n *Expr[Nat],
			inGroup, member Fact,
		) {
			permutations := a.TermAs[group.GroupOps[Permutation[A]]]("permutation_group")
			a.Induct(n)
			a.Base(
				"the zeroth power is the identity",
				By(Normalized, inGroup, group.SubgroupOne.At(permutations, h), comm_monoid.MonoidPowDef))
			a.Step(
				"one more factor of s stays in the subgroup",
				func(b *Argument, inside Fact) {
					b.Show(
						"the subgroup is closed under composition",
						By(
							inside,
							member,
							inGroup,
							group.SubgroupMul.At(permutations, h, s, b.TermAs[Permutation[A]]("«power»(s, n)")),
							comm_monoid.MonoidPowDef))
				})
		}),
})}

// PermutationPowerRepeat — a repeated power of a permutation is a return to
// the identity: if s^i = s^j with i < j, then s^(j − i) cancels s^i from
// s^i = s^i ∘ s^(j − i).
var PermutationPowerRepeat = permutationPowerRepeatThm{family.Add(registry.ProofEntry{
	Name: "PermutationPowerRepeat",
	Key:  "prop_74a655f20189c8f6",
	Build: family.Theorem(Statement{
		Abbrev: Abbrev{
			{Name: "power", Text: "λs:permutation(A). λd:num. " +
				"    monoid_pow⟨A:permutation(A)⟩( " +
				"        (λp:permutation(A). λq:permutation(A). permutation_compose(p, q)), " +
				"        permutation_identity⟨A:A⟩, " +
				"        s, " +
				"        d)"},
		},
		Binders: "∀s:permutation(A). ∀i j:num.",
		Hypotheses: []string{
			"i < j",
			"«power»(s, i) = «power»(s, j)",
		},
		Conclusion: "0 < j - i ∧ «power»(s, j - i) = permutation_identity",
	},
		func(a *Argument, s *Expr[Permutation[A]], i, j *Expr[Nat], ordered, repeated Fact) {
			gap := a.Have(
				"the gap is positive and i plus the gap is j",
				"0 < j - i ∧ i + (j - i) = j",
				ByArith(ordered))
			split := a.Have(
				"s^j splits as s^i ∘ s^(j − i)",
				"«power»(s, i) = permutation_compose(«power»(s, i), «power»(s, j - i))",
				By(gap, repeated, At(PermutationPowerAdd, s, i, a.TermAs[Nat]("j - i"))))
			a.Show(
				"cancel s^i on the left",
				By(
					gap,
					split,
					group.RightIdentity.Read(SymmetricGroup).At(a.TermAs[Permutation[A]]("«power»(s, i)")),
					group.LeftCancel.Read(SymmetricGroup).At(
						a.TermAs[Permutation[A]]("«power»(s, i)"),
						a.TermAs[Permutation[A]]("«power»(s, j - i)"),
						a.TermAs[Permutation[A]]("permutation_identity"))))
		}),
})}

// PermutationOrderUnique — a least positive exponent at which s is the
// identity is the order of s: the choice in the definition meets the same
// description, and two least ones agree.
var PermutationOrderUnique = permutationOrderUniqueThm{family.Add(registry.ProofEntry{
	Name: "PermutationOrderUnique",
	Key:  "prop_785ade7dc3e703c0",
	Build: family.Theorem(Statement{
		Abbrev: Abbrev{
			{Name: "power", Text: "λs:permutation(A). λd:num. " +
				"    monoid_pow⟨A:permutation(A)⟩( " +
				"        (λp:permutation(A). λq:permutation(A). permutation_compose(p, q)), " +
				"        permutation_identity⟨A:A⟩, " +
				"        s, " +
				"        d)"},
		},
		Binders: "∀s:permutation(A). ∀e:num.",
		Hypotheses: []string{
			"0 < e",
			"«power»(s, e) = permutation_identity",
			"∀d:num. 0 < d ∧ «power»(s, d) = permutation_identity ⇒ e ≤ d",
		},
		Conclusion: "permutation_order(s) = e",
	},
		func(a *Argument, s *Expr[Permutation[A]], e *Expr[Nat], positive, annihilates, least Fact) {
			met := a.Have(
				"e meets the description of the order",
				"∃o:num. "+
					"    0 < o ∧ "+
					"    «power»(s, o) = permutation_identity ∧ "+
					"    (∀d:num. 0 < d ∧ «power»(s, d) = permutation_identity ⇒ o ≤ d)",
				Witness(e),
				By(positive, annihilates, least))
			order, chosen := a.ObtainChosen(
				"so the choice in the definition meets it",
				"∃o:num. "+
					"    0 < o ∧ "+
					"    «power»(s, o) = permutation_identity ∧ "+
					"    (∀d:num. 0 < d ∧ «power»(s, d) = permutation_identity ⇒ o ≤ d)",
				met)
			description := a.Conjuncts(
				chosen,
				"the chosen exponent is positive",
				"it annihilates s",
				"it is at most every positive annihilator")
			a.Show(
				"two least positive annihilators are equal",
				By(
					PermutationOrderDef.At(s),
					description[0],
					description[1],
					positive,
					annihilates,
					least.At(order),
					description[2].At(e),
					At(nat_order.LessEqAntisym, order, e)))
		}),
})}

// PowersSubgroup — the powers of s below its order form a subgroup with that
// many members. Every power is a power below e, by induction on the
// exponent, so products and inverses stay among them; two powers below e
// differ, since a repeat would give a smaller annihilating exponent.
var PowersSubgroup = powersSubgroupThm{family.Add(registry.ProofEntry{
	Name: "PowersSubgroup",
	Key:  "prop_c00b660a8365765c",
	Build: family.Theorem(Statement{
		Abbrev: Abbrev{
			{Name: "power", Text: "λs:permutation(A). λd:num. " +
				"    monoid_pow⟨A:permutation(A)⟩( " +
				"        (λp:permutation(A). λq:permutation(A). permutation_compose(p, q)), " +
				"        permutation_identity⟨A:A⟩, " +
				"        s, " +
				"        d)"},
			{Name: "powers", Text: "λs:permutation(A). λe:num. {«power»(s, j) | j:num | j < e}"},
		},
		Binders: "∀s:permutation(A). ∀e:num.",
		Hypotheses: []string{
			"0 < e",
			"«power»(s, e) = permutation_identity",
			"∀d:num. 0 < d ∧ «power»(s, d) = permutation_identity ⇒ e ≤ d",
		},
		Conclusion: "subgroup(permutation_group, «powers»(s, e)) ∧ has_size(«powers»(s, e), e)",
	},
		func(a *Argument, s *Expr[Permutation[A]], e *Expr[Nat], positive, annihilates, least Fact) {
			below := a.TermAs[Set[Nat]]("{i:num | i < e}")
			powerMap := a.TermAs[Fun[Nat, Permutation[A]]]("«power»(s)")
			wrap := a.Have(
				"every power of s is a power below e",
				"∀n:num. «power»(s, n) ∈ «powers»(s, e)",
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]("n")
					b.Induct(n)
					b.Base(
						"the identity is the zeroth power, and 0 is below e",
						BySets(positive))
					b.Step(
						"one more factor raises the exponent below e, or wraps it to zero at e",
						func(c *Argument, wrapped Fact) {
							_, reduced := c.ObtainAs[Nat](
								"the power is a power below e",
								"∃j:num. j < e ∧ «power»(s, n) = «power»(s, j)",
								BySets(wrapped))
							parts := c.Conjuncts(
								reduced,
								"j is below e",
								"the power is the j-th")
							next := c.Have(
								"both sides take one more factor of s",
								"«power»(s, suc(n)) = «power»(s, suc(j))",
								Simp(Fwd(comm_monoid.MonoidPowDef)),
								By(Normalized, parts[1]))
							c.Cases(c.Term("suc(j) < e"))
							c.When(
								"the next exponent is still below e",
								func(d *Argument, stays Fact) {
									d.Show(
										"it is the next power",
										BySets(stays, next))
								})
							c.Otherwise(
								"the next exponent is e, where the power is the identity",
								func(d *Argument, reaches Fact) {
									top := d.Have(
										"j + 1 is e",
										"suc(j) = e",
										ByArith(reaches, parts[0]))
									identity := d.Have(
										"the power is the zeroth",
										"«power»(s, suc(n)) = «power»(s, 0)",
										By(top, next, annihilates, comm_monoid.MonoidPowDef))
									d.Show(
										"it is the zeroth power",
										BySets(identity, positive))
								})
						})
				}))
			products := a.Have(
				"a product of powers is a power, the exponents adding",
				Statement{
					Binders: "∀x y:permutation(A).",
					Hypotheses: []string{
						"x ∈ «powers»(s, e)",
						"y ∈ «powers»(s, e)",
					},
					Conclusion: "permutation_compose(x, y) ∈ «powers»(s, e)",
				},
				Derive(func(b *Argument) {
					b.FixAs[Permutation[A]]("x")
					b.FixAs[Permutation[A]]("y")
					members := b.Assume()
					i, xPower := b.ObtainAs[Nat](
						"x is a power",
						"∃i:num. x = «power»(s, i)",
						BySets(members))
					j, yPower := b.ObtainAs[Nat](
						"y is a power",
						"∃j:num. y = «power»(s, j)",
						BySets(members))
					b.Show(
						"their product is the power at the sum",
						By(xPower, yPower, At(PermutationPowerAdd, s, i, j), wrap.At(b.TermAs[Nat]("i + j"))))
				}))
			inverses := a.Have(
				"the inverse of s^j is s^(e − j)",
				"∀x:permutation(A). x ∈ «powers»(s, e) ⇒ permutation_inverse(x) ∈ «powers»(s, e)",
				Derive(func(b *Argument) {
					x := b.FixAs[Permutation[A]]("x")
					member := b.Assume()
					j, xPower := b.ObtainAs[Nat](
						"x is a power below e",
						"∃j:num. j < e ∧ x = «power»(s, j)",
						BySets(member))
					complement := b.TermAs[Nat]("e - j")
					power := b.TermAs[Permutation[A]]("«power»(s, e - j)")
					gap := b.Have(
						"e − j and j add up to e",
						"(e - j) + j = e",
						ByArith(xPower))
					cancels := b.Have(
						"s^(e − j) ∘ s^j is the identity",
						"permutation_compose(«power»(s, e - j), x) = permutation_identity",
						By(gap, xPower, annihilates, At(PermutationPowerAdd, s, complement, j)))
					b.Show(
						"s^(e − j) is a power, and it inverts x",
						By(cancels, wrap.At(complement), group.InvUnique.Read(SymmetricGroup).At(power, x)))
				}))
			identity := a.Have(
				"the identity is the zeroth power",
				"permutation_identity ∈ «powers»(s, e)",
				By(wrap.At(a.TermAs[Nat]("0")), comm_monoid.MonoidPowDef))
			subgroupOfPowers := a.Have(
				"the powers below e are a subgroup",
				"subgroup(permutation_group, «powers»(s, e))",
				Simp(Fwd(group.SubgroupDef)),
				BySets(identity, products, inverses))
			injective := a.Have(
				"two distinct exponents below e give distinct powers",
				"injective_on({i:num | i < e}, «power»(s))",
				Derive(func(b *Argument) {
					distinct := b.Have(
						"a repeat of powers below e would be a smaller annihilator",
						"∀i j:num. i < j ∧ j < e ∧ «power»(s, i) = «power»(s, j) ⇒ ⊥",
						Derive(func(c *Argument) {
							i, j := c.FixAs[Nat]("i"), c.FixAs[Nat]("j")
							repeat := c.Assume()
							gap := c.TermAs[Nat]("j - i")
							c.Show(
								"the gap between them annihilates s",
								ByArith(repeat, At(PermutationPowerRepeat, s, i, j), least.At(gap)))
						}))
					b.Do(Unfold(functions.InjectiveOnDef))
					i, j := b.FixAs[Nat]("i"), b.FixAs[Nat]("j")
					same := b.Assume()
					b.Show(
						"neither exponent is below the other",
						ByArith(same, distinct.At(i, j), distinct.At(j, i)))
				}))
			image := a.Have(
				"the powers below e are the image of the exponents below e",
				"«powers»(s, e) = image(«power»(s), {i:num | i < e})",
				BySets())
			size := a.Have(
				"there are e of them",
				"has_size(«powers»(s, e), e)",
				By(
					image,
					injective,
					num_segment.HasSizeBelowStrict.At(e),
					cardinality.HasSizeImageInj.At(powerMap, below, e)))
			a.Show(
				"the powers below e are a subgroup of e members",
				By(subgroupOfPowers, size))
		}),
})}
