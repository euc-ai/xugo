// counting.go — how many permutations a finite set has: laying one point
// in multiplies the count by the new number of points, so n points have
// n! permutations; and Lagrange's theorem read at the symmetric group.

package symmetric_group

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/finite_group/finite_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// Laying a point in
// ---------------------------------------------------------------------------

// SymmetricGroupInsert — a permutation q of insert(a, s) is sorted by
// where it sends a. That point b lies in insert(a, s), and p := (a b)·q
// returns a to a and leaves every other point outside s where q left it,
// such a point lying outside insert(a, s) and being neither a nor b; as
// (a b) undoes itself, q is (a b)·p. Conversely (a b) and a permutation
// of s both move no point outside insert(a, s), and the symmetric group
// on insert(a, s) is closed under products. Whether a is new to s does
// not matter here; it matters for the count, where the products must
// be told apart.
var SymmetricGroupInsert = symmetricGroupInsertThm{family.Add(registry.ProofEntry{
	Name: "SymmetricGroupInsert",
	Key:  "prop_9c5d16a2f0f9e4c0",
	Build: family.Theorem("∀a:A. ∀s:set(A). "+
		"    symmetric_group(insert(a, s)) = "+
		"    {permutation_compose(transposition(a, b), p) | "+
		"        b:A, "+
		"        p:permutation(A) | "+
		"        b ∈ insert(a, s) ∧ p ∈ symmetric_group(s)}",
		func(arg *Argument, a *Expr[A], s *Expr[Set[A]]) {
			larger := arg.TermAs[Set[A]]("insert(a, s)")
			aIn := arg.Have(
				"a is a point of insert(a, s)",
				"a ∈ insert(a, s)",
				BySets())
			// ↦ for each permutation q: q moves no point outside insert(a, s) exactly when it is such a product
			arg.Do(Simp(Fwd(set_basic.Extension.Inst[Permutation[A]]())))
			q := arg.FixAs[Permutation[A]]("q")
			product := MakeProp(arg.Term("q ∈ symmetric_group(insert(a, s)) ⇔ " +
				"∃b:A. ∃p:permutation(A). " +
				"    (b ∈ insert(a, s) ∧ p ∈ symmetric_group(s)) ∧ q = transposition(a, b) * p"))
			arg.Do(Suffices(
				product,
				"to lie in the set is to be (a b)·p for a point b of insert(a, s) and a permutation p of s",
				BySets(ResidentHyp(product))))
			arg.Iff()
			arg.Forward(
				"q is (a b)·p, b the point q sends a to and p the permutation (a b)·q",
				func(arg *Argument, qIn Fact) {
					image := arg.TermAs[A]("permutation_map(q, a)")
					arg.Take(image)
					bDef := arg.Let("b", image)
					undone := arg.TermAs[Permutation[A]]("transposition(a, b) * q")
					arg.Take(undone)
					pDef := arg.Let("p", undone)
					bIn := arg.Have(
						"b lies in insert(a, s): q keeps insert(a, s) in itself, and a lies there",
						"b ∈ insert(a, s)",
						By(Normalized, bDef, qIn, aIn, SymmetricGroupMapsInto.At(larger, q, a)))
					qFixes := arg.Have(
						"q leaves every point outside insert(a, s) where it is",
						"∀y:A. y ∉ insert(a, s) ⇒ permutation_map(q, y) = y",
						By(qIn, InSymmetricGroup))
					pIn := arg.Have(
						"p moves no point outside s",
						"p ∈ symmetric_group(s)",
						Derive(func(arg *Argument) {
							arg.Do(pDef.Rw(), Simp(Fwd(InSymmetricGroup)))
							x := arg.FixAs[A]("x")
							outside := arg.Assume()
							arg.Cases(arg.Term("x = a"))
							arg.When(
								"at a: q sends a to b, and (a b) sends b back to a",
								func(arg *Argument, atA Fact) {
									arg.Show(
										"so p returns a to a",
										Simp(Fwd(MapCompose), Fwd(MapTransposition)),
										By(atA, bDef))
								})
							arg.Otherwise(
								"elsewhere x lies outside insert(a, s), where q leaves it, and is not b",
								func(arg *Argument, notA Fact) {
									beyond := arg.Have(
										"x lies outside insert(a, s)",
										"x ∉ insert(a, s)",
										BySets(notA, outside))
									fixed := arg.Have(
										"so q leaves x where it is",
										"permutation_map(q, x) = x",
										By(beyond, qFixes.At(x)))
									notB := arg.Have(
										"and x is not b, which lies in insert(a, s)",
										"x ≠ b",
										By(beyond, bIn))
									arg.Show(
										"so (a b) leaves x where q left it",
										Simp(Fwd(MapCompose), Fwd(MapTransposition)),
										By(Normalized, notA, notB, fixed))
								})
						}))
					undo := arg.Have(
						"(a b) undoes itself, so (a b)·p is q",
						"q = transposition(a, b) * p",
						CalcEq(
							Leg(
								arg.Term("permutation_identity * q"),
								"the identity leaves q as it is",
								By(group.LeftIdentity.Read(SymmetricGroup).At(q))),
							Leg(
								arg.Term("transposition(a, b) * transposition(a, b) * q"),
								"which is the transposition twice",
								Simp(Fwd(TranspositionSelfInverse)),
								Basic()),
							Leg(
								arg.Term("transposition(a, b) * (transposition(a, b) * q)"),
								"regrouped",
								By(group.Assoc.Read(SymmetricGroup).At(arg.TermAs[Permutation[A]]("transposition(a, b)"),
									arg.TermAs[Permutation[A]]("transposition(a, b)"), q))),
							FinalLeg(
								"and (a b)·q is p",
								By(Normalized, pDef)),
						))
					arg.Show(
						"b and p are the point and the permutation asked for",
						By(bIn, pIn, undo))
				})
			arg.Backward(
				"(a b)·p moves no point outside insert(a, s): neither "+
					"factor does, and the group is closed under products",
				func(arg *Argument, built Fact) {
					b, p, parts := arg.Unpack2As[A, Permutation[A]](built, "b", "p")
					given := arg.Conjuncts(
						parts,
						"b lies in insert(a, s)",
						"p moves no point outside s",
						"q is (a b)·p")
					swap := arg.Have(
						"(a b) moves no point outside insert(a, s): a and b both lie there",
						"transposition(a, b) ∈ symmetric_group(insert(a, s))",
						By(aIn, given[0], TranspositionInSymmetricGroup.At(larger, a, b)))
					grows := arg.Have(
						"s lies in insert(a, s)",
						"s ⊆ insert(a, s)",
						BySets())
					included := arg.Have(
						"so a permutation moving no point outside s moves none outside insert(a, s)",
						"symmetric_group(s) ⊆ symmetric_group(insert(a, s))",
						By(grows, SymmetricGroupMono.At(s, larger)))
					widened := arg.Have(
						"p among them",
						"p ∈ symmetric_group(insert(a, s))",
						By(given[1], arg.Unfolded(included, set_basic.SubsetDef).At(p)))
					subgroup := arg.Have(
						"the permutations moving no point outside insert(a, s) form a subgroup",
						"subgroup(permutation_group, symmetric_group(insert(a, s)))",
						By(SymmetricGroupSubgroup.At(larger)))
					permutations := arg.TermAs[group.GroupOps[Permutation[A]]]("permutation_group")
					arg.Show(
						"so it holds (a b)·p, which is q",
						given[2].Rw(),
						By(
							group.SubgroupMul.At(permutations, arg.TermAs[Set[Permutation[A]]]("symmetric_group(insert(a, s))"),
								arg.TermAs[Permutation[A]]("transposition(a, b)"), p),
							subgroup,
							swap,
							widened))
				})
		}),
})}

// InsertProductsDistinct — when a is new to s, the product (a b)·p with p
// a permutation of s determines b and p, so the products counted in
// SymmetricGroupInsert are pairwise distinct. Neither p nor q moves a,
// which lies outside s, so (a b)·p sends a to b and (a c)·q sends it to
// c; one permutation sends a to one point, so b = c. The two products are
// then (a b)·p and (a b)·q, and in the symmetric group (a b) cancels on
// the left.
var InsertProductsDistinct = insertProductsDistinctThm{family.Add(registry.ProofEntry{
	Name: "InsertProductsDistinct",
	Key:  "prop_e09addfebf1644a2",
	Build: family.Theorem(Statement{
		Binders: "∀a b c:A. ∀s:set(A). ∀p q:permutation(A).",
		Hypotheses: []string{
			"a ∉ s",
			"p ∈ symmetric_group(s)",
			"q ∈ symmetric_group(s)",
			"transposition(a, b) * p = transposition(a, c) * q",
		},
		Conclusion: "b = c ∧ p = q",
	},
		func(arg *Argument, a, b, c *Expr[A], s *Expr[Set[A]], p, q *Expr[Permutation[A]], given Fact) {
			parts := arg.Conjuncts(
				given,
				"a lies outside s",
				"p moves no point outside s",
				"q moves no point outside s",
				"the two products are one permutation")
			pFixes := arg.Have(
				"p leaves every point outside s where it is",
				"∀x:A. x ∉ s ⇒ permutation_map(p, x) = x",
				By(parts[1], InSymmetricGroup))
			qFixes := arg.Have(
				"and so does q",
				"∀x:A. x ∉ s ⇒ permutation_map(q, x) = x",
				By(parts[2], InSymmetricGroup))
			same := arg.Have(
				"one permutation sends a to one point, so b = c",
				"b = c",
				CalcEq(
					Leg(
						arg.Term("permutation_map(transposition(a, b) * p, a)"),
						"(a b)·p sends a to b: p leaves a where it is, and (a b) moves it to b",
						Simp(Fwd(MapCompose), Fwd(MapTransposition)),
						By(parts[0], pFixes.At(a))),
					Leg(
						arg.Term("permutation_map(transposition(a, c) * q, a)"),
						"the two products are one permutation",
						By(Normalized, parts[3])),
					FinalLeg(
						"and (a c)·q sends a to c: q leaves a where it is, and (a c) moves it to c",
						Simp(Fwd(MapCompose), Fwd(MapTransposition)),
						By(parts[0], qFixes.At(a))),
				))
			sameFactor := arg.Have(
				"so the two products are (a b)·p and (a b)·q",
				"transposition(a, b) * p = transposition(a, b) * q",
				CalcEq(
					Leg(
						arg.Term("transposition(a, c) * q"),
						"the two products are one permutation",
						By(parts[3])),
					FinalLeg(
						"and c is b",
						By(Normalized, same)),
				))
			cancelled := arg.Have(
				"and (a b) cancels on the left",
				"p = q",
				By(sameFactor, group.LeftCancel.Read(SymmetricGroup)))
			arg.Show(
				"b = c and p = q",
				By(same, cancelled))
		}),
})}

// ---------------------------------------------------------------------------
// The count
// ---------------------------------------------------------------------------

// CardSymmetricGroup — the symmetric group on a finite set of n points has
// n! elements. By induction on the set: on ∅ it is the identity alone,
// and 0! is 1. Laying a new point a into u, the permutations of
// insert(a, u) are the products (a b)·p (SymmetricGroupInsert), which
// are pairwise distinct (InsertProductsDistinct), so there are as many as
// pairs (b, p) — suc(card(u)) choices of b, card(u)! of p — and that is
// suc(card(u))!.
var CardSymmetricGroup = cardSymmetricGroupThm{family.Add(registry.ProofEntry{
	Name: "CardSymmetricGroup",
	Key:  "prop_8e6f86ada349acb4",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(A).",
		Hypotheses: []string{
			"finite(s)",
		},
		Conclusion: "has_size(symmetric_group(s), factorial(card(s)))",
	},
		func(arg *Argument, s *Expr[Set[A]], finiteS Fact) {
			arg.Show(
				"by induction on the finite set, one new point at a time",
				ByInduction(finite_set.FiniteInductFresh, finiteS,

					Case(
						"∅: the identity alone, and 0! is 1",
						Derive(func(base *Argument) {
							single := base.TermAs[Set[Permutation[A]]]("{permutation_identity⟨A:A⟩}")
							identity := base.TermAs[Permutation[A]]("permutation_identity⟨A:A⟩")
							base.Show(
								"a one-point set has one point",
								Simp(Fwd(SymmetricGroupEmpty), Fwd(cardinality.CardClauses), Fwd(nat_arith.Factorial)),
								By(
									Normalized,
									cardinality.FiniteHasSize.At(single),
									finite_set.FiniteSing.At(identity),
									cardinality.CardSing.At(identity)))
						})),

					Case(
						"insert: a new point multiplies the count by the new number of points",
						Derive(func(step *Argument) {
							a := step.FixAs[A]("a")
							u := step.FixAs[Set[A]]("u")
							carried := step.Assume()
							parts := step.Conjuncts(
								carried,
								"the symmetric group on u has card(u)! elements",
								"a is new to u",
								"u is finite")
							countOnU, fresh := parts[0], parts[1]

							transpositionProduct := step.TermAs[Fun[A, Fun[Permutation[A], Permutation[A]]]](
								"λb:A. λp:permutation(A). transposition(a, b) * p")
							enlargedSet := step.TermAs[Set[A]]("insert(a, u)")
							permutationsOnU := step.TermAs[Set[Permutation[A]]]("symmetric_group(u)")

							grows := step.Have(
								"a new point counts one more",
								"card(insert(a, u)) = suc(card(u))",
								By(carried, cardinality.InsertCountsOneMore.At(u, a)))
							points := step.Have(
								"so insert(a, u), finite as u is, has suc(card(u)) points",
								"has_size(insert(a, u), suc(card(u)))",
								By(
									Normalized,
									carried,
									grows,
									cardinality.FiniteHasSize.At(enlargedSet),
									finite_set.FiniteInsert.At(a, u)))
							// Stated in HasSizeProductImage's own premise shape and proved
							// point by point: one By of InsertProductsDistinct over the
							// quantified claim recorded two keys and a route the replay's
							// divergence whistle refuses.
							distinct := step.Have(
								"the products (a b)·p are pairwise distinct, a being new",
								Statement{
									Binders: "∀b c:A. ∀p q:permutation(A).",
									Hypotheses: []string{
										"b ∈ insert(a, u)",
										"p ∈ symmetric_group(u)",
										"c ∈ insert(a, u)",
										"q ∈ symmetric_group(u)",
										"transposition(a, b) * p = transposition(a, c) * q",
									},
									Conclusion: "b = c ∧ p = q",
								},
								Derive(func(d *Argument) {
									b := d.FixAs[A]("b")
									c := d.FixAs[A]("c")
									p := d.FixAs[Permutation[A]]("p")
									q := d.FixAs[Permutation[A]]("q")
									given := d.Assume()
									d.Show(
										"a is outside u, so the two products determine b and p",
										By(fresh, given, InsertProductsDistinct.At(a, b, c, u, p, q)))
								}))
							productCount := step.Have(
								"so they number suc(card(u)) · card(u)!",
								"has_size({permutation_compose(transposition(a, b), p) | "+
									"        b:A, "+
									"        p:permutation(A) | "+
									"        b ∈ insert(a, u) ∧ p ∈ symmetric_group(u)}, "+
									"    suc(card(u)) * factorial(card(u)))",
								By(
									points,
									countOnU,
									distinct,
									cardinality.HasSizeProductImage.At(transpositionProduct, enlargedSet, permutationsOnU,
										step.TermAs[Nat]("suc(card(u))"), step.TermAs[Nat]("factorial(card(u))"))))
							step.Show(
								"which is suc(card(u))!, the permutations of insert(a, u) being those products",
								Simp(Fwd(SymmetricGroupInsert)),
								grows.Rw(),
								Simp(Fwd(nat_arith.Factorial)),
								By(productCount))
						})),
				))
		}),
})}

// SymmetricGroupFinite — the symmetric group on a finite set is finite: it
// has card(s)! elements (CardSymmetricGroup), and a set with a size is
// finite.
var SymmetricGroupFinite = symmetricGroupFiniteThm{family.Add(registry.ProofEntry{
	Name: "SymmetricGroupFinite",
	Key:  "prop_bf86a705443ad132",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(A).",
		Hypotheses: []string{
			"finite(s)",
		},
		Conclusion: "finite(symmetric_group(s))",
	},
		func(arg *Argument, s *Expr[Set[A]], finiteS Fact) {
			arg.Show(
				"it has card(s)! elements, and a set with a size is finite",
				By(
					finiteS,
					CardSymmetricGroup.At(s),
					cardinality.HasSizeDef.At(
						arg.TermAs[Set[Permutation[A]]]("symmetric_group(s)"), arg.TermAs[Nat]("factorial(card(s))"))))
		}),
})}

// CardPermutations — a finite type of n points has n! permutations: the
// count on the whole type, where the symmetric group is every
// permutation (SymmetricGroupUniverse).
var CardPermutations = cardPermutationsThm{family.Add(registry.ProofEntry{
	Name: "CardPermutations",
	Key:  "prop_bf9d1f3c3acff50c",
	Build: family.Theorem(Statement{
		Hypotheses: []string{
			"finite(𝕌⟨A:A⟩)",
		},
		Conclusion: "has_size(𝕌⟨A:permutation(A)⟩, factorial(card(𝕌⟨A:A⟩)))",
	},
		func(arg *Argument, finite Fact) {
			whole := arg.TermAs[Set[A]]("𝕌⟨A:A⟩")
			sized := arg.Have(
				"the symmetric group on the whole type has card(𝕌)! elements",
				"has_size(symmetric_group(𝕌⟨A:A⟩), factorial(card(𝕌⟨A:A⟩)))",
				By(finite, CardSymmetricGroup.At(whole)))
			arg.Show(
				"and it is every permutation",
				Simp(Rev(SymmetricGroupUniverse)),
				By(sized))
		}),
})}

// ---------------------------------------------------------------------------
// Lagrange's theorem in the symmetric group
// ---------------------------------------------------------------------------

// SubgroupOrderDividesFactorial — a group of permutations of n points has
// order dividing n!. It is Lagrange's theorem (finite_group.LagrangeDivides) read
// at the symmetric group: the permutations moving no point outside s form
// a finite subgroup (SymmetricGroupSubgroup) with card(s)! elements
// (CardSymmetricGroup), and h is a subgroup inside it.
var SubgroupOrderDividesFactorial = subgroupOrderDividesFactorialThm{family.Add(registry.ProofEntry{
	Name: "SubgroupOrderDividesFactorial",
	Key:  "prop_1400a560b2275421",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(A). ∀h:set(permutation(A)).",
		Hypotheses: []string{
			"finite(s)",
			"subgroup(permutation_group, h)",
			"h ⊆ symmetric_group(s)",
		},
		Conclusion: "card(h) ∣ factorial(card(s))",
	},
		func(arg *Argument, s *Expr[Set[A]], h *Expr[Set[Permutation[A]]], given Fact) {
			parts := arg.Conjuncts(
				given,
				"s is finite",
				"h is a subgroup",
				"h lies in the symmetric group on s")
			permutationsOnS := arg.TermAs[Set[Permutation[A]]]("symmetric_group(s)")
			sized := arg.Have(
				"the symmetric group on s has card(s)! elements",
				"has_size(symmetric_group(s), factorial(card(s)))",
				By(parts[0], CardSymmetricGroup.At(s)))
			known := arg.Conjuncts(
				arg.Unfolded(sized, cardinality.HasSizeDef),
				"so it is finite",
				"and card(s)! is its count")
			finite, count := known[0], known[1]
			// Lagrange's theorem asks for subgroups of the group restricted
			// to the whole type, which is the permutation group itself
			// (RestrictPermutationGroupUniverse).
			divides := arg.Have(
				"Lagrange's theorem in the symmetric group: card(h) divides that count",
				"card(h) ∣ card(symmetric_group(s))",
				By(
					Normalized,
					parts[1],
					parts[2],
					finite,
					RestrictPermutationGroupUniverse,
					SymmetricGroupSubgroup.At(s),
					finite_group.LagrangeDivides.Read(SymmetricGroup).At(h, permutationsOnS)))
			arg.Show(
				"which is card(s)!",
				count.RwRev(),
				By(divides))
		}),
})}
