// generators.go — the partition of unity one = Σ x(i) * y(i) of an
// invertible fractional ideal, which expands each member c of the field as
// Σ (c * x(i)) * y(i), makes the ideal finitely generated and makes
// dividing by it taking the colon; and, when L is the field of fractions
// of S, its common denominator and a nonzero principal ideal c · S inside
// it.

package invertible_fractional_ideal

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/fractional_ideal"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_ideal"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// InvertiblePartitionOfUnity — an invertible fractional ideal writes one
// as a finite sum of products of its members with members of its inverse.
// The products x * y, x in M and y in (S : M), span M · (S : M) = S, which
// holds one; S scales them into themselves, since c * (x * y) = x * (c * y)
// with c * y in the S-submodule (S : M), so their span is their finite
// sums, and one such sum, its terms factored, is the partition of unity.
var InvertiblePartitionOfUnity = invertiblePartitionOfUnityThm{family.Add(registry.ProofEntry{
	Name: "InvertiblePartitionOfUnity",
	Key:  "prop_4c34cac1278d0f99",
	Reading: "This is the identity L.one = Σ x(i) * y(i) every argument about an invertible " +
		"ideal starts from: it makes M locally principal. The coefficients from S are absorbed " +
		"into the y(i), since (S : M) is an S-submodule. n ≥ 1 is forced by L.one ≠ zero.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S M:set(A).",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"«wfInvertible»(M)",
		},
		Conclusion: "∃n:num. ∃x y:(num → A). " +
			"    (∀i:num. i < n ⇒ x(i) ∈ M ∧ y(i) ∈ «wfInverse»(M)) ∧ " +
			"    module_sum(L.add, L.zero, {i:num | i < n}, λi:num. x(i) * y(i)) = L.one",
	},
		func(a *Argument, L field.FieldFact[on.L], S, M *Expr[Set[A]], hypotheses Fact) {
			parts := a.Conjuncts(
				hypotheses,
				"S is a subring of the field",
				"M is invertible")
			subring, invertible := parts[0], parts[1]
			unfolded := a.Conjuncts(
				a.Unfolded(invertible, fractional_ideal.InvertibleFractionalDef),
				"M is a fractional ideal",
				"and its product with (S : M) is S")
			fractional, product := unfolded[0], unfolded[1]
			overS := a.Have(
				"the field is a module over S",
				"module_on(«wfScalars», «wfField»)",
				By(fractional_ideal.FieldModuleOn.Read(L).At(S), subring))
			mInL := a.Have(
				"a fractional ideal lies in the field",
				"M ⊆ L.carrier",
				By(submodule.SubmoduleSubset.Read(fractional)))
			inverse := a.Have(
				"(S : M) is a fractional ideal",
				"«wfFractional»(«wfInverse»(M))",
				By(fractional_ideal.FractionalInverseSubmodule.Read(L).At(S, M), subring, mInL))
			inverseInL := fractional_ideal.FractionalInverseSubset.Read(L).At(S, M)

			P, definedP := a.LetAs[Set[A]]("P", "{x * y | x:A, y:A | x ∈ M ∧ y ∈ «wfInverse»(M)}")
			formed := a.Have(
				"a product of a member of M and a member of (S : M) lies in P",
				"∀x y:A. x ∈ M ∧ y ∈ «wfInverse»(M) ⇒ x * y ∈ P",
				BySets(definedP))
			factored := a.Have(
				"and every member of P is such a product",
				"∀u:A. u ∈ P ⇒ ∃x y:A. x ∈ M ∧ y ∈ «wfInverse»(M) ∧ u = x * y",
				BySets(definedP))
			within := a.Have(
				"the factors lie in the field, so P does",
				"P ⊆ L.carrier",
				BySets(factored, mInL, inverseInL, comm_ring.MulIn.Read(field.RingOn.Read(L))))
			scaled := a.Have(
				"S scales P into itself",
				"∀c u:A. c ∈ S ∧ u ∈ P ⇒ c * u ∈ P",
				Derive(func(b *Argument) {
					b.FixAs[A]("c")
					u := b.FixAs[A]("u")
					given := b.Conjuncts(
						b.Assume(),
						"c lies in S",
						"u lies in P")
					x, _, factorization := b.Obtain2(
						"u is a product x * y",
						"∃x y:A. x ∈ M ∧ y ∈ «wfInverse»(M) ∧ u = x * y",
						By(factored.At(u), given[1]))
					factors := b.Conjuncts(
						factorization,
						"x lies in M",
						"y lies in (S : M)",
						"u = x * y")
					scaledY := b.Have(
						"(S : M) is an S-submodule, so it holds c * y",
						"c * y ∈ «wfInverse»(M)",
						By(submodule.SubmoduleSmul.Read(inverse), given[0], factors[1]))
					inL := b.Have(
						"c, x and y lie in the field",
						"c ∈ L.carrier ∧ x ∈ L.carrier ∧ y ∈ L.carrier",
						BySets(comm_ring.SubringSubset.Read(subring), mInL, inverseInL, given[0], factors[0], factors[1]))
					regroup := b.Have(
						"the field's product regroups",
						"c * (x * y) = x * (c * y)",
						ByArith(field.RingOn.Read(L), inL))
					b.Show(
						"so c * u = x * (c * y) is a product of the same kind",
						By(formed.At(x, b.TermAs[A]("c * y")), factors[0], scaledY, factors[2], regroup))
				}))
			spanned := a.Have(
				"P spans M · (S : M), which is S",
				"«wfSpan»(P) = S",
				definedP.Rw(),
				By(product, fractional_ideal.FractionalMulDef))
			sums := a.Have(
				"closed under scaling, P spans its finite sums",
				"«wfSpan»(P) = "+
					"{module_sum(L.add, L.zero, {i:num | i < n}, F) | n:num, F:num → A | ∀i:num. i < n ⇒ F(i) ∈ P}",
				By(submodule.SpanFiniteSums.Read(overS).At(P), within, scaled))
			oneIsSum := a.Have(
				"one, in S, is such a sum",
				"L.one ∈ "+
					"{module_sum(L.add, L.zero, {i:num | i < n}, F) | n:num, F:(num → A) | ∀i:num. i < n ⇒ F(i) ∈ P}",
				sums.RwRev(),
				spanned.Rw(),
				By(comm_ring.SubringOne.Read(subring)))
			n, _, expansion := a.Obtain2(
				"so L.one = Σ F(i) over i < n, every F(i) in P",
				"∃n:num. "+
					"    ∃F:(num → A).(∀i:num. i < n ⇒ F(i) ∈ P) ∧ "+
					"    L.one = module_sum(L.add, L.zero, {i:num | i < n}, F)",
				BySets(oneIsSum))
			expanded := a.Conjuncts(
				expansion,
				"every term lies in P",
				"and the terms sum to one")
			terms, sum := expanded[0], expanded[1]
			perTerm := a.Have(
				"each term is a product",
				"∀i:num. i < n ⇒ ∃x y:A. x ∈ M ∧ y ∈ «wfInverse»(M) ∧ F(i) = x * y",
				By(terms, factored))
			x, y, factors := a.Obtain2(
				"choose the factors of every term",
				"∃x y:(num → A). ∀i:num. i < n ⇒ x(i) ∈ M ∧ y(i) ∈ «wfInverse»(M) ∧ F(i) = x(i) * y(i)",
				By(perTerm))
			agree := a.Have(
				"the sum of F is the sum of the products, term by term",
				"module_sum(L.add, L.zero, {i:num | i < n}, F) = "+
					"module_sum(L.add, L.zero, {i:num | i < n}, λi:num. x(i) * y(i))",
				By(factors, module.ModuleSumCongruence))
			a.Take(n)
			a.Take(x)
			a.Take(y)
			a.Show(
				"so L.one = Σ x(i) * y(i) over i < n",
				By(factors, agree, sum))
		}),
})}

// PartitionOfUnityExpansion — a partition of unity one = Σ x(i) * y(i)
// in the field expands every member c of it as c = Σ (c * x(i)) * y(i):
// c = c * one, c passes into the finite sum, and each term regroups.
var PartitionOfUnityExpansion = partitionOfUnityExpansionThm{family.Add(registry.ProofEntry{
	Name: "PartitionOfUnityExpansion",
	Key:  "prop_81daec8cb639f24c",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀c:A. ∀n:num. ∀x y:(num → A).",
		Hypotheses: []string{
			"c ∈ L.carrier",
			"∀i:num. i < n ⇒ x(i) ∈ L.carrier ∧ y(i) ∈ L.carrier",
			"module_sum(L.add, L.zero, {i:num | i < n}, λi:num. x(i) * y(i)) = L.one",
		},
		Conclusion: "c = module_sum(L.add, L.zero, {i:num | i < n}, λi:num. c * x(i) * y(i))",
	},
		func(
			arg *Argument,
			L field.FieldFact[on.L],
			c *Expr[A],
			n *Expr[Nat],
			x, y *Arrow[Nat, A],
			given Fact,
		) {
			parts := arg.Conjuncts(
				given,
				"c lies in the field",
				"and so does each x(i) and each y(i)",
				"and one is the sum of the products x(i) * y(i)")
			cInL, members, sumOne := parts[0], parts[1], parts[2]
			fieldRing := field.RingOn.Read(L)
			below := arg.TermAs[Set[Nat]]("{i:num | i < n}")
			finiteBelow := arg.Have(
				"the indices below n are finitely many",
				"finite({i:num | i < n})",
				Cite(num_segment.FiniteBelowStrict))
			regroup := arg.Have(
				"termwise, c * (x(i) * y(i)) = (c * x(i)) * y(i)",
				"∀i:num. i < n ⇒ c * (x(i) * y(i)) = c * x(i) * y(i)",
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]("i")
					inRange := b.Assume()
					b.Show(
						"a regrouping of three members of the field",
						ByArith(fieldRing, members.At(i), inRange, cInL))
				}))
			passIn := arg.Have(
				"c passes into the finite sum, the field a module over itself",
				"c * module_sum(L.add, L.zero, {i:num | i < n}, λi:num. x(i) * y(i)) = "+
					"module_sum(L.add, L.zero, {i:num | i < n}, λi:num. c * (x(i) * y(i)))",
				By(
					finiteBelow,
					members,
					comm_ring.MulIn.Read(fieldRing),
					module.ModuleSumSmul.Read(module.RegularModuleOn.Read(fieldRing)).At(
						below, arg.MemberOf[on.L](c, cInL), arg.TermAs[Fun[Nat, A]]("λi:num. x(i) * y(i)"))))
			arg.Show(
				"c = c * one = c * Σ x(i) * y(i) = Σ (c * x(i)) * y(i)",
				CalcEq(
					Leg(
						arg.TermAs[A]("c * L.one"),
						"one is the unit of the field",
						ByArith(fieldRing, cInL)),
					Leg(
						arg.TermAs[A]("c * module_sum(L.add, L.zero, {i:num | i < n}, λi:num. x(i) * y(i))"),
						"one is the sum of the products x(i) * y(i)",
						By(sumOne)),
					Leg(
						arg.TermAs[A]("module_sum(L.add, L.zero, {i:num | i < n}, λi:num. c * (x(i) * y(i)))"),
						"c passes into the finite sum",
						By(passIn)),
					FinalLeg(
						"and each term regroups",
						By(regroup, module.ModuleSumCongruence)),
				))
		}),
})}

// InvertibleGenerated — an invertible fractional ideal is finitely
// generated: write one = Σ_{i<n} x(i) * y(i) with x(i) ∈ M and y(i) ∈
// (S : M) and take E = {x(i) | i < n}. E lies in M, so its span does;
// and a member m of M is Σ_{i<n} (m * x(i)) * y(i)
// (PartitionOfUnityExpansion), each term the generator x(i) scaled by
// y(i) * m ∈ S.
var InvertibleGenerated = invertibleGeneratedThm{family.Add(registry.ProofEntry{
	Name: "InvertibleGenerated",
	Key:  "prop_9927550d4becd7d3",
	Reading: "The generators are read off one expression of L.one as a finite sum of " +
		"products x * f with x ∈ M and f ∈ (S : M); no finiteness hypothesis on S enters.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S M:set(A).",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"«wfInvertible»(M)",
		},
		Conclusion: "∃E:set(A). finite(E) ∧ E ⊆ M ∧ «wfSpan»(E) = M",
		Abbrev: Abbrev{
			// The span of the generators x(i), i < n, the partition of unity names.
			{Name: "generatedSpan", Text: "«wfSpan»(image(x, {i:num | i < n}))"},
		},
	},
		func(a *Argument, L field.FieldFact[on.L], S, M *Expr[Set[A]], hypotheses Fact) {
			parts := a.Conjuncts(
				hypotheses,
				"S is a subring of the field",
				"M is invertible")
			subring, invertible := parts[0], parts[1]
			fieldRing := field.RingOn.Read(L)
			n, x, y, partition := a.Unpack3As[Nat, Fun[Nat, A], Fun[Nat, A]](
				GroupPremises(parts[0], parts[1], InvertiblePartitionOfUnity.Read(L).At(S, M)), "n", "x", "y")
			split := a.Conjuncts(
				partition,
				"each x(i) lies in M and each y(i) in (S : M)",
				"and one is the sum of the products x(i) * y(i)")
			onRange, sumOne := split[0], split[1]
			ranges := a.Have(
				"each x(i) lies in M, and each y(i) lies in L and multiplies M into S",
				"∀i:num. i < n ⇒ x(i) ∈ M ∧ y(i) ∈ L.carrier ∧ (∀m:A. m ∈ M ⇒ y(i) * m ∈ S)",
				BySets(a.Unfolded(onRange, fractional_ideal.FractionalInverseDef)))
			below := a.TermAs[Set[Nat]]("{i:num | i < n}")
			generators := a.TermAs[Set[A]]("image(x, {i:num | i < n})")
			span := a.TermAs[Set[A]]("«generatedSpan»")
			scalars, fieldOps :=
				a.TermAs[module_record.RingOps[A]]("«wfScalars»"),
				a.TermAs[module_record.ModuleOps[A, A]]("«wfField»")
			inM := a.Have(
				"the generators lie in M",
				"image(x, {i:num | i < n}) ⊆ M",
				BySets(onRange))
			opened := a.Conjuncts(
				a.Unfolded(invertible, fractional_ideal.InvertibleFractionalDef),
				"M is an S-submodule of the field",
				"whose product with (S : M) is S")
			fractional := opened[0]
			mInL := a.Have(
				"so M lies in the field",
				"M ⊆ L.carrier",
				By(submodule.SubmoduleSubset.Read(fractional)))
			fieldModule := a.Have(
				"the field is an S-module",
				"module_on(«wfScalars», «wfField»)",
				By(fractional_ideal.FieldModuleOn.Read(L).At(S), subring))
			spanSub := a.Have(
				"their span is an S-submodule of the field, the generators lying in M and so in L",
				"«wfFractional»(«generatedSpan»)",
				By(inM, mInL, set_order.SubsetTrans, submodule.SpanSubmodule.Read(fieldModule).At(generators)))
			within := a.Have(
				"the span lies in M, a submodule holding the generators",
				"«generatedSpan» ⊆ M",
				By(fractional, inM, submodule.SpanLeast))
			members := a.Have(
				"each x(i) and each y(i) lies in the field",
				"∀i:num. i < n ⇒ x(i) ∈ L.carrier ∧ y(i) ∈ L.carrier",
				BySets(ranges, mInL))
			spanned := a.Have(
				"each generator lies in the span",
				"∀i:num. i < n ⇒ x(i) ∈ «generatedSpan»",
				BySets(submodule.SubsetSpan.At(scalars, fieldOps, generators)))

			spanning := a.Have(
				"every m of M is a combination of the generators with coefficients in S",
				"∀m:A. m ∈ M ⇒ m ∈ «generatedSpan»",
				Derive(func(b *Argument) {
					m := b.FixAs[A]("m")
					mIn := b.Assume()
					mL := b.Have(
						"m lies in the field",
						"m ∈ L.carrier",
						BySets(mInL, mIn))
					coefficients := b.Have(
						"each y(i) * m lies in S, as y(i) lies in (S : M)",
						"∀i:num. i < n ⇒ y(i) * m ∈ S",
						b.ForEach(func(i *Expr[Nat]) Action { return BySets(ranges.At(i), mIn) }))
					terms := b.Have(
						"so each (m * x(i)) * y(i), the generator x(i) scaled by y(i) * m ∈ S, lies in the span",
						"∀i:num. i < n ⇒ m * x(i) * y(i) ∈ «generatedSpan»",
						Derive(func(c *Argument) {
							i := c.FixAs[Nat]("i")
							inRange := c.Assume()
							regroup := c.Have(
								"the field's product regroups",
								"m * x(i) * y(i) = y(i) * m * x(i)",
								ByArith(fieldRing, members.At(i), inRange, mL))
							c.Show(
								"y(i) * m lies in S and x(i) in the span, an S-submodule",
								regroup.Rw(),
								By(spanned.At(i), coefficients.At(i), inRange, submodule.SubmoduleSmul.Read(spanSub)))
						}))
					sumIn := b.Have(
						"and so does their sum",
						"module_sum(L.add, L.zero, {i:num | i < n}, λi:num. m * x(i) * y(i)) ∈ «generatedSpan»",
						By(
							fractional_ideal.FractionalSumIn.Read(L).At(
								S, span, n, b.TermAs[Fun[Nat, A]]("λi:num. m * x(i) * y(i)")),
							subring,
							spanSub,
							terms))
					b.Show(
						"so m, which the partition of unity expands as that sum, lies in the span",
						By(PartitionOfUnityExpansion.Read(L).At(b.MemberOf[on.L](m, mL), n, x, y), members, sumOne, sumIn))
				}))
			a.Take(generators)
			a.Show(
				"the generators are finitely many, lie in M and span it",
				By(
					num_segment.FiniteBelowStrict,
					finite_set.FiniteImage.At(x, below),
					inM,
					within,
					spanning,
					set_basic.SubsetDef,
					set_order.SubsetAntisym))
		}),
})}

// MulInverseIsColon — dividing by an invertible fractional ideal is taking
// the colon: for X invertible and Y a fractional ideal, Y · (S : X) is the
// colon (Y : X), the members a of L with a · X ⊆ Y. A product n * z with
// n ∈ Y and z ∈ (S : X) carries each m of X to (z * m) * n, an S-multiple
// of n, so the colon, a fractional ideal, holds the products and their
// span Y · (S : X). Conversely, with one = Σ x(i) * y(i) a partition of
// unity of X, a member c of the colon is c * one = Σ (c * x(i)) * y(i), a
// finite sum of products of Y with (S : X).
var MulInverseIsColon = mulInverseIsColonThm{family.Add(registry.ProofEntry{
	Name: "MulInverseIsColon",
	Key:  "prop_d378de4fd84cd5d4",
	Reading: "X invertible is load-bearing for ⊇ alone: Y · (S : X) lies in the colon for " +
		"every X inside L. Y a fractional ideal is what keeps the S-multiples (z * m) * n inside Y.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S X Y:set(A).",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"«wfInvertible»(X)",
			"«wfFractional»(Y)",
		},
		Conclusion: "«wfMul»(Y, «wfInverse»(X)) = {y:A | y ∈ L.carrier ∧ (∀n:A. n ∈ X ⇒ y * n ∈ Y)}",
		Abbrev: Abbrev{
			// The product Y · (S : X), and the colon (Y : X) it equals.
			{Name: "product", Text: "«wfMul»(Y, «wfInverse»(X))"},
			{Name: "colon", Text: "{y:A | y ∈ L.carrier ∧ (∀n:A. n ∈ X ⇒ y * n ∈ Y)}"},
		},
	},
		func(arg *Argument, L field.FieldFact[on.L], S, X, Y *Expr[Set[A]], hypotheses Fact) {
			parts := arg.Conjuncts(
				hypotheses,
				"S is a subring of the field",
				"X is invertible",
				"Y is a fractional ideal")
			subring, invertible, fractionalY := parts[0], parts[1], parts[2]
			fieldRing := field.RingOn.Read(L)
			opened := arg.Conjuncts(
				arg.Unfolded(invertible, fractional_ideal.InvertibleFractionalDef),
				"X is a fractional ideal",
				"whose product with (S : X) is S")
			xInL := arg.Have(
				"X lies in the field",
				"X ⊆ L.carrier",
				By(submodule.SubmoduleSubset.Read(opened[0])))
			yInL := arg.Have(
				"and so does Y",
				"Y ⊆ L.carrier",
				By(submodule.SubmoduleSubset.Read(fractionalY)))
			inverseInL := fractional_ideal.FractionalInverseSubset.Read(L).At(S, X)
			inverseSet, productSet, colonSet :=
				arg.TermAs[Set[A]]("«wfInverse»(X)"), arg.TermAs[Set[A]]("«product»"), arg.TermAs[Set[A]]("«colon»")
			colonIdeal := arg.Have(
				"the colon (Y : X) is a fractional ideal",
				"«wfFractional»(«colon»)",
				By(
					fractional_ideal.ColonSubmodule.Read(L).At(S, Y, X),
					comm_ring.SubringSubset.Read(subring),
					fractionalY,
					xInL))
			productsIn := arg.Have(
				"a product n * z with n ∈ Y and z ∈ (S : X) lies in the colon",
				"∀n z:A. n ∈ Y ∧ z ∈ «wfInverse»(X) ⇒ n * z ∈ «colon»",
				Derive(func(b *Argument) {
					n, z := b.FixAs[A]("n"), b.FixAs[A]("z")
					factors := b.Conjuncts(
						b.Assume(),
						"n lies in Y",
						"z lies in (S : X)")
					nInY := factors[0]
					member := b.Have(
						"n and z lie in L, and z carries X into S",
						"n ∈ L.carrier ∧ z ∈ L.carrier ∧ (∀m:A. m ∈ X ⇒ z * m ∈ S)",
						BySets(nInY, yInL, b.Unfolded(factors[1], fractional_ideal.FractionalInverseDef)))
					carries := b.Have(
						"n * z carries X into Y: (n * z) * m = (z * m) * n is an S-multiple of n",
						"∀m:A. m ∈ X ⇒ n * z * m ∈ Y",
						Derive(func(c *Argument) {
							c.FixAs[A]("m")
							mInX := c.Assume()
							mInL := c.Have(
								"m lies in L",
								"m ∈ L.carrier",
								BySets(mInX, xInL))
							regroup := c.Have(
								"the field's product regroups",
								"n * z * m = z * m * n",
								ByArith(fieldRing, mInL, member))
							c.Show(
								"z * m lies in S, and Y is an S-submodule",
								regroup.Rw(),
								By(
									member,
									mInX,
									nInY,
									submodule.SubmoduleSmul.Read(fractionalY).AsFact().At(c.TermAs[A]("z * m"), n)))
						}))
					b.Show(
						"n * z lies in L, so in the colon",
						BySets(member, carries, comm_ring.MulIn.Read(fieldRing).AsFact().At(n, z)))
				}))
			within := arg.Have(
				"so the colon holds their span, Y · (S : X)",
				"«product» ⊆ «colon»",
				By(
					fractional_ideal.FractionalMulLeast.Read(L).At(S, Y, inverseSet, colonSet),
					colonIdeal,
					productsIn))

			n, x, y, partition := arg.Unpack3As[Nat, Fun[Nat, A], Fun[Nat, A]](
				GroupPremises(parts[0], parts[1], InvertiblePartitionOfUnity.Read(L).At(S, X)), "n", "x", "y")
			split := arg.Conjuncts(
				partition,
				"each x(i) lies in X and each y(i) in (S : X)",
				"and one is the sum of the products x(i) * y(i)")
			onRange, sumOne := split[0], split[1]
			members := arg.Have(
				"each x(i) and each y(i) lies in the field",
				"∀i:num. i < n ⇒ x(i) ∈ L.carrier ∧ y(i) ∈ L.carrier",
				BySets(onRange, xInL, inverseInL))
			productIdeal := arg.Have(
				"Y · (S : X) is a fractional ideal",
				"«wfFractional»(«product»)",
				By(fractional_ideal.FractionalMulSubmodule.Read(L).At(S, Y, inverseSet), subring, yInL, inverseInL))
			spanning := arg.Have(
				"every member c of the colon is Σ (c * x(i)) * y(i), a sum of products of Y with (S : X)",
				"∀c:A. c ∈ «colon» ⇒ c ∈ «product»",
				Derive(func(b *Argument) {
					c := b.FixAs[A]("c")
					member := b.Conjuncts(
						b.Have(
							"c lies in L and carries X into Y",
							"c ∈ L.carrier ∧ (∀m:A. m ∈ X ⇒ c * m ∈ Y)",
							BySets(b.Assume())),
						"c lies in L",
						"and carries X into Y")
					cInL, carries := member[0], member[1]
					terms := b.Have(
						"each (c * x(i)) * y(i) is the product of c * x(i) ∈ Y with y(i) ∈ (S : X)",
						"∀i:num. i < n ⇒ c * x(i) * y(i) ∈ «product»",
						Derive(func(d *Argument) {
							d.FixAs[Nat]("i")
							inRange := d.Assume()
							d.Show(
								"c carries x(i) ∈ X into Y",
								By(
									onRange,
									inRange,
									carries,
									fractional_ideal.FractionalMulHolds.Read(L).At(
										S, Y, inverseSet, d.TermAs[A]("c * x(i)"), d.TermAs[A]("y(i)"))))
						}))
					sumIn := b.Have(
						"so their sum lies in Y · (S : X)",
						"module_sum(L.add, L.zero, {i:num | i < n}, λi:num. c * x(i) * y(i)) ∈ «product»",
						By(
							fractional_ideal.FractionalSumIn.Read(L).At(
								S, productSet, n, b.TermAs[Fun[Nat, A]]("λi:num. c * x(i) * y(i)")),
							subring,
							productIdeal,
							terms))
					b.Show(
						"so c, which the partition of unity expands as that sum, lies in it",
						By(
							PartitionOfUnityExpansion.Read(L).At(b.MemberOf[on.L](c, cInL), n, x, y),
							members,
							sumOne,
							sumIn))
				}))
			arg.Show(
				"so the colon lies in Y · (S : X), and the two inclusions are the equation",
				By(within, spanning, set_basic.SubsetDef, set_order.SubsetAntisym))
		}),
})}

// InvertibleSelfColon — the multipliers of an invertible fractional ideal
// are the ring: the colon (X : X), the members z of L with z · X ⊆ X, is
// S. It is X · (S : X) by MulInverseIsColon at Y = X, and that product is
// S because X is invertible.
var InvertibleSelfColon = invertibleSelfColonThm{family.Add(registry.ProofEntry{
	Name: "InvertibleSelfColon",
	Key:  "prop_be411afde4891585",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S X:set(A).",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"«wfInvertible»(X)",
		},
		Conclusion: "{z:A | z ∈ L.carrier ∧ (∀v:A. v ∈ X ⇒ z * v ∈ X)} = S",
	},
		func(a *Argument, L field.FieldFact[on.L], S, X *Expr[Set[A]], hypotheses Fact) {
			parts := a.Conjuncts(
				hypotheses,
				"S is a subring of the field",
				"X is invertible")
			subring, invertible := parts[0], parts[1]
			a.Show(
				"the colon (X : X) is X · (S : X), and X · (S : X) = S since X is invertible",
				By(
					subring,
					invertible,
					a.Unfolded(invertible, fractional_ideal.InvertibleFractionalDef),
					MulInverseIsColon.Read(L).At(S, X, X)))
		}),
})}

// InvertibleCommonDenominator — when L is the field of fractions of S,
// an invertible fractional ideal has a common denominator: a nonzero
// member d of S with d · M ⊆ S. (S : M) holds a nonzero f, since
// otherwise every product of M with (S : M) would be zero and so would
// their span S, which holds one; f is a fraction a/b of members of S,
// and its numerator a = f * b is a common denominator:
// a * m = b * (f * m) with f * m ∈ S.
var InvertibleCommonDenominator = invertibleCommonDenominatorThm{family.Add(registry.ProofEntry{
	Name: "InvertibleCommonDenominator",
	Key:  "prop_7633c2a7aaedeb5f",
	Reading: "That L is the field of fractions of S is load-bearing: with S " +
		"a subfield k of L = k(t) and M = k · t, M · (S : M) = (k · t) · (k · " +
		"L.inv(t)) = S, so M is invertible, but no nonzero d ∈ k has d * t ∈ k.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S M:set(A).",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"fraction_field_carrier(field_ring(L), S)",
			"«wfInvertible»(M)",
		},
		Conclusion: "∃d:A. d ∈ S ∧ d ≠ L.zero ∧ image(L.mul(d), M) ⊆ S",
	},
		func(arg *Argument, L field.FieldFact[on.L], S, M *Expr[Set[A]], hypotheses Fact) {
			parts := arg.Conjuncts(
				hypotheses,
				"S is a subring of the field",
				"L is the field of fractions of S",
				"M is invertible")
			subring, fractions, invertible := parts[0], parts[1], parts[2]
			inField := arg.Have(
				"S lies in the field",
				"S ⊆ L.carrier",
				By(comm_ring.SubringSubset.Read(subring)))
			opened := arg.Conjuncts(
				arg.Unfolded(invertible, fractional_ideal.InvertibleFractionalDef),
				"M is an S-submodule of L",
				"whose product with its inverse is S")
			fractional, product := opened[0], opened[1]
			mInL := arg.Have(
				"a submodule lies in its module's carrier, so M ⊆ L.carrier",
				"M ⊆ L.carrier",
				By(submodule.SubmoduleSubset.Read(fractional)))
			inverse := arg.TermAs[Set[A]]("«wfInverse»(M)")

			f, chosen := arg.ObtainAs[A](
				"(S : M) holds a nonzero member",
				"∃f:A. f ∈ «wfInverse»(M) ∧ f ≠ L.zero",
				Derive(func(b *Argument) {
					none := b.SupposeNot()
					vanish := b.Have(
						"then every product of a member of M with a member of (S : M) is zero",
						"∀m n:A. m ∈ M ∧ n ∈ «wfInverse»(M) ⇒ m * n ∈ {L.zero}",
						BySets(none, mInL, comm_ring.MulRightZeroOn.Read(field.RingOn.Read(L))))
					overS := b.Have(
						"L is a module over S",
						"module_on(«wfScalars», «wfField»)",
						By(fractional_ideal.FieldModuleOn.Read(L).At(S), subring))
					productZero := b.Have(
						"so M · (S : M) lies in the submodule {zero}",
						"«wfMul»(M, «wfInverse»(M)) ⊆ {L.zero}",
						By(
							fractional_ideal.FractionalMulLeast.Read(L).At(S, M, inverse, b.TermAs[Set[A]]("{L.zero}")),
							submodule.ZeroSubmodule.Read(overS),
							vanish))
					oneIn := b.Have(
						"but M · (S : M) is S, which holds one",
						"L.one ∈ «wfMul»(M, «wfInverse»(M))",
						product.Rw(),
						By(comm_ring.SubringOne.Read(subring)))
					b.Show(
						"so L.one = L.zero, which it is not",
						BySets(productZero, oneIn, field.OneNotZeroOn.Read(L)))
				}))
			picked := arg.Conjuncts(
				chosen,
				"f lies in (S : M)",
				"f is not zero")
			fInverse, fNonzero := picked[0], picked[1]
			member := arg.Have(
				"f lies in L and carries M into S",
				"f ∈ L.carrier ∧ (∀m:A. m ∈ M ⇒ f * m ∈ S)",
				BySets(arg.Unfolded(fInverse, fractional_ideal.FractionalInverseDef)))
			fParts := arg.Conjuncts(
				member,
				"f lies in L",
				"and carries M into S")
			fInL, fScales := fParts[0], fParts[1]

			a, b, fraction := arg.Obtain2As[A, A](
				"f is a fraction a/b of members of S",
				"∃a b:A. a ∈ S ∧ b ∈ S ∧ b ≠ L.zero ∧ f * b = a",
				By(
					fractions,
					fInL,
					field.FractionFieldCarrierDef.At(arg.TermAs[module_record.RingOps[A]]("field_ring(L)"), S)))
			terms := arg.Conjuncts(
				fraction,
				"a lies in S",
				"b lies in S",
				"b is not zero",
				"f * b = a")
			aInS, bInS, bNonzero, cleared := terms[0], terms[1], terms[2], terms[3]
			aInL := arg.Have(
				"a lies in L",
				"a ∈ L.carrier",
				BySets(inField, aInS))
			bInL := arg.Have(
				"b lies in L",
				"b ∈ L.carrier",
				BySets(inField, bInS))
			aNonzero := arg.Have(
				"a = f * b is a product of nonzero members of the field",
				"a ≠ L.zero",
				By(
					Normalized,
					cleared,
					fNonzero,
					bNonzero,
					field.MulEqZeroOn.Read(L).At(arg.MemberOf[on.L](f, fInL), arg.MemberOf[on.L](b, bInL))))
			scaled := arg.Have(
				"for m ∈ M, a * m = b * (f * m) is a product of two members of S",
				"∀m:A. m ∈ M ⇒ a * m ∈ S",
				Derive(func(c *Argument) {
					m := c.FixAs[A]("m")
					mInM := c.Assume()
					mL := c.Have(
						"m lies in L",
						"m ∈ L.carrier",
						BySets(mInL, mInM))
					regroup := c.Have(
						"a * m = (f * b) * m = b * (f * m)",
						"a * m = b * (f * m)",
						ByArith(field.RingOn.Read(L), aInL, bInL, fInL, mL, Scaled(m, cleared)))
					c.Show(
						"b and f * m lie in S, and so does their product",
						regroup.Rw(),
						By(bInS, fScales, mInM, comm_ring.SubringMul.Read(subring)))
				}))
			image := arg.Have(
				"so a · M ⊆ S",
				"image(L.mul(a), M) ⊆ S",
				BySets(scaled))
			arg.Take(a)
			arg.Show(
				"a is a nonzero member of S with a · M ⊆ S",
				By(aInS, aNonzero, image))
		}),
})}

// InvertibleContainsPrincipal — when L is the field of fractions of S, an
// invertible fractional ideal J contains a nonzero principal ideal c · S.
// (S : J) is invertible with inverse J; a common denominator c of (S : J)
// carries it into S, so c lies in (S : (S : J)) = J, and J, an S-module,
// holds every multiple of c by a member of S.
var InvertibleContainsPrincipal = invertibleContainsPrincipalThm{family.Add(registry.ProofEntry{
	Name: "InvertibleContainsPrincipal",
	Key:  "prop_5676e9b24fb9d1f7",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S J:set(A).",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"fraction_field_carrier(field_ring(L), S)",
			"«wfInvertible»(J)",
		},
		Conclusion: "∃c:A. c ∈ S ∧ c ≠ L.zero ∧ image(L.mul(c), S) ⊆ J",
	},
		func(a *Argument, L field.FieldFact[on.L], S, J *Expr[Set[A]], hypotheses Fact) {
			parts := a.Conjuncts(
				hypotheses,
				"S is a subring of the field",
				"L is the field of fractions of S",
				"J is invertible")
			subring, fractions, invertible := parts[0], parts[1], parts[2]
			fractional := a.Conjuncts(
				a.Unfolded(invertible, fractional_ideal.InvertibleFractionalDef),
				"J is an S-submodule of L",
				"whose product with its inverse is S")[0]
			inField := a.Have(
				"S lies in the field",
				"S ⊆ L.carrier",
				By(comm_ring.SubringSubset.Read(subring)))
			inverse := a.TermAs[Set[A]]("«wfInverse»(J)")
			doubleInverse := a.Have(
				"(S : J) is invertible, and its inverse is J",
				"«wfInvertible»(«wfInverse»(J)) ∧ «wfInverse»(«wfInverse»(J)) = J",
				By(fractional_ideal.InvertibleInverse.Read(L).At(S, J), subring, invertible))
			c, denominator := a.ObtainAs[A](
				"(S : J) has a common denominator c",
				"∃c:A. c ∈ S ∧ c ≠ L.zero ∧ image(L.mul(c), «wfInverse»(J)) ⊆ S",
				By(InvertibleCommonDenominator.Read(L).At(S, inverse), subring, fractions, doubleInverse))
			cInJ := a.Have(
				"c carries (S : J) into S, so it lies in (S : (S : J)), which is J",
				"c ∈ J ∧ c ∈ L.carrier",
				BySets(
					denominator,
					inField,
					doubleInverse,
					fractional_ideal.FractionalInverseDef.At(
						a.TermAs[module_record.RingOps[A]]("field_ring(L)"), S, inverse)))
			principal := a.Have(
				"J is an S-module, so it holds each multiple c * x by a member x of S",
				"image(L.mul(c), S) ⊆ J",
				Simp(Fwd(set_image.ImageSubsetIff)),
				Derive(func(b *Argument) {
					x := b.FixAs[A]("x")
					member := b.Assume()
					b.Show(
						"x * c lies in J, and c * x = x * c",
						BySets(
							cInJ,
							member,
							inField,
							submodule.SubmoduleSmul.Read(fractional).AsFact().At(x, c),
							comm_monoid.CommOn.Read(comm_ring.MulMonoidOn.Read(field.RingOn.Read(L))).AsFact().At(c, x)))
				}))
			a.Take(c)
			a.Show(
				"c is a nonzero member of S with c · S ⊆ J",
				By(denominator, principal))
		}),
})}

// InverseMulInside — the fractional ideal X⁻¹Y of a subring S, for an S-submodule Y
// inside an ideal X invertible in S: multiplying by X⁻¹ divides by X, so a member of
// X⁻¹Y times X lands in Y, which puts X⁻¹Y in S, and in any prime holding Y and not X,
// since a member of X off the prime carries the member of X⁻¹Y into it.
var InverseMulInside = inverseMulInsideThm{family.Add(registry.ProofEntry{
	Name: "InverseMulInside",
	Key:  "prop_b3e27cea3f59335f",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S X Y:set(A).",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"invertible_fractional(field_ring(L), S, X)",
			"X ⊆ S",
			"submodule(restrict_ring(field_ring(L), S), regular_module(field_ring(L)), Y)",
			"Y ⊆ X",
		},
		Conclusion: "«divided» ⊆ S ∧ " +
			"(∀Z:set(A). prime_ideal(restrict_ring(field_ring(L), S), Z) ∧ Y ⊆ Z ∧ ¬(X ⊆ Z) ⇒ «divided» ⊆ Z)",
		Abbrev: Abbrev{
			{Name: "divided", Text: "fractional_mul(field_ring(L), " +
				"    S, " +
				"    fractional_inverse(field_ring(L), S, X), " +
				"    Y)"},
		},
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			S, X, Y *Expr[Set[A]],
			subring, invertible, inside, module, contained Fact,
		) {
			ring := a.TermAs[module_record.RingOps[A]]("field_ring(L)")
			scalars := a.TermAs[module_record.RingOps[A]]("restrict_ring(field_ring(L), S)")
			vectors := a.TermAs[module_record.ModuleOps[A, A]]("regular_module(field_ring(L))")
			inverse := a.TermAs[Set[A]]("fractional_inverse(field_ring(L), S, X)")
			inField := a.Have(
				"X and Y lie in L",
				"X ⊆ L.carrier ∧ Y ⊆ L.carrier",
				BySets(
					subring,
					inside,
					module,
					comm_ring.SubringSubset.At(ring, S),
					submodule.SubmoduleSubset.At(scalars, vectors, Y)))
			colon := a.Have(
				"multiplying by the inverse of X divides by X",
				"«divided» = {y:A | y ∈ L.carrier ∧ (∀n:A. n ∈ X ⇒ y * n ∈ Y)}",
				By(
					subring,
					inField,
					invertible,
					module,
					fractional_ideal.FractionalMulComm.Read(L).At(S, inverse, Y),
					fractional_ideal.FractionalInverseSubset.Read(L).At(S, X),
					MulInverseIsColon.Read(L).At(S, X, Y)))
			unit := a.Have(
				"the inverse of X times X is S",
				"fractional_mul(field_ring(L), S, fractional_inverse(field_ring(L), S, X), X) = S",
				By(
					inField,
					invertible,
					fractional_ideal.FractionalMulComm.Read(L).At(S, inverse, X),
					fractional_ideal.FractionalInverseSubset.Read(L).At(S, X),
					fractional_ideal.InvertibleFractionalDef.At(ring, S, X)))
			intoChart := a.Have(
				"Y lies in X, so the quotient lies in S",
				"«divided» ⊆ S",
				BySets(contained, unit, fractional_ideal.FractionalMulMono.Read(L).At(S, inverse, inverse, Y, X)))
			intoPrime := a.Have(
				"a prime holding Y and not X holds the quotient",
				"∀Z:set(A). prime_ideal(restrict_ring(field_ring(L), S), Z) ∧ Y ⊆ Z ∧ ¬(X ⊆ Z) ⇒ «divided» ⊆ Z",
				Derive(func(b *Argument) {
					Z := b.FixAs[Set[A]]("Z")
					assumed := b.Conjuncts(
						b.Assume(),
						"Z is prime",
						"Y lies in Z",
						"X does not")
					prime, holdsY, missesX := assumed[0], assumed[1], assumed[2]
					u, separating := b.ObtainAs[A](
						"X holds a member u off Z",
						"∃u:A. u ∈ X ∧ u ∉ Z",
						BySets(missesX))
					parts := b.Conjuncts(
						separating,
						"u lies in X",
						"u lies off Z")
					pointwise := b.Have(
						"every member x of the quotient lies in Z",
						"∀x:A. x ∈ «divided» ⇒ x ∈ Z",
						Derive(func(c *Argument) {
							x := c.FixAs[A]("x")
							member := c.Assume()
							product := c.Have(
								"x · u lands in Y, inside Z",
								"x * u ∈ Z",
								BySets(colon, holdsY, parts[0], member))
							chartMembers := c.Have(
								"x and u lie in S",
								"x ∈ S ∧ u ∈ S",
								BySets(intoChart, inside, parts[0], member))
							c.Show(
								"Z is prime, and u lies off it",
								By(parts[1], prime, chartMembers, product, ring_ideal.PrimeIdealPrime.At(scalars, Z, x, u)))
						}))
					b.Show(
						"so the quotient lies in Z",
						BySets(pointwise))
				}))
			a.Show(
				"the quotient lies in S and in each such prime",
				By(intoChart, intoPrime))
		}),
})}
