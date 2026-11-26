// picard.go — Pic⁰ of a curve over the projective line: the quotient of
// the invertible pairs by "is a nonzero multiple of" — up to isomorphism,
// by InvertibleIsoIffScale — with the product of classes, the classes of
// degree zero, and the class O(P − E) of a regular point P against a
// regular base point E, the twist of E's ideal pair at P.

package curve_degree

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/abelian_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/fractional_ideal"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/relations/equivalence"
	"github.com/euc-ai/xugo/library/proofs/scheme/algebraic_curve"
	"github.com/euc-ai/xugo/library/proofs/scheme/invertible_lattice_pair"
	"github.com/euc-ai/xugo/library/proofs/scheme/lattice_pair_twist"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// ---------------------------------------------------------------------------
// Classes of pairs and Pic⁰ of a curve
// ---------------------------------------------------------------------------

// curvePairMultipleDef — `curve_pair_multiple(L, M, N)`: N is a nonzero
// multiple a · M of the pair M by a member a of the field. On the
// invertible pairs it is an equivalence (PairMultipleEquivalenceOn), and
// its classes are the points of the Picard group.
var curvePairMultipleDef = curvePairMultipleDefThm{family.Define(registry.DefEntry{
	Name:     "curvePairMultipleDef",
	Key:      "prop_cdd55f259672cfb2",
	Const:    "curve_pair_multiple",
	Type:     "ring_ops(A) → prod(set(A), set(A)) → prod(set(A), set(A)) → bool",
	Implicit: []string{},
	Bundles:  []string{},
	Equations: []string{
		"∀R:ring_ops(A). ∀M:prod(set(A), set(A)). ∀N:prod(set(A), set(A)). " +
			"    curve_pair_multiple(R, M, N) ⇔ " +
			"    (∃a:A. a ∈ R.carrier ∧ a ≠ R.zero ∧ N = lattice_pair_scale(R.mul, a, M))",
	},
})}

// CurvePairClassDef — `curve_pair_class(L, M)`: the class of the pair M
// under curve_pair_multiple, the nonzero multiples a · M of M by members
// a of the field.
var CurvePairClassDef = curvePairClassDefThm{family.Define(registry.DefEntry{
	Name:     "CurvePairClassDef",
	Key:      "prop_111bbb7ca8096726",
	Const:    "curve_pair_class",
	Type:     "ring_ops(A) → prod(set(A), set(A)) → set(prod(set(A), set(A)))",
	Implicit: []string{},
	Bundles:  []string{},
	Equations: []string{
		"∀R:ring_ops(A). ∀M:prod(set(A), set(A)). " +
			"    curve_pair_class(R, M) = equivalence_class(curve_pair_multiple(R), M)",
	},
	Reading: "For an invertible M the nonzero multiples are exactly the pairs " +
		"isomorphic to M (InvertibleIsoIffScale), so the class is M's isomorphism " +
		"class: a point of the Picard group, no representative chosen. M itself is " +
		"a member when its charts lie in the field, as one · M = M there.",
	Deps: []registry.EntryLike{curvePairMultipleDef},
})}

// CurveClassMulDef — `curve_class_mul(L, A₀, A₁, X, Y)`: the products
// M · N of a member M of X and a member N of Y.
var CurveClassMulDef = curveClassMulDefThm{family.Define(registry.DefEntry{
	Name:  "CurveClassMulDef",
	Key:   "prop_2cd2dbd84c11db2d",
	Const: "curve_class_mul",
	Type: "ring_ops(A) → " +
		"set(A) → " +
		"set(A) → " +
		"set(prod(set(A), set(A))) → " +
		"set(prod(set(A), set(A))) → " +
		"set(prod(set(A), set(A)))",
	Implicit: []string{},
	Bundles:  []string{},
	Equations: []string{
		"∀R:ring_ops(A). " +
			"∀A₀:set(A). " +
			"∀A₁:set(A). " +
			"∀X:set(prod(set(A), set(A))). " +
			"∀Y:set(prod(set(A), set(A))). " +
			"    curve_class_mul(R, A₀, A₁, X, Y) = " +
			"    {lattice_pair_mul(R, A₀, A₁, M, N) | " +
			"        M:prod(set(A), set(A)), " +
			"        N:prod(set(A), set(A)) | " +
			"        M ∈ X ∧ N ∈ Y}",
	},
	Reading: "On two classes this is a class: (a · M) · (b · N) = (a·b) " +
		"· (M · N), and a·b runs over the nonzero members of the field, so the " +
		"class of M times the class of N is the class of M · N (PairClassMul).",
})}

// CurveClassInverseDef — `curve_class_inverse(L, A₀, A₁, X)`: the inverses
// M⁻¹ of the members M of X.
var CurveClassInverseDef = curveClassInverseDefThm{family.Define(registry.DefEntry{
	Name:     "CurveClassInverseDef",
	Key:      "prop_be13c23cad42e0c1",
	Const:    "curve_class_inverse",
	Type:     "ring_ops(A) → set(A) → set(A) → set(prod(set(A), set(A))) → set(prod(set(A), set(A)))",
	Implicit: []string{},
	Bundles:  []string{},
	Equations: []string{
		"∀R:ring_ops(A). ∀A₀:set(A). ∀A₁:set(A). ∀X:set(prod(set(A), set(A))). " +
			"    curve_class_inverse(R, A₀, A₁, X) = " +
			"    {lattice_pair_inverse(R, A₀, A₁, M) | M:prod(set(A), set(A)) | M ∈ X}",
	},
	Reading: "On a class this is a class: (a · M)⁻¹ = inv(a) · M⁻¹ chart by " +
		"chart, so the inverse of the class of M is the class of M⁻¹ (PairClassInverse).",
})}

// CurvePicZeroDef — `curve_pic_zero(L, k, A₀, A₁, A₀₁)`, written Pic⁰: the
// quotient of the invertible pairs of degree zero by curve_pair_multiple,
// relations/equivalence's quotient_on — the classes of those pairs.
var CurvePicZeroDef = curvePicZeroDefThm{family.Define(registry.DefEntry{
	Name:     "CurvePicZeroDef",
	Key:      "prop_8abc8ca702f64d4b",
	Const:    "curve_pic_zero",
	Type:     "ring_ops(A) → set(A) → set(A) → set(A) → set(A) → set(set(prod(set(A), set(A))))",
	Implicit: []string{},
	Bundles:  []string{},
	Equations: []string{
		"∀R:ring_ops(A). ∀k:set(A). ∀A₀:set(A). ∀A₁:set(A). ∀A₀₁:set(A). " +
			"    curve_pic_zero(R, k, A₀, A₁, A₀₁) = " +
			"    quotient_on({M:prod(set(A), set(A)) | " +
			"            invertible_lattice_pair(R, A₀, A₁, A₀₁, M) ∧ " +
			"            curve_degree(R, k, A₀, A₁, A₀₁, M) = &0}, " +
			"        curve_pair_multiple(R))",
	},
	Reading: "A notion of every curve over the projective line, not of the Weierstrass curve " +
		"alone. A nonzero multiple of an invertible pair of degree zero is one (PairMultipleInvertible, " +
		"DegreeScale), so a member is the class curve_pair_class of such a pair (InPicZero). The group " +
		"law is the product of classes, its unit the class of the structure pair (PicZeroGroupOn).",
	Deps: []registry.EntryLike{curvePairMultipleDef},
})}

// PairMultipleEquivalenceOn — being a nonzero multiple is an equivalence
// on the invertible pairs over any two charts. The charts of an invertible
// pair lie in L, where scaling by one changes nothing, dividing by a nonzero a
// undoes scaling by it, and scaling twice is scaling by the product: M is
// one · M; N = a · M gives M = inv(a) · N; and
// N = a · M, P = b · N give P = (b · a) · M, with inv(a) and b · a nonzero.
var PairMultipleEquivalenceOn = pairMultipleEquivalenceOnThm{family.Add(registry.ProofEntry{
	Name: "PairMultipleEquivalenceOn",
	Key:  "prop_9fd16e4640963fa4",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀A₀ A₁ A₀₁:set(A).",
		Conclusion: "equivalence_on( " +
			"    {M:prod(set(A), set(A)) | invertible_lattice_pair(field_ring(L), A₀, A₁, A₀₁, M)}, " +
			"    curve_pair_multiple(field_ring(L)))",
	},
		func(a *Argument, L field.FieldFact[on.L], A0, A1, A01 *Expr[Set[A]]) {
			reflexive := a.Have(
				"an invertible pair is one times itself",
				"∀M:prod(set(A), set(A)). «wdInvertible»(M) ⇒ curve_pair_multiple(field_ring(L), M, M)",
				Derive(func(b *Argument) {
					M := b.FixAs[_LatticePair]("M")
					charts := b.Conjuncts(
						GroupPremises(
							b.Assume(), invertible_lattice_pair.InvertibleChartsInField.Read(L).At(A0, A1, A01, M)),
						"M being invertible, its first chart lies in L",
						"and so does its second")
					b.Show(
						"one is a nonzero member of L, and one · M = M",
						Unfold(curvePairMultipleDef),
						Witness(b.TermAs[A]("L.one")),
						By(
							comm_ring.OneIn.Read(field.RingOn.Read(L)),
							field.OneNotZeroOn.Read(L),
							charts[0],
							charts[1],
							invertible_lattice_pair.ScaleOne.Read(L).At(M)))
				}))
			symmetric := a.Have(
				"N = a · M gives M = inv(a) · N",
				Statement{
					Binders: "∀M N:prod(set(A), set(A)).",
					Hypotheses: []string{
						"«wdInvertible»(M)",
						"curve_pair_multiple(field_ring(L), M, N)",
					},
					Conclusion: "curve_pair_multiple(field_ring(L), N, M)",
				},
				Derive(func(b *Argument) {
					M := b.FixAs[_LatticePair]("M")
					b.FixAs[_LatticePair]("N")
					assumed := b.Conjuncts(
						b.Assume(),
						"M is invertible",
						"N is a nonzero multiple of M")
					scalar, scaled := b.UnpackAs[A](b.Unfolded(assumed[1], curvePairMultipleDef), "a")
					scaling := b.Conjuncts(
						scaled,
						"a lies in L",
						"a is not zero",
						"N is a · M")
					am := b.MemberOf[on.L](scalar, scaling[0])
					inverse := field.InvIn.Read(L).At(am)
					charts := b.Conjuncts(
						GroupPremises(
							assumed[0], invertible_lattice_pair.InvertibleChartsInField.Read(L).At(A0, A1, A01, M)),
						"the first chart of M lies in L",
						"and so does its second")
					back := b.Have(
						"dividing N = a · M by a gives M back, a being nonzero",
						"lattice_pair_scale(L.inv(a), N) = M",
						By(
							Normalized,
							scaling[1],
							scaling[2],
							charts[0],
							charts[1],
							invertible_lattice_pair.ScaleCancel.Read(L).At(am, M)))
					b.Show(
						"so M is inv(a) · N, inv(a) a nonzero member of L",
						Unfold(curvePairMultipleDef),
						Witness(inverse),
						By(back, inverse, scaling[1], field.InvEqZeroOn.Read(L).At(am)))
				}))
			transitive := a.Have(
				"N = a · M and P = b · N give P = (b · a) · M",
				Statement{
					Binders: "∀M N P:prod(set(A), set(A)).",
					Hypotheses: []string{
						"«wdInvertible»(M)",
						"curve_pair_multiple(field_ring(L), M, N)",
						"curve_pair_multiple(field_ring(L), N, P)",
					},
					Conclusion: "curve_pair_multiple(field_ring(L), M, P)",
				},
				Derive(func(c *Argument) {
					M := c.FixAs[_LatticePair]("M")
					c.FixAs[_LatticePair]("N")
					c.FixAs[_LatticePair]("P")
					assumed := c.Conjuncts(
						c.Assume(),
						"M is invertible",
						"N is a nonzero multiple of M",
						"and P one of N")
					first, firstScaled := c.UnpackAs[A](c.Unfolded(assumed[1], curvePairMultipleDef), "a")
					firstScaling := c.Conjuncts(
						firstScaled,
						"a lies in L",
						"a is not zero",
						"N is a · M")
					second, secondScaled := c.UnpackAs[A](c.Unfolded(assumed[2], curvePairMultipleDef), "b")
					secondScaling := c.Conjuncts(
						secondScaled,
						"b lies in L",
						"b is not zero",
						"P is b · N")
					am, bm := c.MemberOf[on.L](first, firstScaling[0]), c.MemberOf[on.L](second, secondScaling[0])
					product := comm_ring.MulIn.Read(field.RingOn.Read(L)).At(bm, am)
					charts := c.Conjuncts(
						GroupPremises(
							assumed[0], invertible_lattice_pair.InvertibleChartsInField.Read(L).At(A0, A1, A01, M)),
						"the first chart of M lies in L",
						"and so does its second")
					composite := c.Have(
						"so P = b · (a · M), which is (b · a) · M",
						"P = lattice_pair_scale(b * a, M)",
						By(
							firstScaling[2],
							secondScaling[2],
							charts[0],
							charts[1],
							invertible_lattice_pair.ScaleScale.Read(L).At(am, bm, M)))
					c.Show(
						"so P is (b · a) · M, b · a a nonzero member of L",
						Unfold(curvePairMultipleDef),
						Witness(product),
						By(composite, product, firstScaling[1], secondScaling[1], field.MulEqZeroOn.Read(L).At(bm, am)))
				}))
			a.Show(
				"being a nonzero multiple is reflexive, symmetric and transitive on the invertible pairs",
				Unfold(equivalence.EquivalenceOn),
				By(reflexive, symmetric, transitive))
		}),
})}

// PairMultipleInvertible — a nonzero multiple of an invertible pair is
// invertible: N is a · M for a nonzero a in the field, M's charts lie in
// the field, and scaling such a pair by a nonzero member of the field
// keeps it invertible (invertible_lattice_pair.InvertibleLatticeScale).
var PairMultipleInvertible = pairMultipleInvertibleThm{family.Add(registry.ProofEntry{
	Name: "PairMultipleInvertible",
	Key:  "prop_a770372615e7d791",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀A₀ A₁ A₀₁:set(A). ∀t:A. ∀M N:prod(set(A), set(A)).",
		Hypotheses: []string{
			"A₀₁ ⊆ L.carrier",
			"biaffine(«wcOverlap», A₀, A₁, t, L.inv(t))",
			"«wdInvertible»(M)",
			"curve_pair_multiple(field_ring(L), M, N)",
		},
		Conclusion: "«wdInvertible»(N)",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			M, N *Expr[_LatticePair],
			inField, biaffine, invertible, multiple Fact,
		) {
			scalar, scaled := a.UnpackAs[A](a.Unfolded(multiple, curvePairMultipleDef), "a")
			scaling := a.Conjuncts(
				scaled,
				"a lies in L",
				"a is not zero",
				"N is a · M")
			a.Show(
				"M's charts lying in L, scaling M by the nonzero member "+
					"a of L keeps it invertible, so N = a · M is invertible",
				By(
					Normalized,
					inField,
					biaffine,
					invertible,
					scaling[1],
					scaling[2],
					invertible_lattice_pair.InvertibleChartsInField.Read(L).At(A0, A1, A01, M),
					invertible_lattice_pair.InvertibleLatticeScale.Read(L).At(
						A0, A1, A01, t, a.MemberOf[on.L](scalar, scaling[0]), M)))
		}),
})}

// InPicZero — a member of Pic⁰ is the class of an invertible pair of
// degree zero, and every such class is a member: those pairs are closed
// under nonzero multiples, since scaling by a nonzero member of the field
// keeps invertibility (PairMultipleInvertible) and the degree
// (DegreeScale), so a member of their quotient is the class of one of
// them (equivalence.InQuotientOnClosed).
var InPicZero = inPicZeroThm{family.Add(registry.ProofEntry{
	Name: "InPicZero",
	Key:  "prop_5a60547780f5816d",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀X:set(prod(set(A), set(A))).",
		Hypotheses: []string{
			"curve_over_line(L, k, t, A₀, A₁, A₀₁)",
		},
		Conclusion: "X ∈ curve_pic_zero(field_ring(L), k, A₀, A₁, A₀₁) ⇔ " +
			"∃M:prod(set(A), set(A)). " +
			"    invertible_lattice_pair(field_ring(L), A₀, A₁, A₀₁, M) ∧ " +
			"    curve_degree(field_ring(L), k, A₀, A₁, A₀₁, M) = &0 ∧ " +
			"    X = curve_pair_class(field_ring(L), M)",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			X *Expr[Set[_LatticePair]],
			curve Fact,
		) {
			closed := a.Have(
				"a nonzero multiple of an invertible pair of degree zero is one",
				Statement{
					Binders: "∀U V:prod(set(A), set(A)).",
					Hypotheses: []string{
						"«wdInvertible»(U)",
						"«wdDegree»(U) = &0",
						"curve_pair_multiple(field_ring(L), U, V)",
					},
					Conclusion: "«wdInvertible»(V) ∧ «wdDegree»(V) = &0",
				},
				Derive(func(b *Argument) {
					U := b.FixAs[_LatticePair]("U")
					V := b.FixAs[_LatticePair]("V")
					assumed := b.Conjuncts(
						b.Assume(),
						"U is invertible",
						"U has degree zero",
						"V is a nonzero multiple of U")
					scalar, scaled := b.UnpackAs[A](b.Unfolded(assumed[2], curvePairMultipleDef), "a")
					scaling := b.Conjuncts(
						scaled,
						"a lies in L",
						"a is not zero",
						"V is a · U")
					b.Show(
						"V is invertible as a nonzero multiple of the invertible U, "+
							"and scaling keeps the degree, so V has degree zero as U has",
						By(
							curve,
							algebraic_curve.CurveLatticeData.Read(L).At(k, A0, A1, A01, t),
							assumed[0],
							assumed[1],
							assumed[2],
							scaling[1],
							scaling[2],
							PairMultipleInvertible.Read(L).At(A0, A1, A01, t, U, V),
							DegreeScale.Read(L).At(k, A0, A1, A01, t, b.MemberOf[on.L](scalar, scaling[0]), U)))
				}))
			degreeZero := a.TermAs[Set[_LatticePair]](
				"{M:prod(set(A), set(A)) | «wdInvertible»(M) ∧ «wdDegree»(M) = &0}")
			multiple := a.TermAs[Fun2[_LatticePair, _LatticePair, Bool]]("curve_pair_multiple(field_ring(L))")
			a.Show(
				"Pic⁰ is the quotient of those pairs by being a nonzero "+
					"multiple, so its members are the classes of the pairs",
				Simp(Fwd(CurvePicZeroDef), Fwd(CurvePairClassDef)),
				BySets(closed, equivalence.InQuotientOnClosed.At(degreeZero, multiple, X)))
		}),
})}

// CurvePointClassDef — `curve_point_class(L, A₀, A₁, E, P)`: the class of
// the twist E(P) = P⁻¹ · E; for regular points E and P, the class of
// O(P − E).
var CurvePointClassDef = curvePointClassDefThm{family.Define(registry.DefEntry{
	Name:  "CurvePointClassDef",
	Key:   "prop_6053640bb00ef58",
	Const: "curve_point_class",
	Type: "ring_ops(A) → " +
		"set(A) → " +
		"set(A) → " +
		"prod(set(A), set(A)) → " +
		"prod(set(A), set(A)) → " +
		"set(prod(set(A), set(A)))",
	Implicit: []string{},
	Bundles:  []string{},
	Equations: []string{
		"∀R:ring_ops(A). ∀A₀:set(A). ∀A₁:set(A). ∀E:prod(set(A), set(A)). ∀P:prod(set(A), set(A)). " +
			"    curve_point_class(R, A₀, A₁, E, P) = curve_pair_class(R, lattice_pair_twist(R, A₀, A₁, E, P))",
	},
	Reading: "The ideal pair of the base point E is O(−E), and twisting it at P " +
		"allows a simple pole at P: E(P) is O(P − E). At P = E it is the class of the " +
		"structure pair, E⁻¹ · E = (A₀, A₁) for a regular E (InvertibleLatticeInverse).",
	Deps: []registry.EntryLike{CurvePairClassDef},
})}

// PairClassEqIff — two invertible pairs have one class exactly when one is
// a nonzero multiple of the other: being a nonzero multiple is an
// equivalence on the invertible pairs (PairMultipleEquivalenceOn), and a
// nonzero multiple of an invertible pair is invertible
// (PairMultipleInvertible), so on that set, closed under the relation,
// two pairs have one class exactly when they are related
// (equivalence.ClassEqIffClosed).
var PairClassEqIff = pairClassEqIffThm{family.Add(registry.ProofEntry{
	Name: "PairClassEqIff",
	Key:  "prop_b0222d689fc29ec5",
	Reading: "By InvertibleIsoIffScale the right side says N is isomorphic to M: " +
		"the class is the isomorphism class. A nonzero multiple of an invertible " +
		"pair is invertible (PairMultipleInvertible), so asking it of N loses nothing.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀A₀ A₁ A₀₁:set(A). ∀t:A. ∀M N:prod(set(A), set(A)).",
		Hypotheses: []string{
			"A₀₁ ⊆ L.carrier",
			"biaffine(«wcOverlap», A₀, A₁, t, L.inv(t))",
			"invertible_lattice_pair(field_ring(L), A₀, A₁, A₀₁, M)",
			"invertible_lattice_pair(field_ring(L), A₀, A₁, A₀₁, N)",
		},
		Conclusion: "curve_pair_class(field_ring(L), M) = curve_pair_class(field_ring(L), N) ⇔ " +
			"∃a:A. a ∈ L.carrier ∧ a ≠ L.zero ∧ N = lattice_pair_scale(a, M)",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			M, N *Expr[_LatticePair],
			inField, biaffine, mInvertible, nInvertible Fact,
		) {
			multiples := a.Have(
				"being a nonzero multiple is an equivalence on the invertible pairs",
				"equivalence_on( "+
					"    {P:prod(set(A), set(A)) | invertible_lattice_pair(field_ring(L), A₀, A₁, A₀₁, P)}, "+
					"    curve_pair_multiple(field_ring(L)))",
				By(PairMultipleEquivalenceOn.Read(L).At(A0, A1, A01)))
			mIn := a.Have(
				"M is an invertible pair",
				"M ∈ {P:prod(set(A), set(A)) | invertible_lattice_pair(field_ring(L), A₀, A₁, A₀₁, P)}",
				BySets(mInvertible))
			nIn := a.Have(
				"and so is N",
				"N ∈ {P:prod(set(A), set(A)) | invertible_lattice_pair(field_ring(L), A₀, A₁, A₀₁, P)}",
				BySets(nInvertible))
			criterion := a.Have(
				"the invertible pairs being closed under nonzero multiples, "+
					"M and N have one class exactly when they are related",
				"equivalence_class(curve_pair_multiple(field_ring(L)), M) = "+
					"equivalence_class(curve_pair_multiple(field_ring(L)), N) ⇔ "+
					"curve_pair_multiple(field_ring(L), M, N)",
				By(
					equivalence.ClassEqIffClosed.Read(multiples).At(proof.MemberOf(M, mIn), proof.MemberOf(N, nIn)),
					inField,
					biaffine,
					PairMultipleInvertible.Read(L).AsFact().At(A0, A1, A01, t)))
			a.Show(
				"the classes of M and N are those classes, and being related is being a nonzero multiple",
				Simp(Fwd(CurvePairClassDef)),
				criterion.Rw(),
				Simp(Fwd(curvePairMultipleDef), Fwd(field.FieldRingDef)),
				TrivialNormalized())
		}),
})}

// PairClassMul — the product of the classes of two invertible pairs is the
// class of their product. Scaling comes out of a product of pairs and
// scaling twice is scaling by the product, so (a · M) · (b · N) is
// (a · b) · (M · N) with a · b nonzero; conversely c · (M · N) is
// M · (c · N), M being one times itself.
var PairClassMul = pairClassMulThm{family.Add(registry.ProofEntry{
	Name: "PairClassMul",
	Key:  "prop_58a6e92ff8a415dd",
	Reading: "The biaffine datum inside L is what ScaleMulAssoc asks for to take " +
		"a scalar out of a product of pairs; the product of two nonzero scalars " +
		"being nonzero is what keeps a product of multiples a nonzero multiple.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀A₀ A₁ A₀₁:set(A). ∀t:A. ∀M N:prod(set(A), set(A)).",
		Hypotheses: []string{
			"A₀₁ ⊆ L.carrier",
			"biaffine(«wcOverlap», A₀, A₁, t, L.inv(t))",
			"invertible_lattice_pair(field_ring(L), A₀, A₁, A₀₁, M)",
			"invertible_lattice_pair(field_ring(L), A₀, A₁, A₀₁, N)",
		},
		Conclusion: "curve_class_mul(field_ring(L), " +
			"    A₀, " +
			"    A₁, " +
			"    curve_pair_class(field_ring(L), M), " +
			"    curve_pair_class(field_ring(L), N)) = " +
			"curve_pair_class(field_ring(L), lattice_pair_mul(field_ring(L), A₀, A₁, M, N))",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			M, N *Expr[_LatticePair],
			inField, biaffine, mInvertible, nInvertible Fact,
		) {
			charts := a.Have(
				"the charts of the invertible pairs M and N lie in L",
				"fst(M) ⊆ L.carrier ∧ snd(M) ⊆ L.carrier ∧ fst(N) ⊆ L.carrier ∧ snd(N) ⊆ L.carrier",
				By(
					mInvertible,
					nInvertible,
					invertible_lattice_pair.InvertibleChartsInField.Read(L).At(A0, A1, A01, M),
					invertible_lattice_pair.InvertibleChartsInField.Read(L).At(A0, A1, A01, N)))
			products := a.Have(
				"a product of nonzero multiples of M and of N is a nonzero multiple of M · N",
				Statement{
					Binders: "∀P Q:prod(set(A), set(A)).",
					Hypotheses: []string{
						"curve_pair_multiple(field_ring(L), M, P)",
						"curve_pair_multiple(field_ring(L), N, Q)",
					},
					Conclusion: "curve_pair_multiple(field_ring(L), «wdMul»(M, N), «wdMul»(P, Q))",
				},
				Derive(func(c *Argument) {
					c.FixAs[_LatticePair]("P")
					Q := c.FixAs[_LatticePair]("Q")
					assumed := c.Conjuncts(
						c.Assume(),
						"P is a nonzero multiple of M",
						"and Q one of N")
					first, firstScaled := c.UnpackAs[A](c.Unfolded(assumed[0], curvePairMultipleDef), "a")
					firstScaling := c.Conjuncts(
						firstScaled,
						"a lies in L",
						"a is not zero",
						"P is a · M")
					second, secondScaled := c.UnpackAs[A](c.Unfolded(assumed[1], curvePairMultipleDef), "b")
					secondScaling := c.Conjuncts(
						secondScaled,
						"b lies in L",
						"b is not zero",
						"Q is b · N")
					am, bm := c.MemberOf[on.L](first, firstScaling[0]), c.MemberOf[on.L](second, secondScaling[0])
					scaledN := c.TermAs[_LatticePair]("lattice_pair_scale(b, N)")
					product := c.TermAs[_LatticePair]("«wdMul»(M, N)")
					scaledCharts := c.Have(
						"Q is invertible as a nonzero multiple of the invertible N, so its charts lie in L",
						"fst(Q) ⊆ L.carrier ∧ snd(Q) ⊆ L.carrier",
						By(
							inField,
							biaffine,
							nInvertible,
							assumed[1],
							PairMultipleInvertible.Read(L).At(A0, A1, A01, t, N, Q),
							invertible_lattice_pair.InvertibleChartsInField.Read(L).At(A0, A1, A01, Q)))
					scaled := c.Have(
						"so P · Q is (a · M) · (b · N), which is (a · b) · (M · N)",
						"«wdMul»(P, Q) = lattice_pair_scale(a * b, «wdMul»(M, N))",
						CalcEq(
							Leg(
								c.TermAs[_LatticePair]("lattice_pair_scale(a, «wdMul»(M, lattice_pair_scale(b, N)))"),
								"a comes out of the product (a · M) · (b · N)",
								By(
									firstScaling[2],
									secondScaling[2],
									inField,
									biaffine,
									charts,
									scaledCharts,
									invertible_lattice_pair.ScaleMulAssoc.Read(L).At(A0, A1, A01, t, am, M, scaledN))),
							Leg(
								c.TermAs[_LatticePair]("lattice_pair_scale(a, lattice_pair_scale(b, «wdMul»(M, N)))"),
								"and b out of M · (b · N)",
								By(
									inField,
									biaffine,
									charts,
									invertible_lattice_pair.ScaleMulAssoc.Read(L).At(A0, A1, A01, t, bm, M, N))),
							FinalLeg(
								"scaling by b and then by a is scaling by a · b, "+
									"the charts of the invertible pair M · N lying in L",
								By(
									inField,
									biaffine,
									mInvertible,
									nInvertible,
									invertible_lattice_pair.InvertibleLatticeProduct.Read(L).At(A0, A1, A01, t, M, N),
									invertible_lattice_pair.InvertibleChartsInField.Read(L).At(A0, A1, A01, product),
									invertible_lattice_pair.ScaleScale.Read(L).At(bm, am, product)))))
					scalar := comm_ring.MulIn.Read(field.RingOn.Read(L)).At(am, bm)
					c.Show(
						"so P · Q is (a · b) · (M · N), a · b a nonzero member of L",
						Unfold(curvePairMultipleDef),
						Witness(scalar),
						By(scaled, scalar, firstScaling[1], secondScaling[1], field.MulEqZeroOn.Read(L).At(am, bm)))
				}))
			multiples := a.Have(
				"a nonzero multiple of M · N is a product of nonzero multiples of M and of N",
				Statement{
					Binders: "∀X:prod(set(A), set(A)).",
					Hypotheses: []string{
						"curve_pair_multiple(field_ring(L), «wdMul»(M, N), X)",
					},
					Conclusion: "∃P Q:prod(set(A), set(A)). " +
						"    curve_pair_multiple(field_ring(L), M, P) ∧ " +
						"    curve_pair_multiple(field_ring(L), N, Q) ∧ " +
						"    X = «wdMul»(P, Q)",
				},
				Derive(func(b *Argument) {
					b.FixAs[_LatticePair]("X")
					scalar, scaled := b.UnpackAs[A](b.Unfolded(b.Assume(), curvePairMultipleDef), "c")
					scaling := b.Conjuncts(
						scaled,
						"c lies in L",
						"c is not zero",
						"X is c · (M · N)")
					cm := b.MemberOf[on.L](scalar, scaling[0])
					b.Show(
						"X = c · (M · N) is M · (c · N), M being one times itself and c · N a nonzero multiple of N",
						Witness(M),
						Witness(b.TermAs[_LatticePair]("lattice_pair_scale(c, N)")),
						Simp(Fwd(curvePairMultipleDef)),
						By(
							Normalized,
							scaling[1],
							scaling[2],
							comm_ring.OneIn.Read(field.RingOn.Read(L)),
							field.OneNotZeroOn.Read(L),
							inField,
							biaffine,
							charts,
							invertible_lattice_pair.ScaleOne.Read(L).At(M),
							invertible_lattice_pair.ScaleMulAssoc.Read(L).At(A0, A1, A01, t, cm, M, N)))
				}))
			a.Show(
				"so the products of members of the two classes are the nonzero multiples of M · N",
				Simp(Fwd(CurveClassMulDef), Fwd(CurvePairClassDef), Fwd(equivalence.EquivalenceClassDef)),
				BySets(products, multiples))
		}),
})}

// PairClassInverse — the inverse of the class of an invertible pair is the
// class of its inverse: chart by chart (a · M)⁻¹ = inv(a) · M⁻¹ for a
// nonzero a in the field (fractional_ideal.FractionalInverseScale), and
// a ↦ inv(a) runs over the nonzero members of the field as a does.
var PairClassInverse = pairClassInverseThm{family.Add(registry.ProofEntry{
	Name: "PairClassInverse",
	Key:  "prop_566d668078840d9b",
	Reading: "Invertibility is used only to put M's charts in the field, which " +
		"FractionalInverseScale asks for; inv is a bijection of the nonzero members " +
		"of the field, so the inverses of the multiples of M are the multiples of M⁻¹.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀A₀ A₁ A₀₁:set(A). ∀M:prod(set(A), set(A)).",
		Hypotheses: []string{
			"invertible_lattice_pair(field_ring(L), A₀, A₁, A₀₁, M)",
		},
		Conclusion: "curve_class_inverse(field_ring(L), A₀, A₁, curve_pair_class(field_ring(L), M)) = " +
			"curve_pair_class(field_ring(L), lattice_pair_inverse(field_ring(L), A₀, A₁, M))",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			A0, A1, A01 *Expr[Set[A]],
			M *Expr[_LatticePair],
			invertible Fact,
		) {
			scaling := a.Have(
				"scaling M by a nonzero a scales its inverse by inv(a)",
				Statement{
					Binders: "∀a:A.",
					Hypotheses: []string{
						"a ∈ L.carrier",
						"a ≠ L.zero",
					},
					Conclusion: "lattice_pair_inverse(field_ring(L), A₀, A₁, lattice_pair_scale(a, M)) = " +
						"lattice_pair_scale(L.inv(a), lattice_pair_inverse(field_ring(L), A₀, A₁, M))",
				},
				Derive(func(b *Argument) {
					scalar := b.FixAs[A]()
					nonzero := b.Conjuncts(
						b.Assume(),
						"a lies in L",
						"a is not zero")
					am := b.MemberOf[on.L](scalar, nonzero[0])
					b.Show(
						"chart by chart, the fractional inverse of a · X is inv(a) times that of X, M's charts lying in L",
						Simp(
							Fwd(invertible_lattice_pair.LatticePairInverseDef),
							Fwd(invertible_lattice_pair.LatticePairScaleDef),
							Fwd(pairs.Fst),
							Fwd(pairs.Snd)),
						By(
							nonzero[1],
							invertible,
							invertible_lattice_pair.InvertibleChartsInField.Read(L).At(A0, A1, A01, M),
							fractional_ideal.FractionalInverseScale.Read(L).At(A0, b.TermAs[Set[A]]("fst(M)"), am),
							fractional_ideal.FractionalInverseScale.Read(L).At(A1, b.TermAs[Set[A]]("snd(M)"), am)))
				}))
			a.Show(
				"the inverses of the a · M are the inv(a) · M⁻¹, and inv(a) runs "+
					"over the nonzero members of L as a does: the nonzero multiples of M⁻¹",
				Simp(
					Fwd(CurveClassInverseDef),
					Fwd(CurvePairClassDef),
					Fwd(curvePairMultipleDef),
					Fwd(equivalence.EquivalenceClassDef)),
				BySets(scaling, field.InvIn.Read(L), field.InvEqZeroOn.Read(L), field.InvInvOn.Read(L)))
		}),
})}

// PicZeroGroupOn — Pic⁰ of a curve is a group under the product of
// classes, with the class of the structure pair as unit and the class of
// the inverse as inverse.
var PicZeroGroupOn = picZeroGroupOnThm{family.Add(registry.ProofEntry{
	Name: "PicZeroGroupOn",
	Key:  "prop_d86c978c214eeb44",
	Reading: "Every member of Pic⁰ is the class of an invertible pair of degree zero, and " +
		"the operations on classes are the operations on pairs (PairClassMul, PairClassInverse): " +
		"the group axioms are the laws of the product of invertible pairs, and degree zero is " +
		"kept because the degree adds (DegreeAdditive, DegreeInverse). Any curve over the " +
		"projective line; no rational point is asked. The unit class(A₀, A₁) lies in Pic⁰ " +
		"because (A₀, A₁) is invertible (CurveLatticeData) of degree zero (DegreeStructure); the " +
		"inverse law M⁻¹ · M = (A₀, A₁) is InvertibleLatticeInverse with MulComm.",
	Deps: []registry.EntryLike{
		InPicZero,
		PairClassMul,
		PairClassInverse,
		PairClassEqIff,
		group.GroupOn,
		algebraic_curve.CurveLatticeData,
		DegreeStructure,
		DegreeAdditive,
		DegreeInverse,
		invertible_lattice_pair.InvertibleLatticeProduct,
		invertible_lattice_pair.InvertibleLatticeInverse,
		invertible_lattice_pair.MulAssoc,
		invertible_lattice_pair.MulComm,
		invertible_lattice_pair.MulOne,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A.",
		Hypotheses: []string{
			"curve_over_line(L, k, t, A₀, A₁, A₀₁)",
		},
		Conclusion: "group_on(mk_group(λX:set(prod(set(A), set(A))). λY:set(prod(set(A), set(A))). " +
			"            curve_class_mul(field_ring(L), A₀, A₁, X, Y), " +
			"        curve_pair_class(field_ring(L), (A₀, A₁)), " +
			"        λX:set(prod(set(A), set(A))). curve_class_inverse(field_ring(L), A₀, A₁, X), " +
			"        curve_pic_zero(field_ring(L), k, A₀, A₁, A₀₁)))",
	},
		"unfold group_on (GroupOn) and curve_pic_zero; the members are classes of invertible "+
			"pairs of degree zero. The unit: (A₀, A₁) is invertible (CurveLatticeData) of degree "+
			"zero (DegreeStructure). Closure: class(M) · class(N) = class(M · N) (PairClassMul) "+
			"with M · N invertible (InvertibleLatticeProduct) of degree zero (DegreeAdditive); "+
			"inverses: class(M)⁻¹ = class(M⁻¹) (PairClassInverse) with M⁻¹ invertible "+
			"(InvertibleLatticeInverse) of degree zero (DegreeInverse). Associativity, the unit "+
			"and the inverse law hold of representatives (MulAssoc; MulOne; M⁻¹ · M = (A₀, A₁) "+
			"by InvertibleLatticeInverse and MulComm) and pass to classes through PairClassMul"),
})}

// PicZeroAbelian — Pic⁰ of a curve is an abelian group.
var PicZeroAbelian = picZeroAbelianThm{family.Add(registry.ProofEntry{
	Name: "PicZeroAbelian",
	Key:  "prop_15cbd57569e507ef",
	Deps: []registry.EntryLike{
		PicZeroGroupOn,
		PairClassMul,
		abelian_group.AbelianGroupOn,
		invertible_lattice_pair.MulComm,
		InPicZero,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A.",
		Hypotheses: []string{
			"curve_over_line(L, k, t, A₀, A₁, A₀₁)",
		},
		Conclusion: "abelian_group_on(mk_group(λX:set(prod(set(A), set(A))). " +
			"        λY:set(prod(set(A), set(A))). " +
			"            curve_class_mul(field_ring(L), A₀, A₁, X, Y), " +
			"        curve_pair_class(field_ring(L), (A₀, A₁)), " +
			"        λX:set(prod(set(A), set(A))). curve_class_inverse(field_ring(L), A₀, A₁, X), " +
			"        curve_pic_zero(field_ring(L), k, A₀, A₁, A₀₁)))",
	},
		"unfold abelian_group_on (AbelianGroupOn): the group is PicZeroGroupOn, and class(M) · "+
			"class(N) = class(M · N) = class(N · M) = class(N) · class(M) by PairClassMul and MulComm"),
})}

// PointClassDegreeZero — for regular points E and P, O(P − E) is an
// invertible pair of degree zero, and its class lies in Pic⁰.
var PointClassDegreeZero = pointClassDegreeZeroThm{family.Add(registry.ProofEntry{
	Name: "PointClassDegreeZero",
	Key:  "prop_86f99d5d6760efc2",
	Reading: "deg E = −1 and twisting at P adds one. Both points must be regular: twisting at a " +
		"point whose ideals are not invertible does not raise the degree by one, and a non-invertible " +
		"E is no member of an invertible class. deg E = −1 comes from E regular alone: (A₀, A₁) " +
		"twisted at E is E⁻¹, of degree one (DegreeTwist), and DegreeInverse turns that into −1.",
	Deps: []registry.EntryLike{
		CurvePointClassDef,
		InPicZero,
		lattice_pair_twist.TwistInvertible,
		lattice_pair_twist.BiaffineRegularPointDef,
		lattice_pair_twist.LatticePairTwistDef,
		invertible_lattice_pair.InvertibleLatticeInverse,
		invertible_lattice_pair.MulComm,
		invertible_lattice_pair.MulOne,
		DegreeTwist,
		DegreeInverse,
		DegreeStructure,
		algebraic_curve.CurveLatticeData,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀E P:prod(set(A), set(A)).",
		Hypotheses: []string{
			"curve_over_line(L, k, t, A₀, A₁, A₀₁)",
			"biaffine_regular_point(field_ring(L), k, A₀, A₁, A₀₁, E)",
			"biaffine_regular_point(field_ring(L), k, A₀, A₁, A₀₁, P)",
		},
		Conclusion: "invertible_lattice_pair(field_ring(L), " +
			"    A₀, " +
			"    A₁, " +
			"    A₀₁, " +
			"    lattice_pair_twist(field_ring(L), A₀, A₁, E, P)) ∧ " +
			"curve_degree(field_ring(L), k, A₀, A₁, A₀₁, lattice_pair_twist(field_ring(L), A₀, A₁, E, P)) = " +
			"&0 ∧ " +
			"curve_point_class(field_ring(L), A₀, A₁, E, P) ∈ curve_pic_zero(field_ring(L), k, A₀, A₁, A₀₁)",
	},
		"E and P are invertible (BiaffineRegularPointDef), so E(P) is (TwistInvertible); deg "+
			"E(P) = deg E + &1 (DegreeTwist); E⁻¹ = (A₀, A₁)(E) (LatticePairTwistDef, MulComm, "+
			"MulOne) has degree deg O + &1 = &1 (DegreeTwist, DegreeStructure), and deg E = −deg "+
			"E⁻¹ = −&1 (DegreeInverse at E⁻¹, (E⁻¹)⁻¹ = E by InvertibleLatticeInverse); so deg "+
			"E(P) = &0, and its class is in Pic⁰ (InPicZero, CurvePointClassDef)"),
})}
