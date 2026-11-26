// affine_pieces.go — the Jacobian criterion: each affine piece of a smooth
// projective equation curve is integrally closed in its generic field.

package projective_affine_piece

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/residue_points"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/abelian_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/quotient_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/free_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/algebra_points"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/fractional_ideal"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ideal_factorization"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/invertible_fractional_ideal"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/local_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/homogeneous_polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_algebra"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_algebra_evaluation"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_ideal"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/zariski_cotangent"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/scheme/projective_curve"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// AffinePieceFractionField — for a point x of M whose coordinates lie in K
// and generate it over k, one of them being one, the affine piece where the
// j-th coordinate is not zero — the values at the ratios x(i)/x(j) of the
// polynomials over k — is a subring of M inside K holding k, with K as its
// field of fractions. The piece is a subring holding k
// (AffinePieceDegreeFiltration), and it lies in K since evaluation at the
// ratios, which lie in K, takes the polynomials into K
// (projective_curve.PointEvaluation); the field the piece generates holds
// the inverse of x(j), the ratio at the coordinate that is one, hence x(j)
// and every coordinate, the ratio times x(j).
var AffinePieceFractionField = affinePieceFractionFieldThm{family.Add(registry.ProofEntry{
	Name: "AffinePieceFractionField",
	Key:  "prop_18069186938d6244",
	Reading: "The coordinate equal to one is load-bearing: the piece sees x only " +
		"through its ratios, so at x = (t, t) it is k while K = k(t). subfield(M, K) " +
		"puts the coordinates in M's carrier, where M's operations obey the field laws.",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k K:set(A). ∀n j:num. ∀x:(num → A).",
		Hypotheses: []string{
			"subfield(M, k)",
			"subfield(M, K)",
			"∀i:num. i ≤ n ⇒ x(i) ∈ K",
			"∃i:num. i ≤ n ∧ x(i) = M.one",
			"field_adjoin(M, k, {x(i) | i:num | i ≤ n}) = K",
			"j ≤ n",
			"x(j) ≠ M.zero",
		},
		Conclusion: "subring(field_ring(M), «piece») ∧ " +
			"k ⊆ «piece» ∧ " +
			"«piece» ⊆ K ∧ " +
			"fraction_field_carrier(restrict_ring(field_ring(M), K), «piece»)",
		Abbrev: Abbrev{
			{Name: "evaluation", Text: "polynomial_algebra_eval(«hilbertCoefficients», " +
				"    field_ring(M), " +
				"    (λa:A. a), " +
				"    (λi:num. x(i) * M.inv(x(j))))"},
			{Name: "generated", Text: "field_adjoin(M, «piece», ∅)"},
		},
	}, func(
		a *Argument,
		M field.FieldFact[on.M],
		k, K *Expr[Set[A]],
		n, j *Expr[Nat],
		x *Arrow[Nat, A],
		h Fact,
	) {
		p := a.Conjuncts(
			h,
			"k is a subfield of M",
			"K is a subfield of M",
			"the coordinates lie in K",
			"some coordinate is one",
			"the coordinates generate K over k",
			"j indexes a coordinate",
			"the j-th coordinate is not zero")
		subfieldk, subfieldK, coordinates, normalized, generated, jIndex, nonzero :=
			p[0], p[1], p[2], p[3], p[4], p[5], p[6]
		ops := a.TermAs[FieldOps[A]]("M")
		fieldRing := a.TermAs[module_record.RingOps[A]]("field_ring(M)")
		coefficients := a.TermAs[module_record.RingOps[A]]("«hilbertCoefficients»")
		identity := a.TermAs[Fun[A, A]]("λa:A. a")
		ratios := a.TermAs[Fun[Nat, A]]("λi:num. x(i) * M.inv(x(j))")
		indices := a.TermAs[Set[Nat]]("{i:num | i ≤ n}")
		piece := a.TermAs[Set[A]]("«piece»")
		adjoined := a.TermAs[Set[A]]("«generated»")
		xj := a.TermAs[A]("x(j)")
		inverse := a.TermAs[A]("M.inv(x(j))")
		ringM := field.RingOn.Read(M)
		KInM := a.Have(
			"K lies in M",
			"K ⊆ M.carrier",
			By(subfieldK, field.SubfieldSubset))
		coordinatesInM := a.Have(
			"so the coordinates lie in M",
			"∀i:num. i ≤ n ⇒ x(i) ∈ M.carrier",
			BySets(coordinates, KInM))
		pieceFacts := a.Conjuncts(
			GroupPremises(
				subfieldk,
				coordinatesInM,
				jIndex,
				nonzero,
				Read(AffinePieceDegreeFiltration, M).At(k, n, j, x)),
			"the piece is a subring of M",
			"it holds k",
			"its layers increase with the degree",
			"it is the union of its layers")
		subringPiece, kInPiece := pieceFacts[0], pieceFacts[1]
		inclusion := a.Have(
			"k includes into M as a ring map",
			"ring_homomorphism(«hilbertCoefficients», field_ring(M), λa:A. a)",
			By(
				subfieldk,
				field.SubfieldSubring.Read(M).At(k),
				ring_homomorphism.SubringInclusionHom.Read(ringM).At(k)))
		kInK := a.Have(
			"k lies in K, the field its coordinates generate over k",
			"k ⊆ K",
			BySets(
				generated,
				subfieldk,
				coordinates,
				KInM,
				field.SubfieldSubset.At(ops, k),
				algebraic_element.AdjoinSubfield.Read(M).At(k, a.TermAs[Set[A]]("{x(i) | i:num | i ≤ n}"))))
		xjInK := a.Have(
			"x(j) lies in K",
			"x(j) ∈ K",
			By(coordinates.At(j), jIndex))
		inverseInK := a.Have(
			"and so does its inverse",
			"M.inv(x(j)) ∈ K",
			By(subfieldK, xjInK, field.SubfieldInv.At(ops, K, xj)))
		ratiosInK := a.Have(
			"every ratio lies in K",
			"∀i:num. i ≤ n ⇒ x(i) * M.inv(x(j)) ∈ K",
			By(coordinates, subfieldK, inverseInK, At(field.SubfieldMul, ops, K)))
		ratiosInM := a.Have(
			"so in M",
			"∀i:num. i ∈ {i:num | i ≤ n} ⇒ x(i) * M.inv(x(j)) ∈ M.carrier",
			BySets(ratiosInK, KInM))
		values := a.Conjuncts(
			GroupPremises(
				subfieldk,
				subfieldK,
				kInK,
				ratiosInK,
				projective_curve.PointEvaluation.Read(M).At(k, K, n, ratios)),
			"evaluation at the ratios is a ring map from the polynomials into M",
			"whose values lie in K, a subring holding k and the ratios")
		pieceInK := a.Have(
			"so the piece, its image, lies in K",
			"«piece» ⊆ K",
			BySets(values[1]))
		coefficientsRing := a.Have(
			"k is a ring under M's operations",
			"comm_ring_on(«hilbertCoefficients»)",
			By(subfieldk, field.SubfieldCommRing.Read(M).At(k)))
		ratiosInPiece := a.Have(
			"each ratio is the value of its variable",
			"∀i:num. i ≤ n ⇒ x(i) * M.inv(x(j)) ∈ «piece»",
			Derive(func(b *Argument) {
				i := b.FixAs[Nat]("i")
				iIndex := b.Assume()
				variable := b.Have(
					"the variable is a polynomial",
					"polynomial_algebra_var(«hilbertCoefficients», i) ∈ "+
						"polynomial_algebra(«hilbertCoefficients», {i:num | i ≤ n})",
					By(
						coefficientsRing,
						iIndex,
						polynomial_algebra.PolynomialAlgebraVarIn.At(coefficients, indices, i)))
				value := b.Have(
					"which evaluates to the ratio",
					"«evaluation»(polynomial_algebra_var(«hilbertCoefficients», i)) = x(i) * M.inv(x(j))",
					By(
						inclusion,
						ratiosInM.At(i),
						iIndex,
						polynomial_algebra_evaluation.PolynomialAlgebraEvalVar.At(
							coefficients, fieldRing, identity, ratios, i)))
				b.Show(
					"so the ratio lies in the piece",
					BySets(variable, value))
			}))
		fractions := a.Conjuncts(
			GroupPremises(subringPiece, integral_element.SubringFractionField.Read(M).At(piece)),
			"the field the piece generates is a subfield of M",
			"it holds the piece",
			"it is the field of fractions of the piece")
		subfieldGenerated, pieceInGenerated, fractionsGenerated := fractions[0], fractions[1], fractions[2]
		generatedInK := a.Have(
			"K holds the piece, so the field it generates",
			"«generated» ⊆ K",
			By(subfieldK, pieceInK, set_order.EmptySubset.At(K), algebraic_element.AdjoinLeast.Read(M)))
		o, one := a.UnpackAs[Nat](normalized, "o")
		oParts := a.Conjuncts(
			one,
			"o indexes a coordinate",
			"the o-th coordinate is one")
		oIndex, isOne := oParts[0], oParts[1]
		xjInM := a.Have(
			"x(j) and its inverse lie in M",
			"x(j) ∈ M.carrier ∧ M.inv(x(j)) ∈ M.carrier",
			BySets(KInM, xjInK, inverseInK))
		ratioAtOne := a.Have(
			"the ratio at the coordinate that is one is the inverse of x(j)",
			"x(o) * M.inv(x(j)) = M.inv(x(j))",
			By(
				Normalized,
				isOne,
				xjInM,
				At(comm_monoid.LeftIdentityOn.Read(comm_ring.MulMonoidOn.Read(ringM)), inverse)))
		inverseInPiece := a.Have(
			"so the inverse of x(j) lies in the piece",
			"M.inv(x(j)) ∈ «piece»",
			By(ratiosInPiece.At(o), oIndex, ratioAtOne))
		inverseInGenerated := a.Have(
			"and in the field it generates",
			"M.inv(x(j)) ∈ «generated»",
			BySets(inverseInPiece, pieceInGenerated))
		xjInGenerated := a.Have(
			"which holds x(j), the inverse of its inverse",
			"x(j) ∈ «generated»",
			By(
				subfieldGenerated,
				inverseInGenerated,
				xjInM,
				field.SubfieldInv.At(ops, adjoined, inverse),
				At(field.InvInvOn.Read(M), xj)))
		cancel := a.Have(
			"the inverse of x(j) cancels it",
			"M.inv(x(j)) * x(j) = M.one",
			By(xjInM, nonzero, At(field.MulLeftInverseOn.Read(M), xj)))
		coordinatesInGenerated := a.Have(
			"every coordinate is its ratio times x(j), so lies in the field the piece generates",
			"∀i:num. i ≤ n ⇒ x(i) ∈ «generated»",
			Derive(func(b *Argument) {
				i := b.FixAs[Nat]("i")
				iIndex := b.Assume()
				xiInM := b.Have(
					"x(i) lies in M",
					"x(i) ∈ M.carrier",
					BySets(coordinates.At(i), iIndex, KInM))
				split := b.Have(
					"x(i) is its ratio times x(j)",
					"x(i) = (x(i) * M.inv(x(j))) * x(j)",
					ByArith(M, xiInM, xjInM, Scaled(x.Apply(i), cancel)))
				ratioIn := b.Have(
					"the ratio lies in the field the piece generates",
					"x(i) * M.inv(x(j)) ∈ «generated»",
					BySets(ratiosInPiece.At(i), iIndex, pieceInGenerated))
				b.Show(
					"and so does its product with x(j)",
					By(
						split,
						subfieldGenerated,
						ratioIn,
						xjInGenerated,
						field.SubfieldMul.At(ops, adjoined, b.TermAs[A]("x(i) * M.inv(x(j))"), xj)))
			}))
		generatorsInGenerated := a.Have(
			"the coordinates lie in the field the piece generates",
			"{x(i) | i:num | i ≤ n} ⊆ «generated»",
			Unfold(set_basic.SubsetDef),
			Derive(func(b *Argument) {
				b.FixAs[A]("y")
				yIn := b.Assume()
				_, isCoordinate := b.UnpackAs[Nat](yIn, "i")
				b.Show(
					"a coordinate lies there",
					By(isCoordinate, coordinatesInGenerated))
			}))
		KInGenerated := a.Have(
			"the field the piece generates holds k and the coordinates, so K",
			"K ⊆ «generated»",
			BySets(
				generated,
				subfieldGenerated,
				kInPiece,
				pieceInGenerated,
				generatorsInGenerated,
				algebraic_element.AdjoinLeast.Read(M).At(k, a.TermAs[Set[A]]("{x(i) | i:num | i ≤ n}"), adjoined)))
		generatedIsK := a.Have(
			"so it is K",
			"«generated» = K",
			BySets(KInGenerated, generatedInK))
		a.Show(
			"the piece is a subring holding k inside K, and K, "+
				"the field it generates, is its field of fractions",
			By(subringPiece, kInPiece, pieceInK, fractionsGenerated, generatedIsK))
	}),
})}

// AffinePieceDegreeFiltration — the affine piece where the j-th coordinate
// of a point x of M is not zero is a subring of M holding k, and the union
// of its layers V(d), the values at the affine point y = x/x(j) of the forms
// of degree d, which increase with d. As y(j) = 1, Q(y) = (Q·X_jᵗ)(y), so
// V(d) ⊆ V(d + t); and the piece is the chart of X_j at y, the z with
// z·X_j(y)ᵃ = Q(y) for a form Q of degree a, since that chart is a subring
// holding k (projective_curve.ChartSubring) and the affine coordinates
// y(i) = X_i(y)/X_j(y) lie in it, while X_j(y) = 1 makes each of its
// members the value Q(y).
var AffinePieceDegreeFiltration = affinePieceDegreeFiltrationThm{family.Add(registry.ProofEntry{
	Name: "AffinePieceDegreeFiltration",
	Key:  "prop_8defa519b3d497fe",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k:set(A). ∀n j:num. ∀x:(num → A).",
		Hypotheses: []string{
			"subfield(M, k)",
			"∀i:num. i ≤ n ⇒ x(i) ∈ M.carrier",
			"j ≤ n",
			"x(j) ≠ M.zero",
		},
		Conclusion: "subring(field_ring(M), «piece») ∧ " +
			"k ⊆ «piece» ∧ " +
			"(∀d e:num. d ≤ e ⇒ «affineValues»(d) ⊆ «affineValues»(e)) ∧ " +
			"(∀s:A. s ∈ «piece» ⇔ ∃d:num. s ∈ «affineValues»(d))",
		Abbrev: Abbrev{
			{Name: "varPower", Text: "λb:num. " +
				"    monoid_pow(polynomial_algebra_mul(«hilbertCoefficients»), " +
				"        polynomial_algebra_one(«hilbertCoefficients»), " +
				"        polynomial_algebra_var(«hilbertCoefficients», j), " +
				"        b)"},
			// The chart of X_j at the affine point: X_j takes the value one there.
			{Name: "unitChart", Text: "{z:A | " +
				"    z ∈ M.carrier ∧ " +
				"    ∃a:num. ∃Q:((num → num) → A). " +
				"        homogeneous_polynomial(«hilbertCoefficients», n, 1 * a, Q) ∧ " +
				"        z * " +
				"        monoid_pow(M.mul, " +
				"            M.one, " +
				"            «affine»(polynomial_algebra_var(«hilbertCoefficients», j)), " +
				"            a) = " +
				"        «affine»(Q)}"},
		},
	}, func(
		a *Argument,
		M field.FieldFact[on.M],
		k *Expr[Set[A]],
		n, j *Expr[Nat],
		x *Arrow[Nat, A],
		h Fact,
	) {
		p := a.Conjuncts(
			h,
			"k is a subfield of M",
			"the coordinates of x up to n lie in M",
			"j indexes a coordinate",
			"the j-th coordinate is not zero")
		subK, coordinates, jIndex, nonzero := p[0], p[1], p[2], p[3]
		ring := field.RingOn.Read(M)
		monoid := comm_ring.MulMonoidOn.Read(ring)
		fieldOps := a.TermAs[FieldOps[A]]("M")
		fieldRing := a.TermAs[module_record.RingOps[A]]("field_ring(M)")
		coefficients := a.TermAs[module_record.RingOps[A]]("«hilbertCoefficients»")
		identity := a.TermAs[Fun[A, A]]("λa:A. a")
		affinePoint := a.TermAs[Fun[Nat, A]]("λi:num. x(i) * M.inv(x(j))")
		variables := a.TermAs[Set[Nat]]("{i:num | i ≤ n}")
		varJ := a.TermAs[Fun[Fun[Nat, Nat], A]]("polynomial_algebra_var(«hilbertCoefficients», j)")
		one := a.TermAs[Nat]("1")

		// The affine point y = x/x(j), its coordinates in M, y(j) = 1.
		xjIn := a.Have(
			"x(j) and its inverse lie in M",
			"x(j) ∈ M.carrier ∧ M.inv(x(j)) ∈ M.carrier",
			By(field.InvIn.Read(M), coordinates.At(j), jIndex))
		unit := a.Have(
			"x(j) times its inverse is one",
			"x(j) * M.inv(x(j)) = M.one",
			By(xjIn, nonzero, field.MulRightInverseOn.Read(M)))
		ratiosIn := a.Have(
			"the affine coordinates x(i)·x(j)⁻¹ lie in M",
			"∀i:num. i ≤ n ⇒ x(i) * M.inv(x(j)) ∈ M.carrier",
			By(coordinates, xjIn, comm_ring.MulIn.Read(ring)))
		inclusion := a.Have(
			"k includes into M as a ring map",
			"ring_homomorphism(«hilbertCoefficients», field_ring(M), λa:A. a)",
			By(
				subK,
				field.SubfieldSubring.Read(M).At(k),
				ring_homomorphism.SubringInclusionHom.Read(ring).At(k)))
		scalars := a.Have(
			"k is a commutative ring",
			"comm_ring_on(«hilbertCoefficients»)",
			By(subK, field.SubfieldCommRing.Read(M).At(k)))
		evaluation := a.Have(
			"evaluation at the affine point is a ring map out of the polynomials over k",
			"ring_homomorphism(«polynomials», field_ring(M), «affine»)",
			By(subK, ratiosIn, Read(homogeneous_polynomial.EvaluationRingHom, M).At(k, n, affinePoint)))
		variableValues := a.Have(
			"the variable X_i takes the value x(i)/x(j)",
			"∀i:num. i ≤ n ⇒ «affine»(polynomial_algebra_var(«hilbertCoefficients», i)) = x(i) * M.inv(x(j))",
			Derive(func(b *Argument) {
				i := b.FixAs[Nat]("i")
				below := b.Assume()
				b.Show(
					"evaluation sends a variable to its coordinate",
					By(
						inclusion,
						ratiosIn.At(i),
						below,
						polynomial_algebra_evaluation.PolynomialAlgebraEvalVar.At(
							coefficients, fieldRing, identity, affinePoint, i)))
			}))
		atOne := a.Have(
			"so X_j takes the value one",
			"«affine»(polynomial_algebra_var(«hilbertCoefficients», j)) = M.one",
			By(variableValues.At(j), jIndex, unit))

		// Multiplying by a power of X_j raises the degree and keeps the value.
		shift := a.Have(
			"Q·X_jᵗ is a form of degree d + t with the value of Q",
			Statement{
				Binders:    "∀d t:num. ∀Q:((num → num) → A).",
				Hypotheses: []string{"homogeneous_polynomial(«hilbertCoefficients», n, d, Q)"},
				Conclusion: "homogeneous_polynomial(«hilbertCoefficients», " +
					"    n, " +
					"    d + 1 * t, " +
					"    polynomial_algebra_mul(«hilbertCoefficients», Q, «varPower»(t))) ∧ " +
					"«affine»(polynomial_algebra_mul(«hilbertCoefficients», Q, «varPower»(t))) = «affine»(Q)",
			},
			Derive(func(b *Argument) {
				d := b.FixAs[Nat]("d")
				t := b.FixAs[Nat]("t")
				Q := b.FixAs[Fun[Fun[Nat, Nat], A]]("Q")
				form := b.Assume()
				power := b.TermAs[Fun[Fun[Nat, Nat], A]]("«varPower»(t)")
				powerForm := b.Have(
					"X_jᵗ is a form of degree 1·t",
					"homogeneous_polynomial(«hilbertCoefficients», n, 1 * t, «varPower»(t))",
					By(
						scalars,
						jIndex,
						At(homogeneous_polynomial.FormVariable, coefficients, n, j),
						At(homogeneous_polynomial.FormPower, coefficients, n, one, varJ, t)))
				powerValue := b.Have(
					"whose value is 1ᵗ = 1",
					"«affine»(«varPower»(t)) = M.one",
					By(
						scalars,
						jIndex,
						atOne,
						polynomial_algebra.PolynomialAlgebraVarIn.At(coefficients, variables, j),
						ring_homomorphism.RingMapPower.Read(evaluation).AsFact().At(t, varJ),
						comm_monoid.IdentityPowOn.Read(monoid)))
				product := b.Have(
					"so Q·X_jᵗ is a form of degree d + 1·t",
					"homogeneous_polynomial(«hilbertCoefficients», "+
						"    n, "+
						"    d + 1 * t, "+
						"    polynomial_algebra_mul(«hilbertCoefficients», Q, «varPower»(t)))",
					By(
						scalars,
						form,
						powerForm,
						At(homogeneous_polynomial.FormProduct, coefficients, n, d, b.TermAs[Nat]("1 * t"), Q, power)))
				value := b.Have(
					"with value Q(y)·1 = Q(y)",
					"«affine»(polynomial_algebra_mul(«hilbertCoefficients», Q, «varPower»(t))) = «affine»(Q)",
					ByArith(
						M,
						homogeneous_polynomial.FormPolynomial.Read(form),
						homogeneous_polynomial.FormPolynomial.Read(powerForm),
						powerValue,
						ring_homomorphism.MapMul.Read(evaluation).AsFact().At(Q, power),
						ring_homomorphism.MapIn.Read(evaluation).AsFact().At(Q)))
				b.Show(
					"Q·X_jᵗ has degree d + 1·t and the value of Q",
					By(product, value))
			}))
		increasing := a.Have(
			"the layers increase with the degree",
			"∀d e:num. d ≤ e ⇒ «affineValues»(d) ⊆ «affineValues»(e)",
			Derive(func(b *Argument) {
				d := b.FixAs[Nat]("d")
				b.FixAs[Nat]("e")
				below := b.Assume()
				gap := b.Have(
					"e is d + 1·(e − d)",
					"d + 1 * (e - d) = e",
					ByArith(below))
				b.Show(
					"Q(y) for Q of degree d is the value of Q·X_j^(e−d), of degree e",
					BySets(shift.At(d, b.TermAs[Nat]("e - d")), gap))
			}))

		// The piece is the chart of X_j at the affine point.
		chartRing := a.Have(
			"the values over X_j(y)ᵃ of the forms of degree a are a subring holding k",
			"subring(field_ring(M), «unitChart») ∧ k ⊆ «unitChart»",
			By(
				scalars,
				subK,
				ratiosIn,
				jIndex,
				field.CarrierSubfield.Read(M),
				field.SubfieldSubset.At(fieldOps, k),
				At(homogeneous_polynomial.FormVariable, coefficients, n, j),
				Read(projective_curve.ChartSubring, M).At(
					k, a.TermAs[Set[A]]("M.carrier"), n, one, affinePoint, varJ)))
		ratiosInChart := a.Have(
			"each affine coordinate x(i)/x(j) is X_i(y) over X_j(y)",
			"∀i:num. i ≤ n ⇒ x(i) * M.inv(x(j)) ∈ «unitChart»",
			Derive(func(b *Argument) {
				i := b.FixAs[Nat]("i")
				below := b.Assume()
				ratio := b.TermAs[A]("x(i) * M.inv(x(j))")
				witness := b.Have(
					"X_i is a form of degree 1·1 with x(i)/x(j)·X_j(y)¹ = X_i(y)",
					"homogeneous_polynomial(«hilbertCoefficients», "+
						"    n, "+
						"    1 * 1, "+
						"    polynomial_algebra_var(«hilbertCoefficients», i)) ∧ "+
						"x(i) * "+
						"M.inv(x(j)) * "+
						"monoid_pow(M.mul, M.one, «affine»(polynomial_algebra_var(«hilbertCoefficients», j)), 1) = "+
						"«affine»(polynomial_algebra_var(«hilbertCoefficients», i))",
					By(
						scalars,
						below,
						variableValues.At(i),
						atOne,
						ratiosIn.At(i),
						At(homogeneous_polynomial.FormVariable, coefficients, n, i),
						nat_arith.MulOne,
						comm_monoid.IdentityPowOn.Read(monoid).At(one),
						comm_monoid.RightIdentityOn.Read(monoid).AsFact().At(ratio)))
				b.Show(
					"so it lies in the chart",
					BySets(witness, ratiosIn.At(i), below))
			}))
		constantsInChart := a.Have(
			"the chart holds k",
			"∀c:A. c ∈ «hilbertCoefficients».carrier ⇒ c ∈ «unitChart»",
			BySets(chartRing))
		valuesInChart := a.Have(
			"so the value at y of every polynomial over k lies in the chart, a subring holding k and the y(i)",
			Statement{
				Binders:    "∀P:((num → num) → A).",
				Hypotheses: []string{"P ∈ polynomial_algebra(«hilbertCoefficients», {i:num | i ≤ n})"},
				Conclusion: "«affine»(P) ∈ «unitChart»",
			},
			Derive(func(b *Argument) {
				P := b.FixAs[Fun[Fun[Nat, Nat], A]]("P")
				polynomial := b.Assume()
				b.Show(
					"evaluation lands in a subring holding the coefficients and the coordinates",
					By(
						inclusion,
						chartRing,
						constantsInChart,
						ratiosInChart,
						polynomial,
						At(
							polynomial_algebra_evaluation.PolynomialAlgebraEvalInSubring,
							coefficients,
							fieldRing,
							identity,
							affinePoint,
							variables,
							a.TermAs[Set[A]]("«unitChart»"),
							P)))
			}))
		pieceInChart := a.Have(
			"the piece lies in the chart",
			"«piece» ⊆ «unitChart»",
			BySets(valuesInChart))
		chartInLayers := a.Have(
			"a member z of the chart, z·1ᵃ = Q(y), is the value of the form Q of degree 1·a",
			"∀z:A. z ∈ «unitChart» ⇒ ∃d:num. z ∈ «affineValues»(d)",
			Derive(func(b *Argument) {
				z := b.FixAs[A]("z")
				inChart := b.Assume()
				parts := b.Conjuncts(
					inChart,
					"z lies in M",
					"z·X_j(y)ᵃ is Q(y) for a form Q of degree 1·a")
				degree, _, numerator := b.Unpack2As[Nat, Fun[Fun[Nat, Nat], A]](parts[1], "a", "Q")
				value := b.Have(
					"X_j(y) = 1, so z = Q(y)",
					"z = «affine»(Q)",
					By(
						numerator,
						atOne,
						parts[0],
						comm_monoid.IdentityPowOn.Read(monoid).At(degree),
						comm_monoid.RightIdentityOn.Read(monoid).AsFact().At(z)))
				b.Take(b.TermAs[Nat]("1 * a"))
				b.Show(
					"z lies in the layer of degree 1·a",
					BySets(value, numerator))
			}))
		layersInPiece := a.Have(
			"a form is a polynomial, so its value at y lies in the piece",
			"∀d:num. «affineValues»(d) ⊆ «piece»",
			Derive(func(b *Argument) {
				b.FixAs[Nat]("d")
				polynomials := b.Have(
					"the forms of degree d are polynomials",
					Statement{
						Binders:    "∀P:((num → num) → A).",
						Hypotheses: []string{"homogeneous_polynomial(«hilbertCoefficients», n, d, P)"},
						Conclusion: "P ∈ polynomial_algebra(«hilbertCoefficients», {i:num | i ≤ n})",
					},
					By(homogeneous_polynomial.FormPolynomial))
				b.Show(
					"so their values lie in the piece",
					BySets(polynomials))
			}))
		chartInPiece := a.Have(
			"so the chart lies in the piece",
			"«unitChart» ⊆ «piece»",
			Unfold(set_basic.SubsetDef),
			Derive(func(b *Argument) {
				z := b.FixAs[A]("z")
				inChart := b.Assume()
				d, inLayer := b.UnpackAs[Nat](GroupPremises(inChart, chartInLayers.At(z)), "d")
				b.Show(
					"z lies in a layer, inside the piece",
					BySets(inLayer, layersInPiece.At(d)))
			}))
		pieceIsChart := a.Have(
			"the piece is the chart",
			"«piece» = «unitChart»",
			By(pieceInChart, chartInPiece, set_order.SubsetAntisym))
		subringPiece := a.Have(
			"so the piece is a subring holding k",
			"subring(field_ring(M), «piece») ∧ k ⊆ «piece»",
			By(pieceIsChart, chartRing))
		exhausts := a.Have(
			"the piece is the union of its layers",
			"∀s:A. s ∈ «piece» ⇔ ∃d:num. s ∈ «affineValues»(d)",
			Derive(func(b *Argument) {
				s := b.FixAs[A]("s")
				b.Iff()
				b.Forward(
					"a member of the piece lies in the chart, so in a layer",
					func(c *Argument, inPiece Fact) {
						inChart := c.Have(
							"s lies in the chart",
							"s ∈ «unitChart»",
							BySets(inPiece, pieceInChart))
						c.Show(
							"and a member of the chart lies in a layer",
							By(inChart, chartInLayers.At(s)))
					})
				b.Backward(
					"a member of a layer lies in the piece",
					func(c *Argument, inLayer Fact) {
						d, member := c.UnpackAs[Nat](inLayer, "d")
						c.Show(
							"the layers lie in the piece",
							BySets(member, layersInPiece.At(d)))
					})
			}))
		a.Show(
			"the piece is a subring holding k, the increasing union of its layers",
			By(subringPiece, increasing, exhausts))
	}),
})}

// AffinePieceLayerClasses — for an ideal H of the affine piece at a point x
// of the curve and a form F of degree r whose value f = F(y) at the affine
// point lies in H and is not zero, the classes modulo H of the layer of
// degree r + d are a subspace of the piece modulo H of dimension at most
// h(r + d) − h(d). The map from the forms of degree r + d to the classes,
// P ↦ P(y) + H, is k-linear onto them; its kernel holds the forms in the
// ideal, which vanish at x and so at y, and F times every form Q of degree
// d, whose value f·Q(y) lies in H. F lies outside the prime ideal, as
// F(y) ≠ 0, so the kernel has codimension at most h(r + d) − h(d)
// (projective_curve.HyperplaneSectionBound), and that codimension is the
// dimension of the image (RankNullity).
var AffinePieceLayerClasses = affinePieceLayerClassesThm{family.Add(registry.ProofEntry{
	Name: "AffinePieceLayerClasses",
	Key:  "prop_618235af3393d6e6",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). " +
			"∀k:set(A). " +
			"∀n j:num. " +
			"∀E:set((num → num) → A). " +
			"∀x:(num → A). " +
			"∀H:set(A). " +
			"∀r:num. " +
			"∀F:((num → num) → A). " +
			"∀d:num.",
		Hypotheses: []string{
			"smooth_projective_equation_curve(M, k, n, E)",
			"x ∈ projective_equation_points(field_ring(M), k, M.carrier, n, E)",
			"j ≤ n",
			"x(j) ≠ M.zero",
			"ring_ideal(restrict_ring(field_ring(M), «piece»), H)",
			"homogeneous_polynomial(«hilbertCoefficients», n, r, F)",
			"«affine»(F) ∈ H",
			"«affine»(F) ≠ M.zero",
		},
		Conclusion: "submodule(«hilbertCoefficients», «quotient», «classes»(r + d)) ∧ " +
			"finite_dimensional(«hilbertCoefficients», restrict_module(«quotient», «classes»(r + d))) ∧ " +
			"module_dim(«hilbertCoefficients», restrict_module(«quotient», «classes»(r + d))) + " +
			"projective_hilbert_function(field_ring(M), k, n, E, d) ≤ " +
			"projective_hilbert_function(field_ring(M), k, n, E, r + d)",
		Abbrev: Abbrev{
			{Name: "forms", Text: "λd:num. " +
				"    {P:(num → num) → A | homogeneous_polynomial(«hilbertCoefficients», n, d, P)}"},
			{Name: "formSpace", Text: "λd:num. " +
				"    mk_module(fun_add, " +
				"        fun_zero, " +
				"        fun_neg, " +
				"        λa:A. λP:((num → num) → A). λm:(num → num). a * P(m), " +
				"        «forms»(d))"},
			// A form's class modulo H: its value at the affine point, read in the quotient.
			{Name: "residue", Text: "coset_map(M.add, H) ∘ «affine»"},
			{Name: "kernel", Text: "group_kernel(H, «forms»(r + d), «residue»)"},
		},
	}, func(
		a *Argument,
		M field.FieldFact[on.M],
		k *Expr[Set[A]],
		n, j *Expr[Nat],
		E *Expr[Set[Fun[Fun[Nat, Nat], A]]],
		x *Arrow[Nat, A],
		H *Expr[Set[A]],
		r *Expr[Nat],
		F *Arrow[Fun[Nat, Nat], A],
		d *Expr[Nat],
		h Fact,
	) {
		hyp := a.Conjuncts(
			h,
			"the curve is a smooth projective equation curve",
			"x is a point of it over M",
			"j indexes a coordinate",
			"the j-th coordinate is not zero",
			"H is an ideal of the piece",
			"F is a form of degree r",
			"f = F(y) lies in H",
			"and is not zero")
		curve, point, jIndex, nonzero, ideal, formF, fInH, fNonzero :=
			hyp[0], hyp[1], hyp[2], hyp[3], hyp[4], hyp[5], hyp[6], hyp[7]
		subK, equations :=
			projective_curve.CurveConstantsSubfield.Read(curve),
			projective_curve.CurveEquationsForms.Read(curve)
		fieldRing := a.TermAs[module_record.RingOps[A]]("field_ring(M)")
		carrier := a.TermAs[Set[A]]("M.carrier")
		inM := a.Have(
			"the coordinates of x up to n lie in M",
			"∀i:num. i ≤ n ⇒ x(i) ∈ M.carrier",
			By(point, projective_curve.PointCoordinatesIn))
		vanishes := a.Have(
			"every equation vanishes at x",
			"∀P:((num → num) → A). P ∈ E ⇒ «at»(P) = M.zero",
			By(point, At(projective_curve.PointEquationsVanish, fieldRing, k, carrier, n, E, x)))
		ring := field.RingOn.Read(M)
		monoid := comm_ring.MulMonoidOn.Read(ring)
		fieldOps := a.TermAs[FieldOps[A]]("M")
		coefficients := a.TermAs[module_record.RingOps[A]]("«hilbertCoefficients»")
		source := a.TermAs[module_record.RingOps[A]]("restrict_ring(field_ring(M), «piece»)")
		identity := a.TermAs[Fun[A, A]]("λa:A. a")
		inv := a.TermAs[Fun[A, A]]("M.inv")
		affinePoint := a.TermAs[Fun[Nat, A]]("λi:num. x(i) * M.inv(x(j))")
		affine := a.TermAs[Fun[Fun[Fun[Nat, Nat], A], A]]("«affine»")
		polynomials := a.TermAs[Set[Fun[Fun[Nat, Nat], A]]](
			"polynomial_algebra(«hilbertCoefficients», {i:num | i ≤ n})")
		piece := a.TermAs[Set[A]]("«piece»")
		vectors := a.TermAs[module_record.ModuleOps[A, A]](
			"restrict_module(regular_module(field_ring(M)), «piece»)")
		quotient := a.TermAs[module_record.ModuleOps[A, Set[A]]]("«quotient»")
		degree := a.TermAs[Nat]("r + d")
		space := a.TermAs[module_record.ModuleOps[A, Fun[Fun[Nat, Nat], A]]]("«formSpace»(r + d)")
		forms := a.TermAs[Set[Fun[Fun[Nat, Nat], A]]]("«forms»(r + d)")
		residue := a.TermAs[Fun[Fun[Fun[Nat, Nat], A], Set[A]]]("«residue»")
		kernel := a.TermAs[Set[Fun[Fun[Nat, Nat], A]]]("«kernel»")
		classMap := a.TermAs[Fun[A, Set[A]]]("coset_map(M.add, H)")
		zero := a.TermAs[A]("M.zero")

		// The affine point, evaluation there, and the piece.
		xjIn := a.Have(
			"x(j) and its inverse lie in M",
			"x(j) ∈ M.carrier ∧ M.inv(x(j)) ∈ M.carrier",
			By(field.InvIn.Read(M), inM.At(j), jIndex))
		ratiosIn := a.Have(
			"the affine coordinates x(i)·x(j)⁻¹ lie in M",
			"∀i:num. i ≤ n ⇒ x(i) * M.inv(x(j)) ∈ M.carrier",
			By(inM, xjIn, comm_ring.MulIn.Read(ring)))
		inclusion := a.Have(
			"k includes into M as a ring map",
			"ring_homomorphism(«hilbertCoefficients», field_ring(M), λa:A. a)",
			By(
				subK,
				field.SubfieldSubring.Read(M).At(k),
				ring_homomorphism.SubringInclusionHom.Read(ring).At(k)))
		scalars := a.Have(
			"k is a commutative ring",
			"comm_ring_on(«hilbertCoefficients»)",
			By(subK, field.SubfieldCommRing.Read(M).At(k)))
		evaluation := a.Have(
			"evaluation at the affine point is a ring map out of the polynomials over k",
			"ring_homomorphism(«polynomials», field_ring(M), «affine»)",
			By(subK, ratiosIn, Read(homogeneous_polynomial.EvaluationRingHom, M).At(k, n, affinePoint)))
		pieceRing := a.Have(
			"the piece is a subring of M holding k",
			"subring(field_ring(M), «piece») ∧ k ⊆ «piece»",
			By(subK, inM, jIndex, nonzero, Read(AffinePieceDegreeFiltration, M).At(k, n, j, x)))

		// The piece and H as vector spaces over k, and the projection modulo H.
		sourceRing := a.Have(
			"the piece is a commutative ring in which k is a field",
			"comm_ring_on(restrict_ring(field_ring(M), «piece»)) ∧ "+
				"ring_subfield(restrict_ring(field_ring(M), «piece»), M.inv, k)",
			By(subK, pieceRing, comm_ring.SubringRingOn.Read(ring), field.SubfieldRingSubfield.Read(M)))
		structures := a.Have(
			"over k the piece is a vector space and H a subspace of it",
			"module_on(«hilbertCoefficients», restrict_module(regular_module(field_ring(M)), «piece»)) ∧ "+
				"submodule(«hilbertCoefficients», restrict_module(regular_module(field_ring(M)), «piece»), H)",
			By(
				sourceRing,
				pieceRing,
				ideal,
				module_dimension.IdealQuotientModuleOn.At(source, k, inv, H),
				module_record.RegularModuleRestrict,
				module_record.RestrictRingTwice))
		pieceSubspace := a.Have(
			"the piece is a k-subspace of M",
			"submodule(«hilbertCoefficients», regular_module(field_ring(M)), «piece»)",
			By(
				pieceRing,
				fractional_ideal.SubringSubmodule.Read(M).At(piece),
				submodule.SubmoduleRestrictScalars.At(
					source,
					a.TermAs[module_record.ModuleOps[A, A]]("regular_module(field_ring(M))"),
					piece,
					coefficients)))
		projection := a.Have(
			"the class map is a linear map from the piece onto the piece modulo H",
			"module_homomorphism(«hilbertCoefficients», "+
				"    restrict_module(regular_module(field_ring(M)), «piece»), "+
				"    «quotient», "+
				"    coset_map(M.add, H))",
			By(structures, module_homomorphism.ProjectionHom))

		// A form's class: the forms of degree r + d map linearly to the piece modulo H.
		throughIdentity := a.Have(
			"M over k through the inclusion is M's regular module",
			"scalar_restriction(λa:A. a, regular_module(field_ring(M))) = regular_module(field_ring(M))",
			Simp(Fwd(module_record.ScalarRestrictionDef), Fwd(module_record.RegularModuleDef)),
			Basic())
		valuesLinear := a.Have(
			"evaluation at the affine point is k-linear on the forms of degree r + d",
			"module_homomorphism(«hilbertCoefficients», "+
				"    «formSpace»(r + d), "+
				"    regular_module(field_ring(M)), "+
				"    «affine»)",
			By(
				M,
				subK,
				inclusion,
				ratiosIn,
				throughIdentity,
				At(projective_curve.EvaluationLinear, fieldOps, fieldOps, k, n, degree, identity, affinePoint)))
		valuesInPiece := a.Have(
			"a form is a polynomial, so its value at y lies in the piece",
			"∀P:((num → num) → A). P ∈ «forms»(r + d) ⇒ «affine»(P) ∈ «piece»",
			Derive(func(b *Argument) {
				b.FixAs[Fun[Fun[Nat, Nat], A]]("P")
				form := b.Assume()
				polynomial := b.Have(
					"P is a polynomial over k",
					"P ∈ polynomial_algebra(«hilbertCoefficients», {i:num | i ≤ n})",
					By(form, homogeneous_polynomial.FormPolynomial))
				b.Show(
					"so its value lies in the piece",
					BySets(polynomial))
			}))
		residueLinear := a.Have(
			"so P ↦ P(y) + H is k-linear from the forms of degree r + d to the piece modulo H",
			"module_homomorphism(«hilbertCoefficients», «formSpace»(r + d), «quotient», «residue»)",
			By(
				projection,
				module_homomorphism.HomCompose.At(coefficients, space, vectors, quotient, affine, classMap),
				valuesLinear,
				pieceSubspace,
				valuesInPiece,
				module_homomorphism.HomCorestrict))

		// What the kernel holds: the forms in the ideal, and F times the forms of degree d.
		equationsVanish := a.Have(
			"an equation vanishes at y, a scaling of x",
			"∀P:((num → num) → A). P ∈ E ⇒ «affine»(P) = M.zero",
			Derive(func(b *Argument) {
				P := b.FixAs[Fun[Fun[Nat, Nat], A]]("P")
				inE := b.Assume()
				e, form := b.UnpackAs[Nat](equations.At(b.MemberOf[on.Any](P, inE)), "e")
				b.Show(
					"P(y) is x(j)⁻ᵉ·P(x), and P(x) = 0",
					By(
						inclusion,
						form,
						inM,
						xjIn,
						vanishes.At(P),
						inE,
						homogeneous_polynomial.FormZeroScaling.At(
							coefficients, fieldRing, identity, n, e, x, b.TermAs[A]("M.inv(x(j))"), P)))
			}))
		equationsPolynomials := a.Have(
			"the equations are polynomials over k",
			"E ⊆ polynomial_algebra(«hilbertCoefficients», {i:num | i ≤ n})",
			BySets(equations, homogeneous_polynomial.FormPolynomial))
		idealVanishes := a.Have(
			"so the ideal they span lies in the kernel of evaluation at y",
			"ideal_span(«polynomials», E) ⊆ "+
				"ring_kernel(M.zero, polynomial_algebra(«hilbertCoefficients», {i:num | i ≤ n}), «affine»)",
			By(
				equationsPolynomials,
				equationsVanish,
				ring_homomorphism.IdealSpanInKernel.Read(evaluation).At(E)))
		zeroClass := a.Have(
			"the class of zero is H",
			"coset_map(M.add, H, M.zero) = H",
			By(module_homomorphism.HomZero.Read(projection)))
		idealInKernel := a.Have(
			"a form of degree r + d in the ideal has class zero",
			"«forms»(r + d) ∩ ideal_span(«polynomials», E) ⊆ «kernel»",
			Unfold(set_basic.SubsetDef),
			Derive(func(b *Argument) {
				u := b.FixAs[Fun[Fun[Nat, Nat], A]]("u")
				inIdeal := b.Assume()
				vanishes := b.Have(
					"u is a form of degree r + d vanishing at y",
					"u ∈ «forms»(r + d) ∧ «affine»(u) = M.zero",
					BySets(inIdeal, idealVanishes, ring_homomorphism.RingKernelDef.At(zero, polynomials, affine)))
				b.Show(
					"so its class is the class of zero",
					By(
						vanishes,
						zeroClass,
						functions.ComposeApply,
						group_homomorphism.InKernel.At(H, forms, residue, u)))
			}))
		multiplesInKernel := a.Have(
			"F times a form Q of degree d has class zero: its value f·Q(y) lies in H",
			Statement{
				Binders:    "∀Q:((num → num) → A).",
				Hypotheses: []string{"homogeneous_polynomial(«hilbertCoefficients», n, d, Q)"},
				Conclusion: "polynomial_algebra_mul(«hilbertCoefficients», F, Q) ∈ «kernel»",
			},
			Derive(func(b *Argument) {
				Q := b.FixAs[Fun[Fun[Nat, Nat], A]]("Q")
				form := b.Assume()
				product := b.TermAs[Fun[Fun[Nat, Nat], A]]("polynomial_algebra_mul(«hilbertCoefficients», F, Q)")
				fValue, qValue := b.TermAs[A]("«affine»(F)"), b.TermAs[A]("«affine»(Q)")
				bothPolynomials := b.Have(
					"Q and F are polynomials over k",
					"Q ∈ polynomial_algebra(«hilbertCoefficients», {i:num | i ≤ n}) ∧ "+
						"F ∈ polynomial_algebra(«hilbertCoefficients», {i:num | i ≤ n})",
					By(
						homogeneous_polynomial.FormPolynomial.Read(form),
						homogeneous_polynomial.FormPolynomial.Read(formF)))
				productForm := b.Have(
					"F·Q is a form of degree r + d",
					"homogeneous_polynomial(«hilbertCoefficients», "+
						"    n, "+
						"    r + d, "+
						"    polynomial_algebra_mul(«hilbertCoefficients», F, Q))",
					By(scalars, form, formF, At(homogeneous_polynomial.FormProduct, coefficients, n, r, d, F, Q)))
				qInPiece := b.Have(
					"Q(y) lies in the piece",
					"«affine»(Q) ∈ «piece»",
					BySets(bothPolynomials))
				productInH := b.Have(
					"so (F·Q)(y) = Q(y)·f lies in H",
					"«affine»(polynomial_algebra_mul(«hilbertCoefficients», F, Q)) ∈ H",
					By(
						bothPolynomials,
						qInPiece,
						fInH,
						ideal,
						ring_homomorphism.MapMul.Read(evaluation).AsFact().At(F, Q),
						ring_homomorphism.MapIn.Read(evaluation).AsFact().At(F),
						ring_homomorphism.MapIn.Read(evaluation).AsFact().At(Q),
						ring_ideal.IdealMul.At(source, H, qValue, fValue),
						comm_monoid.CommOn.Read(monoid).AsFact().At(fValue, qValue)))
				productClass := b.Have(
					"whose class is H",
					"coset_map(M.add, H, «affine»(polynomial_algebra_mul(«hilbertCoefficients», F, Q))) = H",
					By(
						structures,
						productInH,
						module_homomorphism.ProjectionKernel.At(coefficients, vectors, H),
						group_homomorphism.InKernel.At(
							H, piece, classMap, b.TermAs[A]("«affine»(polynomial_algebra_mul(«hilbertCoefficients», F, Q))"))))
				b.Show(
					"so F·Q lies in the kernel",
					By(
						productForm,
						productClass,
						functions.ComposeApply,
						group_homomorphism.InKernel.At(H, forms, residue, product)))
			}))
		fPolynomial := a.Have(
			"F is a polynomial over k",
			"F ∈ polynomial_algebra(«hilbertCoefficients», {i:num | i ≤ n})",
			By(homogeneous_polynomial.FormPolynomial.Read(formF)))
		fOutside := a.Have(
			"outside the ideal, as F(y) ≠ 0 while the ideal vanishes at y",
			"F ∉ ideal_span(«polynomials», E)",
			BySets(idealVanishes, fNonzero, ring_homomorphism.RingKernelDef.At(zero, polynomials, affine)))
		prime := a.Have(
			"the ideal over k is prime",
			"prime_ideal(«polynomials», ideal_span(«polynomials», E))",
			By(curve, Read(projective_curve.CurveIdealPrime, M).At(k, n, E)))

		// The count.
		codimension := a.Have(
			"so the kernel has codimension at most h(r + d) − h(d)",
			"module_dim(«hilbertCoefficients», quotient_module(«formSpace»(r + d), «kernel»)) + "+
				"projective_hilbert_function(field_ring(M), k, n, E, d) ≤ "+
				"projective_hilbert_function(field_ring(M), k, n, E, r + d)",
			By(
				subK,
				prime,
				fPolynomial,
				fOutside,
				module_homomorphism.KernelSubmodule.Read(residueLinear),
				idealInKernel,
				multiplesInKernel,
				Read(projective_curve.HyperplaneSectionBound, M).At(k, n, degree, d, E, kernel, F)))
		finiteForms := a.Have(
			"the forms of degree r + d are finite-dimensional over k, a field",
			"finite_dimensional(«hilbertCoefficients», «formSpace»(r + d)) ∧ "+
				"ring_subfield(«hilbertCoefficients», M.inv, k)",
			By(
				subK,
				projective_curve.FormsDimension.Read(M).At(k, n, degree),
				field.SubfieldRingSubfield.Read(M).At(k, k)))
		rank := a.Have(
			"by rank and nullity the image has the dimension of the forms less the kernel's",
			"module_dim(«hilbertCoefficients», restrict_module(«formSpace»(r + d), «kernel»)) + "+
				"module_dim(«hilbertCoefficients», "+
				"    restrict_module(«quotient», image(«residue», «forms»(r + d)))) = "+
				"module_dim(«hilbertCoefficients», «formSpace»(r + d))",
			By(
				finiteForms,
				residueLinear,
				module_homomorphism.HomSource.Read(residueLinear),
				module_homomorphism.HomTarget.Read(residueLinear),
				module_dimension.RankNullity.At(coefficients, space, inv, quotient, residue)))
		codimensionDim := a.Have(
			"which is the kernel's codimension",
			"module_dim(«hilbertCoefficients», restrict_module(«formSpace»(r + d), «kernel»)) + "+
				"module_dim(«hilbertCoefficients», quotient_module(«formSpace»(r + d), «kernel»)) = "+
				"module_dim(«hilbertCoefficients», «formSpace»(r + d))",
			By(
				finiteForms,
				module_homomorphism.KernelSubmodule.Read(residueLinear),
				module_homomorphism.HomSource.Read(residueLinear),
				module_dimension.QuotientDim.At(coefficients, space, inv, kernel)))
		image := a.Have(
			"the image is the classes of the layer of degree r + d",
			"image(«residue», «forms»(r + d)) = «classes»(r + d)",
			By(set_image.ImageCompose))
		a.Show(
			"the classes are a finite-dimensional subspace of dimension at most h(r + d) − h(d)",
			image.RwRev(),
			SplitConj(
				Case(
					"the image of a linear map from a finite-dimensional space is a finite-dimensional subspace",
					By(
						finiteForms,
						residueLinear,
						module_homomorphism.ImageSubmodule.Read(residueLinear),
						module_dimension.ImageDim.At(coefficients, inv, space, quotient, residue))),
				Case(
					"of dimension at most h(r + d) − h(d)",
					ByArith(codimension, rank, codimensionDim)),
			))
	}),
})}

// AffinePieceQuotientsFinite — every nonzero ideal H of the affine piece of
// a smooth projective equation curve at a point x of the curve over M with
// x(j) not zero has a quotient of finite dimension over k. A
// nonzero f in H is the value F(y) at the affine point of a form F of some
// degree r (AffinePieceDegreeFiltration); past the degree N from which the
// Hilbert function is e·d + 1 − g, the classes modulo H of the layers of
// degree r + N + d have dimension at most h(r + N + d) − h(N + d) = e·r
// (AffinePieceLayerClasses); they increase with d and every class is one
// of them, so the piece modulo H is finite-dimensional (BoundedChainUnion).
var AffinePieceQuotientsFinite = affinePieceQuotientsFiniteThm{family.Add(registry.ProofEntry{
	Name: "AffinePieceQuotientsFinite",
	Key:  "prop_1cd09368a68deccb",
	Reading: "Only the point's coordinates and equations, the primality of the ideal " +
		"over k and the linear Hilbert function are read: the dimension count bounds the " +
		"quotient by e times the degree of a form whose value at the affine point is a " +
		"nonzero member of the ideal. H ≠ {M.zero} is load-bearing: at the generic point the " +
		"piece itself, the quotient by the zero ideal, has transcendence degree one over k.",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). " +
			"∀k:set(A). " +
			"∀n j:num. " +
			"∀E:set((num → num) → A). " +
			"∀x:(num → A). " +
			"∀H:set(A).",
		Hypotheses: []string{
			"smooth_projective_equation_curve(M, k, n, E)",
			"x ∈ projective_equation_points(field_ring(M), k, M.carrier, n, E)",
			"j ≤ n",
			"x(j) ≠ M.zero",
			"ring_ideal(restrict_ring(field_ring(M), «piece»), H)",
			"H ≠ {M.zero}",
		},
		Conclusion: "finite_dimensional(«hilbertCoefficients», «quotient»)",
	}, func(
		a *Argument,
		M field.FieldFact[on.M],
		k *Expr[Set[A]],
		n, j *Expr[Nat],
		E *Expr[Set[Fun[Fun[Nat, Nat], A]]],
		x *Arrow[Nat, A],
		H *Expr[Set[A]],
		h Fact,
	) {
		hyp := a.Conjuncts(
			h,
			"the curve is a smooth projective equation curve",
			"x is a point of the curve over M",
			"j indexes a coordinate",
			"the j-th coordinate is not zero",
			"H is an ideal of the piece",
			"H is not the zero ideal")
		curve, pointM := hyp[0], hyp[1]
		jIndex, nonzero, ideal, nontrivial := hyp[2], hyp[3], hyp[4], hyp[5]
		subK, linear :=
			projective_curve.CurveConstantsSubfield.Read(curve),
			projective_curve.CurveHilbertEventuallyLinear.Read(curve)
		inM := a.Have(
			"the coordinates of x up to n lie in M",
			"∀i:num. i ≤ n ⇒ x(i) ∈ M.carrier",
			By(pointM, projective_curve.PointCoordinatesIn))
		coefficients := a.TermAs[module_record.RingOps[A]]("«hilbertCoefficients»")
		inv := a.TermAs[Fun[A, A]]("M.inv")
		piece := a.TermAs[Set[A]]("«piece»")
		quotient := a.TermAs[module_record.ModuleOps[A, Set[A]]]("«quotient»")

		// The piece is filtered by degree.
		filtration := a.Conjuncts(
			GroupPremises(subK, inM, jIndex, nonzero, Read(AffinePieceDegreeFiltration, M).At(k, n, j, x)),
			"the piece is a subring of M",
			"holding k",
			"its layers increase with the degree",
			"and exhaust it")
		pieceRing, kInPiece, increasing, exhausts :=
			filtration[0], filtration[1], filtration[2], filtration[3]

		// A nonzero f in H, the value at the affine point of a form F of degree r.
		f, nonzeroInH := a.ObtainAs[A](
			"H holds a nonzero f",
			"∃f:A. f ∈ H ∧ f ≠ M.zero",
			BySets(nontrivial, ideal, ring_ideal.IdealZero))
		fParts := a.Conjuncts(
			nonzeroInH,
			"f lies in H",
			"f is not zero")
		HInPiece := a.Have(
			"H lies in the piece",
			"H ⊆ «piece»",
			By(ideal, ring_ideal.IdealSubset))
		fInPiece := a.Have(
			"so does f",
			"f ∈ «piece»",
			BySets(fParts[0], HInPiece))
		r, fLayer := a.ObtainAs[Nat](
			"f lies in a layer V(r) of the piece",
			"∃r:num. f ∈ «affineValues»(r)",
			By(fInPiece, exhausts.At(f)))
		F, fForm := a.ObtainAs[Fun[Fun[Nat, Nat], A]](
			"f is F(y) for a form F of degree r",
			"∃F:((num → num) → A). homogeneous_polynomial(«hilbertCoefficients», n, r, F) ∧ «affine»(F) = f",
			BySets(fLayer))
		formParts := a.Conjuncts(
			fForm,
			"F is a form of degree r",
			"whose value at the affine point is f")
		fValue := a.Have(
			"so F(y) lies in H and is not zero",
			"«affine»(F) ∈ H ∧ «affine»(F) ≠ M.zero",
			By(Normalized, formParts[1], fParts[0], fParts[1]))

		// The Hilbert function is e·d + 1 − g from N on.
		_, _, _, slope := a.Unpack3As[Nat, Nat, Nat](linear, "g", "e", "N")
		hilbert := a.Conjuncts(
			slope,
			"the slope e is positive",
			"and from N on h(d) + g = e·d + 1")
		layers := a.Have(
			"the classes of the layer of degree r + d span at most h(r + d) − h(d) dimensions",
			"∀d:num. "+
				"    submodule(«hilbertCoefficients», «quotient», «classes»(r + d)) ∧ "+
				"    finite_dimensional(«hilbertCoefficients», restrict_module(«quotient», «classes»(r + d))) ∧ "+
				"    module_dim(«hilbertCoefficients», restrict_module(«quotient», «classes»(r + d))) + "+
				"    projective_hilbert_function(field_ring(M), k, n, E, d) ≤ "+
				"    projective_hilbert_function(field_ring(M), k, n, E, r + d)",
			a.ForEach(func(d *Expr[Nat]) Action {
				return By(
					curve,
					pointM,
					jIndex,
					nonzero,
					ideal,
					formParts[0],
					fValue,
					Read(AffinePieceLayerClasses, M).At(k, n, j, E, x, H, r, F, d))
			}))

		// The chain of the classes of the layers of degree r + N + d.
		chainSubspaces := a.Have(
			"the classes of the layers of degree r + N + d are subspaces of the piece modulo H",
			"∀d:num. submodule(«hilbertCoefficients», «quotient», «classes»(r + (N + d)))",
			Derive(func(b *Argument) {
				b.FixAs[Nat]("d")
				b.Show(
					"the layer bound at N + d",
					By(layers.At(b.TermAs[Nat]("N + d"))))
			}))
		chainBounded := a.Have(
			"of dimension at most h(r + N + d) − h(N + d) = e·r",
			"∀d:num. "+
				"    finite_dimensional(«hilbertCoefficients», "+
				"        restrict_module(«quotient», «classes»(r + (N + d)))) ∧ "+
				"    module_dim(«hilbertCoefficients», restrict_module(«quotient», «classes»(r + (N + d)))) ≤ "+
				"    e * r",
			Derive(func(b *Argument) {
				b.FixAs[Nat]("d")
				past, top := b.TermAs[Nat]("N + d"), b.TermAs[Nat]("r + (N + d)")
				guards := b.Have(
					"both degrees are at least N",
					"N ≤ N + d ∧ N ≤ r + (N + d)",
					ByArith())
				b.Show(
					"the Hilbert function grows by e·r from N + d to r + N + d",
					SplitConj(
						Case(
							"the classes are finite-dimensional",
							By(layers.At(past))),
						Case(
							"of dimension at most e·r",
							ByArith(layers.At(past), hilbert[1].At(past), hilbert[1].At(top), guards)),
					))
			}))
		chainIncreasing := a.Have(
			"and they increase with d, the layers increasing",
			"∀d₁ d₂:num. d₁ ≤ d₂ ⇒ «classes»(r + (N + d₁)) ⊆ «classes»(r + (N + d₂))",
			Derive(func(b *Argument) {
				b.FixAs[Nat]("d₁")
				b.FixAs[Nat]("d₂")
				below := b.Assume()
				lower, upper := b.TermAs[Nat]("r + (N + d₁)"), b.TermAs[Nat]("r + (N + d₂)")
				shifted := b.Have(
					"r + N + d₁ ≤ r + N + d₂",
					"r + (N + d₁) ≤ r + (N + d₂)",
					ByArith(below))
				b.Show(
					"the classes of a smaller layer lie among those of a larger",
					By(increasing.At(lower, upper), shifted, set_image.ImageSubset))
			}))
		pieceRingOn := a.Have(
			"the piece is a commutative ring under M's operations",
			"comm_ring_on(restrict_ring(field_ring(M), «piece»))",
			By(pieceRing, comm_ring.SubringRingOn.Read(field.RingOn.Read(M))))
		cosets := a.Have(
			"the members of the piece modulo H are the classes of the members of the piece",
			"left_cosets(M.add, «piece», H) = image(coset_map(M.add, H), «piece»)",
			By(
				HInPiece,
				quotient_group.LeftCosetsImage.Read(
					abelian_group.GroupOn.Read(comm_ring.AddGroupOn.Read(pieceRingOn))).At(
					H)))
		covered := a.Have(
			"every class is the class of a member s of the piece, "+
				"which lies in some layer V(d) inside V(r + N + d)",
			"∀u:set(A). u ∈ «quotient».carrier ⇒ ∃d:num. u ∈ «classes»(r + (N + d))",
			Derive(func(b *Argument) {
				b.FixAs[Set[A]]("u")
				member := b.Assume()
				s, representative := b.ObtainAs[A](
					"u is the class of some s in the piece",
					"∃s:A. s ∈ «piece» ∧ u = coset_map(M.add, H, s)",
					BySets(member, cosets))
				sParts := b.Conjuncts(
					representative,
					"s lies in the piece",
					"u is its class")
				d, sLayer := b.ObtainAs[Nat](
					"s lies in a layer V(d)",
					"∃d:num. s ∈ «affineValues»(d)",
					By(sParts[0], exhausts.At(s)))
				b.Take(d)
				top := b.TermAs[Nat]("r + (N + d)")
				below := b.Have(
					"d ≤ r + N + d",
					"d ≤ r + (N + d)",
					ByArith())
				b.Show(
					"so u is among the classes of the layer of degree r + N + d",
					BySets(sParts[1], sLayer, increasing.At(d, top), below))
			}))
		quotientSpace := a.Have(
			"the piece modulo H is a vector space over the field k",
			"module_on(«hilbertCoefficients», «quotient») ∧ ring_subfield(«hilbertCoefficients», M.inv, k)",
			By(
				subK,
				pieceRing,
				kInPiece,
				ideal,
				residue_points.ResidueModuleOn.Read(M).At(k, piece, H),
				field.SubfieldRingSubfield.Read(M).At(k, k)))
		a.Show(
			"covered by an increasing chain of subspaces of dimension "+
				"at most e·r, the piece modulo H is finite-dimensional",
			By(
				quotientSpace,
				chainSubspaces,
				chainIncreasing,
				chainBounded,
				covered,
				At(
					module_dimension.BoundedChainUnion,
					coefficients,
					quotient,
					inv,
					a.TermAs[Fun[Nat, Set[Set[A]]]]("λd:num. «classes»(r + (N + d))"),
					a.TermAs[Nat]("e * r"))))
	}),
})}

// AffinePieceGradientRank — the Jacobian rank at a point of the affine
// piece: for a point x of the curve over M with x(j) ≠ 0 and a point φ of
// its piece in M over k, the gradients at the point a = φ(x/x(j)) of the
// polynomials vanishing at the ratios x/x(j) span at least n of the n + 1
// coordinates. a is a zero of the equations with a(j) = one; scaled by
// some nonzero c it is a point b of the curve over M
// (projective_curve.PointNormalization), where the rows of the Jacobian
// span n − 1 dimensions. Each row at b is c^(d − 1) times the gradient at a
// of its equation, a form of degree d (homogeneous_polynomial.GradientScaling),
// and Euler's identity puts every row in the kernel of v ↦ Σᵢ b(i)·v(i)
// (homogeneous_polynomial.EulerGradientKernel); the gradient of x(j) − 1, the
// coordinate vector of j (homogeneous_polynomial.VariableMinusOneGradient), is not
// in it, b(j) being the nonzero scale.
var AffinePieceGradientRank = affinePieceGradientRankThm{family.Add(registry.ProofEntry{
	Name: "AffinePieceGradientRank",
	Key:  "prop_1ff7ba1195145f94",
	Reading: "The smoothness clause of the curve is read at one point only, the scaled point b. x " +
		"need only be a point of the curve over M: no generic-field fact is read. The relation x(j) − " +
		"1 vanishes on the piece because the ratio at j is one, and it supplies the n-th dimension.",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). " +
			"∀k:set(A). " +
			"∀n j:num. " +
			"∀E:set((num → num) → A). " +
			"∀x:(num → A). " +
			"∀φ:(A → A).",
		Hypotheses: []string{
			"smooth_projective_equation_curve(M, k, n, E)",
			"x ∈ projective_equation_points(field_ring(M), k, M.carrier, n, E)",
			"j ≤ n",
			"x(j) ≠ M.zero",
			"φ ∈ algebra_points(restrict_ring(field_ring(M), «piece»), field_ring(M), k, λa:A. a)",
		},
		Conclusion: "n ≤ " +
			"module_dim(field_ring(M), " +
			"    restrict_module(«vectors», module_span(field_ring(M), «vectors», «gradients»)))",
		Abbrev: Abbrev{
			{Name: "rows", Text: "λy:(num → A). {«gradient»(y, P) | P:((num → num) → A) | P ∈ E}"},
		},
	}, func(
		a *Argument,
		M field.FieldFact[on.M],
		k *Expr[Set[A]],
		n, j *Expr[Nat],
		E *Expr[Set[Fun[Fun[Nat, Nat], A]]],
		x *Arrow[Nat, A],
		φ *Arrow[A, A],
		h Fact,
	) {
		p := a.Conjuncts(
			h,
			"the equations are a smooth projective curve over k",
			"x is a point of the curve over M",
			"j indexes a coordinate",
			"the j-th coordinate is not zero",
			"φ is a point of the piece in M over k")
		curve, point, jIndex, nonzero, located := p[0], p[1], p[2], p[3], p[4]
		subfieldk := projective_curve.CurveConstantsSubfield.Read(curve)
		forms := projective_curve.CurveEquationsForms.Read(curve)
		smooth := projective_curve.CurveJacobianRank.Read(curve)
		coordinates := a.Conjuncts(
			a.Unfolded(point, projective_curve.ProjectiveEquationPointsDef),
			"the coordinates lie in M",
			"the coordinates past n are zero",
			"the first nonzero coordinate is one",
			"the equations vanish at x")
		pointParts := a.Conjuncts(
			a.Unfolded(located, algebra_points.AlgebraPointsDef),
			"φ is a ring map from the piece to M",
			"φ fixes k",
			"φ is zero off the piece")
		hom, fixes, offPiece := pointParts[0], pointParts[1], pointParts[2]
		pieceFacts := a.Conjuncts(
			GroupPremises(
				subfieldk,
				coordinates[0],
				jIndex,
				nonzero,
				Read(AffinePieceDegreeFiltration, M).At(k, n, j, x)),
			"the piece is a subring of M",
			"it holds k",
			"its layers increase with the degree",
			"it is the union of its layers")
		subringPiece, kInPiece := pieceFacts[0], pieceFacts[1]
		fieldRing := a.TermAs[module_record.RingOps[A]]("field_ring(M)")
		carrier := a.TermAs[Set[A]]("M.carrier")
		coefficients := a.TermAs[module_record.RingOps[A]]("«hilbertCoefficients»")
		piece := a.TermAs[Set[A]]("«piece»")
		pieceRing := a.TermAs[module_record.RingOps[A]]("restrict_ring(field_ring(M), «piece»)")
		identity := a.TermAs[Fun[A, A]]("λa:A. a")
		ratios := a.TermAs[Fun[Nat, A]]("λi:num. x(i) * M.inv(x(j))")
		φPoint := a.TermAs[Fun[Nat, A]]("«φPoint»")
		indices := a.TermAs[Set[Nat]]("{i:num | i ≤ n}")
		vectors := a.TermAs[module_record.ModuleOps[A, Fun[Nat, A]]]("«vectors»")
		xj := a.TermAs[A]("x(j)")
		inverse := a.TermAs[A]("M.inv(x(j))")
		ringM := field.RingOn.Read(M)
		coordinatesInM := coordinates[0]
		xjIn := a.Have(
			"x(j) and its inverse lie in M",
			"x(j) ∈ M.carrier ∧ M.inv(x(j)) ∈ M.carrier",
			BySets(coordinatesInM, jIndex, field.InvIn.Read(M)))
		ratiosInM := a.Have(
			"and so do the ratios",
			"∀i:num. i ≤ n ⇒ x(i) * M.inv(x(j)) ∈ M.carrier",
			BySets(coordinatesInM, xjIn, comm_ring.MulIn.Read(ringM)))
		inclusion := a.Have(
			"k includes into M as a ring map",
			"ring_homomorphism(«hilbertCoefficients», field_ring(M), λa:A. a)",
			By(
				subfieldk,
				field.SubfieldSubring.Read(M).At(k),
				ring_homomorphism.SubringInclusionHom.Read(ringM).At(k)))
		coefficientsRing := ring_homomorphism.Source.Read(inclusion)

		// The point a = φ(x/x(j)) is a zero of the equations, with a(j) = one.
		vanishAtRatios := a.Have(
			"the equations vanish at the ratios, a form at x/x(j) being a power of 1/x(j) times its value at x",
			Statement{
				Binders:    "∀P:((num → num) → A).",
				Hypotheses: []string{"P ∈ E"},
				Conclusion: "polynomial_algebra_eval(«hilbertCoefficients», " +
					"    field_ring(M), " +
					"    (λa:A. a), " +
					"    (λi:num. x(i) * M.inv(x(j))), " +
					"    P) = " +
					"M.zero",
			},
			Derive(func(b *Argument) {
				P := b.FixAs[Fun[Fun[Nat, Nat], A]]("P")
				PIn := b.Assume()
				d, form := b.UnpackAs[Nat](forms.At(b.MemberOf[on.Any](P, PIn)), "d")
				b.Show(
					"P vanishes at x, so at the ratios",
					By(
						form,
						inclusion,
						coordinatesInM,
						xjIn,
						coordinates[3].At(P),
						PIn,
						homogeneous_polynomial.FormZeroScaling.At(coefficients, fieldRing, identity, n, d, x, inverse, P)))
			}))
		inPolynomials := a.Have(
			"each equation is a polynomial over k",
			"∀P:((num → num) → A). P ∈ E ⇒ P ∈ polynomial_algebra(«hilbertCoefficients», {i:num | i ≤ n})",
			Derive(func(b *Argument) {
				P := b.FixAs[Fun[Fun[Nat, Nat], A]]("P")
				PIn := b.Assume()
				_, form := b.UnpackAs[Nat](forms.At(b.MemberOf[on.Any](P, PIn)), "d")
				b.Show(
					"a form is a polynomial",
					By(homogeneous_polynomial.FormPolynomial.Read(form)))
			}))
		kInPiecePointwise := a.Have(
			"each member of k lies in the piece",
			"∀c:A. c ∈ k ⇒ c ∈ «piece»",
			BySets(kInPiece))
		inclusionPiece := a.Have(
			"k includes into the piece as a ring map",
			"ring_homomorphism(«hilbertCoefficients», restrict_ring(field_ring(M), «piece»), λa:A. a)",
			By(inclusion, subringPiece, kInPiecePointwise, ring_homomorphism.RingHomCorestrict))
		ratiosInPiece := a.Have(
			"each ratio is the value of its variable, so lies in the piece",
			"∀i:num. i ≤ n ⇒ x(i) * M.inv(x(j)) ∈ «piece»",
			Derive(func(b *Argument) {
				i := b.FixAs[Nat]("i")
				iIndex := b.Assume()
				variable := b.Have(
					"the variable is a polynomial",
					"polynomial_algebra_var(«hilbertCoefficients», i) ∈ "+
						"polynomial_algebra(«hilbertCoefficients», {i:num | i ≤ n})",
					By(
						coefficientsRing,
						iIndex,
						polynomial_algebra.PolynomialAlgebraVarIn.At(coefficients, indices, i)))
				value := b.Have(
					"which evaluates to the ratio",
					"polynomial_algebra_eval(«hilbertCoefficients», "+
						"    field_ring(M), "+
						"    (λa:A. a), "+
						"    (λi:num. x(i) * M.inv(x(j))), "+
						"    polynomial_algebra_var(«hilbertCoefficients», i)) = "+
						"x(i) * M.inv(x(j))",
					By(
						inclusion,
						ratiosInM.At(i),
						iIndex,
						polynomial_algebra_evaluation.PolynomialAlgebraEvalVar.At(
							coefficients, fieldRing, identity, ratios, i)))
				b.Show(
					"so the ratio lies in the piece",
					BySets(variable, value))
			}))
		sameEvaluation := a.Have(
			"evaluation reads only the operations of its target, which the piece shares with M",
			"polynomial_algebra_eval(«hilbertCoefficients», "+
				"    restrict_ring(field_ring(M), «piece»), "+
				"    (λa:A. a), "+
				"    (λi:num. x(i) * M.inv(x(j)))) = "+
				"polynomial_algebra_eval(«hilbertCoefficients», "+
				"    field_ring(M), "+
				"    (λa:A. a), "+
				"    (λi:num. x(i) * M.inv(x(j))))",
			Funext(),
			a.ForEach(func(P *Expr[Fun[Fun[Nat, Nat], A]]) Action {
				return Cite(polynomial_algebra_evaluation.PolynomialAlgebraEvalRestrictTarget,
					coefficients, fieldRing, piece, identity, ratios, P)
			}))
		natural := a.Have(
			"φ commutes with evaluation, fixing the coefficients",
			Statement{
				Binders:    "∀P:((num → num) → A).",
				Hypotheses: []string{"P ∈ polynomial_algebra(«hilbertCoefficients», {i:num | i ≤ n})"},
				Conclusion: "φ(polynomial_algebra_eval(«hilbertCoefficients», " +
					"        field_ring(M), " +
					"        (λa:A. a), " +
					"        (λi:num. x(i) * M.inv(x(j))), " +
					"        P)) = " +
					"polynomial_algebra_eval(«hilbertCoefficients», field_ring(M), (λa:A. a), «φPoint», P)",
			},
			By(
				inclusionPiece,
				hom,
				inclusion,
				fixes,
				ratiosInPiece,
				sameEvaluation,
				At(
					polynomial_algebra_evaluation.PolynomialAlgebraEvalNatural,
					coefficients,
					pieceRing,
					fieldRing,
					identity,
					φ,
					identity,
					indices,
					ratios)))
		vanishAtPoint := a.Have(
			"so the equations vanish at the point, φ carrying zero to zero",
			Statement{
				Binders:    "∀P:((num → num) → A).",
				Hypotheses: []string{"P ∈ E"},
				Conclusion: "polynomial_algebra_eval(«hilbertCoefficients», " +
					"    field_ring(M), " +
					"    (λa:A. a), " +
					"    «φPoint», " +
					"    P) = " +
					"M.zero",
			},
			By(inPolynomials, vanishAtRatios, natural, hom, ring_homomorphism.MapZero.Read(hom)))
		values := a.Have(
			"φ takes its values in M",
			"∀y:A. φ(y) ∈ M.carrier",
			Derive(func(b *Argument) {
				y := b.FixAs[A]("y")
				b.Cases(b.TermAs[Bool]("y ∈ «piece»"))
				b.When(
					"on the piece φ is a ring map into M",
					func(c *Argument, inPiece Fact) {
						c.Show(
							"so φ(y) lies in M",
							By(inPiece, ring_homomorphism.MapIn.Read(hom).AsFact().At(y)))
					})
				b.Otherwise(
					"off the piece φ is zero",
					func(c *Argument, offY Fact) {
						c.Show(
							"which lies in M",
							By(offY, offPiece.At(y), comm_ring.ZeroIn.Read(ringM)))
					})
			}))
		pointInM := a.Have(
			"the point lies in M",
			"∀i:num. i ≤ n ⇒ «φPoint»(i) ∈ M.carrier",
			By(values))
		pointOne := a.Have(
			"its j-th coordinate is one, φ keeping the one",
			"«φPoint»(j) = M.one",
			By(
				xjIn,
				nonzero,
				field.MulRightInverseOn.Read(M).AsFact().At(xj),
				ring_homomorphism.MapOne.Read(hom)))
		pastN := a.Have(
			"and its coordinates past n are zero, φ keeping the zero",
			"∀l:num. n < l ⇒ «φPoint»(l) = M.zero",
			By(
				coordinates[1],
				xjIn,
				comm_ring.MulLeftZeroOn.Read(ringM).AsFact().At(inverse),
				ring_homomorphism.MapZero.Read(hom)))

		// Scaled by some nonzero c, a is a point b of the curve.
		scale, scaling := a.ObtainAs[A](
			"some nonzero c in M scales the point onto the curve over M",
			"∃c:A. "+
				"    c ∈ M.carrier ∧ "+
				"    c ≠ M.zero ∧ "+
				"    (λi:num. «φPoint»(i) * c) ∈ projective_equation_points(field_ring(M), k, M.carrier, n, E)",
			By(
				subfieldk,
				field.CarrierSubfield.Read(M),
				forms,
				pointInM,
				pastN,
				jIndex,
				pointOne,
				field.OneNotZeroOn.Read(M),
				vanishAtPoint,
				projective_curve.PointNormalization.Read(M).At(k, carrier, n, j, E, φPoint)))
		scaleParts := a.Conjuncts(
			scaling,
			"c lies in M",
			"c is not zero",
			"the point scaled by c lies on the curve over M")
		scaleIn := scaleParts[0]
		scaled, scaledDef := a.LetAs[Fun[Nat, A]]("b", "λi:num. «φPoint»(i) * c")
		onCurve := scaleParts[2]
		scaledAt := a.Have(
			"b scales each coordinate of the point by c",
			"∀i:num. b(i) = «φPoint»(i) * c",
			By(Normalized, scaledDef))
		scaledInM := a.Have(
			"the scaled point b lies in M",
			"∀i:num. b(i) ∈ M.carrier",
			scaledDef.Rw(),
			By(values, scaleIn, comm_ring.MulIn.Read(ringM)))
		scaledVanish := a.Have(
			"the equations vanish at b",
			Statement{
				Binders:    "∀P:((num → num) → A).",
				Hypotheses: []string{"P ∈ E"},
				Conclusion: "polynomial_algebra_eval(«hilbertCoefficients», field_ring(M), (λa:A. a), b, P) = " +
					"M.zero",
			},
			By(onCurve, At(projective_curve.PointEquationsVanish, fieldRing, k, carrier, n, E, scaled)))
		smoothAtB := a.Have(
			"the rows of the Jacobian at b span n − 1 dimensions",
			"module_dim(field_ring(M), "+
				"    restrict_module(«vectors», module_span(field_ring(M), «vectors», «rows»(b)))) + "+
				"1 = "+
				"n",
			By(onCurve, smooth.At(scaled)))

		// The rows at b lie in the span V of the gradients at the point.
		vectorsModule := a.Have(
			"the coordinate vectors form a module over M",
			"module_on(field_ring(M), «vectors»)",
			By(ringM, free_module.FreeModuleOn))
		gradientsIn := a.Have(
			"the gradients at the point are coordinate vectors",
			"«gradients» ⊆ «vectors».carrier",
			Simp(Fwd(set_basic.SubsetDef)),
			Derive(func(b *Argument) {
				b.FixAs[Fun[Nat, A]]("v")
				vIn := b.Assume()
				R, isGradient := b.UnpackAs[Fun[Fun[Nat, Nat], A]](vIn, "R")
				b.Show(
					"the gradient of R",
					By(
						isGradient,
						subfieldk,
						pointInM,
						homogeneous_polynomial.GradientCoordinateVector.Read(M).At(k, n, R, φPoint)))
			}))
		gradientsSpan, gradientsSpanDef := a.LetAs[Set[Fun[Nat, A]]](
			"V", "module_span(field_ring(M), «vectors», «gradients»)")
		spanSubmodule := a.Have(
			"they span a subspace V",
			"submodule(field_ring(M), «vectors», V)",
			By(gradientsSpanDef, vectorsModule, gradientsIn, submodule.SpanSubmodule))
		rowsInSpan := a.Have(
			"each row at b is a power of c times the gradient of its equation at the point, so lies in V",
			"∀P:((num → num) → A). P ∈ E ⇒ «gradient»(b, P) ∈ V",
			Derive(func(b *Argument) {
				P := b.FixAs[Fun[Fun[Nat, Nat], A]]("P")
				PIn := b.Assume()
				d, form := b.UnpackAs[Nat](forms.At(b.MemberOf[on.Any](P, PIn)), "d")
				lowered := b.TermAs[Nat]("d - 1")
				power := b.TermAs[A]("monoid_pow(M.mul, M.one, c, d - 1)")
				powerIn := comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(ringM)).AsFact().At(scale, lowered)
				rowScaled := b.Have(
					"the row is c^(d − 1) times the gradient of P at the point",
					"«gradient»(b, P) = fun_smul(monoid_pow(M.mul, M.one, c, d - 1), «gradient»(«φPoint», P))",
					By(
						scaledDef,
						subfieldk,
						form,
						pointInM,
						scaleIn,
						homogeneous_polynomial.GradientScaling.Read(M).AsFact().At(k, n, d, P, φPoint, scale)))
				gradient := b.Have(
					"the gradient of P at the point is among the gradients, P vanishing at the ratios",
					"«gradient»(«φPoint», P) ∈ «gradients»",
					BySets(GroupPremises(PIn, inPolynomials.At(P)), GroupPremises(PIn, vanishAtRatios.At(P))))
				b.Show(
					"so the row, a multiple of a member of V, lies in V",
					By(
						rowScaled,
						b.Have(
							"the gradient lies in V",
							"«gradient»(«φPoint», P) ∈ V",
							BySets(
								gradientsSpanDef,
								gradient,
								submodule.SubsetSpan.At(fieldRing, vectors, a.TermAs[Set[Fun[Nat, A]]]("«gradients»")))),
						spanSubmodule,
						scaleIn,
						powerIn,
						submodule.SubmoduleSmul.At(
							fieldRing, vectors, gradientsSpan, power, b.TermAs[Fun[Nat, A]]("«gradient»(«φPoint», P)"))))
			}))
		rowsSpan, rowsSpanDef := a.LetAs[Set[Fun[Nat, A]]](
			"W", "module_span(field_ring(M), «vectors», «rows»(b))")
		rowsInV := a.Have(
			"the rows at b lie in V",
			"«rows»(b) ⊆ V",
			Simp(Fwd(set_basic.SubsetDef)),
			Derive(func(b *Argument) {
				b.FixAs[Fun[Nat, A]]("v")
				vIn := b.Assume()
				P, isRow := b.UnpackAs[Fun[Fun[Nat, Nat], A]](vIn, "P")
				b.Show(
					"the row of P",
					By(isRow, rowsInSpan.At(P)))
			}))
		rowsSpanIn := a.Have(
			"so the span W of the rows at b lies in V",
			"W ⊆ V",
			By(rowsInV, rowsSpanDef, spanSubmodule, submodule.SpanLeast))

		// The relation x(j) − 1 has the coordinate vector of j as its gradient.
		variableJ := a.TermAs[Fun[Fun[Nat, Nat], A]]("polynomial_algebra_var(«hilbertCoefficients», j)")
		constantOne := a.TermAs[Fun[Fun[Nat, Nat], A]](
			"polynomial_algebra_const(«hilbertCoefficients», M.one)")
		_, relationDef := a.LetAs[Fun[Fun[Nat, Nat], A]](
			"Q",
			"«polynomials».sub(polynomial_algebra_var(«hilbertCoefficients», j), "+
				"    polynomial_algebra_const(«hilbertCoefficients», M.one))")
		one := a.TermAs[A]("M.one")
		oneInK := a.Have(
			"one lies in k",
			"M.one ∈ k",
			By(subfieldk, field.SubfieldOne))
		polynomialsRing := a.Have(
			"the polynomials over k are a commutative ring",
			"comm_ring_on(«polynomials»)",
			By(coefficientsRing, polynomial_algebra.PolynomialAlgebraCommRingOn))
		constants := a.Have(
			"the constants are polynomials",
			"ring_homomorphism(«hilbertCoefficients», "+
				"    «polynomials», "+
				"    polynomial_algebra_const(«hilbertCoefficients»))",
			By(coefficientsRing, polynomial_algebra.PolynomialAlgebraConstHom))
		generatorsIn := a.Have(
			"x(j) and one are polynomials over k",
			"polynomial_algebra_var(«hilbertCoefficients», j) ∈ "+
				"polynomial_algebra(«hilbertCoefficients», {i:num | i ≤ n}) ∧ "+
				"polynomial_algebra_const(«hilbertCoefficients», M.one) ∈ "+
				"polynomial_algebra(«hilbertCoefficients», {i:num | i ≤ n})",
			By(
				coefficientsRing,
				jIndex,
				oneInK,
				polynomial_algebra.PolynomialAlgebraVarIn.At(coefficients, indices, j),
				ring_homomorphism.MapIn.Read(constants).AsFact().At(one),
				polynomial_algebra.PolynomialAlgebraRingDef))
		relationIn := a.Have(
			"so is x(j) − 1",
			"Q ∈ polynomial_algebra(«hilbertCoefficients», {i:num | i ≤ n})",
			By(
				relationDef,
				generatorsIn,
				comm_ring.SubIn.Read(polynomialsRing).AsFact().At(variableJ, constantOne),
				polynomial_algebra.PolynomialAlgebraRingDef))
		evaluationAtRatios := a.Have(
			"evaluation at the ratios is a ring map",
			"ring_homomorphism(«polynomials», "+
				"    field_ring(M), "+
				"    polynomial_algebra_eval(«hilbertCoefficients», "+
				"        field_ring(M), "+
				"        (λa:A. a), "+
				"        (λi:num. x(i) * M.inv(x(j)))))",
			By(subfieldk, ratiosInM, Read(homogeneous_polynomial.EvaluationRingHom, M).At(k, n, ratios)))
		relationVanishes := a.Have(
			"x(j) − 1 vanishes at the ratios, the ratio at j being one",
			"polynomial_algebra_eval(«hilbertCoefficients», "+
				"    field_ring(M), "+
				"    (λa:A. a), "+
				"    (λi:num. x(i) * M.inv(x(j))), "+
				"    Q) = "+
				"M.zero",
			ByArith(
				M,
				a.Have(
					"its value is the ratio at j minus one",
					"polynomial_algebra_eval(«hilbertCoefficients», "+
						"    field_ring(M), "+
						"    (λa:A. a), "+
						"    (λi:num. x(i) * M.inv(x(j))), "+
						"    Q) = "+
						"polynomial_algebra_eval(«hilbertCoefficients», "+
						"    field_ring(M), "+
						"    (λa:A. a), "+
						"    (λi:num. x(i) * M.inv(x(j))), "+
						"    polynomial_algebra_var(«hilbertCoefficients», j)) - "+
						"polynomial_algebra_eval(«hilbertCoefficients», "+
						"    field_ring(M), "+
						"    (λa:A. a), "+
						"    (λi:num. x(i) * M.inv(x(j))), "+
						"    polynomial_algebra_const(«hilbertCoefficients», M.one))",
					By(
						Normalized,
						relationDef,
						generatorsIn,
						ring_homomorphism.MapSub.Read(evaluationAtRatios).AsFact().At(variableJ, constantOne),
						polynomial_algebra.PolynomialAlgebraRingDef)),
				a.Have(
					"the variable evaluates to the ratio and the constant to one",
					"polynomial_algebra_eval(«hilbertCoefficients», "+
						"    field_ring(M), "+
						"    (λa:A. a), "+
						"    (λi:num. x(i) * M.inv(x(j))), "+
						"    polynomial_algebra_var(«hilbertCoefficients», j)) = "+
						"x(j) * M.inv(x(j)) ∧ "+
						"polynomial_algebra_eval(«hilbertCoefficients», "+
						"    field_ring(M), "+
						"    (λa:A. a), "+
						"    (λi:num. x(i) * M.inv(x(j))), "+
						"    polynomial_algebra_const(«hilbertCoefficients», M.one)) = "+
						"M.one",
					By(
						inclusion,
						ratiosInM.At(j),
						jIndex,
						oneInK,
						polynomial_algebra_evaluation.PolynomialAlgebraEvalVar.At(
							coefficients, fieldRing, identity, ratios, j),
						polynomial_algebra_evaluation.PolynomialAlgebraEvalConst.At(
							coefficients, fieldRing, identity, ratios, one))),
				xjIn,
				nonzero,
				field.MulRightInverseOn.Read(M).AsFact().At(xj)))
		coordinateJ := a.Have(
			"its gradient at the point is the coordinate vector of j",
			"«gradient»(«φPoint», Q) = delta_at(j)",
			By(
				relationDef,
				subfieldk,
				jIndex,
				pointInM,
				homogeneous_polynomial.VariableMinusOneGradient.Read(M).At(k, n, j, φPoint),
				polynomial_algebra.PolynomialAlgebraRingDef))
		gradientsSet := a.TermAs[Set[Fun[Nat, A]]]("«gradients»")
		relationGradientIn := a.Have(
			"the gradient of x(j) − 1 is among the gradients, x(j) − 1 vanishing at the ratios",
			"«gradient»(«φPoint», Q) ∈ «gradients»",
			BySets(relationIn, relationVanishes))
		coordinateJInV := a.Have(
			"so the coordinate vector of j lies in V",
			"delta_at(j) ∈ V",
			By(
				coordinateJ,
				a.Have(
					"the gradient of x(j) − 1 lies in V",
					"«gradient»(«φPoint», Q) ∈ V",
					BySets(
						gradientsSpanDef,
						relationGradientIn,
						submodule.SubsetSpan.At(fieldRing, vectors, gradientsSet)))))

		// Euler's identity: every row at b lies in the kernel of v ↦ Σᵢ v(i)·b(i).
		regular := a.TermAs[module_record.ModuleOps[A, A]]("regular_module(field_ring(M))")
		regularModule := module.RegularModuleOn.Read(ringM)
		eulerLinear := a.Have(
			"v ↦ Σᵢ v(i)·b(i) is a linear form on the coordinate vectors",
			"module_homomorphism(field_ring(M), "+
				"    «vectors», "+
				"    regular_module(field_ring(M)), "+
				"    free_lift(M.zero, M.add, M.zero, M.mul, b))",
			By(
				scaledInM,
				regularModule,
				free_module.FreeLiftHom.At(fieldRing, regular, indices, scaled),
				module_record.RegularModuleDef))
		eulerAtJ := a.Have(
			"its value at the coordinate vector of j is b(j)",
			"free_lift(M.zero, M.add, M.zero, M.mul, b, delta_at(j)) = b(j)",
			By(
				scaledInM,
				jIndex,
				regularModule,
				free_module.FreeLiftDelta.At(fieldRing, regular, indices, scaled, j),
				module_record.RegularModuleDef))
		eulerNonzero := a.Have(
			"which is c, not zero",
			"free_lift(M.zero, M.add, M.zero, M.mul, b, delta_at(j)) ≠ M.zero",
			By(
				scaledAt.At(j),
				eulerAtJ,
				pointOne,
				scaleParts[1],
				scaleIn,
				comm_monoid.LeftIdentityOn.Read(comm_ring.MulMonoidOn.Read(ringM)).AsFact().At(scale)))
		eulerKills := a.Have(
			"Euler's identity puts every row at b in its kernel",
			Statement{
				Binders:    "∀P:((num → num) → A).",
				Hypotheses: []string{"P ∈ E"},
				Conclusion: "free_lift(M.zero, M.add, M.zero, M.mul, b, «gradient»(b, P)) = M.zero",
			},
			Derive(func(b *Argument) {
				P := b.FixAs[Fun[Fun[Nat, Nat], A]]("P")
				PIn := b.Assume()
				d, form := b.UnpackAs[Nat](forms.At(b.MemberOf[on.Any](P, PIn)), "d")
				b.Show(
					"P is a form vanishing at b, a point of M",
					By(
						subfieldk,
						form,
						scaledInM,
						scaledVanish.At(P),
						PIn,
						homogeneous_polynomial.EulerGradientKernel.Read(M).At(k, n, d, P, scaled)))
			}))
		rowsIn := a.Have(
			"the rows at b are coordinate vectors",
			"«rows»(b) ⊆ «vectors».carrier",
			Simp(Fwd(set_basic.SubsetDef)),
			Derive(func(b *Argument) {
				b.FixAs[Fun[Nat, A]]("v")
				vIn := b.Assume()
				P, isRow := b.UnpackAs[Fun[Fun[Nat, Nat], A]](vIn, "P")
				b.Show(
					"the row of P is the gradient of P at b",
					By(
						isRow,
						inPolynomials.At(P),
						subfieldk,
						scaledInM,
						homogeneous_polynomial.GradientCoordinateVector.Read(M).At(k, n, P, scaled)))
			}))
		rowsSubmodule := a.Have(
			"W is a subspace",
			"submodule(field_ring(M), «vectors», W)",
			By(rowsSpanDef, vectorsModule, rowsIn, submodule.SpanSubmodule))
		kernelSubmodule := a.Have(
			"the kernel of the form is a subspace",
			"submodule(field_ring(M), "+
				"    «vectors», "+
				"    {v:(num → A) | "+
				"        v ∈ «vectors».carrier ∧ free_lift(M.zero, M.add, M.zero, M.mul, b)(v) = M.zero})",
			By(
				module_homomorphism.KernelSubmodule.Read(eulerLinear),
				group_homomorphism.GroupKernelDef,
				module_record.RegularModuleDef))
		rowsInKernel := a.Have(
			"the rows at b lie in the kernel",
			"«rows»(b) ⊆ "+
				"{v:(num → A) | v ∈ «vectors».carrier ∧ free_lift(M.zero, M.add, M.zero, M.mul, b)(v) = M.zero}",
			Simp(Fwd(set_basic.SubsetDef)),
			Derive(func(b *Argument) {
				b.FixAs[Fun[Nat, A]]("v")
				vIn := b.Assume()
				P, isRow := b.UnpackAs[Fun[Fun[Nat, Nat], A]](vIn, "P")
				rowParts := b.Conjuncts(
					isRow,
					"P is an equation",
					"v is its row at b")
				b.Do(rowParts[1].Rw())
				rowVector := b.Have(
					"the row is a coordinate vector",
					"«gradient»(b, P) ∈ «vectors».carrier",
					By(
						rowParts[0],
						inPolynomials.At(P),
						subfieldk,
						scaledInM,
						homogeneous_polynomial.GradientCoordinateVector.Read(M).At(k, n, P, scaled)))
				b.Show(
					"the row is a coordinate vector the form kills",
					BySets(rowVector, rowParts[0], eulerKills.At(P)))
			}))
		kernel := a.Have(
			"it holds the rows at b, so holding W",
			"W ⊆ "+
				"{v:(num → A) | v ∈ «vectors».carrier ∧ free_lift(M.zero, M.add, M.zero, M.mul, b)(v) = M.zero}",
			rowsSpanDef.Rw(),
			By(kernelSubmodule, rowsInKernel, submodule.SpanLeast))
		vanishes := a.Have(
			"so the form vanishes on W",
			"∀w:(num → A). w ∈ W ⇒ free_lift(M.zero, M.add, M.zero, M.mul, b, w) = M.zero",
			BySets(kernel))
		finiteVectors := a.Have(
			"the coordinate vectors are finite-dimensional, those of 0, …, n a basis",
			"finite_dimensional(field_ring(M), «vectors»)",
			By(
				vectorsModule,
				field.FieldRingSubfield.Read(M),
				free_module.DeltaAtBasis.Read(ringM).AsFact().At(indices),
				finite_set.FiniteImage.At(
					a.TermAs[Fun[Nat, Fun[Nat, A]]]("delta_at(field_ring(M).zero, field_ring(M).one)"), indices),
				num_segment.FiniteBelow.At(n),
				module_dimension.FiniteBasisDim))
		outside := a.Have(
			"the coordinate vector of j lies outside W, the form vanishing on W but not there",
			"delta_at(j) ∉ W",
			By(vanishes, eulerNonzero))
		dimension := a.Have(
			"so W, a proper subspace of V, has dimension less than V",
			"module_dim(field_ring(M), restrict_module(«vectors», W)) + 1 ≤ "+
				"module_dim(field_ring(M), restrict_module(«vectors», V))",
			By(
				field.FieldRingSubfield.Read(M),
				vectorsModule,
				finiteVectors,
				rowsSubmodule,
				spanSubmodule,
				rowsSpanIn,
				coordinateJInV,
				outside,
				module_dimension.ProperSubmoduleDimLess.At(
					fieldRing,
					a.TermAs[Fun[A, A]]("M.inv"),
					vectors,
					rowsSpan,
					gradientsSpan,
					a.TermAs[Fun[Nat, A]]("delta_at(j)")),
				field.FieldRingDef))
		a.Show(
			"so V has dimension at least n",
			ByArith(smoothAtB, dimension))
	}),
})}

// AffinePieceCotangentLine — the Jacobian criterion's cotangent half: at a
// closed point of the affine piece at a point x of a smooth projective
// equation curve over M, seen through a point φ of the piece in M with
// kernel m, the cotangent space m/m² is spanned by one nonzero member u of
// m: every member of m is a multiple of u plus a member of m². The piece is
// generated over the finite k by the ratios x/x(j), the residue field S/m is
// finite over k, and the gradients at the point of the relations among the
// ratios span at least n of the n + 1 coordinates (AffinePieceGradientRank),
// which is what the general bound for a ring generated by finitely many
// elements needs.
var AffinePieceCotangentLine = affinePieceCotangentLineThm{family.Add(registry.ProofEntry{
	Name: "AffinePieceCotangentLine",
	Key:  "prop_c0c123361023f6dd",
	Reading: "The Jacobian rank at the curve's points over M is load-bearing: the cusp Y²Z " +
		"= X³ has rank 0 at (0:0:1), where m/m² has dimension two. φ is what makes the rank " +
		"readable, carrying m to a point of the curve over M; finiteness of k makes the residue " +
		"field φ(S) separable over k, without which the gradient need not see m/m² (Y^p − t " +
		"over 𝔽_p(t)). m ≠ {M.zero} is what lets u be nonzero. m is not asked to be maximal: as " +
		"the kernel of φ it is an ideal, with the residue field φ(S) of finite dimension over k.",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). " +
			"∀k:set(A). " +
			"∀n j:num. " +
			"∀E:set((num → num) → A). " +
			"∀x:(num → A). " +
			"∀m:set(A). " +
			"∀φ:(A → A).",
		Hypotheses: []string{
			"smooth_projective_equation_curve(M, k, n, E)",
			"x ∈ projective_equation_points(field_ring(M), k, M.carrier, n, E)",
			"j ≤ n",
			"x(j) ≠ M.zero",
			"m ≠ {M.zero}",
			"φ ∈ algebra_points(restrict_ring(field_ring(M), «piece»), field_ring(M), k, λa:A. a)",
			"ring_kernel(M.zero, «piece», φ) = m",
		},
		Conclusion: "∃u:A. " +
			"    u ∈ m ∧ " +
			"    u ≠ M.zero ∧ " +
			"    m ⊆ " +
			"    set_mul(M.add, " +
			"        ideal_span(restrict_ring(field_ring(M), «piece»), {u}), " +
			"        ideal_mul(restrict_ring(field_ring(M), «piece»), m, m))",
	}, func(
		a *Argument,
		M field.FieldFact[on.M],
		k *Expr[Set[A]],
		n, j *Expr[Nat],
		E *Expr[Set[Fun[Fun[Nat, Nat], A]]],
		x *Arrow[Nat, A],
		m *Expr[Set[A]],
		φ *Arrow[A, A],
		h Fact,
	) {
		p := a.Conjuncts(
			h,
			"the equations are a smooth projective curve over k",
			"x is a point of the curve over M",
			"j indexes a coordinate",
			"the j-th coordinate is not zero",
			"m is not zero",
			"φ is a point of the piece in M over k",
			"whose kernel is m")
		curve, point, jIndex, nonzero, nonzeroIdeal, located, kernel :=
			p[0], p[1], p[2], p[3], p[4], p[5], p[6]
		ratios := a.TermAs[Fun[Nat, A]]("λi:num. x(i) * M.inv(x(j))")
		subfieldk, finitek :=
			projective_curve.CurveConstantsSubfield.Read(curve),
			projective_curve.CurveConstantsFinite.Read(curve)
		pointParts := a.Conjuncts(
			a.Unfolded(located, algebra_points.AlgebraPointsDef),
			"φ is a ring map from the piece to M",
			"φ fixes k",
			"φ is zero off the piece")
		coordinatesInM := a.Have(
			"the coordinates lie in M",
			"∀i:num. i ≤ n ⇒ x(i) ∈ M.carrier",
			By(point, projective_curve.PointCoordinatesIn))
		ratiosInM := a.Have(
			"the ratios x(i)/x(j) lie in M",
			"∀i:num. i ≤ n ⇒ x(i) * M.inv(x(j)) ∈ M.carrier",
			BySets(
				coordinatesInM,
				a.Have(
					"x(j) and its inverse lie in M",
					"x(j) ∈ M.carrier ∧ M.inv(x(j)) ∈ M.carrier",
					BySets(coordinatesInM, jIndex, field.InvIn.Read(M))),
				comm_ring.MulIn.Read(field.RingOn.Read(M))))
		idealM := a.Have(
			"m, the kernel of φ, is an ideal of the piece",
			"ring_ideal(restrict_ring(field_ring(M), «piece»), m)",
			kernel.RwRev(),
			By(ring_homomorphism.KernelIdeal.Read(pointParts[0])))
		residues := a.Have(
			"the residue field S/m is finite over k",
			"finite_dimensional(«hilbertCoefficients», "+
				"    quotient_module(restrict_module(regular_module(field_ring(M)), «piece»), m))",
			By(
				curve,
				point,
				jIndex,
				nonzero,
				idealM,
				nonzeroIdeal,
				Read(AffinePieceQuotientsFinite, M).At(k, n, j, E, x, m)))
		rank := a.Have(
			"the gradients at the point of the relations among the ratios span at least n coordinates",
			"n ≤ "+
				"module_dim(field_ring(M), "+
				"    restrict_module(«vectors», module_span(field_ring(M), «vectors», «gradients»)))",
			By(curve, point, jIndex, nonzero, located, Read(AffinePieceGradientRank, M).At(k, n, j, E, x, φ)))
		a.Show(
			"so m/m² is spanned by one nonzero member of m",
			By(
				subfieldk,
				finitek,
				ratiosInM,
				pointParts[0],
				pointParts[1],
				kernel,
				nonzeroIdeal,
				residues,
				rank,
				Read(zariski_cotangent.JacobianCotangentBound, M).At(k, n, ratios, m, φ)))
	}),
})}

// AffinePieceMaximalLocallyPrincipal — the Jacobian criterion at a point: a
// nonzero maximal ideal m of the affine piece at a point x of a smooth
// projective equation curve over M has a nonzero member u that generates
// it near the point, some s of the piece outside m carrying all of m into
// the multiples of u. S/m is finite over the finite field k, so m is the
// kernel of a point of the piece in the closed field M, where the cotangent
// space m/m² is spanned by one nonzero u. S/u·S is finite over k as well, so
// finitely many members of m generate it modulo u·S, and Nakayama's lemma
// gives s, one modulo m, with s·m inside u·S.
var AffinePieceMaximalLocallyPrincipal = affinePieceMaximalLocallyPrincipalThm{family.Add(registry.ProofEntry{
	Name: "AffinePieceMaximalLocallyPrincipal",
	Key:  "prop_385689e14eec04b7",
	Reading: "This is m·S_m = u·S_m, the local ring at the point a discrete valuation ring, written " +
		"without the localization. M algebraically closed is load-bearing: the Jacobian rank is stated " +
		"at the curve's points over M, and a closed point of the piece is seen only through one of " +
		"them. The cusp Y²Z = X³ has rank 0 at (0:0:1), where its maximal ideal needs two generators.",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). " +
			"∀k:set(A). " +
			"∀n j:num. " +
			"∀E:set((num → num) → A). " +
			"∀x:(num → A). " +
			"∀m:set(A).",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"smooth_projective_equation_curve(M, k, n, E)",
			"x ∈ projective_equation_points(field_ring(M), k, M.carrier, n, E)",
			"j ≤ n",
			"x(j) ≠ M.zero",
			"maximal_ideal(restrict_ring(field_ring(M), «piece»), m)",
			"m ≠ {M.zero}",
		},
		Conclusion: "∃u s:A. " +
			"    u ∈ m ∧ u ≠ M.zero ∧ s ∈ «piece» ∧ s ∉ m ∧ (∀z:A. z ∈ m ⇒ ∃h:A. h ∈ «piece» ∧ s * z = u * h)",
	}, func(
		a *Argument,
		M field.FieldFact[on.M],
		k *Expr[Set[A]],
		n, j *Expr[Nat],
		E *Expr[Set[Fun[Fun[Nat, Nat], A]]],
		x *Arrow[Nat, A],
		m *Expr[Set[A]],
		h Fact,
	) {
		p := a.Conjuncts(
			h,
			"M is algebraically closed",
			"the equations are a smooth projective curve over k",
			"x is a point of the curve over M",
			"j indexes a coordinate",
			"the j-th coordinate is not zero",
			"m is a maximal ideal of the piece",
			"m is not zero")
		closed, curve, point, jIndex, nonzero, maximal, nonzeroIdeal :=
			p[0], p[1], p[2], p[3], p[4], p[5], p[6]
		piece := a.TermAs[Set[A]]("«piece»")
		ring := a.TermAs[module_record.RingOps[A]]("restrict_ring(field_ring(M), «piece»)")
		subfieldk := a.Have(
			"k is a subfield of M",
			"subfield(M, k)",
			By(projective_curve.CurveConstantsSubfield.Read(curve)))
		finitek := projective_curve.CurveConstantsFinite.Read(curve)
		coordinatesInM := a.Have(
			"the coordinates lie in M",
			"∀i:num. i ≤ n ⇒ x(i) ∈ M.carrier",
			By(point, projective_curve.PointCoordinatesIn))
		pieceFacts := a.Conjuncts(
			GroupPremises(
				subfieldk,
				coordinatesInM,
				jIndex,
				nonzero,
				Read(AffinePieceDegreeFiltration, M).At(k, n, j, x)),
			"the piece is a subring of M",
			"it holds k",
			"its layers increase with the degree",
			"it is the union of its layers")
		subringM, kInPiece := pieceFacts[0], pieceFacts[1]
		ringS := a.Have(
			"the piece is a commutative ring",
			"comm_ring_on(restrict_ring(field_ring(M), «piece»))",
			By(subringM, comm_ring.SubringRingOn.Read(field.RingOn.Read(M)).At(piece)))
		idealM := a.Have(
			"m is an ideal of the piece",
			"ring_ideal(restrict_ring(field_ring(M), «piece»), m)",
			By(maximal, ring_ideal.MaximalIdealIdeal.At(ring, m)))
		mInPiece := a.Have(
			"m lies in the piece",
			"m ⊆ «piece»",
			By(idealM, ring_ideal.IdealSubset.At(ring, m)))
		residues := a.Have(
			"the residue field S/m is finite over k",
			"finite_dimensional(«hilbertCoefficients», "+
				"    quotient_module(restrict_module(regular_module(field_ring(M)), «piece»), m))",
			By(
				curve,
				point,
				jIndex,
				nonzero,
				idealM,
				nonzeroIdeal,
				Read(AffinePieceQuotientsFinite, M).At(k, n, j, E, x, m)))
		φ, located := a.UnpackAs[Fun[A, A]](
			GroupPremises(
				closed,
				subfieldk,
				finitek,
				subringM,
				kInPiece,
				maximal,
				residues,
				residue_points.ResiduePointExists.Read(M).At(k, piece, m)),
			"φ")
		pointParts := a.Conjuncts(
			located,
			"φ is a point of the piece in M over k",
			"whose kernel is m")
		u, line := a.UnpackAs[A](
			GroupPremises(
				curve,
				point,
				jIndex,
				nonzero,
				nonzeroIdeal,
				pointParts[0],
				pointParts[1],
				Read(AffinePieceCotangentLine, M).At(k, n, j, E, x, m, φ)),
			"u")
		lineParts := a.Conjuncts(
			line,
			"u lies in m",
			"u is not zero",
			"u spans m modulo m²")
		uInM, uNonzero, cotangent := lineParts[0], lineParts[1], lineParts[2]
		singleton := a.TermAs[Set[A]]("{u}")
		multiples := a.TermAs[Set[A]]("ideal_span(restrict_ring(field_ring(M), «piece»), {u})")
		uInPiece := a.Have(
			"u lies in the piece",
			"u ∈ «piece»",
			BySets(uInM, mInPiece))
		singletonIn := a.Have(
			"so {u} lies in the piece and in m",
			"{u} ⊆ «piece» ∧ {u} ⊆ m",
			BySets(uInM, uInPiece))
		multiplesIdeal := a.Have(
			"the multiples of u form an ideal",
			"ring_ideal(restrict_ring(field_ring(M), «piece»), "+
				"    ideal_span(restrict_ring(field_ring(M), «piece»), {u}))",
			By(singletonIn, ring_ideal.SpanIdeal.Read(ringS).At(singleton)))
		multiplesInM := a.Have(
			"inside m, which holds u",
			"ideal_span(restrict_ring(field_ring(M), «piece»), {u}) ⊆ m",
			By(singletonIn, idealM, ring_ideal.SpanLeast.At(ring, singleton, m)))
		multiplesNonzero := a.Have(
			"and not zero, holding the nonzero u",
			"ideal_span(restrict_ring(field_ring(M), «piece»), {u}) ≠ {M.zero}",
			BySets(ring_ideal.SpanContains.At(ring, singleton), uNonzero))
		colength := a.Have(
			"S/u·S is finite over k too",
			"finite_dimensional(«hilbertCoefficients», "+
				"    quotient_module(restrict_module(regular_module(field_ring(M)), «piece»), "+
				"        ideal_span(restrict_ring(field_ring(M), «piece»), {u})))",
			By(
				curve,
				point,
				jIndex,
				nonzero,
				multiplesIdeal,
				multiplesNonzero,
				Read(AffinePieceQuotientsFinite, M).At(k, n, j, E, x, multiples)))
		G, spanned := a.UnpackAs[Set[A]](
			GroupPremises(
				subringM,
				subfieldk,
				kInPiece,
				multiplesIdeal,
				idealM,
				multiplesInM,
				colength,
				Read(ideal_factorization.GeneratedModuloFiniteColength, M).At(piece, k, multiples, m)),
			"G")
		generators := a.Conjuncts(
			spanned,
			"G is finite",
			"G lies in m",
			"G generates m modulo the multiples of u")
		s, carried := a.UnpackAs[A](
			GroupPremises(
				idealM,
				generators[0],
				generators[1],
				multiplesIdeal,
				generators[2],
				cotangent,
				Read(local_ring.Nakayama, ringS).At(m, m, G, multiples)),
			"s")
		sParts := a.Conjuncts(
			carried,
			"s lies in the piece",
			"s is one modulo m",
			"s carries m into the multiples of u")
		sIn, sOne, sCarries := sParts[0], sParts[1], sParts[2]
		pieceInM := a.Have(
			"the piece lies in M",
			"«piece» ⊆ M.carrier",
			By(
				subringM,
				comm_ring.SubringSubset.At(a.TermAs[module_record.RingOps[A]]("field_ring(M)"), piece)))
		sInField := a.Have(
			"s lies in M",
			"s ∈ M.carrier",
			BySets(sIn, pieceInM))
		outside := a.Have(
			"s lies outside m, which does not hold one",
			"s ∉ m",
			Derive(func(b *Argument) {
				sInM := b.SupposeNot()
				difference := b.TermAs[A]("s - M.one")
				restore := b.Have(
					"one is s minus s − one",
					"M.one = s + -(s - M.one)",
					ByArith(M, sInField))
				b.Show(
					"so m would hold one",
					By(
						restore,
						idealM,
						sInM,
						sOne,
						ring_ideal.IdealSub.Read(ringS).At(m, s, difference),
						ring_ideal.MaximalIdealProper.At(ring, m),
						maximal))
			}))
		uMember := a.MemberOf[on.Any](u, uInPiece)
		divides := a.Have(
			"s times a member of m is u times a member of the piece",
			"∀z:A. z ∈ m ⇒ ∃h:A. h ∈ «piece» ∧ s * z = u * h",
			Derive(func(b *Argument) {
				z := b.FixAs[A]("z")
				zIn := b.Assume()
				inMultiples := b.Have(
					"s times z is a multiple of u",
					"s * z ∈ ideal_span(restrict_ring(field_ring(M), «piece»), {u})",
					By(sCarries.At(z), zIn))
				r, form := b.ObtainAs[A](
					"a multiple of u is r times u for some r in the piece",
					"∃r:A. r ∈ «piece» ∧ s * z = r * u",
					BySets(ring_ideal.PrincipalIdealMultiples.Read(ringS).At(uMember), inMultiples))
				parts := b.Conjuncts(
					form,
					"r lies in the piece",
					"s times z is r times u")
				members := b.Have(
					"r, u and z lie in M",
					"r ∈ M.carrier ∧ u ∈ M.carrier ∧ z ∈ M.carrier",
					BySets(parts[0], uInPiece, zIn, mInPiece, pieceInM))
				swapped := b.Have(
					"and r times u is u times r",
					"s * z = u * r",
					ByArith(M, members, sInField, parts[1]))
				b.Take(r)
				b.Show(
					"so r is the member of the piece sought",
					By(parts[0], swapped))
			}))
		a.Take(u)
		a.Take(s)
		a.Show(
			"u and s are the generator and the outside member",
			By(uInM, uNonzero, sIn, outside, divides))
	}),
})}

// AffinePiecesIntegrallyClosed — the Jacobian criterion: on a smooth
// projective equation curve, for a point x of the curve over K whose
// coordinates generate K over k, the ring of the affine piece where the j-th
// coordinate of x is not zero is integrally closed in K. The piece is a
// subring of K with K as its field of fractions; its nonzero ideals have
// finite-dimensional quotients, hence finite height, and its nonzero maximal
// ideals are principal near their points, hence invertible; so every nonzero
// ideal is invertible, and a subring of its field of fractions with that
// property is integrally closed.
var AffinePiecesIntegrallyClosed = affinePiecesIntegrallyClosedThm{family.Add(registry.ProofEntry{
	Name: "AffinePiecesIntegrallyClosed",
	Reading: "The Jacobian rank at every point is load-bearing: the cusp Y²Z " +
		"= X³ has a prime ideal and a linear Hilbert function, rank 0 at (0:0:1), " +
		"and y/x integral over its piece but not in it. x need not be the generic " +
		"point: that the forms vanishing at x are those of the ideal is not read.",
	Key: "prop_5ab994e398569b6c",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k K:set(A). ∀n j:num. ∀E:set((num → num) → A). ∀x:(num → A).",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"smooth_projective_equation_curve(M, k, n, E)",
			"subfield(M, K)",
			"x ∈ projective_equation_points(field_ring(M), k, K, n, E)",
			"field_adjoin(M, k, {x(i) | i:num | i ≤ n}) = K",
			"j ≤ n",
			"x(j) ≠ M.zero",
		},
		Conclusion: "integrally_closed_in(restrict_ring(field_ring(M), «piece»), K)",
	}, func(
		a *Argument,
		M field.FieldFact[on.M],
		k, K *Expr[Set[A]],
		n, j *Expr[Nat],
		E *Expr[Set[Fun[Fun[Nat, Nat], A]]],
		x *Arrow[Nat, A],
		h Fact,
	) {
		p := a.Conjuncts(
			h,
			"M is algebraically closed",
			"the equations are a smooth projective curve over k",
			"K is a subfield of M",
			"x is a point of the curve over K",
			"its coordinates generate K over k",
			"j indexes a coordinate",
			"the j-th coordinate is not zero")
		closed, curve, subfieldK, point, generated, jIndex, nonzero :=
			p[0], p[1], p[2], p[3], p[4], p[5], p[6]
		ops := a.TermAs[FieldOps[A]]("M")
		piece := a.TermAs[Set[A]]("«piece»")
		fieldRing := a.TermAs[module_record.RingOps[A]]("field_ring(M)")
		carrier := a.TermAs[Set[A]]("M.carrier")
		subfieldk := projective_curve.CurveConstantsSubfield.Read(curve)
		coordinatesInK := a.Have(
			"the coordinates lie in K",
			"∀i:num. i ≤ n ⇒ x(i) ∈ K",
			By(point, projective_curve.PointCoordinatesIn))
		normalized := a.Have(
			"some coordinate is one",
			"∃i:num. i ≤ n ∧ x(i) = M.one",
			By(point, projective_curve.PointLeadingOne.At(fieldRing, k, K, n, E, x)))
		KInM := a.Have(
			"K lies in M",
			"K ⊆ M.carrier",
			By(subfieldK, field.SubfieldSubset))
		pointM := a.Have(
			"so x is a point of the curve over M, K lying in M",
			"x ∈ projective_equation_points(field_ring(M), k, M.carrier, n, E)",
			BySets(
				point,
				KInM,
				projective_curve.ProjectiveEquationPointsMono.At(fieldRing, k, K, carrier, n, E)))
		pieceFacts := a.Conjuncts(
			GroupPremises(
				subfieldk,
				subfieldK,
				coordinatesInK,
				normalized,
				generated,
				jIndex,
				nonzero,
				Read(AffinePieceFractionField, M).At(k, K, n, j, x)),
			"the piece is a subring of M",
			"it holds k",
			"it lies in K",
			"K is its field of fractions")
		subringM, kInPiece, pieceInK, fractions :=
			pieceFacts[0], pieceFacts[1], pieceFacts[2], pieceFacts[3]
		fieldK := a.Have(
			"K is a field under M's operations",
			"field_on(restrict_field(M, K))",
			By(subfieldK, At(field.SubfieldFieldOn.Read(M), K)))
		sameRing := a.Have(
			"the piece's ring is the same read in K or in M",
			"restrict_ring(field_ring(restrict_field(M, K)), «piece») = restrict_ring(field_ring(M), «piece»)",
			By(field.RestrictFieldRecords.At(ops, K, piece)))
		subringK := a.Have(
			"so the piece is a subring of K",
			"subring(field_ring(restrict_field(M, K)), «piece»)",
			By(
				subringM,
				pieceInK,
				sameRing,
				At(comm_ring.SubringRingOn.Read(field.RingOn.Read(M)), piece),
				At(Read(comm_ring.SubringRingOn, Read(field.RingOn, fieldK)), piece)))
		heights := a.Have(
			"every nonzero ideal of the piece has a quotient of finite dimension over k, so finite height",
			Statement{
				Binders:    "∀H:set(A).",
				Hypotheses: []string{"ring_ideal(restrict_ring(field_ring(M), «piece»), H)", "H ≠ {M.zero}"},
				Conclusion: "finite_ideal_height(restrict_ring(field_ring(M), «piece»), H)",
			},
			a.ForEach(func(H *Expr[Set[A]]) Action {
				return By(
					curve,
					pointM,
					jIndex,
					nonzero,
					Read(AffinePieceQuotientsFinite, M).At(k, n, j, E, x, H),
					subringM,
					subfieldk,
					kInPiece,
					ideal_factorization.FiniteColengthIdealHeight.Read(M).At(piece, k, H))
			}))
		maximals := a.Have(
			"every nonzero maximal ideal of the piece is principal near its point, so invertible",
			Statement{
				Binders:    "∀m:set(A).",
				Hypotheses: []string{"maximal_ideal(restrict_ring(field_ring(M), «piece»), m)", "m ≠ {M.zero}"},
				Conclusion: "invertible_fractional(field_ring(restrict_field(M, K)), «piece», m)",
			},
			Derive(func(b *Argument) {
				m := b.FixAs[Set[A]]("m")
				maximal := b.Assume()
				u, s, local := b.Unpack2As[A, A](
					GroupPremises(
						closed,
						curve,
						pointM,
						jIndex,
						nonzero,
						maximal,
						Read(AffinePieceMaximalLocallyPrincipal, M).At(k, n, j, E, x, m)),
					"u",
					"s")
				b.Show(
					"a maximal ideal generated near itself by a nonzero member is invertible",
					By(
						subringK,
						maximal,
						local,
						sameRing,
						Read(invertible_fractional_ideal.LocallyPrincipalMaximalInvertible, fieldK).At(piece, m, u, s)))
			}))
		ideals := a.Have(
			"so every nonzero ideal of the piece is invertible",
			Statement{
				Binders:    "∀I:set(A).",
				Hypotheses: []string{"ring_ideal(restrict_ring(field_ring(M), «piece»), I)", "I ≠ {M.zero}"},
				Conclusion: "invertible_fractional(field_ring(restrict_field(M, K)), «piece», I)",
			},
			a.ForEach(func(I *Expr[Set[A]]) Action {
				return By(
					subringK,
					heights,
					maximals,
					sameRing,
					Read(ideal_factorization.NonzeroIdealInvertible, fieldK).At(piece, I))
			}))
		a.Show(
			"a subring of K with field of fractions K and every "+
				"nonzero ideal invertible is integrally closed in K",
			By(
				subringK,
				fractions,
				ideals,
				sameRing,
				field.RestrictFieldRing.At(ops, K),
				Read(ideal_factorization.InvertibleIdealsIntegrallyClosed, fieldK).At(piece)))
	}),
})}
