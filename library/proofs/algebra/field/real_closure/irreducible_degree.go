package real_closure

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_closure"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_extension"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/galois_correspondence"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/ordered_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_domain"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_division"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_evaluation"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_roots"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/separable_polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_divides"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
)

// _ClosureHost is algebraic_closure's host type, set(prod(num, num → A)):
// AlgebraicClosureFieldOn states the closure of a field on A as a field on it.
type _ClosureHost = Set[Prod[Nat, Fun[Nat, A]]]

// RootsIrreducibleDegreeBound — Over a Euclidean field in which every
// odd-degree polynomial has a root, irreducibles have degree at most two. In
// an algebraic closure, the field of the adjoined roots of an irreducible and
// of an imaginary unit is finite and Galois, so it is the imaginary adjunction.
var RootsIrreducibleDegreeBound = rootsIrreducibleDegreeBoundThm{family.Add(registry.ProofEntry{
	Name: "RootsIrreducibleDegreeBound",
	Key:  "prop_8b9d4ab8e5c3c24b",
	Build: family.Sections(Statement{
		Binders: "∀F:field_ops(A). ∀lt:(A → A → bool). ∀q:(num → A).",
		Hypotheses: []string{
			"euclidean_field(F, lt)",
			"odd_degree_roots(F)",
			"polynomial_irreducible(field_ring(F), q)",
		},
		Conclusion: "polynomial_degree(q) ≤ 2",
		Abbrev: Abbrev{
			{Name: "xSquaredPlusOne", Text: "λL:field_ops(A). λn:num. COND(n = 0 ∨ n = 2, L.one, L.zero)"},
			{Name: "rootPolynomials", Text: "λL:field_ops(A). λk:set(A). λr:(num → A). λu:A. " +
				"    {r, minimal_polynomial(L, k, u)}"},
			// The entry binds a field of its own beside the one in scope where it is
			// used, so an implicit component would name two records: it spells the
			// evaluation's field operations out.
			{Name: "rootSet", Text: "λL:field_ops(A). λk:set(A). λr:(num → A). λu:A. " +
				"    {v:A | " +
				"        v ∈ L.carrier ∧ " +
				"        (∃s:(num → A). " +
				"            s ∈ «rootPolynomials»(L, k, r, u) ∧ " +
				"            polynomial_eval(L.add, L.zero, L.mul, L.one, s, v) = L.zero)}"},
			{Name: "adjoinedRoots", Text: "λL:field_ops(A). λk:set(A). λr:(num → A). λu:A. " +
				"    field_adjoin(L, k, «rootSet»(L, k, r, u))"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		imaginaryRoot := ctx.Lemma(Statement{
			Binders: "∀M:field_ops(A). ∀K:set(A).",
			Hypotheses: []string{
				"field_on(M)",
				"subfield(M, K)",
				"algebraically_closed_field(M)",
			},
			Conclusion: "∃i:A. " +
				"    i ∈ M.carrier ∧ " +
				"    i * i = -M.one ∧ " +
				"    algebraic_over(M, K, i) ∧ " +
				"    extension_degree(M, K, field_adjoin(M, K, {i})) ≤ 2",
		}, func(
			a *Argument,
			M *Expr[FieldOps[A]],
			K *Expr[Set[A]],
			fieldM field.FieldFact[on.M],
			subK, closed Fact,
		) {
			t := a.TermAs[Fun[Nat, A]]("«xSquaredPlusOne»(M)")
			zero := a.TermAs[A]("M.zero")
			ringM := a.TermAs[module_record.RingOps[A]]("field_ring(M)")
			support := a.Have(
				"X² + 1 vanishes from index three on",
				"vec⟨suc(2)⟩(«xSquaredPlusOne»(M))",
				ByArith(vec_space.VecDef))
			over := a.Have(
				"X² + 1 has its coefficients in the base field",
				"polynomial_over(K, «xSquaredPlusOne»(M))",
				By(subK, support, polynomial.PolynomialOverDef, field.SubfieldZero, field.SubfieldOne))
			degree := a.Have(
				"The leading coefficient gives degree two",
				"polynomial_degree(«xSquaredPlusOne»(M)) = 2",
				By(
					fieldM,
					over,
					support,
					polynomial.DegreeExact.At(zero, K, t, a.TermAs[Nat]("2")),
					field.OneNotZeroOn.Read(fieldM)))
			// The closure law asks for positive degree; ByArith reads 0 < 2 off degree.
			i, root := a.ObtainAs[A](
				"Closedness supplies a root of X² + 1",
				"∃i:A. i ∈ M.carrier ∧ polynomial_eval(«xSquaredPlusOne»(M), i) = M.zero",
				ByArith(
					fieldM,
					subK,
					closed,
					degree,
					over,
					algebraic_closure.AlgebraicallyClosedDef.At(M),
					polynomial.PolynomialOverMono,
					field.SubfieldSubset))
			square := a.Have(
				"A root of X² + 1 squares to minus one",
				"i * i = -M.one",
				ByArith(
					fieldM,
					subK,
					root,
					over,
					support,
					field.RingOn.Read(fieldM),
					polynomial_evaluation.EvalVecThree.At(ringM, t, i),
					polynomial.PolynomialOverMono.At(zero, K, a.TermAs[Set[A]]("M.carrier"), t),
					field.SubfieldSubset.At(M, K)))
			nonzero := a.Have(
				"The constant coefficient excludes the zero polynomial",
				"«xSquaredPlusOne»(M) ≠ vec_zero",
				By(fieldM, field.OneNotZeroOn.Read(fieldM), vec_space.VecZeroDef))
			algebraic := a.Have(
				"X² + 1 makes its root algebraic",
				"algebraic_over(M, K, i)",
				Derive(func(b *Argument) {
					b.Do(Simp(Fwd(algebraic_element.AlgebraicOverDef)))
					b.Take(t)
					b.Show(
						"The nonzero polynomial X² + 1 witnesses algebraicity",
						By(over, nonzero, root))
				}))
			a.Take(i)
			a.Show(
				"The minimal polynomial bounds the imaginary adjunction by two",
				ByArith(
					fieldM,
					subK,
					degree,
					root,
					square,
					nonzero,
					over,
					algebraic,
					algebraic_element.MinimalPolynomialLeast.At(M, K, i, t),
					algebraic_element.AdjoinDegree.At(M, K, i)))
		})

		orderedSeparable := ctx.Lemma(Statement{
			Binders: "∀M:field_ops(A). ∀K:set(A). ∀lt:(A → A → bool). ∀p:(num → A).",
			Hypotheses: []string{
				"field_on(M)",
				"subfield(M, K)",
				"ordered_field_on(restrict_field(M, K), lt)",
				"polynomial_irreducible(restrict_ring(field_ring(M), K), p)",
			},
			Conclusion: "polynomial_separable(restrict_ring(field_ring(M), K), p)",
		}, func(
			a *Argument,
			M *Expr[FieldOps[A]],
			K *Expr[Set[A]],
			lt *Arrow2[A, A, Bool],
			p *Expr[Fun[Nat, A]],
			fieldM field.FieldFact[on.M],
			subK, ordered, irreducible Fact,
		) {
			T := a.TermAs[FieldOps[A]]("restrict_field(M, K)")
			base := a.Have(
				"The ordered restriction is a characteristic-zero field",
				"field_on(restrict_field(M, K)) ∧ "+
					"subfield(restrict_field(M, K), K) ∧ "+
					"characteristic_zero(field_ring(restrict_field(M, K)))",
				By(
					fieldM,
					subK,
					ordered,
					ordered_field.CharacteristicZero.At(T, lt),
					field.SubfieldFieldOn.At(M, K),
					field.CarrierSubfield.At(T),
					field.RestrictFieldDef))
			a.Show(
				"Characteristic zero makes the irreducible separable over the base",
				By(
					fieldM,
					subK,
					ordered,
					irreducible,
					base,
					separable_polynomial.CharZeroIrreducibleSeparable.At(T, K, p),
					field.RestrictFieldRing.At(M, K),
					module_record.RestrictRingTwice.At(a.TermAs[module_record.RingOps[A]]("field_ring(M)"), K, K)))
		})

		rootFieldBound := ctx.Lemma(Statement{
			Binders: "∀M:field_ops(A). ∀K:set(A). ∀lt:(A → A → bool). ∀p:(num → A). ∀α i:A.",
			Hypotheses: []string{
				"field_on(M)",
				"subfield(M, K)",
				"algebraically_closed_field(M)",
				"euclidean_field(restrict_field(M, K), lt)",
				"odd_degree_roots(restrict_field(M, K))",
				"polynomial_irreducible(restrict_ring(field_ring(M), K), p)",
				"α ∈ M.carrier",
				"polynomial_eval(p, α) = M.zero",
				"algebraic_over(M, K, α)",
				"i ∈ M.carrier",
				"i * i = -M.one",
				"algebraic_over(M, K, i)",
				"extension_degree(M, K, field_adjoin(M, K, {i})) ≤ 2",
			},
			Conclusion: "polynomial_degree(p) ≤ 2",
		}, func(
			a *Argument,
			M *Expr[FieldOps[A]],
			K *Expr[Set[A]],
			lt *Arrow2[A, A, Bool],
			p *Expr[Fun[Nat, A]],
			α, i *Expr[A],
			fieldM field.FieldFact[on.M],
			subK, closed, euclidean, odd, irreducible, alphaIn, alphaRoot, alphaAlg, iIn, iSquare, iAlg, iDegree Fact,
		) {
			ordered := ordered_field.EuclideanOrderedField.Read(euclidean)
			ringM := a.TermAs[module_record.RingOps[A]]("field_ring(M)")
			scalarRing := a.TermAs[module_record.RingOps[A]]("restrict_ring(field_ring(M), K)")
			T := a.TermAs[FieldOps[A]]("restrict_field(M, K)")
			muI := a.TermAs[Fun[Nat, A]]("minimal_polynomial(M, K, i)")
			muAlpha := a.TermAs[Fun[Nat, A]]("minimal_polynomial(M, K, α)")
			P := a.TermAs[Set[Fun[Nat, A]]]("«rootPolynomials»(M, K, p, i)")
			roots := a.TermAs[Set[A]]("«rootSet»(M, K, p, i)")
			N := a.TermAs[Set[A]]("«adjoinedRoots»(M, K, p, i)")
			muIrreducible := a.Have(
				"The imaginary root has an irreducible minimal polynomial",
				"polynomial_irreducible(restrict_ring(field_ring(M), K), minimal_polynomial(M, K, i))",
				By(fieldM, subK, iIn, iAlg, algebraic_element.MinimalPolynomialIrreducible.At(M, K, i)))
			irreducibleSplits := a.Have(
				"An irreducible over the base is a base polynomial that is separable and splits in the host",
				Statement{
					Binders: "∀r:(num → A).",
					Hypotheses: []string{
						"polynomial_irreducible(restrict_ring(field_ring(M), K), r)",
					},
					Conclusion: "polynomial_over(K, r) ∧ " +
						"polynomial_separable(restrict_ring(field_ring(M), K), r) ∧ " +
						"polynomial_splits(field_ring(M), r)",
				},
				Derive(func(b *Argument) {
					r := b.FixAs[Fun[Nat, A]]("r")
					irreducibleR := b.Assume()
					b.Show(
						"Characteristic zero makes it separable and the closed host splits it",
						By(
							fieldM,
							subK,
							closed,
							ordered,
							irreducibleR,
							polynomial_division.PolynomialIrreducibleDef.At(scalarRing, r),
							At(orderedSeparable, M, K, lt, r),
							algebraic_closure.ClosedFieldSplits.At(M, r)))
				}))
			familyProperties := a.Have(
				"The two irreducibles form a separable splitting family",
				Statement{
					Binders: "∀r:(num → A).",
					Hypotheses: []string{
						"r ∈ «rootPolynomials»(M, K, p, i)",
					},
					Conclusion: "polynomial_over(K, r) ∧ " +
						"polynomial_separable(restrict_ring(field_ring(M), K), r) ∧ " +
						"polynomial_splits(field_ring(M), r)",
				},
				Derive(func(b *Argument) {
					b.FixAs[Fun[Nat, A]]("r")
					member := b.Assume()
					alternatives := b.Have(
						"A member is one of the two polynomials",
						"r = p ∨ r = minimal_polynomial(M, K, i)",
						BySets(member))
					b.Do(alternatives.SplitDisj(
						LeftHolds(
							"The member is the original irreducible",
							Given(func(c *Argument, equal Fact) {
								c.Do(equal.Rw())
								c.Show(
									"The original irreducible is separable and splits",
									By(irreducible, irreducibleSplits.At(p)))
							})),
						RightHolds(
							"The member is the imaginary minimal polynomial",
							Given(func(c *Argument, equal Fact) {
								c.Do(equal.Rw())
								c.Show(
									"The imaginary minimal polynomial is separable and splits",
									By(muIrreducible, irreducibleSplits.At(muI)))
							})),
					))
				}))
			galois := a.Have(
				"The finite separable splitting family generates a Galois extension",
				"galois_over(M, K, «adjoinedRoots»(M, K, p, i))",
				By(
					fieldM,
					subK,
					familyProperties,
					galois_correspondence.SeparableRootFieldGalois.At(M, K, P),
					finite_set.FiniteInsert.At(p, a.TermAs[Set[Fun[Nat, A]]]("{minimal_polynomial(M, K, i)}")),
					finite_set.FiniteSing.At(muI)))
			adjoin := a.Have(
				"The field of the adjoined roots is a subfield containing the base and all of them",
				"subfield(M, «adjoinedRoots»(M, K, p, i)) ∧ "+
					"K ⊆ «adjoinedRoots»(M, K, p, i) ∧ "+
					"«rootSet»(M, K, p, i) ⊆ «adjoinedRoots»(M, K, p, i)",
				Derive(func(b *Argument) {
					inside := b.Have(
						"The base and the root set lie in the host",
						"K ⊆ M.carrier ∧ «rootSet»(M, K, p, i) ⊆ M.carrier",
						BySets(subK, field.SubfieldSubset.At(M, K)))
					b.Show(
						"Adjoining these elements stays inside the host",
						By(fieldM, inside, algebraic_element.AdjoinSubfield.At(M, K, roots)))
				}))
			selected := a.Have(
				"The polynomial root and the imaginary root lie in the field of the adjoined roots",
				"α ∈ «adjoinedRoots»(M, K, p, i) ∧ i ∈ «adjoinedRoots»(M, K, p, i)",
				Derive(func(b *Argument) {
					witnesses := b.Have(
						"Each selected point is a root of a polynomial in the family",
						"(∃s:(num → A). s ∈ «rootPolynomials»(M, K, p, i) ∧ polynomial_eval(s, α) = M.zero) ∧ "+
							"(∃s:(num → A). s ∈ «rootPolynomials»(M, K, p, i) ∧ polynomial_eval(s, i) = M.zero)",
						Derive(func(c *Argument) {
							c.Do(SplitConj(
								Case(
									"The given polynomial supplies its selected root",
									Derive(func(d *Argument) {
										d.Take(p)
										d.Show(
											"The polynomial belongs to the family and vanishes",
											BySets(alphaRoot))
									})),
								Case(
									"The minimal polynomial supplies the imaginary root",
									Derive(func(d *Argument) {
										d.Take(muI)
										d.Show(
											"The minimal polynomial belongs to the family and vanishes",
											BySets(fieldM, subK, iIn, iAlg, algebraic_element.MinimalPolynomialSpec.At(M, K, i)))
									})),
							))
						}))
					b.Show(
						"The root-set inclusions place both points in the adjunction",
						BySets(alphaIn, iIn, witnesses, adjoin))
				}))
			imaginary := a.Have(
				"The field of the adjoined roots, finite and Galois, is the imaginary adjunction",
				"«adjoinedRoots»(M, K, p, i) = field_adjoin(M, K, {i})",
				By(
					fieldM,
					subK,
					euclidean,
					odd,
					selected,
					adjoin,
					galois,
					iSquare,
					At(FiniteGaloisImaginaryAdjoin, M, K, N, lt, i)))
			finiteN := a.Have(
				"The field of the adjoined roots is finite over K, being Galois",
				"finite_extension(M, K, «adjoinedRoots»(M, K, p, i))",
				By(galois, galois_correspondence.GaloisOverDef.At(M, K, N)))
			rootDegree := a.Have(
				"The degree of the minimal polynomial of α divides [N : K], which is [K(i) : K], at most two",
				"polynomial_degree(minimal_polynomial(M, K, α)) ≤ 2",
				ByArith(
					fieldM,
					subK,
					adjoin,
					finiteN,
					selected,
					imaginary,
					iDegree,
					algebraic_element.MinimalPolynomialDegreeDivides.At(M, K, N, α),
					nat_divides.DividesLessEq.At(
						a.TermAs[Nat]("polynomial_degree(minimal_polynomial(M, K, α))"),
						a.TermAs[Nat]("extension_degree(M, K, «adjoinedRoots»(M, K, p, i))")),
					field_extension.ExtensionDegreePositive.At(M, K, N)))
			minimal := a.Have(
				"The root's minimal polynomial has degree at most two",
				"polynomial_over(K, minimal_polynomial(M, K, α)) ∧ "+
					"polynomial_eval(minimal_polynomial(M, K, α), α) = M.zero ∧ "+
					"minimal_polynomial(M, K, α) ≠ vec_zero ∧ "+
					"polynomial_degree(minimal_polynomial(M, K, α)) ≤ 2",
				ByArith(
					fieldM,
					subK,
					alphaIn,
					alphaAlg,
					rootDegree,
					algebraic_element.MinimalPolynomialSpec.At(M, K, α),
					integral_domain.FieldIntegralDomain.At(M),
					polynomial.MonicNonzero.At(ringM, muAlpha)))
			ambient := a.Have(
				"Both polynomials can be evaluated over the ambient host",
				"polynomial_over(M.carrier, p) ∧ polynomial_over(M.carrier, minimal_polynomial(M, K, α))",
				BySets(
					familyProperties.At(p),
					subK,
					minimal,
					At(polynomial.PolynomialOverMono, a.TermAs[A]("M.zero"), K, a.TermAs[Set[A]]("M.carrier")),
					field.SubfieldSubset.At(M, K)))
			divides := a.Have(
				"The irreducible divides the minimal polynomial of its root",
				"polynomial_divides(restrict_ring(field_ring(M), K), p, minimal_polynomial(M, K, α))",
				Derive(func(b *Argument) {
					notDivides := b.SupposeNot()
					coprime := b.Have(
						"A nondividing irreducible is coprime to the minimal polynomial",
						"polynomial_coprime(restrict_ring(field_ring(M), K), p, minimal_polynomial(M, K, α))",
						By(
							fieldM,
							subK,
							irreducible,
							minimal,
							notDivides,
							field.SubfieldFieldOn.At(M, K),
							field.RestrictFieldRing.At(M, K),
							field.RestrictFieldDef.At(M, K),
							polynomial_division.IrreducibleCoprime.At(T, p, muAlpha),
							polynomial_division.PolynomialCoprimeDef.At(scalarRing, p, muAlpha)))
					b.Show(
						"Coprime polynomials cannot have the selected common root",
						By(
							fieldM,
							subK,
							alphaRoot,
							alphaIn,
							minimal,
							ambient,
							coprime,
							field.SubfieldSubset.At(M, K),
							polynomial_division.CoprimeMono.At(ringM, K, p, muAlpha),
							polynomial_roots.CoprimeNoCommonRoot.At(M, p, muAlpha, α)))
				}))
			a.Show(
				"A divisor of the nonzero minimal polynomial has degree at most two",
				ByArith(
					fieldM,
					subK,
					minimal,
					divides,
					ambient,
					field.SubfieldSubset.At(M, K),
					polynomial_division.DividesMono.At(ringM, K, p, muAlpha),
					polynomial_division.DividesDegree.At(M, p, muAlpha)))
		})

		return ctx.Theorem(headline, func(
			a *Argument,
			F *Expr[FieldOps[A]],
			lt *Arrow2[A, A, Bool],
			q *Expr[Fun[Nat, A]],
			euclidean ordered_field.EuclideanFieldFact[on.F],
			odd, irreducible Fact,
		) {
			// ι is algebraic_closure's embedding, «closureEmbedding» of the chapter's outer
			// table: the map AlgebraicClosureFieldOn is stated at.
			ι, embedding := a.LetAs[Fun[A, _ClosureHost]]("ι", "«closureEmbedding»")
			fieldF := ordered_field.FieldOn.Read(ordered_field.EuclideanOrderedField.Read(euclidean))
			M, closure := a.ObtainAs[FieldOps[_ClosureHost]](
				"Embed the source in an algebraically closed host",
				"∃M:field_ops(set(prod(num, num → A))). "+
					"    field_on(M) ∧ "+
					"    algebraically_closed_field(M) ∧ "+
					"    subfield(M, image(ι, F.carrier)) ∧ "+
					"    ring_isomorphism(field_ring(F), restrict_ring(field_ring(M), image(ι, F.carrier)), ι) ∧ "+
					"    (∀x:set(prod(num, num → A)). x ∈ M.carrier ⇒ algebraic_over(M, image(ι, F.carrier), x))",
				Derive(func(b *Argument) {
					b.Do(embedding.Rw())
					b.Show(
						"The algebraic closure supplies the host and its image isomorphism",
						By(fieldF, algebraic_closure.AlgebraicClosureFieldOn.At(F)))
				}))
			K, image := a.LetAs[Set[_ClosureHost]]("K", "image(ι, F.carrier)")
			restricted := a.TermAs[FieldOps[_ClosureHost]]("restrict_field(M, K)")
			closedParts := a.Conjuncts(
				closure,
				"The host is a field",
				"The host is algebraically closed",
				"The source image is a subfield",
				"The source is isomorphic to its image",
				"The host is algebraic over the image")
			fieldM, closed, subK, iso, algebraic :=
				closedParts[0], closedParts[1], closedParts[2], closedParts[3], closedParts[4]
			base := a.Have(
				"The image restriction is the target field of the isomorphism",
				"field_on(restrict_field(M, K)) ∧ "+
					"ring_isomorphism(field_ring(F), field_ring(restrict_field(M, K)), ι) ∧ "+
					"restrict_field(M, K).carrier = K",
				Derive(func(b *Argument) {
					b.Do(SplitConj(
						Case(
							"Restricting the image gives the target field and scalar ring",
							By(
								Normalized,
								fieldM,
								subK,
								iso,
								field.SubfieldFieldOn.At(M, K),
								field.RestrictFieldRing.At(M, K))),
						Case(
							"The restriction to the image has the image as its carrier",
							Simp(Fwd(field.RestrictFieldDef)),
							Basic()),
					))
				}))
			transferred := a.Have(
				"The image field, with the order carried over, is "+
					"Euclidean, and its odd-degree polynomials have roots",
				"euclidean_field(restrict_field(M, K), transport_order(ι, F.carrier, lt)) ∧ "+
					"odd_degree_roots(restrict_field(M, K))",
				By(
					euclidean,
					odd,
					fieldF,
					base,
					ordered_field.TransportEuclideanIsomorphism.Read(euclidean).At(restricted, ι),
					algebraic_element.TransportOddDegreeRootsIsomorphism.At(F, restricted, ι)))
			p, mapped := a.LetAs[Fun[Nat, _ClosureHost]]("p", "λn:num. ι(q(n))")
			fRing := a.TermAs[module_record.RingOps[A]]("field_ring(F)")
			fCarrier := a.TermAs[Set[A]]("F.carrier")
			sourcePolynomial := a.Have(
				"An irreducible is a polynomial of positive degree",
				"polynomial_over(F.carrier, q) ∧ 0 < polynomial_degree(q)",
				By(irreducible, polynomial_division.PolynomialIrreducibleDef.At(fRing, q)))
			transported := a.Have(
				"The embedded polynomial is irreducible and keeps its positive degree",
				"polynomial_irreducible(restrict_ring(field_ring(M), K), p) ∧ "+
					"polynomial_over(K, p) ∧ "+
					"polynomial_degree(p) = polynomial_degree(q) ∧ "+
					"0 < polynomial_degree(p)",
				Derive(func(b *Argument) {
					b.Do(mapped.Rw())
					b.Show(
						"Embedding preserves irreducibility and degree over the image scalars",
						By(
							fieldF,
							image,
							irreducible,
							base,
							sourcePolynomial,
							field.CarrierSubfield.At(F),
							ring_homomorphism.RingIsomorphismDef.At(
								fRing, b.TermAs[module_record.RingOps[_ClosureHost]]("field_ring(restrict_field(M, K))"), ι),
							module_record.RestrictRingCarrier.At(fRing),
							field.RestrictFieldRing.At(M, K),
							module_record.RestrictRingTwice.At(
								b.TermAs[module_record.RingOps[_ClosureHost]]("field_ring(M)"), K, K),
							algebraic_element.FieldEmbeddingIrreducible.At(F, restricted, ι, fCarrier, q),
							algebraic_element.FieldEmbeddingPolynomials.At(F, restricted, ι, fCarrier, q)))
				}))
			α, root := a.ObtainAs[_ClosureHost](
				"The embedded irreducible has a root in the closed host",
				"∃α:set(prod(num, num → A)). α ∈ M.carrier ∧ polynomial_eval(p, α) = M.zero",
				By(
					closed,
					subK,
					transported,
					algebraic_closure.AlgebraicallyClosedDef.At(M),
					polynomial.PolynomialOverMono.At(
						a.TermAs[_ClosureHost]("M.zero"), K, a.TermAs[Set[_ClosureHost]]("M.carrier"), p),
					field.SubfieldSubset.At(M, K)))
			i, imaginary := a.ObtainAs[_ClosureHost](
				"Choose an imaginary root with adjunction degree at most two",
				"∃i:set(prod(num, num → A)). "+
					"    i ∈ M.carrier ∧ "+
					"    i * i = -M.one ∧ "+
					"    algebraic_over(M, K, i) ∧ "+
					"    extension_degree(M, K, field_adjoin(M, K, {i})) ≤ 2",
				By(fieldM, closed, subK, At(imaginaryRoot, M, K)))
			a.Show(
				"The argument through the adjoined roots bounds the original irreducible degree",
				ByArith(
					closed,
					fieldM,
					algebraic.At(α),
					subK,
					root,
					transferred,
					transported,
					imaginary,
					At(
						rootFieldBound,
						M,
						K,
						a.TermAs[Fun2[_ClosureHost, _ClosureHost, Bool]]("transport_order(ι, F.carrier, lt)"),
						p,
						α,
						i)))
		})
	}),
})}
