// galois_correspondence.go — the chapter: normal extensions, separable
// elements and Galois extensions of a subfield, and how each passes to
// the top of a tower; the conjugates of a separable element of a normal
// extension number its degree; a root of a separable polynomial is
// separable, and a field embedding carries separable elements to
// separable elements.

package galois_correspondence

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_extension"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_division"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_roots"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/separable_polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The definitions
// ---------------------------------------------------------------------------

// NormalOverDef — `normal_over(L, K, M)`: M is normal over K, every
// irreducible polynomial over K with a root in M splitting over M.
var NormalOverDef = normalOverDefThm{family.Define(registry.DefEntry{
	Name:  "NormalOverDef",
	Key:   "prop_ff554ad735071ab0",
	Const: "normal_over",
	Type:  "field_ops(A) → set(A) → set(A) → bool",
	Equations: []string{
		"∀L:field_ops(A). ∀K M:set(A). " +
			"    normal_over(L, K, M) ⇔ " +
			"    (∀p:(num → A). ∀a:A. " +
			"        polynomial_irreducible(restrict_ring(field_ring(L), K), p) ∧ " +
			"        a ∈ M ∧ " +
			"        polynomial_eval(L.add, L.zero, L.mul, L.one, p, a) = L.zero ⇒ " +
			"        polynomial_splits(restrict_ring(field_ring(L), M), p))",
	},
})}

// SeparableOverDef — `separable_over(L, K, a)`: a is algebraic over K and
// its minimal polynomial is coprime over K to its derivative.
var SeparableOverDef = separableOverDefThm{family.Define(registry.DefEntry{
	Name:  "SeparableOverDef",
	Key:   "prop_b69101d555e90ff2",
	Const: "separable_over",
	Type:  "field_ops(A) → set(A) → A → bool",
	Equations: []string{
		"∀L:field_ops(A). ∀K:set(A). ∀a:A. " +
			"    separable_over(L, K, a) ⇔ " +
			"    algebraic_over(L, K, a) ∧ " +
			"    polynomial_separable(restrict_ring(field_ring(L), K), minimal_polynomial(L, K, a))",
	},
})}

// GaloisOverDef — `galois_over(L, K, M)`: M is a finite extension of K,
// normal over K, and each of its members is separable over K.
var GaloisOverDef = galoisOverDefThm{family.Define(registry.DefEntry{
	Name:  "GaloisOverDef",
	Key:   "prop_c09bfc30a1680ae0",
	Const: "galois_over",
	Type:  "field_ops(A) → set(A) → set(A) → bool",
	Equations: []string{
		"∀L:field_ops(A). ∀K M:set(A). " +
			"    galois_over(L, K, M) ⇔ " +
			"    finite_extension(L, K, M) ∧ normal_over(L, K, M) ∧ (∀a:A. a ∈ M ⇒ separable_over(L, K, a))",
	},
	Deps: []registry.EntryLike{NormalOverDef, SeparableOverDef},
})}

// ---------------------------------------------------------------------------
// Normality and separability
// ---------------------------------------------------------------------------

// NormalIffMinimalPolynomial — M is normal over K exactly when the
// minimal polynomial over K of each member of M algebraic over K splits
// over M: every irreducible annihilator divides that minimal polynomial,
// since otherwise the two would be coprime and yet share the root.
var NormalIffMinimalPolynomial = normalIffMinimalPolynomialThm{family.Add(registry.ProofEntry{
	Name: "NormalIffMinimalPolynomial",
	Key:  "prop_e254104bf54744d7",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀K M:set(A).",
		Hypotheses: []string{
			"subfield(L, K)",
			"subfield(L, M)",
			"K ⊆ M",
		},
		Conclusion: "normal_over(L, K, M) ⇔ " +
			"∀a:A. " +
			"    a ∈ M ∧ algebraic_over(L, K, a) ⇒ " +
			"    polynomial_splits(restrict_ring(field_ring(L), M), minimal_polynomial(L, K, a))",
	}, func(arg *Argument, L field.FieldFact[on.L], K, M *Expr[Set[A]], subK, subM, inclusion Fact) {
		l := arg.TermAs[FieldOps[A]]("L")
		carrier := arg.TermAs[Set[A]]("L.carrier")
		zero := arg.TermAs[A]("L.zero")
		fieldRing := arg.TermAs[module_record.RingOps[A]]("field_ring(L)")
		arg.Iff()
		arg.Forward(
			"normality applies to each irreducible minimal polynomial",
			func(b *Argument, normal Fact) {
				x := b.FixAs[A]("a")
				algebraicMember := b.Assume()
				inL := b.Have(
					"a member of M lies in the ambient field",
					"a ∈ L.carrier",
					By(algebraicMember, field.SubfieldSubset.Read(subM), set_basic.SubsetDef.At(M, carrier)))
				xm := b.MemberOf[on.L](x, inL)
				irreducible := b.Have(
					"the minimal polynomial is irreducible over K",
					"polynomial_irreducible(restrict_ring(field_ring(L), K), minimal_polynomial(L, K, a))",
					By(xm, algebraicMember, subK, algebraic_element.MinimalPolynomialIrreducible.Read(L).At(K, xm)))
				vanishes := b.Have(
					"the minimal polynomial annihilates a",
					"polynomial_eval(minimal_polynomial(L, K, a), a) = L.zero",
					By(xm, algebraicMember, subK, algebraic_element.MinimalPolynomialSpec.Read(L).At(K, xm)))
				b.Show(
					"normality makes the minimal polynomial split over M",
					By(algebraicMember, irreducible, vanishes, normal, NormalOverDef.At(l, K, M)))
			})
		arg.Backward(
			"an irreducible polynomial with a root in M splits over M",
			func(b *Argument, splits Fact) {
				b.Do(Simp(Fwd(NormalOverDef)))
				p := b.FixAs[Fun[Nat, A]]("p")
				x := b.FixAs[A]("a")
				irreducibleRoot := b.Assume()
				subsets := b.Have(
					"both scalar fields lie in the ambient carrier",
					"K ⊆ L.carrier ∧ M ⊆ L.carrier",
					By(field.SubfieldSubset.Read(subK), field.SubfieldSubset.Read(subM)))
				inL := b.Have(
					"the root lies in the ambient field",
					"a ∈ L.carrier",
					By(irreducibleRoot, subsets, set_basic.SubsetDef.At(M, carrier)))
				xm := b.MemberOf[on.L](x, inL)
				scalarField := b.Have(
					"K is a field under the operations of L",
					"field_on(restrict_field(L, K))",
					By(subK, field.SubfieldFieldOn.Read(L).At(K)))
				targetRing := b.Have(
					"M is a commutative ring under the operations of L",
					"comm_ring_on(restrict_ring(field_ring(L), M))",
					By(subM, field.SubfieldCommRing.Read(L).At(M)))
				irreducibleData := b.Have(
					"the irreducible polynomial is over K and has positive degree",
					"polynomial_over(K, p) ∧ 0 < polynomial_degree(p)",
					By(
						irreducibleRoot,
						polynomial_division.PolynomialIrreducibleDef.At(
							b.TermAs[module_record.RingOps[A]]("restrict_ring(field_ring(L), K)"), p)))
				nonzero := b.Have(
					"positive degree excludes the zero polynomial",
					"p ≠ vec_zero",
					By(irreducibleData, polynomial.DegreeVecZero.At(zero), nat_order.LessThanIrrefl))
				algebraic := b.Have(
					"the irreducible annihilator witnesses algebraicity",
					"algebraic_over(L, K, a)",
					Simp(Fwd(algebraic_element.AlgebraicOverDef)),
					Witness(p),
					By(irreducibleData, nonzero, irreducibleRoot))
				q, qDef := b.LetAs[Fun[Nat, A]]("q", "minimal_polynomial(L, K, a)")
				minimalData := b.Have(
					"the minimal polynomial is over K and annihilates a",
					"polynomial_over(K, q) ∧ polynomial_eval(q, a) = L.zero",
					By(qDef, subK, xm, algebraic, algebraic_element.MinimalPolynomialSpec.Read(L).At(K, xm)))
				minimalSplits := b.Have(
					"the assumed condition makes the minimal polynomial split",
					"polynomial_splits(restrict_ring(field_ring(L), M), q)",
					By(Normalized, qDef, irreducibleRoot, algebraic, splits.At(x)))
				dividesK := b.Have(
					"the irreducible annihilator divides the minimal polynomial over K",
					"polynomial_divides(restrict_ring(field_ring(L), K), p, q)",
					Derive(func(c *Argument) {
						notDivides := c.SupposeNot()
						coprimeK := c.Have(
							"otherwise the two polynomials are coprime over K",
							"polynomial_coprime(restrict_ring(field_ring(L), K), p, q)",
							By(
								c.Simplified(irreducibleRoot, Fwd(field.RestrictFieldRing)),
								minimalData,
								c.Simplified(notDivides, Fwd(field.RestrictFieldRing)),
								polynomial_division.IrreducibleCoprime.Read(scalarField).At(p, q),
								polynomial_division.PolynomialCoprimeDef.At(
									c.TermAs[module_record.RingOps[A]]("restrict_ring(field_ring(L), K)"), p, q)))
						c.Show(
							"coprime over K they are coprime over L, and there they share no root, yet a is a root of both",
							By(
								subsets,
								irreducibleData,
								minimalData,
								coprimeK,
								irreducibleRoot,
								xm,
								polynomial_division.CoprimeMono.At(fieldRing, K, p, q),
								polynomial.PolynomialOverMono.At(zero, K, carrier, p),
								polynomial.PolynomialOverMono.At(zero, K, carrier, q),
								polynomial_roots.CoprimeNoCommonRoot.Read(L).At(p, q, xm)))
					}))
				b.Show(
					"a divisor over K divides over M, where a divisor of the split minimal polynomial splits",
					By(
						Normalized,
						inclusion,
						dividesK,
						minimalSplits,
						module_record.RestrictRingTwice.At(fieldRing, M, K),
						polynomial_division.DividesMono.At(
							b.TermAs[module_record.RingOps[A]]("restrict_ring(field_ring(L), M)"), K, p, q),
						separable_polynomial.SplitsDivisor.Read(targetRing).At(p, q)))
			})
	}),
})}

// NormalTower — a finite normal extension is normal over every
// intermediate field.
var NormalTower = normalTowerThm{family.Add(registry.ProofEntry{
	Name: "NormalTower",
	Key:  "prop_bd0cfd8f4e4625b9",
	Reading: "finite_extension(K, M) is load-bearing, normal_over asking " +
		"no algebraicity: ℚ(t) is normal over ℚ, but over E = ℚ(t³) the " +
		"irreducible x³ - t³ has the root t in ℚ(t) and does not split there.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀K E M:set(A).",
		Hypotheses: []string{
			"subfield(L, K)",
			"subfield(L, E)",
			"subfield(L, M)",
			"K ⊆ E",
			"E ⊆ M",
			"finite_extension(L, K, M)",
			"normal_over(L, K, M)",
		},
		Conclusion: "normal_over(L, E, M)",
	}, func(
		arg *Argument,
		L field.FieldFact[on.L],
		K, E, M *Expr[Set[A]],
		subK, subE, subM, kInE, eInM, finite, normal Fact,
	) {
		zero := arg.TermAs[A]("L.zero")
		kInM := arg.Have(
			"the bottom field lies in the top field",
			"K ⊆ M",
			BySets(kInE, eInM))
		targetRing := arg.Have(
			"M is a commutative ring under the operations of L",
			"comm_ring_on(restrict_ring(field_ring(L), M))",
			By(subM, field.SubfieldCommRing.Read(L).At(M)))
		arg.Do(Simp(Fwd(NormalIffMinimalPolynomial.Read(L))))
		x := arg.FixAs[A]("a")
		algebraicMember := arg.Assume()
		p := arg.TermAs[Fun[Nat, A]]("minimal_polynomial(L, K, a)")
		q := arg.TermAs[Fun[Nat, A]]("minimal_polynomial(L, E, a)")
		inL := arg.Have(
			"a member of M lies in the ambient field",
			"a ∈ L.carrier",
			By(
				algebraicMember,
				field.SubfieldSubset.Read(subM),
				set_basic.SubsetDef.At(M, arg.TermAs[Set[A]]("L.carrier"))))
		xm := arg.MemberOf[on.L](x, inL)
		algebraicK := arg.Have(
			"finiteness over K makes every member of M algebraic over K",
			"algebraic_over(L, K, a)",
			By(
				subK,
				subM,
				kInM,
				finite,
				algebraicMember,
				algebraic_element.FiniteExtensionAlgebraic.Read(L).At(K, M, x)))
		overK := arg.Have(
			"the minimal polynomial over K has coefficients in K",
			"polynomial_over(K, minimal_polynomial(L, K, a))",
			By(subK, xm, algebraicK, algebraic_element.MinimalPolynomialSpec.Read(L).At(K, xm)))
		vanishes := arg.Have(
			"the minimal polynomial over K annihilates a",
			"polynomial_eval(minimal_polynomial(L, K, a), a) = L.zero",
			By(subK, xm, algebraicK, algebraic_element.MinimalPolynomialSpec.Read(L).At(K, xm)))
		overE := arg.Have(
			"the same polynomial has coefficients in E",
			"polynomial_over(E, minimal_polynomial(L, K, a))",
			By(kInE, overK, polynomial.PolynomialOverMono.At(zero, K, E, p)))
		dividesE := arg.Have(
			"the minimal polynomial over E divides the annihilator over E",
			"polynomial_divides(restrict_ring(field_ring(L), E), "+
				"    minimal_polynomial(L, E, a), "+
				"    minimal_polynomial(L, K, a))",
			By(
				subE,
				algebraicMember,
				xm,
				overE,
				vanishes,
				algebraic_element.MinimalPolynomialDivides.Read(L).At(E, xm, p)))
		splitsK := arg.Have(
			"normality over K makes the original minimal polynomial split over M",
			"polynomial_splits(restrict_ring(field_ring(L), M), minimal_polynomial(L, K, a))",
			By(
				subK,
				subM,
				kInM,
				normal,
				algebraicMember,
				algebraicK,
				NormalIffMinimalPolynomial.Read(L).At(K, M)))
		arg.Show(
			"a divisor over E divides over M, so the minimal polynomial "+
				"over E splits as a divisor of that split polynomial",
			By(
				eInM,
				dividesE,
				splitsK,
				module_record.RestrictRingTwice.At(arg.TermAs[module_record.RingOps[A]]("field_ring(L)"), M, E),
				polynomial_division.DividesMono.At(
					arg.TermAs[module_record.RingOps[A]]("restrict_ring(field_ring(L), M)"), E, q, p),
				separable_polynomial.SplitsDivisor.Read(targetRing).At(q, p)))
	}),
})}

// SeparableTower — an element separable over K is separable over every
// larger subfield: its minimal polynomial over K remains a separable
// annihilator over the larger field.
var SeparableTower = separableTowerThm{family.Add(registry.ProofEntry{
	Name: "SeparableTower",
	Key:  "prop_eddc4c798e892f38",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀K E:set(A). ∀a:A.",
		Hypotheses: []string{
			"subfield(L, K)",
			"subfield(L, E)",
			"K ⊆ E",
			"a ∈ L.carrier",
			"separable_over(L, K, a)",
		},
		Conclusion: "separable_over(L, E, a)",
	}, func(
		arg *Argument,
		L field.FieldFact[on.L],
		K, E *Expr[Set[A]],
		a *Member[A, on.L],
		subfieldK, subfieldE, inclusion, isSeparable Fact,
	) {
		l := arg.TermAs[FieldOps[A]]("L")
		p := arg.TermAs[Fun[Nat, A]]("minimal_polynomial(L, K, a)")
		algebraic := arg.Have(
			"separability supplies algebraicity over K",
			"algebraic_over(L, K, a)",
			By(isSeparable, SeparableOverDef.At(l, K, a)))
		overK := arg.Have(
			"the minimal polynomial has coefficients in K",
			"polynomial_over(K, minimal_polynomial(L, K, a))",
			By(subfieldK, a, algebraic, algebraic_element.MinimalPolynomialSpec.Read(L).At(K, a)))
		vanishes := arg.Have(
			"the minimal polynomial annihilates a",
			"polynomial_eval(minimal_polynomial(L, K, a), a) = L.zero",
			By(subfieldK, a, algebraic, algebraic_element.MinimalPolynomialSpec.Read(L).At(K, a)))
		separableK := arg.Have(
			"the minimal polynomial is separable over K",
			"polynomial_separable(restrict_ring(field_ring(L), K), minimal_polynomial(L, K, a))",
			By(isSeparable, SeparableOverDef.At(l, K, a)))
		overE := arg.Have(
			"the coefficients also lie in E",
			"polynomial_over(E, minimal_polynomial(L, K, a))",
			By(inclusion, overK, polynomial.PolynomialOverMono.At(arg.TermAs[A]("L.zero"), K, E, p)))
		separableE := arg.Have(
			"separability of the polynomial passes to E",
			"polynomial_separable(restrict_ring(field_ring(L), E), minimal_polynomial(L, K, a))",
			By(
				inclusion,
				separableK,
				module_record.RestrictRingTwice.At(arg.TermAs[module_record.RingOps[A]]("field_ring(L)"), E, K),
				separable_polynomial.SeparableMono.At(
					arg.TermAs[module_record.RingOps[A]]("restrict_ring(field_ring(L), E)"), K, p)))
		arg.Show(
			"the separable annihilator over E makes a separable over E",
			By(subfieldE, overE, vanishes, separableE, SeparableAnnihilator.Read(L).At(E, p, a)))
	}),
})}

// GaloisTower — a Galois extension is Galois over every intermediate
// field.
var GaloisTower = galoisTowerThm{family.Add(registry.ProofEntry{
	Name: "GaloisTower",
	Key:  "prop_8465bcc0ffe0f929",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀K E M:set(A).",
		Hypotheses: []string{
			"subfield(L, K)",
			"subfield(L, E)",
			"subfield(L, M)",
			"K ⊆ E",
			"E ⊆ M",
			"galois_over(L, K, M)",
		},
		Conclusion: "galois_over(L, E, M)",
	}, func(
		arg *Argument,
		L field.FieldFact[on.L],
		K, E, M *Expr[Set[A]],
		subK, subE, subM, kInE, eInM, isGalois Fact,
	) {
		l := arg.TermAs[FieldOps[A]]("L")
		parts := arg.Conjuncts(
			arg.Unfolded(isGalois, GaloisOverDef),
			"M is finite over K",
			"M is normal over K",
			"every member of M is separable over K")
		finiteE := arg.Have(
			"M is finite over the intermediate field E",
			"finite_extension(L, E, M)",
			By(subK, subE, subM, kInE, eInM, parts[0], field_extension.TowerFinite.Read(L).At(K, E, M)))
		normalE := arg.Have(
			"M is normal over E",
			"normal_over(L, E, M)",
			By(subK, subE, subM, kInE, eInM, parts[0], parts[1], NormalTower.Read(L).At(K, E, M)))
		separableE := arg.Have(
			"every member of M is separable over E",
			"∀a:A. a ∈ M ⇒ separable_over(L, E, a)",
			Derive(func(b *Argument) {
				x := b.FixAs[A]("a")
				inM := b.Assume()
				inL := b.Have(
					"a member of M lies in the ambient field",
					"a ∈ L.carrier",
					By(inM, field.SubfieldSubset.Read(subM), set_basic.SubsetDef.At(M, b.TermAs[Set[A]]("L.carrier"))))
				xm := b.MemberOf[on.L](x, inL)
				b.Show(
					"separability passes from K to E at a",
					By(subK, subE, kInE, xm, inM, parts[2].At(x), SeparableTower.Read(L).At(K, E, xm)))
			}))
		arg.Show(
			"finiteness, normality and elementwise separability make M Galois over E",
			By(finiteE, normalE, separableE, GaloisOverDef.At(l, E, M)))
	}),
})}

// ConjugatesCount — in a normal extension, an element separable over K
// has exactly as many conjugates in M, roots there of its minimal
// polynomial, as the degree of that polynomial.
var ConjugatesCount = conjugatesCountThm{family.Add(registry.ProofEntry{
	Name: "ConjugatesCount",
	Key:  "prop_4e957fbac393b2aa",
	Reading: "Normality is load-bearing: in ℚ(∛2) over ℚ, ∛2 has one conjugate against degree three. " +
		"Separability is too: t^(1/p) in F_p(t^(1/p)) over F_p(t) has one conjugate against degree p.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀K M:set(A). ∀a:A.",
		Hypotheses: []string{
			"subfield(L, K)",
			"subfield(L, M)",
			"K ⊆ M",
			"normal_over(L, K, M)",
			"a ∈ M",
			"separable_over(L, K, a)",
		},
		Conclusion: "has_size(polynomial_roots(M, minimal_polynomial(L, K, a)), " +
			"    polynomial_degree(minimal_polynomial(L, K, a)))",
	}, func(
		arg *Argument,
		L field.FieldFact[on.L],
		K, M *Expr[Set[A]],
		a *Member[A, on.M],
		subK, subM, inclusion, normal, isSeparable Fact,
	) {
		l := arg.TermAs[FieldOps[A]]("L")
		p := arg.TermAs[Fun[Nat, A]]("minimal_polynomial(L, K, a)")
		inL := arg.Have(
			"a member of M lies in the ambient field",
			"a ∈ L.carrier",
			By(a, field.SubfieldSubset.Read(subM), set_basic.SubsetDef.At(M, arg.TermAs[Set[A]]("L.carrier"))))
		xm := arg.MemberOf[on.L](&a.Expr, inL)
		scalarField := arg.Have(
			"M is a field under the operations of L",
			"field_on(restrict_field(L, M))",
			By(subM, field.SubfieldFieldOn.Read(L).At(M)))
		algebraic := arg.Have(
			"separability supplies algebraicity over K",
			"algebraic_over(L, K, a)",
			By(isSeparable, SeparableOverDef.At(l, K, a)))
		overK := arg.Have(
			"the minimal polynomial has coefficients in K",
			"polynomial_over(K, minimal_polynomial(L, K, a))",
			By(subK, xm, algebraic, algebraic_element.MinimalPolynomialSpec.Read(L).At(K, xm)))
		separableK := arg.Have(
			"the minimal polynomial is separable over K",
			"polynomial_separable(restrict_ring(field_ring(L), K), minimal_polynomial(L, K, a))",
			By(isSeparable, SeparableOverDef.At(l, K, a)))
		overM := arg.Have(
			"the minimal polynomial also has coefficients in M",
			"polynomial_over(M, minimal_polynomial(L, K, a))",
			By(inclusion, overK, polynomial.PolynomialOverMono.At(arg.TermAs[A]("L.zero"), K, M, p)))
		separableM := arg.Have(
			"separability of the polynomial passes to M",
			"polynomial_separable(restrict_ring(field_ring(L), M), minimal_polynomial(L, K, a))",
			By(
				inclusion,
				separableK,
				module_record.RestrictRingTwice.At(arg.TermAs[module_record.RingOps[A]]("field_ring(L)"), M, K),
				separable_polynomial.SeparableMono.At(
					arg.TermAs[module_record.RingOps[A]]("restrict_ring(field_ring(L), M)"), K, p)))
		splitsM := arg.Have(
			"normality makes the minimal polynomial split over M",
			"polynomial_splits(restrict_ring(field_ring(L), M), minimal_polynomial(L, K, a))",
			By(subK, subM, inclusion, normal, a, algebraic, NormalIffMinimalPolynomial.Read(L).At(K, M)))
		separableAtField := arg.Simplified(separableM, Fwd(field.RestrictFieldRing))
		splitsAtField := arg.Simplified(splitsM, Fwd(field.RestrictFieldRing))
		arg.Show(
			"a separable polynomial split over M has its degree many roots there",
			By(
				overM,
				separableAtField,
				splitsAtField,
				separable_polynomial.SeparableSplitsRoots.Read(scalarField).At(p)))
	}),
})}

// SeparableAnnihilator — a root of a polynomial over a subfield B that is
// separable over B is separable over B: the polynomial is nonzero, being
// separable, so the root is algebraic; its minimal polynomial divides the
// given polynomial, and separability passes to divisors.
var SeparableAnnihilator = separableAnnihilatorThm{family.Add(registry.ProofEntry{
	Name: "SeparableAnnihilator",
	Key:  "prop_65ea952461327120",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀B:set(A). ∀p:(num → A). ∀x:A.",
		Hypotheses: []string{
			"subfield(L, B)",
			"polynomial_over(B, p)",
			"polynomial_separable(restrict_ring(field_ring(L), B), p)",
			"x ∈ L.carrier",
			"polynomial_eval(p, x) = L.zero",
		},
		Conclusion: "separable_over(L, B, x)",
	}, func(
		a *Argument,
		L field.FieldFact[on.L],
		B *Expr[Set[A]],
		p *Arrow[Nat, A],
		x *Member[A, on.L],
		subfieldB, over, separable, root Fact,
	) {
		l := a.TermAs[FieldOps[A]]("L")
		scalarField := a.Have(
			"B is a field under the operations of L",
			"field_on(restrict_field(L, B))",
			By(subfieldB, field.SubfieldFieldOn.Read(L).At(B)))
		nonzero := a.Have(
			"a separable polynomial over a field is nonzero",
			"p ≠ vec_zero",
			By(
				Normalized,
				over,
				separable,
				separable_polynomial.SeparableNonzero.Read(scalarField).At(p),
				field.RestrictFieldRing.At(l, B)))
		algebraic := a.Have(
			"the nonzero annihilating polynomial witnesses algebraicity",
			"algebraic_over(L, B, x)",
			Simp(Fwd(algebraic_element.AlgebraicOverDef)),
			Witness(p),
			By(over, nonzero, root))
		scalars := a.Have(
			"the scalar subfield is a commutative ring",
			"comm_ring_on(restrict_ring(field_ring(L), B))",
			By(subfieldB, field.SubfieldCommRing.Read(L).At(B)))
		a.Show(
			"separability passes from the annihilator to the minimal polynomial",
			By(
				subfieldB,
				over,
				separable,
				x,
				root,
				algebraic,
				algebraic_element.MinimalPolynomialSpec.Read(L).At(B, x),
				algebraic_element.MinimalPolynomialDivides.Read(L).At(B, x, p),
				separable_polynomial.SeparableDivisor.Read(scalars).At(
					a.TermAs[Fun[Nat, A]]("minimal_polynomial(L, B, x)"), p),
				SeparableOverDef.At(l, B, x)))
	}),
})}

// FieldEmbeddingSeparable — a field embedding carries an element separable
// over a subfield to one separable over the image subfield: the
// transported minimal polynomial is a separable polynomial over the image
// subfield vanishing at the image element.
var FieldEmbeddingSeparable = fieldEmbeddingSeparableThm{family.Add(registry.ProofEntry{
	Name: "FieldEmbeddingSeparable",
	Key:  "prop_64368317ea0b5d79",
	Build: family.Theorem(Statement{
		Binders: "∀F:field_on(A). ∀G:field_on(B). ∀ι:(A → B). ∀k:set(A). ∀x:A.",
		Hypotheses: []string{
			"ring_homomorphism(field_ring(F), field_ring(G), ι)",
			"subfield(F, k)",
			"x ∈ F.carrier",
			"separable_over(F, k, x)",
		},
		Conclusion: "separable_over(G, image(ι, k), ι(x))",
	}, func(
		a *Argument,
		F field.FieldFact[on.F],
		G field.FieldFact[on.G],
		ι *Arrow[A, B],
		k *Expr[Set[A]],
		x *Member[A, on.F],
		hom, sourceField, isSeparable Fact,
	) {
		fRecord := a.TermAs[FieldOps[A]]("F")
		gRecord := a.TermAs[FieldOps[B]]("G")
		imageK := a.TermAs[Set[B]]("image(ι, k)")
		p, pDef := a.LetAs[Fun[Nat, A]]("p", "minimal_polynomial(F, k, x)")
		q, qDef := a.LetAs[Fun[Nat, B]]("q", "λi:num. ι(p(i))")
		algebraic := a.Have(
			"separability supplies algebraicity",
			"algebraic_over(F, k, x)",
			By(isSeparable, SeparableOverDef.At(fRecord, k, x)))
		sourcePolynomial := a.Have(
			"the source minimal polynomial is a separable annihilator over k",
			"polynomial_over(k, p) ∧ "+
				"polynomial_eval(p, x) = F.zero ∧ "+
				"polynomial_separable(restrict_ring(field_ring(F), k), p)",
			By(
				pDef,
				sourceField,
				x,
				algebraic,
				isSeparable,
				algebraic_element.MinimalPolynomialSpec.Read(F).At(k, x),
				SeparableOverDef.At(fRecord, k, x)))
		targetField := a.Have(
			"the image scalar field is a subfield",
			"subfield(G, image(ι, k))",
			By(F, G, hom, sourceField, algebraic_element.FieldEmbeddingSubfieldsAdjoin.At(fRecord, gRecord, ι)))
		fRing := a.TermAs[module_record.RingOps[A]]("field_ring(F)")
		gRing := a.TermAs[module_record.RingOps[B]]("field_ring(G)")
		onK := a.Have(
			"ι restricts to the subfield k of its source",
			"ring_homomorphism(restrict_ring(field_ring(F), k), field_ring(G), ι)",
			By(
				hom,
				field.SubfieldSubring.Read(F).At(k),
				sourceField,
				ring_homomorphism.RingHomRestrictSource.At(fRing, gRing, ι, k)))
		restricted := a.Have(
			"its values on k lie in the subfield image(ι, k), so it maps k into that subfield",
			"ring_homomorphism(restrict_ring(field_ring(F), k), restrict_ring(field_ring(G), image(ι, k)), ι)",
			By(
				onK,
				targetField,
				field.SubfieldSubring.Read(G).At(imageK),
				At(set_image.FunInImage, ι, k),
				ring_homomorphism.RingHomCorestrict.At(
					a.TermAs[module_record.RingOps[A]]("restrict_ring(field_ring(F), k)"),
					gRing,
					ι,
					imageK)))
		separableImage := a.Have(
			"moving the coefficients of p along ι keeps it separable",
			"polynomial_separable(restrict_ring(field_ring(G), image(ι, k)), q)",
			qDef.Rw(),
			By(
				restricted,
				sourcePolynomial,
				separable_polynomial.SeparableCoefficientMap.At(
					a.TermAs[module_record.RingOps[A]]("restrict_ring(field_ring(F), k)"),
					a.TermAs[module_record.RingOps[B]]("restrict_ring(field_ring(G), image(ι, k))"),
					ι,
					p)))
		transportedPolynomial := a.Have(
			"the transported polynomial keeps the coefficient field and evaluation",
			"polynomial_over(image(ι, k), q) ∧ ι(polynomial_eval(p, x)) = polynomial_eval(q, ι(x))",
			qDef.Rw(),
			By(
				F,
				G,
				hom,
				sourceField,
				sourcePolynomial,
				x,
				algebraic_element.FieldEmbeddingPolynomials.At(fRecord, gRecord, ι, k, p)))
		imagePoint := a.Have(
			"the image element belongs to the target carrier",
			"ι(x) ∈ G.carrier",
			By(x, ring_homomorphism.MapIn.Read(hom)))
		evaluatesZero := a.Have(
			"the transported polynomial annihilates the image element",
			"polynomial_eval(q, ι(x)) = G.zero",
			By(ring_homomorphism.MapZero.Read(hom), sourcePolynomial, transportedPolynomial))
		imageMember := a.MemberOf[on.G](a.TermAs[B]("ι(x)"), imagePoint)
		a.Show(
			"the separable annihilator makes the image element separable",
			By(
				targetField,
				transportedPolynomial,
				separableImage,
				evaluatesZero,
				SeparableAnnihilator.Read(G).At(imageK, q, imageMember)))
	}),
})}
