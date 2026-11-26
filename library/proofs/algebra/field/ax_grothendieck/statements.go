package ax_grothendieck

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_closure"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/finite_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/lefschetz"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_algebra"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_encoding"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// AxPropertyDef — The degree-bounded polynomial injective-implies-surjective statement.
var AxPropertyDef = axPropertyDefThm{family.Define(registry.DefEntry{
	Name: "AxPropertyDef", Const: "ax_property", Type: "field_ops(A) → num → num → bool",
	Key: "prop_c3a2a5605fced234",
	Reading: "Every coefficient of the map is universally quantified, so at a fixed dimension and " +
		"degree the property is a closed sentence of the field language, the form elementarity transfers.",
	Equations: []string{
		"∀F:field_ops(A). ∀n d:num. " +
			"    ax_property(F, n, d) ⇔ " +
			"    ∀P:(num → (num → num) → A). " +
			"        (∀j:num. j < n ⇒ polynomial_bound(field_ring(F), n, d, P(j))) ∧ " +
			"        polynomial_map_injective(field_ring(F), n, P) ⇒ " +
			"        polynomial_map_surjective(field_ring(F), n, P)",
	},
})}

// LocallyFiniteSource — over a locally finite field an injective polynomial self-map of n-space of
// degree at most d is surjective: the finitely many coefficients of the map and the coordinates of
// a target point lie in a finite subfield K, the map sends the finitely many n-tuples of K to
// n-tuples of K and separates them, so it reaches every one of them, the target among them.
var LocallyFiniteSource = locallyFiniteSourceThm{family.Add(registry.ProofEntry{
	Name: "LocallyFiniteSource",
	Key:  "prop_ad10856dd05398e1",
	Build: family.Theorem(Statement{
		Binders: "∀F:field_ops(A). ∀n d:num.",
		Hypotheses: []string{
			"locally_finite_field(F)",
		},
		Conclusion: "ax_property(F, n, d)",
	}, func(a *Argument, F *Expr[FieldOps[A]], n, d *Expr[Nat], locallyFinite Fact) {
		local := a.Conjuncts(
			a.Unfolded(locallyFinite, finite_field.LocallyFiniteFieldDef),
			"F is a field",
			"every finite set of elements of F lies in a finite subfield")
		fieldF, finiteSubfields := local[0], local[1]
		R := a.TermAs[module_record.RingOps[A]]("field_ring(F)")
		indices := a.TermAs[Set[Nat]]("{i:num | i < n}")
		a.Do(Unfold(AxPropertyDef))
		P := a.FixAs[Fun2[Nat, Fun[Nat, Nat], A]]("P")
		given := a.Conjuncts(
			a.Assume(),
			"each P(j) is a polynomial in the variables below n of degree at most d",
			"P separates the n-tuples of F")
		bounded, injective := given[0], given[1]
		a.Do(Unfold(polynomial_encoding.PolynomialMapSurjectiveDef))
		y := a.VecFixAs[A, DimN]("y")
		target := a.Assume()
		coefficients := a.Have(
			"every coefficient of each P(j) lies in F",
			"∀j:num. ∀m:(num → num). j < n ⇒ P(j, m) ∈ F.carrier",
			By(bounded, polynomial_encoding.PolynomialBoundDef, polynomial_algebra.PolynomialAlgebraMember))
		C, CDef := a.LetAs[Set[A]](
			"C",
			"{P(j, m) | j:num, m:(num → num) | j < n ∧ m ∈ bounded_monomials(n, d)} ∪ "+
				"image(y, {i:num | i < n})")
		finiteC := a.Have(
			"C is finite: n polynomials with coefficients on "+
				"finitely many monomials each, and the n coordinates of y",
			"finite(C)",
			By(
				CDef,
				num_segment.FiniteBelowStrict.At(n),
				polynomial_encoding.BoundedMonomialsFinite.At(n, d),
				finite_set.FiniteProductDependent.At(
					P,
					indices,
					a.TermAs[Fun2[Nat, Fun[Nat, Nat], Bool]]("λj:num. bounded_monomials(n, d)")),
				finite_set.FiniteImage.At(y, indices),
				finite_set.FiniteUnionImp))
		inF := a.Have(
			"C lies in F",
			"C ⊆ F.carrier",
			BySets(CDef, coefficients, target, polynomial_encoding.RingTupleDef))
		K, extension := a.UnpackAs[Set[A]](GroupPremises(finiteC, inF, finiteSubfields.At(C)), "K")
		ofK := a.Conjuncts(
			extension,
			"K is a subfield of F",
			"K is finite",
			"K contains C")
		subfieldK, finiteK, CinK := ofK[0], ofK[1], ofK[2]
		RK := a.TermAs[module_record.RingOps[A]]("restrict_ring(field_ring(F), K)")
		coefficientsK := a.Have(
			"every coefficient of each P(j) lies in K",
			"∀j:num. ∀m:(num → num). j < n ⇒ P(j, m) ∈ K",
			Derive(func(b *Argument) {
				j := b.FixAs[Nat]("j")
				b.FixAs[Fun[Nat, Nat]]("m")
				below := b.Assume()
				b.Cases(b.Term("m ∈ bounded_monomials(n, d)"))
				b.When(
					"on a monomial of degree at most d the coefficient is a member of C",
					func(c *Argument, onBox Fact) {
						c.Show(
							"and C lies in K",
							BySets(below, onBox, CDef, CinK))
					})
				b.Otherwise(
					"off those monomials P(j) vanishes, and K holds zero",
					func(c *Argument, offBox Fact) {
						c.Show(
							"the support of P(j) lies among the monomials of degree at most d",
							By(
								offBox,
								below,
								bounded.At(j),
								polynomial_encoding.PolynomialBoundDef.At(R, n, d, c.TermAs[Fun[Fun[Nat, Nat], A]]("P(j)")),
								field.SubfieldZero.Read(subfieldK),
								set_basic.SubsetDef))
					})
			}))
		overK := a.Have(
			"so each P(j) is a polynomial over K",
			"∀j:num. j < n ⇒ P(j) ∈ polynomial_algebra(restrict_ring(field_ring(F), K), {i:num | i < n})",
			Derive(func(b *Argument) {
				j := b.FixAs[Nat]("j")
				below := b.Assume()
				p := b.TermAs[Fun[Fun[Nat, Nat], A]]("P(j)")
				b.Show(
					"its coefficients lie in K, and its support is that of a polynomial over F",
					By(
						below,
						coefficientsK.At(j),
						bounded.At(j),
						polynomial_encoding.PolynomialBoundDef.At(R, n, d, p),
						polynomial_algebra.PolynomialAlgebraMember.At(R, indices, p),
						polynomial_algebra.PolynomialAlgebraMember.At(RK, indices, p)))
			}))
		T, TDef := a.LetAs[Set[Fun[Nat, A]]](
			"T", "{x:num → A | ring_tuple(restrict_ring(field_ring(F), K), n, x)}")
		finiteT := a.Have(
			"K, being finite, has finitely many n-tuples",
			"finite(T)",
			By(finiteK, TDef, polynomial_encoding.RingTuplesFinite.At(RK, n)))
		maps := a.Have(
			"P, its coefficients lying in the subring K, sends n-tuples of K to n-tuples of K",
			Statement{
				Binders: "∀x:(num → A).",
				Hypotheses: []string{
					"ring_tuple(restrict_ring(field_ring(F), K), n, x)",
				},
				Conclusion: "ring_tuple(restrict_ring(field_ring(F), K), " +
					"    n, " +
					"    polynomial_map(field_ring(F), n, P, x))",
			},
			By(
				overK,
				subfieldK,
				field.RingOn.Read(fieldF),
				field.SubfieldSubring.Read(fieldF).At(K),
				polynomial_encoding.PolynomialMapSubring))
		stable := a.Have(
			"so P maps T into itself",
			"image(polynomial_map(field_ring(F), n, P), T) ⊆ T",
			BySets(TDef, maps))
		tuplesF := a.Have(
			"an n-tuple of K is an n-tuple of F",
			"∀x:(num → A). ring_tuple(restrict_ring(field_ring(F), K), n, x) ⇒ ring_tuple(field_ring(F), n, x)",
			By(subfieldK, polynomial_encoding.RingTupleDef, field.SubfieldSubset, set_basic.SubsetDef))
		separates := a.Have(
			"P separates the points of T, as it separates the n-tuples of F",
			"injective_on(T, polynomial_map(field_ring(F), n, P))",
			Unfold(functions.InjectiveOnDef),
			Derive(func(b *Argument) {
				u := b.FixAs[Fun[Nat, A]]("u")
				v := b.FixAs[Fun[Nat, A]]("v")
				same := b.Assume()
				b.Show(
					"u and v are n-tuples of F with one image",
					BySets(
						same,
						TDef,
						tuplesF.At(u),
						tuplesF.At(v),
						injective,
						polynomial_encoding.PolynomialMapInjectiveDef.At(R, n, P)))
			}))
		yInT := a.Have(
			"the coordinates of y lie in C, so in K, and y is a point of T",
			"y ∈ T",
			BySets(
				CDef,
				CinK,
				TDef,
				target,
				polynomial_encoding.RingTupleDef.At(R, y),
				polynomial_encoding.RingTupleDef.At(RK, y)))
		x, preimage := a.ObtainAs[Fun[Nat, A]](
			"a self-map of the finite set T that separates its points is onto, so y has a preimage in T",
			"∃x:num → A. x ∈ T ∧ polynomial_map(field_ring(F), n, P, x) = y",
			By(
				finiteT,
				stable,
				separates,
				yInT,
				cardinality.SurjectiveIffInjective.At(
					T,
					a.TermAs[Fun[Fun[Nat, A], Fun[Nat, A]]]("polynomial_map(field_ring(F), n, P)"))))
		a.Take(x)
		a.Show(
			"the preimage is an n-tuple of K, so of F",
			BySets(preimage, TDef, tuplesF.At(x)))
	}),
})}

// _ClosurePoint is a point of the closure host, the one type in which
// lefschetz.PrimeClosureLocallyFinite finds a model of every prime characteristic. One type serves
// every prime because lefschetz.PrimeFamilyTransfer reads a family of models of one type B: the
// stability bound is fixed first; only then are a prime past it and its model chosen.
type _ClosurePoint = Set[Prod[Nat, Fun[Nat, Set[Int]]]]

// AlgebraicallyClosedAxProperty — over an algebraically closed field, an injective polynomial
// self-map of n-space of degree at most d is surjective: the property holds in a locally finite
// closure of each prime characteristic, and as a closed sentence true in a model of every prime
// characteristic it holds in every algebraically closed field (lefschetz.PrimeFamilyTransfer).
var AlgebraicallyClosedAxProperty = algebraicallyClosedAxPropertyThm{family.Add(registry.ProofEntry{
	Name: "AlgebraicallyClosedAxProperty",
	Key:  "prop_c01981c926b5e38a",
	Build: family.Theorem(Statement{
		Binders: "∀F:field_ops(A). ∀n d:num.",
		Hypotheses: []string{
			"algebraically_closed_field_on(F)",
		},
		Conclusion: "ax_property(F, n, d)",
	}, func(
		a *Argument,
		F *Expr[FieldOps[A]],
		n, d *Expr[Nat],
		closedF algebraic_closure.AlgebraicallyClosedFieldFact[on.F],
	) {
		models := a.Have(
			"each prime characteristic has an algebraically closed field in the host with the Ax property",
			Statement{
				Binders: "∀p:num.",
				Hypotheses: []string{
					"nat_prime(p)",
				},
				Conclusion: "∃G:field_ops(set(prod(num, num → set(int)))). " +
					"    algebraically_closed_field_on(G) ∧ field_characteristic(G, p) ∧ ax_property(G, n, d)",
			},
			Derive(func(b *Argument) {
				p := b.FixAs[Nat]("p")
				prime := b.Assume()
				G, source := b.UnpackAs[FieldOps[_ClosurePoint]](
					GroupPremises(prime, lefschetz.PrimeClosureLocallyFinite.At(p)), "G")
				property := b.Have(
					"G is locally finite, so its injective polynomial self-maps of degree at most d are onto",
					"ax_property(G, n, d)",
					By(source, LocallyFiniteSource.At(G, n, d)))
				b.Take(G)
				b.Show(
					"G is algebraically closed of characteristic p and has the property",
					By(source, property))
			}))
		a.Show(
			"the property, a closed sentence true in the models of every prime characteristic, holds in F",
			ByElementarity(models, closedF))
	}),
})}

// AxGrothendieck — every injective polynomial self-map of finite-dimensional affine space over an
// algebraically closed field is surjective: P's coordinates have a common degree bound d, and
// AlgebraicallyClosedAxProperty, where the transfer happens, gives ax_property at d, of which P is
// an instance.
var AxGrothendieck = axGrothendieckThm{family.Add(registry.ProofEntry{
	Name: "AxGrothendieck",
	Key:  "prop_474ab10cb4af08c3",
	Reading: "Zero padding makes equality of total functions agree " +
		"with coordinate equality below n; dimension zero has one tuple.",
	Build: family.Theorem(Statement{
		Binders: "∀F:field_ops(A). ∀n:num. ∀P:(num → (num → num) → A).",
		Hypotheses: []string{
			"algebraically_closed_field_on(F)",
			"∀j:num. j < n ⇒ P(j) ∈ polynomial_algebra(field_ring(F), {v:num | v < n})",
			"polynomial_map_injective(field_ring(F), n, P)",
		},
		Conclusion: "polynomial_map_surjective(field_ring(F), n, P)",
	}, func(a *Argument, F *Expr[FieldOps[A]], n *Expr[Nat], P *Expr[Fun2[Nat, Fun[Nat, Nat], A]],
		closedF, polynomials, injective Fact) {
		R := a.TermAs[module_record.RingOps[A]]("field_ring(F)")
		d, bounded := a.UnpackAs[Nat](
			GroupPremises(polynomials, polynomial_encoding.CommonDegreeBound.At(R, n, n, P)))
		property := a.Have(
			"injective polynomial self-maps of F of degree at most d are onto",
			"ax_property(F, n, d)",
			By(closedF, AlgebraicallyClosedAxProperty.At(F, n, d)))
		a.Show(
			"P is one of them",
			By(bounded, injective, property, AxPropertyDef.At(F, n, d)))
	}),
})}
