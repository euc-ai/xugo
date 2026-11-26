// root_field_galois.go — the field a separable family of split polynomials generates is Galois.

package galois_correspondence

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_automorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_extension"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/symmetric_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/algebra_points"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_domain"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_evaluation"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_roots"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/separable_polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// SeparableRootFieldGalois — adjoining to a subfield K of L every root of
// finitely many separable polynomials over K that split in L gives a Galois
// extension M of K: the embeddings of M into L fixing K, each a map extended
// by zero (vanishing off its domain), are counted one generator at a time,
// each generator a extending an embedding of the field E before it in as many
// ways as the degree of a over E, since its transported minimal polynomial
// divides a separable polynomial that splits, so is separable and splits; so
// M has as many embeddings as its degree over K. Each embedding sends roots
// to roots, so it maps M into M, and onto M since it is injective and
// K-linear and M is finite over K; extended by the identity it is an
// automorphism of M over K. M therefore has as many automorphisms over K as
// its degree, which makes it Galois over K.
var SeparableRootFieldGalois = separableRootFieldGaloisThm{family.Add(registry.ProofEntry{
	Name: "SeparableRootFieldGalois",
	Key:  "prop_7987c7a48bce6867",
	Build: family.Sections(Statement{
		Binders: "∀L:field_on(A). ∀K:set(A). ∀P:set(num → A).",
		Hypotheses: []string{
			"subfield(L, K)",
			"finite(P)",
			"∀p:(num → A). " +
				"    p ∈ P ⇒ " +
				"    polynomial_over(K, p) ∧ " +
				"    polynomial_separable(restrict_ring(field_ring(L), K), p) ∧ " +
				"    polynomial_splits(field_ring(L), p)",
		},
		Conclusion: "galois_over(L, K, «rootField»)",
		Abbrev: Abbrev{
			{Name: "roots", Text: "{x:A | " +
				"    x ∈ L.carrier ∧ (∃p:(num → A). p ∈ P ∧ polynomial_eval(p, x) = L.zero)}"},
			{Name: "rootField", Text: "field_adjoin(L, K, «roots»)"},
		},
	},
		func(ctx *Script, headline string) *GoalStackNode {
			// An embedding of E(a), extended by zero, is determined by its values on E and at a.
			simpleEmbeddingUnique := ctx.Lemma(Statement{
				Binders: "∀L:field_on(A). ∀E:set(A). ∀a:A. ∀g h:(A → A).",
				Hypotheses: []string{
					"subfield(L, E)",
					"a ∈ L.carrier",
					"algebraic_over(L, E, a)",
					"ring_homomorphism(restrict_ring(field_ring(L), field_adjoin(L, E, {a})), field_ring(L), g)",
					"ring_homomorphism(restrict_ring(field_ring(L), field_adjoin(L, E, {a})), field_ring(L), h)",
					"∀x:A. x ∈ E ⇒ g(x) = h(x)",
					"g(a) = h(a)",
					"∀x:A. x ∉ field_adjoin(L, E, {a}) ⇒ g(x) = L.zero",
					"∀x:A. x ∉ field_adjoin(L, E, {a}) ⇒ h(x) = L.zero",
				},
				Conclusion: "g = h",
			}, func(
				arg *Argument,
				L field.FieldFact[on.L],
				E *Expr[Set[A]],
				a *Expr[A],
				g *Arrow[A, A],
				h *Arrow[A, A],
				eField, aIn, aAlgebraic, gHom, hHom, agreeOnE, agreeAtA, gVanishes, hVanishes Fact,
			) {
				D, DDef := arg.LetAs[Set[A]]("D", "field_adjoin(L, E, {a})")
				aMember := arg.MemberOf[on.L](a, aIn)
				simpleField := arg.Have(
					"the simple adjunction is a field containing its base and generator",
					"subfield(L, D) ∧ E ⊆ D ∧ a ∈ D",
					By(Normalized, DDef, eField, algebraic_element.AdjoinElementSubfield.Read(L).At(E, aMember)))
				sameCoefficients := arg.Have(
					"the two embeddings agree on all polynomial coefficients",
					"∀p:(num → A). polynomial_over(E, p) ⇒ (λi:num. g(p(i))) = λi:num. h(p(i))",
					Derive(func(b *Argument) {
						p := b.FixAs[Fun[Nat, A]]("p")
						pOver := b.Assume()
						b.Do(Funext())
						b.FixAs[Nat]("i")
						b.Do(By(
							At(agreeOnE, b.TermAs[A]("p(i)")),
							pOver,
							polynomial.PolynomialOverDef.At(b.TermAs[A]("L.zero"), E, p)))
					}))
				sameEvaluations := arg.Have(
					"the two embeddings agree on every polynomial evaluation at the generator",
					"∀p:(num → A). polynomial_over(E, p) ⇒ g(polynomial_eval(p, a)) = h(polynomial_eval(p, a))",
					Derive(func(b *Argument) {
						p := b.FixAs[Fun[Nat, A]]("p")
						pOver := b.Assume()
						commute := b.Have(
							"g and h commute with evaluation at a",
							"g(polynomial_eval(p, a)) = polynomial_eval(λi:num. g(p(i)), g(a)) ∧ "+
								"h(polynomial_eval(p, a)) = polynomial_eval(λi:num. h(p(i)), h(a))",
							By(
								simpleField,
								pOver,
								polynomial.PolynomialOverMono.At(b.TermAs[A]("L.zero"), E, D, p),
								polynomial_evaluation.EvalAlongHomomorphism.Read(gHom).AsFact().At(p, a),
								polynomial_evaluation.EvalAlongHomomorphism.Read(hHom).AsFact().At(p, a)))
						coefficientEquality := b.Have(
							"the transported coefficient functions agree",
							"(λi:num. g(p(i))) = λi:num. h(p(i))",
							By(At(sameCoefficients, p), pOver))
						b.Show(
							"replace the coefficients and the value at a under g by those under h",
							Derive(func(c *Argument) {
								c.Do(coefficientEquality.Rw())
								c.Do(agreeAtA.Rw())
								c.Do(By(commute))
							}))
					}))
				arg.Show(
					"compare g and h at each point, on and off D",
					Derive(func(b *Argument) {
						b.Do(Funext())
						b.FixAs[A]("x")
						b.Cases(b.TermAs[Bool]("x ∈ D"))
						b.When(
							"x lies in D, the polynomial image of a over E",
							func(c *Argument, inD Fact) {
								simpleFieldImage := c.Have(
									"the simple algebraic adjunction is the polynomial image",
									"D = polynomial_image(field_ring(L), E, a)",
									By(Normalized, DDef, eField, aAlgebraic, algebraic_element.AdjoinEqImage.Read(L).At(E, aMember)))
								p, representation := c.ObtainAs[Fun[Nat, A]](
									"write x as p(a) for a polynomial p over E",
									"∃p:(num → A). polynomial_over(E, p) ∧ x = polynomial_eval(p, a)",
									BySets(
										simpleFieldImage,
										inD,
										algebraic_element.PolynomialImageDef.At(c.TermAs[comm_ring.RingOps[A]]("field_ring(L)"), E, a)))
								c.Show(
									"g and h agree on p(a)",
									By(Normalized, At(sameEvaluations, p), representation))
							})
						b.Otherwise(
							"x lies off D, where g and h both vanish",
							func(c *Argument, outside Fact) {
								c.Do(By(Normalized, outside, gVanishes, hVanishes))
							})
					}))
			})

			transportRoot := ctx.Lemma(Statement{
				Binders: "∀L:field_on(A). ∀E D:set(A). ∀f g:(A → A). ∀a:A. ∀p:(num → A).",
				Hypotheses: []string{
					"E ⊆ D",
					"a ∈ D",
					"ring_homomorphism(restrict_ring(field_ring(L), D), field_ring(L), g)",
					"∀c:A. c ∈ E ⇒ g(c) = f(c)",
					"polynomial_over(E, p)",
					"polynomial_eval(p, a) = L.zero",
				},
				Conclusion: "g(a) ∈ L.carrier ∧ polynomial_eval(λi:num. f(p(i)), g(a)) = L.zero",
			}, func(
				arg *Argument,
				L field.FieldFact[on.L],
				E *Expr[Set[A]],
				D *Expr[Set[A]],
				f *Arrow[A, A],
				g *Arrow[A, A],
				a *Expr[A],
				p *Arrow[Nat, A],
				nested, aInD, gHom, agrees, pOver, aRoot Fact,
			) {
				transportCoefficients := arg.Have(
					"the larger embedding agrees with the prescribed coefficient map",
					"(λi:num. g(p(i))) = λi:num. f(p(i))",
					Derive(func(b *Argument) {
						b.Do(Funext())
						b.FixAs[Nat]("i")
						b.Do(By(
							At(agrees, b.TermAs[A]("p(i)")),
							pOver,
							polynomial.PolynomialOverDef.At(b.TermAs[A]("L.zero"), E, p)))
					}))
				aMember := arg.MemberOf[on.Any](a, aInD)
				gRoot := arg.Have(
					"g(a) lies in L and is a root of g applied to p",
					"g(a) ∈ L.carrier ∧ polynomial_eval(λi:num. g(p(i)), g(a)) = L.zero",
					By(
						ring_homomorphism.MapZero.Read(gHom),
						nested,
						pOver,
						aRoot,
						polynomial.PolynomialOverMono.At(arg.TermAs[A]("L.zero"), E, D, p),
						polynomial_evaluation.EvalAlongHomomorphism.Read(gHom).At(p, aMember),
						ring_homomorphism.MapIn.Read(gHom).At(aMember)))
				arg.Show(
					"replace g by f on the coefficients of p",
					Derive(func(b *Argument) {
						b.Do(transportCoefficients.Rw())
						b.Do(By(gRoot))
					}))
			})

			// The transported minimal polynomial divides the original separable polynomial, which splits, so its conjugates are counted by its degree.
			conjugateCount := ctx.Lemma(Statement{
				Binders: "∀L:field_on(A). ∀K E:set(A). ∀f:(A → A). ∀a:A. ∀p:(num → A).",
				Hypotheses: []string{
					"subfield(L, K)",
					"subfield(L, E)",
					"K ⊆ E",
					"ring_homomorphism(restrict_ring(field_ring(L), E), field_ring(L), f)",
					"∀x:A. x ∈ K ⇒ f(x) = x",
					"a ∈ L.carrier",
					"algebraic_over(L, E, a)",
					"polynomial_over(K, p)",
					"polynomial_separable(restrict_ring(field_ring(L), K), p)",
					"polynomial_splits(field_ring(L), p)",
					"polynomial_eval(p, a) = L.zero",
				},
				Conclusion: "has_size(polynomial_roots(L.carrier, λi:num. f(minimal_polynomial(L, E, a, i))), " +
					"    polynomial_degree(minimal_polynomial(L, E, a)))",
			}, func(
				arg *Argument,
				L field.FieldFact[on.L],
				K *Expr[Set[A]],
				E *Expr[Set[A]],
				f *Arrow[A, A],
				a *Expr[A],
				p *Arrow[Nat, A],
				kField, eField, nested, hom, fixesK, aIn, aAlgebraic, pOver, pSeparable, pSplits, aRoot Fact,
			) {
				_, qDef := arg.LetAs[Fun[Nat, A]]("q", "minimal_polynomial(L, E, a)")
				Q, QDef := arg.LetAs[Fun[Nat, A]]("Q", "λi:num. f(q(i))")
				transported := arg.Have(
					"Q is a polynomial over L of the degree of q that divides p",
					"polynomial_over(L.carrier, Q) ∧ "+
						"polynomial_degree(Q) = polynomial_degree(q) ∧ "+
						"polynomial_divides(field_ring(L), Q, p)",
					By(
						QDef,
						qDef,
						eField,
						nested,
						hom,
						fixesK,
						aAlgebraic,
						pOver,
						aRoot,
						algebraic_element.TransportedMinimalPolynomial.Read(L).At(K, E, f, arg.MemberOf[on.L](a, aIn), p)))
				transportSeparable := arg.Have(
					"the transported minimal polynomial is separable",
					"polynomial_separable(field_ring(L), Q)",
					By(
						pSeparable,
						kField,
						transported,
						field.SubfieldSubset.At(arg.TermAs[FieldOps[A]]("L"), K),
						separable_polynomial.SeparableMono.At(arg.TermAs[comm_ring.RingOps[A]]("field_ring(L)"), K, p),
						separable_polynomial.SeparableDivisor.Read(field.RingOn.Read(L)).At(Q, p)))
				arg.Show(
					"Q splits in L with distinct roots, as many as its degree",
					By(
						Normalized,
						pSplits,
						transportSeparable,
						transported,
						separable_polynomial.SplitsDivisor.Read(field.RingOn.Read(L)).At(Q, p),
						separable_polynomial.SeparableSplitsRoots.Read(L).At(Q)))
			})

			// Evaluation at the generator identifies an extension fiber with its conjugate root set.
			extensionFiberCount := ctx.Lemma(Statement{
				Binders: "∀L:field_on(A). ∀K E:set(A). ∀f:(A → A). ∀a:A. ∀p:(num → A).",
				Hypotheses: []string{
					"subfield(L, K)",
					"subfield(L, E)",
					"K ⊆ E",
					"ring_homomorphism(restrict_ring(field_ring(L), E), field_ring(L), f)",
					"∀x:A. x ∈ K ⇒ f(x) = x",
					"a ∈ L.carrier",
					"algebraic_over(L, E, a)",
					"polynomial_over(K, p)",
					"polynomial_separable(restrict_ring(field_ring(L), K), p)",
					"polynomial_splits(field_ring(L), p)",
					"polynomial_eval(p, a) = L.zero",
				},
				Conclusion: "has_size( " +
					"    algebra_points(restrict_ring(field_ring(L), field_adjoin(L, E, {a})), field_ring(L), E, f), " +
					"    polynomial_degree(minimal_polynomial(L, E, a)))",
			}, func(
				arg *Argument,
				L field.FieldFact[on.L],
				K *Expr[Set[A]],
				E *Expr[Set[A]],
				f *Arrow[A, A],
				a *Expr[A],
				p *Arrow[Nat, A],
				kField, eField, nested, hom, fixesK, aIn, aAlgebraic, pOver, pSeparable, pSplits, aRoot Fact,
			) {
				D, DDef := arg.LetAs[Set[A]]("D", "field_adjoin(L, E, {a})")
				q, qDef := arg.LetAs[Fun[Nat, A]]("q", "minimal_polynomial(L, E, a)")
				_, QDef := arg.LetAs[Fun[Nat, A]]("Q", "λi:num. f(q(i))")
				_, RDef := arg.LetAs[Set[A]]("R", "polynomial_roots(L.carrier, Q)")
				S, pointsDef := arg.LetAs[Set[Fun[A, A]]](
					"S", "algebra_points(restrict_ring(field_ring(L), D), field_ring(L), E, f)")
				SDef := arg.Simplified(pointsDef, Fwd(algebra_points.AlgebraPointsDef))
				aMember := arg.MemberOf[on.L](a, aIn)
				conjugateSize := arg.Have(
					"the transported minimal polynomial has as many roots as its degree",
					"has_size(R, polynomial_degree(q))",
					By(
						L,
						RDef,
						QDef,
						qDef,
						kField,
						eField,
						nested,
						hom,
						fixesK,
						aIn,
						aAlgebraic,
						pOver,
						pSeparable,
						pSplits,
						aRoot,
						At(conjugateCount, arg.TermAs[FieldOps[A]]("L"), K, E, f, a, p)))
				simpleExtensionData := arg.Have(
					"the simple extension contains E and the generator satisfies its minimal polynomial",
					"subfield(L, D) ∧ E ⊆ D ∧ a ∈ D ∧ polynomial_over(E, q) ∧ polynomial_eval(q, a) = L.zero",
					By(
						Normalized,
						DDef,
						qDef,
						eField,
						aAlgebraic,
						algebraic_element.AdjoinElementSubfield.Read(L).At(E, aMember),
						algebraic_element.MinimalPolynomialSpec.Read(L).At(E, aMember)))
				generatorImages := arg.Have(
					"every extension embedding sends the generator to a conjugate",
					"∀g:(A → A). g ∈ S ⇒ g(a) ∈ R",
					Derive(func(b *Argument) {
						g := b.FixAs[Fun[A, A]]("g")
						inS := b.Assume()
						b.Do(BySets(
							L,
							b.Unfolded(RDef, polynomial_roots.PolynomialRootsDef),
							SDef,
							QDef,
							inS,
							simpleExtensionData,
							At(transportRoot, b.TermAs[FieldOps[A]]("L"), E, D, f, g, a, q)))
					}))
				conjugatesRealized := arg.Have(
					"every conjugate is the image of the generator under an extension embedding",
					"∀b:A. b ∈ R ⇒ ∃g:(A → A). g ∈ S ∧ g(a) = b",
					Derive(func(b *Argument) {
						conjugate := b.FixAs[A]("b")
						fieldL := b.TermAs[FieldOps[A]]("L")
						inR := b.Assume()
						chosenConjugate := b.Have(
							"the chosen conjugate lies in the ambient field and satisfies the transported minimal polynomial",
							"b ∈ L.carrier ∧ polynomial_eval(λi:num. f(minimal_polynomial(L, E, a, i)), b) = L.zero",
							BySets(b.Unfolded(RDef, polynomial_roots.PolynomialRootsDef), QDef, qDef, inR))
						g, extension := b.ObtainAs[Fun[A, A]](
							"extend f to some g on D sending a to b",
							"∃g:(A → A). "+
								"    ring_homomorphism(restrict_ring(field_ring(L), D), field_ring(L), g) ∧ "+
								"    (∀x:A. x ∈ E ⇒ g(x) = f(x)) ∧ "+
								"    g(a) = b",
							By(
								L,
								DDef,
								eField,
								hom,
								aAlgebraic,
								chosenConjugate,
								algebraic_element.AdjoinEmbeddingAtRoot.Read(L).At(fieldL, E, f, aMember, conjugate)))
						h, hDef := b.LetAs[Fun[A, A]]("h", "λx:A. COND(x ∈ D, g(x), L.zero)")
						hValues := b.Have(
							"h has the values of g on D, so of f on E and b at a, and vanishes off D",
							"(∀x:A. x ∈ D ⇒ h(x) = g(x)) ∧ "+
								"(∀x:A. x ∈ E ⇒ h(x) = f(x)) ∧ "+
								"h(a) = b ∧ "+
								"(∀x:A. x ∉ D ⇒ h(x) = L.zero)",
							BySets(hDef, extension, simpleExtensionData))
						carrierD := b.Have(
							"the restriction to D has carrier D",
							"restrict_ring(field_ring(L), D).carrier = D",
							Simp(Fwd(module_record.RestrictRingDef), Fwd(module_record.RingCarrierDef)),
							Basic())
						hHom := b.Have(
							"the homomorphism g carries over to h, which agrees with it on D",
							"ring_homomorphism(restrict_ring(field_ring(L), D), field_ring(L), h)",
							By(
								extension,
								hValues,
								carrierD,
								ring_homomorphism.RingHomCongruence.At(
									b.TermAs[comm_ring.RingOps[A]]("restrict_ring(field_ring(L), D)"),
									b.TermAs[comm_ring.RingOps[A]]("field_ring(L)"),
									g,
									h)))
						b.Show(
							"h lies in S and sends a to b",
							Derive(func(c *Argument) {
								c.Take(h)
								c.Do(BySets(SDef, hValues, hHom))
							}))
					}))
				evaluationOntoRoots := arg.Have(
					"evaluation at the generator covers the conjugate root set",
					"image(λg:(A → A). g(a), S) = R",
					BySets(conjugatesRealized, generatorImages))
				evaluationUnique := arg.Have(
					"two extension embeddings with the same generator image are equal",
					"∀g h:(A → A). g ∈ S ∧ h ∈ S ∧ g(a) = h(a) ⇒ g = h",
					Derive(func(b *Argument) {
						g := b.FixAs[Fun[A, A]]("g")
						h := b.FixAs[Fun[A, A]]("h")
						pair := b.Assume()
						embeddingPairData := b.Have(
							"both maps are extension embeddings and vanish outside the simple field",
							"ring_homomorphism(restrict_ring(field_ring(L), D), field_ring(L), g) ∧ "+
								"ring_homomorphism(restrict_ring(field_ring(L), D), field_ring(L), h) ∧ "+
								"(∀x:A. x ∈ E ⇒ g(x) = f(x)) ∧ "+
								"(∀x:A. x ∈ E ⇒ h(x) = f(x)) ∧ "+
								"(∀x:A. x ∉ D ⇒ g(x) = L.zero) ∧ "+
								"(∀x:A. x ∉ D ⇒ h(x) = L.zero)",
							BySets(SDef, pair))
						embeddingPairAgreement := b.Have(
							"the two embeddings agree on E",
							"∀x:A. x ∈ E ⇒ g(x) = h(x)",
							By(Normalized, embeddingPairData))
						b.Show(
							"an embedding of E(a) is fixed by its values on E and at a",
							Derive(func(c *Argument) {
								c.Do(DDef.Rw())
								c.Do(By(
									L,
									embeddingPairAgreement,
									aIn,
									eField,
									pair,
									embeddingPairData,
									aAlgebraic,
									hom,
									At(simpleEmbeddingUnique, c.TermAs[FieldOps[A]]("L"), E, a, g, h)))
							}))
					}))
				evaluationInjective := arg.Have(
					"evaluation at the generator is injective on extension embeddings",
					"injective_on(S, λg:(A → A). g(a))",
					By(
						evaluationUnique,
						functions.InjectiveOnDef.At(S, arg.TermAs[Fun[Fun[A, A], A]]("λg:(A → A). g(a)"))))
				arg.Show(
					"evaluation at a is a bijection from S onto the conjugates R",
					By(
						Normalized,
						evaluationOntoRoots,
						conjugateSize,
						evaluationInjective,
						cardinality.HasSizeImageInjEq.At(
							arg.TermAs[Fun[Fun[A, A], A]]("λg:(A → A). g(a)"), S, arg.TermAs[Nat]("polynomial_degree(q)"))))
			})

			// The defining polynomial family makes its full root set finite and algebraic.
			finiteAlgebraicRoots := ctx.Lemma(Statement{
				Binders: "∀L:field_on(A). ∀K:set(A). ∀P:set(num → A).",
				Hypotheses: []string{
					"subfield(L, K)",
					"finite(P)",
					"∀p:(num → A). " +
						"    p ∈ P ⇒ polynomial_over(K, p) ∧ polynomial_separable(restrict_ring(field_ring(L), K), p)",
				},
				Conclusion: "finite(«roots») ∧ «roots» ⊆ L.carrier ∧ (∀a:A. a ∈ «roots» ⇒ algebraic_over(L, K, a))",
			}, func(
				a *Argument,
				L field.FieldFact[on.L],
				K *Expr[Set[A]],
				P *Expr[Set[Fun[Nat, A]]],
				kField, finiteP, separableFamily Fact,
			) {
				_, TDef := a.LetAs[Set[A]]("T", "«roots»")
				U, UDef := a.LetAs[Set[Set[A]]]("U", "image(λp:(num → A). polynomial_roots(L.carrier, p), P)")
				baseInside := a.Have(
					"the base field lies in the ambient carrier",
					"K ⊆ L.carrier",
					By(kField, field.SubfieldSubset.At(a.TermAs[FieldOps[A]]("L"), K)))
				nonzeroPolynomials := a.Have(
					"a separable polynomial is not the zero polynomial",
					"∀p:(num → A). p ∈ P ⇒ p ≠ vec_zero",
					Derive(func(b *Argument) {
						p := b.FixAs[Fun[Nat, A]]("p")
						member := b.Assume()
						b.Show(
							"p is separable over the ambient field, hence nonzero",
							By(
								member,
								baseInside,
								At(separableFamily, p),
								polynomial.PolynomialOverMono.At(a.TermAs[A]("L.zero"), K, a.TermAs[Set[A]]("L.carrier"), p),
								separable_polynomial.SeparableMono.At(a.TermAs[comm_ring.RingOps[A]]("field_ring(L)"), K, p),
								separable_polynomial.SeparableNonzero.Read(L).At(p)))
					}))
				finiteRoots := a.Have(
					"each polynomial, being nonzero, has finitely many roots",
					"∀p:(num → A). p ∈ P ⇒ finite(polynomial_roots(L.carrier, p))",
					Derive(func(b *Argument) {
						p := b.FixAs[Fun[Nat, A]]("p")
						member := b.Assume()
						b.Do(By(
							member,
							baseInside,
							At(separableFamily, p),
							At(nonzeroPolynomials, p),
							polynomial.PolynomialOverMono.At(a.TermAs[A]("L.zero"), K, a.TermAs[Set[A]]("L.carrier"), p),
							polynomial_roots.RootBound.Read(integral_domain.FieldIntegralDomain.Read(L)).At(p)))
					}))
				finiteRootFamily := a.Have(
					"the family of root sets is finite",
					"finite(U)",
					By(
						Normalized,
						finiteP,
						UDef,
						finite_set.FiniteImage.At(
							a.TermAs[Fun2[Fun[Nat, A], A, Bool]]("λp:(num → A). polynomial_roots(L.carrier, p)"), P)))
				finiteMembers := a.Have(
					"every root set in the family is finite",
					"∀S:set(A). S ∈ U ⇒ finite(S)",
					Derive(func(b *Argument) {
						S := b.FixAs[Set[A]]("S")
						member := b.Assume()
						b.Do(By(
							Normalized,
							member,
							UDef,
							finiteRoots,
							set_basic.InImage.At(
								a.TermAs[Fun2[Fun[Nat, A], A, Bool]]("λp:(num → A). polynomial_roots(L.carrier, p)"), P, S)))
					}))
				rootsAreUnion := a.Have(
					"the full root set is the union of the individual root sets",
					"T = ⋃U",
					Derive(func(b *Argument) {
						unionOfRootSets := b.Have(
							"the union of the root sets is the corresponding existential set",
							"⋃image(λp:(num → A). polynomial_roots(L.carrier, p), P) = "+
								"{y:A | ∃x:(num → A). x ∈ P ∧ y ∈ polynomial_roots(L.carrier, x)}",
							BySets())
						b.Do(Simp(Fwd(TDef), Fwd(UDef), Fwd(unionOfRootSets), Fwd(polynomial_roots.PolynomialRootsDef)))
						b.Do(BySets())
					}))
				finiteRootSet := a.Have(
					"the full root set is finite",
					"finite(T)",
					By(finiteRootFamily, rootsAreUnion, finiteMembers, finite_set.FiniteFiniteUnions.At(U)))
				rootsInside := a.Have(
					"every root lies in the ambient field",
					"T ⊆ L.carrier",
					BySets(TDef))
				algebraicRoots := a.Have(
					"every root is algebraic over the base field",
					"∀x:A. x ∈ T ⇒ algebraic_over(L, K, x)",
					Derive(func(b *Argument) {
						b.FixAs[A]("x")
						inT := b.Assume()
						b.Do(Simp(Fwd(algebraic_element.AlgebraicOverDef)))
						b.Do(BySets(nonzeroPolynomials, separableFamily, TDef, inT))
					}))
				a.Show(
					"T is finite, lies in L, and is algebraic over K",
					By(finiteRootSet, algebraicRoots, rootsInside))
			})

			// Counting embeddings: restriction to E fibers the embeddings of
			// E(a) over those of E, each fiber as large as the degree of a over E, so by induction a
			// finite set of roots of separable polynomials that split generates as many embeddings as its degree.

			uniformFiberCount := ctx.Lemma(Statement{
				Binders: "∀s:set(A). ∀t:set(B). ∀f:(B → A). ∀m n:num.",
				Hypotheses: []string{
					"has_size(s, m)",
					"∀y:B. y ∈ t ⇒ f(y) ∈ s",
					"∀x:A. x ∈ s ⇒ has_size({y:B | y ∈ t ∧ f(y) = x}, n)",
				},
				Conclusion: "has_size(t, m * n)",
			}, func(
				a *Argument,
				s *Expr[Set[A]],
				t *Expr[Set[B]],
				f *Arrow[B, A],
				m *Expr[Nat],
				n *Expr[Nat],
				sSize, mapsInto, fiberSize Fact,
			) {
				P, PDef := a.LetAs[Set[Prod[A, B]]](
					"P", "{(x, y):prod(A, B) | x:A, y:B | (x ∈ s ∧ y ∈ t) ∧ f(y) = x}")
				dependentProductSize := a.Have(
					"the dependent product has the product cardinality",
					"has_size(P, m * n)",
					Derive(func(b *Argument) {
						fibered := b.Have(
							"P pairs each x in s with the points of its fiber",
							"P = {(x, y):prod(A, B) | x:A, y:B | x ∈ s ∧ y ∈ {z:B | z ∈ t ∧ f(z) = x}}",
							BySets(PDef))
						b.Show(
							"count the dependent product of s with its fibers",
							Derive(func(c *Argument) {
								c.Do(fibered.Rw())
								c.Do(By(
									fiberSize,
									sSize,
									cardinality.HasSizeProductDependent.At(
										s, c.TermAs[Fun2[A, B, Bool]]("λx:A. {y:B | y ∈ t ∧ f(y) = x}"), m, n)))
							}))
					}))
				projectionBijection := a.Have(
					"projection is a bijection from the dependent product to the total set",
					"image(λz:prod(A, B). snd(z), P) = t ∧ injective_on(P, λz:prod(A, B). snd(z))",
					BySets(
						mapsInto,
						PDef,
						functions.InjectiveOnDef.At(P, a.TermAs[Fun[Prod[A, B], B]]("λz:prod(A, B). snd(z)")),
						pairs.Snd))
				a.Show(
					"the second projection is a bijection from P onto t",
					By(
						Normalized,
						dependentProductSize,
						projectionBijection,
						cardinality.HasSizeImageInjEq.At(
							a.TermAs[Fun[Prod[A, B], B]]("λz:prod(A, B). snd(z)"), P, a.TermAs[Nat]("m * n"))))
			})

			restrictEmbedding := ctx.Lemma(Statement{
				Binders: "∀L:field_on(A). ∀E D:set(A). ∀g h:(A → A).",
				Hypotheses: []string{
					"subfield(L, E)",
					"E ⊆ D",
					"ring_homomorphism(restrict_ring(field_ring(L), D), field_ring(L), g)",
					"∀x:A. x ∈ E ⇒ h(x) = g(x)",
				},
				Conclusion: "ring_homomorphism(restrict_ring(field_ring(L), E), field_ring(L), h)",
			}, func(
				a *Argument,
				L field.FieldFact[on.L],
				E *Expr[Set[A]],
				D *Expr[Set[A]],
				g *Arrow[A, A],
				h *Arrow[A, A],
				eField, nested, gHom, agrees Fact,
			) {
				restrictedRings := a.Have(
					"the restricted source and ambient target are commutative rings",
					"comm_ring_on(restrict_ring(field_ring(L), E)) ∧ comm_ring_on(field_ring(L))",
					By(field.RingOn.Read(L), eField, field.SubfieldCommRing.Read(L).At(E)))
				restrictedCarrier := a.Have(
					"the restricted map takes values in the ambient field",
					"∀x:A. x ∈ E ⇒ h(x) ∈ L.carrier",
					BySets(ring_homomorphism.MapIn.Read(gHom), agrees, nested))
				restrictedOperations := a.Have(
					"the restricted map preserves addition and multiplication",
					"∀x y:A. x ∈ E ∧ y ∈ E ⇒ h(x + y) = h(x) + h(y) ∧ h(x * y) = h(x) * h(y)",
					Derive(func(b *Argument) {
						x := b.FixAs[A]("x")
						y := b.FixAs[A]("y")
						bothIn := b.Assume()
						b.Do(BySets(
							At(agrees, x),
							At(agrees, y),
							At(agrees, b.TermAs[A]("x + y")),
							At(agrees, b.TermAs[A]("x * y")),
							eField,
							nested,
							bothIn,
							field.SubfieldAdd.At(b.TermAs[FieldOps[A]]("L"), E, x, y),
							field.SubfieldMul.At(b.TermAs[FieldOps[A]]("L"), E, x, y),
							ring_homomorphism.MapAdd.Read(gHom).AsFact().At(x, y),
							ring_homomorphism.MapMul.Read(gHom).AsFact().At(x, y)))
					}))
				restrictedOne := a.Have(
					"the restricted map preserves one",
					"h(L.one) = L.one",
					By(
						Normalized,
						ring_homomorphism.MapOne.Read(gHom),
						At(agrees, a.TermAs[A]("L.one")),
						eField,
						field.SubfieldOne.At(a.TermAs[FieldOps[A]]("L"), E)))
				a.Show(
					"h inherits the homomorphism laws of g on E",
					By(
						restrictedOperations,
						restrictedCarrier,
						restrictedOne,
						restrictedRings,
						ring_homomorphism.RingHomomorphism.At(
							a.TermAs[comm_ring.RingOps[A]]("restrict_ring(field_ring(L), E)"),
							a.TermAs[comm_ring.RingOps[A]]("field_ring(L)"),
							h)))
			})

			// The fiber over f of restriction to E extended by zero is the set of extensions of f.
			restrictionFiber := ctx.Lemma(Statement{
				Binders: "∀L:field_on(A). ∀K E D:set(A). ∀ρ:((A → A) → A → A). ∀f:(A → A).",
				Hypotheses: []string{
					"K ⊆ E",
					"∀g:(A → A). ∀x:A. (x ∈ E ⇒ ρ(g, x) = g(x)) ∧ (x ∉ E ⇒ ρ(g, x) = L.zero)",
					"∀x:A. x ∈ K ⇒ f(x) = x",
					"∀x:A. x ∉ E ⇒ f(x) = L.zero",
				},
				Conclusion: "{g:A → A | " +
					"    g ∈ algebra_points(restrict_ring(field_ring(L), D), field_ring(L), K, λx:A. x) ∧ " +
					"    ρ(g) = f} = " +
					"algebra_points(restrict_ring(field_ring(L), D), field_ring(L), E, f)",
			}, func(
				a *Argument,
				L field.FieldFact[on.L],
				K *Expr[Set[A]],
				E *Expr[Set[A]],
				D *Expr[Set[A]],
				ρ *Arrow[Fun[A, A], Fun[A, A]],
				f *Arrow[A, A],
				nested, restrictionValues, fixesK, vanishesOffE Fact,
			) {
				_, GPoints := a.LetAs[Set[Fun[A, A]]](
					"G", "algebra_points(restrict_ring(field_ring(L), D), field_ring(L), K, λx:A. x)")
				_, SPoints := a.LetAs[Set[Fun[A, A]]](
					"S", "algebra_points(restrict_ring(field_ring(L), D), field_ring(L), E, f)")
				GDef := a.Simplified(GPoints, Fwd(algebra_points.AlgebraPointsDef))
				SDef := a.Simplified(SPoints, Fwd(algebra_points.AlgebraPointsDef))
				sameMembers := a.Have(
					"a map lies in the fiber over f exactly when it extends f",
					"∀g:(A → A). (g ∈ G ∧ ρ(g) = f) ⇔ g ∈ S",
					Derive(func(b *Argument) {
						g := b.FixAs[Fun[A, A]]("g")
						b.Iff()
						b.Forward(
							"a member g of the fiber over f extends f",
							func(c *Argument, member Fact) {
								fiberData := c.Have(
									"g is a homomorphism vanishing off D whose restriction has the values of f",
									"ring_homomorphism(restrict_ring(field_ring(L), D), field_ring(L), g) ∧ "+
										"(∀x:A. x ∉ D ⇒ g(x) = L.zero) ∧ "+
										"(∀x:A. ρ(g, x) = f(x))",
									BySets(GDef, member))
								extendsF := c.Have(
									"g agrees with f on E",
									"∀x:A. x ∈ E ⇒ g(x) = f(x)",
									Derive(func(d *Argument) {
										x := d.FixAs[A]("x")
										inE := d.Assume()
										d.Do(By(Normalized, At(restrictionValues, g, x), inE, fiberData))
									}))
								c.Show(
									"g is a homomorphism extending f and vanishing off D",
									BySets(SDef, extendsF, fiberData))
							})
						b.Backward(
							"an extension g of f lies in the fiber over f",
							func(c *Argument, extension Fact) {
								extensionData := c.Have(
									"g is a homomorphism extending f and vanishing off D",
									"ring_homomorphism(restrict_ring(field_ring(L), D), field_ring(L), g) ∧ "+
										"(∀x:A. x ∈ E ⇒ g(x) = f(x)) ∧ "+
										"(∀x:A. x ∉ D ⇒ g(x) = L.zero)",
									BySets(SDef, extension))
								restrictsToF := c.Have(
									"the restriction of g extended by zero is f",
									"ρ(g) = f",
									Derive(func(d *Argument) {
										d.Do(Funext())
										x := d.FixAs[A]("x")
										d.Do(By(Normalized, At(vanishesOffE, x), At(restrictionValues, g, x), extensionData))
									}))
								fixesBase := c.Have(
									"an extension of f fixes the base field",
									"∀x:A. x ∈ K ⇒ g(x) = x",
									BySets(fixesK, nested, extensionData))
								c.Show(
									"g fixes K, vanishes off D and restricts to f",
									BySets(GDef, restrictsToF, fixesBase, extensionData))
							})
					}))
				a.Show(
					"sets with the same members are equal",
					BySets(sameMembers))
			})

			// Restriction multiplies the embedding count by the simple extension degree.
			embeddingCountStep := ctx.Lemma(Statement{
				Binders: "∀L:field_on(A). ∀K E:set(A). ∀a:A. ∀p:(num → A). ∀n:num.",
				Hypotheses: []string{
					"subfield(L, K)",
					"subfield(L, E)",
					"K ⊆ E",
					"a ∈ L.carrier",
					"algebraic_over(L, E, a)",
					"polynomial_over(K, p)",
					"polynomial_separable(restrict_ring(field_ring(L), K), p)",
					"polynomial_splits(field_ring(L), p)",
					"polynomial_eval(p, a) = L.zero",
					"has_size(algebra_points(restrict_ring(field_ring(L), E), field_ring(L), K, λx:A. x), n)",
				},
				Conclusion: "has_size(algebra_points(restrict_ring(field_ring(L), field_adjoin(L, E, {a})), " +
					"        field_ring(L), " +
					"        K, " +
					"        λx:A. x), " +
					"    n * polynomial_degree(minimal_polynomial(L, E, a)))",
			}, func(
				arg *Argument,
				L field.FieldFact[on.L],
				K *Expr[Set[A]],
				E *Expr[Set[A]],
				a *Expr[A],
				p *Arrow[Nat, A],
				n *Expr[Nat],
				kField, eField, nested, aIn, aAlgebraic, pOver, pSeparable, pSplits, aRoot, eCount Fact,
			) {
				D, DDef := arg.LetAs[Set[A]]("D", "field_adjoin(L, E, {a})")
				_, qDef := arg.LetAs[Fun[Nat, A]]("q", "minimal_polynomial(L, E, a)")
				F, FDef := arg.LetAs[Set[Fun[A, A]]](
					"F", "algebra_points(restrict_ring(field_ring(L), E), field_ring(L), K, λx:A. x)")
				G, GDef := arg.LetAs[Set[Fun[A, A]]](
					"G", "algebra_points(restrict_ring(field_ring(L), D), field_ring(L), K, λx:A. x)")
				FMembers := arg.Unfolded(FDef, algebra_points.AlgebraPointsDef)
				GMembers := arg.Unfolded(GDef, algebra_points.AlgebraPointsDef)
				ρ, ρDef := arg.LetAs[Fun[Fun[A, A], Fun[A, A]]]("ρ", "λg:(A → A). λx:A. COND(x ∈ E, g(x), L.zero)")
				eInside := arg.Have(
					"E lies in the simple extension",
					"E ⊆ D",
					By(
						Normalized,
						DDef,
						eField,
						algebraic_element.AdjoinElementSubfield.Read(L).At(E, arg.MemberOf[on.L](a, aIn))))
				restrictionValues := arg.Have(
					"the restriction of g to E extended by zero agrees with g on E and is zero off E",
					"∀g:(A → A). ∀x:A. (x ∈ E ⇒ ρ(g, x) = g(x)) ∧ (x ∉ E ⇒ ρ(g, x) = L.zero)",
					By(Normalized, ρDef))
				restrictionMapsEmbeddings := arg.Have(
					"restriction to E extended by zero sends embeddings of D to embeddings of E",
					"∀g:(A → A). g ∈ G ⇒ ρ(g) ∈ F",
					Derive(func(b *Argument) {
						g := b.FixAs[Fun[A, A]]("g")
						inG := b.Assume()
						extensionEmbeddingData := b.Have(
							"the extension embedding is a homomorphism fixing the base field",
							"ring_homomorphism(restrict_ring(field_ring(L), D), field_ring(L), g) ∧ (∀x:A. x ∈ K ⇒ g(x) = x)",
							BySets(GMembers, inG))
						restrictionAgreement := b.Have(
							"the restriction extended by zero agrees with g on E",
							"∀x:A. x ∈ E ⇒ ρ(g, x) = g(x)",
							By(At(restrictionValues, g)))
						restrictionHom := b.Have(
							"the restriction extended by zero is a field homomorphism",
							"ring_homomorphism(restrict_ring(field_ring(L), E), field_ring(L), ρ(g))",
							By(
								L,
								restrictionAgreement,
								eField,
								eInside,
								extensionEmbeddingData,
								At(restrictEmbedding, b.TermAs[FieldOps[A]]("L"), E, D, g, b.TermAs[Fun[A, A]]("ρ(g)"))))
						b.Show(
							"ρ(g) is an embedding of E over K, vanishing off E",
							Derive(func(c *Argument) {
								c.Do(Simp(Fwd(FMembers)))
								c.Do(BySets(nested, extensionEmbeddingData, restrictionHom, At(restrictionValues, g)))
							}))
					}))
				restrictionFiberSize := arg.Have(
					"each restriction fiber has the minimal polynomial degree as its size",
					"∀f:(A → A). f ∈ F ⇒ has_size({g:A → A | g ∈ G ∧ ρ(g) = f}, polynomial_degree(q))",
					Derive(func(b *Argument) {
						f := b.FixAs[Fun[A, A]]("f")
						inF := b.Assume()
						embeddingOfE := b.Have(
							"f is an embedding of E over K, vanishing off E",
							"ring_homomorphism(restrict_ring(field_ring(L), E), field_ring(L), f) ∧ "+
								"(∀x:A. x ∈ K ⇒ f(x) = x) ∧ "+
								"(∀x:A. x ∉ E ⇒ f(x) = L.zero)",
							BySets(FMembers, inF))
						embeddingOfEParts := b.Conjuncts(
							embeddingOfE,
							"f is a homomorphism from E into L",
							"f fixes K",
							"f vanishes off E")
						_, SDef := b.LetAs[Set[Fun[A, A]]](
							"S", "algebra_points(restrict_ring(field_ring(L), D), field_ring(L), E, f)")
						extensionCount := b.Have(
							"f has as many extensions to D as the degree of q",
							"has_size(S, polynomial_degree(q))",
							SDef.Rw(),
							DDef.Rw(),
							qDef.Rw(),
							By(
								L,
								kField,
								eField,
								nested,
								aIn,
								aAlgebraic,
								pOver,
								pSeparable,
								pSplits,
								aRoot,
								embeddingOfE,
								At(extensionFiberCount, b.TermAs[FieldOps[A]]("L"), K, E, f, a, p)))
						fiberIsExtensions := b.Have(
							"the restriction fiber over f is precisely the set of embeddings extending f",
							"{g:A → A | g ∈ G ∧ ρ(g) = f} = S",
							GDef.Rw(),
							SDef.Rw(),
							By(
								L,
								nested,
								restrictionValues,
								embeddingOfEParts[1],
								embeddingOfEParts[2],
								At(restrictionFiber, b.TermAs[FieldOps[A]]("L"), K, E, D, ρ, f)))
						b.Show(
							"the fiber over f is the set S of extensions of f",
							Derive(func(c *Argument) {
								c.Do(fiberIsExtensions.Rw())
								c.Do(By(extensionCount))
							}))
					}))
				arg.Show(
					"count G through the fibers of restriction to E",
					By(
						restrictionFiberSize,
						restrictionMapsEmbeddings,
						eCount,
						At(uniformFiberCount, F, G, ρ, n, arg.TermAs[Nat]("polynomial_degree(q)"))))
			})

			baseEmbeddingCount := ctx.Lemma(Statement{
				Binders: "∀L:field_on(A). ∀K:set(A).",
				Hypotheses: []string{
					"subfield(L, K)",
				},
				Conclusion: "has_size( " +
					"    algebra_points(restrict_ring(field_ring(L), K), field_ring(L), K, λx:A. x), 1)",
			}, func(a *Argument, L field.FieldFact[on.L], K *Expr[Set[A]], kField Fact) {
				_, FPoints := a.LetAs[Set[Fun[A, A]]](
					"F", "algebra_points(restrict_ring(field_ring(L), K), field_ring(L), K, λx:A. x)")
				FDef := a.Simplified(FPoints, Fwd(algebra_points.AlgebraPointsDef))
				h, hDef := a.LetAs[Fun[A, A]]("h", "λx:A. COND(x ∈ K, x, L.zero)")
				inclusionHom := a.Have(
					"the base field inclusion is a ring homomorphism",
					"ring_homomorphism(restrict_ring(field_ring(L), K), field_ring(L), λx:A. x)",
					By(
						kField,
						field.SubfieldSubring.Read(L).At(K),
						ring_homomorphism.SubringInclusionHom.Read(field.RingOn.Read(L)).At(K)))
				extendedInclusionHom := a.Have(
					"the inclusion extended by zero is a ring homomorphism",
					"ring_homomorphism(restrict_ring(field_ring(L), K), field_ring(L), h)",
					By(
						hDef,
						inclusionHom,
						ring_homomorphism.RingHomCongruence.At(
							a.TermAs[comm_ring.RingOps[A]]("restrict_ring(field_ring(L), K)"),
							a.TermAs[comm_ring.RingOps[A]]("field_ring(L)"),
							a.TermAs[Fun[A, A]]("λx:A. x"),
							h)))
				baseEmbedding := a.Have(
					"the inclusion extended by zero is a base embedding",
					"h ∈ F",
					Derive(func(b *Argument) {
						b.Do(Simp(Fwd(FDef)))
						b.Do(BySets(hDef, extendedInclusionHom))
					}))
				baseEmbeddingUnique := a.Have(
					"every base embedding equals the inclusion extended by zero",
					"∀f:(A → A). f ∈ F ⇒ f = h",
					Derive(func(b *Argument) {
						b.FixAs[Fun[A, A]]("f")
						inF := b.Assume()
						fixesAndVanishes := b.Have(
							"f fixes K and vanishes off K",
							"(∀x:A. x ∈ K ⇒ f(x) = x) ∧ (∀x:A. x ∉ K ⇒ f(x) = L.zero)",
							BySets(FDef, inF))
						b.Do(Funext())
						b.FixAs[A]("x")
						b.Do(By(Normalized, hDef, fixesAndVanishes))
					}))
				baseEmbeddingSingleton := a.Have(
					"the set of base embeddings is a singleton",
					"F = {h}",
					BySets(baseEmbeddingUnique, baseEmbedding))
				a.Show(
					"a singleton has exactly one element",
					Derive(func(b *Argument) {
						b.Do(baseEmbeddingSingleton.Rw())
						b.Do(By(
							finite_set.FiniteSing.At(h),
							cardinality.CardSing.At(h),
							cardinality.HasSizeDef.At(b.TermAs[Set[Fun[A, A]]]("{h}"), a.TermAs[Nat]("1"))))
					}))
			})

			// Finite induction and the tower law identify the embedding count with the extension degree.
			finiteEmbeddingCount := ctx.Lemma(Statement{
				Binders: "∀L:field_on(A). ∀K T:set(A).",
				Hypotheses: []string{
					"subfield(L, K)",
					"finite(T)",
					"T ⊆ L.carrier",
					"∀a:A. a ∈ T ⇒ algebraic_over(L, K, a)",
					"∀a:A. a ∈ T ⇒ «separableRoot»(a)",
				},
				Conclusion: "has_size(algebra_points(restrict_ring(field_ring(L), field_adjoin(L, K, T)), " +
					"        field_ring(L), " +
					"        K, " +
					"        λx:A. x), " +
					"    extension_degree(L, K, field_adjoin(L, K, T)))",
				Abbrev: Abbrev{
					{Name: "separableRoot", Text: "λa:A. ∃p:(num → A). " +
						"    polynomial_over(K, p) ∧ " +
						"    polynomial_separable(restrict_ring(field_ring(L), K), p) ∧ " +
						"    polynomial_splits(field_ring(L), p) ∧ " +
						"    polynomial_eval(p, a) = L.zero"},
				},
			}, func(
				a *Argument,
				L field.FieldFact[on.L],
				K *Expr[Set[A]],
				T *Expr[Set[A]],
				kField, finiteT, tInside, algebraic, separableRoots Fact,
			) {
				a.Show(
					"by induction, every finite set of separable roots "+
						"has as many embeddings as its degree, and T is one",
					ByInduction(
						finite_set.FiniteInduct,
						L,
						kField,
						finiteT,
						Generalizing(finiteT, tInside, algebraic, separableRoots),
						Case(
							"no point adjoined",
							Derive(func(b *Argument) {
								adjoinNothing := b.Have(
									"adjoining nothing gives K",
									"field_adjoin(L, K, ∅) = K",
									BySets(kField, algebraic_element.AdjoinOfSubset.Read(L).At(K, b.TermAs[Set[A]]("∅"))))
								b.Show(
									"K has one embedding over itself, and degree one",
									Derive(func(c *Argument) {
										c.Do(adjoinNothing.Rw())
										c.Do(By(
											L,
											kField,
											field_extension.ExtensionOverItself.Read(L).At(K),
											At(baseEmbeddingCount, c.TermAs[FieldOps[A]]("L"), K)))
									}))
							})),
						Case(
							"one more point x adjoined to s",
							Derive(func(b *Argument) {
								x := b.FixAs[A]("x")
								s := b.FixAs[Set[A]]("s")
								inductive := b.Assume()
								enlarged := b.Assume()
								E, EDef := b.LetAs[Set[A]]("E", "field_adjoin(L, K, s)")
								D, DDef := b.LetAs[Set[A]]("D", "field_adjoin(L, E, {x})")
								smallerGeneratorSet := b.Have(
									"the smaller set retains finiteness and all algebraic and separable root conditions",
									"finite(s) ∧ "+
										"s ⊆ L.carrier ∧ "+
										"(∀a:A. a ∈ s ⇒ algebraic_over(L, K, a)) ∧ "+
										"(∀a:A. a ∈ s ⇒ «separableRoot»(a)) ∧ "+
										"x ∈ L.carrier ∧ "+
										"algebraic_over(L, K, x) ∧ "+
										"«separableRoot»(x)",
									BySets(enlarged, finite_set.FiniteInsert.At(x, s)))
								eCount := b.Have(
									"E is finite over K and its embedding count equals its degree",
									"subfield(L, E) ∧ "+
										"K ⊆ E ∧ "+
										"finite_extension(L, K, E) ∧ "+
										"has_size(algebra_points(restrict_ring(field_ring(L), E), field_ring(L), K, λx:A. x), "+
										"    extension_degree(L, K, E))",
									By(
										EDef,
										kField,
										inductive,
										smallerGeneratorSet,
										field.SubfieldSubset.At(b.TermAs[FieldOps[A]]("L"), K),
										algebraic_element.AdjoinSubfield.Read(L).At(K, s),
										algebraic_element.FiniteAlgebraicAdjoin.At(b.TermAs[FieldOps[A]]("L"), K, s)))
								pointOverE := b.Have(
									"the new point is algebraic over E",
									"algebraic_over(L, E, x)",
									By(kField, eCount, smallerGeneratorSet, algebraic_element.AlgebraicOverMono.Read(L).At(K, E, x)))
								simpleDegree := b.Have(
									"the new simple extension has degree equal to the minimal polynomial degree",
									"subfield(L, D) ∧ "+
										"E ⊆ D ∧ "+
										"finite_extension(L, E, D) ∧ "+
										"extension_degree(L, E, D) = polynomial_degree(minimal_polynomial(L, E, x))",
									By(
										DDef,
										eCount,
										smallerGeneratorSet,
										pointOverE,
										algebraic_element.AdjoinElementSubfield.Read(L).AsFact().At(E, x),
										algebraic_element.AdjoinDegree.Read(L).AsFact().At(E, x)))
								generatorStep := b.Have(
									"the enlarged adjunction is the simple extension of E",
									"field_adjoin(L, K, insert(x, s)) = D",
									By(
										L,
										DDef,
										EDef,
										kField,
										smallerGeneratorSet,
										field.SubfieldSubset.At(b.TermAs[FieldOps[A]]("L"), K),
										algebraic_element.AdjoinInsert.Read(L).AsFact().At(K, s, x)))
								p, separableRoot := b.ObtainAs[Fun[Nat, A]](
									"choose a separable polynomial p over K, splitting in L, with root x",
									"«separableRoot»(x)",
									By(smallerGeneratorSet))
								embeddingProduct := b.Have(
									"the number of embeddings multiplies by the simple extension degree",
									"has_size(algebra_points(restrict_ring(field_ring(L), D), field_ring(L), K, λx:A. x), "+
										"    extension_degree(L, K, E) * polynomial_degree(minimal_polynomial(L, E, x)))",
									By(
										L,
										DDef,
										kField,
										eCount,
										smallerGeneratorSet,
										separableRoot,
										pointOverE,
										At(
											embeddingCountStep,
											b.TermAs[FieldOps[A]]("L"),
											K,
											E,
											x,
											p,
											b.TermAs[Nat]("extension_degree(L, K, E)"))))
								degreeProduct := b.Have(
									"the extension degree multiplies by the same factor",
									"extension_degree(L, K, D) = "+
										"extension_degree(L, K, E) * polynomial_degree(minimal_polynomial(L, E, x))",
									By(Normalized, kField, simpleDegree, eCount, field_extension.TowerLaw.Read(L).At(K, E, D)))
								b.Show(
									"both counts are the count for s times the degree of x over E",
									Derive(func(c *Argument) {
										c.Do(generatorStep.Rw())
										c.Do(By(degreeProduct, embeddingProduct))
									}))
							}))))
			})

			// An embedding of the root field sends roots of P to roots of P, so its image
			// stays in the root field. FiniteEmbeddingOnto and EmbeddingPermutation turn
			// it into an automorphism; the embedding count then gives the Galois property.

			rootFieldStable := ctx.Lemma(Statement{
				Binders: "∀L:field_on(A). ∀K:set(A). ∀P:set(num → A). ∀f:(A → A).",
				Hypotheses: []string{
					"subfield(L, K)",
					"∀p:(num → A). p ∈ P ⇒ polynomial_over(K, p)",
					"ring_homomorphism(restrict_ring(field_ring(L), «rootField»), field_ring(L), f)",
					"∀x:A. x ∈ K ⇒ f(x) = x",
				},
				Conclusion: "image(f, «rootField») ⊆ «rootField»",
			}, func(
				a *Argument,
				L field.FieldFact[on.L],
				K *Expr[Set[A]],
				P *Expr[Set[Fun[Nat, A]]],
				f *Arrow[A, A],
				kField, overK, hom, fixesK Fact,
			) {
				T, TDef := a.LetAs[Set[A]]("T", "«roots»")
				M, MDef := a.LetAs[Set[A]]("M", "field_adjoin(L, K, T)")
				S, preimageDef := a.LetAs[Set[A]]("S", "preimage_on(M, f, M)")
				rootCarrier := a.Have(
					"the root set lies in the ambient field",
					"T ⊆ L.carrier",
					BySets(TDef))
				rootField := a.Have(
					"the root field contains the base field and every root",
					"subfield(L, M) ∧ K ⊆ M ∧ T ⊆ M",
					By(
						Normalized,
						MDef,
						kField,
						rootCarrier,
						field.SubfieldSubset.At(a.TermAs[FieldOps[A]]("L"), K),
						algebraic_element.AdjoinSubfield.Read(L).At(K, T)))
				fieldM := a.Have(
					"M is a field under the operations of L",
					"field_on(restrict_field(L, M))",
					By(rootField, field.SubfieldFieldOn.Read(L).At(M)))
				homM := a.Have(
					"f is a homomorphism of the field M into L",
					"ring_homomorphism(field_ring(restrict_field(L, M)), field_ring(L), f)",
					Simp(Rev(field.RestrictFieldRing)),
					By(hom))
				preimageInM := a.Have(
					"the inverse image of the root field is a subfield of M",
					"subfield(restrict_field(L, M), S)",
					By(
						Normalized,
						L,
						homM,
						preimageDef,
						rootField,
						algebraic_element.FieldEmbeddingPreimageSubfield.Read(fieldM).At(a.TermAs[FieldOps[A]]("L"), f, M)))
				preimageField := a.Have(
					"and so a subfield of L, as M is",
					"subfield(L, S)",
					By(rootField, preimageInM, field.SubfieldTrans.At(a.TermAs[FieldOps[A]]("L"), M, S)))
				SDef := a.Simplified(preimageDef, Fwd(functions.PreimageOnDef))
				baseInPreimage := a.Have(
					"the inverse image contains the base field",
					"K ⊆ S",
					BySets(fixesK, SDef, rootField))
				rootsStable := a.Have(
					"the embedding sends each generating root to another generating root",
					"∀x:A. x ∈ T ⇒ f(x) ∈ T",
					Derive(func(b *Argument) {
						x := b.FixAs[A]("x")
						inT := b.Assume()
						p, root := b.ObtainAs[Fun[Nat, A]](
							"choose p in P over K with root x",
							"∃p:(num → A). p ∈ P ∧ polynomial_over(K, p) ∧ polynomial_eval(p, x) = L.zero",
							BySets(overK, TDef, inT))
						imageRootEquation := b.Have(
							"the image of the chosen root satisfies the same base polynomial",
							"f(x) ∈ L.carrier ∧ polynomial_eval(p, f(x)) = L.zero",
							BySets(
								L,
								fixesK,
								inT,
								root,
								rootField,
								hom,
								At(transportRoot, b.TermAs[FieldOps[A]]("L"), K, M, b.TermAs[Fun[A, A]]("λx:A. x"), f, x, p)))
						b.Show(
							"f(x) is again a root of a polynomial in P",
							BySets(TDef, imageRootEquation, root))
					}))
				rootsInPreimage := a.Have(
					"the inverse image contains every generating root",
					"T ⊆ S",
					BySets(rootsStable, SDef, rootField))
				fieldInPreimage := a.Have(
					"the inverse image contains the entire root field",
					"M ⊆ S",
					By(
						Normalized,
						MDef,
						preimageField,
						baseInPreimage,
						rootsInPreimage,
						algebraic_element.AdjoinLeast.Read(L).At(K, T, S)))
				a.Show(
					"M lies in the inverse image of M under f",
					BySets(SDef, fieldInPreimage))
			})

			// An embedding of M is an automorphism of M extended by zero, so the embedding count bounds the
			// automorphisms from below; the degree bound on automorphisms, used once, bounds them from above.
			countImpliesGalois := ctx.Lemma(Statement{
				Binders: "∀L:field_on(A). ∀K M:set(A).",
				Hypotheses: []string{
					"subfield(L, K)",
					"subfield(L, M)",
					"K ⊆ M",
					"finite_extension(L, K, M)",
					"has_size(algebra_points(restrict_ring(field_ring(L), M), field_ring(L), K, λx:A. x), " +
						"    extension_degree(L, K, M))",
					"∀f:(A → A). " +
						"    f ∈ algebra_points(restrict_ring(field_ring(L), M), field_ring(L), K, λx:A. x) ⇒ " +
						"    image(f, M) = M",
				},
				Conclusion: "galois_over(L, K, M)",
			}, func(
				a *Argument,
				L field.FieldFact[on.L],
				K *Expr[Set[A]],
				M *Expr[Set[A]],
				kField, mField, nested, finiteM, count, onto Fact,
			) {
				F, FPoints := a.LetAs[Set[Fun[A, A]]](
					"F", "algebra_points(restrict_ring(field_ring(L), M), field_ring(L), K, λx:A. x)")
				FDef := a.Simplified(FPoints, Fwd(algebra_points.AlgebraPointsDef))
				H, HDef := a.LetAs[Set[symmetric_group.Permutation[A]]]("H", "field_automorphisms(L, K, M)")
				extended, extendedDef := a.LetAs[Fun[symmetric_group.Permutation[A], Fun[A, A]]](
					"extended", "λp:permutation(A). λx:A. COND(x ∈ M, permutation_map(p, x), L.zero)")
				J, JDef := a.LetAs[Set[Fun[A, A]]]("J", "image(extended, H)")
				embeddingsRepresented := a.Have(
					"each embedding of M over K is an automorphism of M extended by zero",
					"∀f:(A → A). f ∈ F ⇒ ∃p:permutation(A). p ∈ field_automorphisms(L, K, M) ∧ extended(p) = f",
					Derive(func(b *Argument) {
						f := b.FixAs[Fun[A, A]]("f")
						inF := b.Assume()
						embeddingData := b.Have(
							"f is an embedding of M over K, vanishing off M",
							"ring_homomorphism(restrict_ring(field_ring(L), M), field_ring(L), f) ∧ "+
								"(∀x:A. x ∈ K ⇒ f(x) = x) ∧ "+
								"(∀x:A. x ∉ M ⇒ f(x) = L.zero)",
							BySets(FDef, inF))
						p, permutation := b.ObtainAs[symmetric_group.Permutation[A]](
							"represent f on M by an automorphism over K",
							"∃p:permutation(A). "+
								"    p ∈ field_automorphisms(L, K, M) ∧ (∀x:A. x ∈ M ⇒ permutation_map(p, x) = f(x))",
							By(
								L,
								onto,
								inF,
								mField,
								embeddingData,
								field_automorphism.EmbeddingPermutation.Read(L).At(K, M, f)))
						embeddingParts := b.Conjuncts(
							embeddingData,
							"f is a homomorphism on M",
							"f fixes K",
							"f vanishes outside M")
						permutationData := b.Conjuncts(
							permutation,
							"p is an automorphism of M fixing K",
							"p agrees with f on M")
						b.Take(p)
						b.Do(SplitConj(
							Case(
								"p is an automorphism of M fixing K",
								By(permutationData[0])),
							Case(
								"p extended by zero off M is f",
								Derive(func(c *Argument) {
									c.Do(extendedDef.Rw())
									c.Do(Funext())
									x := c.FixAs[A]("x")
									c.Do(By(Normalized, At(embeddingParts[2], x), At(permutationData[1], x)))
								}))))
					}))
				embeddingInImage := a.Have(
					"the embedding set lies in the image J of the automorphism group",
					"F ⊆ J",
					Derive(func(b *Argument) {
						b.Do(Simp(Fwd(JDef), Fwd(HDef)))
						b.Do(BySets(embeddingsRepresented))
					}))
				finiteCounts := a.Have(
					"the embedding count equals the degree and the automorphism count is at most the degree",
					"finite(F) ∧ card(F) = extension_degree(L, K, M) ∧ finite(H) ∧ card(H) ≤ extension_degree(L, K, M)",
					By(
						Normalized,
						HDef,
						count,
						kField,
						mField,
						nested,
						finiteM,
						cardinality.HasSizeDef.At(F, a.TermAs[Nat]("extension_degree(L, K, M)")),
						field_automorphism.AutomorphismsBound.Read(L).At(K, M)))
				imageCountBound := a.Have(
					"the image J has cardinality at most that of the automorphism group",
					"finite(J) ∧ card(J) ≤ card(H)",
					By(
						Normalized,
						JDef,
						finiteCounts,
						finite_set.FiniteImage.At(extended, H),
						cardinality.CardImageLe.At(extended, H)))
				automorphismLowerBound := a.Have(
					"the degree is at most the automorphism count",
					"extension_degree(L, K, M) ≤ card(H)",
					By(
						Normalized,
						embeddingInImage,
						imageCountBound,
						finiteCounts,
						cardinality.CardSubset.At(F, J),
						nat_order.LessEqTrans.At(
							a.TermAs[Nat]("card(F)"), a.TermAs[Nat]("card(J)"), a.TermAs[Nat]("card(H)"))))
				automorphismCount := a.Have(
					"M has exactly as many automorphisms over K as its degree",
					"card(H) = extension_degree(L, K, M)",
					By(
						automorphismLowerBound,
						finiteCounts,
						nat_order.LessEqAntisym.At(a.TermAs[Nat]("card(H)"), a.TermAs[Nat]("extension_degree(L, K, M)"))))
				a.Show(
					"the automorphism count gives the Galois property",
					Derive(func(b *Argument) {
						b.Do(HDef.Rw())
						b.Do(By(automorphismCount, kField, mField, nested, finiteM, GaloisIffCard.Read(L).At(K, M)))
					}))
			})

			return ctx.Theorem(headline, func(
				a *Argument,
				L field.FieldFact[on.L],
				K *Expr[Set[A]],
				P *Expr[Set[Fun[Nat, A]]],
				kField, finiteP, separableFamily Fact,
			) {
				T, TDef := a.LetAs[Set[A]]("T", "«roots»")
				M, MDef := a.LetAs[Set[A]]("M", "field_adjoin(L, K, T)")
				_, FDef := a.LetAs[Set[Fun[A, A]]](
					"F", "algebra_points(restrict_ring(field_ring(L), M), field_ring(L), K, λx:A. x)")
				FMembers := a.Unfolded(FDef, algebra_points.AlgebraPointsDef)
				rootsFiniteAlgebraic := a.Have(
					"the generating root set is finite and algebraic over the base field",
					"finite(T) ∧ T ⊆ L.carrier ∧ (∀a:A. a ∈ T ⇒ algebraic_over(L, K, a))",
					By(
						Normalized,
						L,
						TDef,
						kField,
						finiteP,
						separableFamily,
						At(finiteAlgebraicRoots, a.TermAs[FieldOps[A]]("L"), K, P)))
				separableRootData := a.Have(
					"every generator is a root of a separable polynomial over the base field that splits in L",
					"(∀p:(num → A). p ∈ P ⇒ polynomial_over(K, p)) ∧ "+
						"(∀a:A. "+
						"    a ∈ T ⇒ "+
						"    ∃p:(num → A). "+
						"        polynomial_over(K, p) ∧ "+
						"        polynomial_separable(restrict_ring(field_ring(L), K), p) ∧ "+
						"        polynomial_splits(field_ring(L), p) ∧ "+
						"        polynomial_eval(p, a) = L.zero)",
					BySets(separableFamily, TDef))
				finiteRootFieldCount := a.Have(
					"the root field is finite over the base and its embedding count equals its degree",
					"subfield(L, M) ∧ K ⊆ M ∧ finite_extension(L, K, M) ∧ has_size(F, extension_degree(L, K, M))",
					By(
						Normalized,
						MDef,
						FDef,
						kField,
						separableRootData,
						rootsFiniteAlgebraic,
						field.SubfieldSubset.At(a.TermAs[FieldOps[A]]("L"), K),
						algebraic_element.AdjoinSubfield.Read(L).At(K, T),
						algebraic_element.FiniteAlgebraicAdjoin.At(a.TermAs[FieldOps[A]]("L"), K, T),
						At(finiteEmbeddingCount, a.TermAs[FieldOps[A]]("L"), K, T)))
				embeddingsOnto := a.Have(
					"every embedding of M over K maps M onto M",
					"∀f:(A → A). f ∈ F ⇒ image(f, M) = M",
					Derive(func(b *Argument) {
						f := b.FixAs[Fun[A, A]]("f")
						inF := b.Assume()
						chosenEmbedding := b.Have(
							"the chosen embedding is a homomorphism fixing the base field",
							"ring_homomorphism(restrict_ring(field_ring(L), M), field_ring(L), f) ∧ (∀x:A. x ∈ K ⇒ f(x) = x)",
							BySets(FMembers, inF))
						chosenEmbeddingStable := b.Have(
							"the chosen embedding maps the root field into itself",
							"image(f, M) ⊆ M",
							Derive(func(c *Argument) {
								c.Do(MDef.Rw())
								c.Do(TDef.Rw())
								c.Do(By(
									L,
									kField,
									separableRootData,
									chosenEmbedding,
									At(rootFieldStable, c.TermAs[FieldOps[A]]("L"), K, P, f)))
							}))
						b.Show(
							"f maps M into itself, hence onto M by finiteness",
							By(
								L,
								kField,
								chosenEmbeddingStable,
								finiteRootFieldCount,
								chosenEmbedding,
								field_extension.FiniteEmbeddingOnto.Read(L).At(K, M, f)))
					}))
				a.Show(
					"the automorphism count gives the Galois property",
					Derive(func(b *Argument) {
						b.Do(FDef.Rw())
						b.Do(By(
							L,
							embeddingsOnto,
							kField,
							finiteRootFieldCount,
							At(countImpliesGalois, b.TermAs[FieldOps[A]]("L"), K, M)))
					}))
			})
		}),
})}
