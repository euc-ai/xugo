// chains.go — field records ordered by extension: the order is a
// preorder, an extension reads every polynomial and every algebraicity
// over the smaller carrier as the smaller record does, and transport
// along an injection keeps algebraicity; an extension holds the smaller
// carrier as a subfield, its inclusion is a ring homomorphism, and a ring
// homomorphism fixing the smaller carrier makes one. A chain of fields algebraic over one set unites to a
// field algebraic over it, and Zorn's lemma then gives every field a
// maximal algebraic extension on its own type.

package algebraic_closure

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/abelian_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_evaluation"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_transport"
	"github.com/euc-ai/xugo/library/proofs/relations/equivalence"
	"github.com/euc-ai/xugo/library/proofs/relations/order"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
)

// FieldExtendsPreorder — extension of field records is reflexive and
// transitive: carrier inclusion carries the operation agreements through
// the middle record.
var FieldExtendsPreorder = fieldExtendsPreorderThm{family.Add(registry.ProofEntry{
	Name:    "FieldExtendsPreorder",
	Key:     "prop_8ecf98ccf964d017",
	Reading: "It holds of all records, fields or not.",
	Build: family.Theorem("preorder(field_extends⟨A:A⟩)", func(a *Argument) {
		a.Do(Unfold(order.Preorder), SplitConj(
			Case(
				"every record extends itself",
				Unfold(equivalence.ReflexiveDef),
				Unfold(fieldExtendsDef),
				BySets()),
			Case(
				"operation agreements pass through the middle record",
				Unfold(equivalence.TransitiveDef),
				Derive(func(b *Argument) {
					b.FixAs[FieldOps[A]]("F")
					b.FixAs[FieldOps[A]]("G")
					b.FixAs[FieldOps[A]]("H")
					extensions := b.Conjuncts(
						b.Assume(),
						"G extends F",
						"H extends G")
					fg := b.Conjuncts(
						b.Unfolded(extensions[0], fieldExtendsDef),
						"F's carrier lies in G's",
						"F and G share the zero",
						"F and G share the one",
						"negation and inversion agree on F's carrier",
						"the binary operations agree on F's carrier")
					gh := b.Conjuncts(
						b.Unfolded(extensions[1], fieldExtendsDef),
						"G's carrier lies in H's",
						"G and H share the zero",
						"G and H share the one",
						"negation and inversion agree on G's carrier",
						"the binary operations agree on G's carrier")
					fgCarrier, fgZero, fgOne, fgUnary, fgBinary := fg[0], fg[1], fg[2], fg[3], fg[4]
					ghCarrier, ghZero, ghOne, ghUnary, ghBinary := gh[0], gh[1], gh[2], gh[3], gh[4]
					b.Do(Unfold(fieldExtendsDef), SplitConjAll(
						Case(
							"carrier inclusion is transitive",
							BySets(fgCarrier, ghCarrier)),
						Case(
							"the zero agrees through G",
							Simp(Fwd(fgZero), Fwd(ghZero)),
							Basic()),
						Case(
							"the one agrees through G",
							Simp(Fwd(fgOne), Fwd(ghOne)),
							Basic()),
						Case(
							"negation and inversion agree at every point of F",
							Derive(func(c *Argument) {
								c.FixAs[A]("u")
								inF := c.Assume()
								c.Have(
									"the point of F also lies in G",
									"u ∈ G.carrier",
									BySets(fgCarrier, inF))
								c.Show(
									"both unary agreements compose",
									Simp(Fwd(fgUnary), Fwd(ghUnary)),
									Basic())
							})),
						Case(
							"the four binary operations agree at every pair of points of F",
							Derive(func(c *Argument) {
								c.FixAs[A]("u")
								c.FixAs[A]("v")
								inF := c.Assume()
								c.Have(
									"the two points of F also lie in G",
									"u ∈ G.carrier ∧ v ∈ G.carrier",
									BySets(fgCarrier, inF))
								c.Show(
									"all four binary agreements compose",
									Simp(Fwd(fgBinary), Fwd(ghBinary)),
									Basic())
							})),
					))
				})),
		))
	}),
})}

// FieldExtendsEval — an extension of a field evaluates every polynomial
// over a part of the smaller carrier to the same value there. Restricting
// the larger record to that carrier gives an identity ring homomorphism;
// the same nonzero polynomial then witnesses algebraicity on both sides.
var FieldExtendsEval = fieldExtendsEvalThm{family.Add(registry.ProofEntry{
	Name: "FieldExtendsEval",
	Key:  "prop_403b7794bbc7f7ab",
	Reading: "field_on(F) is load-bearing: the powers of x and the partial sums of the evaluation " +
		"must stay in F's carrier, where the two records agree; off it G's operations may differ. G " +
		"is not assumed a field, so its side is read in the restricted record mk_ring(G.add, G.zero, " +
		"G.neg, G.mul, G.one, G.sub, F.carrier): by the agreement the image of field_ring(F) under " +
		"the identity, hence a commutative ring, and F's evaluation is carried along the identity " +
		"homomorphism into it (polynomial_evaluation.EvalAlongHomomorphism). The two supports are one " +
		"because F.zero = G.zero, and every coefficient, past the length too, lies in K ⊆ F.carrier. " +
		"The coefficient set K stays fixed on both sides: irreducibility over the larger carrier is " +
		"not claimed, and is false in general.",
	Build: family.Theorem(Statement{
		Binders: "∀F:field_on(A). ∀G:field_ops(A). ∀K:set(A). ∀x:A.",
		Hypotheses: []string{
			"field_extends(F, G)",
			"K ⊆ F.carrier",
			"x ∈ F.carrier",
		},
		Conclusion: "(∀p:(num → A). " +
			"    polynomial_over(F.zero, K, p) ⇒ " +
			"    polynomial_eval(F.add, F.zero, F.mul, F.one, p, x) = " +
			"    polynomial_eval(G.add, G.zero, G.mul, G.one, p, x)) ∧ " +
			"(algebraic_over(F, K, x) ⇔ algebraic_over(G, K, x))",
	}, func(
		a *Argument,
		F field.FieldFact[on.F],
		G *Expr[FieldOps[A]],
		K *Expr[Set[A]],
		x *Member[A, on.F],
		extension, kInCarrier Fact,
	) {
		agreement := a.Unfolded(extension, fieldExtendsDef)
		parts := a.Conjuncts(
			agreement,
			"the smaller carrier lies in the larger",
			"the two zeros agree",
			"the two units agree",
			"the unary operations agree on the smaller carrier",
			"the binary operations agree on the smaller carrier")
		zero, one, binary := parts[1], parts[2], parts[4]
		carrier := a.TermAs[Set[A]]("F.carrier")
		zeroValue := a.TermAs[A]("F.zero")
		identity := a.TermAs[Fun[A, A]]("λu:A. u")
		restricted := a.TermAs[module_record.RingOps[A]](
			"mk_ring(G.add, G.zero, G.neg, G.mul, G.one, G.sub, F.carrier)")
		restrictedDef := a.Let("restricted", restricted)
		sourceRing := field.RingOn.Read(F)
		restrictedRing := a.Have(
			"the restricted record is the image of F's ring under the identity, so a commutative ring",
			"comm_ring_on(restricted)",
			restrictedDef.Rw(),
			By(
				agreement,
				set_image.ImageIdentity.At(carrier),
				ring_homomorphism.ImageCommRingOn.Read(sourceRing).At(restricted, identity)))
		hom := a.Have(
			"the identity preserves the ring operations and maps "+
				"F's carrier into the restricted carrier, F's own",
			"ring_homomorphism(field_ring(F), restricted, λu:A. u)",
			restrictedDef.Rw(),
			Unfold(ring_homomorphism.RingHomomorphism),
			SplitConjAll(
				Case(
					"F supplies the source ring",
					By(sourceRing)),
				Case(
					"the restricted record supplies the target ring",
					By(restrictedRing)),
				Case(
					"addition agrees on the carrier",
					By(binary)),
				Case(
					"multiplication agrees on the carrier",
					By(binary)),
				Case(
					"the identity preserves one",
					By(one))))
		concreteHom := a.Simplified(hom, Fwd(restrictedDef))
		evaluation := a.Have(
			"evaluation follows the identity homomorphism",
			Statement{
				Binders:    "∀p:(num → A).",
				Hypotheses: []string{"polynomial_over(F.zero, K, p)"},
				Conclusion: "polynomial_eval(F.add, F.zero, F.mul, F.one, p, x) = " +
					"polynomial_eval(G.add, G.zero, G.mul, G.one, p, x)",
			},
			Derive(func(b *Argument) {
				p := b.FixAs[Fun[Nat, A]]("p")
				polynomialInK := b.Assume()
				overCarrier := b.Have(
					"all coefficients also lie in F's carrier",
					"polynomial_over(F.zero, F.carrier, p)",
					By(kInCarrier, polynomialInK, polynomial.PolynomialOverMono.At(zeroValue, K, carrier, p)))
				b.Show(
					"the target ring has exactly G's evaluation operations",
					By(overCarrier, x, polynomial_evaluation.EvalAlongHomomorphism.Read(concreteHom).AsFact().At(p, x)))
			}))
		algebraicity := a.Have(
			"the two records share their zero, hence their zero "+
				"polynomial, so the same polynomials witness algebraicity",
			"algebraic_over(F, K, x) ⇔ algebraic_over(G, K, x)",
			Unfold(algebraic_element.AlgebraicOverDef),
			zero.Rw(),
			Derive(func(b *Argument) {
				b.Iff()
				b.Forward(
					"a polynomial vanishing in F also vanishes in G",
					func(d *Argument, exists Fact) {
						p, data := d.UnpackAs[Fun[Nat, A]](exists, "p")
						d.Take(p)
						d.Show(
							"retain its coefficients, nonzero condition and vanishing",
							By(data, evaluation.At(p)))
					})
				b.Backward(
					"a polynomial vanishing in G also vanishes in F",
					func(d *Argument, exists Fact) {
						p, data := d.UnpackAs[Fun[Nat, A]](exists, "p")
						d.Take(p)
						d.Show(
							"retain its coefficients, nonzero condition and vanishing",
							By(data, evaluation.At(p)))
					})
			}))
		a.Show(
			"evaluation agreement gives algebraicity in both records",
			By(evaluation, algebraicity))
	}),
})}

// AlgebraicOverTransport — along an injection on a field's carrier, a
// point is algebraic over a part of the carrier exactly when its image is
// algebraic over the image of the part in the transported field. ι is a
// ring homomorphism into the transported field, so evaluation at x commutes
// with it (polynomial_evaluation.EvalAlongHomomorphism). A nonzero polynomial over K
// maps coefficientwise to a nonzero one over image(ι, K)
// (polynomial.PolynomialMapNonzero), vanishing at ι(x). Back, a polynomial
// over image(ι, K) pulls back through the preimages chosen in F's carrier
// (functions.InverseOnLeft) to a nonzero polynomial over K mapping onto it,
// and its value at x, a point of F's carrier sent to the transported zero,
// is F's zero.
var AlgebraicOverTransport = algebraicOverTransportThm{family.Add(registry.ProofEntry{
	Name: "AlgebraicOverTransport",
	Key:  "prop_6194b00da114f228",
	Reading: "Injectivity is asked on all of F's carrier, not on K alone: the value at x of a " +
		"polynomial over K lies in F's carrier but in general not in K, and injectivity there is what " +
		"turns ι of the value being the transported zero into the value being F.zero. No hypothesis " +
		"asks F.zero ∈ K: polynomial_over puts a polynomial's zero tail in K, so each side implies it.",
	Build: family.Theorem(Statement{
		Binders: "∀ι:(A → B). ∀F:field_on(A). ∀K:set(A). ∀x:A.",
		Hypotheses: []string{
			"injective_on(F.carrier, ι)",
			"K ⊆ F.carrier",
			"x ∈ F.carrier",
		},
		Conclusion: "algebraic_over(transport_field(ι, F), image(ι, K), ι(x)) ⇔ algebraic_over(F, K, x)",
	}, func(
		a *Argument,
		ι *Arrow[A, B],
		F field.FieldFact[on.F],
		K *Expr[Set[A]],
		x *Member[A, on.F],
		injective, kInCarrier Fact,
	) {
		_, transportDef := a.LetAs[FieldOps[B]]("T", "transport_field(ι, F)")
		source := a.TermAs[FieldOps[A]]("F")
		carrier := a.TermAs[Set[A]]("F.carrier")
		zero := a.TermAs[A]("F.zero")
		sourceRing := field.RingOn.Read(F)
		zeroImage := a.Have(
			"ι sends the source zero to the transported zero",
			"ι(F.zero) = T.zero",
			Simp(Fwd(transportDef), Fwd(ring_transport.TransportFieldDef)),
			Basic())
		hom := a.Have(
			"ι preserves the ring operations on the source carrier",
			"ring_homomorphism(field_ring(F), field_ring(T), ι)",
			transportDef.Rw(),
			By(F, injective, ring_transport.TransportFieldHomomorphism.At(ι, source)))
		injectivity := a.Unfolded(injective, functions.InjectiveOnDef)
		zeroIn := a.Have(
			"the source zero lies in the injectivity domain",
			"F.zero ∈ F.carrier",
			By(comm_ring.ZeroIn.Read(sourceRing)))
		overCarrier := a.Have(
			"a polynomial over K is a polynomial over F's carrier",
			"∀p:(num → A). polynomial_over(K, p) ⇒ polynomial_over(F.carrier, p)",
			Derive(func(b *Argument) {
				p := b.FixAs[Fun[Nat, A]]("p")
				b.Show(
					"K lies in F's carrier",
					By(kInCarrier, b.Assume(), polynomial.PolynomialOverMono.At(zero, K, carrier, p)))
			}))
		inverseZero := a.Have(
			"the chosen preimage of the transported zero is the source zero",
			"inverse_on(F.carrier, ι, T.zero) = F.zero",
			Simp(Rev(zeroImage)),
			By(injective, zeroIn, functions.InverseOnLeft.At(carrier, ι, zero)))
		pushPolynomial := a.Have(
			"mapping coefficients preserves polynomials and nonzeroness",
			Statement{
				Binders:    "∀p:(num → A).",
				Hypotheses: []string{"polynomial_over(K, p)", "p ≠ vec_zero(F.zero)"},
				Conclusion: "polynomial_over(image(ι, K), λi:num. ι(p(i))) ∧ (λi:num. ι(p(i))) ≠ vec_zero(T.zero)",
			},
			Derive(func(b *Argument) {
				p := b.FixAs[Fun[Nat, A]]("p")
				parts := b.Conjuncts(
					b.Assume(),
					"the source coefficients form a polynomial",
					"the source polynomial is nonzero")
				isPolynomial, nonzero := parts[0], parts[1]
				mappedPolynomial := b.Have(
					"the mapped coefficients form a polynomial over the image of K",
					"polynomial_over(image(ι, K), λi:num. ι(p(i)))",
					By(
						isPolynomial,
						zeroImage,
						set_image.FunInImage,
						polynomial.PolynomialOverMap.At(
							ι, zero, b.TermAs[B]("T.zero"), K, b.TermAs[Set[B]]("image(ι, K)"), p)))
				mappedNonzero := b.Have(
					"injectivity prevents the image polynomial from becoming zero",
					"(λi:num. ι(p(i))) ≠ vec_zero(T.zero)",
					By(
						isPolynomial,
						overCarrier.At(p),
						zeroIn,
						injective,
						zeroImage,
						nonzero,
						polynomial.PolynomialMapNonzero.At(ι, zero, b.TermAs[B]("T.zero"), carrier, p)))
				b.Show(
					"finite support, coefficient membership and nonzeroness are preserved",
					By(mappedPolynomial, mappedNonzero))
			}))
		pullPolynomial := a.Have(
			"a polynomial over the image has a nonzero source polynomial",
			Statement{
				Binders:    "∀q:(num → B).",
				Hypotheses: []string{"polynomial_over(image(ι, K), q)", "q ≠ vec_zero(T.zero)"},
				Conclusion: "∃p:(num → A). polynomial_over(K, p) ∧ p ≠ vec_zero(F.zero) ∧ (λi:num. ι(p(i))) = q",
			},
			Derive(func(b *Argument) {
				b.FixAs[Fun[Nat, B]]("q")
				parts := b.Conjuncts(
					b.Assume(),
					"the image coefficients form a polynomial",
					"the image polynomial is nonzero")
				isPolynomial, nonzero := parts[0], parts[1]
				data := b.Conjuncts(
					b.Unfolded(isPolynomial, polynomial.PolynomialOverDef),
					"the image polynomial has a finite cutoff",
					"every image coefficient belongs to the image of K")
				n, finite := b.UnpackAs[Nat](data[0], "n")
				coefficientInImage := data[1]
				P, pullDef := b.LetAs[Fun[Nat, A]]("P", "λi:num. inverse_on(F.carrier, ι, q(i))")
				pointwise := b.Have(
					"pulling each coefficient returns its K-preimage",
					"∀i:num. P(i) ∈ K ∧ ι(P(i)) = q(i)",
					Derive(func(c *Argument) {
						i := c.FixAs[Nat]("i")
						k, preimage := c.ObtainAs[A](
							"the image coefficient has a preimage in K",
							"∃k:A. k ∈ K ∧ q(i) = ι(k)",
							BySets(coefficientInImage.At(i)),
							Named("k"))
						inCarrier := c.Have(
							"this preimage lies in F's carrier",
							"k ∈ F.carrier",
							BySets(kInCarrier, preimage))
						chosen := c.Have(
							"injectivity identifies the chosen preimage",
							"inverse_on(F.carrier, ι, ι(k)) = k",
							By(injective, inCarrier, functions.InverseOnLeft.At(carrier, ι, k)))
						preimageParts := c.Conjuncts(
							preimage,
							"the coefficient preimage belongs to K",
							"its image is the given coefficient")
						c.Show(
							"the pullback is that coefficient in K and maps back to q(i)",
							pullDef.Rw(),
							preimageParts[1].Rw(),
							chosen.Rw(),
							By(preimageParts[0]))
					}))
				pulledFinite := b.Have(
					"pulling coefficients preserves the finite cutoff",
					"vec⟨n⟩(P)",
					Derive(func(c *Argument) {
						tail := c.Unfolded(finite, vec_space.VecDef)
						c.Do(Simp(Fwd(vec_space.VecDef)))
						i := c.FixAs[Nat]("i")
						pastCutoff := c.Assume()
						tailZero := c.Have(
							"past the cutoff the image coefficient is the transported zero",
							"q(i) = T.zero",
							By(pastCutoff, tail.At(i)))
						c.Show(
							"the chosen preimage of each tail zero is F.zero",
							pullDef.Rw(),
							tailZero.Rw(),
							By(inverseZero))
					}))
				pulledPolynomial := b.Have(
					"the pulled coefficients form a polynomial over K",
					"polynomial_over(K, P)",
					Simp(Fwd(polynomial.PolynomialOverDef)),
					SplitConj(
						Case(
							"the pulled sequence has finite support",
							Witness(n),
							By(pulledFinite)),
						Case(
							"the chosen coefficients belong to K",
							Derive(func(c *Argument) {
								i := c.FixAs[Nat]("i")
								c.Show(
									"the pointwise pullback gives this membership",
									By(pointwise.At(i)))
							}))))
				reconstructs := b.Have(
					"mapping the pulled polynomial reconstructs the image polynomial",
					"(λi:num. ι(P(i))) = q",
					Funext(),
					Derive(func(c *Argument) {
						i := c.FixAs[Nat]("i")
						c.Show(
							"every coefficient maps back to the original one",
							By(pointwise.At(i)))
					}))
				pulledNonzero := b.Have(
					"a nonzero image cannot have zero pullback",
					"P ≠ vec_zero(F.zero)",
					Derive(func(c *Argument) {
						pulledZero := c.SupposeNot()
						imageZero := c.Have(
							"then every image coefficient would be the transported zero",
							"q = vec_zero(T.zero)",
							Funext(),
							Derive(func(d *Argument) {
								i := d.FixAs[Nat]("i")
								d.Show(
									"the reconstructed coefficient is the transported zero",
									Simp(Fwd(vec_space.VecZeroDef.Inst[B]())),
									By(pulledZero, pointwise.At(i), zeroImage, vec_space.VecZeroDef.At(zero, i)))
							}))
						c.Show(
							"the given image polynomial was nonzero",
							By(Normalized, imageZero, nonzero))
					}))
				b.Take(P)
				b.Show(
					"the pullback is a nonzero polynomial with the required image",
					By(pulledPolynomial, pulledNonzero, reconstructs))
			}))
		evaluation := a.Have(
			"evaluation at x of a polynomial over K stays in F's carrier and commutes with ι",
			Statement{
				Binders:    "∀p:(num → A).",
				Hypotheses: []string{"polynomial_over(K, p)"},
				Conclusion: "polynomial_eval(p, x) ∈ F.carrier ∧ " +
					"ι(polynomial_eval(p, x)) = polynomial_eval(λi:num. ι(p(i)), ι(x))",
			},
			Derive(func(b *Argument) {
				p := b.FixAs[Fun[Nat, A]]("p")
				b.Show(
					"F's evaluation stays in its carrier and commutes with the transport homomorphism",
					By(
						b.Assume(),
						overCarrier.At(p),
						x,
						polynomial_evaluation.EvalIn.Read(sourceRing).AsFact().At(p, x),
						polynomial_evaluation.EvalAlongHomomorphism.Read(hom).AsFact().At(p, x)))
			}))
		a.Do(Unfold(algebraic_element.AlgebraicOverDef))
		a.Iff()
		a.Forward(
			"pull a vanishing polynomial back to F",
			func(b *Argument, exists Fact) {
				q, given := b.UnpackAs[Fun[Nat, B]](exists, "q")
				parts := b.Conjuncts(
					given,
					"the polynomial is over the image of K",
					"the polynomial over the image is nonzero",
					"it vanishes at the image point")
				p, pulled := b.UnpackAs[Fun[Nat, A]](GroupPremises(parts[0], parts[1], pullPolynomial.At(q)), "p")
				pulledParts := b.Conjuncts(
					pulled,
					"the pulled polynomial is over K",
					"the pulled polynomial is nonzero",
					"its image reconstructs q")
				evaluationOfQ := b.Simplified(GroupPremises(pulledParts[0], evaluation.At(p)), Fwd(pulledParts[2]))
				value := b.TermAs[A]("polynomial_eval(p, x)")
				vanishes := b.Have(
					"injectivity recovers vanishing in the source",
					"polynomial_eval(p, x) = F.zero",
					By(injectivity.At(value, zero), zeroIn, evaluationOfQ, parts[2], zeroImage))
				b.Take(p)
				b.Show(
					"this nonzero polynomial over K vanishes at x",
					By(pulledParts[0], pulledParts[1], vanishes))
			})
		a.Backward(
			"push a vanishing polynomial to the transported field",
			func(b *Argument, exists Fact) {
				p, given := b.UnpackAs[Fun[Nat, A]](exists, "p")
				parts := b.Conjuncts(
					given,
					"the polynomial is over K",
					"the polynomial over K is nonzero",
					"it vanishes at x")
				mapped := b.TermAs[Fun[Nat, B]]("λi:num. ι(p(i))")
				mappedData := b.Have(
					"the image is a nonzero polynomial over image(ι,K)",
					"polynomial_over(image(ι, K), λi:num. ι(p(i))) ∧ (λi:num. ι(p(i))) ≠ vec_zero(T.zero)",
					By(parts[0], parts[1], pushPolynomial.At(p)))
				vanishes := b.Have(
					"the image polynomial vanishes at ι(x)",
					"polynomial_eval(λi:num. ι(p(i)), ι(x)) = T.zero",
					By(parts[0], evaluation.At(p), parts[2], zeroImage))
				b.Take(mapped)
				b.Show(
					"the mapped nonzero polynomial witnesses transported algebraicity",
					By(mappedData, vanishes))
			})
	}),
})}

// FieldExtendsSubfield — an extension holds the smaller field's carrier as
// a subfield of the larger record: each closure law of the smaller field
// carries over, the two records agreeing on that carrier.
var FieldExtendsSubfield = fieldExtendsSubfieldThm{family.Add(registry.ProofEntry{
	Name: "FieldExtendsSubfield",
	Key:  "prop_88586f5b997a6d68",
	Reading: "G is not assumed a field. The inverse clause asks G.inv(x) ∈ F.carrier at the " +
		"zero too: field_on(F) closes its carrier under F.inv at every point, the zero included " +
		"(field.InvIn), and field_extends compares the two inverses at every point of F's carrier.",
	Build: family.Theorem(Statement{
		Binders:    "∀F:field_on(A). ∀G:field_ops(A).",
		Hypotheses: []string{"field_extends(F, G)"},
		Conclusion: "subfield(G, F.carrier)",
	}, func(a *Argument, F field.FieldFact[on.F], G *Expr[FieldOps[A]], extension Fact) {
		agreement := a.Unfolded(extension, fieldExtendsDef)
		parts := a.Conjuncts(
			agreement,
			"F's carrier lies in G's",
			"the zeros agree",
			"the units agree",
			"negation and inversion agree on F's carrier",
			"the binary operations agree on F's carrier")
		carrier, zero, one, unary, binary := parts[0], parts[1], parts[2], parts[3], parts[4]
		ring := field.RingOn.Read(F)
		a.Show(
			"each subfield condition is a closure law of F read through the agreement",
			Simp(Fwd(field.SubfieldDef)),
			SplitConjAll(
				Case(
					"F's carrier lies in G's",
					By(carrier)),
				Case(
					"G's zero is F's, which lies in F",
					Simp(Rev(zero)),
					By(comm_ring.ZeroIn.Read(ring))),
				Case(
					"G's unit is F's, which lies in F",
					Simp(Rev(one)),
					By(comm_ring.OneIn.Read(ring))),
				Case(
					"addition preserves F's carrier",
					Derive(func(b *Argument) {
						x, y := b.FixAs[A]("x"), b.FixAs[A]("y")
						b.Show(
							"G's sum is F's, which lies in F",
							BySets(Normalized, b.Assume(), binary.At(x, y), comm_ring.AddIn.Read(ring).AsFact().At(x, y)))
					})),
				Case(
					"negation preserves F's carrier",
					Derive(func(b *Argument) {
						x := b.FixAs[A]("x")
						b.Show(
							"G's negative is F's, which lies in F",
							BySets(Normalized, b.Assume(), unary.At(x), comm_ring.NegIn.Read(ring).AsFact().At(x)))
					})),
				Case(
					"multiplication preserves F's carrier",
					Derive(func(b *Argument) {
						x, y := b.FixAs[A]("x"), b.FixAs[A]("y")
						b.Show(
							"G's product is F's, which lies in F",
							BySets(Normalized, b.Assume(), binary.At(x, y), comm_ring.MulIn.Read(ring).AsFact().At(x, y)))
					})),
				Case(
					"inversion preserves F's carrier",
					Derive(func(b *Argument) {
						x := b.FixAs[A]("x")
						b.Show(
							"G's inverse is F's, which lies in F",
							BySets(Normalized, b.Assume(), unary.At(x), field.InvIn.Read(F).AsFact().At(x)))
					}))))
	}),
})}

// FieldExtendsHomomorphism — including a field in a field that extends it
// keeps the ring operations: the two records agree on the smaller carrier.
var FieldExtendsHomomorphism = fieldExtendsHomomorphismThm{family.Add(registry.ProofEntry{
	Name: "FieldExtendsHomomorphism",
	Key:  "prop_b5395ecd272166bf",
	Build: family.Theorem(Statement{
		Binders:    "∀F G:field_on(A).",
		Hypotheses: []string{"field_extends(F, G)"},
		Conclusion: "ring_homomorphism(field_ring(F), field_ring(G), λy:A. y)",
	}, func(a *Argument, F field.FieldFact[on.F], G field.FieldFact[on.G], extension Fact) {
		parts := a.Conjuncts(
			a.Unfolded(extension, fieldExtendsDef),
			"F's carrier lies in G's",
			"the zeros agree",
			"the units agree",
			"negation and inversion agree on F's carrier",
			"the binary operations agree on F's carrier")
		carrier, one, binary := parts[0], parts[2], parts[4]
		a.Show(
			"G agrees with F on F's carrier, so including F in G keeps the ring operations",
			Unfold(ring_homomorphism.RingHomomorphism),
			SplitConjAll(
				Case(
					"F is a commutative ring",
					By(field.RingOn.Read(F))),
				Case(
					"G is a commutative ring",
					By(field.RingOn.Read(G))),
				Case(
					"F's carrier lies in G's",
					By(carrier, set_basic.SubsetDef)),
				Case(
					"G adds points of F as F does",
					By(binary)),
				Case(
					"G multiplies points of F as F does",
					By(binary)),
				Case(
					"the units agree",
					By(one))))
	}),
})}

// FixedFieldEmbeddingExtends — a ring homomorphism ι from F to G that
// fixes every point of F's carrier makes G an extension of F: at points
// of F's carrier, G's operation equals ι of F's result, and closure makes
// that result a fixed point too. Subtraction and division follow, each
// field subtracting by adding the negative and dividing by multiplying by
// the inverse.
var FixedFieldEmbeddingExtends = fixedFieldEmbeddingExtendsThm{family.Add(registry.ProofEntry{
	Name: "FixedFieldEmbeddingExtends",
	Key:  "prop_6889c2543df8ba2f",
	Build: family.Theorem(Statement{
		Binders: "∀F G:field_on(A). ∀ι:(A → A).",
		Hypotheses: []string{
			"ring_homomorphism(field_ring(F), field_ring(G), ι)",
			"∀x:A. x ∈ F.carrier ⇒ ι(x) = x",
		},
		Conclusion: "field_extends(F, G)",
	}, func(
		a *Argument,
		F field.FieldFact[on.F],
		G field.FieldFact[on.G],
		ι *Arrow[A, A],
		hom, fixed Fact,
	) {
		f := a.TermAs[FieldOps[A]]("F")
		g := a.TermAs[FieldOps[A]]("G")
		fCarrier := a.TermAs[Set[A]]("F.carrier")
		gCarrier := a.TermAs[Set[A]]("G.carrier")
		sourceRing, targetRing := field.RingOn.Read(F), field.RingOn.Read(G)
		carrier := a.Have(
			"every source element lies in the target carrier",
			"F.carrier ⊆ G.carrier",
			Derive(func(b *Argument) {
				b.Do(Simp(Fwd(set_basic.SubsetDef)))
				x := b.FixAs[A]("x")
				xF := b.MemberOf[on.F](x, b.Assume())
				b.Show(
					"ι carries x into G's carrier and fixes it",
					By(Normalized, xF, fixed.At(xF), ring_homomorphism.MapIn.Read(hom).AsFact().At(xF)))
			}))
		constants := a.Have(
			"the zero and the one agree",
			"F.zero = G.zero ∧ F.one = G.one",
			SplitConj(
				Case(
					"ι carries F's zero, a fixed point, to G's zero",
					By(
						Normalized,
						fixed.At(a.TermAs[A]("F.zero")),
						comm_ring.ZeroIn.Read(sourceRing),
						ring_homomorphism.MapZero.Read(hom))),
				Case(
					"ι carries F's one, a fixed point, to G's one",
					By(
						Normalized,
						fixed.At(a.TermAs[A]("F.one")),
						comm_ring.OneIn.Read(sourceRing),
						ring_homomorphism.MapOne.Read(hom))),
			))
		unary := a.Have(
			"negation and inversion agree on F's carrier",
			"∀x:A. x ∈ F.carrier ⇒ F.neg(x) = G.neg(x) ∧ F.inv(x) = G.inv(x)",
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				xF := b.MemberOf[on.F](x, b.Assume())
				negative := comm_ring.NegIn.Read(sourceRing).At(xF)
				inverse := field.InvIn.Read(F).At(xF)
				keepsInverse := b.Have(
					"ι carries F's inverse of x to G's inverse of ι(x)",
					"ι(F.inv(x)) = G.inv(ι(x))",
					By(
						F,
						G,
						xF,
						field.MapInv.At(f, g, ι, xF),
						ring_homomorphism.MapIn.Read(hom),
						ring_homomorphism.MapZero.Read(hom),
						ring_homomorphism.MapOne.Read(hom),
						ring_homomorphism.MapMul.Read(hom)))
				b.Show(
					"the negative and the inverse of x are fixed points carried to G's",
					SplitConj(
						Case(
							"ι carries F's negative of x to G's, as a homomorphism of the additive groups",
							By(
								Normalized,
								xF,
								negative,
								fixed.At(xF),
								fixed.At(negative),
								ring_homomorphism.MapNeg.Read(hom).AsFact().At(xF))),
						Case(
							"ι carries F's inverse of x to G's",
							By(Normalized, xF, inverse, fixed.At(xF), fixed.At(inverse), keepsInverse)),
					))
			}))
		ringOperations := a.Have(
			"addition and multiplication agree on F's carrier",
			"∀u v:A. u ∈ F.carrier ∧ v ∈ F.carrier ⇒ F.add(u, v) = G.add(u, v) ∧ F.mul(u, v) = G.mul(u, v)",
			Derive(func(b *Argument) {
				u, v := b.FixAs[A]("u"), b.FixAs[A]("v")
				members := b.Conjuncts(
					b.Assume(),
					"u lies in F",
					"v lies in F")
				uF, vF := b.MemberOf[on.F](u, members[0]), b.MemberOf[on.F](v, members[1])
				sum := comm_ring.AddIn.Read(sourceRing).At(uF, vF)
				product := comm_ring.MulIn.Read(sourceRing).At(uF, vF)
				b.Show(
					"the sum and the product of u and v are fixed points carried to G's",
					SplitConj(
						Case(
							"ι carries F's sum of u and v to G's",
							By(
								Normalized,
								uF,
								vF,
								sum,
								fixed.At(uF),
								fixed.At(vF),
								fixed.At(sum),
								ring_homomorphism.MapAdd.Read(hom).AsFact().At(uF, vF))),
						Case(
							"ι carries F's product of u and v to G's",
							By(
								Normalized,
								uF,
								vF,
								product,
								fixed.At(uF),
								fixed.At(vF),
								fixed.At(product),
								ring_homomorphism.MapMul.Read(hom).AsFact().At(uF, vF))),
					))
			}))
		binary := a.Have(
			"the four binary operations agree on F's carrier",
			Statement{
				Binders:    "∀x y:A.",
				Hypotheses: []string{"x ∈ F.carrier", "y ∈ F.carrier"},
				Conclusion: "F.add(x, y) = G.add(x, y) ∧ " +
					"F.mul(x, y) = G.mul(x, y) ∧ " +
					"F.sub(x, y) = G.sub(x, y) ∧ " +
					"F.div(x, y) = G.div(x, y)",
			},
			Derive(func(b *Argument) {
				x, y := b.FixAs[A]("x"), b.FixAs[A]("y")
				inF := b.Assume()
				inG := b.Have(
					"both arguments also lie in G",
					"x ∈ G.carrier ∧ y ∈ G.carrier",
					By(inF, carrier, set_basic.SubsetDef.At(fCarrier, gCarrier)))
				fMembers := b.Conjuncts(
					inF,
					"x lies in F",
					"y lies in F")
				gMembers := b.Conjuncts(
					inG,
					"x lies in G",
					"y lies in G")
				yF := b.MemberOf[on.F](y, fMembers[1])
				xG, yG := b.MemberOf[on.G](x, gMembers[0]), b.MemberOf[on.G](y, gMembers[1])
				negativeIn := b.Have(
					"the negative of y lies in F",
					"F.neg(y) ∈ F.carrier",
					By(comm_ring.NegIn.Read(sourceRing).At(yF)))
				inverseIn := b.Have(
					"the inverse of y lies in F",
					"F.inv(y) ∈ F.carrier",
					By(field.InvIn.Read(F).At(yF)))
				targetSubtraction := b.Have(
					"G subtracts by adding the negative",
					"G.sub(x, y) = G.add(x, G.neg(y))",
					By(comm_ring.SubAddNegOn.Read(targetRing).At(xG, yG)))
				targetDivision := b.Have(
					"G divides by multiplying by the inverse",
					"G.div(x, y) = G.mul(x, G.inv(y))",
					By(field.DivMulInvOn.Read(G).At(xG, yG)))
				b.Show(
					"F too subtracts by adding the negative and divides by multiplying by the inverse",
					Simp(
						Fwd(comm_ring.SubAddNegOn.Read(sourceRing)),
						Fwd(field.DivMulInvOn.Read(F)),
						Fwd(targetSubtraction),
						Fwd(targetDivision),
						Fwd(negativeIn),
						Fwd(inverseIn),
						Fwd(ringOperations),
						Fwd(unary)),
					Basic())
			}))
		a.Show(
			"carrier inclusion and the operation agreements make G an extension of F",
			By(carrier, constants, unary, binary, fieldExtendsDef.At(f, g)))
	}),
})}

// ChainUnionExtends — the union of a chain of field records extends each
// member: each chosen record is comparable with the member and agrees
// with it at every argument they both carry.
var ChainUnionExtends = chainUnionExtendsThm{family.Add(registry.ProofEntry{
	Name:    "ChainUnionExtends",
	Key:     "prop_787f690a564a4902",
	Reading: "No field axiom is used, and a member in c already makes the chosen records exist.",
	Build: family.Theorem(Statement{
		Binders: "∀c:set(field_ops(A)). ∀F:field_ops(A).",
		Hypotheses: []string{
			"chain(field_extends, c)",
			"F ∈ c",
		},
		Conclusion: "field_extends(F, chain_union_field(c))",
	}, func(a *Argument, c *Expr[Set[FieldOps[A]]], F *Expr[FieldOps[A]], isChain, inChain Fact) {
		extends := a.TermAs[Fun2[FieldOps[A], FieldOps[A], Bool]]("field_extends")
		L, unionDef := a.LetAs[FieldOps[A]]("L", "chain_union_field(c)")
		carrier := a.Have(
			"F's carrier lies in the union carrier",
			"F.carrier ⊆ L.carrier",
			Derive(func(b *Argument) {
				b.Do(unionDef.Rw(), Unfold(chainUnionFieldDef))
				occurs := b.Have(
					"F's carrier is one of the united carriers",
					"F.carrier ∈ {G.carrier | G:field_ops(A) | G ∈ c}",
					Unfold(set_basic.SetMemberDef),
					Unfold(set_basic.SetComprehensionDef),
					Unfold(set_basic.ComprehensionSpecDef),
					Witness(F),
					Basic())
				b.Show(
					"every united carrier lies in its union",
					By(occurs, set_order.MemberSubsetUnions))
			}))
		agreement := a.Have(
			"every chain member agrees with F at every argument both carry",
			Statement{
				Binders:    "∀G:field_ops(A).",
				Hypotheses: []string{"G ∈ c"},
				Conclusion: "F.zero = G.zero ∧ " +
					"F.one = G.one ∧ " +
					"(∀x:A. x ∈ F.carrier ∧ x ∈ G.carrier ⇒ F.neg(x) = G.neg(x) ∧ F.inv(x) = G.inv(x)) ∧ " +
					"(∀x y:A. " +
					"    x ∈ F.carrier ∧ y ∈ F.carrier ∧ x ∈ G.carrier ∧ y ∈ G.carrier ⇒ " +
					"    F.add(x, y) = G.add(x, y) ∧ " +
					"    F.mul(x, y) = G.mul(x, y) ∧ " +
					"    F.sub(x, y) = G.sub(x, y) ∧ " +
					"    F.div(x, y) = G.div(x, y))",
			},
			Derive(func(b *Argument) {
				b.FixAs[FieldOps[A]]("G")
				member := b.Assume()
				comparable := b.Have(
					"F and G are comparable",
					"field_extends(F, G) ∨ field_extends(G, F)",
					By(isChain, inChain, member, order.ChainDef.At(extends, c)))
				b.Do(comparable.SplitDisj(
					LeftHolds(
						"G extends F, whose carrier holds every argument compared",
						Given(func(d *Argument, extension Fact) {
							opened := d.Unfolded(extension, fieldExtendsDef)
							d.Show(
								"the operations of G agree with F's on F's carrier",
								By(opened))
						})),
					RightHolds(
						"F extends G, whose carrier holds every argument compared",
						Given(func(d *Argument, extension Fact) {
							opened := d.Unfolded(extension, fieldExtendsDef)
							d.Show(
								"the operations of F agree with G's on G's carrier",
								By(opened))
						})),
				))
			}))
		constants := a.Have(
			"the zero and the one agree",
			"F.zero = L.zero ∧ F.one = L.one",
			Derive(func(b *Argument) {
				b.Do(unionDef.Rw(), Unfold(chainUnionFieldDef))
				chosen, chosenIn := b.ObtainChosen(
					"F witnesses a member for the constant operations",
					"∃G:field_ops(A). G ∈ c",
					inChain)
				b.Show(
					"the chosen member has F's constants",
					By(chosenIn, agreement.At(chosen)))
			}))
		unary := a.Have(
			"negation and inversion agree on F's carrier",
			"∀x:A. x ∈ F.carrier ⇒ F.neg(x) = L.neg(x) ∧ F.inv(x) = L.inv(x)",
			Derive(func(b *Argument) {
				b.Do(unionDef.Rw(), Unfold(chainUnionFieldDef))
				b.FixAs[A]("x")
				inF := b.Assume()
				inhabited := b.Have(
					"F itself holds the argument x",
					"∃G:field_ops(A). G ∈ c ∧ x ∈ G.carrier",
					Witness(F),
					By(inChain, inF))
				chosen, holdsX := b.ObtainChosen(
					"the unary-operation choice holds x",
					"∃G:field_ops(A). G ∈ c ∧ x ∈ G.carrier",
					inhabited)
				agrees := b.Conjuncts(
					GroupPremises(holdsX, agreement.At(chosen)),
					"the chosen member has F's zero",
					"the chosen member has F's one",
					"it agrees with F's negation and inversion wherever both carry the argument",
					"it agrees with F's four binary operations wherever both carry the pair")
				b.Show(
					"the chosen member agrees with F at x",
					By(inF, holdsX, agrees[2]))
			}))
		binary := a.Have(
			"the four binary operations agree on F's carrier",
			Statement{
				Binders:    "∀x y:A.",
				Hypotheses: []string{"x ∈ F.carrier", "y ∈ F.carrier"},
				Conclusion: "F.add(x, y) = L.add(x, y) ∧ " +
					"F.mul(x, y) = L.mul(x, y) ∧ " +
					"F.sub(x, y) = L.sub(x, y) ∧ " +
					"F.div(x, y) = L.div(x, y)",
			},
			Derive(func(b *Argument) {
				b.Do(unionDef.Rw(), Unfold(chainUnionFieldDef))
				b.FixAs[A]("x")
				b.FixAs[A]("y")
				inF := b.Assume()
				inhabited := b.Have(
					"F itself holds both arguments",
					"∃G:field_ops(A). G ∈ c ∧ x ∈ G.carrier ∧ y ∈ G.carrier",
					Witness(F),
					By(inChain, inF))
				chosen, holdsPair := b.ObtainChosen(
					"the binary-operation choice holds both arguments",
					"∃G:field_ops(A). G ∈ c ∧ x ∈ G.carrier ∧ y ∈ G.carrier",
					inhabited)
				agrees := b.Conjuncts(
					GroupPremises(holdsPair, agreement.At(chosen)),
					"the chosen member has F's zero",
					"the chosen member has F's one",
					"it agrees with F's negation and inversion wherever both carry the argument",
					"it agrees with F's four binary operations wherever both carry the pair")
				b.Show(
					"the chosen member agrees with F at the pair",
					By(inF, holdsPair, agrees[3]))
			}))
		a.Show(
			"carrier inclusion and all operation agreements give the extension",
			By(carrier, constants, unary, binary, fieldExtendsDef.At(F, L)))
	}),
})}

// ChainUnionFieldOn — a nonempty chain of fields, each algebraic over one
// set inside its carrier, unites to a field algebraic over that set.
var ChainUnionFieldOn = chainUnionFieldOnThm{family.Add(registry.ProofEntry{
	Name: "ChainUnionFieldOn",
	Key:  "prop_e9676084c51ecfce",
	Reading: "Nonemptiness is load-bearing: the empty chain unites to the empty " +
		"carrier, which is no field (one ≠ zero needs points). K need not be a subfield; " +
		"it is the coefficient set every member reads algebraicity over. Three points " +
		"lie in one member by comparing their containing records, and each field law is " +
		"read in such a member through its agreement with the union; inv(zero) = zero is " +
		"read off any one member F, as L.inv(L.zero) = F.inv(F.zero) = F.zero = L.zero.",
	Build: family.Theorem(Statement{
		Binders: "∀c:set(field_ops(A)). ∀K:set(A).",
		Hypotheses: []string{
			"c ≠ ∅",
			"chain(field_extends, c)",
			"∀F:field_ops(A). " +
				"    F ∈ c ⇒ field_on(F) ∧ K ⊆ F.carrier ∧ (∀x:A. x ∈ F.carrier ⇒ algebraic_over(F, K, x))",
		},
		Conclusion: "field_on(chain_union_field(c)) ∧ " +
			"(∀x:A. x ∈ chain_union_field(c).carrier ⇒ algebraic_over(chain_union_field(c), K, x))",
	}, func(
		a *Argument,
		c *Expr[Set[FieldOps[A]]],
		K *Expr[Set[A]],
		nonempty, isChain, allFields Fact,
	) {
		L, unionDef := a.LetAs[FieldOps[A]]("L", "chain_union_field(c)")
		carrierMember := a.Have(
			"a union point lies in a member's carrier",
			"∀x:A. x ∈ L.carrier ⇔ ∃F:field_ops(A). F ∈ c ∧ x ∈ F.carrier",
			unionDef.Rw(),
			Unfold(chainUnionFieldDef),
			BySets())
		upperPair := a.Have(
			"two chain members lie in one member",
			Statement{
				Binders:    "∀F G:field_ops(A).",
				Hypotheses: []string{"F ∈ c", "G ∈ c"},
				Conclusion: "∃H:field_ops(A). H ∈ c ∧ F.carrier ⊆ H.carrier ∧ G.carrier ⊆ H.carrier",
			},
			Derive(func(b *Argument) {
				F := b.FixAs[FieldOps[A]]("F")
				G := b.FixAs[FieldOps[A]]("G")
				inChain := b.Assume()
				extends := b.TermAs[Fun2[FieldOps[A], FieldOps[A], Bool]]("field_extends")
				comparable := b.Have(
					"the two records are comparable",
					"field_extends(F, G) ∨ field_extends(G, F)",
					By(isChain, inChain, order.ChainDef.At(extends, c)))
				b.Do(comparable.SplitDisj(
					LeftHolds(
						"G contains both carriers",
						Given(func(d *Argument, extension Fact) {
							agreement := d.Unfolded(extension, fieldExtendsDef)
							d.Take(G)
							d.Show(
								"G contains F's carrier and its own",
								BySets(inChain, agreement))
						})),
					RightHolds(
						"F contains both carriers",
						Given(func(d *Argument, extension Fact) {
							agreement := d.Unfolded(extension, fieldExtendsDef)
							d.Take(F)
							d.Show(
								"F contains G's carrier and its own",
								BySets(inChain, agreement))
						}))))
			}))
		chainField := a.Have(
			"every chain field is a field whose operations are the union's on its own carrier",
			Statement{
				Binders:    "∀F:field_ops(A).",
				Hypotheses: []string{"F ∈ c"},
				Conclusion: "field_on(F) ∧ " +
					"F.carrier ⊆ L.carrier ∧ " +
					"F.zero = L.zero ∧ " +
					"F.one = L.one ∧ " +
					"(∀x:A. x ∈ F.carrier ⇒ F.neg(x) = L.neg(x) ∧ F.inv(x) = L.inv(x)) ∧ " +
					"(∀x y:A. " +
					"    x ∈ F.carrier ∧ y ∈ F.carrier ⇒ " +
					"    F.add(x, y) = L.add(x, y) ∧ " +
					"    F.mul(x, y) = L.mul(x, y) ∧ " +
					"    F.sub(x, y) = L.sub(x, y) ∧ " +
					"    F.div(x, y) = L.div(x, y))",
			},
			Derive(func(b *Argument) {
				F := b.FixAs[FieldOps[A]]("F")
				inChain := b.Assume()
				extension := b.Have(
					"the union extends F",
					"field_extends(F, L)",
					unionDef.Rw(),
					By(isChain, inChain, ChainUnionExtends.At(c, F)))
				b.Show(
					"F is a field by hypothesis, and the extension is the agreement",
					By(inChain, allFields.At(F), b.Unfolded(extension, fieldExtendsDef)))
			}))
		commonMember := a.Have(
			"three union points lie in one chain field",
			Statement{
				Binders:    "∀x y z:A.",
				Hypotheses: []string{"x ∈ L.carrier", "y ∈ L.carrier", "z ∈ L.carrier"},
				Conclusion: "∃F:field_ops(A). F ∈ c ∧ x ∈ F.carrier ∧ y ∈ F.carrier ∧ z ∈ F.carrier",
			},
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				y := b.FixAs[A]("y")
				z := b.FixAs[A]("z")
				inUnion := b.Assume()
				P, containsX := b.ObtainAs[FieldOps[A]](
					"x lies in one member",
					"∃P:field_ops(A). P ∈ c ∧ x ∈ P.carrier",
					By(inUnion, carrierMember.At(x)),
					Named("P"))
				Q, containsY := b.ObtainAs[FieldOps[A]](
					"y lies in one member",
					"∃Q:field_ops(A). Q ∈ c ∧ y ∈ Q.carrier",
					By(inUnion, carrierMember.At(y)),
					Named("Q"))
				R, containsZ := b.ObtainAs[FieldOps[A]](
					"z lies in one member",
					"∃R:field_ops(A). R ∈ c ∧ z ∈ R.carrier",
					By(inUnion, carrierMember.At(z)),
					Named("R"))
				S, containsPair := b.ObtainAs[FieldOps[A]](
					"combine the members holding x and y",
					"∃S:field_ops(A). S ∈ c ∧ P.carrier ⊆ S.carrier ∧ Q.carrier ⊆ S.carrier",
					By(containsX, containsY, upperPair.At(P, Q)),
					Named("S"))
				T, containsAll := b.ObtainAs[FieldOps[A]](
					"include the member holding z",
					"∃T:field_ops(A). T ∈ c ∧ S.carrier ⊆ T.carrier ∧ R.carrier ⊆ T.carrier",
					By(containsPair, containsZ, upperPair.At(S, R)),
					Named("T"))
				b.Take(T)
				b.Show(
					"carrier inclusion puts all three points in T",
					BySets(containsX, containsY, containsZ, containsPair, containsAll))
			}))
		constants := a.Have(
			"the union has its field constants and inverse at zero",
			"L.zero ∈ L.carrier ∧ L.one ∈ L.carrier ∧ L.one ≠ L.zero ∧ L.inv(L.zero) = L.zero",
			Derive(func(b *Argument) {
				F, inChain := b.ObtainAs[FieldOps[A]](
					"nonemptiness supplies one chain field",
					"∃F:field_ops(A). F ∈ c",
					By(nonempty, set_basic.MemberNotEmpty.At(c)),
					Named("F"))
				chainF := chainField.At(F)
				isField := b.Have(
					"F is a field",
					"field_on(F)",
					By(inChain, chainF))
				ring := field.RingOn.Read(isField)
				b.Do(SplitConjAll(
					Case(
						"zero belongs to the union",
						BySets(inChain, chainF, comm_ring.ZeroIn.Read(ring))),
					Case(
						"one belongs to the union",
						BySets(inChain, chainF, comm_ring.OneIn.Read(ring))),
					Case(
						"one and zero remain distinct",
						By(inChain, chainF, field.OneNotZeroOn.Read(isField))),
					Case(
						"the inverse of zero remains zero",
						By(Normalized, inChain, chainF, comm_ring.ZeroIn.Read(ring), field.InvZeroOn.Read(isField)))))
			}))
		unaryLaws := a.Have(
			"at each union point negation and inversion stay in the union and the one-point field laws hold",
			Statement{
				Binders:    "∀x:A.",
				Hypotheses: []string{"x ∈ L.carrier"},
				Conclusion: "L.neg(x) ∈ L.carrier ∧ " +
					"L.inv(x) ∈ L.carrier ∧ " +
					"L.add(L.zero, x) = x ∧ " +
					"L.add(L.neg(x), x) = L.zero ∧ " +
					"L.mul(L.one, x) = x ∧ " +
					"(x ≠ L.zero ⇒ L.mul(L.inv(x), x) = L.one)",
			},
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				F, holdsX := b.ObtainAs[FieldOps[A]](
					"a chain field holds x",
					"∃F:field_ops(A). F ∈ c ∧ x ∈ F.carrier",
					By(b.Assume(), carrierMember.At(x)),
					Named("F"))
				chainF := chainField.At(F)
				isField := b.Have(
					"F is a field",
					"field_on(F)",
					By(holdsX, chainF))
				ring := field.RingOn.Read(isField)
				addGroup := abelian_group.GroupOn.Read(comm_ring.AddGroupOn.Read(ring))
				b.Do(SplitConjAll(
					Case(
						"F's negation of x lies in the union",
						BySets(Normalized, holdsX, chainF, comm_ring.NegIn.Read(ring).AsFact().At(x))),
					Case(
						"F's inverse of x lies in the union",
						BySets(Normalized, holdsX, chainF, field.InvIn.Read(isField).AsFact().At(x))),
					Case(
						"the union's zero acts as F's zero",
						By(
							Normalized,
							holdsX,
							chainF,
							comm_ring.ZeroIn.Read(ring),
							comm_monoid.LeftIdentityOn.Read(comm_ring.AddMonoidOn.Read(ring)).AsFact().At(x))),
					Case(
						"the union's negation is F's additive inverse",
						By(
							Normalized,
							holdsX,
							chainF,
							comm_ring.NegIn.Read(ring).AsFact().At(x),
							group.LeftInverseOn.Read(addGroup).AsFact().At(x))),
					Case(
						"the union's one acts as F's one",
						By(
							Normalized,
							holdsX,
							chainF,
							comm_ring.OneIn.Read(ring),
							comm_monoid.LeftIdentityOn.Read(comm_ring.MulMonoidOn.Read(ring)).AsFact().At(x))),
					Case(
						"a nonzero x keeps F's multiplicative inverse",
						By(
							Normalized,
							holdsX,
							chainF,
							field.InvIn.Read(isField).AsFact().At(x),
							field.MulLeftInverseOn.Read(isField).AsFact().At(x)))))
			}))
		binaryLaws := a.Have(
			"at each pair of union points sums and products "+
				"stay in the union and the two-point field laws hold",
			Statement{
				Binders:    "∀x y:A.",
				Hypotheses: []string{"x ∈ L.carrier", "y ∈ L.carrier"},
				Conclusion: "L.add(x, y) ∈ L.carrier ∧ " +
					"L.mul(x, y) ∈ L.carrier ∧ " +
					"L.add(x, y) = L.add(y, x) ∧ " +
					"L.mul(x, y) = L.mul(y, x) ∧ " +
					"L.sub(x, y) = L.add(x, L.neg(y)) ∧ " +
					"L.div(x, y) = L.mul(x, L.inv(y))",
			},
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				y := b.FixAs[A]("y")
				F, holdsPair := b.ObtainAs[FieldOps[A]](
					"a chain field holds x and y, read off the three-point fact with its last two points y",
					"∃F:field_ops(A). F ∈ c ∧ x ∈ F.carrier ∧ y ∈ F.carrier",
					By(b.Assume(), commonMember.At(x, y, y)),
					Named("F"))
				chainF := chainField.At(F)
				isField := b.Have(
					"F is a field",
					"field_on(F)",
					By(holdsPair, chainF))
				ring := field.RingOn.Read(isField)
				b.Do(SplitConjAll(
					Case(
						"F's sum of x and y lies in the union",
						BySets(Normalized, holdsPair, chainF, comm_ring.AddIn.Read(ring).AsFact().At(x, y))),
					Case(
						"F's product of x and y lies in the union",
						BySets(Normalized, holdsPair, chainF, comm_ring.MulIn.Read(ring).AsFact().At(x, y))),
					Case(
						"addition commutes as in F",
						By(
							Normalized,
							holdsPair,
							chainF,
							comm_monoid.CommOn.Read(comm_ring.AddMonoidOn.Read(ring)).AsFact().At(x, y))),
					Case(
						"multiplication commutes as in F",
						By(
							Normalized,
							holdsPair,
							chainF,
							comm_monoid.CommOn.Read(comm_ring.MulMonoidOn.Read(ring)).AsFact().At(x, y))),
					Case(
						"subtraction is addition of the negation, as in F",
						By(
							Normalized,
							holdsPair,
							chainF,
							comm_ring.NegIn.Read(ring).AsFact().At(y),
							comm_ring.SubAddNegOn.Read(ring).AsFact().At(x, y))),
					Case(
						"division is multiplication by the inverse, as in F",
						By(
							Normalized,
							holdsPair,
							chainF,
							field.InvIn.Read(isField).AsFact().At(y),
							field.DivMulInvOn.Read(isField).AsFact().At(x, y)))))
			}))
		ternaryLaws := a.Have(
			"at each triple of union points associativity and distributivity hold",
			Statement{
				Binders:    "∀x y z:A.",
				Hypotheses: []string{"x ∈ L.carrier", "y ∈ L.carrier", "z ∈ L.carrier"},
				Conclusion: "L.add(x, L.add(y, z)) = L.add(L.add(x, y), z) ∧ " +
					"L.mul(x, L.mul(y, z)) = L.mul(L.mul(x, y), z) ∧ " +
					"L.mul(x, L.add(y, z)) = L.add(L.mul(x, y), L.mul(x, z))",
			},
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				y := b.FixAs[A]("y")
				z := b.FixAs[A]("z")
				F, holdsTriple := b.ObtainAs[FieldOps[A]](
					"a chain field holds x, y and z",
					"∃F:field_ops(A). F ∈ c ∧ x ∈ F.carrier ∧ y ∈ F.carrier ∧ z ∈ F.carrier",
					By(b.Assume(), commonMember.At(x, y, z)),
					Named("F"))
				chainF := chainField.At(F)
				isField := b.Have(
					"F is a field",
					"field_on(F)",
					By(holdsTriple, chainF))
				ring := field.RingOn.Read(isField)
				b.Do(SplitConjAll(
					Case(
						"addition associates as in F",
						By(
							Normalized,
							holdsTriple,
							chainF,
							comm_ring.AddIn.Read(ring).AsFact().At(y, z),
							comm_ring.AddIn.Read(ring).AsFact().At(x, y),
							comm_monoid.AssocOn.Read(comm_ring.AddMonoidOn.Read(ring)).AsFact().At(x, y, z))),
					Case(
						"multiplication associates as in F",
						By(
							Normalized,
							holdsTriple,
							chainF,
							comm_ring.MulIn.Read(ring).AsFact().At(y, z),
							comm_ring.MulIn.Read(ring).AsFact().At(x, y),
							comm_monoid.AssocOn.Read(comm_ring.MulMonoidOn.Read(ring)).AsFact().At(x, y, z))),
					Case(
						"multiplication distributes over addition as in F",
						By(
							Normalized,
							holdsTriple,
							chainF,
							comm_ring.AddIn.Read(ring).AsFact().At(y, z),
							comm_ring.MulIn.Read(ring).AsFact().At(x, y),
							comm_ring.MulIn.Read(ring).AsFact().At(x, z),
							comm_ring.LeftDistribOn.Read(ring).AsFact().At(x, y, z)))))
			}))

		additiveGroup := a.Have(
			"addition is an abelian group",
			"abelian_group_on(additive_group(field_ring(L)))",
			Simp(Fwd(abelian_group.AbelianGroupOn), Fwd(group.GroupOn)),
			By(constants, unaryLaws, binaryLaws, ternaryLaws))
		multiplicativeMonoid := a.Have(
			"multiplication is a commutative monoid",
			"comm_monoid_on(L.carrier, L.mul, L.one)",
			Simp(Fwd(comm_monoid.CommMonoidOn)),
			By(constants, unaryLaws, binaryLaws, ternaryLaws))
		unionRing := a.Have(
			"addition and multiplication form a commutative ring",
			"comm_ring_on(field_ring(L))",
			Simp(Fwd(comm_ring.CommRingOn)),
			By(additiveGroup, multiplicativeMonoid, binaryLaws, ternaryLaws))
		unionField := a.Have(
			"the commutative ring has field inverses",
			"field_on(L)",
			Simp(Fwd(field.FieldOn)),
			By(unionRing, constants, unaryLaws, binaryLaws))

		algebraicity := a.Have(
			"each union point keeps its member's algebraic witness",
			"∀x:A. x ∈ L.carrier ⇒ algebraic_over(L, K, x)",
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				F, holdsX := b.ObtainAs[FieldOps[A]](
					"a chain field holds x",
					"∃F:field_ops(A). F ∈ c ∧ x ∈ F.carrier",
					By(b.Assume(), carrierMember.At(x)),
					Named("F"))
				extension := b.Have(
					"the union extends F",
					"field_extends(F, L)",
					unionDef.Rw(),
					By(isChain, holdsX, ChainUnionExtends.At(c, F)))
				isField := b.Have(
					"F is a field",
					"field_on(F)",
					By(holdsX, allFields.At(F)))
				b.Show(
					"evaluation agreement transfers algebraicity over K",
					By(holdsX, extension, allFields.At(F), FieldExtendsEval.Read(isField).AsFact().At(L, K, x)))
			}))
		a.Show(
			"the union is a field algebraic over the same coefficient set",
			By(unionField, algebraicity))
	}),
})}

// MaximalAlgebraicExtension — every field has a maximal algebraic
// extension among field records on the same type, ordered by extension.
// Zorn's lemma runs on the algebraic extensions of K on K's type, ordered
// by field_extends: K bounds the empty chain, and a nonempty chain is
// bounded by its union (ChainUnionFieldOn, ChainUnionExtends).
var MaximalAlgebraicExtension = maximalAlgebraicExtensionThm{family.Add(registry.ProofEntry{
	Name: "MaximalAlgebraicExtension",
	Key:  "prop_d73ae386764bbf0c",
	Build: family.Theorem(Statement{
		Binders: "∀K:field_on(A).",
		Conclusion: "∃M:field_ops(A). " +
			"    field_on(M) ∧ " +
			"    field_extends(K, M) ∧ " +
			"    (∀x:A. x ∈ M.carrier ⇒ algebraic_over(M, K.carrier, x)) ∧ " +
			"    (∀G:field_ops(A). " +
			"        field_on(G) ∧ " +
			"        field_extends(M, G) ∧ " +
			"        (∀x:A. x ∈ G.carrier ⇒ algebraic_over(G, K.carrier, x)) ⇒ " +
			"        field_extends(G, M))",
		Abbrev: Abbrev{
			{Name: "extensions", Text: "{F:field_ops(A) | " +
				"    field_on(F) ∧ field_extends(K, F) ∧ (∀x:A. x ∈ F.carrier ⇒ algebraic_over(F, K.carrier, x))}"},
		},
	}, func(a *Argument, K field.FieldFact[on.K]) {
		base := a.TermAs[FieldOps[A]]("K")
		baseCarrier := a.TermAs[Set[A]]("K.carrier")
		extensions := a.TermAs[Set[FieldOps[A]]]("«extensions»")
		extends := a.TermAs[Fun2[FieldOps[A], FieldOps[A], Bool]]("field_extends")
		reflexive := a.Have(
			"the base field extends itself",
			"field_extends(K, K)",
			By(order.Reflexive.Read(FieldExtendsPreorder).At(base)))
		baseAlgebraic := a.Have(
			"every point of the base field is algebraic over its whole carrier",
			"∀x:A. x ∈ K.carrier ⇒ algebraic_over(K, K.carrier, x)",
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				member := b.Assume()
				b.Show(
					"a member of the whole-carrier subfield is algebraic",
					By(
						field.CarrierSubfield.Read(K),
						member,
						algebraic_element.MemberAlgebraic.Read(K).At(baseCarrier, x)))
			}))
		baseMember := a.Have(
			"the base field belongs to the algebraic extension family",
			"K ∈ «extensions»",
			BySets(K, baseAlgebraic, reflexive))

		chainBounds := a.Have(
			"every chain of algebraic extensions has an upper bound in the family",
			Statement{
				Binders:    "∀c:set(field_ops(A)).",
				Hypotheses: []string{"c ⊆ «extensions»", "chain(field_extends, c)"},
				Conclusion: "∃b:field_ops(A). b ∈ «extensions» ∧ upper_bound(field_extends, c, b)",
			},
			Derive(func(b *Argument) {
				c := b.FixAs[Set[FieldOps[A]]]("c")
				chain := b.Assume()
				b.Cases(b.TermAs[Bool]("c = ∅"))
				b.When(
					"the base field bounds the empty chain",
					func(d *Argument, empty Fact) {
						d.Take(base)
						d.Show(
							"the empty chain has no upper-bound comparisons to check",
							BySets(empty, baseMember, order.UpperBoundDef.At(extends, c, base)))
					})
				b.Otherwise(
					"the union bounds a nonempty chain",
					func(d *Argument, nonempty Fact) {
						union := d.TermAs[FieldOps[A]]("chain_union_field(c)")
						members := d.Have(
							"each chain member is an algebraic field containing the base carrier",
							Statement{
								Binders:    "∀F:field_ops(A).",
								Hypotheses: []string{"F ∈ c"},
								Conclusion: "field_on(F) ∧ " +
									"K.carrier ⊆ F.carrier ∧ " +
									"(∀x:A. x ∈ F.carrier ⇒ algebraic_over(F, K.carrier, x))",
							},
							Derive(func(e *Argument) {
								F := e.FixAs[FieldOps[A]]("F")
								member := e.Assume()
								e.Show(
									"membership supplies the field, carrier inclusion, and algebraicity",
									BySets(member, chain, fieldExtendsDef.At(base, F)))
							}))
						unionData := d.Have(
							"the chain union is a field algebraic over the base carrier",
							"field_on(chain_union_field(c)) ∧ "+
								"(∀x:A. x ∈ chain_union_field(c).carrier ⇒ algebraic_over(chain_union_field(c), K.carrier, x))",
							By(nonempty, members, chain, ChainUnionFieldOn.At(c, baseCarrier)))
						F, member := d.ObtainAs[FieldOps[A]](
							"choose a member of the nonempty chain",
							"∃F:field_ops(A). F ∈ c",
							BySets(nonempty))
						baseToMember := d.Have(
							"the chosen chain member extends the base",
							"field_extends(K, F)",
							BySets(member, chain))
						baseToUnion := d.Have(
							"the union extends the base through the chosen member",
							"field_extends(K, chain_union_field(c))",
							By(
								chain,
								member,
								ChainUnionExtends.At(c, F),
								baseToMember,
								order.Transitive.Read(FieldExtendsPreorder).At(base, F, union)))
						d.Take(union)
						d.Show(
							"the union belongs to the family and bounds the chain",
							Simp(Fwd(order.UpperBoundDef)),
							BySets(chain, baseToUnion, unionData, ChainUnionExtends))
					})
			}))

		M, maximal := a.ObtainAs[FieldOps[A]](
			"Zorn supplies a maximal algebraic extension",
			"∃M:field_ops(A). maximal(field_extends, «extensions», M)",
			By(chainBounds, order.Zorn.Read(FieldExtendsPreorder).At(extensions)))
		maximalData := a.Unfolded(maximal, order.MaximalDef)
		parts := a.Conjuncts(
			maximalData,
			"the maximal field belongs to the algebraic extension family",
			"a field in the family above it also extends back into it")
		baseToMaximal := a.Have(
			"the maximal field extends the base",
			"field_extends(K, M)",
			BySets(parts[0]))
		maximalExtension := a.Have(
			"every algebraic field above the maximal member extends back into it",
			Statement{
				Binders: "∀G:field_ops(A).",
				Hypotheses: []string{
					"field_on(G)",
					"field_extends(M, G)",
					"∀x:A. x ∈ G.carrier ⇒ algebraic_over(G, K.carrier, x)",
				},
				Conclusion: "field_extends(G, M)",
			},
			Derive(func(b *Argument) {
				G := b.FixAs[FieldOps[A]]("G")
				above := b.Assume()
				baseToG := b.Have(
					"G extends the base by transitivity",
					"field_extends(K, G)",
					By(baseToMaximal, above, order.Transitive.Read(FieldExtendsPreorder).At(base, M, G)))
				inFamily := b.Have(
					"G belongs to the same algebraic extension family",
					"G ∈ «extensions»",
					BySets(baseToG, above))
				b.Show(
					"maximality supplies the reverse extension",
					By(parts[1].At(G), inFamily, above))
			}))
		a.Take(M)
		a.Show(
			"the chosen member has the required field, algebraicity, and maximality properties",
			BySets(maximalExtension, parts[0]))
	}),
})}
