// closure.go — the algebraic closure of a field on A, built in the host
// type set(prod(num, num → A)): a field of the host algebraic over an image
// of a set of A is no larger than the pairs of a sequence num → A and an
// index, so it has room off its carrier for its polynomials, and the
// maximal algebraic extension of the field's copy is algebraically closed.

package algebraic_closure

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_domain"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_division"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_evaluation"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_roots"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_transport"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/relations/order"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinal"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// AlgebraicExtensionBound — a field algebraic over the image of a set of
// another type is no larger than the pairs of a sequence of that type and
// an index.
var AlgebraicExtensionBound = algebraicExtensionBoundThm{family.Add(registry.ProofEntry{
	Name: "AlgebraicExtensionBound",
	Key:  "prop_8ad0e998b38b4dc5",
	Reading: "ι need not be injective: a coefficient is pulled back to any preimage, and the " +
		"pulled-back sequence still determines the polynomial, its image under ι (InverseOnRight). " +
		"image(ι, k) ⊆ L.carrier is load-bearing: an off-carrier coefficient z with L.mul(z, ·) = L.zero " +
		"would make every point algebraic. The bound is read on the base field's type A, not on the host.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(B). ∀ι:(A → B). ∀k:set(A).",
		Hypotheses: []string{
			"image(ι, k) ⊆ L.carrier",
			"∀x:B. x ∈ L.carrier ⇒ algebraic_over(L, image(ι, k), x)",
		},
		Conclusion: "card_le(L.carrier, 𝕌⟨A:prod(num → A, num)⟩)",
		Abbrev: Abbrev{
			{Name: "roots", Text: "λp:(num → B). polynomial_roots(L.carrier, p)"},
		},
	}, func(a *Argument, L field.FieldFact[on.L], ι *Arrow[A, B], k *Expr[Set[A]], h Fact) {
		parts := a.Conjuncts(
			h,
			"the coefficient image lies in the field",
			"every carrier point is algebraic over the image")
		imageInCarrier, algebraic := parts[0], parts[1]
		fieldValue := a.TermAs[FieldOps[B]]("L")
		zero := a.TermAs[B]("L.zero")
		carrier := a.TermAs[Set[B]]("L.carrier")
		base := a.TermAs[Set[B]]("image(ι, k)")

		polynomials := a.Have(
			"each carrier point is a root of a nonzero polynomial over the image and the field",
			Statement{
				Binders:    "∀x:B.",
				Hypotheses: []string{"x ∈ L.carrier"},
				Conclusion: "∃p:(num → B). " +
					"    polynomial_over(image(ι, k), p) ∧ " +
					"    polynomial_over(L.carrier, p) ∧ " +
					"    p ≠ vec_zero ∧ " +
					"    polynomial_eval(p, x) = L.zero",
			},
			Derive(func(b *Argument) {
				x := b.FixAs[B]("x")
				member := b.Assume()
				p, data := b.ObtainAs[Fun[Nat, B]](
					"choose a nonzero polynomial vanishing at x",
					"∃p:(num → B). polynomial_over(image(ι, k), p) ∧ p ≠ vec_zero ∧ polynomial_eval(p, x) = L.zero",
					By(algebraic.At(x), member, algebraic_element.AlgebraicOverDef.At(fieldValue, base, x)))
				b.Take(p)
				b.Show(
					"its coefficients also lie in the field",
					By(imageInCarrier, data, polynomial.PolynomialOverMono.At(zero, base, carrier, p)))
			}))

		enumerableRoots := a.Have(
			"the carrier roots of each nonzero polynomial have a countable cover",
			Statement{
				Binders:    "∀p:(num → B).",
				Hypotheses: []string{"polynomial_over(L.carrier, p)", "p ≠ vec_zero"},
				Conclusion: "∃e:(num → B). «roots»(p) ⊆ image(e, 𝕌⟨A:num⟩)",
			},
			Derive(func(b *Argument) {
				p := b.FixAs[Fun[Nat, B]]("p")
				guard := b.Assume()
				roots := b.TermAs[Set[B]]("«roots»(p)")
				b.Show(
					"the finite root set is countable and admits a cover",
					By(
						guard,
						polynomial_roots.RootBound.Read(integral_domain.FieldIntegralDomain.Read(L)).At(p),
						cardinal.FiniteCountable.At(roots),
						cardinal.CountableCover.At(roots)))
			}))
		_, rootCover := a.ObtainAs[Fun[Fun[Nat, B], Fun[Nat, B]]](
			"choose the root enumeration as a function of the polynomial",
			"∃E:((num → B) → num → B). ∀p:(num → B). "+
				"    polynomial_over(L.carrier, p) ∧ p ≠ vec_zero ⇒ «roots»(p) ⊆ image(E(p), 𝕌⟨A:num⟩)",
			Derive(func(b *Argument) {
				b.Take(b.TermAs[Fun[Fun[Nat, B], Fun[Nat, B]]](
					"λp:(num → B). εe:(num → B). «roots»(p) ⊆ image(e, 𝕌⟨A:num⟩)"))
				p := b.FixAs[Fun[Nat, B]]("p")
				guard := b.Assume()
				b.Show(
					"choice picks a cover for every nonzero polynomial",
					By(enumerableRoots.At(p), guard))
			}),
			Named("E"))

		decode, decodeDef := a.LetAs[Fun[Prod[Fun[Nat, A], Nat], B]](
			"decode", "λz:prod(num → A, num). E(λn:num. ι(fst(z)(n)), snd(z))")
		codes := a.Have(
			"every carrier point decodes from a coefficient sequence and a root index",
			"∀x:B. x ∈ L.carrier ⇒ ∃z:prod(num → A, num). decode(z) = x",
			Derive(func(b *Argument) {
				x := b.FixAs[B]("x")
				member := b.Assume()
				p, data := b.UnpackAs[Fun[Nat, B]](GroupPremises(member, polynomials.At(x)), "p")
				_, pulledBack := b.LetAs[Fun[Nat, A]]("q", "λn:num. inverse_on(k, ι, p(n))")
				coefficientImages := b.Have(
					"every coefficient has a preimage in k",
					"∀n:num. p(n) ∈ image(ι, k)",
					By(data, polynomial.PolynomialOverDef.At(zero, base, p)))
				reconstructed := b.Have(
					"the pulled sequence reconstructs the polynomial",
					"(λn:num. ι(q(n))) = p",
					Derive(func(c *Argument) {
						c.Do(pulledBack.Rw(), Funext())
						n := c.FixAs[Nat]("n")
						c.Show(
							"inverse_on is a right inverse at every coefficient",
							By(coefficientImages.At(n), functions.InverseOnRight.At(k, ι, c.TermAs[B]("p(n)"))))
					}))
				_, indexedRoot := b.ObtainAs[Nat](
					"take the root's index in its polynomial's enumeration",
					"∃m:num. E(p, m) = x",
					BySets(
						b.Unfolded(GroupPremises(data, rootCover.At(p)), polynomial_roots.PolynomialRootsDef),
						member,
						data),
					Named("m"))
				b.Take(b.TermAs[Prod[Fun[Nat, A], Nat]]("(q, m)"))
				b.Show(
					"this sequence and index decode to x",
					decodeDef.Rw(),
					Simp(Fwd(pairs.Fst), Fwd(pairs.Snd)),
					reconstructed.Rw(),
					By(indexedRoot))
			}))
		a.Do(Simp(Fwd(cardinal.CardLeCover)))
		a.Take(decode)
		a.Show(
			"the decoder covers the carrier",
			BySets(codes))
	}),
})}

// _ClosureHost is the closure's host type, set(prod(num, num → A)).
type _ClosureHost = Set[Prod[Nat, Fun[Nat, A]]]

// AlgebraicExtensionRoom — the polynomials of a field algebraic over an
// image of A fit outside its carrier in the closure host: the carrier is
// no larger than the pairs of a sequence of A and an index
// (AlgebraicExtensionBound), which are the host's underlying pairs up to
// the swap, so by Cantor it is strictly smaller than the host; the pairs
// of host points fit into the host (cardinal.PairsIntoPowerSet), so the
// carrier leaves a whole copy of the host off it (cardinal.ComplementRoom);
// the polynomials are sequences of host points, and those fit into the
// host (cardinal.SequencesIntoPowerSet).
var AlgebraicExtensionRoom = algebraicExtensionRoomThm{family.Add(registry.ProofEntry{
	Name: "AlgebraicExtensionRoom",
	Key:  "prop_ea4098e237a27f4a",
	Reading: "Both hypotheses enter through AlgebraicExtensionBound, " +
		"the inclusion image(ι, k) ⊆ L.carrier load-bearing there.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(set(prod(num, num → A))). ∀ι:(A → set(prod(num, num → A))). ∀k:set(A).",
		Hypotheses: []string{
			"image(ι, k) ⊆ L.carrier",
			"∀x:set(prod(num, num → A)). x ∈ L.carrier ⇒ algebraic_over(L, image(ι, k), x)",
		},
		Conclusion: "card_le(«polynomials», «outside»)",
		Abbrev: Abbrev{
			{Name: "indexPairs", Text: "𝕌⟨A:prod(num → A, num)⟩"},
			{Name: "hostPairs", Text: "𝕌⟨A:prod(num, num → A)⟩"},
			{Name: "host", Text: "𝕌⟨A:set(prod(num, num → A))⟩"},
			{Name: "sequences", Text: "𝕌⟨A:num → set(prod(num, num → A))⟩"},
			{Name: "outside", Text: "{x:set(prod(num, num → A)) | x ∉ L.carrier}"},
			{Name: "polynomials", Text: "polynomial_ring(field_ring(L)).carrier"},
		},
	}, func(
		a *Argument,
		L field.FieldFact[on.L],
		ι *Arrow[A, _ClosureHost],
		k *Expr[Set[A]],
		algebraic Fact,
	) {
		fieldValue := a.TermAs[FieldOps[_ClosureHost]]("L")
		carrier := a.TermAs[Set[_ClosureHost]]("L.carrier")
		indexPairs := a.TermAs[Set[Prod[Fun[Nat, A], Nat]]]("«indexPairs»")
		hostPairs := a.TermAs[Set[Prod[Nat, Fun[Nat, A]]]]("«hostPairs»")
		host := a.TermAs[Set[_ClosureHost]]("«host»")
		sequences := a.TermAs[Set[Fun[Nat, _ClosureHost]]]("«sequences»")
		outside := a.TermAs[Set[_ClosureHost]]("«outside»")
		polynomials := a.TermAs[Set[Fun[Nat, _ClosureHost]]]("«polynomials»")

		swapped := a.Have(
			"swapping the factors of the host pairs covers the index pairs",
			"card_le(«indexPairs», «hostPairs»)",
			Simp(Fwd(cardinal.CardLeCover)),
			Witness(a.TermAs[Fun[Prod[Nat, Fun[Nat, A]], Prod[Fun[Nat, A], Nat]]](
				"λz:prod(num, num → A). (snd(z), fst(z))")),
			Simp(Fwd(set_basic.SubsetDef), Fwd(set_basic.InImage), Fwd(set_basic.InUniv)),
			Derive(func(b *Argument) {
				b.FixAs[Prod[Fun[Nat, A], Nat]]("y")
				b.Take(b.TermAs[Prod[Nat, Fun[Nat, A]]]("(snd(y), fst(y))"))
				b.Show(
					"swapping y's factors twice returns y",
					Simp(Fwd(pairs.Fst), Fwd(pairs.Snd), Fwd(pairs.PairEta)),
					Basic())
			}))
		encoded := a.Have(
			"algebraicity bounds the carrier by coefficient sequences and root indices",
			"card_le(L.carrier, «indexPairs»)",
			By(L, algebraic, AlgebraicExtensionBound.At(fieldValue, ι, k)))
		reordered := a.Have(
			"the carrier is no larger than the host's underlying pairs",
			"card_le(L.carrier, «hostPairs»)",
			By(encoded, swapped, cardinal.CardLeTrans.At(carrier, indexPairs, hostPairs)))
		strict := a.Have(
			"Cantor makes the carrier strictly smaller than the host",
			"card_lt(L.carrier, «host»)",
			By(
				reordered,
				cardinal.CantorUniv.Inst[Prod[Nat, Fun[Nat, A]]](),
				cardinal.CardLeLtTrans.At(carrier, hostPairs, host)))

		complementRoom := a.Have(
			"the pairs of host points fit into the host, so the complement contains a copy of the whole host",
			"card_le(«host», «outside»)",
			By(cardinal.PairsIntoPowerSet.Inst[Fun[Nat, A]](), strict, cardinal.ComplementRoom.At(carrier)))
		sequenceBound := a.Have(
			"all host-valued sequences fit into the host",
			"card_le(«sequences», «host»)",
			By(cardinal.SequencesIntoPowerSet.Inst[Fun[Nat, A]]()))
		sequenceRoom := a.Have(
			"all host-valued sequences fit outside the carrier",
			"card_le(«sequences», «outside»)",
			By(sequenceBound, complementRoom, cardinal.CardLeTrans.At(sequences, host, outside)))
		polynomialBound := a.Have(
			"the polynomial carrier is a subset of all coefficient sequences",
			"card_le(«polynomials», «sequences»)",
			Simp(Fwd(polynomial.PolynomialRingDef)),
			BySets(cardinal.CardLeSubset.At(polynomials, sequences)))
		a.Show(
			"the polynomials fit outside the field carrier",
			By(polynomialBound, sequenceRoom, cardinal.CardLeTrans.At(polynomials, sequences, outside)))
	}),
})}

// ClosureEmbeddingInjective — a ↦ {(0, λn. a)} is one-to-one: equal
// singletons have equal members, and equal pairs (0, λn. x), (0, λn. y)
// have equal constant sequences, so x = y.
var ClosureEmbeddingInjective = closureEmbeddingInjectiveThm{family.Add(registry.ProofEntry{
	Name: "ClosureEmbeddingInjective",
	Key:  "prop_a7449349d6457b67",
	Build: family.Theorem("∀s:set(A). injective_on(s, «closureEmbedding»)",
		func(a *Argument, s *Expr[Set[A]]) {
			a.Show(
				"the singleton of a constant sequence determines its value",
				Simp(Fwd(functions.InjectiveOnDef)),
				Derive(func(b *Argument) {
					b.FixAs[A]("x")
					b.FixAs[A]("y")
					equalCodes := b.Assume()
					zero := b.TermAs[Nat]("0")
					constantX := b.TermAs[Fun[Nat, A]]("λn:num. x")
					constantY := b.TermAs[Fun[Nat, A]]("λn:num. y")
					sequences := b.Have(
						"equal singleton codes have equal constant sequences",
						"(λn:num. x) = (λn:num. y)",
						BySets(equalCodes, pairs.PairEq.At(zero, constantX, zero, constantY)))
					b.Show(
						"equal constant sequences have equal values",
						By(sequences))
				}))
		}),
})}

// AlgebraicClosureInHost — every field has, in its host type, an
// algebraically closed field extending its transported copy and algebraic
// over it: the maximal algebraic extension M of the copy
// (MaximalAlgebraicExtension). A polynomial of positive degree over M has
// an irreducible factor; the host has room off M's carrier for M's
// polynomials (AlgebraicExtensionRoom), so a root of the factor adjoins in
// an extension G of M inside the host (RootAdjunctionInHost). G is
// algebraic over M's carrier and so over the copy's
// (algebraic_element.AlgebraicOverTrans), maximality brings G back into M,
// and the root of the factor, now in M, is a root of the polynomial.
var AlgebraicClosureInHost = algebraicClosureInHostThm{family.Add(registry.ProofEntry{
	Name: "AlgebraicClosureInHost",
	Key:  "prop_22c09fd6835539f4",
	Build: family.Theorem(Statement{
		Binders: "∀K:field_on(A).",
		Conclusion: "∃M:field_ops(set(prod(num, num → A))). " +
			"    field_on(M) ∧ " +
			"    algebraically_closed_field(M) ∧ " +
			"    field_extends(transport_field(«closureEmbedding», K), M) ∧ " +
			"    (∀x:set(prod(num, num → A)). " +
			"        x ∈ M.carrier ⇒ algebraic_over(M, image(«closureEmbedding», K.carrier), x))",
	}, func(a *Argument, K field.FieldFact[on.K]) {
		base := a.TermAs[FieldOps[A]]("K")
		baseCarrier := a.TermAs[Set[A]]("K.carrier")
		embedding := a.TermAs[Fun[A, _ClosureHost]]("«closureEmbedding»")
		injective := ClosureEmbeddingInjective.At(baseCarrier)
		T, copyDef := a.LetAs[FieldOps[_ClosureHost]]("T", "transport_field(«closureEmbedding», K)")
		copyField := a.Have(
			"the transported copy is a field in the host",
			"field_on(T)",
			Simp(Fwd(copyDef)),
			By(K, injective, ring_transport.TransportFieldOn.At(embedding, base)))
		copyImage := a.Have(
			"the transported carrier is the image of the base carrier",
			"T.carrier = image(«closureEmbedding», K.carrier)",
			Simp(Fwd(copyDef), Fwd(ring_transport.TransportFieldDef)),
			Basic())
		M, maximal := a.UnpackAs[FieldOps[_ClosureHost]](MaximalAlgebraicExtension.Read(copyField), "M")
		maximalParts := a.Conjuncts(
			maximal,
			"M is a field",
			"M extends the transported copy",
			"M is algebraic over the copy's carrier",
			"every algebraic extension above M also extends back into M")
		MField, copyToM, MAlgebraic, maximality :=
			maximalParts[0], maximalParts[1], maximalParts[2], maximalParts[3]
		copyCarrier := a.TermAs[Set[_ClosureHost]]("T.carrier")
		MCarrier := a.TermAs[Set[_ClosureHost]]("M.carrier")
		MCoefficients := a.TermAs[module_record.RingOps[_ClosureHost]]("field_ring(M)")
		imageIncluded := a.Have(
			"the image of the base carrier lies in M",
			"image(«closureEmbedding», K.carrier) ⊆ M.carrier",
			Simp(Rev(copyImage)),
			By(copyToM, fieldExtendsDef.At(T, M)))
		imageAlgebraic := a.Have(
			"M is algebraic over the image of the base carrier",
			Statement{
				Binders: "∀x:set(prod(num, num → A)).",
				Hypotheses: []string{
					"x ∈ M.carrier",
				},
				Conclusion: "algebraic_over(M, image(«closureEmbedding», K.carrier), x)",
			},
			Simp(Rev(copyImage)),
			By(MAlgebraic))
		room := a.Have(
			"the host has room outside M for its polynomials",
			"card_le(polynomial_ring(field_ring(M)).carrier, {x:set(prod(num, num → A)) | x ∉ M.carrier})",
			By(MField, imageIncluded, imageAlgebraic, AlgebraicExtensionRoom.At(M, embedding, baseCarrier)))

		closed := a.Have(
			"maximality forces M to be algebraically closed",
			"algebraically_closed_field(M)",
			Simp(Fwd(AlgebraicallyClosedDef)),
			Derive(func(b *Argument) {
				p := b.FixAs[Fun[Nat, _ClosureHost]]("p")
				positive := b.Assume()
				q, factor := b.ObtainAs[Fun[Nat, _ClosureHost]](
					"choose an irreducible divisor of the positive-degree polynomial",
					"∃q:(num → set(prod(num, num → A))). "+
						"    polynomial_irreducible(field_ring(M), q) ∧ polynomial_divides(field_ring(M), q, p)",
					By(positive, polynomial_division.IrreducibleFactorExists.Read(MField).At(p)))
				factorParts := b.Conjuncts(
					factor,
					"q is irreducible",
					"q divides p")
				G, adjunction := b.ObtainAs[FieldOps[_ClosureHost]](
					"adjoin a root of q inside the host",
					"∃G:field_ops(set(prod(num, num → A))). "+
						"    field_on(G) ∧ "+
						"    field_extends(M, G) ∧ "+
						"    (∃x:set(prod(num, num → A)). "+
						"        x ∈ G.carrier ∧ polynomial_eval(G.add, G.zero, G.mul, G.one, q, x) = G.zero) ∧ "+
						"    (∀x:set(prod(num, num → A)). x ∈ G.carrier ⇒ algebraic_over(G, M.carrier, x))",
					By(factorParts[0], room, RootAdjunctionInHost.Read(MField).At(q)))
				adjunctionParts := b.Conjuncts(
					adjunction,
					"G is a field",
					"G extends M",
					"q has a root in G",
					"G is algebraic over M's carrier")
				GField, MToG, rootExists, GAlgebraic :=
					adjunctionParts[0], adjunctionParts[1], adjunctionParts[2], adjunctionParts[3]
				copyToG := b.Have(
					"G extends the transported copy through M",
					"field_extends(T, G)",
					By(copyToM, MToG, order.Transitive.Read(FieldExtendsPreorder).At(T, M, G)))
				copySubfield := b.Have(
					"the transported carrier is a subfield of G",
					"subfield(G, T.carrier)",
					By(copyToG, FieldExtendsSubfield.Read(copyField).At(G)))
				MInG := b.Have(
					"M's carrier lies in G",
					"M.carrier ⊆ G.carrier",
					By(MToG, fieldExtendsDef.At(M, G)))
				oldAlgebraic := b.Have(
					"every old point remains algebraic over the copy in G",
					"∀y:set(prod(num, num → A)). y ∈ M.carrier ⇒ algebraic_over(G, T.carrier, y)",
					Derive(func(d *Argument) {
						y := d.FixAs[_ClosureHost]("y")
						member := d.Assume()
						d.Show(
							"extension evaluation transfers the old algebraicity",
							By(
								MAlgebraic.At(y),
								member,
								imageIncluded,
								copyImage,
								MToG,
								FieldExtendsEval.Read(MField).AsFact().At(G, copyCarrier, y)))
					}))
				stillAlgebraic := b.Have(
					"the adjunction remains algebraic over the transported copy",
					"∀x:set(prod(num, num → A)). x ∈ G.carrier ⇒ algebraic_over(G, T.carrier, x)",
					Derive(func(d *Argument) {
						x := d.FixAs[_ClosureHost]("x")
						member := d.Assume()
						d.Show(
							"algebraic transitivity descends from M's carrier to the copy",
							By(
								copySubfield,
								MInG,
								oldAlgebraic,
								member,
								GAlgebraic.At(x),
								algebraic_element.AlgebraicOverTrans.Read(GField).AsFact().At(copyCarrier, MCarrier, x)))
					}))
				GToM := b.Have(
					"maximality gives the reverse extension",
					"field_extends(G, M)",
					By(maximality.At(G), GField, MToG, stillAlgebraic))
				GInM := b.Have(
					"the adjunction's carrier lies back in M",
					"G.carrier ⊆ M.carrier",
					By(GToM, fieldExtendsDef.At(G, M)))
				x, rootInG := b.UnpackAs[_ClosureHost](rootExists, "x")
				rootInM := b.Have(
					"the adjoined root lies in M",
					"x ∈ M.carrier",
					BySets(rootInG, GInM))
				qPolynomial := b.Have(
					"the irreducible divisor is a polynomial over M",
					"polynomial_over(M.zero, M.carrier, q)",
					By(factorParts[0], polynomial_division.PolynomialIrreducibleDef.At(MCoefficients, q)))
				zeros := b.Have(
					"M and G have the same zero",
					"M.zero = G.zero",
					By(MToG, fieldExtendsDef.At(M, G)))
				evaluations := b.Have(
					"q has the same evaluation at this M-point in M and G",
					"polynomial_eval(M.add, M.zero, M.mul, M.one, q, x) = "+
						"polynomial_eval(G.add, G.zero, G.mul, G.one, q, x)",
					By(
						MToG,
						rootInM,
						qPolynomial,
						set_order.SubsetRefl.At(MCarrier),
						FieldExtendsEval.Read(MField).AsFact().At(G, MCarrier, x)))
				qRoot := b.Have(
					"the adjoined point is a root of q in M",
					"polynomial_eval(M.add, M.zero, M.mul, M.one, q, x) = M.zero",
					Simp(Fwd(evaluations), Fwd(zeros)),
					By(rootInG))
				r, product := b.ObtainAs[Fun[Nat, _ClosureHost]](
					"write the original polynomial as q times its cofactor",
					"∃r:(num → set(prod(num, num → A))). "+
						"    polynomial_over(M.zero, M.carrier, r) ∧ p = polynomial_mul(M.add, M.zero, M.mul, q, r)",
					By(factorParts[1], polynomial_division.PolynomialDividesDef.At(MCoefficients, q, p)))
				productParts := b.Conjuncts(
					product,
					"the cofactor is a polynomial",
					"p is q times the cofactor")
				pRoot := b.Have(
					"a root of q is a root of its polynomial multiple p",
					"polynomial_eval(M.add, M.zero, M.mul, M.one, p, x) = M.zero",
					Simp(Fwd(productParts[1])),
					By(
						qPolynomial,
						productParts[0],
						rootInM,
						qRoot,
						polynomial_evaluation.EvalMulRoot.Read(field.RingOn.Read(MField)).AsFact().At(q, r, x)))
				b.Take(x)
				b.Show(
					"the positive-degree polynomial has a root in M",
					By(rootInM, pRoot))
			}))
		a.Take(M)
		a.Show(
			"M is closed, extends the copy, and is algebraic over its image carrier",
			By(MField, closed, copyToM, imageAlgebraic))
	}),
})}

// AlgebraicClosureFieldOn — every field is isomorphic to a subfield of
// an algebraically closed field algebraic over it: its algebraic closure.
// M is AlgebraicClosureInHost's. The embedding is a ring homomorphism
// into the transported copy, which M includes, so one into M, and the
// image of K is a subfield of M (ring_homomorphism.ImageSubfield); with
// that image as its target the embedding, one-to-one, is an isomorphism.
var AlgebraicClosureFieldOn = algebraicClosureFieldOnThm{family.Add(registry.ProofEntry{
	Name: "AlgebraicClosureFieldOn",
	Key:  "prop_b78f7575f9422026",
	Reading: "This is the form a statement over an ambient closed field reads, a " +
		"subfield of M; the closure is unique up to isomorphism over K, which is not stated.",
	Build: family.Theorem(Statement{
		Binders: "∀K:field_on(A).",
		Conclusion: "∃M:field_ops(set(prod(num, num → A))). " +
			"    field_on(M) ∧ " +
			"    algebraically_closed_field(M) ∧ " +
			"    subfield(M, image(«closureEmbedding», K.carrier)) ∧ " +
			"    ring_isomorphism(field_ring(K), " +
			"        restrict_ring(field_ring(M), image(«closureEmbedding», K.carrier)), " +
			"        «closureEmbedding») ∧ " +
			"    (∀x:set(prod(num, num → A)). " +
			"        x ∈ M.carrier ⇒ algebraic_over(M, image(«closureEmbedding», K.carrier), x))",
	}, func(a *Argument, K field.FieldFact[on.K]) {
		base := a.TermAs[FieldOps[A]]("K")
		embedding := a.TermAs[Fun[A, _ClosureHost]]("«closureEmbedding»")
		T, copyDef := a.LetAs[FieldOps[_ClosureHost]]("T", "transport_field(«closureEmbedding», K)")
		M, closure := a.UnpackAs[FieldOps[_ClosureHost]](a.Simplified(
			AlgebraicClosureInHost.Read(K),
			Rev(copyDef)), "M")
		parts := a.Conjuncts(
			closure,
			"M is a field",
			"M is algebraically closed",
			"M extends the transported copy",
			"M is algebraic over the image of K")
		MField, closed, extension, algebraic := parts[0], parts[1], parts[2], parts[3]

		injective := ClosureEmbeddingInjective.At(a.TermAs[Set[A]]("K.carrier"))
		copyField := a.Have(
			"the transported copy is a field",
			"field_on(T)",
			Simp(Fwd(copyDef)),
			By(K, injective, ring_transport.TransportFieldOn.At(embedding, base)))
		copyHom := a.Have(
			"the embedding is a ring homomorphism into the transported copy",
			"ring_homomorphism(field_ring(K), field_ring(T), «closureEmbedding»)",
			Simp(Fwd(copyDef)),
			By(K, injective, ring_transport.TransportFieldHomomorphism.At(embedding, base)))
		inclusionHom := a.Have(
			"the extension includes the copy as a ring homomorphism",
			"ring_homomorphism(field_ring(T), field_ring(M), λy:set(prod(num, num → A)). y)",
			By(MField, copyField, extension, FieldExtendsHomomorphism.At(T, M)))
		baseRing := a.TermAs[module_record.RingOps[A]]("field_ring(K)")
		copyRing := a.TermAs[module_record.RingOps[_ClosureHost]]("field_ring(T)")
		MRing := a.TermAs[module_record.RingOps[_ClosureHost]]("field_ring(M)")
		inclusion := a.TermAs[Fun[_ClosureHost, _ClosureHost]]("λy:set(prod(num, num → A)). y")
		intoM := a.Have(
			"the embedding followed by the inclusion is a homomorphism into M",
			"ring_homomorphism(field_ring(K), field_ring(M), «closureEmbedding»)",
			By(
				copyHom,
				inclusionHom,
				ring_homomorphism.RingHomCompose.At(baseRing, copyRing, MRing, embedding, inclusion)))
		imageSubfield := a.Have(
			"the image of K under a homomorphism into M is a subfield of M",
			"subfield(M, image(«closureEmbedding», K.carrier))",
			By(MField, intoM, ring_homomorphism.ImageSubfield.Read(K).At(M, embedding)))
		imageCarrier := a.TermAs[Set[_ClosureHost]]("image(«closureEmbedding», K.carrier)")
		imageHom := a.Have(
			"its values lie in the image, a subring of M, which is then its target",
			"ring_homomorphism(field_ring(K), "+
				"    restrict_ring(field_ring(M), image(«closureEmbedding», K.carrier)), "+
				"    «closureEmbedding»)",
			By(
				intoM,
				field.SubfieldSubring.Read(MField).At(imageCarrier),
				imageSubfield,
				set_image.FunInImage,
				ring_homomorphism.RingHomCorestrict.At(baseRing, MRing, embedding, imageCarrier)))
		imageTarget := a.TermAs[module_record.RingOps[_ClosureHost]](
			"restrict_ring(field_ring(M), image(«closureEmbedding», K.carrier))")
		isomorphism := a.Have(
			"the embedding is injective and onto the restricted carrier",
			"ring_isomorphism(field_ring(K), "+
				"    restrict_ring(field_ring(M), image(«closureEmbedding», K.carrier)), "+
				"    «closureEmbedding»)",
			By(injective, imageHom, ring_homomorphism.RingIsomorphismDef.At(baseRing, imageTarget, embedding)))
		a.Take(M)
		a.Show(
			"M is an algebraic closure with K embedded as a subfield",
			By(closed, MField, algebraic, imageSubfield, isomorphism))
	}),
})}
