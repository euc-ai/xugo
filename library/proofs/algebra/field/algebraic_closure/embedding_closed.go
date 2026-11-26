// embedding_closed.go — a field map into an algebraically closed field extends
// along algebraic adjunctions: one element, and so finitely many.

package algebraic_closure

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// AdjoinEmbeddingClosed — a field map from K into a closed field extends to K
// with one algebraic element adjoined: the map carries the minimal polynomial to
// a polynomial of the same positive degree, which has a root.
var AdjoinEmbeddingClosed = adjoinEmbeddingClosedThm{family.Add(registry.ProofEntry{
	Name: "AdjoinEmbeddingClosed",
	Key:  "prop_8d497a6a7913f20c",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀T:field_on(B). ∀K:set(A). ∀z:A. ∀f:(A → B).",
		Hypotheses: []string{
			"algebraically_closed_field(T)",
			"subfield(L, K)",
			"z ∈ L.carrier",
			"algebraic_over(L, K, z)",
			"ring_homomorphism(restrict_ring(field_ring(L), K), field_ring(T), f)",
		},
		Conclusion: "∃g:(A → B). " +
			"    ring_homomorphism(restrict_ring(field_ring(L), field_adjoin(L, K, {z})), " +
			"        field_ring(T), " +
			"        g) ∧ " +
			"    (∀x:A. x ∈ K ⇒ g(x) = f(x))",
		Abbrev: Abbrev{
			{Name: "transported", Text: "λi:num. f(minimal_polynomial(L, K, z, i))"},
		},
	}, func(
		a *Argument,
		L field.FieldFact[on.L],
		T field.FieldFact[on.T],
		K *Expr[Set[A]],
		z *Expr[A],
		f *Arrow[A, B],
		closed, subK, inL, algebraic, hom Fact,
	) {
		fieldL := a.TermAs[FieldOps[A]]("L")
		fieldT := a.TermAs[FieldOps[B]]("T")
		fieldK := a.TermAs[FieldOps[A]]("restrict_field(L, K)")
		minimal := a.TermAs[Fun[Nat, A]]("minimal_polynomial(L, K, z)")
		minimalData := a.Have(
			"the minimal polynomial of z lies over K with positive degree",
			"polynomial_over(K, minimal_polynomial(L, K, z)) ∧ "+
				"0 < polynomial_degree(minimal_polynomial(L, K, z))",
			By(
				L,
				subK,
				inL,
				algebraic,
				algebraic_element.MinimalPolynomialSpec.At(fieldL, K, z),
				algebraic_element.MinimalPolynomialPositive.At(fieldL, K, z)))
		restricted := a.Have(
			"K is a field and f a map of fields",
			"field_on(restrict_field(L, K)) ∧ "+
				"ring_homomorphism(field_ring(restrict_field(L, K)), field_ring(T), f)",
			By(
				Normalized,
				L,
				subK,
				hom,
				field.SubfieldFieldOn.At(fieldL, K),
				field.RestrictFieldRing.At(fieldL, K)))
		degree := a.Have(
			"a map of fields keeps the degree",
			"polynomial_degree(«transported») = polynomial_degree(minimal_polynomial(L, K, z))",
			By(
				T,
				restricted,
				minimalData,
				field.CarrierSubfield.At(fieldK),
				algebraic_element.FieldEmbeddingPolynomials.At(fieldK, fieldT, f, K, minimal)))
		over := a.Have(
			"the transported polynomial lies over T",
			"polynomial_over(T.carrier, «transported»)",
			By(
				minimalData,
				ring_homomorphism.MapZero.Read(hom),
				ring_homomorphism.MapIn.Read(hom),
				polynomial.PolynomialOverMap.At(
					f, a.TermAs[A]("L.zero"), a.TermAs[B]("T.zero"), K, a.TermAs[Set[B]]("T.carrier"), minimal)))
		root, rooted := a.ObtainAs[B](
			"a closed field holds a root b",
			"∃b:B. b ∈ T.carrier ∧ polynomial_eval(«transported», b) = T.zero",
			By(closed, over, degree, minimalData, AlgebraicallyClosedDef))
		a.Show(
			"send z to the root",
			By(
				L,
				T,
				subK,
				inL,
				algebraic,
				hom,
				rooted,
				algebraic_element.AdjoinEmbeddingAtRoot.At(fieldL, fieldT, K, f, z, root)))
	}),
})}

// FiniteAdjoinEmbedding — a field map from K into a closed field extends to K
// with finitely many algebraic elements adjoined, one adjunction at a time.
var FiniteAdjoinEmbedding = finiteAdjoinEmbeddingThm{family.Add(registry.ProofEntry{
	Name: "FiniteAdjoinEmbedding",
	Key:  "prop_af6f8e859ac8b9fb",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀T:field_on(B). ∀K S:set(A). ∀f:(A → B).",
		Hypotheses: []string{
			"algebraically_closed_field(T)",
			"subfield(L, K)",
			"finite(S)",
			"S ⊆ L.carrier",
			"∀x:A. x ∈ S ⇒ algebraic_over(L, K, x)",
			"ring_homomorphism(restrict_ring(field_ring(L), K), field_ring(T), f)",
		},
		Conclusion: "∃g:(A → B). " +
			"    ring_homomorphism(restrict_ring(field_ring(L), field_adjoin(L, K, S)), field_ring(T), g) ∧ " +
			"    (∀x:A. x ∈ K ⇒ g(x) = f(x))",
	}, func(
		a *Argument,
		L field.FieldFact[on.L],
		T field.FieldFact[on.T],
		K, S *Expr[Set[A]],
		f *Arrow[A, B],
		closed, subK, finiteS, sInL, algebraic, hom Fact,
	) {
		fieldL := a.TermAs[FieldOps[A]]("L")
		fieldT := a.TermAs[FieldOps[B]]("T")
		a.Show(
			"by induction, every finite set of elements of L algebraic over K admits an extension of f",
			ByInduction(
				finite_set.FiniteInduct,
				finiteS,
				Generalizing(sInL, algebraic),
				Case(
					"no element adjoined: K(∅) = K, where f itself serves",
					Derive(func(b *Argument) {
						b.Assume()
						nothing := b.Have(
							"adjoining nothing to K gives K",
							"field_adjoin(L, K, ∅) = K",
							By(
								subK,
								algebraic_element.AdjoinOfSubset.Read(L).At(K, b.TermAs[Set[A]]("∅")),
								set_order.EmptySubset))
						b.Take(f)
						b.Show(
							"f is its own extension",
							By(Normalized, nothing, hom))
					})),
				Case(
					"one more algebraic element x adjoined to the smaller set s",
					Derive(func(b *Argument) {
						x := b.FixAs[A]("x")
						s := b.FixAs[Set[A]]("s")
						inductive := b.Assume()
						enlarged := b.Assume()
						smallerAndPoint := b.Have(
							"the smaller set s and the new element lie in L and are algebraic over K",
							"s ⊆ L.carrier ∧ x ∈ L.carrier ∧ algebraic_over(L, K, x) ∧ (∀y:A. y ∈ s ⇒ algebraic_over(L, K, y))",
							BySets(enlarged))
						Ks := b.TermAs[Set[A]]("field_adjoin(L, K, s)")
						subfieldKs := b.Have(
							"K(s) is a subfield holding K, which lies in L",
							"K ⊆ L.carrier ∧ subfield(L, field_adjoin(L, K, s)) ∧ K ⊆ field_adjoin(L, K, s)",
							By(
								subK,
								smallerAndPoint,
								field.SubfieldSubset.At(fieldL, K),
								algebraic_element.AdjoinSubfield.Read(L).At(K, s)))
						g, lower := b.ObtainAs[Fun[A, B]](
							"f extends to K(s)",
							"∃g:(A → B). "+
								"    ring_homomorphism(restrict_ring(field_ring(L), field_adjoin(L, K, s)), field_ring(T), g) ∧ "+
								"    (∀y:A. y ∈ K ⇒ g(y) = f(y))",
							By(inductive, smallerAndPoint))
						overKs := b.Have(
							"the new element is algebraic over K(s)",
							"algebraic_over(L, field_adjoin(L, K, s), x)",
							By(L, subfieldKs, smallerAndPoint, algebraic_element.AlgebraicOverMono.At(fieldL, K, Ks, x)))
						successive := b.Have(
							"adjoining the enlarged set is adjoining x to K(s)",
							"field_adjoin(L, K, insert(x, s)) = field_adjoin(L, field_adjoin(L, K, s), {x})",
							By(L, subfieldKs, smallerAndPoint, algebraic_element.AdjoinInsert.At(fieldL, K, s, x)))
						h, upper := b.ObtainAs[Fun[A, B]](
							"and the extension g goes one adjunction further",
							"∃h:(A → B). "+
								"    ring_homomorphism( "+
								"        restrict_ring(field_ring(L), field_adjoin(L, field_adjoin(L, K, s), {x})), "+
								"        field_ring(T), "+
								"        h) ∧ "+
								"    (∀y:A. y ∈ field_adjoin(L, K, s) ⇒ h(y) = g(y))",
							By(
								L,
								T,
								closed,
								subfieldKs,
								smallerAndPoint,
								overKs,
								lower,
								AdjoinEmbeddingClosed.At(fieldL, fieldT, Ks, x, g)))
						onK := b.Have(
							"h agrees with g on K(s), so with f on K",
							"∀y:A. y ∈ K ⇒ h(y) = f(y)",
							BySets(subfieldKs, lower, upper))
						b.Take(h)
						b.Show(
							"h is the extension to the enlarged set",
							By(onK, successive, upper))
					}))))
	}),
})}
