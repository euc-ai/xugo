package polish_space

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinal"
	"github.com/euc-ai/xugo/library/proofs/topology/complete_metric"
	"github.com/euc-ai/xugo/library/proofs/topology/metric_space"
	"github.com/euc-ai/xugo/library/proofs/topology/product_topology"
	"github.com/euc-ai/xugo/library/proofs/topology/topological_space"
	"github.com/euc-ai/xugo/library/registry"
)

// FiniteSupportDense — the finitely supported functions are dense in a
// discrete product. The discrete product is the product of the discrete
// topologies on the factors; each is a topology whose space is its factor
// and holds the prescribed value, so the density of the finitely supported
// points of a product applies, with the factors as carriers.
var FiniteSupportDense = finiteSupportDenseThm{family.Add(registry.ProofEntry{
	Name: "FiniteSupportDense",
	Key:  "prop_eb13a8a30de2fa42",
	Build: family.Theorem(Statement{
		Binders: "∀J:set(I). ∀z:(I → A). ∀X:(I → set(A)).",
		Hypotheses: []string{
			"∀i:I. i ∈ J ⇒ z(i) ∈ X(i)",
		},
		Conclusion: "closure(indexed_discrete_topology(J, z, X), " +
			"    {f:I → A | f ∈ indexed_functions(J, z, X) ∧ finite({i:I | ¬(f(i) = z(i))})}) = " +
			"indexed_functions(J, z, X)",
	},
		func(a *Argument, J *Expr[Set[I]], z *Arrow[I, A], X *Arrow2[I, A, Bool], admissible Fact) {
			discrete := a.TermAs[Fun2[I, Set[A], Bool]]("λi:I. {u:set(A) | u ⊆ X(i)}")
			factors := a.Have(
				"each active discrete factor is a topology whose space holds the prescribed value",
				"∀i:I. i ∈ J ⇒ is_topology({u:set(A) | u ⊆ X(i)}) ∧ z(i) ∈ ⋃{u:set(A) | u ⊆ X(i)}",
				Simp(Fwd(topological_space.DiscreteSpace)),
				By(admissible, topological_space.Discrete))
			carriers := a.Have(
				"the space of the discrete topology on a factor is the factor",
				"indexed_functions(J, z, λi:I. ⋃{u:set(A) | u ⊆ X(i)}) = indexed_functions(J, z, X)",
				Simp(Fwd(topological_space.DiscreteSpace)),
				Basic())
			dense := a.Have(
				"the finitely supported points are dense in the product of the discrete factors",
				"closure(indexed_product_topology(J, z, λi:I. {u:set(A) | u ⊆ X(i)}), "+
					"    {f:I → A | "+
					"        f ∈ indexed_functions(J, z, λi:I. ⋃{u:set(A) | u ⊆ X(i)}) ∧ "+
					"        finite({i:I | f(i) ≠ z(i)})}) = "+
					"indexed_functions(J, z, λi:I. ⋃{u:set(A) | u ⊆ X(i)})",
				By(factors, product_topology.ProductFiniteSupportDense.At(J, z, discrete)))
			a.Show(
				"that product is the discrete product, over the factors themselves",
				By(Normalized, dense, carriers, IndexedDiscreteTopologyDef.At(J, z, X)))
		}),
	Reading: "The prescribed values must be admissible, z(i) ∈ X(i) on the active indices; " +
		"otherwise no finitely supported function lies in the product while the product may be " +
		"nonempty. Support is read against z, so on inactive coordinates every function agrees with z.",
})}

// CountableProductPolish — a countable normalized product of Polish factors is Polish.
//
// Each active factor is a separable topology with a compatible complete metric.
// Choose such metrics and a sequence running through the active indices: the
// countable product distance along it is a metric (metric_space.CountableProductMetric),
// complete (complete_metric.CountableProductComplete), and its topology is the product
// of the factor topologies (metric_space.CountableProductMetricTopology). A countable
// product of separable factors is separable (product_topology.IndexedProductSeparable).
var CountableProductPolish = countableProductPolishThm{family.Add(registry.ProofEntry{
	Name: "CountableProductPolish",
	Key:  "prop_24a461a7514c80f1",
	Build: family.Theorem(Statement{
		Binders: "∀J:set(I). ∀z:(I → A). ∀T:(I → set(set(A))).",
		Hypotheses: []string{
			"countable(J)",
			"∀i:I. i ∈ J ⇒ polish_space(T(i))",
		},
		Conclusion: "polish_space(indexed_product_topology(J, z, T))",
		Abbrev: Abbrev{
			{Name: "ProductCarrier", Text: "indexed_functions(J, z, λi:I. ⋃T(i))"},
		},
	}, func(
		a *Argument,
		J *Expr[Set[I]],
		z *Arrow[I, A],
		T *Arrow[I, Set[Set[A]]],
		countableIndices, polishFactors Fact,
	) {
		factors := a.Have(
			"each active factor is a separable topology with a compatible complete metric",
			Statement{
				Binders: "∀i:I.",
				Hypotheses: []string{
					"i ∈ J",
				},
				Conclusion: "is_topology(T(i)) ∧ " +
					"separable_space(T(i)) ∧ " +
					"(∃d:(A → A → real). " +
					"    metric_space(⋃T(i), d) ∧ metric_complete(⋃T(i), d) ∧ metric_topology(⋃T(i), d) = T(i))",
			},
			Derive(func(b *Argument) {
				i := b.FixAs[I]()
				active := b.Assume()
				b.Show(
					"this is what a Polish factor is",
					By(polishFactors.At(i), active, PolishSpaceDef.At(b.TermAs[Set[Set[A]]]("T(i)"))))
			}))
		d, compatible := a.ObtainAs[Fun3[I, A, A, Real]](
			"choose compatible complete metrics on the active coordinates",
			"∃d:(I → A → A → real). ∀i:I. "+
				"    i ∈ J ⇒ "+
				"    metric_space(⋃T(i), d(i)) ∧ "+
				"    metric_complete(⋃T(i), d(i)) ∧ "+
				"    metric_topology(⋃T(i), d(i)) = T(i)",
			By(factors))
		h, cover := a.ObtainAs[Fun[Nat, I]](
			"a sequence runs through the countable active index set",
			"∃h:(num → I). J ⊆ image(h, 𝕌)",
			By(countableIndices, cardinal.CountableCover.At(J)))
		carriers := a.TermAs[Fun[I, Set[A]]]("λi:I. ⋃T(i)")
		metricTopologies := a.TermAs[Fun[I, Set[Set[A]]]]("λi:I. metric_topology(⋃T(i), d(i))")
		metric := a.Have(
			"the countable product distance along h is a compatible complete metric on the product",
			"∃e:((I → A) → (I → A) → real). "+
				"    metric_space(«ProductCarrier», e) ∧ "+
				"    metric_complete(«ProductCarrier», e) ∧ "+
				"    metric_topology(«ProductCarrier», e) = indexed_product_topology(J, z, T)",
			Witness(a.TermAs[Fun2[Fun[I, A], Fun[I, A], Real]]("countable_product_metric(J, d, h)")),
			SplitConjAll(
				Case(
					"it is a metric on the product of the factor spaces",
					By(compatible, cover, metric_space.CountableProductMetric.At(J, z, carriers, d, h))),
				Case(
					"it is complete, each factor metric being complete",
					By(compatible, cover, complete_metric.CountableProductComplete.At(J, z, carriers, d, h))),
				Case(
					"and its topology is the product of the factor metric topologies, which are the factor topologies",
					By(
						compatible,
						cover,
						metric_space.CountableProductMetricTopology.At(J, z, carriers, d, h),
						product_topology.IndexedProductTopologyCongruence.At(J, z, metricTopologies, T))),
			))
		separable := a.Have(
			"the product is separable, countably many factors being separable",
			"separable_space(indexed_product_topology(J, z, T))",
			By(countableIndices, factors, product_topology.IndexedProductSeparable.At(J, z, T)))
		a.Show(
			"the product is a separable topology with a compatible complete metric on its points",
			By(
				product_topology.IndexedProductTopology.At(J, z, T),
				separable,
				metric,
				product_topology.IndexedProductCarrier.At(J, z, T),
				PolishSpaceDef.Inst[Fun[I, A]]().At(
					a.TermAs[Set[Set[Fun[I, A]]]]("indexed_product_topology(J, z, T)"))))
	}),
	Reading: "Inactive coordinates are fixed at z. With J empty the product " +
		"is the one point z, and an empty active factor makes the product empty.",
})}
