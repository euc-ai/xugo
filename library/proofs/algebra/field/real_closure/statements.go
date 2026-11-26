package real_closure

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_closure"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_ordering"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/ordered_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/real_closed_field"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/ring_formula"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_division"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_evaluation"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/relations/order"
	_ "github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	_ "github.com/euc-ai/xugo/library/proofs/sets/functions"
	_ "github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	_ "github.com/euc-ai/xugo/library/proofs/topology/topological_space"
	"github.com/euc-ai/xugo/library/registry"
)

// OrderedSubfieldExtensionDef — An ordered subfield of an ambient field extending the given order on K.
var OrderedSubfieldExtensionDef = orderedSubfieldExtensionDefThm{family.Define(registry.DefEntry{
	Name:  "OrderedSubfieldExtensionDef",
	Const: "ordered_subfield_extension",
	Type:  "field_ops(A) → set(A) → (A → A → bool) → set(A) → (A → A → bool) → bool",
	Key:   "prop_975441ce93e2abf3",
	Equations: []string{
		"∀M:field_ops(A). ∀K:set(A). ∀lt:(A → A → bool). ∀L:set(A). ∀ls:(A → A → bool). " +
			"    ordered_subfield_extension(M, K, lt, L, ls) ⇔ " +
			"    K ⊆ L ∧ " +
			"    subfield(M, L) ∧ " +
			"    ordered_field_on(restrict_field(M, L), ls) ∧ " +
			"    (∀x y:A. x ∈ K ∧ y ∈ K ⇒ (lt(x, y) ⇔ ls(x, y)))",
	},
})}

// WeightedSquaresOrderExtension — An order on K extends to a subfield L ⊇ K when minus one is
// no sum of squares of L weighted by positive elements of K.
var WeightedSquaresOrderExtension = weightedSquaresOrderExtensionThm{family.Add(registry.ProofEntry{
	Name: "WeightedSquaresOrderExtension",
	Key:  "prop_5462a808bca22465",
	Deps: []registry.EntryLike{
		field_ordering.PreorderingExtension,
		field_ordering.PositiveConeOrder,
		ordered_field.OnePositive,
	},
	Build: family.Card(Statement{
		Binders: "∀M:field_ops(A). ∀K L:set(A). ∀lt:(A → A → bool).",
		Hypotheses: []string{
			"field_on(M)",
			"subfield(M, K)",
			"subfield(M, L)",
			"K ⊆ L",
			"ordered_field_on(restrict_field(M, K), lt)",
			"-M.one ∉ " +
				"{module_sum(M.add, M.zero, {j:num | j < k}, λj:num. p(j) * (y(j) * y(j))) | " +
				"    k:num, " +
				"    p:(num → A), " +
				"    y:(num → A) | " +
				"    ∀j:num. j < k ⇒ p(j) ∈ K ∧ lt(M.zero, p(j)) ∧ y(j) ∈ L}",
		},
		Conclusion: "∃ls:(A → A → bool). ordered_subfield_extension(M, K, lt, L, ls)",
	},
		"Real closed field transfer design, Artin-Schreier relative to K. The weighted sums form a "+
			"preordering T of L: a square is one term of weight one (OnePositive), and sums concatenate "+
			"and products multiply weights. PreorderingExtension extends T, which misses −1, to a "+
			"positive cone P of L, and PositiveConeOrder orders L by P. On K that order is lt: a positive "+
			"element of K lies in T ⊆ P, and P holds no nonzero element together with its negative."),
	Reading: "The weights are positive in K's order, not squares: that is what makes the " +
		"order on L restrict to lt. The converse holds too, every weighted sum being nonnegative " +
		"in an order extending lt, and is left out. With L = K the order is lt itself.",
})}

// SquareRootOrderExtension — A positive element acquires a square root in an order-extending subfield.
var SquareRootOrderExtension = squareRootOrderExtensionThm{family.Add(registry.ProofEntry{
	Name: "SquareRootOrderExtension",
	Key:  "prop_a988ea0d1db6b045",
	Deps: []registry.EntryLike{
		WeightedSquaresOrderExtension,
		ordered_field.SquareNonnegative,
	},
	Build: family.Card(Statement{
		Binders: "∀M:field_ops(A). ∀K:set(A). ∀lt:(A → A → bool). ∀a:A.",
		Hypotheses: []string{
			"algebraically_closed_field_on(M)",
			"subfield(M, K)",
			"ordered_field_on(restrict_field(M, K), lt)",
			"a ∈ K",
			"lt(M.zero, a)",
		},
		Conclusion: "∃L:set(A). ∃ls:(A → A → bool). ∃b:A. " +
			"    ordered_subfield_extension(M, K, lt, L, ls) ∧ b ∈ L ∧ b * b = a",
	},
		"Real closed field transfer design, real-closure construction. If a is a square in K, L = "+
			"K. Otherwise take a root b of X² − a in M and L = {u + v·b | u, v ∈ K}, a subfield since "+
			"b·b = a, the inverse of u + v·b being (u − v·b)/(u² − a·v²). A weighted sum Σ p·(u + "+
			"v·b)² is Σ p·(u² + a·v²) + b·2·Σ p·u·v: were it −1, b ∉ K would make 2·Σ p·u·v zero, and "+
			"the first part would be a sum of nonnegative elements of K (SquareNonnegative) equal to "+
			"−1. So WeightedSquaresOrderExtension extends the order to L."),
})}

// OddDegreeOrderExtension — An odd-degree polynomial acquires a root in an order-extending subfield.
var OddDegreeOrderExtension = oddDegreeOrderExtensionThm{family.Add(registry.ProofEntry{
	Name: "OddDegreeOrderExtension",
	Key:  "prop_febad0f5ebfed60d",
	Deps: []registry.EntryLike{
		WeightedSquaresOrderExtension,
		algebraic_element.AdjoinElementSubfield,
		algebraic_element.AdjoinPowerBasis,
		algebraic_element.MinimalPolynomialDivides,
		polynomial_division.IrreducibleFactorExists,
	},
	Build: family.Card(Statement{
		Binders: "∀M:field_ops(A). ∀K:set(A). ∀lt:(A → A → bool). ∀p:(num → A).",
		Hypotheses: []string{
			"algebraically_closed_field_on(M)",
			"subfield(M, K)",
			"ordered_field_on(restrict_field(M, K), lt)",
			"polynomial_over(K, p)",
			"∃j:num. polynomial_degree(p) = 2 * j + 1",
		},
		Conclusion: "∃L:set(A). ∃ls:(A → A → bool). ∃b:A. " +
			"    ordered_subfield_extension(M, K, lt, L, ls) ∧ b ∈ L ∧ polynomial_eval(p, b) = M.zero",
	},
		"Real closed field transfer design, odd-degree order extension (Serre). By strong induction "+
			"on odd d: for q irreducible over K of degree d and b a root of q in M, −1 is no weighted "+
			"sum Σ p·y² over K(b), the weights positive in K. Were −1 = Σ p·g(b)², each g of degree "+
			"below d (AdjoinPowerBasis; b's minimal polynomial is q up to a unit by "+
			"MinimalPolynomialDivides), then −1 = Σ p·g² + h·q in K[X]. If every g is constant, −h·q is "+
			"the positive constant 1 + Σ p·g² while q has degree d > 0: impossible. Otherwise the top "+
			"coefficients of Σ p·g² are positive, so its degree is even and at most 2d − 2, and h has "+
			"odd degree at most d − 2. An odd-degree irreducible factor of h (IrreducibleFactorExists, "+
			"by induction on the degree, degrees adding) has a root c in M, and −1 = Σ p·g(c)² over "+
			"K(c), against the induction. For p take an odd-degree irreducible factor q and its root b "+
			"in M: WeightedSquaresOrderExtension extends the order to K(b) (AdjoinElementSubfield)."),
})}

// RootsCharacterization — A field with an order is real closed exactly when
// it is Euclidean and every odd-degree polynomial over it has a root.
// Intermediate values supply the square roots and the odd-degree roots;
// conversely the two root conditions bound irreducibles by degree two, and a
// Euclidean field with that bound has intermediate values.
var RootsCharacterization = rootsCharacterizationThm{family.Add(registry.ProofEntry{
	Name: "RootsCharacterization",
	Key:  "prop_b7d795b750129a57",
	Build: family.Theorem("∀F:field_ops(A). ∀lt:(A → A → bool). "+
		"    real_closed_field(F, lt) ⇔ euclidean_field(F, lt) ∧ odd_degree_roots(F)",
		func(a *Argument, F *Expr[FieldOps[A]], lt *Arrow2[A, A, Bool]) {
			a.Iff()
			a.Forward(
				"Intermediate values give both root conditions",
				func(b *Argument, closed Fact) {
					b.Show(
						"A real closed field is Euclidean, and its odd-degree polynomials have roots",
						By(real_closed_field.EuclideanField.Read(closed), real_closed_field.OddDegreeRoot.Read(closed)))
				})
			a.Backward(
				"The root conditions bound irreducibles and give intermediate values",
				func(b *Argument, roots Fact) {
					b.Show(
						"A Euclidean field whose irreducibles have degree at most two is real closed",
						By(
							roots,
							At(RootsIrreducibleDegreeBound.Inst[A](), F, lt),
							QuadraticIrreduciblesRealClosed.At(F, lt)))
				})
		}),
})}

// MaximalOrderedSubfield — A maximal ordered subfield of an algebraically closed field is real closed.
var MaximalOrderedSubfield = maximalOrderedSubfieldThm{family.Add(registry.ProofEntry{
	Name: "MaximalOrderedSubfield",
	Key:  "prop_d682368c43cc4ba7",
	Deps: []registry.EntryLike{
		SquareRootOrderExtension,
		OddDegreeOrderExtension,
		RootsCharacterization,
	},
	Build: family.Card(Statement{
		Binders: "∀M:field_ops(A). ∀K:set(A). ∀lt:(A → A → bool).",
		Hypotheses: []string{
			"algebraically_closed_field_on(M)",
			"subfield(M, K)",
			"ordered_field_on(restrict_field(M, K), lt)",
			"∀L:set(A). ∀ls:(A → A → bool). ordered_subfield_extension(M, K, lt, L, ls) ⇒ L = K",
		},
		Conclusion: "real_closed_field(restrict_field(M, K), lt)",
	},
		"Real closed field transfer design, maximality. Maximality "+
			"forces the square roots and odd-degree roots supplied by the "+
			"two extension theorems back into K; apply RootsCharacterization."),
})}

// RealClosureExists — Every ordered field embeds order-preservingly in an algebraic real closure.
var RealClosureExists = realClosureExistsThm{family.Add(registry.ProofEntry{
	Name: "RealClosureExists",
	Key:  "prop_5412ad4a452d0192",
	Deps: []registry.EntryLike{
		algebraic_closure.AlgebraicClosureFieldOn,
		ordered_field.TransportOrderedField,
		order.Zorn,
		MaximalOrderedSubfield,
	},
	Reading: "The extension preserves the specified order on the base " +
		"carrier. The ambient algebraic closure itself is not ordered; its " +
		"fixed host and algebraicity are inherited by the chosen real closure.",
	Build: family.Card(Statement{
		Binders: "∀F:field_ops(A). ∀lt:(A → A → bool).",
		Hypotheses: []string{
			"ordered_field_on(F, lt)",
		},
		Conclusion: "∃G:field_ops(set(prod(num, num → A))). " +
			"∃ls:(set(prod(num, num → A)) → set(prod(num, num → A)) → bool). " +
			"∃i:(A → set(prod(num, num → A))). " +
			"    real_closed_field(G, ls) ∧ " +
			"    ordered_field_embedding(F, lt, G, ls, i) ∧ " +
			"    (∀x:set(prod(num, num → A)). x ∈ G.carrier ⇒ algebraic_over(G, image(i, F.carrier), x))",
	},
		"Real closed field transfer design, real closure with prescribed order. Embed F in its existing "+
			"algebraic closure, use Zorn on ordered subfields extending the transported order, and apply "+
			"MaximalOrderedSubfield. The ambient algebraicity supplies algebraicity of the result."),
})}

// NoProperOrderedAlgebraicExtension — A real closed field has no proper ordered algebraic extension.
var NoProperOrderedAlgebraicExtension = noProperOrderedAlgebraicExtensionThm{family.Add(registry.ProofEntry{
	Name: "NoProperOrderedAlgebraicExtension",
	Key:  "prop_73fab4ee68402869",
	Deps: []registry.EntryLike{RootsCharacterization},
	Build: family.Card(Statement{
		Binders: "∀F:field_ops(A). ∀lt:(A → A → bool). ∀G:field_ops(B). ∀ls:(B → B → bool). ∀i:(A → B).",
		Hypotheses: []string{
			"real_closed_field(F, lt)",
			"ordered_field_embedding(F, lt, G, ls, i)",
			"∀x:B. x ∈ G.carrier ⇒ algebraic_over(G, image(i, F.carrier), x)",
		},
		Conclusion: "image(i, F.carrier) = G.carrier",
	},
		"Real closed field transfer design, real-closed equivalences. The "+
			"algebraic characterization excludes a proper ordered algebraic extension."),
})}
