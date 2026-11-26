// free_algebra.go — the free commutative algebra hosted in a type: the
// polynomials are carried by an injection ι into a host type E, the
// algebra on a set of variables is the image of its polynomials, and
// one ring's operations, transported once along ι from the polynomials
// in every variable, serve the algebra on every set of variables. The
// constants, the variables, the evaluation into a ring, the map induced
// by a coefficient map and a map of the variables, the multiplication
// that flattens a polynomial of polynomials, and the coefficients along
// one set of variables over another are each read through ι from the
// polynomial model. Along an embedding the algebra is a commutative
// ring isomorphic to the polynomials, free on its variables: the
// evaluation is the one algebra map with given values, the induced maps
// are functorial, the multiplication and the variables make a monad,
// an algebra on two disjoint sets of variables is the algebra on one
// with coefficients in the algebra on the other, a monic linear
// factor divides with the substitution as remainder, the quotient by
// var y − c and one more relation is the quotient of the algebra
// without y by that relation with c put for y, and modulo a monic
// quadratic in y every member is p + q · var y for p, q without y.

package free_algebra

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/free_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/function_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_algebra"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_algebra_evaluation"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/quotient_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_ideal"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_transport"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The host and the algebra
// ---------------------------------------------------------------------------

// FreeAlgebraEmbeddingDef — `free_algebra_embedding(R, ι)`: ι is
// injective on the polynomials over R in every variable.
var FreeAlgebraEmbeddingDef = freeAlgebraEmbeddingDefThm{family.Define(registry.DefEntry{
	Name:  "FreeAlgebraEmbeddingDef",
	Key:   "prop_6189effa951312fe",
	Const: "free_algebra_embedding",
	Type:  "ring_ops(A) → (((D → num) → A) → E) → bool",
	Equations: []string{
		"∀R:ring_ops(A). ∀ι:(((D → num) → A) → E). " +
			"    free_algebra_embedding(R, ι) ⇔ injective_on(polynomial_algebra(R, 𝕌), ι)",
	},
	Reading: "The set is the polynomials over R, coefficients in R's carrier: the room the " +
		"host must have is bounded through the carrier, not the coefficient type, so a ring on " +
		"set(A) whose carrier is small, a quotient among them, has an embedding into a host that its " +
		"type does not fit. Every construction of the host interface reads ι on these polynomials " +
		"only — the operations, the evaluation and the coefficients pull back through the preimage " +
		"chosen among them, and the constants of R's carrier, the variables (R a ring) and the " +
		"coefficient functions of members of the algebra are polynomials over R — so injectivity " +
		"there is all a theorem over the algebra asks. The polynomials of every set of variables are " +
		"among them (PolynomialAlgebraSubset). Two rings with one zero and different carriers ask " +
		"injectivity on different sets; the embedding belongs to the ring, not to its zero.",
})}

// FreeAlgebraDef — `free_algebra(ι, R, S)`: the free commutative
// algebra on the variables of S over R in the host, the image under ι of
// the polynomials of S.
var FreeAlgebraDef = freeAlgebraDefThm{family.Define(registry.DefEntry{
	Name:  "FreeAlgebraDef",
	Key:   "prop_f8d50a577d8961ab",
	Const: "free_algebra",
	Type:  "(((D → num) → A) → E) → ring_ops(A) → set(D) → set(E)",
	Equations: []string{
		"∀ι:(((D → num) → A) → E). ∀R:ring_ops(A). ∀S:set(D). " +
			"    free_algebra(ι, R, S) = image(ι, polynomial_algebra(R, S))",
	},
})}

// FreeAlgebraRingDef — `free_algebra_ring(ι, R, S)`: the algebra on S as
// a ring record — the operations of the polynomials in every variable,
// transported along ι, and the algebra on S as the carrier. The
// operations do not read S: the algebras on all sets of variables have
// the six operations of the one on 𝕌, and along an embedding are its
// subrings.
var FreeAlgebraRingDef = freeAlgebraRingDefThm{family.Define(registry.DefEntry{
	Name:  "FreeAlgebraRingDef",
	Key:   "prop_b6d71aa8cb1a9946",
	Const: "free_algebra_ring",
	Type:  "(((D → num) → A) → E) → ring_ops(A) → set(D) → ring_ops(E)",
	Equations: []string{
		"∀ι:(((D → num) → A) → E). ∀R:ring_ops(A). ∀S:set(D). " +
			"    free_algebra_ring(ι, R, S) = " +
			"    restrict_ring(transport_ring(ι, polynomial_algebra_ring(R, 𝕌)), free_algebra(ι, R, S))",
	},
	Reading: "Every operation pulls its arguments back through the preimage " +
		"chosen among all polynomials, so it is one function of the host whatever S " +
		"is; the algebra on S is closed under it because the polynomials of S are a " +
		"subring of the polynomials in every variable and ι is injective on those.",
	Deps: []registry.EntryLike{FreeAlgebraDef},
})}

// FreeAlgebraConstDef — `free_algebra_const(ι, R, a)`: the constant a in
// the host, the image of the constant polynomial.
var FreeAlgebraConstDef = freeAlgebraConstDefThm{family.Define(registry.DefEntry{
	Name:  "FreeAlgebraConstDef",
	Key:   "prop_6b6d3bd5ffb6a7b",
	Const: "free_algebra_const",
	Type:  "(((D → num) → A) → E) → ring_ops(A) → A → E",
	Equations: []string{
		"∀ι:(((D → num) → A) → E). ∀R:ring_ops(A). ∀a:A. " +
			"    free_algebra_const(ι, R, a) = ι(polynomial_algebra_const(R, a))",
	},
})}

// FreeAlgebraVarDef — `free_algebra_var(ι, R, x)`: the variable x in the
// host, the image of the polynomial x.
var FreeAlgebraVarDef = freeAlgebraVarDefThm{family.Define(registry.DefEntry{
	Name:  "FreeAlgebraVarDef",
	Key:   "prop_aa004eec2a1ca91a",
	Const: "free_algebra_var",
	Type:  "(((D → num) → A) → E) → ring_ops(A) → D → E",
	Equations: []string{
		"∀ι:(((D → num) → A) → E). ∀R:ring_ops(A). ∀x:D. " +
			"    free_algebra_var(ι, R, x) = ι(polynomial_algebra_var(R, x))",
	},
})}

// FreeAlgebraModuleDef — `free_algebra_module(ι, R)`: the algebra on
// every variable as a module over R — the ring's sum, zero and negation,
// a scalar r acting by the product with the constant r, and the algebra
// on 𝕌 as the vectors.
var FreeAlgebraModuleDef = freeAlgebraModuleDefThm{family.Define(registry.DefEntry{
	Name:  "FreeAlgebraModuleDef",
	Key:   "prop_a25369e0a7e979a6",
	Const: "free_algebra_module",
	Type:  "(((D → num) → A) → E) → ring_ops(A) → module_ops(A, E)",
	Equations: []string{
		"∀ι:(((D → num) → A) → E). ∀R:ring_ops(A). " +
			"    free_algebra_module(ι, R) = " +
			"    restrict_module(scalar_restriction(free_algebra_const(ι, R), " +
			"            regular_module(free_algebra_ring(ι, R, 𝕌))), " +
			"        free_algebra(ι, R, 𝕌))",
	},
	Deps: []registry.EntryLike{FreeAlgebraRingDef, FreeAlgebraConstDef, FreeAlgebraDef},
})}

// ---------------------------------------------------------------------------
// Evaluation, induced maps and the multiplication
// ---------------------------------------------------------------------------

// FreeAlgebraEvalDef — `free_algebra_eval(ι, R, R', φ, θ, u)`: the
// member u of the host evaluated in the ring R', its polynomial — the
// preimage chosen among all polynomials — evaluated with coefficients
// carried by φ and each variable x given the value θ(x).
var FreeAlgebraEvalDef = freeAlgebraEvalDefThm{family.Define(registry.DefEntry{
	Name:  "FreeAlgebraEvalDef",
	Key:   "prop_38ff0a27c42f0dae",
	Const: "free_algebra_eval",
	Type:  "(((D → num) → A) → E) → ring_ops(A) → ring_ops(B) → (A → B) → (D → B) → E → B",
	Equations: []string{
		"∀ι:(((D → num) → A) → E). ∀R:ring_ops(A). ∀R':ring_ops(B). ∀φ:(A → B). ∀θ:(D → B). ∀u:E. " +
			"    free_algebra_eval(ι, R, R', φ, θ, u) = " +
			"    polynomial_algebra_eval(R, R', φ, θ, inverse_on(polynomial_algebra(R, 𝕌), ι, u))",
	},
	Reading: "The value reads R' through its operations only, never its " +
		"carrier. Off the algebra on 𝕌 the chosen preimage is unspecified, so " +
		"a statement reads the evaluation on a member of the algebra.",
})}

// FreeAlgebraMapDef — `free_algebra_map(ι, ι', R, R', φ, h, u)`: the map
// from the algebra over R in the host of ι to the algebra over R' in the
// host of ι' that carries each coefficient a to the constant φ(a) and
// each variable x to the variable h(x).
var FreeAlgebraMapDef = freeAlgebraMapDefThm{family.Define(registry.DefEntry{
	Name:  "FreeAlgebraMapDef",
	Key:   "prop_ced5426d0e10b943",
	Const: "free_algebra_map",
	Type: "(((D → num) → A) → E) → " +
		"(((I → num) → B) → C) → " +
		"ring_ops(A) → " +
		"ring_ops(B) → " +
		"(A → B) → " +
		"(D → I) → " +
		"E → " +
		"C",
	Equations: []string{
		"∀ι:(((D → num) → A) → E). " +
			"∀ι':(((I → num) → B) → C). " +
			"∀R:ring_ops(A). " +
			"∀R':ring_ops(B). " +
			"∀φ:(A → B). " +
			"∀h:(D → I). " +
			"∀u:E. " +
			"    free_algebra_map(ι, ι', R, R', φ, h, u) = " +
			"    free_algebra_eval(ι, " +
			"        R, " +
			"        free_algebra_ring(ι', R', 𝕌), " +
			"        (λa:A. free_algebra_const(ι', R', φ(a))), " +
			"        (λx:D. free_algebra_var(ι', R', h(x))), " +
			"        u)",
	},
	Deps: []registry.EntryLike{
		FreeAlgebraEvalDef,
		FreeAlgebraRingDef,
		FreeAlgebraConstDef,
		FreeAlgebraVarDef,
	},
})}

// FreeAlgebraMultDef — `free_algebra_mult(ι, R, u)`: the multiplication
// of the free algebra as a monad, for a host whose members serve as
// variables — u, a polynomial whose variables are members of the host,
// evaluated in the host's ring with each coefficient a constant and
// each variable itself.
var FreeAlgebraMultDef = freeAlgebraMultDefThm{family.Define(registry.DefEntry{
	Name:  "FreeAlgebraMultDef",
	Key:   "prop_c37c0066e3bb94bd",
	Const: "free_algebra_mult",
	Type:  "(((E → num) → A) → E) → ring_ops(A) → E → E",
	Equations: []string{
		"∀ι:(((E → num) → A) → E). ∀R:ring_ops(A). ∀u:E. " +
			"    free_algebra_mult(ι, R, u) = " +
			"    free_algebra_eval(ι, R, free_algebra_ring(ι, R, 𝕌), free_algebra_const(ι, R), (λv:E. v), u)",
	},
	Reading: "No set of variables is an argument: the evaluation reads the host " +
		"ring's operations, which do not depend on one. On the algebra over the algebra " +
		"on S the value lies in the algebra on S, each variable being a member of it.",
	Deps: []registry.EntryLike{FreeAlgebraEvalDef, FreeAlgebraRingDef, FreeAlgebraConstDef},
})}

// FreeAlgebraSubstituteDef — `free_algebra_substitute(ι, R, y, c, u)`:
// the member c of the host substituted for the variable y in u — u
// evaluated in the host's ring with each coefficient a constant, y given
// the value c and every other variable itself.
var FreeAlgebraSubstituteDef = freeAlgebraSubstituteDefThm{family.Define(registry.DefEntry{
	Name:  "FreeAlgebraSubstituteDef",
	Key:   "prop_c4657794565cebf0",
	Const: "free_algebra_substitute",
	Type:  "(((D → num) → A) → E) → ring_ops(A) → D → E → E → E",
	Equations: []string{
		"∀ι:(((D → num) → A) → E). ∀R:ring_ops(A). ∀y:D. ∀c u:E. " +
			"    free_algebra_substitute(ι, R, y, c, u) = " +
			"    free_algebra_eval(ι, " +
			"        R, " +
			"        free_algebra_ring(ι, R, 𝕌), " +
			"        free_algebra_const(ι, R), " +
			"        (λx:D. COND(x = y, c, free_algebra_var(ι, R, x))), " +
			"        u)",
	},
	Reading: "The substitution fixes every constant and every variable other than " +
		"y, so with c in the algebra on S it carries the algebra on S into itself; with " +
		"c in the algebra on S ∖ {y} its values on the algebra on S lie in the algebra " +
		"on S ∖ {y}. At c = free_algebra_var(ι, R, y) it is the identity on the algebra.",
	Deps: []registry.EntryLike{
		FreeAlgebraEvalDef,
		FreeAlgebraRingDef,
		FreeAlgebraConstDef,
		FreeAlgebraVarDef,
	},
})}

// ---------------------------------------------------------------------------
// Algebra maps
// ---------------------------------------------------------------------------

// FreeAlgebraHomomorphismDef — `free_algebra_homomorphism(ι, ι', R, R',
// φ, S, T, F)`: F is an algebra map over φ from the algebra on S over R
// in the host of ι to the algebra on T over R' in the host of ι' — φ
// carries R's carrier into the carrier of R', and F is a ring
// homomorphism of the two algebras that carries the constant a to the
// constant φ(a) for every a in R's carrier.
var FreeAlgebraHomomorphismDef = freeAlgebraHomomorphismDefThm{family.Define(registry.DefEntry{
	Name:  "FreeAlgebraHomomorphismDef",
	Key:   "prop_91f0f20c2791df88",
	Const: "free_algebra_homomorphism",
	Type: "(((D → num) → A) → E) → " +
		"(((I → num) → B) → C) → " +
		"ring_ops(A) → " +
		"ring_ops(B) → " +
		"(A → B) → " +
		"set(D) → " +
		"set(I) → " +
		"(E → C) → " +
		"bool",
	Equations: []string{
		"∀ι:(((D → num) → A) → E). " +
			"∀ι':(((I → num) → B) → C). " +
			"∀R:ring_ops(A). " +
			"∀R':ring_ops(B). " +
			"∀φ:(A → B). " +
			"∀S:set(D). " +
			"∀T:set(I). " +
			"∀F:(E → C). " +
			"    free_algebra_homomorphism(ι, ι', R, R', φ, S, T, F) ⇔ " +
			"    (∀a:A. a ∈ R.carrier ⇒ φ(a) ∈ R'.carrier) ∧ " +
			"    ring_homomorphism(free_algebra_ring(ι, R, S), free_algebra_ring(ι', R', T), F) ∧ " +
			"    (∀a:A. a ∈ R.carrier ⇒ F(free_algebra_const(ι, R, a)) = free_algebra_const(ι', R', φ(a)))",
	},
	Reading: "The first conjunct is load-bearing: an embedding ι' is injective on the polynomials " +
		"over R' only, so at a φ(a) off the carrier of R' the constant is no polynomial, and its image " +
		"may be any member of the algebra on T, a variable among them, which the last conjunct would " +
		"then read as the image of a constant. With it the constants φ(a) are polynomials over R', so F " +
		"fixes the constants up to φ in the sense the derivatives and the Jacobians read: the derivative " +
		"of the image of a constant vanishes. The ring homomorphism conjoins that both algebras are " +
		"rings under their records, so the predicate is never true of an algebra that is not one. F is " +
		"read on the algebra on S only and φ on R's carrier only. An R-algebra map between two algebras " +
		"in one host is the case ι' = ι, R' = R.carrier, φ = λa. a, where the first conjunct is void.",
	Deps: []registry.EntryLike{FreeAlgebraRingDef, FreeAlgebraConstDef},
})}

// ---------------------------------------------------------------------------
// Coefficients along a second set of variables
// ---------------------------------------------------------------------------

// FreeAlgebraCoefficientAtDef — `free_algebra_coefficient_at(ι, R, X, S,
// u, m)`: for u in the algebra on X ∪ S, the coefficient of the monomial
// m of S, a member of the algebra on X — the polynomial of X whose
// coefficient at a monomial n of X is u's coefficient at n + m. At an m
// that is not a monomial of S it is the zero of the host.
var FreeAlgebraCoefficientAtDef = freeAlgebraCoefficientAtDefThm{family.Define(registry.DefEntry{
	Name:  "FreeAlgebraCoefficientAtDef",
	Key:   "prop_a37c5ca63db29c68",
	Const: "free_algebra_coefficient_at",
	Type:  "(((D → num) → A) → E) → ring_ops(A) → set(D) → set(D) → E → (D → num) → E",
	Equations: []string{
		"∀ι:(((D → num) → A) → E). ∀R:ring_ops(A). ∀X S:set(D). ∀u:E. ∀m:(D → num). " +
			"    free_algebra_coefficient_at(ι, R, X, S, u, m) = " +
			"    ι(λn:(D → num). " +
			"            COND(m ∈ monomials(S) ∧ n ∈ monomials(X), " +
			"                inverse_on(polynomial_algebra(R, 𝕌), ι, u, λx:D. n(x) + m(x)), " +
			"                R.zero))",
	},
	Reading: "The split n + m of a monomial of X ∪ S into its parts on X and on S is " +
		"unique only when X and S are disjoint, so every expansion through these coefficients " +
		"asks X ∩ S = ∅. Over the empty S the one monomial is zero and the coefficient there " +
		"is u itself; over the zero ring every coefficient is the host's zero.",
})}

// ---------------------------------------------------------------------------
// The algebra as a ring and as a module
// ---------------------------------------------------------------------------

// FreeAlgebraEmbeddingDecode — along an embedding the preimage chosen
// among all polynomials reads a polynomial back from its image, and a
// member of the algebra on S back to a polynomial of S with that image:
// ι is one-to-one on the polynomials in every variable, among which lie
// the polynomials of S.
var FreeAlgebraEmbeddingDecode = freeAlgebraEmbeddingDecodeThm{family.Add(registry.ProofEntry{
	Name: "FreeAlgebraEmbeddingDecode",
	Key:  "prop_409fde87c42205fb",
	Reading: "This is the reading every construction of the host makes: the operations, the " +
		"evaluation and the coefficients pull a member of the algebra back to its polynomial. " +
		"The image half, ι of the chosen preimage being u, holds for every u in the image " +
		"without the embedding; the embedding is what makes the preimage the polynomial u came " +
		"from, and so a polynomial of S. Off the algebra on 𝕌 the chosen preimage is unspecified.",
	Build: family.Theorem(Statement{
		Binders: "∀ι:(((D → num) → A) → E). ∀R:ring_ops(A).",
		Hypotheses: []string{
			"free_algebra_embedding(R, ι)",
		},
		Conclusion: "(∀f:((D → num) → A). " +
			"    f ∈ polynomial_algebra(R, 𝕌) ⇒ inverse_on(polynomial_algebra(R, 𝕌), ι, ι(f)) = f) ∧ " +
			"(∀S:set(D). ∀u:E. " +
			"    u ∈ free_algebra(ι, R, S) ⇒ " +
			"    inverse_on(polynomial_algebra(R, 𝕌), ι, u) ∈ polynomial_algebra(R, S) ∧ " +
			"    ι(inverse_on(polynomial_algebra(R, 𝕌), ι, u)) = u)",
	},
		func(a *Argument, ι *Arrow[Fun[Fun[D, Nat], A], E], R *Expr[RingOps[A]], embedding Fact) {
			a.Do(SplitConj(
				Case(
					"ι is one-to-one on the polynomials in every "+
						"variable, so it reads each of them back from its image",
					By(embedding, FreeAlgebraEmbeddingDef, functions.InverseOnLeft)),
				Case(
					"a member u of the algebra on S is the image of a "+
						"polynomial g of S, and the chosen preimage of u is g",
					Derive(func(b *Argument) {
						S := b.FixAs[Set[D]]("S")
						b.FixAs[E]("u")
						member := b.Assume()
						_, source := b.UnpackAs[Fun[Fun[D, Nat], A]](
							b.Unfolded(b.Unfolded(member, FreeAlgebraDef), set_basic.ImageDef), "g")
						parts := b.Conjuncts(
							source,
							"g is a polynomial of S",
							"and u is its image")
						everyVariable := b.Have(
							"a polynomial of S is a polynomial in every variable",
							"g ∈ polynomial_algebra(R, 𝕌)",
							BySets(parts[0], polynomial_algebra.PolynomialAlgebraSubset.At(R, S, b.TermAs[Set[D]]("𝕌"))))
						readback := b.Have(
							"so ι reads g back from its image",
							"inverse_on(polynomial_algebra(R, 𝕌), ι, ι(g)) = g",
							By(embedding, everyVariable, FreeAlgebraEmbeddingDef, functions.InverseOnLeft))
						b.Show(
							"the chosen preimage of u = ι(g) is g: a polynomial of S, whose image is u",
							By(Normalized, parts[1], readback, parts[0]))
					})),
			))
		}),
})}

// FreeAlgebraRingIsomorphism — along an embedding, ι is a ring
// isomorphism from the polynomials of S onto the algebra on S: under the
// operations of the polynomials in every variable the polynomials of S
// are their own ring, a commutative ring, and ι is injective on the
// carrier of the polynomials in every variable, so ι is an isomorphism
// from that subring onto its image under the transported operations
// (ring_transport.TransportRingIsomorphism), which is the algebra on S.
var FreeAlgebraRingIsomorphism = freeAlgebraRingIsomorphismThm{family.Add(registry.ProofEntry{
	Name: "FreeAlgebraRingIsomorphism",
	Key:  "prop_2706b51bf81297a9",
	Reading: "The embedding is asked to be injective on the polynomials in every variable " +
		"only: the transport chooses its preimages there, and the polynomials of S lie among " +
		"them. comm_ring_on(R) makes the polynomials of S a ring for ι to be an isomorphism from.",
	Build: family.Theorem(Statement{
		Binders: "∀ι:(((D → num) → A) → E). ∀R:ring_ops(A). ∀S:set(D).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"free_algebra_embedding(R, ι)",
		},
		Conclusion: "ring_isomorphism(polynomial_algebra_ring(R, S), free_algebra_ring(ι, R, S), ι)",
	},
		func(
			a *Argument,
			ι *Arrow[Fun[Fun[D, Nat], A], E],
			R *Expr[RingOps[A]],
			S *Expr[Set[D]],
			ring, embedding Fact,
		) {
			polynomials := a.TermAs[RingOps[Fun[Fun[D, Nat], A]]]("polynomial_algebra_ring(R, 𝕌)")
			ofS := a.TermAs[Set[Fun[Fun[D, Nat], A]]]("polynomial_algebra(R, S)")
			injective := a.Have(
				"ι is injective on the carrier of the polynomials in every variable, as the embedding asks",
				"injective_on(polynomial_algebra_ring(R, 𝕌).carrier, ι)",
				By(embedding, FreeAlgebraEmbeddingDef, polynomial_algebra.PolynomialAlgebraRingDef))
			inCarrier := a.Have(
				"the polynomials of S are polynomials in every variable",
				"polynomial_algebra(R, S) ⊆ polynomial_algebra_ring(R, 𝕌).carrier",
				By(
					polynomial_algebra.PolynomialAlgebraSubset,
					set_order.SubsetUniv,
					polynomial_algebra.PolynomialAlgebraRingDef))
			subring := a.Have(
				"restricted to the polynomials of S, the polynomials in every "+
					"variable are the ring of the polynomials of S, a commutative ring",
				"comm_ring_on(restrict_ring(polynomial_algebra_ring(R, 𝕌), polynomial_algebra(R, S)))",
				By(
					ring,
					polynomial_algebra.PolynomialAlgebraRingRestrictVariables,
					polynomial_algebra.PolynomialAlgebraCommRingOn.At(R, S)))
			a.Show(
				"ι is an isomorphism from that subring, the ring of the polynomials of "+
					"S, onto its image under the transported operations, the algebra on S",
				By(
					injective,
					inCarrier,
					subring,
					ring_transport.TransportRingIsomorphism.At(ι, polynomials, ofS),
					polynomial_algebra.PolynomialAlgebraRingRestrictVariables,
					FreeAlgebraRingDef,
					FreeAlgebraDef))
		}),
})}

// FreeAlgebraCommRingOn — along an embedding, the algebra on S is a
// commutative ring under the transported operations: it is the target of
// the ring isomorphism ι from the polynomials of S
// (FreeAlgebraRingIsomorphism), and a ring homomorphism asks its target
// to be a commutative ring (ring_homomorphism.Target).
var FreeAlgebraCommRingOn = freeAlgebraCommRingOnThm{family.Add(registry.ProofEntry{
	Name: "FreeAlgebraCommRingOn",
	Key:  "prop_d79a199038d3fb86",
	Reading: "The embedding is injective on every polynomial in every variable, so " +
		"the preimage the operations choose among all polynomials is the polynomial " +
		"itself; without it two polynomials with one image would make the operations " +
		"choose. Over the zero ring the algebra is the one point ι of the zero polynomial.",
	Build: family.Theorem(Statement{
		Binders: "∀ι:(((D → num) → A) → E). ∀R:ring_ops(A). ∀S:set(D).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"free_algebra_embedding(R, ι)",
		},
		Conclusion: "comm_ring_on(free_algebra_ring(ι, R, S))",
	},
		func(
			a *Argument,
			ι *Arrow[Fun[Fun[D, Nat], A], E],
			R *Expr[RingOps[A]],
			S *Expr[Set[D]],
			ring, embedding Fact,
		) {
			homomorphism := a.Have(
				"ι is a ring isomorphism from the polynomials of S "+
					"onto the algebra on S, so a ring homomorphism into it",
				"ring_homomorphism(polynomial_algebra_ring(R, S), free_algebra_ring(ι, R, S), ι)",
				By(ring, embedding, FreeAlgebraRingIsomorphism.At(ι, R, S), ring_homomorphism.RingIsomorphismDef))
			a.Show(
				"the algebra on S is the target of that homomorphism, a commutative ring",
				By(ring_homomorphism.Target.Read(homomorphism)))
		}),
})}

// FreeAlgebraModuleOn — along an embedding, the algebra on every
// variable is a module over R, scalars acting through the constants,
// and the algebra on each S is a submodule of it.
var FreeAlgebraModuleOn = freeAlgebraModuleOnThm{family.Add(registry.ProofEntry{
	Name: "FreeAlgebraModuleOn",
	Key:  "prop_93e86cc8ad88f577",
	Reading: "Scaling is the product with a constant, and R.one • u = u because " +
		"the constant of R.one is literally the one polynomial, the ring's one.",
	Deps: []registry.EntryLike{
		FreeAlgebraModuleDef,
		FreeAlgebraCommRingOn,
		FreeAlgebraConstHom,
		FreeAlgebraSubset,
		module.ModuleOn,
		submodule.SubmoduleDef,
		ring_homomorphism.MapAdd,
		ring_homomorphism.MapMul,
		ring_homomorphism.MapOne,
		ring_homomorphism.MapIn,
	},
	Build: family.Card(Statement{
		Binders: "∀ι:(((D → num) → A) → E). ∀R:ring_ops(A).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"free_algebra_embedding(R, ι)",
		},
		Conclusion: "module_on(R, free_algebra_module(ι, R)) ∧ " +
			"(∀S:set(D). submodule(R, free_algebra_module(ι, R), free_algebra(ι, R, S)))",
	},
		"the algebra on 𝕌 is a commutative ring (FreeAlgebraCommRingOn), so an abelian group under "+
			"its sum; scaling by r is the product with the constant of r, a member of the algebra on "+
			"every S (FreeAlgebraConstHom), so each module law is a ring law of the product together "+
			"with the constants' keeping the sum, the product and the one; the algebra on S is a "+
			"subring, so closed under the sum, the negation and the product with a constant"),
})}

// FreeAlgebraOpsIndependentOfVariables — the algebras on two sets of
// variables have the same six operations.
var FreeAlgebraOpsIndependentOfVariables = freeAlgebraOpsIndependentOfVariablesThm{family.Add(registry.ProofEntry{
	Name: "FreeAlgebraOpsIndependentOfVariables",
	Key:  "prop_920e0754863da61a",
	Reading: "No hypothesis: the operations are transported from the polynomials " +
		"in every variable whatever the set, so the algebras on two sets of " +
		"variables differ in their carriers only. That each is a subring of the one " +
		"on 𝕌 asks more — closure, which the embedding gives (FreeAlgebraCommRingOn).",
	Build: family.Theorem("∀ι:(((D → num) → A) → E). ∀R:ring_ops(A). ∀S T:set(D). "+
		"    free_algebra_ring(ι, R, S).add = free_algebra_ring(ι, R, T).add ∧ "+
		"    free_algebra_ring(ι, R, S).zero = free_algebra_ring(ι, R, T).zero ∧ "+
		"    free_algebra_ring(ι, R, S).neg = free_algebra_ring(ι, R, T).neg ∧ "+
		"    free_algebra_ring(ι, R, S).mul = free_algebra_ring(ι, R, T).mul ∧ "+
		"    free_algebra_ring(ι, R, S).one = free_algebra_ring(ι, R, T).one ∧ "+
		"    free_algebra_ring(ι, R, S).sub = free_algebra_ring(ι, R, T).sub",
		func(a *Argument, ι *Arrow[Fun[Fun[D, Nat], A], E], R *Expr[RingOps[A]], S, T *Expr[Set[D]]) {
			a.Show(
				"both rings restrict the one ring transported from the polynomials "+
					"in every variable, and a restriction keeps the six operations",
				By(FreeAlgebraRingDef, module_record.RestrictRingDef))
		}),
})}

// FreeAlgebraSubset — more variables, a larger algebra: the polynomials
// of S are polynomials of T, and the image of a subset is a subset of the
// image.
var FreeAlgebraSubset = freeAlgebraSubsetThm{family.Add(registry.ProofEntry{
	Name: "FreeAlgebraSubset",
	Key:  "prop_6efa3b19d2fd66c",
	Build: family.Theorem(Statement{
		Binders: "∀ι:(((D → num) → A) → E). ∀R:ring_ops(A). ∀S T:set(D).",
		Hypotheses: []string{
			"S ⊆ T",
		},
		Conclusion: "free_algebra(ι, R, S) ⊆ free_algebra(ι, R, T)",
	},
		func(
			a *Argument,
			ι *Arrow[Fun[Fun[D, Nat], A], E],
			R *Expr[RingOps[A]],
			S, T *Expr[Set[D]],
			sub Fact,
		) {
			a.Show(
				"the polynomials of S lie among those of T, so their image lies in the image of those",
				Simp(Fwd(FreeAlgebraDef)),
				By(sub, set_image.ImageSubset, polynomial_algebra.PolynomialAlgebraSubset))
		}),
})}

// FreeAlgebraNoVariables — the algebra on no variables is the image of
// the carrier under the constants.
var FreeAlgebraNoVariables = freeAlgebraNoVariablesThm{family.Add(registry.ProofEntry{
	Name: "FreeAlgebraNoVariables",
	Key:  "prop_efed1a47fe9555f0",
	Reading: "The ring hypothesis is load-bearing: a polynomial takes the " +
		"value R.zero off its support, so with R.zero outside the carrier " +
		"there would be no polynomial at all, while every constant names one.",
	Deps: []registry.EntryLike{
		FreeAlgebraDef,
		FreeAlgebraConstDef,
		polynomial_algebra.PolynomialAlgebraDef,
		polynomial_algebra.PolynomialAlgebraConstDef,
		polynomial_algebra.MonomialsDef,
		function_module.FiniteSuppDef,
		free_module.DeltaAtDef,
		comm_ring.ZeroIn,
	},
	Build: family.Card(Statement{
		Binders: "∀ι:(((D → num) → A) → E). ∀R:ring_ops(A).",
		Hypotheses: []string{
			"comm_ring_on(R)",
		},
		Conclusion: "free_algebra(ι, R, ∅) = image(free_algebra_const(ι, R), R.carrier)",
	},
		"the empty set has one monomial, the monomial of the constants, so a polynomial of ∅ is zero "+
			"off it: it is the constant polynomial of its value there, a member of the carrier; conversely "+
			"a constant of the carrier is such a polynomial (its values a and R.zero lie in the carrier)"),
})}

// ---------------------------------------------------------------------------
// Constants and variables
// ---------------------------------------------------------------------------

// FreeAlgebraConstHom — along an embedding, the constants are a ring
// homomorphism from R into the algebra on every S: the constant of a is
// ι of the constant polynomial of a, so the constants are the constant
// polynomials, a ring homomorphism into the polynomials of S, followed by
// ι, a ring isomorphism of these onto the algebra on S.
var FreeAlgebraConstHom = freeAlgebraConstHomThm{family.Add(registry.ProofEntry{
	Name: "FreeAlgebraConstHom",
	Key:  "prop_af29c89224a0f17e",
	Build: family.Theorem(Statement{
		Binders: "∀ι:(((D → num) → A) → E). ∀R:ring_ops(A). ∀S:set(D).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"free_algebra_embedding(R, ι)",
		},
		Conclusion: "ring_homomorphism(R, free_algebra_ring(ι, R, S), free_algebra_const(ι, R))",
	},
		func(
			a *Argument,
			ι *Arrow[Fun[Fun[D, Nat], A], E],
			R *Expr[RingOps[A]],
			S *Expr[Set[D]],
			ring, embedding Fact,
		) {
			constants := a.Have(
				"the constant polynomials are a ring homomorphism from R into the polynomials of S",
				"ring_homomorphism(R, polynomial_algebra_ring(R, S), polynomial_algebra_const(R))",
				By(ring, polynomial_algebra.PolynomialAlgebraConstHom.At(R, S)))
			hosting := a.Have(
				"ι is a ring isomorphism of the polynomials of S onto the algebra on S, so a ring homomorphism",
				"ring_homomorphism(polynomial_algebra_ring(R, S), free_algebra_ring(ι, R, S), ι)",
				By(ring, embedding, FreeAlgebraRingIsomorphism.At(ι, R, S), ring_homomorphism.RingIsomorphismDef))
			a.Show(
				"the constant of a is ι of the constant polynomial "+
					"of a, so the constants are the composite of the two",
				By(
					constants,
					hosting,
					ring_homomorphism.RingHomCompose.At(
						R,
						a.TermAs[RingOps[Fun[Fun[D, Nat], A]]]("polynomial_algebra_ring(R, S)"),
						a.TermAs[RingOps[E]]("free_algebra_ring(ι, R, S)"),
						a.TermAs[Fun[A, Fun[Fun[D, Nat], A]]]("polynomial_algebra_const(R)"),
						ι),
					FreeAlgebraConstDef))
		}),
})}

// FreeAlgebraVarIn — the variable x of S lies in the algebra on S.
var FreeAlgebraVarIn = freeAlgebraVarInThm{family.Add(registry.ProofEntry{
	Name: "FreeAlgebraVarIn",
	Key:  "prop_e931738ba83749c7",
	Reading: "No embedding is asked: membership is ι applied " +
		"to a polynomial of S, by the definition of the image.",
	Build: family.Theorem(Statement{
		Binders: "∀ι:(((D → num) → A) → E). ∀R:ring_ops(A). ∀S:set(D). ∀x:D.",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"x ∈ S",
		},
		Conclusion: "free_algebra_var(ι, R, x) ∈ free_algebra(ι, R, S)",
	},
		func(
			a *Argument,
			ι *Arrow[Fun[Fun[D, Nat], A], E],
			R *Expr[RingOps[A]],
			S *Expr[Set[D]],
			x *Expr[D],
			ring, xIn Fact,
		) {
			a.Show(
				"the variable is ι of the polynomial x, a polynomial of S, so a value of ι on the polynomials of S",
				Simp(Fwd(FreeAlgebraVarDef), Fwd(FreeAlgebraDef)),
				By(ring, xIn, polynomial_algebra.PolynomialAlgebraVarIn.At(R, S, x), set_image.FunInImage))
		}),
})}

// ---------------------------------------------------------------------------
// Evaluation
// ---------------------------------------------------------------------------

// FreeAlgebraEvalHom — evaluation at values in R' of the variables of
// S is a ring homomorphism from the algebra on S into R': on the algebra
// on S it is the inverse of the isomorphism ι followed by the evaluation
// of the polynomials of S, a composite of two ring homomorphisms, since
// the preimage the evaluation chooses among all polynomials is the one
// chosen among the polynomials of S.
var FreeAlgebraEvalHom = freeAlgebraEvalHomThm{family.Add(registry.ProofEntry{
	Name: "FreeAlgebraEvalHom",
	Key:  "prop_4b0fbdd52e9a293",
	Reading: "θ is read on S only. The homomorphism is from the record " +
		"free_algebra_ring(ι, R, S): the evaluation of a member of the host outside " +
		"the algebra on 𝕌 reads an unspecified preimage, so nothing is said of it there.",
	Build: family.Theorem(Statement{
		Binders: "∀ι:(((D → num) → A) → E). " +
			"∀R:ring_ops(A). " +
			"∀R':ring_ops(B). " +
			"∀φ:(A → B). " +
			"∀S:set(D). " +
			"∀θ:(D → B).",
		Hypotheses: []string{
			"free_algebra_embedding(R, ι)",
			"ring_homomorphism(R, R', φ)",
			"∀x:D. x ∈ S ⇒ θ(x) ∈ R'.carrier",
		},
		Conclusion: "ring_homomorphism(free_algebra_ring(ι, R, S), R', free_algebra_eval(ι, R, R', φ, θ))",
	},
		func(
			a *Argument,
			ι *Arrow[Fun[Fun[D, Nat], A], E],
			R *Expr[RingOps[A]],
			RPrime *Expr[RingOps[B]],
			φ *Arrow[A, B],
			S *Expr[Set[D]],
			θ *Arrow[D, B],
			embedding, hom, values Fact,
		) {
			polynomials := a.TermAs[RingOps[Fun[Fun[D, Nat], A]]]("polynomial_algebra_ring(R, S)")
			algebra := a.TermAs[RingOps[E]]("free_algebra_ring(ι, R, S)")
			ring := ring_homomorphism.Source.Read(hom)
			isomorphism := a.Have(
				"ι is a ring isomorphism from the polynomials of S onto the algebra on S",
				"ring_isomorphism(polynomial_algebra_ring(R, S), free_algebra_ring(ι, R, S), ι)",
				By(ring, embedding, FreeAlgebraRingIsomorphism))
			inverse := a.Have(
				"so its inverse, taken among the polynomials of S, is "+
					"a ring homomorphism from the algebra on S back to them",
				"ring_homomorphism(free_algebra_ring(ι, R, S), "+
					"    polynomial_algebra_ring(R, S), "+
					"    inverse_on(polynomial_algebra(R, S), ι))",
				By(
					isomorphism,
					ring_homomorphism.IsomorphismInverse.At(polynomials, algebra, ι),
					ring_homomorphism.RingIsomorphismDef))
			composite := a.Have(
				"followed by the evaluation of the polynomials of S, a ring homomorphism "+
					"into R', it is a ring homomorphism from the algebra on S into R'",
				"ring_homomorphism(free_algebra_ring(ι, R, S), "+
					"    R', "+
					"    λu:E. polynomial_algebra_eval(R, R', φ, θ, inverse_on(polynomial_algebra(R, S), ι, u)))",
				By(
					inverse,
					hom,
					values,
					polynomial_algebra_evaluation.PolynomialAlgebraEvalHom.At(R, RPrime, φ, θ, S),
					ring_homomorphism.RingHomCompose.At(
						algebra,
						polynomials,
						RPrime,
						a.TermAs[Fun[E, Fun[Fun[D, Nat], A]]]("inverse_on(polynomial_algebra(R, S), ι)"),
						a.TermAs[Fun[Fun[Fun[D, Nat], A], B]]("polynomial_algebra_eval(R, R', φ, θ)"))))
			agreement := a.Have(
				"on the algebra on S the evaluation is that composite",
				Statement{
					Binders: "∀u:E.",
					Hypotheses: []string{
						"u ∈ free_algebra(ι, R, S)",
					},
					Conclusion: "free_algebra_eval(ι, R, R', φ, θ, u) = " +
						"polynomial_algebra_eval(R, R', φ, θ, inverse_on(polynomial_algebra(R, S), ι, u))",
				},
				Derive(func(b *Argument) {
					b.FixAs[E]("u")
					uIn := b.Assume()
					decoded := b.Have(
						"u is ι of the polynomial its preimage among all polynomials "+
							"chooses, and that polynomial is a polynomial of S",
						"inverse_on(polynomial_algebra(R, 𝕌), ι, u) ∈ polynomial_algebra(R, S) ∧ "+
							"ι(inverse_on(polynomial_algebra(R, 𝕌), ι, u)) = u",
						By(embedding, uIn, FreeAlgebraEmbeddingDecode.At(ι, R)))
					preimage := b.Have(
						"ι is injective on the polynomials of S, so the preimage chosen among them is that polynomial too",
						"inverse_on(polynomial_algebra(R, S), ι, u) = inverse_on(polynomial_algebra(R, 𝕌), ι, u)",
						By(
							decoded,
							isomorphism,
							ring_homomorphism.RingIsomorphismDef.At(polynomials, algebra, ι),
							functions.InverseOnLeft.At(
								b.TermAs[Set[Fun[Fun[D, Nat], A]]]("polynomial_algebra(R, S)"),
								ι,
								b.TermAs[Fun[Fun[D, Nat], A]]("inverse_on(polynomial_algebra(R, 𝕌), ι, u)"))))
					b.Show(
						"so both evaluate the one polynomial",
						Simp(Fwd(FreeAlgebraEvalDef), Fwd(preimage)),
						Refl())
				}))
			a.Show(
				"a map agreeing on the algebra on S with a ring homomorphism from it is one",
				By(composite, agreement, ring_homomorphism.RingHomCongruence))
		}),
})}

// FreeAlgebraEvalConst — a constant evaluates to its image under the
// coefficient map: the constant polynomial of a is a polynomial in every
// variable, so the embedding reads its image back to it, and the
// polynomial evaluation carries it to φ(a).
var FreeAlgebraEvalConst = freeAlgebraEvalConstThm{family.Add(registry.ProofEntry{
	Name: "FreeAlgebraEvalConst",
	Key:  "prop_3053e44e0b793e51",
	Build: family.Theorem(Statement{
		Binders: "∀ι:(((D → num) → A) → E). " +
			"∀R:ring_ops(A). " +
			"∀R':ring_ops(B). " +
			"∀φ:(A → B). " +
			"∀θ:(D → B). " +
			"∀a:A.",
		Hypotheses: []string{
			"free_algebra_embedding(R, ι)",
			"ring_homomorphism(R, R', φ)",
			"a ∈ R.carrier",
		},
		Conclusion: "free_algebra_eval(ι, R, R', φ, θ, free_algebra_const(ι, R, a)) = φ(a)",
	},
		func(
			arg *Argument,
			ι *Arrow[Fun[Fun[D, Nat], A], E],
			R *Expr[RingOps[A]],
			RPrime *Expr[RingOps[B]],
			φ *Arrow[A, B],
			θ *Arrow[D, B],
			a *Expr[A],
			embedding, hom, aIn Fact,
		) {
			polynomials := arg.TermAs[RingOps[Fun[Fun[D, Nat], A]]]("polynomial_algebra_ring(R, 𝕌)")
			polynomial := arg.Have(
				"the constant polynomial of a is a polynomial in every variable: R, "+
					"φ's source, is a commutative ring whose constants are polynomials",
				"polynomial_algebra_const⟨D:D⟩(R, a) ∈ polynomial_algebra(R, 𝕌)",
				By(
					ring_homomorphism.Source.Read(hom),
					aIn,
					Where(ring_homomorphism.MapIn, "S", polynomials),
					polynomial_algebra.PolynomialAlgebraConstHom))
			readback := arg.Have(
				"ι is injective on the polynomials in every variable, "+
					"so it reads the image of that polynomial back to it",
				"inverse_on(polynomial_algebra(R, 𝕌), ι, ι(polynomial_algebra_const(R, a))) = "+
					"polynomial_algebra_const(R, a)",
				By(embedding, polynomial, FreeAlgebraEmbeddingDecode.At(ι, R)))
			arg.Show(
				"so the constant a evaluates as its polynomial does, to φ(a)",
				Simp(Fwd(FreeAlgebraEvalDef), Fwd(FreeAlgebraConstDef)),
				By(readback, aIn, hom, polynomial_algebra_evaluation.PolynomialAlgebraEvalConst))
		}),
})}

// FreeAlgebraEvalVar — the variable x evaluates to its value: the
// polynomial of x is a polynomial in every variable, so the embedding
// reads its image back to it, and the polynomial evaluation carries it to
// θ(x).
var FreeAlgebraEvalVar = freeAlgebraEvalVarThm{family.Add(registry.ProofEntry{
	Name: "FreeAlgebraEvalVar",
	Key:  "prop_18d80439870faa0",
	Reading: "x ∈ S is not asked, since every variable lies in the " +
		"algebra on 𝕌. θ(x) ∈ R'.carrier is load-bearing: the evaluation " +
		"multiplies θ(x) by R'.one, which returns θ(x) only on the carrier.",
	Build: family.Theorem(Statement{
		Binders: "∀ι:(((D → num) → A) → E). " +
			"∀R:ring_ops(A). " +
			"∀R':ring_ops(B). " +
			"∀φ:(A → B). " +
			"∀θ:(D → B). " +
			"∀x:D.",
		Hypotheses: []string{
			"free_algebra_embedding(R, ι)",
			"ring_homomorphism(R, R', φ)",
			"θ(x) ∈ R'.carrier",
		},
		Conclusion: "free_algebra_eval(ι, R, R', φ, θ, free_algebra_var(ι, R, x)) = θ(x)",
	},
		func(
			a *Argument,
			ι *Arrow[Fun[Fun[D, Nat], A], E],
			R *Expr[RingOps[A]],
			RPrime *Expr[RingOps[B]],
			φ *Arrow[A, B],
			θ *Arrow[D, B],
			x *Expr[D],
			embedding, hom, valueIn Fact,
		) {
			polynomial := a.Have(
				"the polynomial of x is a polynomial in every variable: R is a "+
					"commutative ring, as φ's source, and x is one of the variables",
				"polynomial_algebra_var(R, x) ∈ polynomial_algebra(R, 𝕌)",
				By(ring_homomorphism.Source.Read(hom), set_basic.InUniv, polynomial_algebra.PolynomialAlgebraVarIn))
			readback := a.Have(
				"ι is injective on the polynomials in every variable, "+
					"so it reads the image of that polynomial back to it",
				"inverse_on(polynomial_algebra(R, 𝕌), ι, ι(polynomial_algebra_var(R, x))) = "+
					"polynomial_algebra_var(R, x)",
				By(embedding, polynomial, FreeAlgebraEmbeddingDecode.At(ι, R)))
			a.Show(
				"so the variable x evaluates as its polynomial does, to θ(x)",
				Simp(Fwd(FreeAlgebraEvalDef), Fwd(FreeAlgebraVarDef)),
				By(readback, valueIn, hom, polynomial_algebra_evaluation.PolynomialAlgebraEvalVar))
		}),
})}

// FreeAlgebraEvalUnique — two ring homomorphisms out of the algebra on
// S that agree on the constants and on the variables of S agree on the
// algebra on S: after ι they are ring homomorphisms out of the
// polynomials of S that agree on the constant polynomials and on the
// polynomials of the variables, so they agree on every polynomial of S,
// and every member of the algebra on S is ι of one.
var FreeAlgebraEvalUnique = freeAlgebraEvalUniqueThm{family.Add(registry.ProofEntry{
	Name: "FreeAlgebraEvalUnique",
	Key:  "prop_bd1a66cc7509c10e",
	Reading: "Both maps are homomorphisms from the record free_algebra_ring(ι, R, S), so they " +
		"are read on the algebra on S only. Agreement on the constants is asked as F = G there, " +
		"with no coefficient map: two algebra maps over one φ agree on the constants by definition.",
	Build: family.Theorem(Statement{
		Binders: "∀ι:(((D → num) → A) → E). " +
			"∀R:ring_ops(A). " +
			"∀R':ring_ops(B). " +
			"∀S:set(D). " +
			"∀F G:(E → B). " +
			"∀u:E.",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"free_algebra_embedding(R, ι)",
			"ring_homomorphism(free_algebra_ring(ι, R, S), R', F)",
			"ring_homomorphism(free_algebra_ring(ι, R, S), R', G)",
			"∀a:A. a ∈ R.carrier ⇒ F(free_algebra_const(ι, R, a)) = G(free_algebra_const(ι, R, a))",
			"∀x:D. x ∈ S ⇒ F(free_algebra_var(ι, R, x)) = G(free_algebra_var(ι, R, x))",
			"u ∈ free_algebra(ι, R, S)",
		},
		Conclusion: "F(u) = G(u)",
	},
		func(
			a *Argument,
			ι *Arrow[Fun[Fun[D, Nat], A], E],
			R *Expr[RingOps[A]],
			RPrime *Expr[RingOps[B]],
			S *Expr[Set[D]],
			F, G *Arrow[E, B],
			u *Expr[E],
			ring, embedding, homF, homG, constants, variables, uIn Fact,
		) {
			polynomialsOfS := a.TermAs[RingOps[Fun[Fun[D, Nat], A]]]("polynomial_algebra_ring(R, S)")
			algebra := a.TermAs[RingOps[E]]("free_algebra_ring(ι, R, S)")
			afterF := a.TermAs[Fun[Fun[Fun[D, Nat], A], B]]("λg:((D → num) → A). F(ι(g))")
			afterG := a.TermAs[Fun[Fun[Fun[D, Nat], A], B]]("λg:((D → num) → A). G(ι(g))")
			hosting := a.Have(
				"ι is a ring homomorphism from the polynomials of S onto the algebra on S",
				"ring_homomorphism(polynomial_algebra_ring(R, S), free_algebra_ring(ι, R, S), ι)",
				By(ring, embedding, FreeAlgebraRingIsomorphism.At(ι, R, S), ring_homomorphism.RingIsomorphismDef))
			composedF := a.Have(
				"so F after ι is a ring homomorphism out of the polynomials of S",
				"ring_homomorphism(polynomial_algebra_ring(R, S), R', λg:((D → num) → A). F(ι(g)))",
				By(hosting, homF, ring_homomorphism.RingHomCompose.At(polynomialsOfS, algebra, RPrime, ι, F)))
			composedG := a.Have(
				"and so is G after ι",
				"ring_homomorphism(polynomial_algebra_ring(R, S), R', λg:((D → num) → A). G(ι(g)))",
				By(hosting, homG, ring_homomorphism.RingHomCompose.At(polynomialsOfS, algebra, RPrime, ι, G)))
			f, decoded := a.UnpackAs[Fun[Fun[D, Nat], A]](
				a.Unfolded(a.Unfolded(uIn, FreeAlgebraDef), set_basic.ImageDef), "f")
			agree := a.Have(
				"after ι the two agree on the constant polynomials "+
					"and on the polynomials of the variables of S, so at f",
				"F(ι(f)) = G(ι(f))",
				By(
					ring,
					composedF,
					composedG,
					constants,
					variables,
					FreeAlgebraConstDef,
					FreeAlgebraVarDef,
					decoded,
					polynomial_algebra_evaluation.PolynomialAlgebraEvalUnique.At(R, RPrime, S, afterF, afterG, f)))
			a.Show(
				"and ι(f) is u",
				By(Normalized, agree, decoded))
		}),
})}

// FreeAlgebraEvalCongruence — the evaluation of a member of the
// algebra on S reads the coefficient map on R's carrier and the values
// on S only.
var FreeAlgebraEvalCongruence = freeAlgebraEvalCongruenceThm{family.Add(registry.ProofEntry{
	Name: "FreeAlgebraEvalCongruence",
	Key:  "prop_7f8283fa41de6203",
	Reading: "Only the embedding is asked, and neither ring need be commutative: it makes " +
		"the preimage of a member of the algebra on S a polynomial of S, whose coefficients " +
		"lie in R's carrier and whose monomials use variables of S, so the summands agree and " +
		"the two folds are literally the same. The induced maps, the multiplication and the " +
		"substitution are evaluations, so this is how each is read on a set of variables.",
	Deps: []registry.EntryLike{
		FreeAlgebraEvalDef,
		polynomial_algebra_evaluation.PolynomialAlgebraEvalDef,
		polynomial_algebra_evaluation.MonomialEvalDef,
		FreeAlgebraEmbeddingDecode,
		polynomial_algebra.PolynomialAlgebraDef,
		polynomial_algebra.MonomialsDef,
		module.ModuleSumCongruence,
	},
	Build: family.Card(Statement{
		Binders: "∀ι:(((D → num) → A) → E). " +
			"∀R:ring_ops(A). " +
			"∀R':ring_ops(B). " +
			"∀φ φ':(A → B). " +
			"∀θ θ':(D → B). " +
			"∀S:set(D). " +
			"∀u:E.",
		Hypotheses: []string{
			"free_algebra_embedding(R, ι)",
			"∀a:A. a ∈ R.carrier ⇒ φ(a) = φ'(a)",
			"∀x:D. x ∈ S ⇒ θ(x) = θ'(x)",
			"u ∈ free_algebra(ι, R, S)",
		},
		Conclusion: "free_algebra_eval(ι, R, R', φ, θ, u) = free_algebra_eval(ι, R, R', φ', θ', u)",
	},
		"u = ι(f) with f a polynomial of S, and the preimage chosen among all "+
			"polynomials is f (FreeAlgebraEmbeddingDecode); the sum runs over the "+
			"support of f, each term reading φ at a coefficient of f, in R's carrier, "+
			"and θ at the variables of a monomial of S (ModuleSumCongruence twice)"),
})}

// FreeAlgebraEvalNatural — a ring homomorphism applied after an
// evaluation is the evaluation with the coefficient map and the values
// composed with it.
var FreeAlgebraEvalNatural = freeAlgebraEvalNaturalThm{family.Add(registry.ProofEntry{
	Name: "FreeAlgebraEvalNatural",
	Key:  "prop_c4d237ba6a1a53a4",
	Deps: []registry.EntryLike{
		FreeAlgebraEvalUnique,
		FreeAlgebraEvalHom,
		FreeAlgebraEvalConst,
		FreeAlgebraEvalVar,
		ring_homomorphism.RingHomomorphism,
		ring_homomorphism.MapIn,
	},
	Build: family.Card(Statement{
		Binders: "∀ι:(((D → num) → A) → E). " +
			"∀R:ring_ops(A). " +
			"∀R':ring_ops(B). " +
			"∀φ:(A → B). " +
			"∀R'':ring_ops(C). " +
			"∀ψ:(B → C). " +
			"∀S:set(D). " +
			"∀θ:(D → B). " +
			"∀u:E.",
		Hypotheses: []string{
			"free_algebra_embedding(R, ι)",
			"ring_homomorphism(R, R', φ)",
			"ring_homomorphism(R', R'', ψ)",
			"∀x:D. x ∈ S ⇒ θ(x) ∈ R'.carrier",
			"u ∈ free_algebra(ι, R, S)",
		},
		Conclusion: "ψ(free_algebra_eval(ι, R, R', φ, θ, u)) = " +
			"free_algebra_eval(ι, R, R'', λa:A. ψ(φ(a)), λx:D. ψ(θ(x)), u)",
	},
		"both sides are ring homomorphisms from the algebra on S into R'' (FreeAlgebraEvalHom, "+
			"composed with ψ on the left), taking the constant of a to ψ(φ(a)) and the variable x "+
			"of S to ψ(θ(x)) (FreeAlgebraEvalConst, FreeAlgebraEvalVar); FreeAlgebraEvalUnique"),
})}

// ---------------------------------------------------------------------------
// Induced maps
// ---------------------------------------------------------------------------

// FreeAlgebraMapHom — the map induced by φ and by a map h of S into T
// is an algebra map over φ from the algebra on S to the algebra on T.
var FreeAlgebraMapHom = freeAlgebraMapHomThm{family.Add(registry.ProofEntry{
	Name: "FreeAlgebraMapHom",
	Key:  "prop_cc833130a8e7d193",
	Reading: "h(S) ⊆ T is load-bearing only for landing in the algebra on T: without it " +
		"the map is still a ring map into the algebra on 𝕌 over R', fixing the constants over φ.",
	Deps: []registry.EntryLike{
		FreeAlgebraMapDef,
		FreeAlgebraHomomorphismDef,
		FreeAlgebraEvalHom,
		FreeAlgebraEvalConst,
		FreeAlgebraCommRingOn,
		FreeAlgebraConstHom,
		FreeAlgebraVarIn,
		FreeAlgebraOpsIndependentOfVariables,
		FreeAlgebraEvalDef,
		polynomial_algebra_evaluation.PolynomialAlgebraEvalDef,
		polynomial_algebra_evaluation.MonomialEvalDef,
		module.ModuleSumIn,
		module.ModuleSumInMonoid,
		comm_ring.MulMonoidOn,
		ring_homomorphism.MapIn,
	},
	Build: family.Card(Statement{
		Binders: "∀ι:(((D → num) → A) → E). " +
			"∀ι':(((I → num) → B) → C). " +
			"∀R:ring_ops(A). " +
			"∀R':ring_ops(B). " +
			"∀φ:(A → B). " +
			"∀h:(D → I). " +
			"∀S:set(D). " +
			"∀T:set(I).",
		Hypotheses: []string{
			"free_algebra_embedding(R, ι)",
			"free_algebra_embedding(R', ι')",
			"ring_homomorphism(R, R', φ)",
			"∀x:D. x ∈ S ⇒ h(x) ∈ T",
		},
		Conclusion: "free_algebra_homomorphism(ι, " +
			"    ι', " +
			"    R, " +
			"    R', " +
			"    φ, " +
			"    S, " +
			"    T, " +
			"    free_algebra_map(ι, ι', R, R', φ, h))",
	},
		"the map is an evaluation into the algebra on 𝕌 over R', a commutative ring "+
			"(FreeAlgebraCommRingOn), with coefficients carried by the constants after φ, a ring "+
			"homomorphism (FreeAlgebraConstHom), so a ring homomorphism (FreeAlgebraEvalHom); φ carries "+
			"R's carrier into the carrier of R' (MapIn); its values on the algebra on S are finite sums "+
			"of constants times products of the variables h(x) ∈ T, so in the subring on T(the products "+
			"by ModuleSumInMonoid at its multiplicative monoid, MulMonoidOn at FreeAlgebraCommRingOn; the "+
			"sums by ModuleSumIn), which has the same operations (FreeAlgebraOpsIndependentOfVariables); "+
			"the constant of a goes to the constant of φ(a) (FreeAlgebraEvalConst)"),
})}

// FreeAlgebraMapConst — the induced map carries the constant a to the
// constant φ(a).
var FreeAlgebraMapConst = freeAlgebraMapConstThm{family.Add(registry.ProofEntry{
	Name: "FreeAlgebraMapConst",
	Key:  "prop_89d599058c333f38",
	Deps: []registry.EntryLike{
		FreeAlgebraMapDef,
		FreeAlgebraEvalConst,
		FreeAlgebraCommRingOn,
		FreeAlgebraConstHom,
	},
	Build: family.Card(Statement{
		Binders: "∀ι:(((D → num) → A) → E). " +
			"∀ι':(((I → num) → B) → C). " +
			"∀R:ring_ops(A). " +
			"∀R':ring_ops(B). " +
			"∀φ:(A → B). " +
			"∀h:(D → I). " +
			"∀a:A.",
		Hypotheses: []string{
			"free_algebra_embedding(R, ι)",
			"free_algebra_embedding(R', ι')",
			"ring_homomorphism(R, R', φ)",
			"a ∈ R.carrier",
		},
		Conclusion: "free_algebra_map(ι, ι', R, R', φ, h, free_algebra_const(ι, R, a)) = " +
			"free_algebra_const(ι', R', φ(a))",
	},
		"FreeAlgebraEvalConst into the algebra on 𝕌 over R', whose "+
			"constants after φ are a ring homomorphism (FreeAlgebraConstHom)"),
})}

// FreeAlgebraMapVar — the induced map carries the variable x to the
// variable h(x).
var FreeAlgebraMapVar = freeAlgebraMapVarThm{family.Add(registry.ProofEntry{
	Name: "FreeAlgebraMapVar",
	Key:  "prop_186938c7becf04ca",
	Deps: []registry.EntryLike{
		FreeAlgebraMapDef,
		FreeAlgebraEvalVar,
		FreeAlgebraVarIn,
		FreeAlgebraCommRingOn,
		FreeAlgebraConstHom,
	},
	Build: family.Card(Statement{
		Binders: "∀ι:(((D → num) → A) → E). " +
			"∀ι':(((I → num) → B) → C). " +
			"∀R:ring_ops(A). " +
			"∀R':ring_ops(B). " +
			"∀φ:(A → B). " +
			"∀h:(D → I). " +
			"∀x:D.",
		Hypotheses: []string{
			"free_algebra_embedding(R, ι)",
			"free_algebra_embedding(R', ι')",
			"ring_homomorphism(R, R', φ)",
		},
		Conclusion: "free_algebra_map(ι, ι', R, R', φ, h, free_algebra_var(ι, R, x)) = " +
			"free_algebra_var(ι', R', h(x))",
	},
		"FreeAlgebraEvalVar into the algebra on 𝕌 over R', which holds every variable (FreeAlgebraVarIn)"),
})}

// FreeAlgebraMapCongruence — the map induced on the algebra on S reads
// the coefficient map on R's carrier and the map of the variables on S
// only.
var FreeAlgebraMapCongruence = freeAlgebraMapCongruenceThm{family.Add(registry.ProofEntry{
	Name:    "FreeAlgebraMapCongruence",
	Key:     "prop_d389709073b6bae6",
	Reading: "Only the source embedding is needed, and no ring law: ι' and R' enter both sides alike.",
	Deps:    []registry.EntryLike{FreeAlgebraMapDef, FreeAlgebraEvalCongruence},
	Build: family.Card(Statement{
		Binders: "∀ι:(((D → num) → A) → E). " +
			"∀ι':(((I → num) → B) → C). " +
			"∀R:ring_ops(A). " +
			"∀R':ring_ops(B). " +
			"∀φ φ':(A → B). " +
			"∀h h':(D → I). " +
			"∀S:set(D). " +
			"∀u:E.",
		Hypotheses: []string{
			"free_algebra_embedding(R, ι)",
			"∀a:A. a ∈ R.carrier ⇒ φ(a) = φ'(a)",
			"∀x:D. x ∈ S ⇒ h(x) = h'(x)",
			"u ∈ free_algebra(ι, R, S)",
		},
		Conclusion: "free_algebra_map(ι, ι', R, R', φ, h, u) = free_algebra_map(ι, ι', R, R', φ', h', u)",
	},
		"both are evaluations (FreeAlgebraMapDef) whose coefficient maps agree on R's "+
			"carrier and whose values at the variables agree on S; FreeAlgebraEvalCongruence"),
})}

// FreeAlgebraMapIdentity — the map induced by the identities is the
// identity on the algebra.
var FreeAlgebraMapIdentity = freeAlgebraMapIdentityThm{family.Add(registry.ProofEntry{
	Name: "FreeAlgebraMapIdentity",
	Key:  "prop_5c175fc24cd1f4e",
	Deps: []registry.EntryLike{
		FreeAlgebraMapHom,
		FreeAlgebraMapConst,
		FreeAlgebraMapVar,
		FreeAlgebraEvalUnique,
		FreeAlgebraHomomorphismDef,
		ring_homomorphism.RingHomomorphism,
	},
	Build: family.Card(Statement{
		Binders: "∀ι:(((D → num) → A) → E). ∀R:ring_ops(A). ∀u:E.",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"free_algebra_embedding(R, ι)",
			"u ∈ free_algebra(ι, R, 𝕌)",
		},
		Conclusion: "free_algebra_map(ι, ι, R, R, λa:A. a, λx:D. x, u) = u",
	},
		"the induced map and the identity are ring homomorphisms of the algebra on 𝕌 "+
			"(FreeAlgebraMapHom; the identity of a commutative ring) agreeing on the constants "+
			"and the variables (FreeAlgebraMapConst, FreeAlgebraMapVar); FreeAlgebraEvalUnique"),
})}

// FreeAlgebraMapCompose — the induced maps compose as their
// coefficient maps and their maps of variables do.
var FreeAlgebraMapCompose = freeAlgebraMapComposeThm{family.Add(registry.ProofEntry{
	Name: "FreeAlgebraMapCompose",
	Key:  "prop_2bb5459b513a5967",
	Deps: []registry.EntryLike{
		FreeAlgebraMapHom,
		FreeAlgebraMapConst,
		FreeAlgebraMapVar,
		FreeAlgebraEvalUnique,
		FreeAlgebraHomomorphismDef,
		ring_homomorphism.RingHomomorphism,
		ring_homomorphism.MapIn,
	},
	Build: family.Card(Statement{
		Binders: "∀ι:(((D → num) → A) → E). " +
			"∀ι':(((I → num) → B) → C). " +
			"∀ι'':(((F → num) → G) → H). " +
			"∀R:ring_ops(A). " +
			"∀R':ring_ops(B). " +
			"∀R'':ring_ops(G). " +
			"∀φ:(A → B). " +
			"∀φ':(B → G). " +
			"∀h:(D → I). " +
			"∀h':(I → F). " +
			"∀u:E.",
		Hypotheses: []string{
			"free_algebra_embedding(R, ι)",
			"free_algebra_embedding(R', ι')",
			"free_algebra_embedding(R'', ι'')",
			"ring_homomorphism(R, R', φ)",
			"ring_homomorphism(R', R'', φ')",
			"u ∈ free_algebra(ι, R, 𝕌)",
		},
		Conclusion: "free_algebra_map(ι', " +
			"    ι'', " +
			"    R', " +
			"    R'', " +
			"    φ', " +
			"    h', " +
			"    free_algebra_map(ι, ι', R, R', φ, h, u)) = " +
			"free_algebra_map(ι, ι'', R, R'', λa:A. φ'(φ(a)), λx:D. h'(h(x)), u)",
	},
		"both sides are ring homomorphisms from the algebra on 𝕌 over R into the "+
			"algebra on 𝕌 over R'' (FreeAlgebraMapHom, twice on the left), carrying the "+
			"constant of a to the constant of φ'(φ(a)) and the variable x to the variable "+
			"h'(h(x)) (FreeAlgebraMapConst, FreeAlgebraMapVar); FreeAlgebraEvalUnique"),
})}

// FreeAlgebraEvalMap — an evaluation after an induced map is the
// evaluation with the coefficient maps and the maps of variables
// composed.
var FreeAlgebraEvalMap = freeAlgebraEvalMapThm{family.Add(registry.ProofEntry{
	Name: "FreeAlgebraEvalMap",
	Key:  "prop_ef710cd497cdd27d",
	Deps: []registry.EntryLike{
		FreeAlgebraMapHom,
		FreeAlgebraMapConst,
		FreeAlgebraMapVar,
		FreeAlgebraEvalHom,
		FreeAlgebraEvalConst,
		FreeAlgebraEvalVar,
		FreeAlgebraEvalUnique,
		FreeAlgebraHomomorphismDef,
	},
	Build: family.Card(Statement{
		Binders: "∀ι:(((D → num) → A) → E). " +
			"∀ι':(((I → num) → B) → C). " +
			"∀R:ring_ops(A). " +
			"∀R':ring_ops(B). " +
			"∀R'':ring_ops(G). " +
			"∀φ:(A → B). " +
			"∀ψ:(B → G). " +
			"∀h:(D → I). " +
			"∀θ:(I → G). " +
			"∀S:set(D). " +
			"∀u:E.",
		Hypotheses: []string{
			"free_algebra_embedding(R, ι)",
			"free_algebra_embedding(R', ι')",
			"ring_homomorphism(R, R', φ)",
			"ring_homomorphism(R', R'', ψ)",
			"∀x:D. x ∈ S ⇒ θ(h(x)) ∈ R''.carrier",
			"u ∈ free_algebra(ι, R, S)",
		},
		Conclusion: "free_algebra_eval(ι', R', R'', ψ, θ, free_algebra_map(ι, ι', R, R', φ, h, u)) = " +
			"free_algebra_eval(ι, R, R'', λa:A. ψ(φ(a)), λx:D. θ(h(x)), u)",
	},
		"the induced map carries the algebra on S into the algebra on image(h, S) "+
			"(FreeAlgebraMapHom), where θ takes values in R''; so both sides are ring "+
			"homomorphisms from the algebra on S into R'' (FreeAlgebraEvalHom) with the same "+
			"values on the constants and the variables (FreeAlgebraMapConst, FreeAlgebraMapVar, "+
			"FreeAlgebraEvalConst, FreeAlgebraEvalVar); FreeAlgebraEvalUnique"),
})}

// ---------------------------------------------------------------------------
// The multiplication: a monad on the host's subsets
// ---------------------------------------------------------------------------

// FreeAlgebraMultHom — the multiplication is an R-algebra map from the
// algebra over the algebra on S to the algebra on S.
var FreeAlgebraMultHom = freeAlgebraMultHomThm{family.Add(registry.ProofEntry{
	Name: "FreeAlgebraMultHom",
	Key:  "prop_cdf122b7695f5f9d",
	Reading: "The variables of the outer algebra are the members of the algebra " +
		"on S, each its own value; the constants are the constants of R. At S = 𝕌 " +
		"it is the flattening of a polynomial of polynomials into a polynomial.",
	Deps: []registry.EntryLike{
		FreeAlgebraMultDef,
		FreeAlgebraHomomorphismDef,
		FreeAlgebraEvalHom,
		FreeAlgebraEvalConst,
		FreeAlgebraCommRingOn,
		FreeAlgebraConstHom,
		FreeAlgebraOpsIndependentOfVariables,
		FreeAlgebraEvalDef,
		polynomial_algebra_evaluation.PolynomialAlgebraEvalDef,
		polynomial_algebra_evaluation.MonomialEvalDef,
		module.ModuleSumIn,
		module.ModuleSumInMonoid,
		comm_ring.MulMonoidOn,
	},
	Build: family.Card(Statement{
		Binders: "∀ι:(((E → num) → A) → E). ∀R:ring_ops(A). ∀S:set(E).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"free_algebra_embedding(R, ι)",
		},
		Conclusion: "free_algebra_homomorphism(ι, " +
			"    ι, " +
			"    R, " +
			"    R, " +
			"    λa:A. a, " +
			"    free_algebra(ι, R, S), " +
			"    S, " +
			"    free_algebra_mult(ι, R))",
	},
		"an evaluation into the algebra on 𝕌 with the constants as coefficient map and the identity on "+
			"the variables, a ring homomorphism (FreeAlgebraEvalHom); its values on the algebra over the "+
			"algebra on S are finite sums of constants times products of members of the algebra on S, so "+
			"in that subring (the products by ModuleSumInMonoid at its multiplicative monoid, MulMonoidOn "+
			"at FreeAlgebraCommRingOn; the sums by ModuleSumIn); FreeAlgebraEvalConst for the constants"),
})}

// FreeAlgebraMultVar — the multiplication undoes the variables: μ ∘ η
// is the identity.
var FreeAlgebraMultVar = freeAlgebraMultVarThm{family.Add(registry.ProofEntry{
	Name: "FreeAlgebraMultVar",
	Key:  "prop_81d523c6119cc0e3",
	Reading: "u ∈ free_algebra(ι, R, S) is load-bearing: it puts u in the carrier of the " +
		"host ring evaluated in, where the evaluation reads the variable u as its own value.",
	Deps: []registry.EntryLike{
		FreeAlgebraMultDef,
		FreeAlgebraEvalVar,
		FreeAlgebraSubset,
		FreeAlgebraCommRingOn,
		FreeAlgebraConstHom,
	},
	Build: family.Card(Statement{
		Binders: "∀ι:(((E → num) → A) → E). ∀R:ring_ops(A). ∀S:set(E). ∀u:E.",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"free_algebra_embedding(R, ι)",
			"u ∈ free_algebra(ι, R, S)",
		},
		Conclusion: "free_algebra_mult(ι, R, free_algebra_var(ι, R, u)) = u",
	},
		"FreeAlgebraEvalVar at θ the identity, u being in the algebra "+
			"on 𝕌 (FreeAlgebraSubset), the carrier of the ring evaluated in"),
})}

// FreeAlgebraMultUnitRight — the multiplication undoes the variables
// applied inside: μ ∘ F(η) is the identity.
var FreeAlgebraMultUnitRight = freeAlgebraMultUnitRightThm{family.Add(registry.ProofEntry{
	Name: "FreeAlgebraMultUnitRight",
	Key:  "prop_6bb47fa19429471b",
	Deps: []registry.EntryLike{
		FreeAlgebraMultHom,
		FreeAlgebraMapHom,
		FreeAlgebraMapConst,
		FreeAlgebraMapVar,
		FreeAlgebraMultVar,
		FreeAlgebraEvalUnique,
		FreeAlgebraVarIn,
		FreeAlgebraHomomorphismDef,
	},
	Build: family.Card(Statement{
		Binders: "∀ι:(((E → num) → A) → E). ∀R:ring_ops(A). ∀S:set(E). ∀u:E.",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"free_algebra_embedding(R, ι)",
			"u ∈ free_algebra(ι, R, S)",
		},
		Conclusion: "free_algebra_mult(ι, " +
			"    R, " +
			"    free_algebra_map(ι, ι, R, R, λa:A. a, free_algebra_var(ι, R), u)) = " +
			"u",
	},
		"the map of the variables carries the algebra on S into the algebra over the algebra "+
			"on S (FreeAlgebraMapHom, FreeAlgebraVarIn), where the multiplication is a ring "+
			"homomorphism (FreeAlgebraMultHom); the composite fixes the constants and sends the "+
			"variable x to the variable of the variable x and then back to the variable x "+
			"(FreeAlgebraMapVar, FreeAlgebraMultVar); FreeAlgebraEvalUnique against the identity"),
})}

// FreeAlgebraMultNatural — the multiplication commutes with induced
// maps: F(h) ∘ μ = μ ∘ F(F(h)).
var FreeAlgebraMultNatural = freeAlgebraMultNaturalThm{family.Add(registry.ProofEntry{
	Name: "FreeAlgebraMultNatural",
	Key:  "prop_27a0568dcd649597",
	Reading: "The embedding ι' is load-bearing: it makes the target's multiplication " +
		"free_algebra_mult(ι', R') a ring homomorphism, which the comparison of the two sides needs.",
	Deps: []registry.EntryLike{
		FreeAlgebraMultHom,
		FreeAlgebraMultVar,
		FreeAlgebraMapHom,
		FreeAlgebraMapConst,
		FreeAlgebraMapVar,
		FreeAlgebraEvalUnique,
		FreeAlgebraHomomorphismDef,
	},
	Build: family.Card(Statement{
		Binders: "∀ι:(((E → num) → A) → E). " +
			"∀ι':(((C → num) → B) → C). " +
			"∀R:ring_ops(A). " +
			"∀R':ring_ops(B). " +
			"∀φ:(A → B). " +
			"∀h:(E → C). " +
			"∀S:set(E). " +
			"∀u:E.",
		Hypotheses: []string{
			"free_algebra_embedding(R, ι)",
			"free_algebra_embedding(R', ι')",
			"ring_homomorphism(R, R', φ)",
			"u ∈ free_algebra(ι, R, free_algebra(ι, R, S))",
		},
		Conclusion: "free_algebra_map(ι, ι', R, R', φ, h, free_algebra_mult(ι, R, u)) = " +
			"free_algebra_mult(ι', " +
			"    R', " +
			"    free_algebra_map(ι, ι', R, R', φ, free_algebra_map(ι, ι', R, R', φ, h), u))",
	},
		"both sides are ring homomorphisms from the algebra over the algebra on S into the algebra "+
			"on 𝕌 over R' (FreeAlgebraMultHom, FreeAlgebraMapHom); both carry the constant of a to the "+
			"constant of φ(a), and the variable v, a member of the algebra on S, to the image of v under "+
			"the induced map (FreeAlgebraMultVar on each side, FreeAlgebraMapVar); FreeAlgebraEvalUnique"),
})}

// FreeAlgebraMultAssoc — the multiplication is associative: μ ∘ F(μ) =
// μ ∘ μ on the algebra over the algebra over the algebra on S.
var FreeAlgebraMultAssoc = freeAlgebraMultAssocThm{family.Add(registry.ProofEntry{
	Name: "FreeAlgebraMultAssoc",
	Key:  "prop_e155119d925725e5",
	Deps: []registry.EntryLike{
		FreeAlgebraMultHom,
		FreeAlgebraMultVar,
		FreeAlgebraMapHom,
		FreeAlgebraMapConst,
		FreeAlgebraMapVar,
		FreeAlgebraEvalUnique,
		FreeAlgebraHomomorphismDef,
	},
	Build: family.Card(Statement{
		Binders: "∀ι:(((E → num) → A) → E). ∀R:ring_ops(A). ∀S:set(E). ∀u:E.",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"free_algebra_embedding(R, ι)",
			"u ∈ free_algebra(ι, R, free_algebra(ι, R, free_algebra(ι, R, S)))",
		},
		Conclusion: "free_algebra_mult(ι, " +
			"    R, " +
			"    free_algebra_map(ι, ι, R, R, λa:A. a, free_algebra_mult(ι, R), u)) = " +
			"free_algebra_mult(ι, R, free_algebra_mult(ι, R, u))",
	},
		"both sides are ring homomorphisms from the triple algebra into the algebra on S, "+
			"composites of FreeAlgebraMultHom at S and at the algebra on S with FreeAlgebraMapHom; "+
			"both fix the constants, and a variable w, a member of the algebra over the algebra on "+
			"S, goes on the left to the variable of μ(w) and then to μ(w), on the right to w and "+
			"then to μ(w) (FreeAlgebraMapVar, FreeAlgebraMultVar); FreeAlgebraEvalUnique"),
})}

// FreeAlgebraEvalMult — an evaluation after the multiplication is the
// evaluation of the outer polynomial at the evaluations of its
// variables.
var FreeAlgebraEvalMult = freeAlgebraEvalMultThm{family.Add(registry.ProofEntry{
	Name: "FreeAlgebraEvalMult",
	Key:  "prop_89a37987a0d2932f",
	Deps: []registry.EntryLike{
		FreeAlgebraMultHom,
		FreeAlgebraMultVar,
		FreeAlgebraEvalHom,
		FreeAlgebraEvalConst,
		FreeAlgebraEvalVar,
		FreeAlgebraEvalUnique,
		FreeAlgebraHomomorphismDef,
		ring_homomorphism.MapIn,
	},
	Build: family.Card(Statement{
		Binders: "∀ι:(((E → num) → A) → E). " +
			"∀R:ring_ops(A). " +
			"∀R':ring_ops(B). " +
			"∀φ:(A → B). " +
			"∀θ:(E → B). " +
			"∀S:set(E). " +
			"∀u:E.",
		Hypotheses: []string{
			"free_algebra_embedding(R, ι)",
			"ring_homomorphism(R, R', φ)",
			"∀x:E. x ∈ S ⇒ θ(x) ∈ R'.carrier",
			"u ∈ free_algebra(ι, R, free_algebra(ι, R, S))",
		},
		Conclusion: "free_algebra_eval(ι, R, R', φ, θ, free_algebra_mult(ι, R, u)) = " +
			"free_algebra_eval(ι, R, R', φ, λv:E. free_algebra_eval(ι, R, R', φ, θ, v), u)",
	},
		"both sides are ring homomorphisms from the algebra over the algebra on S into "+
			"R' (FreeAlgebraMultHom then FreeAlgebraEvalHom on the left; FreeAlgebraEvalHom "+
			"on the right, the evaluation at θ carrying the algebra on S into R'.carrier); "+
			"both send the constant of a to φ(a) and the variable v to the evaluation of v "+
			"(FreeAlgebraMultVar, FreeAlgebraEvalVar); FreeAlgebraEvalUnique"),
})}

// ---------------------------------------------------------------------------
// Coefficients along a disjoint set of variables
// ---------------------------------------------------------------------------

// FreeAlgebraDisjointCoefficients — over disjoint X and S, a member of
// the algebra on X ∪ S is, in exactly one way, a finite sum of members
// of the algebra on X times monomials of S: its coefficients.
var FreeAlgebraDisjointCoefficients = freeAlgebraDisjointCoefficientsThm{family.Add(registry.ProofEntry{
	Name: "FreeAlgebraDisjointCoefficients",
	Key:  "prop_ca19f7cf0130360f",
	Reading: "Disjointness is load-bearing for the expansion itself, a monomial of X ∪ S splitting " +
		"into its parts on X and on S uniquely only when no variable is in both: with X = S = {x} and " +
		"u = var x the coefficients are x at the monomial of the constants and 1 at the monomial of x, " +
		"so the expansion gives 2x. At X = ∅ the coefficients are constants (FreeAlgebraNoVariables) " +
		"and the expansion is the familiar sum of constants times monomials; at S = ∅ the one monomial " +
		"is the constants' and the coefficient there is u. The monomial m of the host is the product " +
		"of the powers of the variables of m, monomial_eval at the variables.",
	Deps: []registry.EntryLike{
		FreeAlgebraCoefficientAtDef,
		FreeAlgebraRingIsomorphism,
		FreeAlgebraCommRingOn,
		FreeAlgebraVarIn,
		polynomial_algebra_evaluation.MonomialAsProduct,
		polynomial_algebra.MonomialsDef,
		polynomial_algebra.PolynomialAlgebraMulDef,
		free_module.FreeModuleExpand,
		FreeAlgebraEmbeddingDecode,
		module.ModuleSumSupport,
		module.ModuleSumImage,
		module.ModuleSumCongruence,
		finite_set.FiniteImageInjGeneral,
		finite_set.FiniteSubset,
	},
	Build: family.Card(Statement{
		Binders: "∀ι:(((D → num) → A) → E). ∀R:ring_ops(A). ∀X S:set(D). ∀u:E.",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"free_algebra_embedding(R, ι)",
			"X ∩ S = ∅",
			"u ∈ free_algebra(ι, R, X ∪ S)",
		},
		Conclusion: "(∀m:(D → num). " +
			"    free_algebra_coefficient_at(ι, R, X, S, u, m) ∈ free_algebra(ι, R, X)) ∧ " +
			"(∀m:(D → num). " +
			"    m ∉ monomials(S) ⇒ " +
			"    free_algebra_coefficient_at(ι, R, X, S, u, m) = free_algebra_ring(ι, R, 𝕌).zero) ∧ " +
			"finite(fun_support(free_algebra_ring(ι, R, 𝕌).zero, " +
			"        λm:D → num. free_algebra_coefficient_at(ι, R, X, S, u, m))) ∧ " +
			"u = " +
			"module_sum(free_algebra_ring(ι, R, 𝕌).add, " +
			"    free_algebra_ring(ι, R, 𝕌).zero, " +
			"    fun_support(free_algebra_ring(ι, R, 𝕌).zero, " +
			"        λm:D → num. free_algebra_coefficient_at(ι, R, X, S, u, m)), " +
			"    λm:(D → num). " +
			"        free_algebra_ring(ι, R, 𝕌).mul(free_algebra_coefficient_at(ι, R, X, S, u, m), " +
			"            monomial_eval(free_algebra_ring(ι, R, 𝕌), free_algebra_var(ι, R), m))) ∧ " +
			"(∀c:((D → num) → E). " +
			"    (∀m:(D → num). c(m) ∈ free_algebra(ι, R, X)) ∧ " +
			"    (∀m:(D → num). m ∉ monomials(S) ⇒ c(m) = free_algebra_ring(ι, R, 𝕌).zero) ∧ " +
			"    finite(fun_support(free_algebra_ring(ι, R, 𝕌).zero, c)) ∧ " +
			"    u = " +
			"    module_sum(free_algebra_ring(ι, R, 𝕌).add, " +
			"        free_algebra_ring(ι, R, 𝕌).zero, " +
			"        fun_support(free_algebra_ring(ι, R, 𝕌).zero, c), " +
			"        λm:(D → num). " +
			"            free_algebra_ring(ι, R, 𝕌).mul(c(m), " +
			"                monomial_eval(free_algebra_ring(ι, R, 𝕌), free_algebra_var(ι, R), m))) ⇒ " +
			"    ∀m:(D → num). c(m) = free_algebra_coefficient_at(ι, R, X, S, u, m))",
	},
		"u = ι(f) with f a polynomial of X ∪ S; the coefficient at a monomial m of S is ι of n ↦ "+
			"f(n + m) on the monomials n of X, a polynomial of X, nonzero only when f is nonzero at "+
			"some n + m, and (n, m) ↦ n + m is injective on pairs of monomials of the disjoint X and "+
			"S, so finitely many m have a nonzero coefficient; the product of that polynomial with "+
			"the generator at m (MonomialAsProduct) is f restricted to the monomials whose part on S "+
			"is m, and these restrictions sum to f; conversely, if u is such a sum with coefficients "+
			"ι(g_m), the coefficient of f at n + m is g_m(n), which is the definition's value"),
})}

// FreeAlgebraBaseMapCoefficientwise — an algebra map that fixes the
// variables of S and carries the algebra on X into the algebra on X'
// acts on the coefficients along S: the coefficient of the image is the
// image of the coefficient.
var FreeAlgebraBaseMapCoefficientwise = freeAlgebraBaseMapCoefficientwiseThm{family.Add(registry.ProofEntry{
	Name: "FreeAlgebraBaseMapCoefficientwise",
	Key:  "prop_1047add58391241b",
	Reading: "The map may change the coefficient ring and the host (an algebra map over φ), " +
		"but the variables of S keep their names: their images are the variables of S in the " +
		"target. At X' = ∅ the target coefficients are constants, the case of an augmentation " +
		"that sends the variables of X into the coefficients. Off the monomials of S both sides " +
		"are the target's zero: the coefficient there is the source's zero, which Φ keeps.",
	Deps: []registry.EntryLike{
		FreeAlgebraDisjointCoefficients,
		FreeAlgebraHomomorphismDef,
		FreeAlgebraCommRingOn,
		polynomial_algebra_evaluation.MonomialAsProduct,
		ring_homomorphism.RingHomomorphism,
		ring_homomorphism.MapAdd,
		ring_homomorphism.MapMul,
		ring_homomorphism.AdditiveHomomorphism,
		comm_monoid.MapPow,
		module.ModuleSumSupport,
		module.ModuleSumMonoidHomomorphism,
		comm_ring.MulMonoidOn,
	},
	Build: family.Card(Statement{
		Binders: "∀ι:(((D → num) → A) → E). " +
			"∀ι':(((D → num) → B) → C). " +
			"∀R:ring_ops(A). " +
			"∀R':ring_ops(B). " +
			"∀φ:(A → B). " +
			"∀X X' S:set(D). " +
			"∀Φ:(E → C). " +
			"∀u:E. " +
			"∀m:(D → num).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"comm_ring_on(R')",
			"free_algebra_embedding(R, ι)",
			"free_algebra_embedding(R', ι')",
			"X ∩ S = ∅",
			"X' ∩ S = ∅",
			"free_algebra_homomorphism(ι, ι', R, R', φ, X ∪ S, X' ∪ S, Φ)",
			"∀v:E. v ∈ free_algebra(ι, R, X) ⇒ Φ(v) ∈ free_algebra(ι', R', X')",
			"∀y:D. y ∈ S ⇒ Φ(free_algebra_var(ι, R, y)) = free_algebra_var(ι', R', y)",
			"u ∈ free_algebra(ι, R, X ∪ S)",
		},
		Conclusion: "free_algebra_coefficient_at(ι', R', X', S, Φ(u), m) = " +
			"Φ(free_algebra_coefficient_at(ι, R, X, S, u, m))",
	},
		"expand u along S (FreeAlgebraDisjointCoefficients); Φ keeps finite sums and finite products "+
			"(ModuleSumMonoidHomomorphism at the multiplicative monoid, MulMonoidOn) and fixes each variable "+
			"of S, so it fixes each monomial of S (MonomialAsProduct, MapPow) and carries the expansion of u "+
			"to the sum of Φ of the coefficients times the same monomials; those images lie in the algebra "+
			"on X', vanish off the monomials of S and are nonzero at finitely many, so by the uniqueness "+
			"half of FreeAlgebraDisjointCoefficients over X' they are the coefficients of Φ(u)"),
})}

// ---------------------------------------------------------------------------
// Substitution and division by a monic linear factor
// ---------------------------------------------------------------------------

// FreeAlgebraSubstituteHom — substituting a member c of the algebra
// without y for y is an R-algebra map from the algebra on S onto the
// algebra on S ∖ {y}, fixing that algebra.
var FreeAlgebraSubstituteHom = freeAlgebraSubstituteHomThm{family.Add(registry.ProofEntry{
	Name: "FreeAlgebraSubstituteHom",
	Key:  "prop_ec7aa7c4d23a39fc",
	Reading: "y ∉ S is allowed: then S ∖ {y} = S and the " +
		"substitution is the identity on the algebra on S.",
	Deps: []registry.EntryLike{
		FreeAlgebraSubstituteDef,
		FreeAlgebraHomomorphismDef,
		FreeAlgebraEvalHom,
		FreeAlgebraEvalConst,
		FreeAlgebraEvalVar,
		FreeAlgebraEvalUnique,
		FreeAlgebraVarIn,
		FreeAlgebraConstHom,
		FreeAlgebraCommRingOn,
		FreeAlgebraOpsIndependentOfVariables,
		set_basic.InDiff,
	},
	Build: family.Card(Statement{
		Binders: "∀ι:(((D → num) → A) → E). ∀R:ring_ops(A). ∀S:set(D). ∀y:D. ∀c:E.",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"free_algebra_embedding(R, ι)",
			"c ∈ free_algebra(ι, R, S ∖ {y})",
		},
		Conclusion: "free_algebra_homomorphism(ι, " +
			"    ι, " +
			"    R, " +
			"    R, " +
			"    λa:A. a, " +
			"    S, " +
			"    S ∖ {y}, " +
			"    free_algebra_substitute(ι, R, y, c)) ∧ " +
			"(∀u:E. u ∈ free_algebra(ι, R, S ∖ {y}) ⇒ free_algebra_substitute(ι, R, y, c, u) = u)",
	},
		"the substitution is an evaluation into the algebra on 𝕌 with the constants as coefficient "+
			"map (FreeAlgebraEvalHom, FreeAlgebraEvalConst), and its values at the variables of S, c at "+
			"y and the variable itself elsewhere, lie in the algebra on S ∖ {y}, a subring with the "+
			"same operations; on the algebra on S ∖ {y} it agrees with the identity on the constants "+
			"and the variables (FreeAlgebraEvalVar), so it is the identity there (FreeAlgebraEvalUnique)"),
})}

// FreeAlgebraMonicLinearDivision — division by var y − c, for c not
// involving y: every member of the algebra on S is a multiple of
// var y − c plus its value at y := c.
var FreeAlgebraMonicLinearDivision = freeAlgebraMonicLinearDivisionThm{family.Add(registry.ProofEntry{
	Name: "FreeAlgebraMonicLinearDivision",
	Key:  "prop_32eed49c5dd4e6eb",
	Reading: "No hypothesis on c beyond not involving y: var y − c is monic of degree one " +
		"in y, so the division needs no unit and holds over any commutative ring. The remainder " +
		"is the substitution, a member of the algebra on S ∖ {y} (FreeAlgebraSubstituteHom).",
	Deps: []registry.EntryLike{
		FreeAlgebraSubstituteHom,
		FreeAlgebraDisjointCoefficients,
		FreeAlgebraCommRingOn,
		FreeAlgebraVarIn,
		FreeAlgebraSubset,
		ring_homomorphism.MapAdd,
		ring_homomorphism.MapMul,
		FreeAlgebraHomomorphismDef,
	},
	Build: family.Card(Statement{
		Binders: "∀ι:(((D → num) → A) → E). ∀R:ring_ops(A). ∀S:set(D). ∀y:D. ∀c u:E.",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"free_algebra_embedding(R, ι)",
			"y ∈ S",
			"c ∈ free_algebra(ι, R, S ∖ {y})",
			"u ∈ free_algebra(ι, R, S)",
		},
		Conclusion: "∃q:E. " +
			"    q ∈ free_algebra(ι, R, S) ∧ " +
			"    u = " +
			"    free_algebra_ring(ι, R, S).add(free_algebra_ring(ι, R, S).mul( " +
			"            free_algebra_ring(ι, R, S).sub(free_algebra_var(ι, R, y), c), q), " +
			"        free_algebra_substitute(ι, R, y, c, u))",
	},
		"expand u along {y} over S ∖ {y} (FreeAlgebraDisjointCoefficients): u is the sum of a_k * "+
			"y ^ k with a_k in the algebra on S ∖ {y}, and the substitution is the sum of a_k * c ^ k "+
			"(FreeAlgebraSubstituteHom); each y ^ k − c ^ k is (y − c) times the sum of y ^ i * c ^ "+
			"(k − 1 − i) over i < k, so q is the sum of a_k times these, a member of the algebra on S"),
})}

// FreeAlgebraMonicLinearRegular — var y − c, for c not involving y, is
// not a zero divisor in the algebra on S.
var FreeAlgebraMonicLinearRegular = freeAlgebraMonicLinearRegularThm{family.Add(registry.ProofEntry{
	Name: "FreeAlgebraMonicLinearRegular",
	Key:  "prop_5ec596f85e03cb5f",
	Reading: "True over every commutative ring, the zero ring included (where u is the " +
		"zero anyway): the factor is monic in y, so the product's top coefficient in y is u's.",
	Deps: []registry.EntryLike{
		FreeAlgebraDisjointCoefficients,
		FreeAlgebraCommRingOn,
		FreeAlgebraVarIn,
		FreeAlgebraSubset,
	},
	Build: family.Card(Statement{
		Binders: "∀ι:(((D → num) → A) → E). ∀R:ring_ops(A). ∀S:set(D). ∀y:D. ∀c u:E.",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"free_algebra_embedding(R, ι)",
			"y ∈ S",
			"c ∈ free_algebra(ι, R, S ∖ {y})",
			"u ∈ free_algebra(ι, R, S)",
			"free_algebra_ring(ι, R, S).mul(free_algebra_ring(ι, R, S).sub(free_algebra_var(ι, R, y), c), " +
				"    u) = " +
				"free_algebra_ring(ι, R, S).zero",
		},
		Conclusion: "u = free_algebra_ring(ι, R, S).zero",
	},
		"expand u along {y} over S ∖ {y} (FreeAlgebraDisjointCoefficients) as the "+
			"sum of a_k * y ^ k; if u ≠ 0, let d be the largest k with a_k ≠ 0; the "+
			"coefficient of the product at y ^ (d + 1) is a_d, since c does not involve "+
			"y, so the product is not zero by the uniqueness of the coefficients"),
})}

// FreeAlgebraMonicLinearDivides — a member of the algebra on S vanishes
// at y := c exactly when var y − c divides it there.
var FreeAlgebraMonicLinearDivides = freeAlgebraMonicLinearDividesThm{family.Add(registry.ProofEntry{
	Name: "FreeAlgebraMonicLinearDivides",
	Key:  "prop_916fb4936424940a",
	Reading: "The substitution sends var y − c to c − c = 0 and keeps products, which " +
		"is the backward direction; the forward direction is FreeAlgebraMonicLinearDivision " +
		"with remainder zero, y ∈ S and c free of y making var y − c monic and linear in y.",
	Deps: []registry.EntryLike{
		FreeAlgebraMonicLinearDivision,
		FreeAlgebraSubstituteHom,
		FreeAlgebraHomomorphismDef,
		FreeAlgebraVarIn,
		FreeAlgebraCommRingOn,
		FreeAlgebraEvalVar,
		ring_homomorphism.MapMul,
		ring_homomorphism.AdditiveHomomorphism,
	},
	Build: family.Card(Statement{
		Binders: "∀ι:(((D → num) → A) → E). ∀R:ring_ops(A). ∀S:set(D). ∀y:D. ∀c u:E.",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"free_algebra_embedding(R, ι)",
			"y ∈ S",
			"c ∈ free_algebra(ι, R, S ∖ {y})",
			"u ∈ free_algebra(ι, R, S)",
		},
		Conclusion: "free_algebra_substitute(ι, R, y, c, u) = free_algebra_ring(ι, R, S).zero ⇔ " +
			"∃q:E. " +
			"    q ∈ free_algebra(ι, R, S) ∧ " +
			"    u = " +
			"    free_algebra_ring(ι, R, S).mul( " +
			"        free_algebra_ring(ι, R, S).sub(free_algebra_var(ι, R, y), c), q)",
	},
		"if the substitution is zero, FreeAlgebraMonicLinearDivision leaves u the multiple; "+
			"conversely the substitution keeps products (FreeAlgebraSubstituteHom), sends var y "+
			"to c and fixes c, so it sends var y − c to c − c = 0 and the multiple to 0"),
})}

// ---------------------------------------------------------------------------
// Quotients: eliminating a variable, and reducing modulo a monic quadratic
// ---------------------------------------------------------------------------

// FreeAlgebraSubstitutionQuotient — for c not involving y, the algebra
// on S modulo g and var y − c is the algebra on S ∖ {y} modulo g with c
// put for y, through the substitution y := c.
var FreeAlgebraSubstitutionQuotient = freeAlgebraSubstitutionQuotientThm{family.Add(registry.ProofEntry{
	Name: "FreeAlgebraSubstitutionQuotient",
	Key:  "prop_c9c07161ce9c48f2",
	Reading: "The relation var y − c eliminates y: modulo it every member is its substitution. " +
		"The plane-curve case is S = {x, y} with x ≠ y, S ∖ {y} = {x}, and c a polynomial in x: " +
		"k[x, y]/(g, y − c) ≅ k[x]/(g(x, c)). y ∈ S is load-bearing: otherwise var y − c is no " +
		"member of the algebra on S and the first ideal is ⋂∅ = 𝕌. The isomorphism is named — the " +
		"substitution read at the chosen member of a coset — and the formula on cosets is the " +
		"second conjunct. Over any commutative ring; at g = 0 it says the algebra on S modulo var " +
		"y − c is the algebra on S ∖ {y}, up to the quotient by {0}. The chosen member of a coset " +
		"is harmless because the substitution sends g and var y − c into the ideal of g(y := c).",
	Deps: []registry.EntryLike{
		FreeAlgebraSubstituteHom,
		FreeAlgebraMonicLinearDivides,
		FreeAlgebraCommRingOn,
		FreeAlgebraSubset,
		FreeAlgebraVarIn,
		FreeAlgebraHomomorphismDef,
		FreeAlgebraOpsIndependentOfVariables,
		quotient_ring.QuotientFirstIso,
		quotient_ring.IdealQuotientProjection,
		quotient_ring.IdealQuotientRingDef,
		quotient_ring.IdealQuotientProjectionDef,
		ring_ideal.SpanIdeal,
		ring_ideal.SpanContains,
		ring_ideal.SpanLeast,
		ring_ideal.SpanInsert,
		ring_ideal.IdealAdd,
		ring_ideal.IdealMul,
		ring_homomorphism.RingKernelDef,
		ring_homomorphism.MapMul,
		ring_homomorphism.AdditiveHomomorphism,
	},
	Build: family.Card(Statement{
		Binders: "∀ι:(((D → num) → A) → E). ∀R:ring_ops(A). ∀S:set(D). ∀y:D. ∀c g:E.",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"free_algebra_embedding(R, ι)",
			"y ∈ S",
			"c ∈ free_algebra(ι, R, S ∖ {y})",
			"g ∈ free_algebra(ι, R, S)",
		},
		Conclusion: "ring_isomorphism(ideal_quotient_ring(free_algebra_ring(ι, R, S), " +
			"        ideal_span(restrict_ring(free_algebra_ring(ι, R, S), free_algebra(ι, R, S)), " +
			"            {g, free_algebra_ring(ι, R, S).sub(free_algebra_var(ι, R, y), c)})), " +
			"    ideal_quotient_ring(free_algebra_ring(ι, R, S ∖ {y}), " +
			"        ideal_span(free_algebra_ring(ι, R, S ∖ {y}), " +
			"            {free_algebra_substitute(ι, R, y, c, g)})), " +
			"    induced_map(λu:E. " +
			"            ideal_quotient_projection(free_algebra_ring(ι, R, S ∖ {y}), " +
			"                ideal_span(free_algebra_ring(ι, R, S ∖ {y}), " +
			"                    {free_algebra_substitute(ι, R, y, c, g)}), " +
			"                free_algebra_substitute(ι, R, y, c, u)))) ∧ " +
			"(∀u:E. " +
			"    u ∈ free_algebra(ι, R, S) ⇒ " +
			"    induced_map(λu:E. " +
			"            ideal_quotient_projection(free_algebra_ring(ι, R, S ∖ {y}), " +
			"                ideal_span(free_algebra_ring(ι, R, S ∖ {y}), " +
			"                    {free_algebra_substitute(ι, R, y, c, g)}), " +
			"                free_algebra_substitute(ι, R, y, c, u)), " +
			"        ideal_quotient_projection(free_algebra_ring(ι, R, S), " +
			"            ideal_span(restrict_ring(free_algebra_ring(ι, R, S), free_algebra(ι, R, S)), " +
			"                {g, free_algebra_ring(ι, R, S).sub(free_algebra_var(ι, R, y), c)}), " +
			"            u)) = " +
			"    ideal_quotient_projection(free_algebra_ring(ι, R, S ∖ {y}), " +
			"        ideal_span(free_algebra_ring(ι, R, S ∖ {y}), {free_algebra_substitute(ι, R, y, c, g)}), " +
			"        free_algebra_substitute(ι, R, y, c, u)))",
	},
		"the map u ↦ u(y := c) + J is a ring map from the algebra on S onto the quotient by J "+
			"(FreeAlgebraSubstituteHom, onto since it fixes the algebra on S ∖ {y}; "+
			"IdealQuotientProjection); its kernel is the ideal I of g and var y − c: I lies in it, "+
			"the substitution sending g into J and var y − c to c − c = 0; conversely if u(y := c) "+
			"lies in J it is g(y := c) * h with h in the algebra on S ∖ {y} (SpanInsert at one "+
			"generator), so u − g * h substitutes to zero and is a multiple of var y − c "+
			"(FreeAlgebraMonicLinearDivides), putting u in I (IdealAdd, IdealMul); QuotientFirstIso "+
			"at this map, its kernel rewritten to I (RingKernelDef), gives both conjuncts"),
})}

// FreeAlgebraMonicQuadraticReduction — for f not involving y, every
// member of the algebra on S is p + q · var y modulo var y · var y − f,
// with p and q not involving y and determined by it.
var FreeAlgebraMonicQuadraticReduction = freeAlgebraMonicQuadraticReductionThm{family.Add(registry.ProofEntry{
	Name: "FreeAlgebraMonicQuadraticReduction",
	Key:  "prop_c87d0906f007eef3",
	Reading: "The plane-curve case is S = {x, y}, S ∖ {y} = {x}: modulo y² − f(x) every " +
		"polynomial is p(x) + q(x) y, uniquely — the basis 1, y of the coordinate ring over " +
		"k[x]. The uniqueness half is stated on the representations themselves: two of them " +
		"with the same value have the same p and q, whatever multiples of the quadratic they " +
		"carry. Over any commutative ring, the zero ring included: the quadratic is monic in " +
		"y, so a nonzero multiple of it has y-degree at least two, which p + q · var y has not.",
	Deps: []registry.EntryLike{
		FreeAlgebraDisjointCoefficients,
		FreeAlgebraMonicLinearRegular,
		FreeAlgebraCommRingOn,
		FreeAlgebraVarIn,
		FreeAlgebraSubset,
		polynomial_algebra_evaluation.MonomialAsProduct,
		FreeAlgebraOpsIndependentOfVariables,
	},
	Build: family.Card(Statement{
		Binders: "∀ι:(((D → num) → A) → E). ∀R:ring_ops(A). ∀S:set(D). ∀y:D. ∀f:E.",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"free_algebra_embedding(R, ι)",
			"y ∈ S",
			"f ∈ free_algebra(ι, R, S ∖ {y})",
		},
		Conclusion: "(∀u:E. " +
			"    u ∈ free_algebra(ι, R, S) ⇒ " +
			"    ∃p q h:E. " +
			"        p ∈ free_algebra(ι, R, S ∖ {y}) ∧ " +
			"        q ∈ free_algebra(ι, R, S ∖ {y}) ∧ " +
			"        h ∈ free_algebra(ι, R, S) ∧ " +
			"        u = " +
			"        free_algebra_ring(ι, R, S).add(free_algebra_ring(ι, R, S).add(p, " +
			"                free_algebra_ring(ι, R, S).mul(q, free_algebra_var(ι, R, y))), " +
			"            free_algebra_ring(ι, R, S).mul(free_algebra_ring(ι, R, S).sub(free_algebra_ring(ι, " +
			"                        R, " +
			"                        S).mul(free_algebra_var(ι, R, y), free_algebra_var(ι, R, y)), " +
			"                    f), " +
			"                h))) ∧ " +
			"(∀p q h p' q' h':E. " +
			"    p ∈ free_algebra(ι, R, S ∖ {y}) ∧ " +
			"    q ∈ free_algebra(ι, R, S ∖ {y}) ∧ " +
			"    h ∈ free_algebra(ι, R, S) ∧ " +
			"    p' ∈ free_algebra(ι, R, S ∖ {y}) ∧ " +
			"    q' ∈ free_algebra(ι, R, S ∖ {y}) ∧ " +
			"    h' ∈ free_algebra(ι, R, S) ∧ " +
			"    free_algebra_ring(ι, R, S).add(free_algebra_ring(ι, R, S).add(p, " +
			"            free_algebra_ring(ι, R, S).mul(q, free_algebra_var(ι, R, y))), " +
			"        free_algebra_ring(ι, R, S).mul(free_algebra_ring(ι, R, S).sub(free_algebra_ring(ι, " +
			"                    R, " +
			"                    S).mul(free_algebra_var(ι, R, y), free_algebra_var(ι, R, y)), " +
			"                f), " +
			"            h)) = " +
			"    free_algebra_ring(ι, R, S).add(free_algebra_ring(ι, R, S).add(p', " +
			"            free_algebra_ring(ι, R, S).mul(q', free_algebra_var(ι, R, y))), " +
			"        free_algebra_ring(ι, R, S).mul(free_algebra_ring(ι, R, S).sub(free_algebra_ring(ι, " +
			"                    R, " +
			"                    S).mul(free_algebra_var(ι, R, y), free_algebra_var(ι, R, y)), " +
			"                f), " +
			"            h')) ⇒ " +
			"    p = p' ∧ q = q')",
	},
		"expand along {y} over S ∖ {y} (FreeAlgebraDisjointCoefficients): u is the finite sum of a_k "+
			"* y ^ k with a_k not involving y; existence by induction on the largest k with a_k ≠ 0: for "+
			"k ≥ 2, y ^ k = y ^ (k − 2) * (var y · var y − f) + f * y ^ (k − 2), which lowers the degree, "+
			"the multiples of the quadratic collected into h; uniqueness: the difference of the two sides "+
			"gives (p − p') + (q − q') · var y = (var y · var y − f) · (h' − h); were h' − h nonzero, "+
			"with top coefficient b at y ^ d, the right side would have the coefficient b at y ^ (d + 2), "+
			"the quadratic being monic in y, while the left has none above y, against the uniqueness of "+
			"the coefficients; so h' = h, and the coefficients at 1 and y give p = p', q = q'"),
})}
