package real_polynomial_geometry

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/semialgebraic_properties"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_algebra"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_algebra_evaluation"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_encoding"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	_ "github.com/euc-ai/xugo/library/proofs/cartesian/carrier"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/real/real_closed_instance"
	"github.com/euc-ai/xugo/library/proofs/real/real_continuous"
	"github.com/euc-ai/xugo/library/proofs/real/real_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_ordered_instance"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/proofs/real/real_topology"
	_ "github.com/euc-ai/xugo/library/proofs/relations/order"
	_ "github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_product"
	"github.com/euc-ai/xugo/library/proofs/topology/compact"
	"github.com/euc-ai/xugo/library/proofs/topology/continuous"
	"github.com/euc-ai/xugo/library/proofs/topology/metric_space"
	"github.com/euc-ai/xugo/library/proofs/topology/product_topology"
	"github.com/euc-ai/xugo/library/proofs/topology/real_valued"
	"github.com/euc-ai/xugo/library/proofs/vector/euclidean_topology"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// ---------------------------------------------------------------------------
// Reading the real field
// ---------------------------------------------------------------------------

// RealRingTuple — a tuple of reals of length n is an n-vector: the real
// ring's zero is 0 and its carrier is every real.
var RealRingTuple = realRingTupleThm{family.Add(registry.ProofEntry{
	Name: "RealRingTuple",
	Key:  "prop_5e80bbba4bf628cf",
	Build: family.Theorem(
		"∀n:num. ∀x:(num → real). ring_tuple(real_ring, n, x) ⇔ vec⟨n⟩(x)",
		func(a *Argument, n *Expr[Nat], x *Expr[Fun[Nat, Real]]) {
			a.Show(
				"by the definition of a ring tuple",
				By(polynomial_encoding.RingTupleDef, set_basic.InUniv))
		}),
})}

// RealCarrierCube — the carrier cube of ℝ is the unit cube: read at the
// real field, whose carrier is every real and whose weak order is ≤, a
// point of the carrier cube is an n-vector (RealRingTuple) with its
// coordinates in ⟦0, 1⟧.
var RealCarrierCube = realCarrierCubeThm{family.Add(registry.ProofEntry{
	Name: "RealCarrierCube",
	Key:  "prop_b44808a353baa2d5",
	Build: family.Theorem(
		"∀n:num. carrier_cube(real_field_ops, real_lt, n) = unit_cube(n)",
		func(a *Argument, n *Expr[Nat]) {
			a.Show(
				"both cubes are the n-vectors with coordinates in ⟦0, 1⟧",
				Simp(Fwd(real_field.RealFieldOpsDef)),
				BySets(
					a.Simplified(
						semialgebraic_properties.CarrierCubeDef.At(
							a.TermAs[field.FieldOps[Real]]("real_field_ops"), a.TermAs[Fun2[Real, Real, Bool]]("real_lt"), n),
						Fwd(real_ordered_instance.RealOrderedLe),
						Fwd(real_field.RealFieldRing),
						Fwd(real_field.RealFieldOpsDef),
						Fwd(RealRingTuple)),
					euclidean_topology.UnitCubeDef.At(n)))
		}),
})}

// ---------------------------------------------------------------------------
// Continuity
// ---------------------------------------------------------------------------

// PolynomialContinuous — multivariate real polynomial functions are
// continuous in every finite dimension. By induction on the polynomials
// below n: the continuous ones hold the constants, whose value maps are
// constant, and are closed under sums and under multiplication by a
// variable j below n, whose value maps are sums and products of continuous
// real functions, the coordinate j among them.
var PolynomialContinuous = polynomialContinuousThm{family.Add(registry.ProofEntry{
	Name: "PolynomialContinuous",
	Key:  "prop_966835b18cb0cef9",
	Build: family.Theorem(Statement{
		Binders: "∀n:num. ∀p:((num → num) → real).",
		Hypotheses: []string{
			"p ∈ polynomial_algebra(real_ring, {i:num | i < n})",
		},
		Conclusion: "continuous_map(euclidean_topology(n), " +
			"    real_topology, " +
			"    λx:(num → real). polynomial_value(real_ring, p, x))",
	}, func(a *Argument, n *Expr[Nat], p *Expr[Fun[Fun[Nat, Nat], Real]], pIn Fact) {
		type poly = Fun[Fun[Nat, Nat], Real]
		type point = Fun[Nat, Real]
		ring := a.TermAs[module_record.RingOps[Real]]("real_ring")
		identity := a.TermAs[Fun[Real, Real]]("λa:real. a")
		variables := a.TermAs[Set[Nat]]("{i:num | i < n}")
		space := a.TermAs[Set[Set[point]]]("euclidean_topology(n)")
		line := a.TermAs[Set[Set[Real]]]("real_topology")
		continuousPolynomials, continuousDef := a.LetAs[Set[poly]](
			"C",
			"{q:((num → num) → real) | "+
				"    q ∈ polynomial_algebra(real_ring, {i:num | i < n}) ∧ "+
				"    continuous_map(euclidean_topology(n), "+
				"        real_topology, "+
				"        λx:(num → real). polynomial_value(real_ring, q, x))}")
		evaluation := a.Have(
			"a polynomial is evaluated through the identity of ℝ, a ring homomorphism",
			"ring_homomorphism(real_ring, real_ring, λa:real. a)",
			Cite(ring_homomorphism.RingHomIdentity.Read(real_ring.CommRingOn)))
		polynomials := a.Have(
			"the polynomials below n form a commutative ring",
			"comm_ring_on(polynomial_algebra_ring(real_ring, {i:num | i < n}))",
			By(real_ring.CommRingOn, polynomial_algebra.PolynomialAlgebraCommRingOn.At(ring, variables)))
		polynomialRing := a.TermAs[module_record.RingOps[poly]](
			"polynomial_algebra_ring(real_ring, {i:num | i < n})")
		constantsIn := a.Have(
			"the constants are continuous polynomials",
			"∀c:real. polynomial_algebra_const(real_ring, c) ∈ C",
			Derive(func(b *Argument) {
				c := b.FixAs[Real]("c")
				value := b.Have(
					"a constant polynomial takes its constant as value",
					"∀x:(num → real). polynomial_value(real_ring, polynomial_algebra_const(real_ring, c), x) = c",
					b.ForEach(func(x *Expr[point]) Action {
						return By(
							evaluation,
							polynomial_encoding.PolynomialValueDef,
							polynomial_algebra_evaluation.PolynomialAlgebraEvalConst.At(ring, ring, identity, x, c),
							set_basic.InUniv)
					}))
				flat := b.Have(
					"so its value map is the constant map at c",
					"continuous_map(euclidean_topology(n), "+
						"    real_topology, "+
						"    λx:(num → real). polynomial_value(real_ring, polynomial_algebra_const(real_ring, c), x))",
					By(
						value,
						euclidean_topology.EuclideanTopology.At(n),
						continuous.Constant.At(space, line, c),
						Where(continuous.Eq, "f", b.TermAs[Fun[point, Real]]("λx:(num → real). c")),
						real_topology.RealSpace,
						set_basic.InUniv))
				b.Show(
					"and the constants are polynomials, the image of a ring homomorphism",
					BySets(
						continuousDef,
						flat,
						real_ring.CommRingOn,
						polynomial_algebra.PolynomialAlgebraConstHom.At(ring, variables),
						ring_homomorphism.MapIn.At(
							ring, polynomialRing, b.TermAs[Fun[Real, poly]]("polynomial_algebra_const(real_ring)"), c)))
			}))
		sumsIn := a.Have(
			"a sum of continuous polynomials is one",
			"∀f g:((num → num) → real). f ∈ C ∧ g ∈ C ⇒ fun_add(f, g) ∈ C",
			Derive(func(b *Argument) {
				f := b.FixAs[poly]("f")
				g := b.FixAs[poly]("g")
				parts := b.Conjuncts(
					b.Have(
						"f and g are continuous polynomials",
						"f ∈ polynomial_algebra(real_ring, {i:num | i < n}) ∧ "+
							"continuous_map(euclidean_topology(n), "+
							"    real_topology, "+
							"    λx:(num → real). polynomial_value(real_ring, f, x)) ∧ "+
							"g ∈ polynomial_algebra(real_ring, {i:num | i < n}) ∧ "+
							"continuous_map(euclidean_topology(n), "+
							"    real_topology, "+
							"    λx:(num → real). polynomial_value(real_ring, g, x))",
						BySets(b.Assume(), continuousDef)),
					"f is a polynomial",
					"f is continuous",
					"g is a polynomial",
					"g is continuous")
				value := b.Have(
					"the sum takes the sum of the values",
					"∀x:(num → real). "+
						"    polynomial_value(real_ring, fun_add(f, g), x) = "+
						"    polynomial_value(real_ring, f, x) + polynomial_value(real_ring, g, x)",
					b.ForEach(func(x *Expr[point]) Action {
						return By(
							evaluation,
							parts[0],
							parts[2],
							polynomial_encoding.PolynomialValueDef,
							polynomial_algebra_evaluation.PolynomialAlgebraEvalAdd.At(ring, ring, identity, x, variables, f, g),
							set_basic.InUniv)
					}))
				sum := b.Have(
					"so its value map is the sum of two continuous maps",
					"continuous_map(euclidean_topology(n), "+
						"    real_topology, "+
						"    λx:(num → real). polynomial_value(real_ring, fun_add(f, g), x))",
					By(
						value,
						parts[1],
						parts[3],
						euclidean_topology.EuclideanTopology.At(n),
						real_valued.ContinuousRealAdd.At(
							space,
							b.TermAs[Fun[point, Real]]("λx:(num → real). polynomial_value(real_ring, f, x)"),
							b.TermAs[Fun[point, Real]]("λx:(num → real). polynomial_value(real_ring, g, x)")),
						Where(
							continuous.Eq,
							"f",
							b.TermAs[Fun[point, Real]](
								"λx:(num → real). polynomial_value(real_ring, f, x) + polynomial_value(real_ring, g, x)"))))
				b.Show(
					"and the polynomials are closed under sums",
					BySets(
						continuousDef,
						parts[0],
						parts[2],
						sum,
						comm_ring.AddIn.At(polynomialRing, f, g),
						polynomials))
			}))
		productsIn := a.Have(
			"a variable below n times a continuous polynomial is one",
			Statement{
				Binders: "∀j:num. ∀f:((num → num) → real).",
				Hypotheses: []string{
					"j ∈ {i:num | i < n}",
					"f ∈ C",
				},
				Conclusion: "polynomial_algebra_mul(real_ring, polynomial_algebra_var(real_ring, j), f) ∈ C",
			},
			Derive(func(b *Argument) {
				j := b.FixAs[Nat]("j")
				f := b.FixAs[poly]("f")
				parts := b.Conjuncts(
					b.Have(
						"j is below n and f is a continuous polynomial",
						"j < n ∧ "+
							"f ∈ polynomial_algebra(real_ring, {i:num | i < n}) ∧ "+
							"continuous_map(euclidean_topology(n), "+
							"    real_topology, "+
							"    λx:(num → real). polynomial_value(real_ring, f, x))",
						BySets(b.Assume(), continuousDef)),
					"j is below n",
					"f is a polynomial",
					"f is continuous")
				variable := b.TermAs[poly]("polynomial_algebra_var(real_ring, j)")
				variableIn := b.Have(
					"the variable j is a polynomial below n",
					"polynomial_algebra_var(real_ring, j) ∈ polynomial_algebra(real_ring, {i:num | i < n})",
					By(
						real_ring.CommRingOn,
						parts[0],
						polynomial_algebra.PolynomialAlgebraVarIn.At(ring, variables, j)))
				value := b.Have(
					"the product takes the coordinate j times the value",
					"∀x:(num → real). "+
						"    polynomial_value(real_ring, "+
						"        polynomial_algebra_mul(real_ring, polynomial_algebra_var(real_ring, j), f), "+
						"        x) = "+
						"    x(j) * polynomial_value(real_ring, f, x)",
					b.ForEach(func(x *Expr[point]) Action {
						return By(
							evaluation,
							variableIn,
							parts[1],
							polynomial_encoding.PolynomialValueDef,
							polynomial_algebra_evaluation.PolynomialAlgebraEvalMul.At(
								ring, ring, identity, x, variables, variable, f),
							polynomial_algebra_evaluation.PolynomialAlgebraEvalVar.At(ring, ring, identity, x, j),
							set_basic.InUniv)
					}))
				product := b.Have(
					"so its value map is the product of the coordinate j and a continuous map",
					"continuous_map(euclidean_topology(n), "+
						"    real_topology, "+
						"    λx:(num → real). "+
						"        polynomial_value(real_ring, "+
						"            polynomial_algebra_mul(real_ring, polynomial_algebra_var(real_ring, j), f), "+
						"            x))",
					By(
						value,
						parts[0],
						parts[2],
						euclidean_topology.CoordinateContinuous.At(n, j),
						euclidean_topology.EuclideanTopology.At(n),
						real_valued.ContinuousRealMul.At(
							space,
							b.TermAs[Fun[point, Real]]("λx:(num → real). x(j)"),
							b.TermAs[Fun[point, Real]]("λx:(num → real). polynomial_value(real_ring, f, x)")),
						Where(
							continuous.Eq,
							"f",
							b.TermAs[Fun[point, Real]]("λx:(num → real). x(j) * polynomial_value(real_ring, f, x)"))))
				b.Show(
					"and the polynomials are closed under products",
					BySets(
						continuousDef,
						variableIn,
						parts[1],
						product,
						real_ring.CommRingOn,
						polynomial_algebra.PolynomialAlgebraMulIn.At(ring, variables, variable, f)))
			}))
		covered := a.Have(
			"so every polynomial below n lies in C, by induction on the polynomials",
			"polynomial_algebra(real_ring, {i:num | i < n}) ⊆ C",
			By(
				real_ring.CommRingOn,
				constantsIn,
				sumsIn,
				productsIn,
				polynomial_algebra.PolynomialInduction.At(ring, variables, continuousPolynomials)))
		a.Show(
			"and p is one of them",
			BySets(pIn, covered, continuousDef))
	}),
})}

// PolynomialNearby — a polynomial below n is ε-δ continuous at every point of
// ℝⁿ: its continuity, read between the metric topologies of ℝⁿ and of the
// line.
var PolynomialNearby = polynomialNearbyThm{family.Add(registry.ProofEntry{
	Name: "PolynomialNearby",
	Key:  "prop_64d0df932f1511d8",
	Build: family.Theorem(Statement{
		Binders: "∀n:num. ∀p:((num → num) → real). ∀x:(num → real). ∀ε:real.",
		Hypotheses: []string{
			"p ∈ polynomial_algebra(real_ring, {i:num | i < n})",
			"vec⟨n⟩(x)",
			"&0 < ε",
		},
		Conclusion: "∃δ:real. " +
			"    &0 < δ ∧ " +
			"    (∀y:(num → real). " +
			"        vec⟨n⟩(y) ∧ dist⟨n⟩(x, y) < δ ⇒ " +
			"        dist(polynomial_value(real_ring, p, x), polynomial_value(real_ring, p, y)) < ε)",
	}, func(
		a *Argument,
		n *Expr[Nat],
		p *Expr[Fun[Fun[Nat, Nat], Real]],
		x *Expr[Fun[Nat, Real]],
		ε *Expr[Real],
		given Fact,
	) {
		continuity := a.Have(
			"p is continuous between the metric topologies of ℝⁿ and of the line",
			"continuous_map(metric_topology({u:num → real | vec⟨n⟩(u)}, vec_dist⟨n⟩), "+
				"    metric_topology(𝕌, real_dist), "+
				"    λx:(num → real). polynomial_value(real_ring, p, x))",
			By(
				given,
				PolynomialContinuous.At(n, p),
				euclidean_topology.EuclideanTopologyDef,
				real_topology.RealTopologyMetric))
		a.Show(
			"which is its ε-δ reading",
			By(given, continuity, metric_space.ContinuousMapIff, real_topology.RealMetric))
	}),
})}

// PolynomialMapContinuous — a normalized multivariate real polynomial map is
// continuous: the map reads P(i) at the coordinates below n and vanishes
// from n on, so it takes values in ℝⁿ and its coordinate i below n is the
// value map of P(i), continuous by PolynomialContinuous; a map into ℝⁿ
// with continuous coordinates is continuous
// (euclidean_topology.ContinuousIffCoordinates).
var PolynomialMapContinuous = polynomialMapContinuousThm{family.Add(registry.ProofEntry{
	Name: "PolynomialMapContinuous",
	Key:  "prop_37cc8339c8168ba7",
	Build: family.Theorem(Statement{
		Binders: "∀n:num. ∀P:(num → (num → num) → real).",
		Hypotheses: []string{
			"∀j:num. j < n ⇒ P(j) ∈ polynomial_algebra(real_ring, {i:num | i < n})",
		},
		Conclusion: "continuous_map(euclidean_topology(n), " +
			"    euclidean_topology(n), " +
			"    polynomial_map(real_ring, n, P))",
	}, func(a *Argument, n *Expr[Nat], P *Arrow[Nat, Fun[Fun[Nat, Nat], Real]], polynomials Fact) {
		type point = Fun[Nat, Real]
		space := a.TermAs[Set[Set[point]]]("euclidean_topology(n)")
		coordinates := a.Have(
			"the coordinates of the map are the polynomials below n and zero from n on",
			"∀x:(num → real). ∀i:num. "+
				"    polynomial_map(real_ring, n, P, x, i) = COND(i < n, polynomial_value(real_ring, P(i), x), &0)",
			By(polynomial_encoding.PolynomialMapDef))
		padded := a.Have(
			"the map takes its values in ℝⁿ",
			"∀x:(num → real). vec⟨n⟩(polynomial_map(real_ring, n, P, x))",
			By(coordinates, vec_space.VecDef, nat_order.NotLessThan))
		coordinatewise := a.Have(
			"its coordinate i below n is the value map of P(i), which is continuous",
			Statement{
				Binders: "∀i:num.",
				Hypotheses: []string{
					"i < n",
				},
				Conclusion: "continuous_map(euclidean_topology(n), " +
					"    real_topology, " +
					"    λx:(num → real). polynomial_map(real_ring, n, P, x, i))",
			},
			Derive(func(b *Argument) {
				i := b.FixAs[Nat]("i")
				below := b.Assume()
				agree := b.Have(
					"the coordinate i of the map is the value of P(i)",
					"∀x:(num → real). polynomial_value(real_ring, P(i), x) = polynomial_map(real_ring, n, P, x, i)",
					By(coordinates, below))
				b.Show(
					"so it is continuous with the value map of P(i)",
					By(
						agree,
						polynomials.At(i),
						below,
						PolynomialContinuous.At(n, P.Apply(i)),
						Where(
							continuous.Eq,
							"g",
							b.TermAs[Fun[point, Real]]("λx:(num → real). polynomial_map(real_ring, n, P, x, i)"))))
			}))
		a.Show(
			"so the map is continuous, coordinate by coordinate",
			By(
				padded,
				coordinatewise,
				euclidean_topology.EuclideanTopology.At(n),
				euclidean_topology.ContinuousIffCoordinates.At(
					n, space, a.TermAs[Fun2[point, Nat, Real]]("polynomial_map(real_ring, n, P)"))))
	}),
})}

// ---------------------------------------------------------------------------
// Compactness and extrema
// ---------------------------------------------------------------------------

// BoxAppendImage — the box of bound M in ℝⁿ⁺¹ is the image of the box in
// ℝⁿ times ⟦-M, M⟧ under appending a coordinate: a point of the image
// appends a coordinate in ⟦-M, M⟧ to a point of the box, and a point of the
// box is its truncation at n with its coordinate n appended.
var BoxAppendImage = boxAppendImageThm{family.Add(registry.ProofEntry{
	Name: "BoxAppendImage",
	Key:  "prop_bc496b2ec3b26f1",
	Build: family.Theorem(
		"∀n:num. ∀M:real. "+
			"    «box»(n + 1, M) = "+
			"    image(λp:prod(num → real, real). «append»(fst(p), snd(p)), set_cross(«box»(n, M), ⟦-M, M⟧))",
		func(a *Argument, n *Expr[Nat], M *Expr[Real]) {
			type point = Fun[Nat, Real]
			type pair = Prod[point, Real]
			rectangle := a.TermAs[Set[pair]]("set_cross(«box»(n, M), ⟦-M, M⟧)")
			appendMap := a.TermAs[Fun[pair, point]]("λp:prod(num → real, real). «append»(fst(p), snd(p))")
			_, imageDef := a.LetAs[Set[point]](
				"K",
				"image(λp:prod(num → real, real). «append»(fst(p), snd(p)), set_cross(«box»(n, M), ⟦-M, M⟧))")
			members := a.Have(
				"K is the box of bound M in ℝⁿ⁺¹",
				"∀z:(num → real). z ∈ K ⇔ vec⟨n + 1⟩(z) ∧ (∀j:num. j < n + 1 ⇒ -M ≤ z(j) ∧ z(j) ≤ M)",
				Derive(func(b *Argument) {
					z := b.FixAs[point]("z")
					b.Iff()
					b.Forward(
						"a point of K appends a coordinate in ⟦-M, M⟧ to a point of the box",
						func(c *Argument, inK Fact) {
							_, preimage := c.ObtainAs[pair](
								"z is the image of a pair p of the rectangle",
								"∃p:prod(num → real, real). z = «append»(fst(p), snd(p)) ∧ p ∈ set_cross(«box»(n, M), ⟦-M, M⟧)",
								By(inK, imageDef, set_basic.InImage.At(appendMap, rectangle, z)))
							parts := c.Conjuncts(
								c.Have(
									"z appends snd(p) to fst(p), an n-vector bounded by M, and snd(p) lies in ⟦-M, M⟧",
									"z = «append»(fst(p), snd(p)) ∧ "+
										"vec⟨n⟩(fst(p)) ∧ "+
										"(∀j:num. j < n ⇒ -M ≤ fst(p)(j) ∧ fst(p)(j) ≤ M) ∧ "+
										"-M ≤ snd(p) ∧ "+
										"snd(p) ≤ M",
									By(preimage, set_product.InCrossProjections, RealRingTuple)),
								"z appends snd(p) to fst(p)",
								"fst(p) is an n-vector",
								"fst(p) is bounded by M",
								"snd(p) is at least -M",
								"snd(p) is at most M")
							bounded := c.Have(
								"every coordinate of the appended tuple below n + 1 lies in ⟦-M, M⟧",
								"∀j:num. j < n + 1 ⇒ -M ≤ COND(j = n, snd(p), fst(p)(j)) ∧ COND(j = n, snd(p), fst(p)(j)) ≤ M",
								Derive(func(d *Argument) {
									j := d.FixAs[Nat]("j")
									below := d.Assume()
									d.Cases(d.Term("j = n"))
									d.When(
										"at n it is snd(p)",
										func(e *Argument, last Fact) {
											e.Show(
												"in ⟦-M, M⟧",
												ByArith(last, parts[3], parts[4]))
										})
									d.Otherwise(
										"below n it is fst(p)(j)",
										func(e *Argument, earlier Fact) {
											e.Show(
												"in ⟦-M, M⟧",
												ByArith(earlier, below, parts[2].At(j)))
										})
								}))
							c.Show(
								"so z is an (n + 1)-vector bounded by M",
								parts[0].Rw(),
								By(
									bounded,
									parts[1],
									euclidean_topology.AppendCoordinateVec.At(
										proof.Inhabit(c.VecAt[Real](n, "fst(p)"), parts[1]), c.TermAs[Real]("snd(p)"))))
						})
					b.Backward(
						"a point of the box is its truncation at n with its coordinate n appended",
						func(c *Argument, inBox Fact) {
							given := c.Conjuncts(
								inBox,
								"z is an (n + 1)-vector",
								"z is bounded by M")
							short := c.Have(
								"the truncation of z at n vanishes from n on: at n by its definition, past n as z does",
								"vec⟨n⟩(λi:num. COND(i = n, &0, z(i)))",
								Derive(func(d *Argument) {
									long := d.Unfolded(given[0], vec_space.VecDef)
									d.Do(Unfold(vec_space.VecDef))
									i := d.FixAs[Nat]("i")
									past := d.Assume()
									d.Cases(d.Term("i = n"))
									d.When(
										"at n the truncation is 0",
										func(e *Argument, at Fact) {
											e.Show(
												"by its definition",
												ByArith(at))
										})
									d.Otherwise(
										"past n it is z, which vanishes from n + 1 on",
										func(e *Argument, beyond Fact) {
											e.Show(
												"as z does",
												ByArith(beyond, past, long.At(i)))
										})
								}))
							inside := c.Have(
								"the coordinates of the truncation below n are those of z",
								"∀j:num. j < n ⇒ -M ≤ COND(j = n, &0, z(j)) ∧ COND(j = n, &0, z(j)) ≤ M",
								c.ForEach(func(j *Expr[Nat]) Action { return ByArith(given[1].At(j)) }))
							truncation := c.Have(
								"so the truncation of z at n is an n-vector bounded by M, and z(n) lies in ⟦-M, M⟧",
								"vec⟨n⟩(λi:num. COND(i = n, &0, z(i))) ∧ "+
									"(∀j:num. j < n ⇒ -M ≤ COND(j = n, &0, z(j)) ∧ COND(j = n, &0, z(j)) ≤ M) ∧ "+
									"-M ≤ z(n) ∧ "+
									"z(n) ≤ M",
								ByArith(short, inside, given[1].At(n)))
							recovered := c.Have(
								"z is its truncation with z(n) appended",
								"z = (λi:num. COND(i = n, z(n), COND(i = n, &0, z(i))))",
								By(Normalized, given[0]))
							pairIn := c.Have(
								"the truncation and z(n) form a pair of the rectangle",
								"(λi:num. COND(i = n, &0, z(i)), z(n)) ∈ set_cross(«box»(n, M), ⟦-M, M⟧)",
								BySets(truncation, set_product.InCross, RealRingTuple))
							preimage := c.Have(
								"z is the image of that pair",
								"∃p:prod(num → real, real). z = «append»(fst(p), snd(p)) ∧ p ∈ set_cross(«box»(n, M), ⟦-M, M⟧)",
								Derive(func(d *Argument) {
									d.Take(d.TermAs[pair]("(λi:num. COND(i = n, &0, z(i)), z(n))"))
									d.Show(
										"its parts are the truncation and z(n)",
										Simp(Fwd(pairs.Fst), Fwd(pairs.Snd)),
										By(recovered, pairIn))
								}))
							c.Show(
								"so z lies in K",
								By(preimage, imageDef, set_basic.InImage.At(appendMap, rectangle, z)))
						})
				}))
			a.Show(
				"so the box of bound M in ℝⁿ⁺¹ is K",
				BySets(members, At(RealRingTuple, a.TermAs[Nat]("n + 1"))))
		}),
})}

// BoxCompact — every closed real coordinate box is compact. By induction on
// n: in dimension 0 the box is the zero tuple, the image of a point of the
// line; the box in ℝⁿ⁺¹ is the image of the box in ℝⁿ times ⟦-M, M⟧ under
// the continuous map appending a coordinate (BoxAppendImage), and a product
// of compact sets is compact.
var BoxCompact = boxCompactThm{family.Add(registry.ProofEntry{
	Name: "BoxCompact",
	Key:  "prop_2ac039437ef1a92d",
	Reading: "A negative bound gives the empty box only in positive " +
		"dimension. At dimension zero the box is always the singleton zero tuple.",
	Build: family.Theorem(
		"∀n:num. ∀M:real. compact_in(euclidean_topology(n), «box»(n, M))",
		func(a *Argument) {
			type point = Fun[Nat, Real]
			type pair = Prod[point, Real]
			a.Induct("n")
			a.Base(
				"in dimension 0 the box is the zero tuple, the image of a point of the line",
				func(b *Argument) {
					b.FixAs[Real]("M")
					zero := b.TermAs[point]("λi:num. &0")
					line := b.TermAs[Set[Set[Real]]]("real_topology")
					space := b.TermAs[Set[Set[point]]]("euclidean_topology(0)")
					tuples := b.Have(
						"the only tuple of length 0 is zero",
						"∀x:(num → real). ring_tuple(real_ring, 0, x) ⇔ x = (λi:num. &0)",
						By(RealRingTuple, vec_space.VecDef, nat_order.ZeroLessEq))
					image := b.Have(
						"the constant map at zero takes the point 0 to zero",
						"∀x:(num → real). x ∈ image(λt:real. λi:num. &0, ⟦&0, &0⟧) ⇔ x = (λi:num. &0)",
						BySets(real_order_ring.LessEqRefl))
					box := b.Have(
						"so the box is that image",
						"{x:(num → real) | ring_tuple(real_ring, 0, x) ∧ (∀j:num. j < 0 ⇒ -M ≤ x(j) ∧ x(j) ≤ M)} = "+
							"image(λt:real. λi:num. &0, ⟦&0, &0⟧)",
						BySets(image, tuples, nat_order.LessThanZeroClause))
					pointOf := b.Have(
						"zero is the point of ℝ⁰",
						"(λi:num. &0) ∈ ⋃euclidean_topology(0)",
						BySets(euclidean_topology.EuclideanSpace.At(b.TermAs[Nat]("0")), vec_space.VecDef))
					constant := b.Have(
						"a constant map is continuous",
						"continuous_map(real_topology, euclidean_topology(0), λt:real. λi:num. &0)",
						By(pointOf, continuous.Constant.At(line, space, zero), real_topology.RealTopology))
					b.Show(
						"and the continuous image of the compact interval ⟦0, 0⟧ is compact",
						box.Rw(),
						By(
							constant,
							continuous.ImageCompact.At(
								line, space, b.TermAs[Fun[Real, point]]("λt:real. λi:num. &0"), b.TermAs[Set[Real]]("⟦&0, &0⟧")),
							real_topology.ClosedIntervalCompact.At(b.TermAs[Real]("&0"), b.TermAs[Real]("&0"))))
				})
			a.Step(
				"the box in ℝⁿ⁺¹ is the image of the box in ℝⁿ times ⟦-M, M⟧ under appending a coordinate",
				func(b *Argument, ih Fact) {
					n := b.TermAs[Nat]("n")
					M := b.FixAs[Real]("M")
					space := b.TermAs[Set[Set[point]]]("euclidean_topology(n)")
					line := b.TermAs[Set[Set[Real]]]("real_topology")
					box := b.TermAs[Set[point]]("«box»(n, M)")
					interval := b.TermAs[Set[Real]]("⟦-M, M⟧")
					rectangle := b.TermAs[Set[pair]]("set_cross(«box»(n, M), ⟦-M, M⟧)")
					appendMap := b.TermAs[Fun[pair, point]]("λp:prod(num → real, real). «append»(fst(p), snd(p))")
					compactRectangle := b.Have(
						"the box in ℝⁿ times ⟦-M, M⟧ is compact in the product",
						"compact_in(product_topology(euclidean_topology(n), real_topology), "+
							"    set_cross(«box»(n, M), ⟦-M, M⟧))",
						By(
							ih.At(M),
							product_topology.CompactProduct.At(space, line, box, interval),
							euclidean_topology.EuclideanTopology.At(n),
							real_topology.RealTopology,
							real_topology.ClosedIntervalCompact.At(b.TermAs[Real]("-M"), M)))
					_, imageDef := b.LetAs[Set[point]](
						"K",
						"image(λp:prod(num → real, real). «append»(fst(p), snd(p)), set_cross(«box»(n, M), ⟦-M, M⟧))")
					compactImage := b.Have(
						"so is its image K under appending the coordinate",
						"compact_in(euclidean_topology(n + 1), K)",
						By(
							imageDef,
							compactRectangle,
							euclidean_topology.AppendCoordinateContinuous.At(n),
							continuous.ImageCompact.At(
								b.TermAs[Set[Set[pair]]]("product_topology(euclidean_topology(n), real_topology)"),
								b.TermAs[Set[Set[point]]]("euclidean_topology(n + 1)"),
								appendMap,
								rectangle)))
					boxIsImage := b.Have(
						"the box of bound M in ℝⁿ⁺¹ is K",
						"«box»(n + 1, M) = K",
						imageDef.Rw(),
						Cite(BoxAppendImage, n, M))
					b.Show(
						"and K is compact",
						Simp(Fwd(nat_arith.Add1)),
						boxIsImage.Rw(),
						By(compactImage))
				})
		}),
})}

// ClosedConstraintsCompact — a bounded set cut out by closed polynomial
// constraints is compact over the reals. About a point of ℝⁿ outside the set
// some g(j) is negative or some h(j) nonzero, and by continuity stays so on a
// ball, which then misses the set: the set is closed, and it lies in the
// compact box the bound M gives.
var ClosedConstraintsCompact = closedConstraintsCompactThm{family.Add(registry.ProofEntry{
	Name: "ClosedConstraintsCompact",
	Key:  "prop_aad54c86fae46a06",
	Build: family.Theorem(Statement{
		Binders: "∀n s t:num. ∀g h:(num → (num → num) → real). ∀M:real.",
		Hypotheses: []string{
			"∀j:num. j < s ⇒ g(j) ∈ polynomial_algebra(real_ring, {i:num | i < n})",
			"∀j:num. j < t ⇒ h(j) ∈ polynomial_algebra(real_ring, {i:num | i < n})",
			"polynomial_box_bound(real_field_ops, " +
				"    real_lt, " +
				"    n, " +
				"    polynomial_constraint_set(real_field_ops, real_lt, n, s, t, g, h), " +
				"    M)",
		},
		Conclusion: "compact_in(euclidean_topology(n), " +
			"    polynomial_constraint_set(real_field_ops, real_lt, n, s, t, g, h))",
	}, func(
		a *Argument,
		n, s, t *Expr[Nat],
		g, h *Arrow[Nat, Fun[Fun[Nat, Nat], Real]],
		M *Expr[Real],
		gIn, hIn, bounded Fact,
	) {
		type point = Fun[Nat, Real]
		vectors := a.TermAs[Set[point]]("{u:num → real | vec⟨n⟩(u)}")
		constraints, constraintsDef := a.LetAs[Set[point]](
			"C", "polynomial_constraint_set(real_field_ops, real_lt, n, s, t, g, h)")
		members := a.Have(
			"a point lies in C when it is an n-vector at which "+
				"every g(j) is nonnegative and every h(j) vanishes",
			"∀x:(num → real). "+
				"    x ∈ C ⇔ "+
				"    vec⟨n⟩(x) ∧ "+
				"    (∀j:num. j < s ⇒ &0 ≤ polynomial_value(real_ring, g(j), x)) ∧ "+
				"    (∀j:num. j < t ⇒ polynomial_value(real_ring, h(j), x) = &0)",
			BySets(
				// two passes: field_ring(real_field_ops) is named real_ring before
				// real_field_ops is unfolded, which would leave no field_ring of it to name
				a.Simplified(
					a.Simplified(
						constraintsDef,
						Fwd(semialgebraic_properties.ConstraintSetDef),
						Fwd(real_field.RealFieldRing)),
					Fwd(real_ordered_instance.RealOrderedLe),
					Fwd(real_field.RealFieldOpsDef),
					Fwd(RealRingTuple))))
		boxed := a.Have(
			"the bound M confines C to the box of bound M",
			"∀x:(num → real). x ∈ C ⇒ (∀j:num. j < n ⇒ -M ≤ x(j) ∧ x(j) ≤ M)",
			By(a.Simplified(
				bounded,
				Fwd(semialgebraic_properties.BoundedSetDef),
				Fwd(real_ordered_instance.RealOrderedLe),
				Fwd(real_field.RealFieldOpsDef))))
		outsideOpen := a.Have(
			"about a point of ℝⁿ outside C some ball misses C",
			Statement{
				Binders: "∀x:(num → real).",
				Hypotheses: []string{
					"vec⟨n⟩(x)",
					"x ∉ C",
				},
				Conclusion: "∃r:real. &0 < r ∧ (∀y:(num → real). vec⟨n⟩(y) ∧ dist⟨n⟩(x, y) < r ⇒ y ∉ C)",
			},
			Derive(func(b *Argument) {
				x := b.FixAs[point]("x")
				outside := b.Conjuncts(
					b.Assume(),
					"x is an n-vector",
					"x lies outside C")
				centre := proof.Inhabit(b.VecAt[Real](n, "x"), outside[0])
				b.Cases(b.Term("∀j:num. j < s ⇒ &0 ≤ polynomial_value(real_ring, g(j), x)"))
				b.When(
					"every inequality holds at x, so some equation fails there",
					func(c *Argument, inequalities Fact) {
						j, failing := c.ObtainAs[Nat](
							"some h(j) with j < t does not vanish at x",
							"∃j:num. j < t ∧ polynomial_value(real_ring, h(j), x) ≠ &0",
							By(members.At(x), inequalities, outside[0], outside[1]))
						parts := c.Conjuncts(
							failing,
							"j is below t",
							"h(j) does not vanish at x")
						value := c.TermAs[Real]("polynomial_value(real_ring, h(j), x)")
						δ, radius := c.ObtainAs[Real](
							"within some δ of x the value of h(j) stays closer to h(j)(x) than its size",
							"∃δ:real. "+
								"    &0 < δ ∧ "+
								"    (∀y:(num → real). "+
								"        vec⟨n⟩(y) ∧ dist⟨n⟩(x, y) < δ ⇒ "+
								"        dist(polynomial_value(real_ring, h(j), x), polynomial_value(real_ring, h(j), y)) < "+
								"        |polynomial_value(real_ring, h(j), x)|)",
							By(
								hIn.At(j),
								parts[0],
								parts[1],
								PolynomialNearby.At(h.Apply(j), centre, c.TermAs[Real]("|polynomial_value(real_ring, h(j), x)|")),
								real_sgn_abs.AbsPosIffNonzero.At(value)))
						near := c.Conjuncts(
							radius,
							"δ is positive",
							"h(j) stays close within δ")
						c.Take(δ)
						stays := c.Have(
							"so h(j) does not vanish within δ of x",
							"∀y:(num → real). vec⟨n⟩(y) ∧ dist⟨n⟩(x, y) < δ ⇒ polynomial_value(real_ring, h(j), y) ≠ &0",
							Derive(func(e *Argument) {
								y := e.FixAs[point]("y")
								nearby := e.Assume()
								e.Show(
									"a value closer to h(j)(x) than its size is not 0",
									By(
										near[1].At(y),
										nearby,
										real_sgn_abs.RealDistDef,
										real_sgn_abs.NonzeroNear.At(value, e.TermAs[Real]("polynomial_value(real_ring, h(j), y)"))))
							}))
						c.Show(
							"and those points are not in C",
							By(members, stays, parts[0], near[0]))
					})
				b.Otherwise(
					"some inequality fails at x",
					func(c *Argument, failingInequality Fact) {
						j, failing := c.ObtainAs[Nat](
							"some g(j) with j < s is negative at x",
							"∃j:num. j < s ∧ polynomial_value(real_ring, g(j), x) < &0",
							By(failingInequality, real_order_ring.NotLessEq))
						parts := c.Conjuncts(
							failing,
							"j is below s",
							"g(j) is negative at x")
						value := c.TermAs[Real]("polynomial_value(real_ring, g(j), x)")
						δ, radius := c.ObtainAs[Real](
							"within some δ of x the value of g(j) stays within -g(j)(x) of g(j)(x)",
							"∃δ:real. "+
								"    &0 < δ ∧ "+
								"    (∀y:(num → real). "+
								"        vec⟨n⟩(y) ∧ dist⟨n⟩(x, y) < δ ⇒ "+
								"        dist(polynomial_value(real_ring, g(j), x), polynomial_value(real_ring, g(j), y)) < "+
								"        -polynomial_value(real_ring, g(j), x))",
							ByArith(
								gIn.At(j),
								parts[0],
								parts[1],
								PolynomialNearby.At(g.Apply(j), centre, c.TermAs[Real]("-polynomial_value(real_ring, g(j), x)"))))
						near := c.Conjuncts(
							radius,
							"δ is positive",
							"g(j) stays close within δ")
						c.Take(δ)
						stays := c.Have(
							"so g(j) stays negative within δ of x",
							"∀y:(num → real). vec⟨n⟩(y) ∧ dist⟨n⟩(x, y) < δ ⇒ polynomial_value(real_ring, g(j), y) < &0",
							Derive(func(e *Argument) {
								y := e.FixAs[point]("y")
								nearby := e.Assume()
								other := e.TermAs[Real]("polynomial_value(real_ring, g(j), y)")
								e.Show(
									"a value within -g(j)(x) of the negative g(j)(x) is negative",
									ByArith(
										near[1].At(y),
										nearby,
										parts[1],
										real_sgn_abs.RealDistDef.At(value, other),
										real_sgn_abs.AbsBetween.At(other, value, e.TermAs[Real]("-polynomial_value(real_ring, g(j), x)"))))
							}))
						c.Show(
							"and those points are not in C",
							By(members, stays, parts[0], near[0], real_order_ring.NotLessEq))
					})
			}))
		inSpace := a.Have(
			"C lies in ℝⁿ",
			"C ⊆ {u:num → real | vec⟨n⟩(u)}",
			BySets(members))
		balls := a.Have(
			"about each point of ℝⁿ outside C a ball misses C",
			Statement{
				Binders: "∀x:(num → real).",
				Hypotheses: []string{
					"x ∈ {u:num → real | vec⟨n⟩(u)}",
					"x ∉ C",
				},
				Conclusion: "∃r:real. &0 < r ∧ ball({u:num → real | vec⟨n⟩(u)}, vec_dist⟨n⟩, x, r) ∩ C = ∅",
			},
			Derive(func(b *Argument) {
				x := b.FixAs[point]("x")
				outside := b.Assume()
				r, radius := b.ObtainAs[Real](
					"a radius r about x missing C",
					"∃r:real. &0 < r ∧ (∀y:(num → real). vec⟨n⟩(y) ∧ dist⟨n⟩(x, y) < r ⇒ y ∉ C)",
					By(outsideOpen.At(x), outside))
				b.Take(r)
				b.Show(
					"the ball of radius r misses C",
					BySets(radius, metric_space.BallDef))
			}))
		closed := a.Have(
			"so C is closed in ℝⁿ",
			"closed_in(euclidean_topology(n), C)",
			Simp(Fwd(euclidean_topology.EuclideanTopologyDef)),
			By(
				inSpace,
				balls,
				metric_space.ClosedIff.At(vectors, a.TermAs[Fun2[point, point, Real]]("vec_dist⟨n⟩"), constraints)))
		box := a.TermAs[Set[point]]("«box»(n, M)")
		insideBox := a.Have(
			"and it lies in the box of bound M",
			"C ⊆ «box»(n, M)",
			BySets(members, boxed, RealRingTuple))
		a.Show(
			"a closed subset of a compact box is compact",
			By(
				closed,
				insideBox,
				compact.ClosedSubsetCompact.At(
					a.TermAs[Set[Set[point]]]("euclidean_topology(n)"), box, constraints),
				BoxCompact.At(n, M)))
	}),
})}

// CompactPolynomialMinimum — a real polynomial attains its minimum on a
// nonempty compact set: its value map is a continuous real function, and a
// continuous real function attains a least value on a nonempty compact set.
var CompactPolynomialMinimum = compactPolynomialMinimumThm{family.Add(registry.ProofEntry{
	Name: "CompactPolynomialMinimum",
	Key:  "prop_29cf91e48ca0c179",
	Build: family.Theorem(Statement{
		Binders: "∀n:num. ∀S:set(num → real). ∀p:((num → num) → real).",
		Hypotheses: []string{
			"S ≠ ∅",
			"compact_in(euclidean_topology(n), S)",
			"p ∈ polynomial_algebra(real_ring, {i:num | i < n})",
		},
		Conclusion: "∃x:(num → real). " +
			"    x ∈ S ∧ " +
			"    (∀y:(num → real). " +
			"        y ∈ S ⇒ polynomial_value(real_ring, p, x) ≤ polynomial_value(real_ring, p, y))",
	}, func(
		a *Argument,
		n *Expr[Nat],
		S *Expr[Set[Fun[Nat, Real]]],
		p *Expr[Fun[Fun[Nat, Nat], Real]],
		nonempty, compactS, pIn Fact,
	) {
		a.Show(
			"the value map of p is continuous on ℝⁿ",
			By(
				nonempty,
				compactS,
				pIn,
				PolynomialContinuous.At(n, p),
				real_valued.ContinuousCompactMinimum.At(
					a.TermAs[Set[Set[Fun[Nat, Real]]]]("euclidean_topology(n)"),
					a.TermAs[Fun[Fun[Nat, Real], Real]]("λx:(num → real). polynomial_value(real_ring, p, x)"),
					S)))
	}),
})}

// ---------------------------------------------------------------------------
// The real sources
// ---------------------------------------------------------------------------

// LexicographicSource — the real field satisfies every degree-bounded
// lexicographic minimum statement. The constraint set C is compact, so f
// attains its least value on C at some x₀; the points of C where f takes
// that value form a closed part L of C, compact again, and q attains its
// least value on L at the minimizer sought.
var LexicographicSource = lexicographicSourceThm{family.Add(registry.ProofEntry{
	Name: "LexicographicSource",
	Key:  "prop_f1c796b7f0e09f63",
	Build: family.Theorem(Statement{
		Binders:    "∀n s t d:num.",
		Conclusion: "lexicographic_minimum_property(real_field_ops, real_lt, n, s, t, d)",
		Abbrev: Abbrev{
			{Name: "levelSet", Text: "preimage_on(⋃euclidean_topology(n), " +
				"    λx:(num → real). polynomial_value(real_ring, f, x), " +
				"    ⟦polynomial_value(real_ring, f, x₀), polynomial_value(real_ring, f, x₀)⟧)"},
		},
	},
		func(a *Argument, n, s, t, d *Expr[Nat]) {
			type point = Fun[Nat, Real]
			type poly = Fun[Fun[Nat, Nat], Real]
			a.Show(
				"for bounded polynomials f, q, g, h and a box M about the nonempty constraint set C",
				Unfold(semialgebraic_properties.LexPropertyDef),
				Derive(func(b *Argument) {
					f := b.FixAs[poly]("f")
					q := b.FixAs[poly]("q")
					g := b.FixAs[Fun[Nat, poly]]("g")
					h := b.FixAs[Fun[Nat, poly]]("h")
					M := b.FixAs[Real]("M")
					parts := b.Conjuncts(
						b.Assume(),
						"f is bounded by d",
						"q is bounded by d",
						"each g(j) is bounded by d",
						"each h(j) is bounded by d",
						"the constraint set is nonempty",
						"the constraint set lies in the box of bound M")
					// a degree bound is read at the ring of the real field, which real_field.RealFieldRing names real_ring
					fieldRing := b.TermAs[module_record.RingOps[Real]]("field_ring(real_field_ops)")
					fIn := b.Have(
						"f is a polynomial below n",
						"f ∈ polynomial_algebra(real_ring, {i:num | i < n})",
						By(
							parts[0],
							real_field.RealFieldRing,
							polynomial_encoding.PolynomialBoundDef.At(fieldRing, n, d, f)))
					qIn := b.Have(
						"q is a polynomial below n",
						"q ∈ polynomial_algebra(real_ring, {i:num | i < n})",
						By(
							parts[1],
							real_field.RealFieldRing,
							polynomial_encoding.PolynomialBoundDef.At(fieldRing, n, d, q)))
					gIn := b.Have(
						"so is each g(j)",
						"∀j:num. j < s ⇒ g(j) ∈ polynomial_algebra(real_ring, {i:num | i < n})",
						Derive(func(c *Argument) {
							j := c.FixAs[Nat]("j")
							below := c.Assume()
							c.Show(
								"a polynomial bounded by d",
								By(
									parts[2].At(j),
									below,
									real_field.RealFieldRing,
									polynomial_encoding.PolynomialBoundDef.At(fieldRing, n, d, c.TermAs[poly]("g(j)"))))
						}))
					hIn := b.Have(
						"so is each h(j)",
						"∀j:num. j < t ⇒ h(j) ∈ polynomial_algebra(real_ring, {i:num | i < n})",
						Derive(func(c *Argument) {
							j := c.FixAs[Nat]("j")
							below := c.Assume()
							c.Show(
								"a polynomial bounded by d",
								By(
									parts[3].At(j),
									below,
									real_field.RealFieldRing,
									polynomial_encoding.PolynomialBoundDef.At(fieldRing, n, d, c.TermAs[poly]("h(j)"))))
						}))
					space := b.TermAs[Set[Set[point]]]("euclidean_topology(n)")
					constraints, constraintsDef := b.LetAs[Set[point]](
						"C", "polynomial_constraint_set(real_field_ops, real_lt, n, s, t, g, h)")
					compactC := b.Have(
						"C is compact",
						"compact_in(euclidean_topology(n), C)",
						By(constraintsDef, gIn, hIn, parts[5], ClosedConstraintsCompact.At(n, s, t, g, h, M)))
					x0, least := b.ObtainAs[point](
						"f attains its least value on C at some x₀",
						"∃x₀:(num → real). "+
							"    x₀ ∈ C ∧ "+
							"    (∀y:(num → real). "+
							"        y ∈ C ⇒ polynomial_value(real_ring, f, x₀) ≤ polynomial_value(real_ring, f, y))",
						By(parts[4], compactC, fIn, CompactPolynomialMinimum.At(n, constraints, f)))
					minimum := b.Conjuncts(
						least,
						"x₀ lies in C",
						"f is least on C at x₀")
					value := b.TermAs[Real]("polynomial_value(real_ring, f, x₀)")
					valueMap := b.TermAs[Fun[point, Real]]("λx:(num → real). polynomial_value(real_ring, f, x)")
					levelSet := b.TermAs[Set[point]]("«levelSet»")
					closedLevel := b.Have(
						"the points of ℝⁿ where f takes the value f(x₀) form a closed set",
						"closed_in(euclidean_topology(n), «levelSet»)",
						By(
							fIn,
							PolynomialContinuous.At(n, f),
							continuous.ClosedPreimage.At(space, b.TermAs[Set[Set[Real]]]("real_topology"), valueMap),
							real_topology.ClosedIntervalClosed.At(value, value)))
					level, levelDef := b.LetAs[Set[point]]("L", "C ∩ «levelSet»")
					compactL := b.Have(
						"so the points L of C where f is least form a compact set",
						"compact_in(euclidean_topology(n), L)",
						By(levelDef, compactC, closedLevel, compact.CompactInterClosed.At(space, constraints, levelSet)))
					inSpace := b.Have(
						"C lies in ℝⁿ",
						"C ⊆ ⋃euclidean_topology(n)",
						By(compactC, compact.CompactInDef))
					levelMembers := b.Have(
						"a point lies in L when it lies in C and f takes the value f(x₀) there",
						"∀y:(num → real). "+
							"    y ∈ L ⇔ "+
							"    y ∈ C ∧ "+
							"    polynomial_value(real_ring, f, x₀) ≤ polynomial_value(real_ring, f, y) ∧ "+
							"    polynomial_value(real_ring, f, y) ≤ polynomial_value(real_ring, f, x₀)",
						BySets(levelDef, inSpace))
					x0In := b.Have(
						"x₀ lies in L",
						"x₀ ∈ L",
						By(levelMembers.At(x0), minimum[0], real_order_ring.LessEqRefl.At(value)))
					nonemptyL := b.Have(
						"so L is nonempty",
						"L ≠ ∅",
						BySets(x0In))
					z, best := b.ObtainAs[point](
						"q attains its least value on L at some z",
						"∃z:(num → real). "+
							"    z ∈ L ∧ "+
							"    (∀y:(num → real). "+
							"        y ∈ L ⇒ polynomial_value(real_ring, q, z) ≤ polynomial_value(real_ring, q, y))",
						By(compactL, qIn, nonemptyL, CompactPolynomialMinimum.At(n, level, q)),
						Named("z"))
					optimum := b.Conjuncts(
						best,
						"z lies in L",
						"q is least on L at z")
					atZ := b.Conjuncts(
						b.Have(
							"z lies in C and f takes the value f(x₀) there",
							"z ∈ C ∧ "+
								"polynomial_value(real_ring, f, x₀) ≤ polynomial_value(real_ring, f, z) ∧ "+
								"polynomial_value(real_ring, f, z) ≤ polynomial_value(real_ring, f, x₀)",
							By(levelMembers.At(z), optimum[0])),
						"z lies in C",
						"f(x₀) is at most f(z)",
						"f(z) is at most f(x₀)")
					fLeast := b.Have(
						"so f is least on C at z",
						"∀y:(num → real). y ∈ C ⇒ polynomial_value(real_ring, f, z) ≤ polynomial_value(real_ring, f, y)",
						Derive(func(c *Argument) {
							y := c.FixAs[point]("y")
							inC := c.Assume()
							c.Show(
								"f(z) ≤ f(x₀) ≤ f(y)",
								ByArith(atZ[2], minimum[1].At(y), inC))
						}))
					qLeast := b.Have(
						"and q is least at z among the points of C where f is least",
						Statement{
							Binders: "∀y:(num → real).",
							Hypotheses: []string{
								"y ∈ C",
								"∀z:(num → real). z ∈ C ⇒ polynomial_value(real_ring, f, y) ≤ polynomial_value(real_ring, f, z)",
							},
							Conclusion: "polynomial_value(real_ring, q, z) ≤ polynomial_value(real_ring, q, y)",
						},
						Derive(func(c *Argument) {
							y := c.FixAs[point]("y")
							given := c.Conjuncts(
								c.Assume(),
								"y lies in C",
								"f is least on C at y")
							inL := c.Have(
								"y lies in L",
								"y ∈ L",
								ByArith(levelMembers.At(y), given[0], given[1].At(x0), minimum[0], minimum[1].At(y)))
							c.Show(
								"as q is least on L at z",
								By(optimum[1].At(y), inL))
						}))
					b.Take(z)
					b.Show(
						"z is the lexicographic minimizer",
						Unfold(semialgebraic_properties.LexMinimizerDef),
						Simp(Fwd(real_field.RealFieldRing), Fwd(real_ordered_instance.RealOrderedLe)),
						By(atZ[0], fLeast, qLeast))
				}))
		}),
})}

// BrouwerSource — the real cube has the polynomial fixed-point property in
// every dimension and degree. The carrier cube of ℝ is the unit cube
// (RealCarrierCube), a polynomial map of ℝⁿ is continuous, and so is its
// restriction to the cube; Brouwer's theorem on the cube gives the fixed
// point.
var BrouwerSource = brouwerSourceThm{family.Add(registry.ProofEntry{
	Name: "BrouwerSource",
	Key:  "prop_cb9267487d1d3929",
	Build: family.Theorem(
		"∀n d:num. polynomial_brouwer_property(real_field_ops, real_lt, n, d)",
		func(a *Argument, n, d *Expr[Nat]) {
			type point = Fun[Nat, Real]
			type poly = Fun[Fun[Nat, Nat], Real]
			cube := RealCarrierCube.At(n)
			a.Show(
				"for a polynomial map P of bounded degree carrying the cube into itself",
				Unfold(semialgebraic_properties.BrouwerPropertyDef),
				Derive(func(b *Argument) {
					P := b.FixAs[Fun[Nat, poly]]("P")
					parts := b.Conjuncts(
						b.Assume(),
						"each P(j) is bounded by d",
						"the map carries the cube into itself")
					fieldRing := b.TermAs[module_record.RingOps[Real]]("field_ring(real_field_ops)")
					polynomials := b.Have(
						"each P(j) with j < n is a polynomial below n",
						"∀j:num. j < n ⇒ P(j) ∈ polynomial_algebra(real_ring, {i:num | i < n})",
						Derive(func(c *Argument) {
							j := c.FixAs[Nat]("j")
							below := c.Assume()
							c.Show(
								"a polynomial bounded by d",
								By(
									parts[0].At(j),
									below,
									real_field.RealFieldRing,
									polynomial_encoding.PolynomialBoundDef.At(fieldRing, n, d, c.TermAs[poly]("P(j)"))))
						}))
					space := b.TermAs[Set[Set[point]]]("euclidean_topology(n)")
					polynomialMap := b.TermAs[Fun2[point, Nat, Real]]("polynomial_map(real_ring, n, P)")
					onCube := b.Have(
						"the polynomial map is continuous on the unit cube",
						"continuous_map(subtopology(euclidean_topology(n), unit_cube(n)), "+
							"    euclidean_topology(n), "+
							"    polynomial_map(real_ring, n, P))",
						By(
							polynomials,
							PolynomialMapContinuous.At(n, P),
							continuous.FromSubtopology.At(space, space, polynomialMap, b.TermAs[Set[point]]("unit_cube(n)"))))
					selfMap := b.Have(
						"and carries the unit cube into itself",
						"∀x:(num → real). x ∈ unit_cube(n) ⇒ polynomial_map(real_ring, n, P, x) ∈ unit_cube(n)",
						By(parts[1], cube, real_field.RealFieldRing))
					b.Show(
						"Brouwer's theorem on the cube gives its fixed point",
						By(
							selfMap,
							onCube,
							cube,
							real_field.RealFieldRing,
							euclidean_topology.BrouwerCube.At(n, polynomialMap)))
				}))
		}),
})}

// CubePositiveSource — over the reals, a polynomial of degree at most d positive on the carrier
// cube has a positive lower bound there, in every dimension: the carrier cube of ℝ is the unit
// cube (RealCarrierCube), which is nonempty (euclidean_topology.CubeNonempty) and compact —
// closed in ℝⁿ (euclidean_topology.CubeClosed) and inside the box of bound 1 — so the polynomial
// attains a least value on it, which is positive.
var CubePositiveSource = cubePositiveSourceThm{family.Add(registry.ProofEntry{
	Name: "CubePositiveSource",
	Key:  "prop_d444919a828bcfb6",
	Build: family.Theorem(
		"∀n d:num. cube_positive_bound_property(real_field_ops, real_lt, n, d)",
		func(a *Argument, n, d *Expr[Nat]) {
			type point = Fun[Nat, Real]
			type poly = Fun[Fun[Nat, Nat], Real]
			space := a.TermAs[Set[Set[point]]]("euclidean_topology(n)")
			unitInterval := a.Have(
				"a real in ⟦0, 1⟧ lies in ⟦-1, 1⟧",
				"∀t:real. &0 ≤ t ∧ t ≤ &1 ⇒ -&1 ≤ t ∧ t ≤ &1",
				ByArith())
			insideBox := a.Have(
				"the unit cube lies in the box of bound 1",
				"unit_cube(n) ⊆ «box»(n, &1)",
				BySets(euclidean_topology.UnitCubeDef.At(n), RealRingTuple, unitInterval))
			compactCube := a.Have(
				"a closed subset of a compact box is compact",
				"compact_in(euclidean_topology(n), unit_cube(n))",
				By(
					euclidean_topology.CubeClosed.At(n),
					insideBox,
					compact.ClosedSubsetCompact.At(
						space, a.TermAs[Set[point]]("«box»(n, &1)"), a.TermAs[Set[point]]("unit_cube(n)")),
					BoxCompact.At(n, a.TermAs[Real]("&1"))))
			a.Show(
				"for a polynomial p of degree at most d positive on the cube",
				Unfold(semialgebraic_properties.CubePositiveBoundPropertyDef),
				Derive(func(b *Argument) {
					p := b.FixAs[poly]("p")
					parts := b.Conjuncts(
						b.Assume(),
						"p is bounded by d",
						"p is positive on the cube")
					// a degree bound is read at the ring of the real field, which real_field.RealFieldRing names real_ring
					fieldRing := b.TermAs[module_record.RingOps[Real]]("field_ring(real_field_ops)")
					member := b.Have(
						"p is a polynomial below n",
						"p ∈ polynomial_algebra(real_ring, {i:num | i < n})",
						By(
							parts[0],
							real_field.RealFieldRing,
							polynomial_encoding.PolynomialBoundDef.At(fieldRing, n, d, p)))
					x0, least := b.UnpackAs[point](
						GroupPremises(
							euclidean_topology.CubeNonempty.At(n),
							compactCube,
							member,
							CompactPolynomialMinimum.At(n, b.TermAs[Set[point]]("unit_cube(n)"), p)),
						"x₀")
					positive := b.Simplified(
						parts[1],
						Fwd(RealCarrierCube),
						Fwd(real_field.RealFieldRing),
						Fwd(real_ordered_instance.RealOrderedLe))
					b.Take(b.TermAs[Real]("polynomial_value(real_ring, p, x₀)"))
					b.Show(
						"p's least value on the cube, a real, positive at x₀, and at most each value there",
						Simp(Fwd(RealCarrierCube), Fwd(real_field.RealFieldRing), Fwd(real_ordered_instance.RealOrderedLe)),
						By(least, positive.At(x0), set_basic.InUniv))
				}))
		}),
})}

// IntervalMinimumSource — over the reals, a polynomial in one variable with at most n coefficients
// attains its minimum on every nonempty closed interval, for every n: its evaluation is a real
// polynomial function (real_closed_instance.PolynomialFunctionBridge), continuous on the line and
// so on ⟦a, b⟧, and a function continuous on ⟦a, b⟧ takes a least value there
// (real_continuous.ExtremeValueMin).
var IntervalMinimumSource = intervalMinimumSourceThm{family.Add(registry.ProofEntry{
	Name: "IntervalMinimumSource",
	Key:  "prop_26f53f5ea179e5be",
	Build: family.Theorem(
		"∀n:num. interval_minimum_property(real_field_ops, real_lt, n)",
		func(arg *Argument, n *Expr[Nat]) {
			arg.Show(
				"for a polynomial p with at most n coefficients and an interval ⟦a, b⟧ with a ≤ b",
				Unfold(semialgebraic_properties.IntervalMinimumPropertyDef),
				Derive(func(c *Argument) {
					p := c.FixAs[Fun[Nat, Real]]("p")
					a := c.FixAs[Real]("a")
					b := c.FixAs[Real]("b")
					parts := c.Conjuncts(
						c.Assume(),
						"p is a tuple of n reals",
						"a is a real",
						"b is a real",
						"a is at most b")
					over := c.Have(
						"p is a real polynomial",
						"polynomial_over(𝕌, p)",
						By(
							parts[0],
							real_field.RealFieldRing,
							RealRingTuple,
							polynomial.PolynomialOverDef,
							set_basic.InUniv))
					value := c.TermAs[Fun[Real, Real]]("λx:real. polynomial_eval(p, x)")
					continuity := c.Have(
						"its evaluation, a polynomial function, is continuous on ⟦a, b⟧",
						"real_continuous_on(⟦a, b⟧, λx:real. polynomial_eval(p, x))",
						By(
							over,
							real_closed_instance.PolynomialFunctionBridge.At(p),
							real_continuous.PolynomialFunctionContinuous.At(value),
							real_continuous.ContinuousMapIffPointwise.At(value),
							real_continuous.ContinuousAtOn.At(value, c.TermAs[Set[Real]]("⟦a, b⟧"))))
					c.Show(
						"a function continuous on ⟦a, b⟧ takes a least value there",
						By(
							continuity,
							parts[3],
							real_continuous.ExtremeValueMin.At(value, a, b),
							real_ordered_instance.RealOrderedLe,
							set_basic.InUniv))
				}))
		}),
})}
