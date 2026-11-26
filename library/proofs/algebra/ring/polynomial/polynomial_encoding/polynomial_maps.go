// polynomial_maps.go — the polynomial map of n coordinate polynomials on
// zero-padded n-tuples, its injectivity and surjectivity read on the ring
// tuples, and the tuples it sends into a subring; ring tuples equal by their
// first n coordinates, finitely many over a finite ring, and of length n + 1
// the vectors of the free module on {i | i ≤ n}.

package polynomial_encoding

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/free_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/function_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_algebra_evaluation"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
)

// PolynomialMapDef — the polynomial map has n active coordinates and zero padding.
var PolynomialMapDef = polynomialMapDefThm{family.Define(registry.DefEntry{
	Name:  "PolynomialMapDef",
	Const: "polynomial_map",
	Type:  "ring_ops(A) → num → (num → (num → num) → A) → (num → A) → num → A",
	Key:   "prop_5adf36043017ddca",
	Equations: []string{
		"∀R:ring_ops(A). ∀n:num. ∀P:(num → (num → num) → A). ∀x:(num → A). ∀i:num. " +
			"    polynomial_map(R, n, P, x, i) = COND(i < n, polynomial_value(R, P(i), x), R.zero)",
	},
	Deps: []registry.EntryLike{PolynomialValueDef},
})}

// PolynomialMapInjectiveDef — injectivity is tested on the normalized finite-tuple carrier.
var PolynomialMapInjectiveDef = polynomialMapInjectiveDefThm{family.Define(registry.DefEntry{
	Name:  "PolynomialMapInjectiveDef",
	Const: "polynomial_map_injective",
	Type:  "ring_ops(A) → num → (num → (num → num) → A) → bool",
	Key:   "prop_82f259118af0a336",
	Equations: []string{
		"∀R:ring_ops(A). ∀n:num. ∀P:(num → (num → num) → A). " +
			"    polynomial_map_injective(R, n, P) ⇔ " +
			"    ∀x y:(num → A). " +
			"        ring_tuple(R, n, x) ∧ " +
			"        ring_tuple(R, n, y) ∧ " +
			"        polynomial_map(R, n, P, x) = polynomial_map(R, n, P, y) ⇒ " +
			"        x = y",
	},
	Deps: []registry.EntryLike{PolynomialMapDef, RingTupleDef},
})}

// PolynomialMapSurjectiveDef — every normalized finite tuple is the image of one in the carrier.
var PolynomialMapSurjectiveDef = polynomialMapSurjectiveDefThm{family.Define(registry.DefEntry{
	Name:  "PolynomialMapSurjectiveDef",
	Const: "polynomial_map_surjective",
	Type:  "ring_ops(A) → num → (num → (num → num) → A) → bool",
	Key:   "prop_1789e20b7ce79a23",
	Equations: []string{
		"∀R:ring_ops(A). ∀n:num. ∀P:(num → (num → num) → A). " +
			"    polynomial_map_surjective(R, n, P) ⇔ " +
			"    ∀y:(num → A). " +
			"        ring_tuple(R, n, y) ⇒ ∃x:(num → A). ring_tuple(R, n, x) ∧ polynomial_map(R, n, P, x) = y",
	},
	Deps: []registry.EntryLike{PolynomialMapDef, RingTupleDef},
})}

// PolynomialMapCongruence — a polynomial self-map of n-space, and with it its injectivity and its
// surjectivity on n-tuples, depends only on its first n coordinate polynomials: below n the
// coordinates of the map are their values, and past n it is zero.
var PolynomialMapCongruence = polynomialMapCongruenceThm{family.Add(registry.ProofEntry{
	Name: "PolynomialMapCongruence",
	Key:  "prop_6bbfdca59880e218",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀n:num. ∀P Q:(num → (num → num) → A).",
		Hypotheses: []string{
			"∀j:num. j < n ⇒ P(j) = Q(j)",
		},
		Conclusion: "polynomial_map(R, n, P) = polynomial_map(R, n, Q) ∧ " +
			"(polynomial_map_injective(R, n, P) ⇔ polynomial_map_injective(R, n, Q)) ∧ " +
			"(polynomial_map_surjective(R, n, P) ⇔ polynomial_map_surjective(R, n, Q))",
	},
		func(a *Argument, R *Expr[RingOps[A]], n *Expr[Nat], P, Q *Arrow2[Nat, _Monomial, A], agree Fact) {
			same := a.Have(
				"the two maps agree",
				"polynomial_map(R, n, P) = polynomial_map(R, n, Q)",
				Derive(func(b *Argument) {
					b.Do(Funext())
					b.FixAs[Fun[Nat, A]]("x")
					b.FixAs[Nat]("i")
					b.Show(
						"below n the coordinates are the values of P(i) and Q(i), which agree, and past n both are zero",
						By(agree, PolynomialMapDef))
				}))
			a.Show(
				"injectivity and surjectivity on n-tuples are read off the map",
				Simp(Fwd(PolynomialMapInjectiveDef), Fwd(PolynomialMapSurjectiveDef)),
				same.Rw(),
				Basic())
		}),
})}

// RingTupleEqual — two ring tuples of one length are equal exactly when their first n coordinates
// agree: equal tuples agree everywhere, and tuples agreeing below n agree from n on too, where
// both are padded by the ring zero.
var RingTupleEqual = ringTupleEqualThm{family.Add(registry.ProofEntry{
	Name: "RingTupleEqual",
	Key:  "prop_711e5ed7c672b5b",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀n:num. ∀x y:(num → A).",
		Hypotheses: []string{
			"ring_tuple(R, n, x)",
			"ring_tuple(R, n, y)",
		},
		Conclusion: "x = y ⇔ ∀j:num. j < n ⇒ x(j) = y(j)",
	},
		func(a *Argument, R *Expr[RingOps[A]], n *Expr[Nat], x, y *Arrow[Nat, A], xTuple, yTuple Fact) {
			xPadded := a.Conjuncts(
				a.Unfolded(a.Unfolded(xTuple, RingTupleDef), vec_space.VecDef),
				"x is zero from n on",
				"x is carrier-valued below n")[0]
			yPadded := a.Conjuncts(
				a.Unfolded(a.Unfolded(yTuple, RingTupleDef), vec_space.VecDef),
				"y is zero from n on",
				"y is carrier-valued below n")[0]
			a.Iff()
			a.Forward(
				"equal tuples agree at every coordinate",
				func(b *Argument, same Fact) {
					b.Show(
						"x(j) is y(j)",
						By(Normalized, same))
				})
			a.Backward(
				"tuples agreeing below n agree everywhere",
				func(b *Argument, agree Fact) {
					b.Do(Funext())
					j := b.FixAs[Nat]("j")
					b.Cases(b.Term("j < n"))
					b.When(
						"below n the coordinates agree by hypothesis",
						func(c *Argument, below Fact) {
							c.Show(
								"x(j) is y(j)",
								By(agree, below))
						})
					b.Otherwise(
						"from n on both coordinates are the ring zero",
						func(c *Argument, above Fact) {
							c.Show(
								"x(j) and y(j) are both R.zero",
								By(Normalized, above, nat_order.NotLessThan.At(j, n), xPadded.At(j), yPadded.At(j)))
						})
				})
		}),
})}

// RingTuplesFinite — a ring with finitely many elements has finitely many n-tuples: an n-tuple
// is a map from the indices below n into the carrier, zero at every other index, and a finite
// set of indices with a finite set of values admits finitely many such maps.
var RingTuplesFinite = ringTuplesFiniteThm{family.Add(registry.ProofEntry{
	Name: "RingTuplesFinite",
	Key:  "prop_16e6cc3c6a21f4c",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀n:num.",
		Hypotheses: []string{
			"finite(R.carrier)",
		},
		Conclusion: "finite({x:num → A | ring_tuple(R, n, x)})",
	}, func(a *Argument, R *Expr[RingOps[A]], n *Expr[Nat], finiteCarrier Fact) {
		maps := a.Have(
			"an n-tuple is a map from the indices below n into the carrier, zero at every other index",
			"{x:num → A | ring_tuple(R, n, x)} ⊆ "+
				"{h:num → A | "+
				"    (∀i:num. i ∈ {j:num | j < n} ⇒ h(i) ∈ R.carrier) ∧ "+
				"    (∀i:num. i ∉ {j:num | j < n} ⇒ h(i) = R.zero)}",
			BySets(RingTupleDef, vec_space.VecDef, nat_order.NotLessThan))
		a.Show(
			"finitely many indices and finitely many values admit finitely many such maps",
			By(
				finiteCarrier,
				maps,
				num_segment.FiniteBelowStrict.At(n),
				cardinality.FiniteFunspace.At(
					a.TermAs[Set[Nat]]("{j:num | j < n}"),
					a.TermAs[Set[A]]("R.carrier"),
					a.TermAs[A]("R.zero")),
				finite_set.FiniteSubset))
	}),
})}

// TuplesAsVectors — over a commutative ring R, the tuples of length n + 1
// are the vectors of the free module on {i | i ≤ n}: both are the functions
// with values in R that vanish past n, a tuple having finite support since it
// vanishes off the finite {i | i ≤ n}.
var TuplesAsVectors = tuplesAsVectorsThm{family.Add(registry.ProofEntry{
	Name: "TuplesAsVectors",
	Key:  "prop_269fd88f887f1adf",
	Build: family.Theorem(
		"∀R:comm_ring_on(A). ∀n:num. ∀a:(num → A). "+
			"    ring_tuple(R, n + 1, a) ⇔ a ∈ free_module_record(R, {i:num | i ≤ n}).carrier",
		func(arg *Argument, R comm_ring.CommRingFact[on.R], n *Expr[Nat], a *Arrow[Nat, A]) {
			arg.Do(
				Simp(
					Fwd(RingTupleDef),
					Fwd(vec_space.VecDef),
					Fwd(free_module.FreeModuleRecordDef),
					Fwd(module_record.ModCarrierDef),
					Fwd(function_module.FiniteSuppDef),
					Fwd(function_module.FiniteSupportDef),
					Fwd(functions.FunSupportDef)))
			arg.Iff()
			arg.Forward(
				"a tuple takes its values in R and vanishes off the finite {i | i ≤ n}",
				func(b *Argument, tuple Fact) {
					parts := b.Conjuncts(
						tuple,
						"a vanishes from n + 1 on",
						"below n + 1 its values lie in R")
					offN := b.Have(
						"a vanishes off {i | i ≤ n}",
						"∀x:num. x ∉ {i:num | i ≤ n} ⇒ a(x) = R.zero",
						BySets(parts[0], nat_order.NotLessEq, nat_order.SucLessEqIffLessThan, nat_arith.Add1))
					finiteSupport := b.Have(
						"so its support lies in the finite {i | i ≤ n}",
						"finite({x:num | a(x) ≠ R.zero})",
						BySets(offN, num_segment.FiniteBelow.At(n), finite_set.FiniteSubset))
					values := b.Have(
						"its values lie in R: below n + 1 by hypothesis, and past n it is zero",
						"∀x:num. a(x) ∈ R.carrier",
						b.ForEach(func(i *Expr[Nat]) Action {
							return By(
								Normalized,
								parts[0],
								parts[1],
								comm_ring.ZeroIn.Read(R),
								nat_order.NotLessThan.At(i, b.TermAs[Nat]("n + 1")))
						}))
					b.Show(
						"a is a vector of the free module",
						By(finiteSupport, values, offN))
				})
			arg.Backward(
				"a vector vanishes off {i | i ≤ n} and takes its values in R",
				func(b *Argument, vector Fact) {
					b.Show(
						"below n + 1 is up to n, and from n + 1 on is past n",
						Simp(Rev(nat_arith.Add1), Fwd(nat_order.LessThanSucIffLessEq), Rev(nat_order.SucLessEqIffLessThan)),
						BySets(vector, nat_order.NotLessEq))
				})
		}),
})}

// PolynomialMapRingTuple — a polynomial map whose coordinates are polynomials in the first n variables
// sends a ring tuple to a ring tuple: below n each coordinate of the image is the value of a
// polynomial over the ring at a carrier-valued point, evaluated along the identity of the ring, so
// it lies in the carrier, and past n the image is zero.
var PolynomialMapRingTuple = polynomialMapRingTupleThm{family.Add(registry.ProofEntry{
	Name: "PolynomialMapRingTuple",
	Key:  "prop_9af810973f69605a",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀n:num. ∀P:(num → (num → num) → A). ∀x:(num → A).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"∀j:num. j < n ⇒ P(j) ∈ polynomial_algebra(R, {i:num | i < n})",
			"ring_tuple(R, n, x)",
		},
		Conclusion: "ring_tuple(R, n, polynomial_map(R, n, P, x))",
	},
		func(a *Argument, R *Expr[RingOps[A]], n *Expr[Nat], P *Arrow2[Nat, _Monomial, A], x *Arrow[Nat, A],
			ring comm_ring.CommRingFact[on.R], polynomials, point Fact) {
			coordinates := a.Conjuncts(
				a.Unfolded(point, RingTupleDef),
				"x is zero from n on",
				"x is carrier-valued below n")[1]
			values := a.Have(
				"below n each coordinate of the image is the value of a polynomial at a carrier-valued point",
				"∀j:num. j < n ⇒ polynomial_value(R, P(j), x) ∈ R.carrier",
				Derive(func(b *Argument) {
					j := b.FixAs[Nat]("j")
					below := b.Assume()
					p := b.TermAs[Fun[_Monomial, A]]("P(j)")
					b.Show(
						"the value is the evaluation along the identity of the ring, which keeps the carrier",
						By(
							below,
							coordinates,
							polynomials.At(j),
							PolynomialValueDef.At(R, p, x),
							ring_homomorphism.RingHomIdentity.Read(ring),
							polynomial_algebra_evaluation.PolynomialAlgebraEvalIn.At(
								R,
								R,
								b.TermAs[Fun[A, A]]("λa:A. a"),
								x,
								b.TermAs[Set[Nat]]("{i:num | i < n}"),
								p)))
				}))
			a.Show(
				"below n the image takes those values, and past n it is zero",
				Unfold(RingTupleDef),
				Unfold(vec_space.VecDef),
				Unfold(PolynomialMapDef),
				By(values, nat_order.NotLessThan))
		}),
})}

// PolynomialMapSubring — a polynomial map whose polynomials have their coefficients in a subring
// sends the n-tuples of the subring to n-tuples of the subring: below n each coordinate of the
// image is a polynomial over the subring evaluated at a point of it, and past n it is zero.
var PolynomialMapSubring = polynomialMapSubringThm{family.Add(registry.ProofEntry{
	Name: "PolynomialMapSubring",
	Key:  "prop_3ff7bb61aa6d5df2",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀T:set(A). ∀n:num. ∀P:(num → (num → num) → A). ∀x:(num → A).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"subring(R, T)",
			"∀j:num. j < n ⇒ P(j) ∈ polynomial_algebra(restrict_ring(R, T), {i:num | i < n})",
			"ring_tuple(restrict_ring(R, T), n, x)",
		},
		Conclusion: "ring_tuple(restrict_ring(R, T), n, polynomial_map(R, n, P, x))",
	}, func(a *Argument, R *Expr[RingOps[A]], T *Expr[Set[A]], n *Expr[Nat],
		P *Arrow2[Nat, _Monomial, A], x *Arrow[Nat, A],
		ring comm_ring.CommRingFact[on.R], subring, polynomials, point Fact) {
		values := a.Have(
			"below n each coordinate of the image is the value "+
				"of a polynomial over T at a point of T, so lies in T",
			"∀j:num. j < n ⇒ polynomial_value(R, P(j), x) ∈ T",
			Derive(func(b *Argument) {
				j := b.FixAs[Nat]("j")
				below := b.Assume()
				p := b.TermAs[Fun[_Monomial, A]]("P(j)")
				identity := b.TermAs[Fun[A, A]]("λa:A. a")
				b.Show(
					"read over T the value is the same, and the inclusion of T into R carries it into T",
					By(
						below,
						subring,
						point,
						polynomials.At(j),
						RingTupleDef,
						ring_homomorphism.SubringInclusionHom.Read(ring).At(T),
						PolynomialValueDef,
						polynomial_algebra_evaluation.PolynomialAlgebraEvalRestrictCoefficients.At(R, T, R, identity, x, p),
						polynomial_algebra_evaluation.PolynomialAlgebraEvalInSubring.At(
							b.TermAs[RingOps[A]]("restrict_ring(R, T)"),
							R,
							identity,
							x,
							b.TermAs[Set[Nat]]("{i:num | i < n}"),
							T,
							p)))
			}))
		a.Show(
			"below n the image takes those values, and past n it is zero",
			Unfold(RingTupleDef),
			Unfold(vec_space.VecDef),
			Unfold(PolynomialMapDef),
			By(values, nat_order.NotLessThan))
	}),
})}
