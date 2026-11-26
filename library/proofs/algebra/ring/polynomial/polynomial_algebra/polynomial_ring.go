// polynomial_ring.go — the polynomials of a set of variables as a commutative
// ring. A coefficient function is a polynomial of S exactly when it is
// nonzero at finitely many monomials, all of them monomials of S, with every
// coefficient in the carrier. The product of two polynomials is the
// convolution of their coefficients over the finitely many monomials below
// each monomial, compared exponent by exponent, or equally the sum over the
// pairs of support monomials adding up to it, so it is nonzero only at those
// sums. The product keeps the polynomials of S, and on coefficient functions
// with values in the carrier it is commutative, associative and distributive.
// Multiplying by a term c·xⁿ shifts the coefficients by n and scales them by
// c: the one polynomial is a unit, a constant scales every coefficient, and
// the generators multiply by adding their monomials. So the polynomials of S
// are a commutative ring, the constants a ring homomorphism into it, each
// variable of S a polynomial of S, and more variables give more polynomials.
// That ring is the ring in every variable restricted to the polynomials of S.
// A polynomial over R restricted to a subset of its carrier is a polynomial
// over R, with the same product, one and constants, so the polynomials over a
// subring include into those over R as a ring homomorphism; more generally,
// carrying the coefficients along a ring homomorphism is a ring homomorphism
// of the polynomial rings, and along an isomorphism an isomorphism. A set
// that holds the constants and is closed under sums and under multiplication
// by the variables of S holds every polynomial of S.

package polynomial_algebra

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/free_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/function_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/iterate/monoidal"
	"github.com/euc-ai/xugo/library/proofs/iterate/nat/nat_sum"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_monus"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/nat_num/peano"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/proofs/sets/set_product"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The ring of polynomials
// ---------------------------------------------------------------------------

// PolynomialAlgebraMember — a coefficient function is a polynomial of S
// exactly when it is nonzero at finitely many monomials, all of them
// monomials of S, with every coefficient in the carrier: the membership
// law of the free module (function_module.FiniteSuppMember) at the
// monomials of S.
var PolynomialAlgebraMember = polynomialAlgebraMemberThm{family.Add(registry.ProofEntry{
	Name: "PolynomialAlgebraMember",
	Key:  "prop_c74da18a8cb94564",
	Build: family.Theorem("∀R:ring_ops(A). ∀S:set(D). ∀f:((D → num) → A). "+
		"    f ∈ polynomial_algebra(R, S) ⇔ "+
		"    finite(fun_support(R.zero, f)) ∧ "+
		"    fun_support(R.zero, f) ⊆ monomials(S) ∧ "+
		"    (∀m:(D → num). f(m) ∈ R.carrier)",
		func(a *Argument, R *Expr[RingOps[A]], S *Expr[Set[D]], f *Arrow[Fun[D, Nat], A]) {
			a.Show(
				"the polynomials of S are the free module on the monomials of S",
				Simp(Fwd(PolynomialAlgebraDef)),
				Cite(function_module.FiniteSuppMember))
		}),
})}

// PolynomialAlgebraMulSupport — a coefficient of a product of two
// coefficient functions valued in the carrier that is not zero sits at a
// finitely supported monomial m and has a term f(m₁) · g(m − m₁), m₁ below
// m, with both factors nonzero: off the finitely supported monomials the
// coefficient is R.zero by definition, and at one of them it is a finite
// sum, which a sum of zeros would make zero.
var PolynomialAlgebraMulSupport = polynomialAlgebraMulSupportThm{family.Add(registry.ProofEntry{
	Name: "PolynomialAlgebraMulSupport",
	Key:  "prop_5339d7c44c999ab2",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀f g:((D → num) → A). ∀m:(D → num).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"∀u:(D → num). f(u) ∈ R.carrier",
			"∀u:(D → num). g(u) ∈ R.carrier",
			"polynomial_algebra_mul(R, f, g, m) ≠ R.zero",
		},
		Conclusion: "finite_support(0, m) ∧ " +
			"(∃m₁:(D → num). (∀x:D. m₁(x) ≤ m(x)) ∧ f(m₁) ≠ R.zero ∧ g(λx:D. m(x) - m₁(x)) ≠ R.zero)",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			f, g *Arrow[Fun[D, Nat], A],
			m *Expr[Fun[D, Nat]],
			ring, fIn, gIn, nonzero Fact,
		) {
			a.Cases(a.TermAs[Bool]("finite_support(0, m)"))
			a.When(
				"at a finitely supported m the coefficient is a finite sum, and a sum of zeros is zero",
				func(c *Argument, finite Fact) {
					m1, term := c.ObtainAs[Fun[D, Nat]](
						"so some term of the sum is nonzero",
						"∃m₁:(D → num). (∀x:D. m₁(x) ≤ m(x)) ∧ f(m₁) * g(λx:D. m(x) - m₁(x)) ≠ R.zero",
						By(
							nonzero,
							finite,
							PolynomialAlgebraMulDef.At(R, f, g, m),
							MonomialsBelowFinite.At(m),
							module.ModuleSumIdentityMonoid.Read(comm_ring.AddMonoidOn.Read(ring)).At(
								c.TermAs[Set[Fun[D, Nat]]]("«below»"),
								c.TermAs[Fun[Fun[D, Nat], A]]("λm₁:(D → num). f(m₁) * g(λx:D. m(x) - m₁(x))"))))
					rest := c.TermAs[Fun[D, Nat]]("λx:D. m(x) - m₁(x)")
					c.Show(
						"a product with a zero factor is zero, so neither factor of that term is",
						By(
							finite,
							term,
							fIn.At(m1),
							gIn.At(rest),
							comm_ring.MulLeftZeroOn.Read(ring).AsFact().At(g.Apply(rest)),
							comm_ring.MulRightZeroOn.Read(ring).AsFact().At(f.Apply(m1))))
				})
			a.Otherwise(
				"elsewhere the coefficient is R.zero by definition",
				func(c *Argument, infinite Fact) {
					c.Show(
						"which contradicts its being nonzero",
						By(nonzero, infinite, PolynomialAlgebraMulDef))
				})
		}),
})}

// PolynomialAlgebraMulSupportInSums — a product of two coefficient
// functions valued in the carrier is nonzero only at the sums of a monomial
// where f is nonzero and one where g is: a nonzero coefficient at m has a
// term f(m₁) · g(m − m₁), m₁ below m, with both factors nonzero
// (PolynomialAlgebraMulSupport), and m is m₁ plus m − m₁, exponent by
// exponent.
var PolynomialAlgebraMulSupportInSums = polynomialAlgebraMulSupportInSumsThm{family.Add(registry.ProofEntry{
	Name: "PolynomialAlgebraMulSupportInSums",
	Key:  "prop_49ca2e805076b31e",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀f g:((D → num) → A).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"∀u:(D → num). f(u) ∈ R.carrier",
			"∀u:(D → num). g(u) ∈ R.carrier",
		},
		Conclusion: "fun_support(R.zero, λm:(D → num). polynomial_algebra_mul(R, f, g, m)) ⊆ «sums»",
	},
		func(a *Argument, R *Expr[RingOps[A]], f, g *Arrow[Fun[D, Nat], A], ring, fIn, gIn Fact) {
			cross := a.TermAs[Set[Prod[Fun[D, Nat], Fun[D, Nat]]]]("«cross»")
			addParts := a.TermAs[Fun[Prod[Fun[D, Nat], Fun[D, Nat]], Fun[D, Nat]]](
				"λp:prod(D → num, D → num). λx:D. fst(p, x) + snd(p, x)")
			a.Show(
				"a monomial where the product is nonzero is the sum "+
					"of a monomial where f is nonzero and one where g is",
				Simp(Fwd(set_basic.SubsetDef)),
				Derive(func(b *Argument) {
					m := b.FixAs[Fun[D, Nat]]("m")
					nonzero := b.Simplified(b.Assume(), Fwd(functions.InFunSupport))
					parts := b.Conjuncts(
						GroupPremises(ring, fIn, gIn, nonzero, At(PolynomialAlgebraMulSupport, R, f, g, m)),
						"m is finitely supported",
						"some m₁ below m has f(m₁) and g(m − m₁) nonzero")
					_, term := b.UnpackAs[Fun[D, Nat]](parts[1])
					pieces := b.Conjuncts(
						term,
						"m₁ lies below m",
						"f is nonzero at m₁",
						"g is nonzero at m − m₁")
					sum := b.Have(
						"exponent by exponent, m is m₁ plus m − m₁",
						"(λx:D. m₁(x) + (m(x) - m₁(x))) = m",
						Funext(),
						ByArith(pieces[0]))
					b.Show(
						"so m is the sum of the parts of the pair (m₁, m − "+
							"m₁), f being nonzero at the first and g at the second",
						By(
							pieces[1],
							pieces[2],
							sum,
							pairs.Fst,
							pairs.Snd,
							set_product.InCross,
							set_image.FunInImage.At(
								addParts, cross, b.TermAs[Prod[Fun[D, Nat], Fun[D, Nat]]]("(m₁, λx:D. m(x) - m₁(x))"))))
				}))
		}),
})}

// PolynomialAlgebraMulPairs — the coefficient at a finitely supported m of
// the product of two finitely supported coefficient functions is the sum of
// f(m₁) · g(m₂) over the pairs of a monomial where f is nonzero and one
// where g is that add up to m. A pair adding to m is (m₁, m − m₁) with m₁
// below m, so the first part tells the pairs apart and reindexes the sum
// over them by the monomials below m (ModuleSumImage); a monomial below m
// that is no first part leaves a zero factor in its term, so the sum over
// the first parts is the convolution sum over all the monomials below m
// (ModuleSumSupport).
var PolynomialAlgebraMulPairs = polynomialAlgebraMulPairsThm{family.Add(registry.ProofEntry{
	Name: "PolynomialAlgebraMulPairs",
	Key:  "prop_5201beded1c7ea0b",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀f g:((D → num) → A). ∀m:(D → num).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"∀u:(D → num). f(u) ∈ R.carrier",
			"∀u:(D → num). g(u) ∈ R.carrier",
			"finite_support(R.zero, f)",
			"finite_support(R.zero, g)",
			"finite_support(0, m)",
		},
		Conclusion: "polynomial_algebra_mul(R, f, g, m) = " +
			"module_sum(R.add, R.zero, «fibre»(m), λp:prod(D → num, D → num). f(fst(p)) * g(snd(p)))",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			f, g *Arrow[Fun[D, Nat], A],
			m *Arrow[D, Nat],
			ring, fIn, gIn, fFinite, gFinite, mFinite Fact,
		) {
			cross := a.TermAs[Set[Prod[Fun[D, Nat], Fun[D, Nat]]]]("«cross»")
			pairsAddingToM := a.TermAs[Set[Prod[Fun[D, Nat], Fun[D, Nat]]]]("«fibre»(m)")
			first := a.TermAs[Fun[Prod[Fun[D, Nat], Fun[D, Nat]], Fun[D, Nat]]]("fst")
			inCross := a.Have(
				"the pairs of a monomial where f is nonzero and one where "+
					"g is are finitely many, those adding to m among them",
				"finite(«cross») ∧ «fibre»(m) ⊆ «cross»",
				BySets(
					fFinite,
					gFinite,
					function_module.FiniteSupportDef,
					finite_set.FiniteProduct.At(
						a.TermAs[Set[Fun[D, Nat]]]("fun_support(R.zero, f)"),
						a.TermAs[Set[Fun[D, Nat]]]("fun_support(R.zero, g)"))))
			finitePairs := a.Have(
				"so the pairs adding to m are finitely many",
				"finite(«fibre»(m))",
				By(inCross, finite_set.FiniteSubset.At(pairsAddingToM, cross)))
			determined := a.Have(
				"a pair adding to m has its first part below m and its second part m minus the first",
				Statement{
					Binders:    "∀p:prod(D → num, D → num).",
					Hypotheses: []string{"p ∈ «fibre»(m)"},
					Conclusion: "(∀x:D. fst(p, x) ≤ m(x)) ∧ snd(p) = (λx:D. m(x) - fst(p, x))",
				},
				Derive(func(b *Argument) {
					b.FixAs[Prod[Fun[D, Nat], Fun[D, Nat]]]("p")
					parts := b.Conjuncts(
						b.Assume(),
						"p pairs a monomial where f is nonzero with one where g is",
						"and its two parts add up to m")
					sums := b.Have(
						"exponent by exponent the two parts add up to m",
						"∀x:D. fst(p, x) + snd(p, x) = m(x)",
						By(Normalized, parts[1]))
					b.Show(
						"so the first part is at most m and the second is m minus the first",
						SplitConj(
							Case(
								"each exponent of the first part is at most that of m",
								ByArith(sums)),
							Case(
								"each exponent of the second part is that of m minus that of the first",
								Funext(),
								ByArith(sums))))
				}))
			apart := a.Have(
				"the first part tells the pairs adding to m apart",
				"injective_on(«fibre»(m), fst)",
				Simp(Fwd(functions.InjectiveOnDef)),
				Derive(func(b *Argument) {
					p := b.FixAs[Prod[Fun[D, Nat], Fun[D, Nat]]]("p")
					q := b.FixAs[Prod[Fun[D, Nat], Fun[D, Nat]]]("q")
					both := b.Conjuncts(
						b.Assume(),
						"p adds up to m",
						"so does q",
						"and the two have one first part")
					seconds := b.Have(
						"so they have one second part, m minus the first",
						"snd(p) = snd(q)",
						By(determined.At(p), determined.At(q), both[0], both[1], both[2]))
					b.Show(
						"and a pair is its two parts",
						By(both[2], seconds, pairs.PairEta.At(p), pairs.PairEta.At(q)))
				}))
			firsts := a.Have(
				"the first parts of the pairs adding to m are below m",
				"image(fst, «fibre»(m)) ⊆ «below»",
				Simp(Fwd(set_basic.SubsetDef)),
				Derive(func(b *Argument) {
					b.FixAs[Fun[D, Nat]]("k")
					p, pair := b.UnpackAs[Prod[Fun[D, Nat], Fun[D, Nat]]](
						b.Unfolded(b.Assume(), set_basic.ImageDef), "p")
					b.Show(
						"k is the first part of a pair adding to m",
						By(determined.At(p), pair))
				}))
			reached := a.Have(
				"a monomial m₁ below m with f(m₁) and g(m − m₁) nonzero is the first part of the pair (m₁, m − m₁)",
				Statement{
					Binders: "∀m₁:(D → num).",
					Hypotheses: []string{
						"m₁ ∈ «below»",
						"f(m₁) ≠ R.zero",
						"g(λx:D. m(x) - m₁(x)) ≠ R.zero",
					},
					Conclusion: "m₁ ∈ image(fst, «fibre»(m))",
				},
				Derive(func(b *Argument) {
					b.FixAs[Fun[D, Nat]]("m₁")
					parts := b.Conjuncts(
						b.Assume(),
						"m₁ is below m",
						"f is nonzero at m₁",
						"g is nonzero at m − m₁")
					bound := b.Have(
						"exponent by exponent m₁ is at most m",
						"∀x:D. m₁(x) ≤ m(x)",
						By(parts[0]))
					sum := b.Have(
						"so m₁ plus m − m₁ is m",
						"(λx:D. m₁(x) + (m(x) - m₁(x))) = m",
						Funext(),
						ByArith(bound))
					member := b.Have(
						"so (m₁, m − m₁) is a pair adding to m",
						"(m₁, λx:D. m(x) - m₁(x)) ∈ «fibre»(m)",
						BySets(parts[1], parts[2], sum, pairs.Fst, pairs.Snd, set_product.InCross))
					b.Show(
						"whose first part is m₁",
						By(
							member,
							pairs.Fst,
							set_image.FunInImage.At(
								first, pairsAddingToM, b.TermAs[Prod[Fun[D, Nat], Fun[D, Nat]]]("(m₁, λx:D. m(x) - m₁(x))"))))
				}))
			vanish := a.Have(
				"below m and off the first parts a term of the convolution has a zero factor, so is R.zero",
				Statement{
					Binders: "∀m₁:(D → num).",
					Hypotheses: []string{
						"m₁ ∈ «below»",
						"m₁ ∉ image(fst, «fibre»(m))",
					},
					Conclusion: "f(m₁) * g(λx:D. m(x) - m₁(x)) = R.zero",
				},
				Derive(func(b *Argument) {
					m1 := b.FixAs[Fun[D, Nat]]("m₁")
					off := b.Assume()
					rest := b.TermAs[Fun[D, Nat]]("λx:D. m(x) - m₁(x)")
					b.Show(
						"either factor being zero, so is the product",
						By(
							off,
							fIn.At(m1),
							gIn.At(rest),
							reached.At(m1),
							comm_ring.MulLeftZeroOn.Read(ring).AsFact().At(g.Apply(rest)),
							comm_ring.MulRightZeroOn.Read(ring).AsFact().At(f.Apply(m1))))
				}))
			terms := a.Have(
				"every term f(m₁) · g(m − m₁) lies in R",
				"∀m₁:(D → num). f(m₁) * g(λx:D. m(x) - m₁(x)) ∈ R.carrier",
				By(fIn, gIn, comm_ring.MulIn.Read(ring)))
			sameSecond := a.Have(
				"at a pair adding to m the second part is m minus the first",
				Statement{
					Binders:    "∀p:prod(D → num, D → num).",
					Hypotheses: []string{"p ∈ «fibre»(m)"},
					Conclusion: "f(fst(p)) * g(λx:D. m(x) - fst(p, x)) = f(fst(p)) * g(snd(p))",
				},
				By(determined))
			regular := module.RegularModuleOn.Read(ring)
			convolution := a.TermAs[Fun[Fun[D, Nat], A]]("λm₁:(D → num). f(m₁) * g(λx:D. m(x) - m₁(x))")
			a.Show(
				"the coefficient at m is the convolution sum over the monomials "+
					"below m, whose nonzero terms are indexed by the pairs adding to m",
				Simp(Fwd(PolynomialAlgebraMulDef)),
				CalcEq(
					Leg(
						a.TermAs[A](
							"module_sum(R.add, R.zero, image(fst, «fibre»(m)), λm₁:(D → num). f(m₁) * g(λx:D. m(x) - m₁(x)))"),
						"off the first parts of the pairs adding to m the terms vanish",
						By(
							terms,
							vanish,
							mFinite,
							firsts,
							MonomialsBelowFinite.At(m),
							module.ModuleSumSupport.Read(regular).At(
								a.TermAs[Set[Fun[D, Nat]]]("«below»"),
								a.TermAs[Set[Fun[D, Nat]]]("image(fst, «fibre»(m))"),
								convolution))),
					Leg(
						a.TermAs[A](
							"module_sum(R.add, "+
								"    R.zero, "+
								"    «fibre»(m), "+
								"    λp:prod(D → num, D → num). f(fst(p)) * g(λx:D. m(x) - fst(p, x)))"),
						"reindex by the first part, which tells the pairs apart",
						By(
							finitePairs,
							terms,
							apart,
							module.ModuleSumImage.Read(regular).At(pairsAddingToM, first, convolution))),
					FinalLeg(
						"and the second part of each pair is m minus the first",
						By(sameSecond, module.ModuleSumCongruence)),
				))
		}),
})}

// PolynomialAlgebraMulIn — the product of two polynomials of S is a
// polynomial of S: each coefficient of the product is a finite sum of
// products of coefficients, so it lies in the carrier, and the product is
// nonzero only at the sums of a monomial where f is nonzero and one where g
// is (PolynomialAlgebraMulSupportInSums), finitely many, each the sum of
// two monomials of S and so one itself (MonomialAddIn).
var PolynomialAlgebraMulIn = polynomialAlgebraMulInThm{family.Add(registry.ProofEntry{
	Name: "PolynomialAlgebraMulIn",
	Key:  "prop_85179c4819f29d29",
	Reading: "No condition on S is asked beyond f and g being polynomials of S: " +
		"the product is nonzero only at the sums of a monomial where f is nonzero " +
		"and one where g is, and a sum of two monomials of S is a monomial of S.",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀S:set(D). ∀f g:((D → num) → A).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"f ∈ polynomial_algebra(R, S)",
			"g ∈ polynomial_algebra(R, S)",
		},
		Conclusion: "polynomial_algebra_mul(R, f, g) ∈ polynomial_algebra(R, S)",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			S *Expr[Set[D]],
			f, g *Arrow[Fun[D, Nat], A],
			ring, fIn, gIn Fact,
		) {
			cross := a.TermAs[Set[Prod[Fun[D, Nat], Fun[D, Nat]]]]("«cross»")
			addParts := a.TermAs[Fun[Prod[Fun[D, Nat], Fun[D, Nat]], Fun[D, Nat]]](
				"λp:prod(D → num, D → num). λx:D. fst(p, x) + snd(p, x)")
			fParts := a.Conjuncts(
				a.Simplified(fIn, Fwd(PolynomialAlgebraMember)),
				"f is nonzero at finitely many monomials",
				"every monomial where f is nonzero is a monomial of S",
				"every coefficient of f lies in the carrier")
			gParts := a.Conjuncts(
				a.Simplified(gIn, Fwd(PolynomialAlgebraMember)),
				"g is nonzero at finitely many monomials",
				"every monomial where g is nonzero is a monomial of S",
				"every coefficient of g lies in the carrier")
			inCarrier := a.Have(
				"every coefficient of the product lies in the carrier",
				"∀m:(D → num). polynomial_algebra_mul(R, f, g, m) ∈ R.carrier",
				Derive(func(b *Argument) {
					m := b.FixAs[Fun[D, Nat]]("m")
					b.Cases(b.TermAs[Bool]("finite_support(0, m)"))
					b.When(
						"at a finitely supported m it is a finite sum of products of coefficients",
						func(c *Argument, finite Fact) {
							c.Show(
								"each product lying in the carrier, so does the sum",
								Simp(Fwd(PolynomialAlgebraMulDef)),
								By(
									fParts[2],
									gParts[2],
									finite,
									comm_ring.MulIn.Read(ring),
									MonomialsBelowFinite.At(m),
									module.ModuleSumInMonoid.Read(comm_ring.AddMonoidOn.Read(ring))))
						})
					b.Otherwise(
						"elsewhere it is R.zero",
						Simp(Fwd(PolynomialAlgebraMulDef)),
						By(comm_ring.ZeroIn.Read(ring)))
				}))
			fSupport := a.TermAs[Set[Fun[D, Nat]]]("fun_support(R.zero, f)")
			gSupport := a.TermAs[Set[Fun[D, Nat]]]("fun_support(R.zero, g)")
			sums := a.TermAs[Set[Fun[D, Nat]]]("«sums»")
			productSupport := a.TermAs[Set[Fun[D, Nat]]](
				"fun_support(R.zero, λm:(D → num). polynomial_algebra_mul(R, f, g, m))")
			support := a.Simplified(
				GroupPremises(ring, fParts[2], gParts[2], PolynomialAlgebraMulSupportInSums.At(R, f, g)))
			finiteSums := a.Have(
				"the pointwise sums of a monomial where f is nonzero and one where g "+
					"is, the image of the product of the two supports, are finitely many",
				"finite(«sums»)",
				By(
					fParts[0],
					gParts[0],
					finite_set.FiniteProduct.At(fSupport, gSupport),
					finite_set.FiniteImage.At(addParts, cross)))
			finiteSupport := a.Have(
				"so the product, nonzero only at those sums, is nonzero at finitely many monomials",
				"finite(fun_support(R.zero, λm:(D → num). polynomial_algebra_mul(R, f, g, m)))",
				By(support, finiteSums, finite_set.FiniteSubset.At(productSupport, sums)))
			sumsMonomials := a.Have(
				"each of those sums, the sum of two monomials of S, is a monomial of S",
				"«sums» ⊆ monomials(S)",
				Simp(Fwd(set_basic.SubsetDef)),
				Derive(func(b *Argument) {
					b.FixAs[Fun[D, Nat]]("k")
					p, pair := b.UnpackAs[Prod[Fun[D, Nat], Fun[D, Nat]]](
						b.Unfolded(b.Assume(), set_basic.ImageDef), "p")
					first, second := b.TermAs[Fun[D, Nat]]("fst(p)"), b.TermAs[Fun[D, Nat]]("snd(p)")
					b.Show(
						"k is the sum of the parts of p, monomials of S since f "+
							"and g are nonzero there and nonzero only at monomials of S",
						By(
							pair,
							b.Unfolded(fParts[1], set_basic.SubsetDef).At(first),
							b.Unfolded(gParts[1], set_basic.SubsetDef).At(second),
							set_product.InCrossProjections.At(fSupport, gSupport, p),
							MonomialAddIn.At(S, first, second)))
				}))
			a.Show(
				"finitely supported, with coefficients in the carrier, nonzero only "+
					"at those sums, all monomials of S, the product is a polynomial of S",
				Simp(Fwd(PolynomialAlgebraMember)),
				By(
					finiteSupport,
					support,
					sumsMonomials,
					inCarrier,
					set_order.SubsetTrans.At(productSupport, sums, a.TermAs[Set[Fun[D, Nat]]]("monomials(S)"))))
		}),
})}

// PolynomialAlgebraMulComm — the product of two coefficient functions with
// values in the carrier, polynomials among them, is commutative:
// coefficient by coefficient, as polynomial.PolynomialMulComm, with the
// monomials below m in place of the indices up to n. At a finitely
// supported m the reflection m₁ ↦ m − m₁ maps the monomials below m one to
// one onto themselves, the subtraction being exact exponent by exponent,
// so it reindexes the sum of f(m₁) * g(m − m₁) into the sum of
// f(m − m₁) * g(m₁), whose terms are those of g(m₁) * f(m − m₁) with the
// factors swapped.
var PolynomialAlgebraMulComm = polynomialAlgebraMulCommThm{family.Add(registry.ProofEntry{
	Name: "PolynomialAlgebraMulComm",
	Key:  "prop_7d89f63a795c1cae",
	Reading: "At an exponent function of infinite support both sides are R.zero " +
		"by the guard of polynomial_algebra_mul. No finite support is asked of f " +
		"and g: below a finitely supported m the sum is finite whatever they are, " +
		"and the coefficients in the carrier are what the ring's commutativity reads.",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀f g:((D → num) → A).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"∀u:(D → num). f(u) ∈ R.carrier",
			"∀u:(D → num). g(u) ∈ R.carrier",
		},
		Conclusion: "polynomial_algebra_mul(R, f, g) = polynomial_algebra_mul(R, g, f)",
		Abbrev: Abbrev{
			{Name: "reflect", Text: "λm₁:(D → num). λx:D. m(x) - m₁(x)"},
			{Name: "summand", Text: "λm₁:(D → num). f(m₁) * g(λx:D. m(x) - m₁(x))"},
		},
	},
		func(a *Argument, R *Expr[RingOps[A]], f, g *Arrow[Fun[D, Nat], A], ring, fIn, gIn Fact) {
			a.Do(Funext())
			m := a.FixAs[Fun[D, Nat]]("m")
			finite := a.Assuming(
				a.Term("finite_support(0, m)"),
				"at an m of infinite support both coefficients are R.zero",
				Simp(Fwd(PolynomialAlgebraMulDef)),
				Refl())
			reflection := a.Have(
				"m₁ ↦ m − m₁ keeps the exponents below m and undoes itself there",
				"∀m₁:(D → num). ∀x:D. m₁(x) ≤ m(x) ⇒ m(x) - m₁(x) ≤ m(x) ∧ m(x) - (m(x) - m₁(x)) = m₁(x)",
				ByArith())
			onto := a.Have(
				"so it maps the monomials below m onto themselves",
				"image(«reflect», «below») = «below»",
				BySets(reflection))
			oneToOne := a.Have(
				"and one to one",
				"injective_on(«below», «reflect»)",
				By(reflection, functions.InjectiveOnDef))
			swapped := a.Have(
				"at m₁ below m the reflected term is the term at m₁ of the other product, its factors swapped",
				Statement{
					Binders:    "∀m₁:(D → num).",
					Hypotheses: []string{"m₁ ∈ «below»"},
					Conclusion: "f(λx:D. m(x) - m₁(x)) * g(λx:D. m(x) - (m(x) - m₁(x))) = " +
						"g(m₁) * f(λx:D. m(x) - m₁(x))",
				},
				Derive(func(b *Argument) {
					b.FixAs[Fun[D, Nat]]("m₁")
					isBelow := b.Assume()
					back := b.Have(
						"the reflection undoes itself at m₁",
						"(λx:D. m(x) - (m(x) - m₁(x))) = m₁",
						Funext(),
						By(reflection, isBelow))
					b.Show(
						"so the term is f(m − m₁) * g(m₁), and the ring's product commutes",
						back.Rw(),
						By(fIn, gIn, comm_monoid.CommOn.Read(comm_ring.MulMonoidOn.Read(ring))))
				}))
			below, reflect :=
				a.TermAs[Set[Fun[D, Nat]]]("«below»"), a.TermAs[Fun[Fun[D, Nat], Fun[D, Nat]]]("«reflect»")
			a.Show(
				"the reflection reindexes one sum into the other, so the two coefficients at m agree",
				Simp(Fwd(PolynomialAlgebraMulDef)),
				CalcEq(
					Leg(
						a.TermAs[A]("module_sum(R.add, R.zero, image(«reflect», «below»), «summand»)"),
						"the monomials below m are their own image under the reflection",
						onto.Rw(),
						Basic()),
					Leg(
						a.TermAs[A](
							"module_sum(R.add, "+
								"    R.zero, "+
								"    «below», "+
								"    λm₁:(D → num). f(λx:D. m(x) - m₁(x)) * g(λx:D. m(x) - (m(x) - m₁(x))))"),
						"reindex along the reflection, the monomials below m being finitely many",
						By(
							module.ModuleSumImage.Read(module.RegularModuleOn.Read(ring)).At(
								below, reflect, a.TermAs[Fun[Fun[D, Nat], A]]("«summand»")),
							MonomialsBelowFinite.At(m),
							finite,
							oneToOne,
							fIn,
							gIn,
							comm_ring.MulIn.Read(ring))),
					FinalLeg(
						"and swap the factors of each term",
						By(swapped, module.ModuleSumCongruence)),
				))
		}),
})}

// PolynomialAlgebraMulAssoc — the product of coefficient functions with
// values in the carrier, polynomials among them, is associative:
// coefficient by coefficient, by the argument of the one-variable
// convolution product (polynomial.PolynomialMulAssoc), with monomials in
// place of the indices, compared exponent by exponent. At a finitely
// supported m each monomial below m is finitely supported, and so is
// m − i, so the guards of the products below m open; h(m − k) and f(i)
// pass into the inner sums, the ring being a module over itself, and both
// sides sum f(i) * g(j) * h(m − i − j) over the triangle i ≤ k ≤ m, the
// left grouped by k = i + j and the right by i (MonomialTriangleSwap).
var PolynomialAlgebraMulAssoc = polynomialAlgebraMulAssocThm{family.Add(registry.ProofEntry{
	Name: "PolynomialAlgebraMulAssoc",
	Key:  "prop_bcfe1e15e096de30",
	Reading: "At an exponent function of infinite support both sides are R.zero " +
		"by the guard of polynomial_algebra_mul. No finite support is asked of f, g " +
		"and h: below a finitely supported m every sum is finite whatever they are, " +
		"and the coefficients in the carrier are what the ring's laws read.",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀f g h:((D → num) → A).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"∀u:(D → num). f(u) ∈ R.carrier",
			"∀u:(D → num). g(u) ∈ R.carrier",
			"∀u:(D → num). h(u) ∈ R.carrier",
		},
		Conclusion: "polynomial_algebra_mul(R, polynomial_algebra_mul(R, f, g), h) = " +
			"polynomial_algebra_mul(R, f, polynomial_algebra_mul(R, g, h))",
	},
		func(a *Argument, R *Expr[RingOps[A]], f, g, h *Arrow[Fun[D, Nat], A], ring, fIn, gIn, hIn Fact) {
			regular := module.RegularModuleOn.Read(ring)
			mulIn := comm_ring.MulIn.Read(ring)
			a.Do(Funext())
			m := a.FixAs[Fun[D, Nat]]("m")
			finiteM := a.Assuming(
				a.Term("finite_support(0, m)"),
				"at an m of infinite support both coefficients are R.zero, by the guard of the product",
				Simp(Fwd(PolynomialAlgebraMulDef)),
				Basic())
			belowFinitelySupported := a.Have(
				"a monomial below m is finitely supported, its support inside the support of m",
				"∀k:(D → num). (∀x:D. k(x) ≤ m(x)) ⇒ finite_support(0, k)",
				Derive(func(b *Argument) {
					b.FixAs[Fun[D, Nat]]("k")
					kBelow := b.Assume()
					inside := b.Have(
						"where k is nonzero, so is m",
						"fun_support(0, k) ⊆ fun_support(0, m)",
						BySets(kBelow, nat_order.LessEqZeroClause))
					b.Show(
						"and a part of a finite set is finite",
						By(
							finiteM,
							inside,
							function_module.FiniteSupportDef,
							finite_set.FiniteSubset.At(
								b.TermAs[Set[D]]("fun_support(0, k)"), b.TermAs[Set[D]]("fun_support(0, m)"))))
				}))
			differenceFinite := a.Have(
				"so is m − i, below m",
				"∀i:(D → num). finite_support(0, λx:D. m(x) - i(x))",
				ByArith(belowFinitelySupported))
			hDistributes := a.Have(
				"h(m − k) distributes over the sum over i ≤ k, a finite sum of members of R",
				Statement{
					Binders: "∀k:(D → num).",
					Hypotheses: []string{
						"∀x:D. k(x) ≤ m(x)",
					},
					Conclusion: "module_sum(R.add, " +
						"    R.zero, " +
						"    {i:(D → num) | ∀x:D. i(x) ≤ k(x)}, " +
						"    λi:(D → num). f(i) * g(λx:D. k(x) - i(x))) * " +
						"h(λx:D. m(x) - k(x)) = " +
						"module_sum(R.add, " +
						"    R.zero, " +
						"    {i:(D → num) | ∀x:D. i(x) ≤ k(x)}, " +
						"    λi:(D → num). f(i) * g(λx:D. k(x) - i(x)) * h(λx:D. m(x) - k(x)))",
				},
				Derive(func(b *Argument) {
					k := b.FixAs[Fun[D, Nat]]("k")
					kBelow := b.Assume()
					b.Show(
						"a finite sum of scalars scales term by term",
						By(
							kBelow,
							belowFinitelySupported,
							fIn,
							gIn,
							hIn,
							mulIn,
							module.ModuleSumSmulRight.Read(regular).AsFact().At(
								b.TermAs[Set[Fun[D, Nat]]]("{i:(D → num) | ∀x:D. i(x) ≤ k(x)}"),
								b.TermAs[Fun[Fun[D, Nat], A]]("λi:(D → num). f(i) * g(λx:D. k(x) - i(x))"),
								b.TermAs[A]("h(λx:D. m(x) - k(x))")),
							MonomialsBelowFinite.At(k)))
				}))
			fDistributes := a.Have(
				"f(i) distributes over the sum over j ≤ m − i, a finite sum of members of R",
				"∀i:(D → num). "+
					"    f(i) * "+
					"    module_sum(R.add, "+
					"        R.zero, "+
					"        {j:(D → num) | ∀x:D. j(x) ≤ m(x) - i(x)}, "+
					"        λj:(D → num). g(j) * h(λx:D. m(x) - i(x) - j(x))) = "+
					"    module_sum(R.add, "+
					"        R.zero, "+
					"        {j:(D → num) | ∀x:D. j(x) ≤ m(x) - i(x)}, "+
					"        λj:(D → num). f(i) * (g(j) * h(λx:D. m(x) - i(x) - j(x))))",
				Derive(func(b *Argument) {
					i := b.FixAs[Fun[D, Nat]]("i")
					b.Show(
						"a scalar distributes over a finite sum",
						By(
							differenceFinite.At(i),
							fIn,
							gIn,
							hIn,
							mulIn,
							module.ModuleSumSmul.Read(regular).AsFact().At(
								b.TermAs[Set[Fun[D, Nat]]]("{j:(D → num) | ∀x:D. j(x) ≤ m(x) - i(x)}"),
								b.TermAs[A]("f(i)"),
								b.TermAs[Fun[Fun[D, Nat], A]]("λj:(D → num). g(j) * h(λx:D. m(x) - i(x) - j(x))")),
							MonomialsBelowFinite.At(b.TermAs[Fun[D, Nat]]("λx:D. m(x) - i(x)"))))
				}))
			regroup := a.Have(
				"each product regroups, its exponents read as i, (i + j) − i and m − (i + j)",
				"∀i j:(D → num). "+
					"    f(i) * g(λx:D. i(x) + j(x) - i(x)) * h(λx:D. m(x) - (i(x) + j(x))) = "+
					"    f(i) * (g(j) * h(λx:D. m(x) - i(x) - j(x)))",
				Derive(func(b *Argument) {
					b.FixAs[Fun[D, Nat]]("i")
					b.FixAs[Fun[D, Nat]]("j")
					middle := b.Have(
						"adding i and taking it away leaves j",
						"∀x:D. i(x) + j(x) - i(x) = j(x)",
						ByArith())
					last := b.Have(
						"taking i + j from m is taking i and then j",
						"∀x:D. m(x) - (i(x) + j(x)) = m(x) - i(x) - j(x)",
						ByArith())
					b.Show(
						"and the product of three members of R associates",
						Simp(Fwd(middle), Fwd(last)),
						By(fIn, gIn, hIn, comm_monoid.AssocOn.Read(comm_ring.MulMonoidOn.Read(ring))))
				}))
			triangle := a.TermAs[Fun2[Fun[D, Nat], Fun[D, Nat], A]](
				"λi:(D → num). λk:(D → num). f(i) * g(λx:D. k(x) - i(x)) * h(λx:D. m(x) - k(x))")
			a.Show(
				"both coefficients at m sum f(i) * g(j) * h(m − i − j) over the triangle i + j ≤ m",
				CalcEq(
					Leg(
						a.TermAs[A](
							"module_sum(R.add, "+
								"    R.zero, "+
								"    «below», "+
								"    λk:(D → num). "+
								"        module_sum(R.add, "+
								"            R.zero, "+
								"            {i:(D → num) | ∀x:D. i(x) ≤ k(x)}, "+
								"            λi:(D → num). f(i) * g(λx:D. k(x) - i(x))) * "+
								"        h(λx:D. m(x) - k(x)))"),
						"below m each coefficient of f g is its finite sum",
						Simp(Fwd(PolynomialAlgebraMulDef)),
						By(belowFinitelySupported, module.ModuleSumCongruence)),
					Leg(
						a.TermAs[A](
							"module_sum(R.add, "+
								"    R.zero, "+
								"    «below», "+
								"    λk:(D → num). "+
								"        module_sum(R.add, "+
								"            R.zero, "+
								"            {i:(D → num) | ∀x:D. i(x) ≤ k(x)}, "+
								"            λi:(D → num). f(i) * g(λx:D. k(x) - i(x)) * h(λx:D. m(x) - k(x))))"),
						"h(m − k) passes into each inner sum",
						By(hDistributes, module.ModuleSumCongruence)),
					Leg(
						a.TermAs[A](
							"module_sum(R.add, "+
								"    R.zero, "+
								"    «below», "+
								"    λi:(D → num). "+
								"        module_sum(R.add, "+
								"            R.zero, "+
								"            {j:(D → num) | ∀x:D. j(x) ≤ m(x) - i(x)}, "+
								"            λj:(D → num). f(i) * g(λx:D. i(x) + j(x) - i(x)) * h(λx:D. m(x) - (i(x) + j(x)))))"),
						"the triangle i ≤ k ≤ m summed by i instead of by k = i + j",
						By(finiteM, fIn, gIn, hIn, mulIn, MonomialTriangleSwap.Read(regular).At(m, triangle))),
					Leg(
						a.TermAs[A](
							"module_sum(R.add, "+
								"    R.zero, "+
								"    «below», "+
								"    λi:(D → num). "+
								"        module_sum(R.add, "+
								"            R.zero, "+
								"            {j:(D → num) | ∀x:D. j(x) ≤ m(x) - i(x)}, "+
								"            λj:(D → num). f(i) * (g(j) * h(λx:D. m(x) - i(x) - j(x)))))"),
						"each product regroups",
						By(regroup, module.ModuleSumCongruence)),
					Leg(
						a.TermAs[A](
							"module_sum(R.add, "+
								"    R.zero, "+
								"    «below», "+
								"    λi:(D → num). "+
								"        f(i) * "+
								"        module_sum(R.add, "+
								"            R.zero, "+
								"            {j:(D → num) | ∀x:D. j(x) ≤ m(x) - i(x)}, "+
								"            λj:(D → num). g(j) * h(λx:D. m(x) - i(x) - j(x))))"),
						"f(i) leaves each inner sum",
						By(fDistributes, module.ModuleSumCongruence)),
					FinalLeg(
						"and m − i being finitely supported, each inner sum is the coefficient of g h at m − i",
						Simp(Fwd(PolynomialAlgebraMulDef)),
						By(differenceFinite)),
				))
		}),
})}

// PolynomialAlgebraMulDistrib — the product of coefficient functions with
// values in the carrier, polynomials among them, distributes over their
// sum. Coefficientwise, as polynomial.PolynomialMulDistrib: at a finitely
// supported monomial m each term f(m₁) · (g(m − m₁) + h(m − m₁)) splits by
// the ring's distributivity, and over the finitely many monomials below m
// a sum of sums of members of the carrier is the sum of the two sums.
var PolynomialAlgebraMulDistrib = polynomialAlgebraMulDistribThm{family.Add(registry.ProofEntry{
	Name: "PolynomialAlgebraMulDistrib",
	Key:  "prop_d00819a2e9a97e1d",
	Reading: "At an exponent function of infinite support the left side is R.zero by the guard of " +
		"polynomial_algebra_mul and the right side R.zero + R.zero, one value because R.zero lies in " +
		"R.carrier. No finite support is asked of f, g and h: below a finitely supported m the sums are " +
		"finite whatever they are, and the coefficients in the carrier are what the ring's laws read.",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀f g h:((D → num) → A).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"∀u:(D → num). f(u) ∈ R.carrier",
			"∀u:(D → num). g(u) ∈ R.carrier",
			"∀u:(D → num). h(u) ∈ R.carrier",
		},
		Conclusion: "polynomial_algebra_mul(R, f, λm:(D → num). R.add(g(m), h(m))) = " +
			"λm:(D → num). R.add(polynomial_algebra_mul(R, f, g, m), polynomial_algebra_mul(R, f, h, m))",
	},
		func(a *Argument, R *Expr[RingOps[A]], f, g, h *Arrow[Fun[D, Nat], A], ring, fIn, gIn, hIn Fact) {
			a.Do(Funext())
			m := a.FixAs[Fun[D, Nat]]("m")
			finite := a.Assuming(
				a.Term("finite_support(0, m)"),
				"at an m of infinite support both coefficients are "+
					"R.zero, and R.zero, lying in R.carrier, is R.zero + R.zero",
				Simp(Fwd(PolynomialAlgebraMulDef)),
				By(comm_ring.ZeroIn.Read(ring), comm_monoid.RightIdentityOn.Read(comm_ring.AddMonoidOn.Read(ring))))
			splits := a.Have(
				"each term f(m₁) · (g(m − m₁) + h(m − m₁)) splits, as the ring's product distributes over its sum",
				"∀m₁:(D → num). "+
					"    f(m₁) * (g(λx:D. m(x) - m₁(x)) + h(λx:D. m(x) - m₁(x))) = "+
					"    f(m₁) * g(λx:D. m(x) - m₁(x)) + f(m₁) * h(λx:D. m(x) - m₁(x))",
				By(fIn, gIn, hIn, comm_ring.LeftDistribOn.Read(ring)))
			a.Show(
				"the coefficient at m of f times g + h is the sum of those of f times g and f times h",
				Simp(Fwd(PolynomialAlgebraMulDef)),
				CalcEq(
					Leg(
						a.TermAs[A](
							"module_sum(R.add, "+
								"    R.zero, "+
								"    «below», "+
								"    λm₁:(D → num). f(m₁) * g(λx:D. m(x) - m₁(x)) + f(m₁) * h(λx:D. m(x) - m₁(x)))"),
						"split each term",
						By(splits, module.ModuleSumCongruence)),
					FinalLeg(
						"over the finitely many monomials below m, a sum of sums is the sum of the two sums",
						By(
							fIn,
							gIn,
							hIn,
							comm_ring.MulIn.Read(ring),
							finite,
							MonomialsBelowFinite.At(m),
							module.ModuleSumAdd.Read(module.RegularModuleOn.Read(ring)).At(
								a.TermAs[Set[Fun[D, Nat]]]("«below»"),
								a.TermAs[Fun[Fun[D, Nat], A]]("λm₁:(D → num). f(m₁) * g(λx:D. m(x) - m₁(x))"),
								a.TermAs[Fun[Fun[D, Nat], A]]("λm₁:(D → num). f(m₁) * h(λx:D. m(x) - m₁(x))")))),
				))
		}),
})}

// PolynomialAlgebraTermMul — multiplying by the term c·xⁿ, the coefficient
// c at the monomial n and R.zero elsewhere, shifts the coefficients by n
// and scales them by c: the coefficient at a finitely supported m above n
// is c * f(m − n), and every other coefficient is R.zero. At a finitely
// supported m the convolution over the monomials below m has one term that
// can be nonzero, the term at n: when n lies below m the sum is that term
// (ModuleSumSingle), and when it does not every term vanishes; at an m of
// infinite support the product is R.zero by its definition.
var PolynomialAlgebraTermMul = polynomialAlgebraTermMulThm{family.Add(registry.ProofEntry{
	Name: "PolynomialAlgebraTermMul",
	Key:  "prop_e6accc6aa4e02ef2",
	Reading: "No finite support is asked of n: a finitely supported m never lies above an n of " +
		"infinite support, so both sides then vanish everywhere. Nor is f asked to be a polynomial: " +
		"below a finitely supported m the sum is finite whatever f is, and only its coefficients' " +
		"membership in the carrier is read. At c = R.zero both sides are the zero polynomial.",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀c:A. ∀n:(D → num). ∀f:((D → num) → A).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"c ∈ R.carrier",
			"∀u:(D → num). f(u) ∈ R.carrier",
		},
		Conclusion: "polynomial_algebra_mul(R, delta_at(R.zero, c, n), f) = " +
			"λm:(D → num). COND(finite_support(0, m) ∧ (∀x:D. n(x) ≤ m(x)), c * f(λx:D. m(x) - n(x)), R.zero)",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			c *Expr[A],
			n *Arrow[D, Nat],
			f *Arrow[Fun[D, Nat], A],
			ring, cIn, coefficients Fact,
		) {
			a.Do(Funext())
			m := a.FixAs[Fun[D, Nat]]("m")
			finite := a.Assuming(
				a.Term("finite_support(0, m)"),
				"at an m of infinite support both sides are R.zero",
				Given(func(b *Argument, infinite Fact) {
					b.Show(
						"the product is R.zero by the guard of its definition, and so is the right side",
						Simp(Fwd(PolynomialAlgebraMulDef)),
						By(infinite))
				}))
			terms := a.Have(
				"every term of the sum is c or R.zero times a coefficient of f, so lies in the carrier",
				"∀m₁:(D → num). delta_at(R.zero, c, n, m₁) * f(λx:D. m(x) - m₁(x)) ∈ R.carrier",
				Simp(Fwd(free_module.DeltaAtDef)),
				By(cIn, coefficients, comm_ring.ZeroIn.Read(ring), comm_ring.MulIn.Read(ring)))
			offN := a.Have(
				"off n the term is R.zero times a coefficient of f, so it vanishes",
				"∀m₁:(D → num). m₁ ≠ n ⇒ delta_at(R.zero, c, n, m₁) * f(λx:D. m(x) - m₁(x)) = R.zero",
				By(coefficients, free_module.DeltaAtDef, comm_ring.MulLeftZeroOn.Read(ring)))
			below := a.TermAs[Set[Fun[D, Nat]]]("«below»")
			term := a.TermAs[Fun[Fun[D, Nat], A]](
				"λm₁:(D → num). delta_at(R.zero, c, n, m₁) * f(λx:D. m(x) - m₁(x))")
			a.Cases(a.TermAs[Bool]("∀x:D. n(x) ≤ m(x)"))
			a.When(
				"when n lies below m, the one surviving term is the term at n",
				func(b *Argument, above Fact) {
					b.Show(
						"the finite sum over the monomials below m is its term at n, c * f(m − n)",
						Simp(Fwd(PolynomialAlgebraMulDef)),
						By(
							above,
							terms,
							offN,
							finite,
							MonomialsBelowFinite.At(m),
							module.ModuleSumSingle.Read(module.RegularModuleOn.Read(ring)).At(below, n, term),
							free_module.DeltaAtDef))
				})
			a.Otherwise(
				"when n does not lie below m, every term vanishes",
				func(b *Argument, notAbove Fact) {
					vanish := b.Have(
						"no monomial below m is n, so every term of the sum is R.zero",
						"∀m₁:(D → num). m₁ ∈ «below» ⇒ delta_at(R.zero, c, n, m₁) * f(λx:D. m(x) - m₁(x)) = R.zero",
						By(notAbove, offN))
					b.Show(
						"both sides are R.zero",
						Simp(Fwd(PolynomialAlgebraMulDef)),
						CalcEq(
							Leg(
								b.TermAs[A]("R.zero"),
								"a finite sum of R.zero's is R.zero",
								By(
									vanish,
									finite,
									MonomialsBelowFinite.At(m),
									module.ModuleSumIdentityMonoid.Read(comm_ring.AddMonoidOn.Read(ring)).At(below, term))),
							FinalLeg(
								"n not lying below m, the right side is R.zero",
								By(notAbove)),
						))
				})
		}),
})}

// PolynomialAlgebraMulOne — the one polynomial is a unit for the
// product: multiplied on the left by it, every polynomial comes back.
// The one polynomial is the constant R.one, both being the generator at
// the monomial of the constants, so this is PolynomialAlgebraConstMul at
// c = R.one: every coefficient comes back as R.one * f(m) = f(m).
var PolynomialAlgebraMulOne = polynomialAlgebraMulOneThm{family.Add(registry.ProofEntry{
	Name: "PolynomialAlgebraMulOne",
	Key:  "prop_71a9f47ab46aba2f",
	Reading: "At an exponent function of infinite support the product is zero by " +
		"definition, and so is a polynomial, whose coefficients vanish off the monomials.",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀S:set(D). ∀f:((D → num) → A).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"f ∈ polynomial_algebra(R, S)",
		},
		Conclusion: "polynomial_algebra_mul(R, polynomial_algebra_one(R), f) = f",
	},
		func(a *Argument, R *Expr[RingOps[A]], S *Expr[Set[D]], f *Arrow[Fun[D, Nat], A], ring, fIn Fact) {
			constant := a.Have(
				"the one polynomial is the constant R.one, both the generator at the monomial of the constants",
				"polynomial_algebra_one⟨D:D⟩(R) = polynomial_algebra_const(R, R.one)",
				Simp(Fwd(PolynomialAlgebraOneDef), Fwd(PolynomialAlgebraConstDef)),
				Basic())
			a.Do(
				constant.Rw(),
				Simp(Fwd(PolynomialAlgebraConstMul), Fwd(comm_ring.OneIn.Read(ring)), Fwd(fIn)),
				Funext())
			// The unpack rewrites fIn in place, so it comes after the rewrite
			// above that reads fIn whole.
			fParts := a.Conjuncts(
				a.Simplified(fIn, Fwd(PolynomialAlgebraMember)),
				"f is nonzero at finitely many monomials",
				"every monomial where f is nonzero is a monomial of S",
				"every coefficient of f lies in the carrier")
			coefficients := fParts[2]
			m := a.FixAs[Fun[D, Nat]]("m")
			a.Show(
				"R.one is the unit of the product",
				By(
					coefficients.At(m),
					comm_monoid.LeftIdentityOn.Read(comm_ring.MulMonoidOn.Read(ring)).AsFact().At(f.Apply(m))))
		}),
})}

// PolynomialAlgebraConstMul — the product with the constant c scales
// every coefficient by c. It is PolynomialAlgebraTermMul at the monomial
// of the constants, the constant c being the term c·x⁰: every exponent
// function lies above the exponent zero and m − 0 is m, so at a finitely
// supported m the coefficient is c * f(m); at an m of infinite support
// both sides are zero, the polynomial vanishing off the monomials.
var PolynomialAlgebraConstMul = polynomialAlgebraConstMulThm{family.Add(registry.ProofEntry{
	Name: "PolynomialAlgebraConstMul",
	Key:  "prop_c86a667099e5d8ba",
	Reading: "At an exponent function of infinite support both sides are R.zero: the product by the " +
		"guard of polynomial_algebra_mul, c * f(m) because f vanishes off the monomials of S. So the " +
		"scalar action of the coefficient ring on the polynomials is multiplication by the constants.",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀S:set(D). ∀c:A. ∀f:((D → num) → A).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"c ∈ R.carrier",
			"f ∈ polynomial_algebra(R, S)",
		},
		Conclusion: "polynomial_algebra_mul(R, polynomial_algebra_const(R, c), f) = " +
			"(λm:(D → num). c * f(m))",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			S *Expr[Set[D]],
			c *Expr[A],
			f *Arrow[Fun[D, Nat], A],
			ring, cIn, fIn Fact,
		) {
			fParts := a.Conjuncts(
				a.Simplified(fIn, Fwd(PolynomialAlgebraMember)),
				"f is nonzero at finitely many monomials",
				"every monomial where f is nonzero is a monomial of S",
				"every coefficient of f lies in the carrier")
			supportInS, coefficients := fParts[1], fParts[2]
			a.Do(
				Simp(Fwd(PolynomialAlgebraConstDef), Fwd(PolynomialAlgebraTermMul), Fwd(coefficients)),
				Funext())
			a.FixAs[Fun[D, Nat]]("m")
			finite := a.Assuming(
				a.Term("finite_support(0, m)"),
				"at an m of infinite support both sides are R.zero",
				Given(func(b *Argument, infinite Fact) {
					vanishes := b.Have(
						"f vanishes at m: the monomials of S are finitely supported",
						"f(m) = R.zero",
						BySets(infinite, supportInS, MonomialsDef))
					b.Show(
						"and so does c * f(m)",
						By(Normalized, infinite, vanishes, cIn, comm_ring.MulRightZeroOn.Read(ring).AsFact().At(c)))
				}))
			a.Show(
				"every m lies above the exponent zero, and m − 0 is m",
				Simp(Fwd(nat_monus.Sub)),
				By(finite, nat_order.ZeroLessEq))
		}),
})}

// PolynomialAlgebraGeneratorMul — the product of the generators at two
// finitely supported monomials is the generator at their sum. It is
// PolynomialAlgebraTermMul at c = R.one, n = m₁ and f the generator at
// m₂: the coefficient at m is R.one · R.one when m is finitely supported,
// lies above m₁ and m − m₁ = m₂, that is when m = m₁ + m₂, a finitely
// supported monomial, and R.zero at every other m.
var PolynomialAlgebraGeneratorMul = polynomialAlgebraGeneratorMulThm{family.Add(registry.ProofEntry{
	Name: "PolynomialAlgebraGeneratorMul",
	Key:  "prop_b3fd5b17f5b50a7",
	Reading: "Both finite supports are load-bearing. Were m₂ of infinite support, the " +
		"product would vanish at every finitely supported m, m − m₁ being finitely supported and " +
		"never m₂, and by definition at every other; were m₁ of infinite support, no monomial " +
		"below a finitely supported m would be m₁, and the product would vanish everywhere " +
		"again; while the generator at m₁ + m₂ is R.one there, nonzero unless R is the zero ring.",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀m₁ m₂:(D → num).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"finite_support(0, m₁)",
			"finite_support(0, m₂)",
		},
		Conclusion: "polynomial_algebra_mul(R, delta_at(m₁), delta_at(m₂)) = delta_at(λx:D. m₁(x) + m₂(x))",
	},
		func(a *Argument, R *Expr[RingOps[A]], m1, m2 *Arrow[D, Nat], ring, finite1, finite2 Fact) {
			values := a.Have(
				"the generator at m₂ takes the values R.one and R.zero, both in the carrier",
				"∀u:(D → num). delta_at(m₂, u) ∈ R.carrier",
				Simp(Fwd(free_module.DeltaAtDef)),
				By(comm_ring.OneIn.Read(ring), comm_ring.ZeroIn.Read(ring)))
			a.Do(
				Simp(Fwd(PolynomialAlgebraTermMul), Fwd(comm_ring.OneIn.Read(ring)), Fwd(values)),
				Funext())
			a.FixAs[Fun[D, Nat]]("m")
			a.Cases(a.TermAs[Bool]("m = (λx:D. m₁(x) + m₂(x))"))
			a.When(
				"at m = m₁ + m₂ the coefficient is R.one · R.one, and the generator at m₁ + m₂ is R.one",
				func(c *Argument, same Fact) {
					sum := c.Have(
						"m₁ + m₂ is finitely supported, a sum of two monomials in all the variables",
						"finite_support(0, λx:D. m₁(x) + m₂(x))",
						BySets(finite1, finite2, MonomialsDef, MonomialAddIn.At(c.TermAs[Set[D]]("𝕌"), m1, m2)))
					pointwise := c.Have(
						"exponent by exponent, m is m₁ + m₂",
						"∀x:D. m(x) = m₁(x) + m₂(x)",
						By(Normalized, same))
					first := c.Have(
						"so m₁ lies below m",
						"∀x:D. m₁(x) ≤ m(x)",
						ByArith(pointwise))
					rest := c.Have(
						"and m − m₁ is m₂",
						"(λx:D. m(x) - m₁(x)) = m₂",
						Funext(),
						ByArith(pointwise))
					c.Show(
						"m is finitely supported and above m₁, and the generator at m₂ is R.one at m − m₁",
						By(
							same,
							sum,
							first,
							rest,
							free_module.DeltaAtDef,
							comm_ring.OneIn.Read(ring),
							comm_monoid.RightIdentityOn.Read(comm_ring.MulMonoidOn.Read(ring))))
				})
			a.Otherwise(
				"at any other m the coefficient is R.zero, and so is the generator at m₁ + m₂",
				func(c *Argument, other Fact) {
					split := c.Have(
						"m₁ lying below m with m − m₁ = m₂ puts m at m₁ + m₂",
						"(∀x:D. m₁(x) ≤ m(x)) ∧ (λx:D. m(x) - m₁(x)) = m₂ ⇒ m = λx:D. m₁(x) + m₂(x)",
						Derive(func(d *Argument) {
							parts := d.Conjuncts(
								d.Assume(),
								"m₁ lies below m",
								"m − m₁ is m₂")
							pointwise := d.Have(
								"exponent by exponent, m − m₁ is m₂",
								"∀x:D. m(x) - m₁(x) = m₂(x)",
								By(Normalized, parts[1]))
							d.Show(
								"so m is m₁ + m₂ exponent by exponent",
								Funext(),
								ByArith(parts[0], pointwise))
						}))
					c.Show(
						"where m₁ lies below m, m − m₁ is not m₂ and the coefficient is R.one · R.zero",
						By(
							other,
							split,
							free_module.DeltaAtDef,
							comm_ring.OneIn.Read(ring),
							comm_ring.MulRightZeroOn.Read(ring)))
				})
		}),
})}

// PolynomialAlgebraCommRingOn — the polynomials of S over a commutative
// ring are a commutative ring under the pointwise sum and the product:
// the sum, zero and negation are the free module's on the monomials of
// S, whose vectors form an abelian group; the one polynomial is the
// generator at the monomial of the constants, a monomial of every S; the
// product is closed, commutative, associative and distributive by the
// product laws, with the one polynomial its unit; and the difference is
// the sum of the negation, coefficient by coefficient.
var PolynomialAlgebraCommRingOn = polynomialAlgebraCommRingOnThm{family.Add(registry.ProofEntry{
	Name: "PolynomialAlgebraCommRingOn",
	Key:  "prop_45c699185634af10",
	Reading: "Over the zero ring every polynomial is zero and the ring is the zero ring, " +
		"which comm_ring_on admits. The operations do not read S: the ring is the ring in every " +
		"variable restricted to the polynomials of S (PolynomialAlgebraRingRestrictVariables).",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀S:set(D).",
		Hypotheses: []string{
			"comm_ring_on(R)",
		},
		Conclusion: "comm_ring_on(polynomial_algebra_ring(R, S))",
	},
		func(a *Argument, R *Expr[RingOps[A]], S *Expr[Set[D]], ring Fact) {
			additive := a.Have(
				"the sum, zero and negation are the free module's on the monomials of S, an abelian group",
				"abelian_group_on(additive_group(polynomial_algebra_ring(R, S)))",
				Simp(Fwd(module_record.AdditiveGroupDef), Fwd(PolynomialAlgebraRingDef), Fwd(PolynomialAlgebraDef)),
				By(
					module.AddAbelianGroupOn,
					free_module.FreeModuleOn.Read(ring).At(a.TermAs[Set[Fun[D, Nat]]]("monomials(S)")),
					module_record.ModuleAdditiveGroupDef))
			coefficients := a.Have(
				"a polynomial of S has every coefficient in the carrier",
				"∀f:((D → num) → A). f ∈ polynomial_algebra(R, S) ⇒ ∀m:(D → num). f(m) ∈ R.carrier",
				BySets(PolynomialAlgebraMember))
			multiplicative := a.Have(
				"the polynomials of S are a commutative monoid under the product, the one polynomial its identity",
				"comm_monoid_on(polynomial_algebra(R, S), polynomial_algebra_mul(R), polynomial_algebra_one(R))",
				Derive(func(b *Argument) {
					constants := b.Have(
						"the monomial of the constants, zero at every variable, is a monomial of S",
						"(λx:D. 0) ∈ monomials(S)",
						Simp(Fwd(MonomialsMember)),
						Unfold(functions.FunSupportDef),
						BySets(finite_set.FiniteRules))
					one := b.Have(
						"so the one polynomial, the generator at that monomial, is a polynomial of S",
						"polynomial_algebra_one(R) ∈ polynomial_algebra(R, S)",
						Simp(Fwd(PolynomialAlgebraOneDef), Fwd(PolynomialAlgebraDef)),
						By(constants, free_module.DeltaAtIn.Read(ring)))
					b.Show(
						"and the product is closed, commutative and associative "+
							"on the polynomials of S, the one polynomial its unit",
						Unfold(comm_monoid.CommMonoidOn),
						By(
							ring,
							one,
							coefficients,
							PolynomialAlgebraMulIn,
							PolynomialAlgebraMulComm,
							PolynomialAlgebraMulAssoc,
							PolynomialAlgebraMulOne))
				}))
			distributes := a.Have(
				"the product distributes over the sum, the sum read coefficient by coefficient",
				Statement{
					Binders: "∀f g h:((D → num) → A).",
					Hypotheses: []string{
						"f ∈ polynomial_algebra(R, S)",
						"g ∈ polynomial_algebra(R, S)",
						"h ∈ polynomial_algebra(R, S)",
					},
					Conclusion: "polynomial_algebra_mul(R, f, fun_add(g, h)) = " +
						"fun_add(polynomial_algebra_mul(R, f, g), polynomial_algebra_mul(R, f, h))",
				},
				Simp(Fwd(function_module.FunAddDef)),
				By(ring, coefficients, PolynomialAlgebraMulDistrib))
			difference := a.Have(
				"the difference is the sum of the negation, x - y = x + -y at each coefficient",
				Statement{
					Binders: "∀f g:((D → num) → A).",
					Hypotheses: []string{
						"f ∈ polynomial_algebra(R, S)",
						"g ∈ polynomial_algebra(R, S)",
					},
					Conclusion: "(λm:(D → num). f(m) - g(m)) = fun_add(f, fun_neg(g))",
				},
				Simp(Fwd(function_module.FunAddDef), Fwd(function_module.FunNegDef)),
				By(coefficients, comm_ring.SubAddNegOn.Read(ring)))
			a.Show(
				"the two structures, distributivity and the difference are the conditions of a commutative ring",
				By(
					comm_ring.CommRingOn.At(a.TermAs[RingOps[Fun[Fun[D, Nat], A]]]("polynomial_algebra_ring(R, S)")),
					additive,
					multiplicative,
					distributes,
					difference))
		}),
})}

// PolynomialAlgebraRingRestrictVariables — the ring of the polynomials of
// S is the ring of the polynomials in every variable restricted to the
// polynomials of S: the six operations of the record do not read the set
// of variables, and only the carrier does.
var PolynomialAlgebraRingRestrictVariables = polynomialAlgebraRingRestrictVariablesThm{family.Add(registry.ProofEntry{
	Name: "PolynomialAlgebraRingRestrictVariables",
	Key:  "prop_f938cf236425f528",
	Build: family.Theorem("∀R:ring_ops(A). ∀S:set(D). "+
		"    restrict_ring(polynomial_algebra_ring(R, 𝕌), polynomial_algebra(R, S)) = "+
		"    polynomial_algebra_ring(R, S)",
		func(a *Argument, R *Expr[RingOps[A]], S *Expr[Set[D]]) {
			a.Show(
				"both are the record of the same six operations with the polynomials of S as its carrier",
				Simp(Fwd(PolynomialAlgebraRingDef), Fwd(module_record.RestrictRingDef)),
				Basic())
		}),
})}

// PolynomialAlgebraConstHom — a member of the carrier is carried to
// its constant polynomial by a ring homomorphism into the polynomials
// of every set of variables. A constant c is the term c at the monomial
// of the constants, a monomial of every S, so it is a polynomial of S
// when c lies in the carrier; the constant of a sum is the sum of the
// constants coefficient by coefficient, R.zero + R.zero being R.zero; the
// constant of x * y is x times every coefficient of the constant y,
// x * R.zero being R.zero, which is the product with the constant x
// (PolynomialAlgebraConstMul); and the constant R.one and the one
// polynomial are the same generator at the monomial of the constants.
var PolynomialAlgebraConstHom = polynomialAlgebraConstHomThm{family.Add(registry.ProofEntry{
	Name: "PolynomialAlgebraConstHom",
	Key:  "prop_901044fd273be0f9",
	Reading: "The constants map into the polynomials of every S, ∅ included, " +
		"because the monomial of the constants is a monomial of every S.",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀S:set(D).",
		Hypotheses: []string{
			"comm_ring_on(R)",
		},
		Conclusion: "ring_homomorphism(R, polynomial_algebra_ring(R, S), polynomial_algebra_const(R))",
	},
		func(a *Argument, R *Expr[RingOps[A]], S *Expr[Set[D]], ring Fact) {
			zero, one := a.TermAs[A]("R.zero"), a.TermAs[A]("R.one")
			constants := a.TermAs[Fun[D, Nat]]("λx:D. 0")
			into := a.Have(
				"a constant of the carrier is a polynomial of S",
				"∀c:A. c ∈ R.carrier ⇒ polynomial_algebra_const(R, c) ∈ polynomial_algebra(R, S)",
				Derive(func(b *Argument) {
					c := b.FixAs[A]("c")
					cIn := b.Assume()
					monomial := b.Have(
						"the monomial of the constants, zero at every variable, is a monomial of S",
						"(λx:D. 0) ∈ monomials(S)",
						Simp(Fwd(MonomialsMember)),
						Unfold(functions.FunSupportDef),
						BySets(finite_set.FiniteRules))
					b.Show(
						"the constant c is the term c at that monomial, so a polynomial of S",
						Simp(Fwd(PolynomialAlgebraConstDef), Fwd(PolynomialAlgebraDef)),
						By(
							cIn,
							monomial,
							free_module.DeltaAtCoefficientIn.Read(ring).AsFact().At(
								b.TermAs[Set[Fun[D, Nat]]]("monomials(S)"), c, constants)))
				}))
			additive := a.Have(
				"the constant of a sum is the sum of the constants: x + y "+
					"at the monomial of the constants, R.zero + R.zero elsewhere",
				"∀x y:A. "+
					"    polynomial_algebra_const⟨D:D⟩(R, x + y) = "+
					"    fun_add(polynomial_algebra_const(R, x), polynomial_algebra_const(R, y))",
				StripQuant(),
				Funext(),
				Simp(Fwd(PolynomialAlgebraConstDef), Fwd(function_module.FunAddDef), Fwd(free_module.DeltaAtDef)),
				By(
					comm_ring.ZeroIn.Read(ring),
					comm_monoid.RightIdentityOn.Read(comm_ring.AddMonoidOn.Read(ring)).AsFact().At(zero)))
			multiplicative := a.Have(
				"the constant of a product is the product of the constants",
				Statement{
					Binders:    "∀x y:A.",
					Hypotheses: []string{"x ∈ R.carrier", "y ∈ R.carrier"},
					Conclusion: "polynomial_algebra_const⟨D:D⟩(R, x * y) = " +
						"polynomial_algebra_mul(R, polynomial_algebra_const(R, x), polynomial_algebra_const(R, y))",
				},
				Derive(func(b *Argument) {
					x, y := b.FixAs[A]("x"), b.FixAs[A]("y")
					members := b.Conjuncts(
						b.Assume(),
						"x lies in the carrier",
						"y lies in the carrier")
					b.Show(
						"both are x times the constant y, coefficient by coefficient",
						CalcEq(
							Leg(
								b.TermAs[Fun[Fun[D, Nat], A]]("λm:(D → num). x * polynomial_algebra_const(R, y, m)"),
								"x * y at the monomial of the constants, and x * R.zero = R.zero elsewhere",
								Funext(),
								Simp(Fwd(PolynomialAlgebraConstDef), Fwd(free_module.DeltaAtDef)),
								By(members[0], comm_ring.MulRightZeroOn.Read(ring).AsFact().At(x))),
							FinalLeg(
								"the product with the constant x scales every "+
									"coefficient by x, the constant y being a polynomial of S",
								By(
									ring,
									members[0],
									members[1],
									into.At(y),
									PolynomialAlgebraConstMul.At(
										R, S, x, b.TermAs[Fun[Fun[D, Nat], A]]("polynomial_algebra_const(R, y)")))),
						))
				}))
			a.Show(
				"both rings are commutative, the constants keep the carrier, "+
					"sums and products, and the constant R.one is the one polynomial",
				Unfold(ring_homomorphism.RingHomomorphism),
				By(
					Normalized,
					ring,
					PolynomialAlgebraCommRingOn.At(R, S),
					into,
					additive,
					multiplicative,
					PolynomialAlgebraConstDef.At[A, D](R, one),
					PolynomialAlgebraOneDef.At[A, D](R)))
		}),
})}

// PolynomialAlgebraVarIn — the variable x of S is a polynomial of S: it is
// the generator at the monomial of x, a monomial of S, and so lies in the
// free module on the monomials of S.
var PolynomialAlgebraVarIn = polynomialAlgebraVarInThm{family.Add(registry.ProofEntry{
	Name: "PolynomialAlgebraVarIn",
	Key:  "prop_fed73446354bb647",
	Reading: "x ∈ S is load-bearing except over the zero ring, where " +
		"the variable is the zero polynomial, a polynomial of every S.",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀S:set(D). ∀x:D.",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"x ∈ S",
		},
		Conclusion: "polynomial_algebra_var(R, x) ∈ polynomial_algebra(R, S)",
	},
		func(a *Argument, R *Expr[RingOps[A]], S *Expr[Set[D]], x *Expr[D], ring, xIn Fact) {
			a.Show(
				"the variable is the generator at the monomial of x, a monomial of S, so a polynomial of S",
				Simp(Fwd(PolynomialAlgebraVarDef), Fwd(PolynomialAlgebraDef)),
				By(xIn, MonomialVarIn.At(S, x), free_module.DeltaAtIn.Read(ring)))
		}),
})}

// PolynomialAlgebraSubset — more variables, more polynomials: a polynomial
// of S vanishes off the monomials of S, and these are monomials of T
// (MonomialsSubset), so it vanishes off the monomials of T.
var PolynomialAlgebraSubset = polynomialAlgebraSubsetThm{family.Add(registry.ProofEntry{
	Name:    "PolynomialAlgebraSubset",
	Key:     "prop_94f2e6cba8963033",
	Reading: "No ring hypothesis: it is the monotonicity of monomials(S) in S.",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀S T:set(D).",
		Hypotheses: []string{
			"S ⊆ T",
		},
		Conclusion: "polynomial_algebra(R, S) ⊆ polynomial_algebra(R, T)",
	},
		func(a *Argument, R *Expr[RingOps[A]], S, T *Expr[Set[D]], sub Fact) {
			a.Show(
				"the same coefficients, vanishing off the monomials "+
					"of S and so off the monomials of T, which include them",
				Simp(Fwd(PolynomialAlgebraDef), Fwd(function_module.FiniteSuppDef)),
				BySets(sub, MonomialsSubset.At(S, T)))
		}),
})}

// PolynomialAlgebraOverMono — a polynomial over a subset k of R's carrier,
// k under R's operations, is a polynomial over R: the same coefficients,
// finitely many of them nonzero, all at monomials of S, and those in k lie
// in R's carrier.
var PolynomialAlgebraOverMono = polynomialAlgebraOverMonoThm{family.Add(registry.ProofEntry{
	Name: "PolynomialAlgebraOverMono",
	Key:  "prop_f0487e9570c92a4b",
	Build: family.Theorem(Statement{
		Binders:    "∀R:ring_ops(A). ∀k:set(A). ∀S:set(D).",
		Hypotheses: []string{"k ⊆ R.carrier"},
		Conclusion: "polynomial_algebra(restrict_ring(R, k), S) ⊆ polynomial_algebra(R, S)",
	},
		func(a *Argument, R *Expr[RingOps[A]], k *Expr[Set[A]], S *Expr[Set[D]], inCarrier Fact) {
			a.Show(
				"the same coefficients, their values in k and so in R's carrier",
				Unfold(set_basic.SubsetDef),
				Simp(Fwd(PolynomialAlgebraMember)),
				BySets(inCarrier))
		}),
})}

// PolynomialAlgebraMulRestrict — polynomials over R restricted to a subset
// k of its carrier multiply as polynomials over R: the product reads the
// sum, zero and product of the coefficients, which restricting keeps.
var PolynomialAlgebraMulRestrict = polynomialAlgebraMulRestrictThm{family.Add(registry.ProofEntry{
	Name: "PolynomialAlgebraMulRestrict",
	Key:  "prop_6ab580fdef964d7c",
	Build: family.Theorem("∀R:ring_ops(A). ∀k:set(A). ∀f g:((D → num) → A). "+
		"    polynomial_algebra_mul(restrict_ring(R, k), f, g) = polynomial_algebra_mul(R, f, g)",
		func(a *Argument, R *Expr[RingOps[A]], k *Expr[Set[A]], f, g *Arrow[Fun[D, Nat], A]) {
			a.Show(
				"both products are the one convolution of the coefficients",
				Funext(),
				Simp(Fwd(PolynomialAlgebraMulDef)),
				Basic())
		}),
})}

// PolynomialAlgebraOneRestrict — the one polynomial over R restricted to a
// subset k of its carrier is the one polynomial over R: R's zero and one at
// the monomial of the constants, which restricting keeps.
var PolynomialAlgebraOneRestrict = polynomialAlgebraOneRestrictThm{family.Add(registry.ProofEntry{
	Name: "PolynomialAlgebraOneRestrict",
	Key:  "prop_ff4c3ca99cf5e7ee",
	Build: family.Theorem("∀R:ring_ops(A). ∀k:set(A). "+
		"    polynomial_algebra_one⟨D:D⟩(restrict_ring(R, k)) = polynomial_algebra_one(R)",
		func(a *Argument, R *Expr[RingOps[A]], k *Expr[Set[A]]) {
			a.Show(
				"both are the generator at the monomial of the constants",
				Simp(Fwd(PolynomialAlgebraOneDef)),
				Basic())
		}),
})}

// PolynomialAlgebraConstRestrict — the constant polynomial c over R
// restricted to a subset k of its carrier is the constant c over R: c at the
// monomial of the constants and R's zero elsewhere, which restricting keeps.
var PolynomialAlgebraConstRestrict = polynomialAlgebraConstRestrictThm{family.Add(registry.ProofEntry{
	Name: "PolynomialAlgebraConstRestrict",
	Key:  "prop_1e5722e128394591",
	Build: family.Theorem("∀R:ring_ops(A). ∀k:set(A). ∀c:A. "+
		"    polynomial_algebra_const⟨D:D⟩(restrict_ring(R, k), c) = polynomial_algebra_const(R, c)",
		func(a *Argument, R *Expr[RingOps[A]], k *Expr[Set[A]], c *Expr[A]) {
			a.Show(
				"both are c at the monomial of the constants",
				Simp(Fwd(PolynomialAlgebraConstDef)),
				Basic())
		}),
})}

// PolynomialAlgebraInclusionHom — for a subset k of R's carrier on which
// R's operations are a commutative ring, the polynomials over k include into
// those over R as a ring homomorphism: a polynomial over k is one over R
// (PolynomialAlgebraOverMono), and the two rings share the sum, and the
// product and the one by the restriction laws.
var PolynomialAlgebraInclusionHom = polynomialAlgebraInclusionHomThm{family.Add(registry.ProofEntry{
	Name: "PolynomialAlgebraInclusionHom",
	Key:  "prop_e6907bf5eacb8138",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀k:set(A). ∀S:set(D).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"k ⊆ R.carrier",
			"comm_ring_on(restrict_ring(R, k))",
		},
		Conclusion: "ring_homomorphism(polynomial_algebra_ring(restrict_ring(R, k), S), " +
			"    polynomial_algebra_ring(R, S), " +
			"    λf:((D → num) → A). f)",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			k *Expr[Set[A]],
			S *Expr[Set[D]],
			ring, inCarrier, subring Fact,
		) {
			restricted := a.TermAs[RingOps[A]]("restrict_ring(R, k)")
			a.Show(
				"a polynomial over k is one over R, under the same sum, product and one",
				Simp(
					Fwd(ring_homomorphism.RingHomomorphism),
					Fwd(PolynomialAlgebraMulRestrict),
					Fwd(PolynomialAlgebraOneRestrict)),
				By(
					inCarrier,
					PolynomialAlgebraCommRingOn.At(restricted, S),
					subring,
					PolynomialAlgebraCommRingOn.At(R, S),
					ring,
					PolynomialAlgebraOverMono.At(R, k, S),
					set_basic.SubsetDef))
		}),
})}

// PolynomialAlgebraMapHomomorphism — carrying the coefficients of polynomials
// along a ring homomorphism f is a ring homomorphism of the polynomial rings
// in the same variables. f keeps zero, so a carried polynomial is supported
// where the polynomial is; a sum is read at each coefficient; a coefficient
// of a product is a finite sum, over the monomials below m, of products of
// coefficients, through which f passes; and the one polynomial is one at the
// constant monomial and zero elsewhere. PolynomialAlgebraInclusionHom, above,
// is the case of f the identity, read from a subring k into R.
var PolynomialAlgebraMapHomomorphism = polynomialAlgebraMapHomomorphismThm{family.Add(registry.ProofEntry{
	Name: "PolynomialAlgebraMapHomomorphism",
	Key:  "prop_803d632297bc1755",
	Build: family.Theorem(Statement{
		Binders:    "∀R:ring_ops(A). ∀T:ring_ops(B). ∀f:(A → B). ∀S:set(D).",
		Hypotheses: []string{"ring_homomorphism(R, T, f)"},
		Conclusion: "ring_homomorphism(polynomial_algebra_ring(R, S), " +
			"    polynomial_algebra_ring(T, S), " +
			"    λP:((D → num) → A). λm:(D → num). f(P(m)))",
		Abbrev: Abbrev{
			{Name: "productTerms", Text: "λP:((D → num) → A). " +
				"λQ:((D → num) → A). " +
				"λm:(D → num). " +
				"λm₁:(D → num). " +
				"    R.mul(P(m₁), Q(λx:D. m(x) - m₁(x)))"},
		},
	}, func(
		a *Argument,
		R *Expr[RingOps[A]],
		T *Expr[RingOps[B]],
		f *Arrow[A, B],
		S *Expr[Set[D]],
		hom ring_homomorphism.RingHomomorphismFact[on.R, on.T],
	) {
		type polynomial = Fun[Fun[D, Nat], A]
		type carriedPolynomial = Fun[Fun[D, Nat], B]
		source := ring_homomorphism.Source.Read(hom)
		target := ring_homomorphism.Target.Read(hom)
		into := a.Have(
			"a carried polynomial is a polynomial over T",
			Statement{
				Binders: "∀P:((D → num) → A).",
				Hypotheses: []string{
					"P ∈ polynomial_algebra(R, S)",
				},
				Conclusion: "(λm:(D → num). f(P(m))) ∈ polynomial_algebra(T, S)",
			},
			Derive(func(b *Argument) {
				P := b.FixAs[polynomial]("P")
				member := b.Assume()
				support := b.Have(
					"f keeps zero, so the carried polynomial is supported where P is",
					"fun_support(T.zero, λm:(D → num). f(P(m))) ⊆ fun_support(R.zero, P)",
					BySets(ring_homomorphism.MapZero.Read(hom)))
				b.Show(
					"finitely supported on the monomials of S, with its coefficients f(P(m)) in T",
					By(
						member,
						support,
						ring_homomorphism.MapIn.Read(hom),
						PolynomialAlgebraMember.At(R, S, P),
						PolynomialAlgebraMember.At(T, S, b.TermAs[carriedPolynomial]("λm:(D → num). f(P(m))")),
						finite_set.FiniteSubset,
						set_order.SubsetTrans))
			}))
		additive := a.Have(
			"a sum is read at each coefficient, where f is additive",
			Statement{
				Binders: "∀P Q:((D → num) → A).",
				Hypotheses: []string{
					"P ∈ polynomial_algebra(R, S)",
					"Q ∈ polynomial_algebra(R, S)",
				},
				Conclusion: "(λm:(D → num). f(fun_add(R.add, P, Q, m))) = " +
					"fun_add(T.add, λm:(D → num). f(P(m)), λm:(D → num). f(Q(m)))",
			},
			Derive(func(b *Argument) {
				P := b.FixAs[polynomial]("P")
				Q := b.FixAs[polynomial]("Q")
				members := b.Assume()
				b.Do(Simp(Fwd(function_module.FunAddDef)))
				b.Show(
					"f(P(m) + Q(m)) = f(P(m)) + f(Q(m)), both coefficients lying in R",
					By(
						members,
						ring_homomorphism.MapAdd.Read(hom),
						PolynomialAlgebraMember.At(R, S, P),
						PolynomialAlgebraMember.At(R, S, Q)))
			}))
		multiplicative := a.Have(
			"f passes through the finite sum of products of coefficients that is a coefficient of a product",
			Statement{
				Binders: "∀P Q:((D → num) → A).",
				Hypotheses: []string{
					"P ∈ polynomial_algebra(R, S)",
					"Q ∈ polynomial_algebra(R, S)",
				},
				Conclusion: "(λm:(D → num). f(polynomial_algebra_mul(R, P, Q, m))) = " +
					"polynomial_algebra_mul(T, λm:(D → num). f(P(m)), λm:(D → num). f(Q(m)))",
			},
			Derive(func(b *Argument) {
				b.FixAs[polynomial]("P")
				b.FixAs[polynomial]("Q")
				members := b.Assume()
				coefficients := b.Have(
					"the coefficients of P and Q lie in R",
					"∀m:(D → num). P(m) ∈ R.carrier ∧ Q(m) ∈ R.carrier",
					By(members, PolynomialAlgebraMember))
				b.Do(Funext())
				m := b.FixAs[Fun[D, Nat]]("m")
				b.Do(Simp(Fwd(PolynomialAlgebraMulDef)))
				b.Cases(b.Term("finite_support(0, m)"))
				b.When(
					"at a finitely supported monomial the coefficient is a finite sum over the monomials below it",
					func(c *Argument, finitely Fact) {
						below := c.TermAs[Set[Fun[D, Nat]]]("«below»")
						terms := c.TermAs[polynomial]("«productTerms»(P, Q, m)")
						sum := c.Have(
							"f carries R's additive monoid to T's, so it passes through the sum",
							"f(module_sum(R.add, R.zero, «below», «productTerms»(P, Q, m))) = "+
								"module_sum(T.add, T.zero, «below», λm₁:(D → num). f(«productTerms»(P, Q, m, m₁)))",
							By(
								coefficients,
								finitely,
								ring_homomorphism.MapZero.Read(hom),
								ring_homomorphism.MapAdd.Read(hom),
								MonomialsBelowFinite.At(m),
								comm_ring.MulIn.Read(source),
								module.ModuleSumMonoidHomomorphism.Read(comm_ring.AddMonoidOn.Read(source)).At(
									c.TermAs[Op[B]]("T.add"),
									c.TermAs[B]("T.zero"),
									f,
									below,
									terms)))
						products := c.Have(
							"and through each product of coefficients",
							"∀m₁:(D → num). f(«productTerms»(P, Q, m, m₁)) = T.mul(f(P(m₁)), f(Q(λx:D. m(x) - m₁(x))))",
							By(coefficients, ring_homomorphism.MapMul.Read(hom)))
						c.Show(
							"so f of the coefficient of the product is the "+
								"coefficient of the product of the carried polynomials",
							By(products, sum, finitely))
					})
				b.Otherwise(
					"elsewhere both coefficients are zero, and f keeps zero",
					func(c *Argument, infinitely Fact) {
						c.Show(
							"f(R.zero) = T.zero",
							By(infinitely, ring_homomorphism.MapZero.Read(hom)))
					})
			}))
		one := a.Have(
			"f keeps one and zero, so it carries the one polynomial to the one polynomial",
			"(λm:(D → num). f(polynomial_algebra_one(R, m))) = polynomial_algebra_one(T)",
			Simp(Fwd(PolynomialAlgebraOneDef), Fwd(free_module.DeltaAtDef)),
			By(ring_homomorphism.MapOne.Read(hom), ring_homomorphism.MapZero.Read(hom)))
		a.Show(
			"the polynomial rings are commutative, and carrying "+
				"coefficients keeps polynomials, sums, products and one",
			By(
				source,
				target,
				into,
				additive,
				multiplicative,
				one,
				PolynomialAlgebraCommRingOn.At(R, S),
				PolynomialAlgebraCommRingOn.At(T, S),
				ring_homomorphism.RingHomomorphism.At(
					a.TermAs[RingOps[polynomial]]("polynomial_algebra_ring(R, S)"),
					a.TermAs[RingOps[carriedPolynomial]]("polynomial_algebra_ring(T, S)"),
					a.TermAs[Fun[polynomial, carriedPolynomial]]("λP:((D → num) → A). λm:(D → num). f(P(m))"))))
	}),
})}

// PolynomialAlgebraMapIsomorphism — carrying the coefficients of
// polynomials along a ring isomorphism f is an isomorphism of the polynomial
// rings. It is a homomorphism (PolynomialAlgebraMapHomomorphism), and so is
// carrying them back along the inverse of f on R, itself a ring isomorphism.
// Two polynomials with one carried polynomial agree at every monomial, f
// being one to one on R; and a polynomial over T is carried from the
// polynomial its coefficients are carried back to, since f undoes its
// inverse on T, the image of R.
var PolynomialAlgebraMapIsomorphism = polynomialAlgebraMapIsomorphismThm{family.Add(registry.ProofEntry{
	Name: "PolynomialAlgebraMapIsomorphism",
	Key:  "prop_7bf58cc21ab86cb5",
	Build: family.Theorem(Statement{
		Binders:    "∀R:ring_ops(A). ∀T:ring_ops(B). ∀f:(A → B). ∀S:set(D).",
		Hypotheses: []string{"ring_isomorphism(R, T, f)"},
		Conclusion: "ring_isomorphism(polynomial_algebra_ring(R, S), " +
			"    polynomial_algebra_ring(T, S), " +
			"    λP:((D → num) → A). λm:(D → num). f(P(m)))",
	}, func(
		a *Argument,
		R *Expr[RingOps[A]],
		T *Expr[RingOps[B]],
		f *Arrow[A, B],
		S *Expr[Set[D]],
		iso Fact,
	) {
		type polynomial = Fun[Fun[D, Nat], A]
		type carriedPolynomial = Fun[Fun[D, Nat], B]
		parts := a.Conjuncts(
			a.Unfolded(iso, ring_homomorphism.RingIsomorphismDef),
			"f is a ring homomorphism",
			"one to one on R",
			"onto T")
		hom, oneToOne, onto := parts[0], parts[1], parts[2]
		inverse := a.TermAs[Fun[B, A]]("inverse_on(R.carrier, f)")
		polynomialsR := a.TermAs[RingOps[polynomial]]("polynomial_algebra_ring(R, S)")
		polynomialsT := a.TermAs[RingOps[carriedPolynomial]]("polynomial_algebra_ring(T, S)")
		carried := a.TermAs[Fun[polynomial, carriedPolynomial]]("λP:((D → num) → A). λm:(D → num). f(P(m))")
		inverseHom := a.Conjuncts(
			a.Unfolded(
				GroupPremises(iso, ring_homomorphism.IsomorphismInverse.At(R, T, f)),
				ring_homomorphism.RingIsomorphismDef),
			"the inverse of f on R is a ring homomorphism of T to R",
			"one to one on T",
			"onto R")[0]
		carriedHom := a.Have(
			"carrying coefficients along f is a ring homomorphism",
			"ring_homomorphism(polynomial_algebra_ring(R, S), "+
				"    polynomial_algebra_ring(T, S), "+
				"    λP:((D → num) → A). λm:(D → num). f(P(m)))",
			By(hom, PolynomialAlgebraMapHomomorphism.At(R, T, f, S)))
		backHom := a.Have(
			"and so is carrying them back along the inverse",
			"ring_homomorphism(polynomial_algebra_ring(T, S), "+
				"    polynomial_algebra_ring(R, S), "+
				"    λQ:((D → num) → B). λm:(D → num). inverse_on(R.carrier, f, Q(m)))",
			By(inverseHom, PolynomialAlgebraMapHomomorphism.At(T, R, inverse, S)))
		injective := a.Have(
			"two polynomials over R with one carried polynomial "+
				"agree at every monomial, f being one to one on R",
			"injective_on(polynomial_algebra(R, S), λP:((D → num) → A). λm:(D → num). f(P(m)))",
			Simp(Fwd(functions.InjectiveOnDef)),
			Derive(func(b *Argument) {
				P := b.FixAs[polynomial]("P")
				Q := b.FixAs[polynomial]("Q")
				given := b.Assume()
				b.Do(Funext())
				b.FixAs[Fun[D, Nat]]("m")
				b.Show(
					"f(P(m)) = f(Q(m)), with P(m) and Q(m) in R",
					By(
						oneToOne,
						given,
						PolynomialAlgebraMember.At(R, S, P),
						PolynomialAlgebraMember.At(R, S, Q),
						functions.InjectiveOnDef.At(a.TermAs[Set[A]]("R.carrier"), f)))
			}))
		undone := a.Have(
			"carrying a polynomial over T back along the inverse and then along f returns it",
			Statement{
				Binders: "∀Q:((D → num) → B).",
				Hypotheses: []string{
					"Q ∈ polynomial_algebra(T, S)",
				},
				Conclusion: "(λm:(D → num). f(inverse_on(R.carrier, f, Q(m)))) = Q",
			},
			Derive(func(b *Argument) {
				Q := b.FixAs[carriedPolynomial]("Q")
				member := b.Assume()
				b.Do(Funext())
				b.FixAs[Fun[D, Nat]]("m")
				b.Show(
					"Q(m) lies in T, the image of R under f, where f undoes its inverse",
					By(
						onto,
						member,
						PolynomialAlgebraMember.At(T, S, Q),
						functions.InverseOnRight.At(a.TermAs[Set[A]]("R.carrier"), f, b.TermAs[B]("Q(m)"))))
			}))
		image := a.Have(
			"so the carried polynomials are all the polynomials over T",
			"image(λP:((D → num) → A). λm:(D → num). f(P(m)), polynomial_algebra(R, S)) = "+
				"polynomial_algebra(T, S)",
			BySets(undone, ring_homomorphism.MapIn.Read(carriedHom), ring_homomorphism.MapIn.Read(backHom)))
		a.Show(
			"a ring homomorphism, one to one, onto the polynomials over T",
			By(
				carriedHom,
				injective,
				image,
				ring_homomorphism.RingIsomorphismDef.At(polynomialsR, polynomialsT, carried)))
	}),
})}

// ---------------------------------------------------------------------------
// The polynomials generated by the constants and the variables
// ---------------------------------------------------------------------------

// PolynomialInduction — a set of coefficient functions that holds every
// constant and is closed under sums and under multiplication by each
// variable of S holds every polynomial of S. The term c at a monomial w of
// S lies in the set by induction on the degree of w: in degree zero it is
// the constant c, and raising the exponent of a variable l of S by one
// multiplies the term by the variable l, the generator at the monomial of
// l (PolynomialAlgebraTermMul). A polynomial of S is the finite sum of its
// terms, each a polynomial of S in the set, and the polynomials of S in
// the set are a commutative monoid under the sum.
var PolynomialInduction = polynomialInductionThm{family.Add(registry.ProofEntry{
	Name: "PolynomialInduction",
	Key:  "prop_d0ffd3ac45d89665",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀S:set(D). ∀C:set((D → num) → A).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"∀a:A. a ∈ R.carrier ⇒ polynomial_algebra_const(R, a) ∈ C",
			"∀f g:((D → num) → A). f ∈ C ∧ g ∈ C ⇒ fun_add(f, g) ∈ C",
			"∀x:D. ∀f:((D → num) → A). " +
				"    x ∈ S ∧ f ∈ C ⇒ polynomial_algebra_mul(R, polynomial_algebra_var(R, x), f) ∈ C",
		},
		Conclusion: "polynomial_algebra(R, S) ⊆ C",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			S *Expr[Set[D]],
			C *Expr[Set[Fun[Fun[D, Nat], A]]],
			ring, constants, sums, variables Fact,
		) {
			type poly = Fun[Fun[D, Nat], A]
			type monomial = Fun[D, Nat]
			polynomials := a.Simplified(
				GroupPremises(ring, PolynomialAlgebraCommRingOn.At(R, S)),
				Fwd(PolynomialAlgebraRingDef))
			termIn := a.Have(
				"the term c at a monomial w of S is a polynomial of S",
				Statement{
					Binders:    "∀c:A. ∀w:(D → num).",
					Hypotheses: []string{"c ∈ R.carrier", "w ∈ monomials(S)"},
					Conclusion: "delta_at(R.zero, c, w) ∈ polynomial_algebra(R, S)",
				},
				Derive(func(b *Argument) {
					c := b.FixAs[A]("c")
					w := b.FixAs[monomial]("w")
					given := b.Conjuncts(
						b.Assume(),
						"c lies in R",
						"w is a monomial of S")
					b.Show(
						"the term c at a monomial w of S lies in the free module on the monomials of S",
						Simp(Fwd(PolynomialAlgebraDef)),
						By(
							given[0],
							given[1],
							free_module.DeltaAtCoefficientIn.Read(ring).AsFact().At(
								b.TermAs[Set[monomial]]("monomials(S)"), c, w)))
				}))
			scaling := a.Have(
				"c times the generator at w is the term c at w",
				"∀c:A. ∀w:(D → num). c ∈ R.carrier ⇒ fun_smul(c, delta_at(w)) = delta_at(R.zero, c, w)",
				Derive(func(b *Argument) {
					c := b.FixAs[A]("c")
					b.FixAs[monomial]("w")
					cIn := b.Assume()
					b.Show(
						"c·1 = c at w and c·0 = 0 elsewhere",
						Funext(),
						Simp(Fwd(function_module.FunSmulDef), Fwd(free_module.DeltaAtDef)),
						By(
							cIn,
							comm_ring.MulRightZeroOn.Read(ring).AsFact().At(c),
							comm_monoid.RightIdentityOn.Read(comm_ring.MulMonoidOn.Read(ring)).AsFact().At(c)))
				}))
			raisedTerm := a.Have(
				"raising the exponent of a variable l of S by one multiplies the term c at w by the variable l",
				Statement{
					Binders:    "∀c:A. ∀w:(D → num). ∀l:D.",
					Hypotheses: []string{"c ∈ R.carrier", "w ∈ monomials(S)", "l ∈ S"},
					Conclusion: "delta_at(R.zero, c, λx:D. w(x) + monomial_var(l, x)) = " +
						"polynomial_algebra_mul(R, polynomial_algebra_var(R, l), delta_at(R.zero, c, w))",
				},
				Derive(func(b *Argument) {
					c := b.FixAs[A]("c")
					w := b.FixAs[monomial]("w")
					l := b.FixAs[D]("l")
					given := b.Conjuncts(
						b.Assume(),
						"c lies in R",
						"w is a monomial of S",
						"l is a variable of S")
					values := b.Have(
						"the term c at w takes the values c and R.zero, both in R",
						"∀u:(D → num). delta_at(R.zero, c, w, u) ∈ R.carrier",
						Simp(Fwd(free_module.DeltaAtDef)),
						By(given[0], comm_ring.ZeroIn.Read(ring)))
					b.Do(
						Simp(
							Fwd(PolynomialAlgebraVarDef),
							Fwd(PolynomialAlgebraTermMul),
							Fwd(comm_ring.OneIn.Read(ring)),
							Fwd(values)),
						Funext())
					b.FixAs[monomial]("m")
					b.Cases(b.TermAs[Bool]("m = (λx:D. w(x) + monomial_var(l, x))"))
					b.When(
						"at m = w raised at l the coefficient is R.one · c, and the term c at w raised at l is c",
						func(d *Argument, same Fact) {
							raised := d.Have(
								"w raised at l, the sum of w and the monomial of l, monomials of S, is finitely supported",
								"finite_support(0, λx:D. w(x) + monomial_var(l, x))",
								BySets(
									given[1],
									given[2],
									MonomialsDef,
									MonomialVarIn.At(S, l),
									MonomialAddIn.At(S, w, d.TermAs[monomial]("monomial_var(l)"))))
							above := d.Have(
								"the monomial of l lies below w raised at l",
								"∀x:D. monomial_var(l, x) ≤ w(x) + monomial_var(l, x)",
								ByArith())
							rest := d.Have(
								"and taking it off again leaves w",
								"(λx:D. w(x) + monomial_var(l, x) - monomial_var(l, x)) = w",
								Funext(),
								ByArith())
							d.Do(same.Rw())
							d.Show(
								"so at m the coefficient is R.one · c, the term c at w being c at w",
								By(
									raised,
									above,
									rest,
									free_module.DeltaAtDef,
									given[0],
									comm_monoid.LeftIdentityOn.Read(comm_ring.MulMonoidOn.Read(ring)).AsFact().At(c)))
						})
					b.Otherwise(
						"at any other m the coefficient is R.zero, and so is the term c at w raised at l",
						func(d *Argument, other Fact) {
							split := d.Have(
								"the monomial of l lying below m with m − monomial_var(l) = w puts m at w raised at l",
								Statement{
									Hypotheses: []string{
										"∀x:D. monomial_var(l, x) ≤ m(x)",
										"(λx:D. m(x) - monomial_var(l, x)) = w",
									},
									Conclusion: "m = (λx:D. w(x) + monomial_var(l, x))",
								},
								Derive(func(e *Argument) {
									parts := e.Conjuncts(
										e.Assume(),
										"the monomial of l lies below m",
										"m − monomial_var(l) is w")
									pointwise := e.Have(
										"exponent by exponent, m − monomial_var(l) is w",
										"∀x:D. m(x) - monomial_var(l, x) = w(x)",
										By(Normalized, parts[1]))
									e.Show(
										"so m is w raised at l exponent by exponent",
										Funext(),
										ByArith(parts[0], pointwise))
								}))
							d.Show(
								"where the monomial of l lies below m, m − monomial_var(l) "+
									"is not w, and the coefficient is R.one · R.zero",
								By(
									other,
									split,
									free_module.DeltaAtDef,
									comm_ring.OneIn.Read(ring),
									comm_ring.MulRightZeroOn.Read(ring)))
						})
				}))
			termsInC := a.Have(
				"every term c at a monomial of S lies in C, by induction on the degree of the monomial",
				Statement{
					Binders: "∀s:num. ∀T:set(D). ∀w:(D → num). ∀c:A.",
					Hypotheses: []string{
						"finite(T)",
						"∀x:D. w(x) ≠ 0 ⇒ x ∈ T",
						"w ∈ monomials(S)",
						"sum(T, w) = s",
						"c ∈ R.carrier",
					},
					Conclusion: "delta_at(R.zero, c, w) ∈ C",
				},
				Derive(func(b *Argument) {
					b.Induct("s")
					b.Base(
						"in degree zero the monomial has no variable, and the term c at it is the constant c",
						func(d *Argument) {
							T := d.FixAs[Set[D]]("T")
							w := d.FixAs[monomial]("w")
							c := d.FixAs[A]("c")
							given := d.Conjuncts(
								d.Assume(),
								"T is finite",
								"T holds the variables of w",
								"w is a monomial of S",
								"of degree zero",
								"c lies in R")
							zero := d.Have(
								"so every exponent of w is zero",
								"w = (λx:D. 0)",
								Funext(),
								By(given[0], given[1], given[3], nat_sum.EqZero.At(T, w)))
							d.Do(zero.Rw())
							d.Show(
								"and the term c at the monomial of the constants is the constant c",
								Simp(Rev(PolynomialAlgebraConstDef)),
								By(given[4], constants.At(c)))
						})
					b.Step(
						"the term c at a monomial of degree s + 1 is the variable l times the "+
							"term c at one of degree s, for an l where its exponent is positive",
						func(d *Argument, ih Fact) {
							T := d.FixAs[Set[D]]("T")
							w := d.FixAs[monomial]("w")
							c := d.FixAs[A]("c")
							s := d.TermAs[Nat]("s")
							given := d.Conjuncts(
								d.Assume(),
								"T is finite",
								"T holds the variables of w",
								"w is a monomial of S",
								"of degree s + 1",
								"c lies in R")
							l, positive := d.ObtainAs[D](
								"some exponent of w in T is positive",
								"∃l:D. l ∈ T ∧ w(l) ≠ 0",
								By(Normalized, given[0], given[3], nat_sum.EqZero.At(T, w), peano.SucNotZero.At(s)))
							atL := d.Conjuncts(
								positive,
								"l lies in T",
								"the exponent of w at l is positive")
							inS := d.Have(
								"so l is a variable of S",
								"l ∈ S",
								By(atL[1], given[2], MonomialSupport.At(S, w)))
							restore := d.Have(
								"lowering the exponent at l by one and raising it "+
									"again restores w, its exponent at l being positive",
								"(λx:D. w(x) - monomial_var(l, x) + monomial_var(l, x)) = w",
								ByArith(atL[1], MonomialLowerRaise.At(w, l, d.TermAs[Nat]("1"))))
							lowered := d.TermAs[monomial]("λx:D. w(x) - monomial_var(l, x)")
							lMonomial := d.TermAs[monomial]("monomial_var(l)")
							overL := d.Have(
								"over {l} the exponents of the monomial of l sum to one",
								"sum({l}, monomial_var(l)) = 1",
								Simp(Fwd(nat_sum.NatSumDef), Fwd(MonomialVarDef), Fwd(free_module.DeltaAtDef)),
								By(
									nat_sum.MonoidalNatAdd,
									monoidal.Sing.At(d.TermAs[Op[Nat]]("(+)"), d.TermAs[monomial]("λy:D. COND(y = l, 1, 0)"), l)))
							offL := d.Have(
								"and in T they vanish off l",
								"{l} ⊆ T ∧ (∀y:D. y ∈ T ∧ y ∉ {l} ⇒ monomial_var(l, y) = 0)",
								BySets(atL[0], MonomialVarDef, free_module.DeltaAtDef))
							degree := d.Have(
								"so the lowered monomial has degree s",
								"sum(T, λx:D. w(x) - monomial_var(l, x)) = s",
								ByArith(
									given[0],
									restore,
									given[3],
									overL,
									offL,
									nat_sum.Superset.At(d.TermAs[Set[D]]("{l}"), T, lMonomial),
									nat_sum.Add.At(lowered, lMonomial, T)))
							below := d.Have(
								"the lowered exponents are nonzero only where those of w are",
								"∀x:D. w(x) - monomial_var(l, x) ≠ 0 ⇒ w(x) ≠ 0",
								ByArith())
							loweredMonomial := d.Have(
								"so the lowered monomial is a monomial of S",
								"(λx:D. w(x) - monomial_var(l, x)) ∈ monomials(S)",
								BySets(
									given[0],
									given[1],
									below,
									given[2],
									MonomialsMember,
									finite_set.FiniteSubset.At(d.TermAs[Set[D]]("fun_support(0, λx:D. w(x) - monomial_var(l, x))"), T)))
							loweredIn := d.Have(
								"the term c at the lowered monomial lies in C, by the induction hypothesis",
								"delta_at(R.zero, c, λx:D. w(x) - monomial_var(l, x)) ∈ C",
								By(given[0], given[1], below, degree, given[4], loweredMonomial, ih.At(T, lowered, c)))
							d.Show(
								"and the variable l times it, the term c at w, lies in C",
								By(
									restore,
									given[4],
									inS,
									loweredMonomial,
									loweredIn,
									raisedTerm.At(c, lowered, l),
									variables.At(l, d.TermAs[poly]("delta_at(R.zero, c, λx:D. w(x) - monomial_var(l, x))"))))
						})
				}))
			zeroConstant := a.Have(
				"the constant zero is the zero polynomial",
				"polynomial_algebra_const⟨D:D⟩(R, R.zero) = fun_zero",
				Simp(Fwd(PolynomialAlgebraConstDef)),
				Funext(),
				Simp(Fwd(free_module.DeltaAtDef), Fwd(function_module.FunZeroDef)),
				Basic())
			zeroIn := a.Have(
				"so the zero polynomial lies in C",
				"fun_zero ∈ C",
				By(Normalized, zeroConstant, comm_ring.ZeroIn.Read(ring), constants.At(a.TermAs[A]("R.zero"))))
			additive := comm_ring.AddMonoidOn.Read(polynomials)
			monoid := a.Have(
				"the polynomials of S in C are a commutative monoid under addition",
				"comm_monoid_on(C ∩ polynomial_algebra(R, S), fun_add, fun_zero)",
				Simp(Fwd(comm_monoid.CommMonoidOn)),
				BySets(
					sums,
					zeroIn,
					comm_monoid.IdentityIn.Read(additive),
					comm_monoid.OpIn.Read(additive),
					comm_monoid.CommOn.Read(additive),
					comm_monoid.AssocOn.Read(additive),
					comm_monoid.LeftIdentityOn.Read(additive)))
			a.Show(
				"a polynomial of S is the sum of its terms, each the term at a monomial of S",
				Unfold(set_basic.SubsetDef),
				Derive(func(b *Argument) {
					f := b.FixAs[poly]("f")
					member := b.Assume()
					support := b.TermAs[Set[monomial]]("fun_support(R.zero, f)")
					expansion := b.Have(
						"f, in the free module on the monomials of S, is the sum of its coefficients times the generators",
						"f = "+
							"module_sum(fun_add, fun_zero, fun_support(R.zero, f), λm:(D → num). fun_smul(f(m), delta_at(m)))",
						By(
							ring,
							b.Unfolded(member, PolynomialAlgebraDef),
							free_module.FreeModuleExpand.At(R, b.TermAs[Set[monomial]]("monomials(S)"), f)))
					parts := b.Conjuncts(
						b.Simplified(member, Fwd(PolynomialAlgebraMember)),
						"f has finitely many terms",
						"every monomial where f is nonzero is a monomial of S",
						"every coefficient of f lies in R")
					terms := b.Have(
						"each is the term f(m) at a monomial m of S, so a polynomial of S in C",
						Statement{
							Binders:    "∀m:(D → num).",
							Hypotheses: []string{"m ∈ fun_support(R.zero, f)"},
							Conclusion: "fun_smul(f(m), delta_at(m)) ∈ C ∩ polynomial_algebra(R, S)",
						},
						Derive(func(c *Argument) {
							m := c.FixAs[monomial]("m")
							nonzero := c.Assume()
							monomialOfS := c.Have(
								"f is nonzero at m, so m is a monomial of S",
								"m ∈ monomials(S)",
								By(nonzero, c.Unfolded(parts[1], set_basic.SubsetDef).At(m)))
							coefficientIn := parts[2].At(m)
							variablesOfM := c.TermAs[Set[D]]("fun_support(0, m)")
							coefficientOfM := c.TermAs[A]("f(m)")
							finiteVariables := c.Have(
								"m has finitely many variables",
								"finite(fun_support(0, m))",
								By(monomialOfS, MonomialSupport.At(S, m)))
							c.Do(GroupPremises(coefficientIn, scaling.At(coefficientOfM, m)).Rw())
							c.Show(
								"the term f(m) at m lies in C and is a polynomial of S",
								BySets(
									finiteVariables,
									monomialOfS,
									coefficientIn,
									termsInC.At(c.TermAs[Nat]("sum(fun_support(0, m), m)"), variablesOfM, m, coefficientOfM),
									termIn.At(coefficientOfM, m)))
						}))
					b.Show(
						"so f, the sum of its terms, lies in C",
						BySets(
							parts[0],
							terms,
							expansion,
							module.ModuleSumInMonoid.Read(monoid).At(
								support, b.TermAs[Fun[monomial, poly]]("λm:(D → num). fun_smul(f(m), delta_at(m))"))))
				}))
		}),
})}
