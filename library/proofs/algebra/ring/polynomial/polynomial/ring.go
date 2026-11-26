// ring.go — the polynomials over a ring on a set: each coefficient of a
// polynomial over c lies in c, a polynomial over a subset of c is one over
// c, a map sending the zero to a zero carries its coefficients to a
// polynomial of the same length, which a map injective
// on c keeps nonzero, and the powers of the variable and the zero
// polynomial are polynomials over c; under the pointwise sum and the
// convolution product, which keeps sequences in c, has as constant coefficient
// the product of the constant coefficients and goes to the convolution of the
// images under a ring homomorphism, the polynomials form a ring, and a module
// over the ring; a power of a polynomial is the one polynomial at zero and one more
// factor at a successor, and is over c with it; the powers of the variable
// are the basis polynomials, multiply by adding exponents, shift
// coefficients and expand every polynomial, the
// polynomials below a degree have the first powers as a basis, a scalar
// and a power pass through the product, the product distributes over a
// difference, and multiplying by a constant polynomial is scaling; and the
// binomial 1 - c x ^ d multiplies by taking differences at the shift d.

package polynomial

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/abelian_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/linear_independence"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// CoefficientIn — each coefficient of a polynomial over c lies in c:
// the definition's second half, read at one index.
var CoefficientIn = coefficientInThm{family.Add(registry.ProofEntry{
	Name: "CoefficientIn",
	Key:  "prop_ad5f1557a8fa050f",
	Build: family.Theorem(Statement{
		Binders: "∀zero:A. ∀c:set(A). ∀p:(num → A). ∀i:num.",
		Hypotheses: []string{
			"polynomial_over(zero, c, p)",
		},
		Conclusion: "p(i) ∈ c",
	},
		func(a *Argument, zero *Expr[A], c *Expr[Set[A]], p *Arrow[Nat, A], i *Expr[Nat], over Fact) {
			a.Show(
				"by the definition, every coefficient of p lies in c",
				By(over, PolynomialOverDef.At(zero, c, p)))
		}),
})}

// PolynomialOverMono — a polynomial over a subset of c is a polynomial
// over c: the same sequence, its coefficients in the larger set.
var PolynomialOverMono = polynomialOverMonoThm{family.Add(registry.ProofEntry{
	Name: "PolynomialOverMono",
	Key:  "prop_2ebe0dc31263f67d",
	Build: family.Theorem(Statement{
		Binders: "∀zero:A. ∀K c:set(A). ∀p:(num → A).",
		Hypotheses: []string{
			"K ⊆ c",
			"polynomial_over(zero, K, p)",
		},
		Conclusion: "polynomial_over(zero, c, p)",
	},
		func(a *Argument, zero *Expr[A], K, c *Expr[Set[A]], p *Arrow[Nat, A], hypotheses Fact) {
			a.Show(
				"p is a polynomial over c: the same vanishing, its coefficients in K ⊆ c",
				BySets(hypotheses, PolynomialOverDef.At(zero, K, p), PolynomialOverDef.At(zero, c, p)))
		}),
})}

// PolynomialOverMap — the coefficients of a polynomial over c, mapped
// along a map that sends c into d and the zero z to w, form a polynomial
// over d with zero w.
var PolynomialOverMap = polynomialOverMapThm{family.Add(registry.ProofEntry{
	Name: "PolynomialOverMap",
	Key:  "prop_7e1d9e4648ff6d85",
	Reading: "f(z) = w is what makes the mapped sequence vanish from some index on: " +
		"past p's length its coefficients are z, and their images must be the target's " +
		"zero. Nothing else of f is read — no operation is kept, and f need not be injective.",
	Build: family.Theorem(Statement{
		Binders: "∀f:(A → B). ∀z:A. ∀w:B. ∀c:set(A). ∀d:set(B). ∀p:(num → A).",
		Hypotheses: []string{
			"polynomial_over(z, c, p)",
			"f(z) = w",
			"∀x:A. x ∈ c ⇒ f(x) ∈ d",
		},
		Conclusion: "polynomial_over(w, d, λi:num. f(p(i)))",
	},
		func(
			a *Argument,
			f *Arrow[A, B],
			z *Expr[A],
			w *Expr[B],
			c *Expr[Set[A]],
			d *Expr[Set[B]],
			p *Arrow[Nat, A],
			over, zero, into Fact,
		) {
			definition := a.Conjuncts(
				a.Unfolded(over, PolynomialOverDef),
				"p vanishes from some index n on",
				"and every coefficient of p lies in c")
			n, bound := a.UnpackAs[Nat](definition[0], "n")
			coefficients := definition[1]
			a.Show(
				"the mapped coefficients vanish from the same n on and lie in d",
				Unfold(PolynomialOverDef),
				SplitConj(
					Case(
						"past n each mapped coefficient is f(z), which is w",
						Witness(n),
						By(zero, VecMap.At(f, z, w, proof.InhabitFrom(p, bound)))),
					Case(
						"each mapped coefficient is the image of a member of c, so lies in d",
						Derive(func(b *Argument) {
							i := b.FixAs[Nat]("i")
							b.Show(
								"p(i) lies in c",
								By(coefficients.At(i), into.At(p.Apply(i))))
						}))))
		}),
})}

// PolynomialPullBack — a polynomial over the image of a set under a map
// one-to-one on it is the image of a polynomial over the set: the chosen
// preimages of its coefficients form one, the zero going back to z.
var PolynomialPullBack = polynomialPullBackThm{family.Add(registry.ProofEntry{
	Name: "PolynomialPullBack",
	Key:  "prop_3287fc09ec012968",
	Build: family.Theorem(Statement{
		Binders: "∀ι:(A → B). ∀c:set(A). ∀z:A. ∀q:(num → B).",
		Hypotheses: []string{
			"injective_on(c, ι)",
			"z ∈ c",
			"polynomial_over(ι(z), image(ι, c), q)",
		},
		Conclusion: "∃p:(num → A). polynomial_over(z, c, p) ∧ (λn:num. ι(p(n))) = q",
	}, func(
		a *Argument,
		ι *Arrow[A, B],
		c *Expr[Set[A]],
		z *Expr[A],
		q *Arrow[Nat, B],
		injective, zeroIn, over Fact,
	) {
		a.Take(a.TermAs[Fun[Nat, A]]("λn:num. inverse_on(c, ι, q(n))"))
		a.Show(
			"the chosen preimages of the coefficients of q",
			SplitConj(
				Case(
					"form a polynomial over c: the preimage sends image(ι, c) into c and ι(z) to z",
					By(
						injective,
						zeroIn,
						over,
						PolynomialOverMap.At(
							a.TermAs[Fun[B, A]]("inverse_on(c, ι)"),
							ι.Apply(z),
							z,
							a.TermAs[Set[B]]("image(ι, c)"),
							c,
							q),
						functions.InverseOnLeft.At(c, ι, z),
						functions.InverseOnIn)),
				Case(
					"and ι carries each of them back to its coefficient",
					By(over, PolynomialOverDef, functions.InverseOnRight))))
	}),
})}

// VecMap — a map sending the zero z to w keeps a vector's length: past
// n each coefficient of p is z, and its image is f(z) = w.
var VecMap = vecMapThm{family.Add(registry.ProofEntry{
	Name: "VecMap",
	Key:  "prop_37187cffa45a13d0",
	Build: family.Theorem(Statement{
		Binders: "∀f:(A → B). ∀z:A. ∀w:B. ∀n:num. ∀p:(num → A).",
		Hypotheses: []string{
			"vec⟨n⟩(z, p)",
			"f(z) = w",
		},
		Conclusion: "vec⟨n⟩(w, λi:num. f(p(i)))",
	},
		func(
			a *Argument,
			f *Arrow[A, B],
			z *Expr[A],
			w *Expr[B],
			n *Expr[Nat],
			p *Vec[A, DimN],
			bound, zero Fact,
		) {
			tail := a.Unfolded(bound, vec_space.VecDef)
			a.Do(Unfold(vec_space.VecDef))
			i := a.FixAs[Nat]("i")
			beyond := a.Assume()
			a.Show(
				"past n, p(i) is z, which f sends to w",
				By(Normalized, tail.At(i), beyond, zero))
		}),
})}

// PolynomialMapNonzero — a map injective on c keeps a polynomial over c
// nonzero: were every mapped coefficient w = f(z), injectivity on c,
// which holds z and every coefficient of p, would make p zero.
var PolynomialMapNonzero = polynomialMapNonzeroThm{family.Add(registry.ProofEntry{
	Name: "PolynomialMapNonzero",
	Key:  "prop_7ff566addbc7b4f4",
	Build: family.Theorem(Statement{
		Binders: "∀f:(A → B). ∀z:A. ∀w:B. ∀c:set(A). ∀p:(num → A).",
		Hypotheses: []string{
			"polynomial_over(z, c, p)",
			"z ∈ c",
			"injective_on(c, f)",
			"f(z) = w",
			"p ≠ vec_zero(z)",
		},
		Conclusion: "(λi:num. f(p(i))) ≠ vec_zero(w)",
	},
		func(
			a *Argument,
			f *Arrow[A, B],
			z *Expr[A],
			w *Expr[B],
			c *Expr[Set[A]],
			p *Arrow[Nat, A],
			over, zeroIn, injective, zero, nonzero Fact,
		) {
			injectivity := a.Unfolded(injective, functions.InjectiveOnDef)
			imageZero := a.SupposeNot()
			sourceZero := a.Have(
				"then every coefficient of p is z",
				"p = vec_zero(z)",
				Funext(),
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]("i")
					b.Show(
						"p(i) and z lie in c and have the one image w, so they are equal",
						Simp(Fwd(vec_space.VecZeroDef.Inst[A]())),
						BySets(
							imageZero,
							injectivity.At(p.Apply(i), z),
							CoefficientIn.Read(over).At(i),
							zeroIn,
							zero,
							vec_space.VecZeroDef.At(w, i)))
				}))
			a.Show(
				"which p is not",
				By(Normalized, sourceZero, nonzero))
		}),
})}

// PolynomialFiniteSupport — a sequence is a polynomial over k exactly
// when finitely many of its terms are nonzero, all of them in k: a
// vector of length n vanishes from n on, and finitely many naturals lie
// in some 0 .. m.
var PolynomialFiniteSupport = polynomialFiniteSupportThm{family.Add(registry.ProofEntry{
	Name: "PolynomialFiniteSupport",
	Key:  "prop_ff964ae377a14018",
	Build: family.Theorem("∀zero:A. ∀k:set(A). ∀p:(num → A). "+
		"    polynomial_over(zero, k, p) ⇔ finite(fun_support(zero, p)) ∧ (∀i:num. p(i) ∈ k)",
		func(arg *Argument, zero *Expr[A], k *Expr[Set[A]], p *Arrow[Nat, A]) {
			support := arg.TermAs[Set[Nat]]("fun_support(zero, p)")
			below := arg.Have(
				"a vector of length n is nonzero only below n",
				"∀n:num. vec⟨n⟩(zero, p) ⇒ fun_support(zero, p) ⊆ {i:num | i < n}",
				BySets(vec_space.VecDef, nat_order.NotLessEq))
			past := arg.Have(
				"a support inside 0 .. m makes p a vector of length m + 1",
				"∀m:num. fun_support(zero, p) ⊆ 0 .. m ⇒ vec⟨suc(m)⟩(zero, p)",
				BySets(vec_space.VecDef, nat_order.SucLessEqIffLessThan, nat_order.NotLessEq))
			arg.Iff()
			arg.Forward(
				"a vector of length n has its support among the naturals below n",
				func(b *Argument, over Fact) {
					parts := b.Conjuncts(
						b.Unfolded(over, PolynomialOverDef),
						"p is a vector of some length",
						"its terms lie in k")
					n, isVec := b.UnpackAs[Nat](parts[0], "n")
					b.Show(
						"finitely many nonzero terms, all in k",
						By(
							isVec,
							parts[1],
							below.At(n),
							num_segment.FiniteBelowStrict.At(n),
							finite_set.FiniteSubset.At(support, b.TermAs[Set[Nat]]("{i:num | i < n}"))))
				})
			arg.Backward(
				"a finite support lies in some 0 .. m, past which p vanishes",
				func(b *Argument, h Fact) {
					parts := b.Conjuncts(
						h,
						"finitely many nonzero terms",
						"all of them in k")
					m, bounded := b.ObtainAs[Nat](
						"the support lies in some 0 .. m",
						"∃m:num. fun_support(zero, p) ⊆ 0 .. m",
						By(parts[0], num_segment.FiniteIffBounded.At(support)))
					b.Show(
						"p is a vector of length m + 1 with its terms in k",
						Unfold(PolynomialOverDef),
						By(past.At(m), bounded, parts[1]))
				})
		}),
})}

// BasisVectorOver — each basis_vector(k), the polynomial x ^ k, is a
// polynomial over c: its coefficients are one and zero, and every one
// past k is zero.
var BasisVectorOver = basisVectorOverThm{family.Add(registry.ProofEntry{
	Name: "BasisVectorOver",
	Key:  "prop_6baeedf5d7baf1be",
	Build: comm_ring.CommRingOn.Law("∀k:num. polynomial_over(R.carrier, basis_vector(k))",
		func(a *Argument, ring comm_ring.CommRingFact[on.R], k *Expr[Nat]) {
			zero, one, c := a.TermAs[A]("R.zero"), a.TermAs[A]("R.one"), a.TermAs[Set[A]]("R.carrier")
			coefficients := a.Have(
				"every coefficient of basis_vector(k) is one or zero, both members of c",
				"∀i:num. basis_vector(k, i) ∈ R.carrier",
				a.ForEach(func(_ *Expr[Nat]) Action {
					return Chain(Simp(Fwd(vec_space.BasisVectorDef)), By(
						comm_ring.OneIn.Read(ring),
						comm_ring.ZeroIn.Read(ring)))
				}))
			vanishes := a.Have(
				"its one entry that need not be zero is at k, below suc(k), so it vanishes from suc(k) on",
				"vec⟨suc(k)⟩(basis_vector(k))",
				By(
					vec_space.VecBasisVector.At(zero, one, a.TermAs[Nat]("suc(k)"), k),
					nat_order.LessThanSucIffLessEq.At(k, k),
					nat_order.LessEqRefl))
			a.Show(
				"vanishing from an index on with every coefficient in c, basis_vector(k) is a polynomial over c",
				By(coefficients, vanishes, PolynomialOverDef.At(zero, c, a.TermAs[Fun[Nat, A]]("basis_vector(k)"))))
		}),
})}

// VecZeroOver — the zero polynomial is a polynomial over c: it vanishes
// from 0 on, and each of its coefficients is zero, a member of c.
var VecZeroOver = vecZeroOverThm{family.Add(registry.ProofEntry{
	Name: "VecZeroOver",
	Key:  "prop_35aee94a959e27d2",
	Build: comm_ring.CommRingOn.Law("polynomial_over(R.carrier, vec_zero)",
		func(a *Argument, ring comm_ring.CommRingFact[on.R]) {
			zero, c := a.TermAs[A]("R.zero"), a.TermAs[Set[A]]("R.carrier")
			coefficients := a.Have(
				"every coefficient of vec_zero is R.zero, a member of R.carrier",
				"∀i:num. vec_zero(i) ∈ R.carrier",
				a.ForEach(func(_ *Expr[Nat]) Action {
					return Chain(Simp(Fwd(vec_space.VecZeroDef)), By(comm_ring.ZeroIn.Read(ring)))
				}))
			a.Show(
				"vanishing from 0 on with every coefficient in R.carrier, vec_zero is a polynomial over R.carrier",
				By(
					coefficients,
					vec_space.VecZero.At(zero, a.TermAs[Nat]("0")),
					PolynomialOverDef.At(zero, c, a.TermAs[Fun[Nat, A]]("vec_zero"))))
		}),
})}

// SeriesMulIn — the convolution of two sequences with every term in the
// ring's carrier has every term there: each coefficient is a finite sum of
// products of terms.
var SeriesMulIn = seriesMulInThm{family.Add(registry.ProofEntry{
	Name: "SeriesMulIn",
	Key:  "prop_9e474b032d83693f",
	Build: family.Theorem(Statement{
		Binders:    "∀R:comm_ring_on(A). ∀p q:(num → A). ∀n:num.",
		Hypotheses: []string{"∀i:num. p(i) ∈ R.carrier ∧ q(i) ∈ R.carrier"},
		Conclusion: "polynomial_mul(p, q, n) ∈ R.carrier",
	}, func(
		arg *Argument,
		ring comm_ring.CommRingFact[on.R],
		p, q *Arrow[Nat, A],
		n *Expr[Nat],
		coefficients Fact,
	) {
		arg.Show(
			"a coefficient of the product is a finite sum of products of terms",
			Simp(Fwd(PolynomialMulDef)),
			By(
				coefficients,
				comm_ring.MulIn.Read(ring),
				num_segment.FiniteBelow.At(n),
				module.ModuleSumInMonoid.Read(comm_ring.AddMonoidOn.Read(ring))))
	}),
})}

// PolynomialMulOver — the product of two polynomials over c is a
// polynomial over c. Each coefficient of the product is a finite sum of
// products of coefficients, the ring a module over itself, so it lies in
// c; and the product vanishes past the sum of the degrees
// (PolynomialMulVec).
var PolynomialMulOver = polynomialMulOverThm{family.Add(registry.ProofEntry{
	Name: "PolynomialMulOver",
	Key:  "prop_91992283d8dd7603",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀p q:(num → A).",
		Hypotheses: []string{
			"polynomial_over(R.carrier, p)",
			"polynomial_over(R.carrier, q)",
		},
		Conclusion: "polynomial_over(R.carrier, polynomial_mul(p, q))",
	},
		func(a *Argument, ring comm_ring.CommRingFact[on.R], p, q *Expr[Fun[Nat, A]], over Fact) {
			zero, c := a.TermAs[A]("R.zero"), a.TermAs[Set[A]]("R.carrier")
			coefficients := a.Have(
				"every coefficient of p and of q lies in c",
				"∀i:num. p(i) ∈ R.carrier ∧ q(i) ∈ R.carrier",
				By(over, PolynomialOverDef))
			productIn := a.Have(
				"so every coefficient of the product lies in c",
				"∀n:num. polynomial_mul(p, q, n) ∈ R.carrier",
				By(ring, coefficients, SeriesMulIn))
			vanishes := a.Have(
				"p and q vanish past their degrees, so the product vanishes past the sum of the degrees",
				"vec⟨suc(polynomial_degree(p) + polynomial_degree(q))⟩(polynomial_mul(p, q))",
				By(
					over,
					DegreeVec.At(zero, c, p),
					DegreeVec.At(zero, c, q),
					PolynomialMulVec.Read(ring).At(
						a.TermAs[Nat]("polynomial_degree(p)"), a.TermAs[Nat]("polynomial_degree(q)"), p, q)))
			a.Show(
				"vanishing past an index with every coefficient in c, the product is a polynomial over c",
				By(
					productIn,
					vanishes,
					PolynomialOverDef.At(zero, c, a.TermAs[Fun[Nat, A]]("polynomial_mul(p, q)"))))
		}),
})}

// PolynomialMulComm — the convolution product of two sequences with
// every term in c is commutative, whether or not they vanish from some
// index on. Coefficientwise: at n the reflection i ↦ n - i maps the
// indices up to n one to one onto themselves, so it reindexes the sum of
// p(i) * q(n - i) into the sum of p(n - i) * q(i), whose terms are those
// of q(i) * p(n - i) with the factors swapped.
var PolynomialMulComm = polynomialMulCommThm{family.Add(registry.ProofEntry{
	Name: "PolynomialMulComm",
	Key:  "prop_c5e85ea07c370c03",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀p q:(num → A).",
		Hypotheses: []string{
			"∀i:num. p(i) ∈ R.carrier ∧ q(i) ∈ R.carrier",
		},
		Conclusion: "polynomial_mul(p, q) = polynomial_mul(q, p)",
	},
		func(a *Argument, ring comm_ring.CommRingFact[on.R], p, q *Arrow[Nat, A], coefficients Fact) {
			products := a.Have(
				"every product of a coefficient of p by one of q lies in c",
				"∀i j:num. p(i) * q(j) ∈ R.carrier",
				By(coefficients, comm_ring.MulIn.Read(ring)))
			a.Do(Funext())
			n := a.FixAs[Nat]("n")
			reflection := a.Have(
				"i ↦ n - i keeps the indices up to n and undoes itself there",
				"∀i:num. i ≤ n ⇒ n - i ≤ n ∧ n - (n - i) = i",
				ByArith())
			onto := a.Have(
				"so it maps the indices up to n onto themselves",
				"image(λi:num. n - i, {i:num | i ≤ n}) = {i:num | i ≤ n}",
				BySets(reflection))
			oneToOne := a.Have(
				"and one to one",
				"injective_on({i:num | i ≤ n}, λi:num. n - i)",
				BySets(reflection, functions.InjectiveOnDef))
			swapped := a.Have(
				"at i ≤ n the reflected term is the term at i of the other product, its factors swapped",
				"∀i:num. i ≤ n ⇒ p(n - i) * q(n - (n - i)) = q(i) * p(n - i)",
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]("i")
					below := b.Assume()
					back := b.Have(
						"the reflection undoes itself at i",
						"n - (n - i) = i",
						By(reflection.At(i), below))
					b.Show(
						"so the term is p(n - i) * q(i), and the ring's product commutes",
						back.Rw(),
						By(coefficients, comm_monoid.CommOn.Read(comm_ring.MulMonoidOn.Read(ring))))
				}))
			indices, reflect := a.TermAs[Set[Nat]]("{i:num | i ≤ n}"), a.TermAs[Fun[Nat, Nat]]("λi:num. n - i")
			a.Show(
				"the two coefficients at n agree",
				Simp(Fwd(PolynomialMulDef)),
				CalcEq(
					Leg(
						a.TermAs[A](
							"module_sum(R.add, R.zero, image(λi:num. n - i, {i:num | i ≤ n}), λi:num. p(i) * q(n - i))"),
						"the indices up to n are their own image under the reflection",
						onto.Rw(),
						Basic()),
					Leg(
						a.TermAs[A]("module_sum(R.add, R.zero, {i:num | i ≤ n}, λi:num. p(n - i) * q(n - (n - i)))"),
						"reindex along the reflection",
						By(
							module.ModuleSumImage.Read(module.RegularModuleOn.Read(ring)).At(
								indices, reflect, a.TermAs[Fun[Nat, A]]("λi:num. p(i) * q(n - i)")),
							num_segment.FiniteBelow.At(n),
							oneToOne,
							products)),
					FinalLeg(
						"and swap the factors of each term",
						BySets(swapped, module.ModuleSumCongruence)),
				))
		}),
})}

// PolynomialMulAssoc — the convolution product is associative on
// sequences with every term in c, coefficient by coefficient. At n the
// left side is the sum over i ≤ n of p(i) times the coefficient of
// polynomial_mul(q, r) at n - i, and the right side the sum over k ≤ n of
// the coefficient of polynomial_mul(p, q) at k times r(n - k). The outer
// factor passes into each inner sum, the ring being a module over itself,
// so both sides are double sums of the products p(i) * q(j) * r(n - i - j):
// the left over i and then j ≤ n - i, the right over k and then i ≤ k with
// j = k - i. These are the two ways of summing the triangle i ≤ k ≤ n
// (ModuleSumTriangleSwap).
var PolynomialMulAssoc = polynomialMulAssocThm{family.Add(registry.ProofEntry{
	Name: "PolynomialMulAssoc",
	Key:  "prop_2b269b37d1008dd2",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀p q r:(num → A).",
		Hypotheses: []string{
			"∀i:num. p(i) ∈ R.carrier ∧ q(i) ∈ R.carrier ∧ r(i) ∈ R.carrier",
		},
		Conclusion: "polynomial_mul(p, polynomial_mul(q, r)) = polynomial_mul(polynomial_mul(p, q), r)",
	},
		func(a *Argument, ring comm_ring.CommRingFact[on.R], p, q, r *Arrow[Nat, A], coefficients Fact) {
			regular := module.RegularModuleOn.Read(ring)
			mulIn := comm_ring.MulIn.Read(ring)
			a.Do(Funext())
			n := a.FixAs[Nat]("n")
			a.Do(Simp(Fwd(PolynomialMulDef)))
			intoInner := a.Have(
				"p(i) passes into the sum over j ≤ n - i, a finite sum of members of c",
				"∀i:num. "+
					"    p(i) * module_sum(R.add, R.zero, {j:num | j ≤ n - i}, λj:num. q(j) * r(n - i - j)) = "+
					"    module_sum(R.add, R.zero, {j:num | j ≤ n - i}, λj:num. p(i) * (q(j) * r(n - i - j)))",
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]()
					b.Show(
						"a scalar distributes over a finite sum",
						By(
							coefficients,
							mulIn,
							module.ModuleSumSmul.Read(regular).AsFact().At(
								b.TermAs[Set[Nat]]("{j:num | j ≤ n - i}"),
								p.Apply(i),
								b.TermAs[Fun[Nat, A]]("λj:num. q(j) * r(n - i - j)")),
							num_segment.FiniteBelow.At(b.TermAs[Nat]("n - i"))))
				}))
			outOfInner := a.Have(
				"r(n - k) passes into the sum over i ≤ k, a finite sum of members of c",
				"∀k:num. "+
					"    module_sum(R.add, R.zero, {i:num | i ≤ k}, λi:num. p(i) * q(k - i)) * r(n - k) = "+
					"    module_sum(R.add, R.zero, {i:num | i ≤ k}, λi:num. p(i) * q(k - i) * r(n - k))",
				Derive(func(b *Argument) {
					k := b.FixAs[Nat]()
					b.Show(
						"a finite sum of scalars scales term by term",
						By(
							coefficients,
							mulIn,
							module.ModuleSumSmulRight.Read(regular).AsFact().At(
								b.TermAs[Set[Nat]]("{i:num | i ≤ k}"),
								b.TermAs[Fun[Nat, A]]("λi:num. p(i) * q(k - i)"),
								b.TermAs[A]("r(n - k)")),
							num_segment.FiniteBelow.At(k)))
				}))
			regroup := a.Have(
				"each product regroups, its indices read as i, (i + j) - i and n - (i + j)",
				"∀i j:num. p(i) * (q(j) * r(n - i - j)) = p(i) * q(i + j - i) * r(n - (i + j))",
				Derive(func(b *Argument) {
					b.FixAs[Nat]()
					b.FixAs[Nat]()
					middle := b.Have(
						"adding i and taking it away leaves j",
						"i + j - i = j",
						ByArith())
					last := b.Have(
						"taking i + j from n is taking i and then j",
						"n - (i + j) = n - i - j",
						ByArith())
					b.Show(
						"and the product of three members of c associates",
						middle.Rw(),
						last.Rw(),
						By(comm_monoid.AssocOn.Read(comm_ring.MulMonoidOn.Read(ring)), coefficients))
				}))
			triangle := a.TermAs[Fun2[Nat, Nat, A]]("λi:num. λk:num. p(i) * q(k - i) * r(n - k)")
			a.Show(
				"both sides sum p(i) * q(j) * r(n - i - j) over the triangle i + j ≤ n",
				CalcEq(
					Leg(
						a.TermAs[A](
							"module_sum(R.add, "+
								"    R.zero, "+
								"    {i:num | i ≤ n}, "+
								"    λi:num. "+
								"        module_sum(R.add, R.zero, {j:num | j ≤ n - i}, λj:num. p(i) * (q(j) * r(n - i - j))))"),
						"p(i) passes into each inner sum",
						By(intoInner, module.ModuleSumCongruence)),
					Leg(
						a.TermAs[A](
							"module_sum(R.add, "+
								"    R.zero, "+
								"    {i:num | i ≤ n}, "+
								"    λi:num. "+
								"        module_sum(R.add, "+
								"            R.zero, "+
								"            {j:num | j ≤ n - i}, "+
								"            λj:num. p(i) * q(i + j - i) * r(n - (i + j))))"),
						"each product regroups",
						By(regroup, module.ModuleSumCongruence)),
					Leg(
						a.TermAs[A](
							"module_sum(R.add, "+
								"    R.zero, "+
								"    {k:num | k ≤ n}, "+
								"    λk:num. module_sum(R.add, R.zero, {i:num | i ≤ k}, λi:num. p(i) * q(k - i) * r(n - k)))"),
						"the triangle i ≤ k ≤ n summed by k = i + j instead of by i",
						By(coefficients, mulIn, module.ModuleSumTriangleSwap.Read(regular).At(n, triangle))),
					FinalLeg(
						"r(n - k) leaves each inner sum",
						By(outOfInner, module.ModuleSumCongruence)),
				))
		}),
})}

// PolynomialMulLeftComm — the first two factors of a convolution product of
// three sequences with every term in c interchange: associate, commute the
// two factors, and associate back.
var PolynomialMulLeftComm = polynomialMulLeftCommThm{family.Add(registry.ProofEntry{
	Name: "PolynomialMulLeftComm",
	Key:  "prop_b51ade6ddc5ba362",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders:    "∀p q r:(num → A).",
		Hypotheses: []string{"∀i:num. p(i) ∈ R.carrier ∧ q(i) ∈ R.carrier ∧ r(i) ∈ R.carrier"},
		Conclusion: "polynomial_mul(p, polynomial_mul(q, r)) = polynomial_mul(q, polynomial_mul(p, r))",
	},
		func(arg *Argument, ring comm_ring.CommRingFact[on.R], p, q, r *Arrow[Nat, A], coefficients Fact) {
			arg.Show(
				"associate, commute the first two factors, and associate back",
				By(
					coefficients,
					PolynomialMulAssoc.Read(ring).At(p, q, r),
					PolynomialMulComm.Read(ring).At(p, q),
					PolynomialMulAssoc.Read(ring).At(q, p, r)))
		}),
})}

// PolynomialOneMul — the one polynomial basis_vector(0) is a left
// identity for the convolution product of sequences with every term in c.
// Coefficientwise: at n the one polynomial is one at the index 0 and zero
// elsewhere, so every term of the sum of basis_vector(0, i) * p(n - i)
// over i ≤ n but the one at 0 is zero, the sum is its term at 0
// (ModuleSumSingle), and that term is one * p(n) = p(n).
var PolynomialOneMul = polynomialOneMulThm{family.Add(registry.ProofEntry{
	Name: "PolynomialOneMul",
	Key:  "prop_6a02798e0e61fd0f",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀p:(num → A).",
		Hypotheses: []string{
			"∀i:num. p(i) ∈ R.carrier",
		},
		Conclusion: "polynomial_mul(basis_vector(0), p) = p",
	},
		func(a *Argument, ring comm_ring.CommRingFact[on.R], p *Arrow[Nat, A], coefficients Fact) {
			regular := module.RegularModuleOn.Read(ring)
			zero, one, c, zeroIndex :=
				a.TermAs[A]("R.zero"), a.TermAs[A]("R.one"), a.TermAs[Set[A]]("R.carrier"), a.TermAs[Nat]("0")
			oneCoefficients := a.Have(
				"every coefficient of the one polynomial lies in c, itself a polynomial over c",
				"∀i:num. basis_vector(0, i) ∈ R.carrier",
				By(
					BasisVectorOver.Read(ring).At(zeroIndex),
					PolynomialOverDef.At(zero, c, a.TermAs[Fun[Nat, A]]("basis_vector(0)"))))
			a.Do(Funext())
			n := a.FixAs[Nat]("n")
			terms := a.Have(
				"every term of the coefficient at n is a product of two members of c, so lies in c",
				"∀i:num. basis_vector(0, i) * p(n - i) ∈ R.carrier",
				By(oneCoefficients, coefficients, comm_ring.MulIn.Read(ring)))
			vanish := a.Have(
				"off the index 0 the one polynomial is R.zero, so each other term is R.zero * p(n - i) = R.zero",
				"∀i:num. i ≠ 0 ⇒ basis_vector(0, i) * p(n - i) = R.zero",
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]("i")
					off := b.Assume()
					complement := b.TermAs[Nat]("n - i")
					b.Show(
						"basis_vector(0, i) is zero, and zero times a member of c is zero",
						By(
							Normalized,
							off,
							vec_space.BasisVectorDef.At(zero, one, zeroIndex, i),
							coefficients.At(complement),
							comm_ring.MulLeftZeroOn.Read(ring).AsFact().At(p.Apply(complement))))
				}))
			zeroAmong := a.Have(
				"0 is one of the indices up to n",
				"0 ∈ {i:num | i ≤ n}",
				BySets(nat_order.ZeroLessEq.At(n)))
			unshifted := a.Have(
				"taking nothing from n leaves n",
				"n - 0 = n",
				ByArith())
			indices, term :=
				a.TermAs[Set[Nat]]("{i:num | i ≤ n}"),
				a.TermAs[Fun[Nat, A]]("λi:num. basis_vector(0, i) * p(n - i)")
			a.Show(
				"so the coefficient at n is p(n)",
				Simp(Fwd(PolynomialMulDef)),
				CalcEq(
					Leg(
						a.TermAs[A]("basis_vector(0, 0) * p(n - 0)"),
						"the terms off the index 0 vanish, so the sum over the indices up to n is its term at 0",
						By(
							terms,
							vanish,
							zeroAmong,
							num_segment.FiniteBelow.At(n),
							module.ModuleSumSingle.Read(regular).At(indices, zeroIndex, term))),
					Leg(
						a.TermAs[A]("R.one * p(n)"),
						"the one polynomial is R.one at 0, and n - 0 = n",
						By(Normalized, unshifted, vec_space.BasisVectorDef.At(zero, one, zeroIndex, zeroIndex))),
					FinalLeg(
						"one is the unit of the product",
						By(
							coefficients,
							comm_monoid.LeftIdentityOn.Read(comm_ring.MulMonoidOn.Read(ring)).AsFact().At(p.Apply(n)))),
				))
		}),
})}

// PolynomialMulDistrib — the convolution product of sequences with every
// term in c distributes over their sum. Coefficientwise: at n each term
// p(i) * (q(n - i) + r(n - i)) of the left side splits by the ring's
// distributivity, and a finite sum of sums of members of c is the sum of
// the two sums.
var PolynomialMulDistrib = polynomialMulDistribThm{family.Add(registry.ProofEntry{
	Name: "PolynomialMulDistrib",
	Key:  "prop_ada4884daedac57c",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀p q r:(num → A).",
		Hypotheses: []string{
			"∀i:num. p(i) ∈ R.carrier ∧ q(i) ∈ R.carrier ∧ r(i) ∈ R.carrier",
		},
		Conclusion: "polynomial_mul(p, q + r) = polynomial_mul(p, q) + polynomial_mul(p, r)",
	},
		func(a *Argument, ring comm_ring.CommRingFact[on.R], p, q, r *Arrow[Nat, A], coefficients Fact) {
			products := a.Have(
				"every product of a coefficient of p by one of q or of r lies in c",
				"∀i j:num. p(i) * q(j) ∈ R.carrier ∧ p(i) * r(j) ∈ R.carrier",
				By(coefficients, comm_ring.MulIn.Read(ring)))
			a.Do(Funext())
			n := a.FixAs[Nat]("n")
			splits := a.Have(
				"each term p(i) * (q(n - i) + r(n - i)) splits, as the ring's product distributes over its sum",
				"∀i:num. p(i) * (q(n - i) + r(n - i)) = p(i) * q(n - i) + p(i) * r(n - i)",
				By(coefficients, comm_ring.LeftDistribOn.Read(ring)))
			a.Show(
				"the coefficient at n of p times q + r is the sum of those of p times q and p times r",
				Simp(Fwd(PolynomialMulDef), Fwd(vec_space.VecAddDef)),
				CalcEq(
					Leg(
						a.TermAs[A](
							"module_sum(R.add, R.zero, {i:num | i ≤ n}, λi:num. p(i) * q(n - i) + p(i) * r(n - i))"),
						"split each term",
						By(splits, module.ModuleSumCongruence)),
					FinalLeg(
						"a finite sum of sums is the sum of the two sums",
						By(
							products,
							module.ModuleSumAdd.Read(module.RegularModuleOn.Read(ring)).At(
								a.TermAs[Set[Nat]]("{i:num | i ≤ n}"),
								a.TermAs[Fun[Nat, A]]("λi:num. p(i) * q(n - i)"),
								a.TermAs[Fun[Nat, A]]("λi:num. p(i) * r(n - i)")),
							num_segment.FiniteBelow.At(n))),
				))
		}),
})}

// PolynomialMulDistribLeft — the convolution product of sequences with every
// term in c distributes over a sum in its left factor: every coefficient of
// p + q lies in c, so the product commutes, and PolynomialMulDistrib is the
// law in the right factor.
var PolynomialMulDistribLeft = polynomialMulDistribLeftThm{family.Add(registry.ProofEntry{
	Name: "PolynomialMulDistribLeft",
	Key:  "prop_a20c8918a7c8917e",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders:    "∀p q r:(num → A).",
		Hypotheses: []string{"∀i:num. p(i) ∈ R.carrier ∧ q(i) ∈ R.carrier ∧ r(i) ∈ R.carrier"},
		Conclusion: "polynomial_mul(p + q, r) = polynomial_mul(p, r) + polynomial_mul(q, r)",
	},
		func(arg *Argument, ring comm_ring.CommRingFact[on.R], p, q, r *Arrow[Nat, A], coefficients Fact) {
			sumIn := arg.Have(
				"every coefficient of p + q lies in the ring",
				"∀i:num. (p + q)(i) ∈ R.carrier",
				arg.ForEach(func(_ *Expr[Nat]) Action {
					return Chain(Simp(Fwd(vec_space.VecAddDef)), By(coefficients, comm_ring.AddIn.Read(ring)))
				}))
			arg.Show(
				"commute, distribute in the right factor, and commute each product back",
				By(
					coefficients,
					sumIn,
					PolynomialMulComm.Read(ring).At(arg.TermAs[Fun[Nat, A]]("p + q"), r),
					PolynomialMulDistrib.Read(ring).At(r, p, q),
					PolynomialMulComm.Read(ring).At(r, p),
					PolynomialMulComm.Read(ring).At(r, q)))
		}),
})}

// PolynomialMulSub — the convolution product of sequences with every term
// in the ring distributes over their difference. q is q − r plus r, so p
// times q is p times q − r plus p times r (PolynomialMulDistrib); every
// coefficient of those two products is a finite sum of products of members
// of the ring, so lies in it, and coefficient by coefficient p times q − r
// is p times q less p times r.
var PolynomialMulSub = polynomialMulSubThm{family.Add(registry.ProofEntry{
	Name: "PolynomialMulSub",
	Key:  "prop_809ff9fa1d16d610",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders:    "∀p q r:(num → A).",
		Hypotheses: []string{"∀i:num. p(i) ∈ R.carrier ∧ q(i) ∈ R.carrier ∧ r(i) ∈ R.carrier"},
		Conclusion: "polynomial_mul(p, q - r) = polynomial_mul(p, q) - polynomial_mul(p, r)",
	},
		func(arg *Argument, ring comm_ring.CommRingFact[on.R], p, q, r *Arrow[Nat, A], coefficients Fact) {
			difference := arg.TermAs[Fun[Nat, A]]("q - r")
			differenceIn := arg.Have(
				"every coefficient of q − r lies in the ring",
				"∀i:num. (q - r)(i) ∈ R.carrier",
				arg.ForEach(func(_ *Expr[Nat]) Action {
					return Chain(Simp(Fwd(vec_space.VecSubDef)), By(coefficients, comm_ring.SubIn.Read(ring)))
				}))
			regroup := arg.Have(
				"q is q − r plus r, coefficient by coefficient",
				"q - r + r = q",
				Derive(func(arg *Argument) {
					arg.Do(Funext())
					i := arg.FixAs[Nat]("i")
					arg.Show(
						"a less b, plus b, is a",
						Simp(Fwd(vec_space.VecAddDef), Fwd(vec_space.VecSubDef)),
						ByArith(ring, coefficients.At(i)))
				}))
			split := arg.Have(
				"so p times q is p times q − r plus p times r",
				"polynomial_mul(p, q) = polynomial_mul(p, q - r) + polynomial_mul(p, r)",
				By(regroup, coefficients, differenceIn, PolynomialMulDistrib.Read(ring).At(p, difference, r)))
			products := arg.Have(
				"every coefficient of p times q − r and of p times r lies in the ring",
				"∀n:num. polynomial_mul(p, q - r, n) ∈ R.carrier ∧ polynomial_mul(p, r, n) ∈ R.carrier",
				By(ring, coefficients, differenceIn, SeriesMulIn))
			arg.Do(split.Rw(), Funext())
			n := arg.FixAs[Nat]("n")
			arg.Show(
				"coefficient by coefficient, a is a plus b less b",
				Simp(Fwd(vec_space.VecSubDef), Fwd(vec_space.VecAddDef)),
				ByArith(ring, arg.Simplified(products.At(n), Fwd(vec_space.VecSubDef))))
		}),
})}

// PolynomialMulSubLeft — the convolution product of sequences with every term
// in the ring distributes over a difference in its left factor: every
// coefficient of p − q lies in the ring, so the product commutes, and
// PolynomialMulSub is the law in the right factor.
var PolynomialMulSubLeft = polynomialMulSubLeftThm{family.Add(registry.ProofEntry{
	Name: "PolynomialMulSubLeft",
	Key:  "prop_ab71adde9e058f3b",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders:    "∀p q r:(num → A).",
		Hypotheses: []string{"∀i:num. p(i) ∈ R.carrier ∧ q(i) ∈ R.carrier ∧ r(i) ∈ R.carrier"},
		Conclusion: "polynomial_mul(p - q, r) = polynomial_mul(p, r) - polynomial_mul(q, r)",
	},
		func(arg *Argument, ring comm_ring.CommRingFact[on.R], p, q, r *Arrow[Nat, A], coefficients Fact) {
			differenceIn := arg.Have(
				"every coefficient of p − q lies in the ring",
				"∀i:num. (p - q)(i) ∈ R.carrier",
				arg.ForEach(func(_ *Expr[Nat]) Action {
					return Chain(Simp(Fwd(vec_space.VecSubDef)), By(coefficients, comm_ring.SubIn.Read(ring)))
				}))
			arg.Show(
				"commute, distribute in the right factor, and commute each product back",
				By(
					coefficients,
					differenceIn,
					PolynomialMulComm.Read(ring).At(arg.TermAs[Fun[Nat, A]]("p - q"), r),
					PolynomialMulSub.Read(ring).At(r, p, q),
					PolynomialMulComm.Read(ring).At(r, p),
					PolynomialMulComm.Read(ring).At(r, q)))
		}),
})}

// PolynomialMulAtZero — the constant coefficient of a convolution product
// is the product of the constant coefficients: at 0 the convolution sum runs
// over the one index 0 (ModuleSumSingle), where its term is p(0) * q(0).
var PolynomialMulAtZero = polynomialMulAtZeroThm{family.Add(registry.ProofEntry{
	Name: "PolynomialMulAtZero",
	Key:  "prop_b7b6097c984262c7",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders:    "∀p q:(num → A).",
		Hypotheses: []string{"∀i:num. p(i) ∈ R.carrier ∧ q(i) ∈ R.carrier"},
		Conclusion: "polynomial_mul(p, q, 0) = p(0) * q(0)",
	},
		func(arg *Argument, ring comm_ring.CommRingFact[on.R], p, q *Arrow[Nat, A], coefficients Fact) {
			zeroIndex := arg.TermAs[Nat]("0")
			single := arg.Have(
				"0 is an index up to 0, and the only one",
				"0 ∈ {i:num | i ≤ 0} ∧ (∀y:num. y ∈ {i:num | i ≤ 0} ∧ y ≠ 0 ⇒ p(y) * q(0 - y) = R.zero)",
				ByArith())
			term := arg.Have(
				"so the convolution sum at 0, a sum of members of the ring, is its term at 0",
				"module_sum(R.add, R.zero, {i:num | i ≤ 0}, λi:num. p(i) * q(0 - i)) = p(0) * q(0 - 0)",
				By(
					single,
					coefficients,
					comm_ring.MulIn.Read(ring),
					num_segment.FiniteBelow.At(zeroIndex),
					module.ModuleSumSingle.Read(module.RegularModuleOn.Read(ring)).At(
						arg.TermAs[Set[Nat]]("{i:num | i ≤ 0}"),
						zeroIndex,
						arg.TermAs[Fun[Nat, A]]("λi:num. p(i) * q(0 - i)"))))
			arg.Show(
				"which is p(0) * q(0)",
				Simp(Fwd(PolynomialMulDef)),
				By(term))
		}),
})}

// ConvolutionRingMap — a ring homomorphism carries the convolution of two
// sequences with every term in its source's carrier to the convolution of their
// images: it keeps the zero and sums on the carrier, so it passes through the
// finite sum at each coefficient, and it keeps the product of each term.
var ConvolutionRingMap = convolutionRingMapThm{family.Add(registry.ProofEntry{
	Name: "ConvolutionRingMap",
	Key:  "prop_9738bcc14d8a38c4",
	Build: family.Theorem(Statement{
		Binders:    "∀R:comm_ring_on(A). ∀S:comm_ring_on(B). ∀ι:(A → B). ∀p q:(num → A).",
		Hypotheses: []string{"ring_homomorphism(R, S, ι)", "∀n:num. p(n) ∈ R.carrier ∧ q(n) ∈ R.carrier"},
		Conclusion: "(λn:num. ι(polynomial_mul(p, q, n))) = " +
			"polynomial_mul(λi:num. ι(p(i)), λi:num. ι(q(i)))",
	}, func(
		a *Argument,
		R comm_ring.CommRingFact[on.R],
		S comm_ring.CommRingFact[on.S],
		ι *Arrow[A, B],
		p, q *Arrow[Nat, A],
		hom, coefficients Fact,
	) {
		a.Do(Funext())
		n := a.FixAs[Nat]("n")
		a.Do(Simp(Fwd(PolynomialMulDef)))
		additive := a.Have(
			"zero and carrier sums are preserved",
			"ι(R.zero) = S.zero ∧ (∀u v:A. u ∈ R.carrier ∧ v ∈ R.carrier ⇒ ι(R.add(u, v)) = S.add(ι(u), ι(v)))",
			By(
				hom,
				ring_homomorphism.MapZero.Read(hom),
				ring_homomorphism.RingHomomorphism.At(
					a.TermAs[module_record.RingOps[A]]("R"), a.TermAs[module_record.RingOps[B]]("S"), ι)))
		terms := a.Have(
			"each convolution term belongs to the carrier and its product is preserved",
			"∀i:num. "+
				"    p(i) ∈ R.carrier ∧ "+
				"    q(n - i) ∈ R.carrier ∧ "+
				"    R.mul(p(i), q(n - i)) ∈ R.carrier ∧ "+
				"    ι(R.mul(p(i), q(n - i))) = S.mul(ι(p(i)), ι(q(n - i)))",
			Derive(func(b *Argument) {
				i := b.FixAs[Nat]("i")
				b.Show(
					"apply multiplicativity to the two coefficients",
					By(
						coefficients,
						comm_ring.MulIn.Read(R).AsFact().At(p.Apply(i), q.Apply(b.TermAs[Nat]("n - i"))),
						ring_homomorphism.MapMul.Read(hom).AsFact().At(p.Apply(i), q.Apply(b.TermAs[Nat]("n - i")))))
			}))
		mappedSum := a.Have(
			"the homomorphism passes through the finite convolution sum",
			"ι(module_sum(R.add, R.zero, {i:num | i ≤ n}, λi:num. R.mul(p(i), q(n - i)))) = "+
				"module_sum(S.add, S.zero, {i:num | i ≤ n}, λi:num. ι(R.mul(p(i), q(n - i))))",
			By(
				terms,
				additive,
				num_segment.FiniteBelow.At(n),
				module.ModuleSumMonoidHomomorphism.Read(comm_ring.AddMonoidOn.Read(R)).At(
					a.TermAs[Fun[B, Fun[B, B]]]("S.add"),
					a.TermAs[B]("S.zero"),
					ι,
					a.TermAs[Set[Nat]]("{i:num | i ≤ n}"),
					a.TermAs[Fun[Nat, A]]("λi:num. R.mul(p(i), q(n - i))"))))
		a.Show(
			"the image convolution is the target product",
			By(
				mappedSum,
				terms,
				module.ModuleSumCongruence.At(
					a.TermAs[Fun[B, Fun[B, B]]]("S.add"),
					a.TermAs[B]("S.zero"),
					a.TermAs[Set[Nat]]("{i:num | i ≤ n}"),
					a.TermAs[Fun[Nat, B]]("λi:num. ι(R.mul(p(i), q(n - i)))"),
					a.TermAs[Fun[Nat, B]]("λi:num. S.mul(ι(p(i)), ι(q(n - i)))"))))
	}),
})}

// PolynomialRingOn — the polynomials over a ring on c form a ring on
// their set: sums and negations pointwise, the product by convolution,
// the one polynomial basis_vector(0). The additive group is the vectors'
// own at the ring on c: a sum of an m-vector and a k-vector vanishes from
// m + k on, a negation where its argument does, and each group law is
// the vector chapter's law at a ring on c, every coefficient of a
// polynomial over c lying in c. The one polynomial is a polynomial over
// c (BasisVectorOver), and the product's closure, commutativity,
// associativity, identity and distributivity are PolynomialMulOver,
// PolynomialMulComm, PolynomialMulAssoc, PolynomialOneMul and
// PolynomialMulDistrib.
var PolynomialRingOn = polynomialRingOnThm{family.Add(registry.ProofEntry{
	Name: "PolynomialRingOn",
	Key:  "prop_292353d7beebdfc",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders:    "",
		Conclusion: "comm_ring_on(polynomial_ring(R))",
	},
		func(a *Argument, ring comm_ring.CommRingFact[on.R]) {
			zero, c := a.TermAs[A]("R.zero"), a.TermAs[Set[A]]("R.carrier")
			coefficients := a.Have(
				"a polynomial over c has every coefficient in c",
				"∀p:(num → A). polynomial_over(R.carrier, p) ⇒ (∀i:num. p(i) ∈ R.carrier)",
				By(PolynomialOverDef))
			// The definition of a polynomial over c, read forward for its
			// other half, that a polynomial vanishes from some index on, and
			// backward, from the two halves to a polynomial over c.
			vanishes := a.Have(
				"a polynomial over c vanishes from some index on",
				"∀p:(num → A). polynomial_over(R.carrier, p) ⇒ ∃m:num. vec⟨m⟩(p)",
				a.ForEach(func(p *Expr[Fun[Nat, A]]) Action { return By(PolynomialOverDef.At(zero, c, p)) }))
			over := a.Have(
				"a sequence vanishing from some index on, with every coefficient in c, is a polynomial over c",
				"∀p:(num → A). ∀n:num. vec⟨n⟩(p) ∧ (∀i:num. p(i) ∈ R.carrier) ⇒ polynomial_over(R.carrier, p)",
				a.ForEach(func(p *Expr[Fun[Nat, A]]) Action {
					return By(Normalized, PolynomialOverDef.At(zero, c, p))
				}))
			additive := a.Have(
				"the polynomials over c are an abelian group under +, index by index",
				"abelian_group_on(mk_group(vec_add, vec_zero, vec_neg, «polynomialRingCarrier»))",
				Derive(func(b *Argument) {
					zeroCoefficients := b.Have(
						"every coefficient of the zero sequence is zero, a member of c",
						"∀i:num. vec_zero(i) ∈ R.carrier",
						b.ForEach(func(_ *Expr[Nat]) Action {
							return Chain(Simp(Fwd(vec_space.VecZeroDef)), By(comm_ring.ZeroIn.Read(ring)))
						}))
					zeroOver := b.Have(
						"the zero sequence is a polynomial over c, vanishing from 0 on",
						"polynomial_over(R.carrier, vec_zero)",
						By(over, vec_space.VecZero.At(zero, b.TermAs[Nat]("0")), zeroCoefficients))
					sumOver := b.Have(
						"a sum of polynomials over c is one",
						Statement{
							Binders: "∀p q:(num → A).",
							Hypotheses: []string{
								"polynomial_over(R.carrier, p)",
								"polynomial_over(R.carrier, q)",
							},
							Conclusion: "polynomial_over(R.carrier, p + q)",
						},
						Derive(func(d *Argument) {
							p := d.FixAs[Fun[Nat, A]]()
							q := d.FixAs[Fun[Nat, A]]()
							both := d.Assume()
							m, pVec := d.ObtainAs[Nat](
								"p vanishes from some m on",
								"∃m:num. vec⟨m⟩(p)",
								By(vanishes.At(p), both))
							k, qVec := d.ObtainAs[Nat](
								"q vanishes from some k on",
								"∃k:num. vec⟨k⟩(q)",
								By(vanishes.At(q), both))
							mk := d.TermAs[Nat]("m + k")
							pPast := d.Have(
								"so p vanishes from m + k on",
								"vec⟨m + k⟩(p)",
								By(pVec, nat_order.LessEqAdd.At(m, k), vec_space.VecMono.At(zero, m, mk, p)))
							qPast := d.Have(
								"and so does q",
								"vec⟨m + k⟩(q)",
								By(qVec, nat_order.LessEqAddLeft.At(m, k), vec_space.VecMono.At(zero, k, mk, q)))
							sumVec := d.Have(
								"and so does p + q, a sum of two (m + k)-vectors",
								"vec⟨m + k⟩(p + q)",
								By(pPast, qPast, vec_space.VecAddOn.Read(ring)))
							sumIn := d.Have(
								"each coefficient p(i) + q(i) lies in c, a sum of two of its members",
								"∀i:num.(p + q)(i) ∈ R.carrier",
								d.ForEach(func(_ *Expr[Nat]) Action {
									return Chain(Simp(Fwd(vec_space.VecAddDef)), By(coefficients, both, comm_ring.AddIn.Read(ring)))
								}))
							d.Show(
								"so p + q is a polynomial over c",
								By(over, sumVec, sumIn))
						}))
					negOver := b.Have(
						"the negation of a polynomial over c is one",
						"∀p:(num → A). polynomial_over(R.carrier, p) ⇒ polynomial_over(R.carrier, -p)",
						Derive(func(d *Argument) {
							p := d.FixAs[Fun[Nat, A]]()
							pOver := d.Assume()
							_, pVec := d.ObtainAs[Nat](
								"p vanishes from some m on",
								"∃m:num. vec⟨m⟩(p)",
								By(vanishes.At(p), pOver))
							negIn := d.Have(
								"each coefficient -p(i) lies in c, the negation of one of its members",
								"∀i:num.(-p)(i) ∈ R.carrier",
								d.ForEach(func(_ *Expr[Nat]) Action {
									return Chain(Simp(Fwd(vec_space.VecNegDef)), By(coefficients, pOver, comm_ring.NegIn.Read(ring)))
								}))
							d.Show(
								"-p vanishes from m on too, so it is a polynomial over c",
								By(over, pVec, vec_space.VecNegOn.Read(ring), negIn))
						}))
					associates := b.Have(
						"+ associates, as it does on sequences with coefficients in c",
						Statement{
							Binders: "∀p q r:(num → A).",
							Hypotheses: []string{
								"polynomial_over(R.carrier, p)",
								"polynomial_over(R.carrier, q)",
								"polynomial_over(R.carrier, r)",
							},
							Conclusion: "p + (q + r) = p + q + r",
						},
						By(coefficients, vec_space.AddAssocOn.Read(ring)))
					leftZero := b.Have(
						"the zero sequence is a left identity",
						"∀p:(num → A). polynomial_over(R.carrier, p) ⇒ vec_zero + p = p",
						By(coefficients, vec_space.AddLeftZeroOn.Read(ring)))
					leftNeg := b.Have(
						"-p is a left inverse of p",
						"∀p:(num → A). polynomial_over(R.carrier, p) ⇒ -p + p = vec_zero",
						By(coefficients, vec_space.AddLeftNegOn.Read(ring)))
					commutes := b.Have(
						"+ commutes",
						"∀p q:(num → A). polynomial_over(R.carrier, p) ∧ polynomial_over(R.carrier, q) ⇒ p + q = q + p",
						By(coefficients, vec_space.AddCommOn.Read(ring)))
					b.Show(
						"these are the conditions of an abelian group on the polynomials over c",
						Unfold(abelian_group.AbelianGroupOn),
						Unfold(group.GroupOn),
						BySets(zeroOver, sumOver, negOver, associates, leftZero, leftNeg, commutes))
				}))
			multiplicative := a.Have(
				"the polynomials over c are a commutative monoid "+
					"under the product, with the one polynomial as identity",
				"comm_monoid_on(«polynomialRingCarrier», polynomial_mul, basis_vector(0))",
				Unfold(comm_monoid.CommMonoidOn),
				BySets(
					BasisVectorOver.Read(ring),
					PolynomialMulOver.Read(ring),
					coefficients,
					PolynomialMulComm.Read(ring),
					PolynomialMulAssoc.Read(ring),
					PolynomialOneMul.Read(ring)))
			difference := a.Have(
				"p - q = p + -q, as on sequences with coefficients in R.carrier",
				"∀p q:(num → A). polynomial_over(R.carrier, p) ∧ polynomial_over(R.carrier, q) ⇒ p - q = p + -q",
				By(coefficients, vec_space.SubAddNegOn.Read(ring)))
			polynomialRing := a.TermAs[RingOps[Fun[Nat, A]]]("polynomial_ring(R)")
			ringAdditive := a.Have(
				"the polynomial ring record has the abelian additive group already proved",
				"abelian_group_on(additive_group(polynomial_ring(R)))",
				Simp(
					Fwd(module_record.AdditiveGroupDef),
					Fwd(module_record.RingAddDef),
					Fwd(module_record.RingZeroDef),
					Fwd(module_record.RingNegDef),
					Fwd(module_record.RingCarrierDef)),
				By(additive))
			a.Show(
				"the two structures, distributivity and the difference are the conditions of a commutative ring",
				BySets(
					comm_ring.CommRingOn.At(polynomialRing),
					ringAdditive,
					multiplicative,
					coefficients,
					PolynomialMulDistrib.Read(ring),
					difference))
		}),
})}

// PolynomialModuleOn — the polynomials over a ring on c form a module
// over it, scaled coefficient by coefficient. Their additive group is the
// one of the polynomial ring (PolynomialRingOn). A polynomial scaled by a
// member x of c vanishes where it does (VecSmulOn) and has its
// coefficients x * p(i) in c. Each scaling law is the vector chapter's
// law at the ring on c (SmulAddLeftOn, SmulAddRightOn, SmulMulOn,
// SmulOneOn), every coefficient of a polynomial over c lying in c.
var PolynomialModuleOn = polynomialModuleOnThm{family.Add(registry.ProofEntry{
	Name: "PolynomialModuleOn",
	Key:  "prop_f9bf945d860f6c78",
	Build: comm_ring.CommRingOn.Law(Statement{
		Conclusion: "module_on(R, «polynomialModule»(«polynomialRingCarrier»))",
		Abbrev: Abbrev{
			// The polynomials over the ring as a module record over it — the
			// vector chapter's sum, zero, negation and scaling — on a carrier,
			// and the carrier of polynomial_ring(R).
			{Name: "polynomialModule", Text: "mk_module(vec_add, vec_zero, vec_neg, vec_scalar_mul)"},
		},
	},
		func(a *Argument, ring comm_ring.CommRingFact[on.R]) {
			zero, c := a.TermAs[A]("R.zero"), a.TermAs[Set[A]]("R.carrier")
			additive := comm_ring.AddGroupOn.Read(PolynomialRingOn.Read(ring))
			additiveGroup := a.Simplified(
				abelian_group.GroupOn.Read(additive),
				Fwd(module_record.AdditiveGroupDef))
			members := a.Have(
				"the members of the set of polynomials over c are the polynomials over c",
				"∀q:(num → A). q ∈ «polynomialRingCarrier» ⇔ polynomial_over(R.carrier, q)",
				BySets())
			coefficients := a.Have(
				"a member of the set of polynomials over c has every coefficient in c",
				"∀p:(num → A). p ∈ «polynomialRingCarrier» ⇒ (∀i:num. p(i) ∈ R.carrier)",
				By(members, PolynomialOverDef))
			scaled := a.Have(
				"a polynomial over c scaled by a member of c is one",
				Statement{
					Binders: "∀x:A. ∀p:(num → A).",
					Hypotheses: []string{
						"x ∈ R.carrier",
						"polynomial_over(R.carrier, p)",
					},
					Conclusion: "polynomial_over(R.carrier, x • p)",
				},
				Derive(func(b *Argument) {
					b.FixAs[A]()
					b.FixAs[Fun[Nat, A]]()
					given := b.Conjuncts(
						b.Assume(),
						"x lies in c",
						"p is a polynomial over c")
					xIn, pOver := given[0], given[1]
					definition := b.Conjuncts(
						b.Unfolded(pOver, PolynomialOverDef),
						"p vanishes from some index on",
						"and every coefficient of p lies in c")
					_, pVec := b.UnpackAs[Nat](definition[0], "m")
					scaledVec := b.Have(
						"so x • p vanishes from m on as well, x lying in c",
						"vec⟨m⟩(x • p)",
						By(xIn, pVec, vec_space.VecSmulOn.Read(ring)))
					scaledIn := b.Have(
						"each coefficient x * p(i) is a product of two members of c, so lies in c",
						"∀i:num.(x • p)(i) ∈ R.carrier",
						Simp(Fwd(vec_space.VecScalarMulDef)),
						By(xIn, definition[1], comm_ring.MulIn.Read(ring)))
					b.Show(
						"vanishing from m on with every coefficient in c, x • p is a polynomial over c",
						By(scaledVec, scaledIn, PolynomialOverDef.At(zero, c, b.TermAs[Fun[Nat, A]]("x • p"))))
				}))
			a.Show(
				"the polynomials over c, scaled by members of c, satisfy the module laws",
				Unfold(module.ModuleOn),
				SplitConjAll(
					Case(
						"c is a ring, the hypothesis",
						By(ring)),
					Case(
						"the polynomials are the additive group of the polynomial ring",
						Simp(Fwd(module_record.ModuleAdditiveGroupDef)),
						By(additiveGroup)),
					Case(
						"addition commutes",
						By(abelian_group.CommOn.Read(additive))),
					Case(
						"a polynomial scaled by a member of c is a polynomial",
						BySets(scaled)),
					Case(
						"a scalar distributes over a sum of polynomials",
						By(coefficients, vec_space.SmulAddLeftOn.Read(ring))),
					Case(
						"a sum of scalars distributes over a polynomial",
						By(coefficients, vec_space.SmulAddRightOn.Read(ring))),
					Case(
						"scaling by a product is scaling twice",
						By(coefficients, vec_space.SmulMulOn.Read(ring))),
					Case(
						"and one fixes every polynomial",
						By(coefficients, vec_space.SmulOneOn.Read(ring))),
				))
		}),
})}

// BasisVectorMul — powers of the variable multiply by adding exponents:
// the coefficient shift for multiplication by x ^ k moves the one at j
// to j + k and leaves every other coefficient zero.
var BasisVectorMul = basisVectorMulThm{family.Add(registry.ProofEntry{
	Name: "BasisVectorMul",
	Key:  "prop_c250ec8dc0345f84",
	Build: comm_ring.CommRingOn.Law("∀j k:num. "+
		"    polynomial_mul(basis_vector(j), basis_vector(k)) = basis_vector(j + k)",
		func(a *Argument, ring comm_ring.CommRingFact[on.R], j, k *Expr[Nat]) {
			zero, one := a.TermAs[A]("R.zero"), a.TermAs[A]("R.one")
			powerCoefficients := a.Have(
				"x ^ j is a polynomial over c, so every coefficient of it lies in c",
				"∀i:num. basis_vector(j, i) ∈ R.carrier",
				By(BasisVectorOver.Read(ring).At(j), PolynomialOverDef))
			coefficients := a.Have(
				"the product and x ^ (j + k) agree at every coefficient",
				"∀n:num. polynomial_mul(basis_vector(j), basis_vector(k), n) = basis_vector(j + k, n)",
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]("n")
					shifted := b.Have(
						"multiplication by x ^ k shifts the coefficients of x ^ j",
						"polynomial_mul(basis_vector(j), basis_vector(k), n) = COND(k ≤ n, basis_vector(j, n - k), R.zero)",
						By(PolynomialMulBasisVector.Read(ring), powerCoefficients))
					b.Cases(b.Term("k ≤ n"))
					b.When(
						"at or above k, the shifted and target coefficients choose their one branch at the same index",
						func(c *Argument, atOrAbove Fact) {
							sameIndex := c.Have(
								"subtracting k reaches j exactly when n is j + k",
								"n - k = j ⇔ n = j + k",
								ByArith(atOrAbove))
							c.Show(
								"both basis coefficients have the same one and zero cases",
								By(
									atOrAbove,
									shifted,
									sameIndex,
									vec_space.BasisVectorDef.At(zero, one, j, c.TermAs[Nat]("n - k")),
									vec_space.BasisVectorDef.At(zero, one, c.TermAs[Nat]("j + k"), n)))
						})
					b.Otherwise(
						"below k, both coefficients are zero",
						func(c *Argument, below Fact) {
							off := c.Have(
								"an index below k cannot be j + k",
								"n ≠ j + k",
								ByArith(below))
							c.Show(
								"the shift vanishes and the basis vector is off its index",
								By(below, off, shifted, vec_space.BasisVectorDef.At(zero, one, c.TermAs[Nat]("j + k"), n)))
						})
				}))
			a.Show(
				"equality of every coefficient gives equality of the polynomials",
				By(coefficients))
		}),
})}

// PolynomialPowZero — the zeroth power of a sequence is the one
// polynomial: the identity of the monoid power, read through the
// definition of the power.
var PolynomialPowZero = polynomialPowZeroThm{family.Add(registry.ProofEntry{
	Name: "PolynomialPowZero",
	Key:  "prop_d4e0427e471fa4ec",
	Build: comm_ring.CommRingOn.Law("∀p:(num → A). polynomial_pow(p, 0) = basis_vector(0)",
		func(a *Argument, ring comm_ring.CommRingFact[on.R], p *Arrow[Nat, A]) {
			a.Show(
				"the zeroth power is the identity of the product",
				Simp(Fwd(PolynomialPowDef), Fwd(comm_monoid.MonoidPowDef)),
				Basic())
		}),
})}

// PolynomialPowSuc — the next power of a sequence multiplies the last one
// by the sequence once more: the recursion of the monoid power, read
// through the definition of the power.
var PolynomialPowSuc = polynomialPowSucThm{family.Add(registry.ProofEntry{
	Name: "PolynomialPowSuc",
	Key:  "prop_e0ae38cf52237da9",
	Build: comm_ring.CommRingOn.Law("∀n:num. ∀p:(num → A). "+
		"    polynomial_pow(p, suc(n)) = polynomial_mul(p, polynomial_pow(p, n))",
		func(a *Argument, ring comm_ring.CommRingFact[on.R], n *Expr[Nat], p *Arrow[Nat, A]) {
			a.Show(
				"a successor power multiplies by one more factor",
				Simp(Fwd(PolynomialPowDef), Fwd(comm_monoid.MonoidPowDef)),
				Basic())
		}),
})}

// VarPow — the n-th power of the variable x is the basis polynomial
// x ^ n: the zeroth power is the one polynomial, and each further factor
// of x moves its one up an index.
var VarPow = varPowThm{family.Add(registry.ProofEntry{
	Name: "VarPow",
	Key:  "prop_b500415afab23e56",
	Build: comm_ring.CommRingOn.Law("∀n:num. polynomial_pow(basis_vector(1), n) = basis_vector(n)",
		func(a *Argument, ring comm_ring.CommRingFact[on.R], n *Expr[Nat]) {
			a.Induct(n)
			a.Base(
				"the zeroth power is the one polynomial",
				Cite(PolynomialPowZero.Read(ring)))
			a.Step(
				"one more factor of x shifts the basis index",
				func(b *Argument, previous Fact) {
					b.Do(Simp(Fwd(PolynomialPowSuc.Read(ring)), Fwd(previous), Fwd(BasisVectorMul.Read(ring))))
					nextIndex := b.Have(
						"the next index is one plus n",
						"suc(n) = 1 + n",
						ByArith())
					b.Show(
						"the basis indices agree",
						By(Normalized, nextIndex))
				})
		}),
})}

// PolynomialPowOver — a power of a polynomial over c is over c. By
// induction on the exponent: the zeroth power is the one polynomial
// (PolynomialPowZero), and each further power multiplies the last one by
// p, a product of two polynomials over c (PolynomialPowSuc,
// PolynomialMulOver).
var PolynomialPowOver = polynomialPowOverThm{family.Add(registry.ProofEntry{
	Name: "PolynomialPowOver",
	Key:  "prop_aedd2ffe75264640",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders:    "∀n:num. ∀p:(num → A).",
		Hypotheses: []string{"polynomial_over(R.carrier, p)"},
		Conclusion: "polynomial_over(R.carrier, polynomial_pow(p, n))",
	},
		func(a *Argument, ring comm_ring.CommRingFact[on.R], n *Expr[Nat], p *Arrow[Nat, A], over Fact) {
			a.Induct(n)
			a.Base(
				"the zeroth power is the one polynomial",
				Cite(PolynomialPowZero.Read(ring)),
				By(BasisVectorOver.Read(ring).At(a.TermAs[Nat]("0"))))
			a.Step(
				"the next power multiplies the last one by p",
				func(b *Argument, previous Fact) {
					power := b.TermAs[Fun[Nat, A]]("polynomial_pow(p, n)")
					b.Show(
						"a product of two polynomials over c is over c",
						PolynomialPowSuc.Read(ring).At(n, p).Rw(),
						By(over, previous, PolynomialMulOver.Read(ring).At(p, power)))
				})
		}),
})}

// PolynomialMulBasisVector — multiplying a sequence with every term in c
// by the power x ^ s shifts its terms up by s: the coefficient at j of
// p times x ^ s is p's term at j - s, and zero below s. The coefficient is
// the sum over i ≤ j of p(i) * basis_vector(s, j - i), and a term vanishes
// unless j - i = s, the basis vector being zero off its index. When s ≤ j
// the sum is its one term at i = j - s (ModuleSumSingle), p(j - s) * one;
// when j < s no j - i reaches s, and the sum is a sum of zeros
// (ModuleSumZero).
var PolynomialMulBasisVector = polynomialMulBasisVectorThm{family.Add(registry.ProofEntry{
	Name: "PolynomialMulBasisVector",
	Reading: "The COND carries num's truncated subtraction: below s, j - s is 0, " +
		"and p(0) need not be R.zero where the coefficient is. The hypothesis puts each " +
		"p(i) in R.carrier, where p(i) * R.one = p(i) and p(i) * R.zero = R.zero hold.",
	Key: "prop_384cd5f748684f30",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀p:(num → A). ∀s j:num.",
		Hypotheses: []string{
			"∀i:num. p(i) ∈ R.carrier",
		},
		Conclusion: "polynomial_mul(p, basis_vector(s), j) = COND(s ≤ j, p(j - s), R.zero)",
	},
		func(
			a *Argument,
			ring comm_ring.CommRingFact[on.R],
			p *Arrow[Nat, A],
			s, j *Expr[Nat],
			coefficients Fact,
		) {
			regular := module.RegularModuleOn.Read(ring)
			zero, one, c := a.TermAs[A]("R.zero"), a.TermAs[A]("R.one"), a.TermAs[Set[A]]("R.carrier")
			vanish := a.Have(
				"a term p(i) * basis_vector(s, j - i) vanishes unless "+
					"j - i is s, the basis vector being zero off its index",
				"∀i:num. j - i ≠ s ⇒ p(i) * basis_vector(s, j - i) = R.zero",
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]("i")
					off := b.Assume()
					b.Show(
						"basis_vector(s, j - i) is zero, and a member of c times zero is zero",
						By(
							off,
							coefficients,
							vec_space.BasisVectorDef.At(zero, one, s, b.TermAs[Nat]("j - i")),
							comm_ring.MulRightZeroOn.Read(ring).AsFact().At(p.Apply(i))))
				}))
			indices, term :=
				a.TermAs[Set[Nat]]("{i:num | i ≤ j}"),
				a.TermAs[Fun[Nat, A]]("λi:num. p(i) * basis_vector(s, j - i)")
			finite := num_segment.FiniteBelow.At(j)
			a.Do(Simp(Fwd(PolynomialMulDef)))
			a.Cases(a.Term("s ≤ j"))
			a.When(
				"at s ≤ j the sum is its one term at j - s, p(j - s) times one",
				func(b *Argument, below Fact) {
					powerCoefficients := b.Have(
						"x ^ s is a polynomial over c, so every coefficient of it lies in c",
						"∀i:num. basis_vector(s, i) ∈ R.carrier",
						By(
							BasisVectorOver.Read(ring).At(s),
							PolynomialOverDef.At(zero, c, b.TermAs[Fun[Nat, A]]("basis_vector(s)"))))
					terms := b.Have(
						"so every term of the sum lies in c",
						"∀i:num. p(i) * basis_vector(s, j - i) ∈ R.carrier",
						By(coefficients, powerCoefficients, comm_ring.MulIn.Read(ring)))
					offIndex := b.Have(
						"every term at an index up to j other than j - s vanishes",
						"∀i:num. i ∈ {i:num | i ≤ j} ∧ i ≠ j - s ⇒ p(i) * basis_vector(s, j - i) = R.zero",
						Derive(func(d *Argument) {
							i := d.FixAs[Nat]("i")
							off := d.Assume()
							upTo := d.Have(
								"i is at most j",
								"i ≤ j",
								BySets(off))
							d.Show(
								"so j - i is not s, and the term vanishes",
								ByArith(upTo, off, vanish.At(i)))
						}))
					within := b.Have(
						"j - s is at most j",
						"j - s ≤ j",
						ByArith())
					among := b.Have(
						"so it is one of the indices of the sum",
						"j - s ∈ {i:num | i ≤ j}",
						BySets(within))
					onShift := b.Have(
						"and there j - (j - s) is s",
						"j - (j - s) = s",
						ByArith(below))
					b.Show(
						"the coefficient at j is p(j - s)",
						CalcEq(
							Leg(
								b.TermAs[A]("p(j - s) * basis_vector(s, j - (j - s))"),
								"the terms off j - s vanish, so the sum is its one term there",
								By(
									terms,
									offIndex,
									among,
									finite,
									module.ModuleSumSingle.Read(regular).At(indices, b.TermAs[Nat]("j - s"), term))),
							FinalLeg(
								"there the basis vector is at its own index, one, the unit of the product",
								By(
									Normalized,
									below,
									onShift,
									coefficients,
									vec_space.BasisVectorDef.At(zero, one, s, s),
									comm_monoid.RightIdentityOn.Read(comm_ring.MulMonoidOn.Read(ring)).AsFact().At(
										b.TermAs[A]("p(j - s)")))),
						))
				})
			a.Otherwise(
				"at j < s no j - i reaches s, and the coefficient is zero",
				func(b *Argument, above Fact) {
					every := b.Have(
						"j - i is at most j, below s, so every term vanishes",
						"∀i:num. p(i) * basis_vector(s, j - i) = R.zero",
						b.ForEach(func(i *Expr[Nat]) Action {
							return ByArith(above, vanish.At(i))
						}))
					b.Show(
						"a finite sum of zeros is zero",
						By(above, every, finite, module.ModuleSumZero.Read(regular).At(indices, term)))
				})
		}),
})}

// BinomialConvolution — multiplying a sequence f with every term in the
// ring's carrier by the binomial 1 - c x ^ d leaves at n the term f(n) less
// c times f(n - d), the subtracted term present from n = d on. The
// convolution product commutes, distributes over the difference and lets
// the scalar c out (PolynomialMulComm, PolynomialMulSub,
// PolynomialMulScalar), and multiplying f by x ^ s shifts its terms up by s
// (PolynomialMulBasisVector).
var BinomialConvolution = binomialConvolutionThm{family.Add(registry.ProofEntry{
	Name: "BinomialConvolution",
	Key:  "prop_c9e537818d6ba909",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀c:A. ∀d n:num. ∀f:(num → A).",
		Hypotheses: []string{
			"c ∈ R.carrier",
			"∀i:num. f(i) ∈ R.carrier",
		},
		Conclusion: "polynomial_mul(basis_vector(0) - c • basis_vector(d), f, n) = " +
			"f(n) + COND(d ≤ n, -(c * f(n - d)), R.zero)",
	},
		func(
			arg *Argument,
			ring comm_ring.CommRingFact[on.R],
			c *Member[A, on.R],
			d, n *Expr[Nat],
			f *Arrow[Nat, A],
			coefficients Fact,
		) {
			zeroIndex := arg.TermAs[Nat]("0")
			unit, power :=
				arg.TermAs[Fun[Nat, A]]("basis_vector(0)"), arg.TermAs[Fun[Nat, A]]("basis_vector(d)")
			scaled, binomial :=
				arg.TermAs[Fun[Nat, A]]("c • basis_vector(d)"),
				arg.TermAs[Fun[Nat, A]]("basis_vector(0) - c • basis_vector(d)")
			powers := arg.Have(
				"x ^ 0 and x ^ d are polynomials over the ring, so every coefficient of them lies in it",
				"∀i:num. basis_vector(0, i) ∈ R.carrier ∧ basis_vector(d, i) ∈ R.carrier",
				By(BasisVectorOver.Read(ring).At(zeroIndex), BasisVectorOver.Read(ring).At(d), PolynomialOverDef))
			terms := arg.Have(
				"so every coefficient of c times x ^ d, and of the binomial, lies in the ring",
				"∀i:num. "+
					"    (c • basis_vector(d))(i) ∈ R.carrier ∧ (basis_vector(0) - c • basis_vector(d))(i) ∈ R.carrier",
				arg.ForEach(func(_ *Expr[Nat]) Action {
					return Chain(Simp(Fwd(vec_space.VecSubDef), Fwd(vec_space.VecScalarMulDef)), By(
						c,
						powers,
						comm_ring.MulIn.Read(ring),
						comm_ring.SubIn.Read(ring)))
				}))
			expansion := arg.Have(
				"so the binomial times f is f times x ^ 0 less c times f times x ^ d",
				"polynomial_mul(basis_vector(0) - c • basis_vector(d), f) = "+
					"polynomial_mul(f, basis_vector(0)) - c • polynomial_mul(f, basis_vector(d))",
				CalcEq(
					Leg(
						arg.TermAs[Fun[Nat, A]]("polynomial_mul(f, basis_vector(0) - c • basis_vector(d))"),
						"the product commutes",
						By(coefficients, terms, PolynomialMulComm.Read(ring).At(binomial, f))),
					Leg(
						arg.TermAs[Fun[Nat, A]](
							"polynomial_mul(f, basis_vector(0)) - polynomial_mul(f, c • basis_vector(d))"),
						"the product distributes over the difference",
						By(coefficients, powers, terms, PolynomialMulSub.Read(ring).At(f, unit, scaled))),
					FinalLeg(
						"and c passes out of the second product",
						By(coefficients, powers, PolynomialMulScalar.Read(ring).At(c, f, power))),
				))
			shifts := arg.Have(
				"multiplying f by x ^ 0 leaves its terms, and by x ^ d shifts them up by d",
				"polynomial_mul(f, basis_vector(0), n) = f(n) ∧ "+
					"polynomial_mul(f, basis_vector(d), n) = COND(d ≤ n, f(n - d), R.zero)",
				ByArith(
					coefficients,
					PolynomialMulBasisVector.Read(ring).At(f, zeroIndex, n),
					PolynomialMulBasisVector.Read(ring).At(f, d, n)))
			arg.Do(expansion.Rw(), Simp(Fwd(vec_space.VecSubDef), Fwd(vec_space.VecScalarMulDef)))
			arg.Cases(arg.Term("d ≤ n"))
			arg.When(
				"from d on, the subtracted term is c times f(n - d)",
				func(arg *Argument, reached Fact) {
					arg.Show(
						"and subtracting it adds -(c * f(n - d))",
						ByArith(ring, c, coefficients.At(n), coefficients.At(arg.TermAs[Nat]("n - d")), shifts, reached))
				})
			arg.Otherwise(
				"below d, it is c times zero",
				func(arg *Argument, below Fact) {
					arg.Show(
						"which is zero",
						ByArith(ring, c, coefficients.At(n), shifts, below))
				})
		}),
})}

// PolynomialExpansion — an n-vector is the sum of its coefficients
// scaling the first n powers of the variable. It is the vector chapter's
// BasisExpansion with BasisCombinationAt read at a ring on c: the sum is
// the module chapter's finite sum in the module of polynomials over c,
// where the vector chapter folds over a ring on the whole type.
// Coefficientwise: reading a sequence at j keeps the zero sequence and
// carries vec_add to add, so it carries the sum of the polynomials
// p(i) • basis_vector(i) to the sum of their entries
// p(i) * basis_vector(i, j) (ModuleSumMonoidHomomorphism, at the
// polynomials' additive monoid). Below n only the term at j survives,
// p(j) * one; from n on every term vanishes, and so does p(j).
var PolynomialExpansion = polynomialExpansionThm{family.Add(registry.ProofEntry{
	Name: "PolynomialExpansion",
	Key:  "prop_b8e7fee35fde1c48",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀n:num. ∀p:(num → A).",
		Hypotheses: []string{
			"polynomial_over(R.carrier, p)",
			"vec⟨n⟩(p)",
		},
		Conclusion: "p = module_sum(vec_add, vec_zero, {i:num | i < n}, λi:num. p(i) • basis_vector(i))",
	},
		func(
			a *Argument,
			ring comm_ring.CommRingFact[on.R],
			n *Expr[Nat],
			p *Vec[A, DimN],
			hypotheses Fact,
		) {
			parts := a.Conjuncts(
				hypotheses,
				"p is a polynomial over c",
				"vanishing from n on")
			over, vanishes := parts[0], parts[1]
			moduleOfPolynomials, regular := PolynomialModuleOn.Read(ring), module.RegularModuleOn.Read(ring)
			zero, one, c := a.TermAs[A]("R.zero"), a.TermAs[A]("R.one"), a.TermAs[Set[A]]("R.carrier")
			coefficients := a.Have(
				"every coefficient of p lies in c",
				"∀i:num. p(i) ∈ R.carrier",
				By(over, PolynomialOverDef))
			scaled := a.Have(
				"each p(i) • basis_vector(i) is a polynomial over "+
					"c, a power of the variable scaled by a member of c",
				"∀i:num. p(i) • basis_vector(i) ∈ «polynomialRingCarrier»",
				BySets(coefficients, BasisVectorOver.Read(ring), module.SmulIn.Read(moduleOfPolynomials)))
			// The two sides agree at every index j.
			a.Do(Funext())
			j := a.FixAs[Nat]("j")
			basisCoefficients := a.Have(
				"the coefficient at j of each power of the variable lies in c, the power a polynomial over c",
				"∀i:num. basis_vector(i, j) ∈ R.carrier",
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]("i")
					b.Show(
						"the coefficients of a polynomial over c lie in c",
						By(
							BasisVectorOver.Read(ring).At(i),
							PolynomialOverDef.At(zero, c, b.TermAs[Fun[Nat, A]]("basis_vector(i)"))))
				}))
			entries := a.Have(
				"so each p(i) * basis_vector(i, j) lies in c",
				"∀i:num. p(i) * basis_vector(i, j) ∈ R.carrier",
				By(coefficients, basisCoefficients, comm_ring.MulIn.Read(ring)))
			offIndex := a.Have(
				"off the index j, basis_vector(i, j) is zero, and so is p(i) * basis_vector(i, j)",
				"∀i:num. i ≠ j ⇒ p(i) * basis_vector(i, j) = R.zero",
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]("i")
					off := b.Assume()
					b.Show(
						"basis_vector(i, j) is zero, and a member of c times zero is zero",
						By(
							Normalized,
							off,
							vec_space.BasisVectorDef.At(zero, one, i, j),
							coefficients.At(i),
							comm_ring.MulRightZeroOn.Read(ring).AsFact().At(b.TermAs[A]("p(i)"))))
				}))
			indices, term :=
				a.TermAs[Set[Nat]]("{i:num | i < n}"), a.TermAs[Fun[Nat, A]]("λi:num. p(i) * basis_vector(i, j)")
			finite := num_segment.FiniteBelowStrict.At(n)
			atJ := a.Have(
				"the sum over i < n of p(i) * basis_vector(i, j) is p(j)",
				"module_sum(R.add, R.zero, {i:num | i < n}, λi:num. p(i) * basis_vector(i, j)) = p(j)",
				Derive(func(b *Argument) {
					b.Cases(b.Term("j < n"))
					b.When(
						"below n only the term at j survives, and it is p(j) * one",
						func(d *Argument, below Fact) {
							among := d.Have(
								"j is one of the indices",
								"j ∈ {i:num | i < n}",
								BySets(below))
							d.Show(
								"the sum is its term at j",
								CalcEq(
									Leg(
										d.TermAs[A]("p(j) * basis_vector(j, j)"),
										"the terms off j vanish, the ring a module over itself",
										By(entries, offIndex, among, finite, module.ModuleSumSingle.Read(regular).At(indices, j, term))),
									FinalLeg(
										"basis_vector(j, j) is one, the unit of the product",
										By(
											Normalized,
											coefficients,
											vec_space.BasisVectorDef.At(zero, one, j, j),
											comm_monoid.RightIdentityOn.Read(comm_ring.MulMonoidOn.Read(ring)).AsFact().At(
												d.TermAs[A]("p(j)")))),
								))
						})
					b.Otherwise(
						"from n on every term vanishes, and so does p(j)",
						func(d *Argument, past Fact) {
							vanishing := d.Have(
								"j is no index below n, so every term of the sum is off j and vanishes",
								"∀i:num. i ∈ {i:num | i < n} ⇒ p(i) * basis_vector(i, j) = R.zero",
								BySets(past, offIndex))
							pZero := d.Have(
								"p vanishes at j, which lies at n or beyond",
								"p(j) = R.zero",
								By(past, vanishes, vec_space.VecDef.At(zero, p), nat_order.NotLessThan.At(j, n)))
							d.Show(
								"a sum of vanishing terms is zero, the ring a module over itself",
								By(vanishing, pZero, finite, module.ModuleSumZero.Read(regular).At(indices, term)))
						})
				}))
			a.Show(
				"the entry at j of the sum is p(j)",
				CalcEq(
					Leg(
						a.TermAs[A]("module_sum(R.add, R.zero, {i:num | i < n}, λi:num. p(i) * basis_vector(i, j))"),
						"p(j) is the sum over i < n of p(i) * basis_vector(i, j)",
						By(atJ)),
					Leg(
						a.TermAs[A]("module_sum(R.add, R.zero, {i:num | i < n}, λi:num.(p(i) • basis_vector(i))(j))"),
						"the entry at j of p(i) • basis_vector(i) is p(i) * basis_vector(i, j)",
						Simp(Fwd(vec_space.VecScalarMulDef)),
						Basic()),
					FinalLeg(
						"evaluation at j preserves zero and addition, so it commutes with the polynomial sum",
						By(
							scaled,
							vec_space.VecZeroDef,
							vec_space.VecAddDef,
							finite,
							module.ModuleSumMonoidHomomorphism.Read(module.AddMonoidOn.Read(moduleOfPolynomials)).At(
								a.TermAs[Op[A]]("R.add"),
								zero,
								a.TermAs[Fun[Fun[Nat, A], A]]("λq:(num → A). q(j)"),
								indices,
								a.TermAs[Fun[Nat, Fun[Nat, A]]]("λi:num. p(i) • basis_vector(i)")))),
				))
		}),
})}

// PolynomialsBelowDim — over a field, the polynomials of degree below n
// with coefficients in c are an n-dimensional vector space: the first n
// powers of the variable are a basis.
var PolynomialsBelowDim = polynomialsBelowDimThm{family.Add(registry.ProofEntry{
	Name: "PolynomialsBelowDim",
	Key:  "prop_a93db1089b0d5e34",
	Reading: "The polynomials of degree below n are the n-vectors of " +
		"the vector chapter with coefficients in c; one ≠ zero, which " +
		"the field supplies, keeps the n powers of the variable distinct.",
	Deps: []registry.EntryLike{
		PolynomialExpansion,
		PolynomialModuleOn,
		BasisVectorOver,
		module_dimension.DimBasis,
		linear_independence.ModuleBasisDef,
		linear_independence.ModuleIndependentDef,
		linear_independence.SpanCombinations,
		field.RingOn,
		field.OneNotZeroOn,
		cardinality.HasSizeImageInj,
	},
	Build: family.Card(
		field.FieldOn.Statement(
			"∀n:num. "+
				"    module_dim(field_ring(F), "+
				"        mk_module(vec_add, "+
				"            vec_zero, "+
				"            vec_neg, "+
				"            vec_scalar_mul, "+
				"            {p:(num → A) | vec⟨n⟩(p) ∧ (∀i:num. p(i) ∈ F.carrier)})) = "+
				"    n"),
		"the set is a submodule of the polynomials over c; {basis_vector(k) | k < n} lies "+
			"in it, spans it (PolynomialExpansion), is independent (a vanishing combination "+
			"is zero at each k < n, where it reads its k-th coefficient), and has n members "+
			"(k ↦ basis_vector(k) separates points as one ≠ zero, HasSizeImageInj); DimBasis"),
})}

// PolynomialMulScalar — a scalar factor of one side of a convolution
// product of sequences with every term in c comes out of the product.
// Coefficientwise: at n each term p(i) * (a * q(n - i)) is
// a * (p(i) * q(n - i)), the product of members of c commuting, and a
// member of c passes out of the finite sum of those terms, the ring a
// module over itself.
var PolynomialMulScalar = polynomialMulScalarThm{family.Add(registry.ProofEntry{
	Name: "PolynomialMulScalar",
	Key:  "prop_b782d1bdd1c5a60",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀a:A. ∀p q:(num → A).",
		Hypotheses: []string{
			"a ∈ R.carrier",
			"∀i:num. p(i) ∈ R.carrier ∧ q(i) ∈ R.carrier",
		},
		Conclusion: "polynomial_mul(p, a • q) = a • polynomial_mul(p, q)",
	},
		func(
			arg *Argument,
			ring comm_ring.CommRingFact[on.R],
			a *Expr[A],
			p, q *Arrow[Nat, A],
			hypotheses Fact,
		) {
			parts := arg.Conjuncts(
				hypotheses,
				"a lies in c",
				"every coefficient of p and of q lies in c")
			aIn, coefficients := parts[0], parts[1]
			products := arg.Have(
				"every product of a coefficient of p by one of q lies in c",
				"∀i j:num. p(i) * q(j) ∈ R.carrier",
				By(coefficients, comm_ring.MulIn.Read(ring)))
			arg.Do(Funext())
			n := arg.FixAs[Nat]("n")
			moved := arg.Have(
				"a moves to the front of each term, the product of members of c commuting",
				"∀i:num. p(i) * (a * q(n - i)) = a * (p(i) * q(n - i))",
				By(aIn, coefficients, comm_monoid.LeftCommOn.Read(comm_ring.MulMonoidOn.Read(ring))))
			arg.Show(
				"the coefficients at n agree",
				Simp(Fwd(PolynomialMulDef), Fwd(vec_space.VecScalarMulDef)),
				CalcEq(
					Leg(
						arg.TermAs[A]("module_sum(R.add, R.zero, {i:num | i ≤ n}, λi:num. a * (p(i) * q(n - i)))"),
						"move a to the front of each term",
						By(moved, module.ModuleSumCongruence)),
					FinalLeg(
						"a member of c passes out of a finite sum",
						By(
							products,
							num_segment.FiniteBelow.At(n),
							module.ModuleSumSmul.Read(module.RegularModuleOn.Read(ring)).At(
								arg.TermAs[Set[Nat]]("{i:num | i ≤ n}"),
								arg.MemberOf[on.R](a, aIn),
								arg.TermAs[Fun[Nat, A]]("λi:num. p(i) * q(n - i)")))),
				))
		}),
})}

// PolynomialMulConstant — multiplying by the constant polynomial a is
// scaling by a: a passes out of the product (PolynomialMulScalar), and p
// times the one polynomial is p.
var PolynomialMulConstant = polynomialMulConstantThm{family.Add(registry.ProofEntry{
	Name: "PolynomialMulConstant",
	Key:  "prop_9d52de185f361783",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀a:A. ∀p:(num → A).",
		Hypotheses: []string{
			"a ∈ R.carrier",
			"polynomial_over(R.carrier, p)",
		},
		Conclusion: "polynomial_mul(p, a • basis_vector(0)) = a • p",
	},
		func(
			arg *Argument,
			ring comm_ring.CommRingFact[on.R],
			a *Expr[A],
			p *Arrow[Nat, A],
			hypotheses Fact,
		) {
			parts := arg.Conjuncts(
				hypotheses,
				"a lies in c",
				"p is a polynomial over c")
			aIn, pOver := parts[0], parts[1]
			aMember, onePolynomial := arg.MemberOf[on.R](a, aIn), arg.TermAs[Fun[Nat, A]]("basis_vector(0)")
			pMember := arg.Have(
				"p lies in the ring of polynomials over c",
				"p ∈ «polynomialRingCarrier»",
				BySets(pOver))
			timesOne := arg.Have(
				"p times the one polynomial is p",
				"polynomial_mul(p, basis_vector(0)) = p",
				ByArith(PolynomialRingOn.Read(ring), pMember))
			arg.Show(
				"a passes out of the product of p and the one polynomial, which is p",
				CalcEq(
					Leg(
						arg.TermAs[Fun[Nat, A]]("a • polynomial_mul(p, basis_vector(0))"),
						"a passes out of the product",
						By(
							pOver,
							BasisVectorOver.Read(ring).At(arg.TermAs[Nat]("0")),
							PolynomialOverDef,
							PolynomialMulScalar.Read(ring).At(aMember, p, onePolynomial))),
					FinalLeg(
						"and p times the one polynomial is p",
						timesOne.Rw(),
						Basic()),
				))
		}),
})}

// ConstantPolynomialHomomorphism — taking a member a of c to the constant
// polynomial a • basis_vector(0) is a ring homomorphism from c to the
// polynomials over c. Of its six conditions the ring on c is the
// hypothesis; the others: the polynomials over c form a ring, a constant
// is a polynomial (the polynomials a module over c), scaling distributes
// over a sum of scalars, the constant of a product x * y is y • (x •
// basis_vector(0)), the constant x multiplied by the constant y
// (PolynomialMulConstant), and one scales nothing.
var ConstantPolynomialHomomorphism = constantPolynomialHomomorphismThm{family.Add(registry.ProofEntry{
	Name: "ConstantPolynomialHomomorphism",
	Key:  "prop_c8478fafb5478b2d",
	Build: comm_ring.CommRingOn.Law("ring_homomorphism(R, "+
		"    polynomial_ring(R), "+
		"    λa:A. a • basis_vector(0))",
		func(a *Argument, ring comm_ring.CommRingFact[on.R]) {
			zero, c := a.TermAs[A]("R.zero"), a.TermAs[Set[A]]("R.carrier")
			onePolynomial := a.TermAs[Fun[Nat, A]]("basis_vector(0)")
			oneOver := BasisVectorOver.Read(ring).At(a.TermAs[Nat]("0"))
			scaledIn := module.SmulIn.Read(PolynomialModuleOn.Read(ring))
			oneCoefficients := a.Have(
				"every coefficient of the one polynomial lies in c",
				"∀i:num. basis_vector(0, i) ∈ R.carrier",
				By(oneOver, PolynomialOverDef.At(zero, c, onePolynomial)))
			a.Show(
				"the constants keep the carrier, sums, products and one",
				Unfold(ring_homomorphism.RingHomomorphism),
				SplitConjAll(
					Case(
						"c is a ring, the hypothesis",
						By(ring)),
					Case(
						"the polynomials over c form a ring",
						By(PolynomialRingOn.Read(ring))),
					Case(
						"a constant polynomial is a polynomial over c, a scaled polynomial",
						BySets(oneOver, scaledIn)),
					Case(
						"the constant of a sum is the sum of the constants",
						By(oneCoefficients, vec_space.SmulAddRightOn.Read(ring))),
					Case(
						"the constant of a product is the product of the constants",
						Derive(func(b *Argument) {
							x, y := b.FixAs[A]("x"), b.FixAs[A]("y")
							members := b.Conjuncts(
								b.Assume(),
								"x lies in c",
								"y lies in c")
							xm, ym := b.MemberOf[on.R](x, members[0]), b.MemberOf[on.R](y, members[1])
							constantX := b.TermAs[Fun[Nat, A]]("x • basis_vector(0)")
							xOver := b.Have(
								"the constant x is a polynomial over c",
								"polynomial_over(R.carrier, x • basis_vector(0))",
								BySets(xm, oneOver, scaledIn))
							b.Show(
								"scaling by x * y is scaling by x, then by y, which multiplies by the constant y",
								CalcEq(
									Leg(
										b.TermAs[Fun[Nat, A]]("(y * x) • basis_vector(0)"),
										"the product of members of c commutes",
										By(Normalized, comm_monoid.CommOn.Read(comm_ring.MulMonoidOn.Read(ring)).At(xm, ym))),
									Leg(
										b.TermAs[Fun[Nat, A]]("y • (x • basis_vector(0))"),
										"scaling by a product is scaling twice",
										By(oneCoefficients, vec_space.SmulMulOn.Read(ring).At(ym, xm, onePolynomial))),
									FinalLeg(
										"and multiplying by the constant y is scaling by y",
										By(xOver, PolynomialMulConstant.Read(ring).At(ym, constantX))),
								))
						})),
					Case(
						"one scales the one polynomial to itself",
						By(oneCoefficients, vec_space.SmulOneOn.Read(ring).At(onePolynomial))),
				))
		}),
})}
