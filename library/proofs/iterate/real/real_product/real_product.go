// real_product.go — products of reals, where the fold at ℝ's
// multiplication meets real arithmetic: the recursion (ProductClauses), and
// a product with a vanishing factor vanishing, the index of that factor
// splitting off the rest (Delete); a product of natural numbers read in ℝ
// is the product of their readings. Under a second banner, the fold's laws
// read at ℝ's multiplication and the identities they give: congruence,
// products of ones, enlarging and restricting the index set, singletons,
// deleting an index, disjoint unions, exchanging two products, the
// pointwise and the subset splits, halves, constants, squares of signs,
// nonnegative factors, and the sum of the products over the subsets of a
// set.

package real_product

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/iterate/monoidal"
	"github.com/euc-ai/xugo/library/proofs/iterate/nat/nat_product"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_pow"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The recursion at ℝ's multiplication
// ---------------------------------------------------------------------------
//
// The empty fold returns the operation's neutral element, and inserting
// a point either changes nothing, because the point was already there,
// or contributes its own value.

// ProductClauses — the recursion at ℝ's multiplication. `real_ring`'s
// two facts divide the work: MonoidalMul discharges the mechanism law's
// antecedent, NeutralMul says which real number an empty product is.
var ProductClauses = productClausesThm{family.Add(registry.ProofEntry{
	Name: "ProductClauses",
	Key:  "prop_5295cbb8de150936",
	Build: family.Theorem(
		"(∀f:(A → real). product(∅, f) = &1) ∧ "+
			"(∀g:(C → real). ∀x:C. ∀s:set(C). "+
			"    finite(s) ⇒ product(insert(x, s), g) = COND(x ∈ s, product(s, g), g(x) * product(s, g)))",
		func(a *Argument) {
			a.Do(Unfold(RealProductDef), By(monoidal.Clauses, real_ring.MonoidalMul, real_ring.NeutralMul))
		}),
})}

// ProductZero — a finite product of reals with a zero factor is zero:
// the index of that factor splits off the rest.
var ProductZero = productZeroThm{family.Add(registry.ProofEntry{
	Name: "ProductZero",
	Key:  "prop_d2b7aa8c6fa352e9",
	Build: family.Theorem(Statement{
		Binders: "∀k:set(A). ∀x:A → real. ∀j:A.",
		Hypotheses: []string{
			"finite(k)",
			"j ∈ k",
			"x(j) = &0",
		},
		Conclusion: "Π_{i∈k} x(i) = &0",
	}, func(a *Argument, k *Expr[Set[A]], x *Expr[Fun[A, Real]], j *Expr[A], finiteK, jIn, zero Fact) {
		a.Show(
			"the product is x(j) times the product over the rest of k, and x(j) is zero",
			ByArith(finiteK, jIn, zero, Delete.At(k, x, j)))
	}),
})}

// ---------------------------------------------------------------------------
// The cast from ℕ
// ---------------------------------------------------------------------------

// RealOfNatProduct — the cast of a finite product of natural numbers is the
// product of the casts: the transfer law for folds, read at the cast from
// multiplication on ℕ to multiplication on ℝ, which keeps the unit.
var RealOfNatProduct = realOfNatProductThm{family.Add(registry.ProofEntry{
	Name: "RealOfNatProduct",
	Key:  "prop_c67f988a16298e55",
	Build: family.Theorem(Statement{
		Binders:    "∀s:set(A). ∀f:(A → num).",
		Hypotheses: []string{"finite(s)"},
		Conclusion: "real_of_num(product(s, f)) = product(s, λx:A. real_of_num(f(x)))",
	}, func(a *Argument, s *Expr[Set[A]], f *Arrow[A, Nat], finite Fact) {
		// Each product is the fold at its carrier's multiplication.
		a.Do(Unfold(nat_product.NatProductDef), Unfold(RealProductDef))
		fixesUnit := a.Have(
			"the cast fixes the unit",
			"real_of_num(neutral_elem(λx:num. λy:num. x * y)) = neutral_elem(real_mul)",
			Simp(Fwd(nat_product.NeutralNatMul), Fwd(real_ring.NeutralMul)),
			Refl())
		a.Show(
			"so the transfer law carries the fold across the cast, which crosses multiplication",
			By(
				finite,
				fixesUnit,
				monoidal.Homomorphic,
				nat_product.MonoidalNatMul,
				real_ring.MonoidalMul,
				real_construction.OfNumMul))
	}),
})}

// ---------------------------------------------------------------------------
// Real products
// ---------------------------------------------------------------------------
//
// The fold's laws at ℝ's multiplication, as real_sum states them at its
// addition, and the identities about products they give.

// Congruence — a product reads its factor on the index set alone: two
// factors agreeing there give the same product.
var Congruence = congruenceThm{family.Add(registry.ProofEntry{
	Name: "Congruence",
	Key:  "prop_ada32245ec1e218b",
	Build: family.Theorem(Statement{
		Binders:    "∀s:set(A). ∀g f:(A → real).",
		Hypotheses: []string{"∀x:A. x ∈ s ⇒ g(x) = f(x)"},
		Conclusion: "Π_{x∈s} g(x) = Π_{x∈s} f(x)",
	}, func(a *Argument) {
		a.Do(Unfold(RealProductDef), By(monoidal.Congruence, real_ring.MonoidalMul))
	}),
})}

// Pointwise — a finite product of pointwise products is the product of
// the two products.
var Pointwise = pointwiseThm{family.Add(registry.ProofEntry{
	Name: "Pointwise",
	Key:  "prop_c900ca40ccc24f4f",
	Build: family.Theorem(Statement{
		Binders:    "∀s:set(A). ∀f g:(A → real).",
		Hypotheses: []string{"finite(s)"},
		Conclusion: "Π_{x∈s} f(x) * g(x) = (Π_{x∈s} f(x)) * Π_{x∈s} g(x)",
	}, func(a *Argument) {
		a.Do(Unfold(RealProductDef), By(monoidal.Pointwise, real_ring.MonoidalMul))
	}),
})}

// Diff — a finite product splits at a subset of its index set: the
// product off the subset times the product over it.
var Diff = diffThm{family.Add(registry.ProofEntry{
	Name: "Diff",
	Key:  "prop_530957c97089241e",
	Build: family.Theorem(Statement{
		Binders: "∀s t:set(A). ∀f:(A → real).",
		Hypotheses: []string{
			"finite(s)",
			"t ⊆ s",
		},
		Conclusion: "(Π_{x∈s ∖ t} f(x)) * Π_{x∈t} f(x) = Π_{x∈s} f(x)",
	}, func(a *Argument) {
		a.Do(Unfold(RealProductDef), By(monoidal.Diff, real_ring.MonoidalMul))
	}),
})}

// EqOne — a product whose factor is 1 at every index is 1.
var EqOne = eqOneThm{family.Add(registry.ProofEntry{
	Name: "EqOne",
	Key:  "prop_963a23fa01e0e3af",
	Build: family.Theorem(Statement{
		Binders:    "∀s:set(A). ∀f:(A → real).",
		Hypotheses: []string{"∀x:A. x ∈ s ⇒ f(x) = &1"},
		Conclusion: "Π_{x∈s} f(x) = &1",
	}, func(a *Argument) {
		a.Do(Unfold(RealProductDef), By(monoidal.EqNeutral, real_ring.MonoidalMul, real_ring.NeutralMul))
	}),
})}

// Superset — enlarging the index set leaves a product unchanged when the
// factor is 1 at every added index.
var Superset = supersetThm{family.Add(registry.ProofEntry{
	Name: "Superset",
	Key:  "prop_996ffef3f63e9c36",
	Build: family.Theorem(Statement{
		Binders: "∀u v:set(A). ∀f:(A → real).",
		Hypotheses: []string{
			"u ⊆ v",
			"∀x:A. x ∈ v ∧ x ∉ u ⇒ f(x) = &1",
		},
		Conclusion: "Π_{x∈u} f(x) = Π_{x∈v} f(x)",
	}, func(a *Argument) {
		a.Do(Unfold(RealProductDef), By(monoidal.Superset, real_ring.NeutralMul))
	}),
})}

// Restrict — a product over the indices where P holds is the product over
// all of s with the factor silenced to 1 where P fails.
var Restrict = restrictThm{family.Add(registry.ProofEntry{
	Name: "Restrict",
	Key:  "prop_ac9f02c6c0aa86f8",
	Build: family.Theorem(
		"∀s:set(A). ∀P:(A → bool). ∀f:(A → real). "+
			"    Π_{x∈{x:A | x ∈ s ∧ P(x)}} f(x) = Π_{x∈s} COND(P(x), f(x), &1)",
		func(a *Argument, s *Expr[Set[A]], P *Expr[Set[A]], f *Arrow[A, Real]) {
			a.Do(Unfold(RealProductDef), By(
				monoidal.Restrict.Read(real_ring.MonoidalMul).At(s, P, f),
				real_ring.NeutralMul))
		}),
})}

// Sing — a product over one index is its factor there.
var Sing = singThm{family.Add(registry.ProofEntry{
	Name: "Sing",
	Key:  "prop_dac1cfbcc07e30c0",
	Build: family.Theorem(
		"∀f:(A → real). ∀x:A. Π_{y∈{x}} f(y) = f(x)",
		func(a *Argument) {
			a.Do(Unfold(RealProductDef), By(monoidal.Sing, real_ring.MonoidalMul))
		}),
})}

// Delete — a finite product is the factor at one of its indices times the
// product over the others.
var Delete = deleteThm{family.Add(registry.ProofEntry{
	Name: "Delete",
	Key:  "prop_c29b9dbdd5f7b2d0",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(A). ∀f:(A → real). ∀a:A.",
		Hypotheses: []string{
			"finite(s)",
			"a ∈ s",
		},
		Conclusion: "f(a) * Π_{x∈delete(s, a)} f(x) = Π_{x∈s} f(x)",
	}, func(arg *Argument) {
		arg.Do(Unfold(RealProductDef), By(monoidal.Delete, real_ring.MonoidalMul))
	}),
})}

// Union — a product over two disjoint finite index sets is the product of
// the two products.
var Union = unionThm{family.Add(registry.ProofEntry{
	Name: "Union",
	Key:  "prop_e95c64bb8e95ceb8",
	Build: family.Theorem(Statement{
		Binders: "∀s t:set(A). ∀f:(A → real).",
		Hypotheses: []string{
			"finite(s)",
			"finite(t)",
			"disjoint(s, t)",
		},
		Conclusion: "Π_{x∈s ∪ t} f(x) = (Π_{x∈s} f(x)) * Π_{x∈t} f(x)",
	}, func(a *Argument) {
		a.Do(Unfold(RealProductDef), By(monoidal.Union, real_ring.MonoidalMul))
	}),
})}

// Swap — two finite products exchange.
var Swap = swapThm{family.Add(registry.ProofEntry{
	Name: "Swap",
	Key:  "prop_c12d5984d3cb515e",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(A). ∀t:set(B). ∀f:(A → B → real).",
		Hypotheses: []string{
			"finite(s)",
			"finite(t)",
		},
		Conclusion: "Π_{i∈s} Π_{j∈t} f(i, j) = Π_{j∈t} Π_{i∈s} f(i, j)",
	}, func(a *Argument) {
		a.Do(Unfold(RealProductDef), By(monoidal.Swap, real_ring.MonoidalMul))
	}),
})}

// ProductOfHalves — the halves leave a finite product: the product of the
// f(v)/2 is the product of the f(v) over 2 to the number of factors. By
// induction on the index set: a fresh index puts f(x)/2 on the left, f(x) and
// one more factor 2 on the right.
var ProductOfHalves = productOfHalvesThm{family.Add(registry.ProofEntry{
	Name: "ProductOfHalves",
	Key:  "prop_fffaafbaa966b7c",
	Build: family.Theorem(Statement{
		Binders:    "∀N:set(A). ∀f:(A → real).",
		Hypotheses: []string{"finite(N)"},
		Conclusion: "Π_{v∈N} f(v) / &2 = (Π_{v∈N} f(v)) / &(2 ^ card(N))",
	}, func(a *Argument, N *Expr[Set[A]], f *Arrow[A, Real], finite Fact) {
		a.Show(
			"by induction on the finite index set, adjoining a fresh index",
			ByInduction(finite_set.FiniteInductFresh, finite,
				Case(
					"over no index both products are 1 and the power is 2 ^ 0",
					ByArith(ProductClauses, cardinality.CardClauses)),
				Case(
					"a fresh index x puts f(x) / 2 on the left, f(x) and one more factor 2 on the right",
					Derive(func(b *Argument) {
						b.FixAs[A]()
						b.FixAs[Set[A]]()
						step := b.Assume()
						parts := b.Conjuncts(
							step,
							"the identity over the smaller set",
							"the index is fresh",
							"the smaller set is finite")
						b.Show(
							"peel x off both products and off the count, then scale the smaller identity by f(x) / 2",
							Simp(
								Fwd(ProductClauses),
								Fwd(cardinality.CardClauses),
								Fwd(nat_arith.NatPow),
								Fwd(real_construction.OfNumMul),
								Fwd(parts[1]),
								Fwd(parts[2])),
							ByArith(Scaled(b.TermAs[Real]("f(x) / &2"), parts[0])))
					}))))
	}),
})}

// SubsetProductsSum — the sum over the subsets of a finite set of the products
// over them is the product of the binomials 1 + b(u): the expansion of a product
// of binomials whose first terms are all 1, the product of ones over the
// complement of each subset being 1.
var SubsetProductsSum = subsetProductsSumThm{family.Add(registry.ProofEntry{
	Name: "SubsetProductsSum",
	Key:  "prop_1eca8c64aea72384",
	Build: family.Theorem(Statement{
		Binders:    "∀U:set(A). ∀b:(A → real).",
		Hypotheses: []string{"finite(U)"},
		Conclusion: "Σ_{S∈{S:set(A) | S ⊆ U}} Π_{u∈S} b(u) = Π_{u∈U} (&1 + b(u))",
	}, func(a *Argument, U *Expr[Set[A]], b *Arrow[A, Real], finiteU Fact) {
		ones := a.Have(
			"a product of ones is one",
			"∀S:set(A). Π_{v∈U ∖ S} &1 = &1",
			By(EqOne))
		a.Show(
			"expand the product of the 1 + b(u) over the finite "+
				"set U: each subset takes b on itself and 1 off it",
			Simp(Fwd(ProductOfBinomials), Fwd(finiteU), Fwd(ones), Fwd(real_construction.MulLeftId)),
			Refl())
	}),
})}

// ProductSquareOne — a product of reals that each square to one squares to
// one: squaring to one holds of 1 and passes to a product of two, so the
// fold keeps it. No finiteness is asked, the fold over an infinite support
// being 1.
var ProductSquareOne = productSquareOneThm{family.Add(registry.ProofEntry{
	Name: "ProductSquareOne",
	Key:  "prop_f9d5714c66600bea",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(A). ∀f:(A → real).",
		Hypotheses: []string{
			"∀x:A. x ∈ s ⇒ f(x) * f(x) = &1",
		},
		Conclusion: "(Π_{x∈s} f(x)) * (Π_{x∈s} f(x)) = &1",
	}, func(a *Argument, s *Expr[Set[A]], f *Arrow[A, Real], unit Fact) {
		atOne := a.Have(
			"the empty product squares to one",
			"neutral_elem(real_mul) * neutral_elem(real_mul) = &1",
			Simp(Fwd(real_ring.NeutralMul)),
			ByArith())
		products := a.Have(
			"the product of two square roots of one is a square root of one",
			"∀x y:real. x * x = &1 ∧ y * y = &1 ⇒ (x * y) * (x * y) = &1",
			ByArith())
		a.Show(
			"so the fold at real multiplication keeps the property",
			Unfold(RealProductDef),
			By(
				unit,
				atOne,
				products,
				monoidal.Closed.Read(real_ring.MonoidalMul).At(a.TermAs[Set[Real]]("λy:real. y * y = &1"), s, f)))
	}),
})}

// Nonneg — a product of nonnegative reals is nonnegative. As for
// ProductSquareOne above, no finiteness is asked.
var Nonneg = nonnegThm{family.Add(registry.ProofEntry{
	Name: "Nonneg",
	Key:  "prop_5e460474ac083778",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(A). ∀f:(A → real).",
		Hypotheses: []string{
			"∀x:A. x ∈ s ⇒ &0 ≤ f(x)",
		},
		Conclusion: "&0 ≤ Π_{x∈s} f(x)",
	}, func(a *Argument, s *Expr[Set[A]], f *Arrow[A, Real], nonnegative Fact) {
		a.Show(
			"nonnegativity holds of 1 and passes to a product "+
				"of two, so the fold at real multiplication keeps it",
			Unfold(RealProductDef),
			By(
				nonnegative,
				real_ring.NeutralMul,
				real_order_ring.ZeroLessEqOne,
				real_construction.LessEqMul,
				monoidal.Closed.Read(real_ring.MonoidalMul).At(a.TermAs[Set[Real]]("λy:real. &0 ≤ y"), s, f)))
	}),
})}

// ProductConst — the product of one real c over a finite set is c to the
// set's size: by induction on the set, a fresh point contributes one factor
// c and raises the size by one.
var ProductConst = productConstThm{family.Add(registry.ProofEntry{
	Name: "ProductConst",
	Key:  "prop_d10418e56a51e3d8",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(A). ∀c:real.",
		Hypotheses: []string{
			"finite(s)",
		},
		Conclusion: "Π_{x∈s} c = c ^ card(s)",
	}, func(a *Argument, s *Expr[Set[A]], c *Expr[Real], finite Fact) {
		a.Show(
			"by induction on the finite set s",
			ByInduction(finite_set.FiniteInductFresh, finite,
				Case(
					"the empty product is 1 = c⁰",
					Simp(Fwd(ProductClauses), Fwd(cardinality.CardClauses), Fwd(real_pow.PowExpZeroClause)),
					Refl()),
				Case(
					"a fresh point x contributes one factor c and one to the size",
					Derive(func(b *Argument) {
						b.FixAs[A]("x")
						b.FixAs[Set[A]]("t")
						grown := b.Conjuncts(
							b.Assume(),
							"the product over t is c to the size of t",
							"x is not in t",
							"t is finite")
						b.Do(Simp(
							Fwd(ProductClauses),
							Fwd(cardinality.CardClauses),
							Fwd(real_pow.PowExpSucClause),
							Fwd(grown[1]),
							Fwd(grown[2])))
						b.Show(
							"both sides are c times what the hypothesis equates",
							By(Normalized, grown[0]))
					}))))
	}),
})}
