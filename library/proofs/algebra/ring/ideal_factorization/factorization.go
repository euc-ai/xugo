package ideal_factorization

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/fractional_ideal"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_domain"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/quotient_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_ideal"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_embed"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/nat_num/peano"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// IdealProductSubsetPrime — a prime ideal holding a finite product of ideals
// holds one of its factors. Induct on the support: the zero vector's product
// is the whole ring, which no prime holds; a vector with a nonzero m
// coordinate has as its product that power times the product of the rest
// (IdealExponentProductSplit), so p holds the power, hence m, or holds the
// rest, where the induction finds a factor of the rest, a factor of the
// vector.
var IdealProductSubsetPrime = idealProductSubsetPrimeThm{family.Add(registry.ProofEntry{
	Name: "IdealProductSubsetPrime",
	Key:  "prop_ccb24f65d5a4fcb4",
	Build: family.Theorem(Statement{
		Binders: "∀R:comm_ring_on(A). ∀p:set(A). ∀v:(set(A) → num).",
		Hypotheses: []string{
			"prime_ideal(R, p)",
			"finite(fun_support(0, v))",
			"∀q:set(A). v(q) ≠ 0 ⇒ ring_ideal(R, q)",
			"ideal_exponent_product(R, v) ⊆ p",
		},
		Conclusion: "∃q:set(A). v(q) ≠ 0 ∧ q ⊆ p",
		Abbrev: Abbrev{
			{Name: "Motive", Text: "λu:(set(A) → num). " +
				"    (∀q:set(A). u(q) ≠ 0 ⇒ ring_ideal(R, q)) ∧ ideal_exponent_product(R, u) ⊆ p ⇒ " +
				"    ∃q:set(A). u(q) ≠ 0 ∧ q ⊆ p"},
		},
	}, func(
		a *Argument,
		R comm_ring.CommRingFact[on.R],
		p *Expr[Set[A]],
		v *Arrow[Set[A], Nat],
		h Fact,
	) {
		parts := a.Conjuncts(
			h,
			"p is prime",
			"the support is finite",
			"supported factors are ideals",
			"p holds the product")
		r := a.TermAs[RingOps[A]]("R")
		proper := a.Have(
			"p, proper, does not hold the whole ring",
			"¬(R.carrier ⊆ p)",
			BySets(parts[0], comm_ring.OneIn.Read(R), ring_ideal.PrimeIdealProper.At(r, p)))
		powerBase := a.Have(
			"a prime holding a power of an ideal holds the ideal",
			"∀m:set(A). ∀n:num. ring_ideal(R, m) ∧ ideal_pow(R, m, n) ⊆ p ⇒ m ⊆ p",
			Derive(func(b *Argument) {
				m := b.FixAs[Set[A]]("m")
				b.Induct("n")
				b.Base(
					"the zeroth power is the carrier, which p does not hold",
					Simp(Fwd(ring_ideal.IdealPowZero), Fwd(ring_ideal.IdealPowSuc)),
					By(proper))
				b.Step(
					"the power at suc(n) is m times the power at n: p holds m, or the power at n and so m",
					func(c *Argument, ih Fact) {
						given := c.Assume()
						power := c.TermAs[Set[A]]("ideal_pow(R, m, n)")
						powerIdeal := c.Have(
							"the power at n is an ideal",
							"ring_ideal(R, ideal_pow(R, m, n))",
							BySets(given, ring_ideal.IdealPowIdeal.Read(R).At(m, c.TermAs[Nat]("n"))))
						product := c.Simplified(given, Fwd(ring_ideal.IdealPowZero), Fwd(ring_ideal.IdealPowSuc))
						either := c.Have(
							"p holds m or the power at n",
							"m ⊆ p ∨ ideal_pow(R, m, n) ⊆ p",
							By(product, powerIdeal, parts[0], ring_ideal.PrimeIdealMulSubset.At(r, p, m, power)))
						c.Show(
							"either way p holds m",
							By(either, given, powerIdeal, ih))
					})
			}))
		supported := a.Have(
			"for every vector of finite support, p holds a supported factor",
			"∀u:(set(A) → num). finite(fun_support(0, u)) ⇒ «Motive»(u)",
			ByInduction(finite_set.FiniteInductSupport,
				Case(
					"the zero vector has the whole ring as its product",
					Derive(func(b *Argument) {
						given := b.Assume()
						whole := b.Have(
							"its product is the carrier",
							"ideal_exponent_product(R, λq:set(A). 0) = R.carrier",
							Simp(Fwd(IdealExponentProductZero)),
							Basic())
						b.Show(
							"p would hold the carrier",
							By(Normalized, given, whole, proper))
					})),
				Case(
					"a nonzero coordinate m splits its power off the product",
					Derive(func(b *Argument) {
						u := b.FixAs[Fun[Set[A], Nat]]("u")
						m := b.FixAs[Set[A]]("m")
						previous := b.Conjuncts(
							b.Assume(),
							"the motive holds of the rest",
							"u has an m factor",
							"u has finite support")
						g := b.Conjuncts(
							b.Assume(),
							"its supported factors are ideals",
							"p holds its product")
						rest := b.TermAs[Fun[Set[A], Nat]]("«Delete»(u, m)")
						support := b.TermAs[Set[Set[A]]]("fun_support(0, u)")
						restSupport := b.TermAs[Set[Set[A]]]("fun_support(0, λq:set(A). «Delete»(u, m, q))")
						restInside := b.Have(
							"the rest is supported inside u's support",
							"fun_support(0, λq:set(A). «Delete»(u, m, q)) ⊆ fun_support(0, u)",
							BySets())
						restFactors := b.Have(
							"its supported factors are ideals",
							"∀q:set(A). «Delete»(u, m, q) ≠ 0 ⇒ ring_ideal(R, q)",
							BySets(g[0]))
						finiteRest := b.Have(
							"so it has finite support",
							"finite(fun_support(0, λq:set(A). «Delete»(u, m, q)))",
							By(restInside, previous[2], finite_set.FiniteSubset.At(restSupport, support)))
						split := b.Have(
							"the product is the m power times the product of the rest",
							"ideal_exponent_product(R, u) = "+
								"ideal_mul(R, ideal_pow(R, m, u(m)), ideal_exponent_product(R, «Delete»(u, m)))",
							By(previous[2], g[0], IdealExponentProductSplit.Read(R).At(u, m)))
						mIdeal := b.Have(
							"m is an ideal",
							"ring_ideal(R, m)",
							By(previous[1], g[0]))
						um := b.TermAs[Nat]("u(m)")
						power := b.TermAs[Set[A]]("ideal_pow(R, m, u(m))")
						restProduct := b.TermAs[Set[A]]("ideal_exponent_product(R, «Delete»(u, m))")
						factorsIdeal := b.Have(
							"both factors are ideals",
							"ring_ideal(R, ideal_pow(R, m, u(m))) ∧ ring_ideal(R, ideal_exponent_product(R, «Delete»(u, m)))",
							BySets(
								mIdeal,
								ring_ideal.IdealPowIdeal.Read(R).At(m, um),
								finiteRest,
								restFactors,
								IdealExponentProductIntegral.Read(R).At(rest)))
						either := b.Have(
							"p holds the m power or the rest",
							"ideal_pow(R, m, u(m)) ⊆ p ∨ ideal_exponent_product(R, «Delete»(u, m)) ⊆ p",
							By(
								split,
								g[1],
								factorsIdeal,
								parts[0],
								ring_ideal.PrimeIdealMulSubset.At(r, p, power, restProduct)))
						b.Cases(b.TermAs[Bool]("ideal_pow(R, m, u(m)) ⊆ p"))
						b.When(
							"p holds the power, so m, a factor of u",
							func(c *Argument, inPower Fact) {
								c.Take(m)
								c.Show(
									"m is supported and p holds it",
									By(previous[1], mIdeal, inPower, powerBase.At(m, um)))
							})
						b.Otherwise(
							"p holds the rest, where the motive finds a factor",
							func(c *Argument, notPower Fact) {
								q, found := c.ObtainAs[Set[A]](
									"the motive at the rest finds a factor of it in p",
									"∃q:set(A). «Delete»(u, m, q) ≠ 0 ∧ q ⊆ p",
									By(restFactors, either, notPower, previous[0]),
									Named("q"))
								c.Take(q)
								c.Show(
									"a factor of the rest is a factor of u",
									BySets(found))
							})
					}))))
		a.Show(
			"the motive at v, whose support is finite",
			By(parts[1], parts[2], parts[3], supported.At(v)))
	}),
})}

// IdealContainsNonzeroPrimeProduct — in a commutative ring whose nonzero
// ideals have finite quotients, every nonzero ideal contains a finite product
// of nonzero prime ideals: induction on finite quotient index reduces a
// nonprime ideal to two strictly larger ideals, and the product of their two
// prime products lies in it.
var IdealContainsNonzeroPrimeProduct = idealContainsNonzeroPrimeProductThm{family.Add(registry.ProofEntry{
	Name: "IdealContainsNonzeroPrimeProduct",
	Key:  "prop_916bc0d23f22433b",
	Build: family.Theorem(Statement{
		Binders: "∀R:comm_ring_on(A). ∀I:set(A).",
		Hypotheses: []string{
			"∀H:set(A). ring_ideal(R, H) ∧ H ≠ {R.zero} ⇒ finite(left_cosets(R.add, R.carrier, H))",
			"ring_ideal(R, I)",
			"I ≠ {R.zero}",
		},
		Conclusion: "∃v:(set(A) → num). " +
			"    finite(fun_support(0, v)) ∧ " +
			"    (∀p:set(A). v(p) ≠ 0 ⇒ prime_ideal(R, p) ∧ p ≠ {R.zero}) ∧ " +
			"    ideal_exponent_product(R, v) ⊆ I",
		Abbrev: Abbrev{
			{Name: "HasPrimeProduct", Text: "λH:set(A). ∃v:(set(A) → num). " +
				"    finite(fun_support(0, v)) ∧ " +
				"    (∀p:set(A). v(p) ≠ 0 ⇒ prime_ideal(R, p) ∧ p ≠ {R.zero}) ∧ " +
				"    ideal_exponent_product(R, v) ⊆ H"},
		},
	}, func(a *Argument, R comm_ring.CommRingFact[on.R], I *Expr[Set[A]], h Fact) {
		parts := a.Conjuncts(
			h,
			"nonzero ideal quotients are finite",
			"I is an ideal",
			"I is nonzero")
		r := a.TermAs[RingOps[A]]("R")
		emptySupport := a.Have(
			"the zero vector has empty support",
			"fun_support(0, λp:set(A). 0) = ∅",
			BySets())
		finiteZero := a.Have(
			"so its support is finite",
			"finite(fun_support(0, λp:set(A). 0))",
			Simp(Fwd(emptySupport)),
			By(finite_set.FiniteRules.Inst[Set[A]]()))
		all := a.Have(
			"every nonzero ideal contains a prime product",
			"∀H:set(A). ring_ideal(R, H) ∧ H ≠ {R.zero} ⇒ «HasPrimeProduct»(H)",
			Derive(func(b *Argument) {
				base := b.Have(
					"the unit ideal is the empty prime product",
					"∃v:(set(A) → num). "+
						"    finite(fun_support(0, v)) ∧ "+
						"    (∀p:set(A). v(p) ≠ 0 ⇒ prime_ideal(R, p) ∧ p ≠ {R.zero}) ∧ "+
						"    ideal_exponent_product(R, v) ⊆ R.carrier",
					Derive(func(c *Argument) {
						c.Take(c.TermAs[Fun[Set[A], Nat]]("λp:set(A). 0"))
						c.Show(
							"the zero vector represents the unit ideal",
							BySets(finiteZero, IdealExponentProductZero.At(r)))
					}))
				step := b.Have(
					"strict larger ideals supply the induction step",
					Statement{
						Binders: "∀H:set(A).",
						Hypotheses: []string{
							"ring_ideal(R, H)",
							"H ≠ {R.zero}",
							"H ≠ R.carrier",
							"∀J:set(A). ring_ideal(R, J) ∧ J ≠ {R.zero} ∧ H ⊆ J ∧ H ≠ J ⇒ «HasPrimeProduct»(J)",
						},
						Conclusion: "∃v:(set(A) → num). " +
							"    finite(fun_support(0, v)) ∧ " +
							"    (∀p:set(A). v(p) ≠ 0 ⇒ prime_ideal(R, p) ∧ p ≠ {R.zero}) ∧ " +
							"    ideal_exponent_product(R, v) ⊆ H",
					},
					Derive(func(c *Argument) {
						H := c.FixAs[Set[A]]("H")
						given := c.Assume()
						hp := c.Conjuncts(
							given,
							"H is an ideal",
							"H is nonzero",
							"H is proper",
							"strict larger nonzero ideals contain prime products")
						c.Cases(c.TermAs[Bool]("prime_ideal(R, H)"))
						c.When(
							"a prime ideal is its own one-factor product",
							func(d *Argument, prime Fact) {
								zero := d.TermAs[Fun[Set[A], Nat]]("λp:set(A). 0")
								// 0 + 1, not 1: the delta vector is IdealExponentProductIncrement's «inc» at v = 0.
								delta := d.TermAs[Fun[Set[A], Nat]]("λp:set(A). COND(p = H, 0 + 1, 0)")
								zeroFactors := d.Have(
									"the zero vector supports no factor, so each supported one is an ideal",
									"∀p:set(A). 0 ≠ 0 ⇒ ring_ideal(R, p)",
									Basic())
								increment := d.Have(
									"the delta product adjoins H to the empty product",
									"ideal_exponent_product(R, λp:set(A). COND(p = H, 0 + 1, 0)) = "+
										"ideal_mul(R, H, ideal_exponent_product(R, λp:set(A). 0))",
									By(hp[0], finiteZero, zeroFactors, IdealExponentProductIncrement.Read(R).At(H, zero)))
								monoid := ring_ideal.IdealsCommMonoid.Read(R)
								inMonoid := d.Have(
									"H belongs to the ideal carrier",
									"H ∈ {J:set(A) | ring_ideal(R, J)}",
									BySets(hp[0]))
								deltaProduct := d.Have(
									"the delta product is H",
									"ideal_exponent_product(R, λp:set(A). COND(p = H, 0 + 1, 0)) = H",
									By(
										increment,
										inMonoid,
										comm_monoid.RightIdentityOn.Read(monoid).AsFact().At(H),
										IdealExponentProductZero.At(r)))
								positive := d.Have(
									"the delta exponent is nonzero",
									"0 + 1 ≠ 0",
									ByArith())
								support := d.Have(
									"the delta vector is supported at H",
									"fun_support(0, λp:set(A). (λp:set(A). COND(p = H, 0 + 1, 0))(p)) = {H}",
									BySets(positive))
								finiteDelta := d.Have(
									"the singleton support is finite",
									"finite(fun_support(0, λp:set(A). (λp:set(A). COND(p = H, 0 + 1, 0))(p)))",
									By(support, finite_set.FiniteSing.Inst[Set[A]]()))
								d.Take(delta)
								d.Show(
									"the one supported factor is a nonzero prime",
									BySets(deltaProduct, prime, hp[1], finiteDelta))
							})
						c.Otherwise(
							"a nonprime ideal is reduced to two strict larger ideals",
							func(d *Argument, nonprime Fact) {
								oneOutside := d.Have(
									"the proper ideal omits one",
									"R.one ∉ H",
									By(Normalized, hp[0], hp[2], ring_ideal.IdealOneIff.Read(R).At(H)))
								aElem, bElem, witnesses := d.Obtain2As[A, A](
									"choose the witnesses to failure of primality",
									"∃a b:A. a ∈ R.carrier ∧ b ∈ R.carrier ∧ a ∉ H ∧ b ∉ H ∧ a * b ∈ H",
									By(hp[0], oneOutside, nonprime, ring_ideal.PrimeIdealDef.At(r, H)),
									Named("a", "b"))
								J, jDef := d.LetAs[Set[A]]("J", "ideal_span(R, insert(a, H))")
								K, kDef := d.LetAs[Set[A]]("K", "ideal_span(R, insert(b, H))")
								hInRing := d.Have(
									"H lies in the ring",
									"H ⊆ R.carrier",
									By(hp[0], ring_ideal.IdealSubset.At(r, H)))
								insertA := d.TermAs[Set[A]]("insert(a, H)")
								insertB := d.TermAs[Set[A]]("insert(b, H)")
								aInRing := d.Have(
									"adjoining a stays in the ring",
									"insert(a, H) ⊆ R.carrier",
									BySets(hInRing, witnesses))
								jIdeal := d.Have(
									"J is an ideal",
									"ring_ideal(R, J)",
									Simp(Fwd(jDef)),
									By(aInRing, ring_ideal.SpanIdeal.Read(R).At(insertA)))
								jContains := d.Have(
									"J contains H and a",
									"H ⊆ J ∧ a ∈ J",
									BySets(jDef, ring_ideal.SpanContains.At(r, insertA)))
								jStrict := d.Have(
									"a makes the inclusion strict",
									"H ≠ J",
									BySets(jContains, witnesses))
								jNonzero := d.Have(
									"J contains the nonzero ideal H",
									"J ≠ {R.zero}",
									BySets(jContains, hp[1], hp[0], ring_ideal.IdealZero.At(r, H)))
								bInRing := d.Have(
									"adjoining b stays in the ring",
									"insert(b, H) ⊆ R.carrier",
									BySets(hInRing, witnesses))
								kIdeal := d.Have(
									"K is an ideal",
									"ring_ideal(R, K)",
									Simp(Fwd(kDef)),
									By(bInRing, ring_ideal.SpanIdeal.Read(R).At(insertB)))
								kContains := d.Have(
									"K contains H and b",
									"H ⊆ K ∧ b ∈ K",
									BySets(kDef, ring_ideal.SpanContains.At(r, insertB)))
								kStrict := d.Have(
									"b makes the inclusion strict",
									"H ≠ K",
									BySets(kContains, witnesses))
								kNonzero := d.Have(
									"K contains the nonzero ideal H",
									"K ≠ {R.zero}",
									BySets(kContains, hp[1], hp[0], ring_ideal.IdealZero.At(r, H)))
								jShape := d.Have(
									"elements of J are multiples of a modulo H",
									"J = {r * a + i | r:A, i:A | r ∈ R.carrier ∧ i ∈ H}",
									By(jDef, hp[0], witnesses, ring_ideal.SpanInsertIdeal.Read(R).AsFact().At(H, aElem)))
								kShape := d.Have(
									"elements of K are multiples of b modulo H",
									"K = {r * b + i | r:A, i:A | r ∈ R.carrier ∧ i ∈ H}",
									By(kDef, hp[0], witnesses, ring_ideal.SpanInsertIdeal.Read(R).AsFact().At(H, bElem)))
								products := d.Have(
									"every product of a J element and a K element lies in H",
									"∀x y:A. x ∈ J ∧ y ∈ K ⇒ x * y ∈ H",
									Derive(func(e *Argument) {
										e.FixAs[A]("x")
										e.FixAs[A]("y")
										xy := e.Assume()
										rElem, i, dx := e.Obtain2As[A, A](
											"write x as a multiple of a modulo H",
											"∃r i:A. r ∈ R.carrier ∧ i ∈ H ∧ x = r * a + i",
											BySets(xy, jShape),
											Named("r", "i"))
										sElem, j, dy := e.Obtain2As[A, A](
											"write y as a multiple of b modulo H",
											"∃s j:A. s ∈ R.carrier ∧ j ∈ H ∧ y = s * b + j",
											BySets(xy, kShape),
											Named("s", "j"))
										carriers := e.Have(
											"the six expansion factors lie in the ring",
											"a ∈ R.carrier ∧ b ∈ R.carrier ∧ r ∈ R.carrier ∧ s ∈ R.carrier ∧ i ∈ R.carrier ∧ j ∈ R.carrier",
											BySets(witnesses, dx, dy, hInRing))
										abTerm := e.Have(
											"the leading term is absorbed from ab",
											"(r * s) * (a * b) ∈ H",
											By(
												witnesses,
												carriers,
												comm_ring.MulIn.Read(R).AsFact().At(rElem, sElem),
												ring_ideal.IdealMul.Read(hp[0]).AsFact().At(e.TermAs[A]("r * s"), e.TermAs[A]("a * b"))))
										aTerm := e.Have(
											"the a mixed term is absorbed from j",
											"(r * a) * j ∈ H",
											By(
												dy,
												carriers,
												comm_ring.MulIn.Read(R).AsFact().At(rElem, aElem),
												ring_ideal.IdealMul.Read(hp[0]).AsFact().At(e.TermAs[A]("r * a"), j)))
										bTerm := e.Have(
											"the b mixed term is absorbed from i",
											"(s * b) * i ∈ H",
											By(
												dx,
												carriers,
												comm_ring.MulIn.Read(R).AsFact().At(sElem, bElem),
												ring_ideal.IdealMul.Read(hp[0]).AsFact().At(e.TermAs[A]("s * b"), i)))
										ijTerm := e.Have(
											"the old ideal absorbs the last term",
											"i * j ∈ H",
											By(dy, carriers, ring_ideal.IdealMul.Read(hp[0]).AsFact().At(i, j)))
										firstPair := e.Have(
											"the leading and a mixed terms add in H",
											"(r * s) * (a * b) + (r * a) * j ∈ H",
											By(
												abTerm,
												aTerm,
												ring_ideal.IdealAdd.Read(hp[0]).AsFact().At(
													e.TermAs[A]("(r * s) * (a * b)"), e.TermAs[A]("(r * a) * j"))))
										secondPair := e.Have(
											"the remaining terms add in H",
											"(s * b) * i + i * j ∈ H",
											By(
												bTerm,
												ijTerm,
												ring_ideal.IdealAdd.Read(hp[0]).AsFact().At(e.TermAs[A]("(s * b) * i"), e.TermAs[A]("i * j"))))
										sum := e.Have(
											"all four terms add in H",
											"((r * s) * (a * b) + (r * a) * j) + ((s * b) * i + i * j) ∈ H",
											By(
												firstPair,
												secondPair,
												ring_ideal.IdealAdd.Read(hp[0]).AsFact().At(
													e.TermAs[A]("(r * s) * (a * b) + (r * a) * j"), e.TermAs[A]("(s * b) * i + i * j"))))
										expansion := e.Have(
											"distributivity gives the four-term expansion",
											"x * y = ((r * s) * (a * b) + (r * a) * j) + ((s * b) * i + i * j)",
											Simp(Fwd(dx), Fwd(dy)),
											ByArith(R, carriers))
										e.Show(
											"the expanded product lies in H",
											By(expansion, sum))
									}))
								jkInH := d.Have(
									"the product ideal lies in H",
									"ideal_mul(R, J, K) ⊆ H",
									By(hp[0], products, ring_ideal.IdealMulLeast.At(r, J, K, H)))
								v, vFacts := d.ObtainAs[Fun[Set[A], Nat]](
									"choose the prime product inside J",
									"∃v:(set(A) → num). "+
										"    finite(fun_support(0, v)) ∧ "+
										"    (∀p:set(A). v(p) ≠ 0 ⇒ prime_ideal(R, p) ∧ p ≠ {R.zero}) ∧ "+
										"    ideal_exponent_product(R, v) ⊆ J",
									By(jIdeal, jNonzero, jContains, jStrict, hp[3].At(J)),
									Named("v"))
								w, wFacts := d.ObtainAs[Fun[Set[A], Nat]](
									"choose the prime product inside K",
									"∃w:(set(A) → num). "+
										"    finite(fun_support(0, w)) ∧ "+
										"    (∀p:set(A). w(p) ≠ 0 ⇒ prime_ideal(R, p) ∧ p ≠ {R.zero}) ∧ "+
										"    ideal_exponent_product(R, w) ⊆ K",
									By(kIdeal, kNonzero, kContains, kStrict, hp[3].At(K)),
									Named("w"))
								vp := d.Conjuncts(
									vFacts,
									"v has finite support",
									"the supported factors of v are nonzero primes",
									"the v product lies in J")
								wp := d.Conjuncts(
									wFacts,
									"w has finite support",
									"the supported factors of w are nonzero primes",
									"the w product lies in K")
								sv := d.TermAs[Set[Set[A]]]("fun_support(0, v)")
								sw := d.TermAs[Set[Set[A]]]("fun_support(0, w)")
								ss := d.TermAs[Set[Set[A]]]("fun_support(0, λp:set(A). v(p) + w(p))")
								union := d.TermAs[Set[Set[A]]]("fun_support(0, v) ∪ fun_support(0, w)")
								supportBound := d.Have(
									"addition introduces no new supported ideal",
									"fun_support(0, λp:set(A). v(p) + w(p)) ⊆ fun_support(0, v) ∪ fun_support(0, w)",
									BySets(nat_arith.AddEqZero))
								finiteUnion := d.Have(
									"the union of supports is finite",
									"finite(fun_support(0, v) ∪ fun_support(0, w))",
									By(vp[0], wp[0], finite_set.FiniteUnionImp.At(sv, sw)))
								finiteSum := d.Have(
									"the sum vector has finite support",
									"finite(fun_support(0, λp:set(A). v(p) + w(p)))",
									By(finiteUnion, supportBound, finite_set.FiniteSubset.At(ss, union)))
								primeSum := d.Have(
									"every supported sum factor is a nonzero prime",
									"∀p:set(A). v(p) + w(p) ≠ 0 ⇒ prime_ideal(R, p) ∧ p ≠ {R.zero}",
									Derive(func(e *Argument) {
										p := e.FixAs[Set[A]]("p")
										nonzero := e.Assume()
										active := e.Have(
											"one of the two exponents is nonzero",
											"v(p) ≠ 0 ∨ w(p) ≠ 0",
											ByArith(nonzero))
										e.Show(
											"the active summand supplies a nonzero prime",
											By(active, vp[1].At(p), wp[1].At(p)))
									}))
								idealFactors := d.Have(
									"every factor in either support is an ideal",
									"∀p:set(A). v(p) ≠ 0 ∨ w(p) ≠ 0 ⇒ ring_ideal(R, p)",
									By(vp[1], wp[1], ring_ideal.PrimeIdealIdeal))
								vProduct := d.TermAs[Set[A]]("ideal_exponent_product(R, v)")
								wProduct := d.TermAs[Set[A]]("ideal_exponent_product(R, w)")
								productBound := d.Have(
									"the inductive product lies in JK",
									"ideal_mul(R, ideal_exponent_product(R, v), ideal_exponent_product(R, w)) ⊆ ideal_mul(R, J, K)",
									By(vp[2], wp[2], ring_ideal.IdealMulMono.At(r, vProduct, wProduct, J, K)))
								productSum := d.Have(
									"adding exponents multiplies the two prime products",
									"ideal_exponent_product(R, λp:set(A). v(p) + w(p)) = "+
										"ideal_mul(R, ideal_exponent_product(R, v), ideal_exponent_product(R, w))",
									By(vp[0], wp[0], idealFactors, IdealExponentProductAdd.Read(R).At(v, w)))
								contained := d.Have(
									"the combined prime product lies in H",
									"ideal_exponent_product(R, λp:set(A). v(p) + w(p)) ⊆ H",
									BySets(productSum, productBound, jkInH))
								d.Take(d.TermAs[Fun[Set[A], Nat]]("λp:set(A). v(p) + w(p)"))
								d.Show(
									"the sum vector is the required nonzero prime product",
									By(finiteSum, primeSum, contained))
							})
					}))
				predicate := b.TermAs[Set[Set[A]]]("«HasPrimeProduct»")
				b.Show(
					"finite quotient induction covers every nonzero ideal",
					By(parts[0], base, step, IdealInductionByFiniteQuotient.Read(R).AsFact().At(predicate)))
			}))
		a.Show(
			"apply the induction result to I",
			By(parts[1], parts[2], all.At(I)))
	}),
})}

// MaximalInverseStrict — the inverse of a nonzero maximal ideal strictly
// contains the subring: minimize its coordinate in a prime product inside (a).
var MaximalInverseStrict = maximalInverseStrictThm{family.Add(registry.ProofEntry{
	Name: "MaximalInverseStrict",
	Key:  "prop_bdbe441443f1c2c3",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S m:set(A).",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"∀H:set(A). " +
				"    ring_ideal(restrict_ring(field_ring(L), S), H) ∧ H ≠ {L.zero} ⇒ " +
				"    finite(left_cosets(L.add, S, H))",
			"maximal_ideal(restrict_ring(field_ring(L), S), m)",
			"m ≠ {L.zero}",
		},
		Conclusion: "S ⊆ fractional_inverse(field_ring(L), S, m) ∧ " +
			"S ≠ fractional_inverse(field_ring(L), S, m)",
		Abbrev: Abbrev{
			{Name: "Principal", Text: "λa:A. ideal_span(«R», insert(a, {L.zero}))"},
			{Name: "Coordinate", Text: "λv:(set(A) → num). λk:num. λq:set(A). COND(q = m, k, v(q))"},
			{Name: "ProductAt", Text: "λv:(set(A) → num). λk:num. " +
				"    ideal_exponent_product(«R», «Coordinate»(v, k))"},
			{Name: "SupportAt", Text: "λv:(set(A) → num). λk:num. " +
				"    fun_support(0, λq:set(A). «Coordinate»(v, k, q))"},
		},
	}, func(arg *Argument, L field.FieldFact[on.L], S, m *Expr[Set[A]], h Fact) {
		parts := arg.Conjuncts(
			h,
			"S is a subring of L",
			"nonzero ideals have finite quotient",
			"m is maximal",
			"m is nonzero")
		r := arg.TermAs[RingOps[A]]("«R»")
		fieldRing := field.RingOn.Read(L)
		sInL := arg.Have(
			"S lies in the field",
			"S ⊆ L.carrier",
			By(comm_ring.SubringSubset.Read(parts[0])))
		ringS := arg.Have(
			"S is a ring under L's operations",
			"comm_ring_on(«R»)",
			By(parts[0], comm_ring.SubringRingOn.Read(fieldRing).At(S)))

		// A nonzero a in m, and a product of nonzero primes inside (a), each of them maximal.
		mIdeal := arg.Have(
			"the maximal ideal is an ideal",
			"ring_ideal(«R», m)",
			By(parts[2], ring_ideal.MaximalIdealIdeal.At(r, m)))
		mInS := arg.Have(
			"the maximal ideal lies in S",
			"m ⊆ S",
			By(mIdeal, ring_ideal.IdealSubset.At(r, m)))
		zeroInM := arg.Have(
			"m contains zero",
			"L.zero ∈ m",
			By(mIdeal, ring_ideal.IdealZero.At(r, m)))
		mPrime := arg.Have(
			"the maximal ideal is prime",
			"prime_ideal(«R», m)",
			By(parts[2], ring_ideal.MaximalIsPrime.Read(ringS).AsFact().At(m)))
		a, nonzero := arg.ObtainAs[A](
			"choose a nonzero element of m",
			"∃a:A. a ∈ m ∧ a ≠ L.zero",
			BySets(parts[3], zeroInM),
			Named("a"))
		aIn := arg.Have(
			"a lies in the subring and field",
			"a ∈ S ∧ a ∈ L.carrier",
			BySets(nonzero, mInS, sInL))
		generators := arg.TermAs[Set[A]]("insert(a, {L.zero})")
		principal := arg.TermAs[Set[A]]("«Principal»(a)")
		generatorsInS := arg.Have(
			"the principal generators lie in S",
			"insert(a, {L.zero}) ⊆ S",
			BySets(aIn, zeroInM, mInS))
		principalIdeal := arg.Have(
			"the principal span is an ideal",
			"ring_ideal(«R», «Principal»(a))",
			By(generatorsInS, ring_ideal.SpanIdeal.Read(ringS).AsFact().At(generators)))
		aInPrincipal := arg.Have(
			"the principal span contains a",
			"a ∈ «Principal»(a)",
			BySets(ring_ideal.SpanContains.At(r, generators)))
		generatorsInM := arg.Have(
			"the principal generators lie in m",
			"insert(a, {L.zero}) ⊆ m",
			BySets(nonzero, zeroInM))
		principalInM := arg.Have(
			"the principal ideal lies in m",
			"«Principal»(a) ⊆ m",
			By(mIdeal, generatorsInM, ring_ideal.SpanLeast.At(r, generators, m)))
		principalNonzero := arg.Have(
			"the principal ideal is nonzero",
			"«Principal»(a) ≠ {L.zero}",
			BySets(aInPrincipal, nonzero))
		zeroSet := arg.TermAs[Set[A]]("{L.zero}")
		expansion := arg.Have(
			"principal elements are scalar multiples with a zero remainder",
			"«Principal»(a) = {L.add(L.mul(r, a), t):A | r:A, t:A | r ∈ S ∧ t ∈ {L.zero}}",
			By(
				aIn,
				ring_ideal.ZeroIdeal.Read(ringS),
				ring_ideal.SpanInsertIdeal.Read(ringS).AsFact().At(zeroSet, a)))
		_, productData := arg.ObtainAs[Fun[Set[A], Nat]](
			"choose a finite product of nonzero prime ideals inside the principal ideal",
			"∃v:(set(A) → num). "+
				"    finite(fun_support(0, v)) ∧ "+
				"    (∀q:set(A). v(q) ≠ 0 ⇒ prime_ideal(«R», q) ∧ q ≠ {L.zero}) ∧ "+
				"    ideal_exponent_product(«R», v) ⊆ «Principal»(a)",
			By(
				parts[1],
				principalIdeal,
				principalNonzero,
				IdealContainsNonzeroPrimeProduct.Read(ringS).At(principal)),
			Named("v"))
		productParts := arg.Conjuncts(
			productData,
			"the original support is finite",
			"supported factors are nonzero primes",
			"the original product lies in the principal ideal")
		maximalFactors := arg.Have(
			"the supported primes are maximal",
			"∀q:set(A). v(q) ≠ 0 ⇒ maximal_ideal(«R», q)",
			Derive(func(d *Argument) {
				q := d.FixAs[Set[A]]("q")
				positive := d.Assume()
				prime := d.Have(
					"q is a nonzero prime",
					"prime_ideal(«R», q) ∧ q ≠ {L.zero}",
					By(positive, productParts[1].At(q)))
				finiteIndex := d.Have(
					"q has finite index, being a nonzero ideal",
					"finite(left_cosets(L.add, S, q))",
					By(prime, ring_ideal.PrimeIdealIdeal.At(r, q), parts[1].At(q)))
				d.Show(
					"a prime of finite index is maximal",
					By(prime, finiteIndex, quotient_ring.FiniteIndexPrimeMaximal.Read(ringS).At(q)))
			}))

		// Replace the exponent of m by k: the least k whose product still lies in (a).
		support := arg.TermAs[Set[Set[A]]]("fun_support(0, v)")
		supportBound := arg.Have(
			"every replaced support lies in one finite insertion",
			"∀k:num. «SupportAt»(v, k) ⊆ insert(m, fun_support(0, v))",
			BySets())
		finiteSupports := arg.Have(
			"every replaced vector has finite support",
			"∀k:num. finite(«SupportAt»(v, k))",
			Derive(func(d *Argument) {
				k := d.FixAs[Nat]("k")
				replacedSupport := d.TermAs[Set[Set[A]]]("«SupportAt»(v, k)")
				bound := d.TermAs[Set[Set[A]]]("insert(m, fun_support(0, v))")
				d.Show(
					"a subset of the finite insertion is finite",
					By(
						productParts[0],
						finite_set.FiniteInsert.At(m, support),
						supportBound.At(k),
						finite_set.FiniteSubset.At(replacedSupport, bound)))
			}))
		factorData := arg.Have(
			"all replaced positive factors remain nonzero maximal primes",
			Statement{
				Binders: "∀k:num. ∀q:set(A).",
				Hypotheses: []string{
					"«Coordinate»(v, k, q) ≠ 0",
				},
				Conclusion: "prime_ideal(«R», q) ∧ maximal_ideal(«R», q) ∧ q ≠ {L.zero}",
			},
			Derive(func(d *Argument) {
				d.FixAs[Nat]("k")
				q := d.FixAs[Set[A]]("q")
				positive := d.Assume()
				d.Cases(d.TermAs[Bool]("q = m"))
				d.When(
					"the replaced coordinate is m itself",
					func(e *Argument, equal Fact) {
						e.Show(
							"m is a nonzero maximal prime",
							Simp(Fwd(equal)),
							By(mPrime, parts[2], parts[3]))
					})
				d.Otherwise(
					"every other coordinate keeps its original exponent",
					func(e *Argument, unequal Fact) {
						oldPositive := e.Have(
							"the original exponent is nonzero",
							"v(q) ≠ 0",
							By(Normalized, unequal, positive))
						e.Show(
							"the original factor retains its properties",
							By(oldPositive, maximalFactors.At(q), productParts[1].At(q)))
					})
			}))
		original := arg.Have(
			"restoring the original m coordinate restores the vector",
			"«Coordinate»(v, v(m)) = v",
			Derive(func(d *Argument) {
				d.Do(Funext())
				d.FixAs[Set[A]]("q")
				d.Cases(d.TermAs[Bool]("q = m"))
				d.When(
					"the m coordinate takes its original value",
					func(e *Argument, equal Fact) {
						e.Show(
							"both functions have the original m value",
							Simp(Fwd(equal)),
							Basic())
					})
				d.Otherwise(
					"the other coordinates are unchanged",
					func(e *Argument, unequal Fact) {
						e.Show(
							"both functions have the original value",
							By(Normalized, unequal))
					})
			}))
		vm := arg.TermAs[Nat]("v(m)")
		someExponent := arg.Have(
			"some m exponent places the product inside the principal ideal",
			"∃k:num. «ProductAt»(v, k) ⊆ «Principal»(a)",
			Derive(func(d *Argument) {
				d.Take(vm)
				d.Show(
					"the original exponent works",
					Simp(Fwd(original)),
					By(productParts[2]))
			}))
		property := arg.TermAs[Set[Nat]]("λk:num. «ProductAt»(v, k) ⊆ «Principal»(a)")
		k, least := arg.ObtainAs[Nat](
			"choose the least successful exponent of m",
			"∃k:num. "+
				"    «ProductAt»(v, k) ⊆ «Principal»(a) ∧ (∀j:num. j < k ⇒ ¬(«ProductAt»(v, j) ⊆ «Principal»(a)))",
			By(someExponent, nat_order.WellOrdering.At(property)),
			Named("k"))
		primeFactors := arg.Have(
			"every replaced positive factor is prime",
			"∀k:num. ∀q:set(A). «Coordinate»(v, k, q) ≠ 0 ⇒ prime_ideal(«R», q)",
			By(factorData))
		idealFactors := arg.Have(
			"every replaced positive factor is integral",
			"∀k:num. ∀q:set(A). «Coordinate»(v, k, q) ≠ 0 ⇒ ring_ideal(«R», q)",
			By(primeFactors, ring_ideal.PrimeIdealIdeal))

		// k is not 0: with no m factor the product would lie in m, so one of its primes would be m.
		positiveK := arg.Have(
			"the least successful exponent is not zero",
			"k ≠ 0",
			Derive(func(d *Argument) {
				zero := d.SupposeNot()
				contained := d.Have(
					"the product with m deleted would lie in m",
					"«ProductAt»(v, 0) ⊆ m",
					Derive(func(e *Argument) {
						leastParts := e.Conjuncts(
							least,
							"the least product lies in the principal ideal",
							"every smaller exponent fails")
						equalZero := e.Have(
							"the supposed exponent equals zero",
							"k = 0",
							By(zero))
						atZero := e.Simplified(leastParts[0], Fwd(equalZero))
						e.Show(
							"the principal ideal lies in m",
							BySets(atZero, principalInM))
					}))
				zeroVector := d.TermAs[Fun[Set[A], Nat]]("«Coordinate»(v, 0)")
				zeroNum := d.TermAs[Nat]("0")
				q, selected := d.ObtainAs[Set[A]](
					"detect a supported prime factor in m",
					"∃q:set(A). «Coordinate»(v, 0, q) ≠ 0 ∧ q ⊆ m",
					By(
						mPrime,
						finiteSupports.At(zeroNum),
						idealFactors.At(zeroNum),
						contained,
						IdealProductSubsetPrime.Read(ringS).At(m, zeroVector)),
					Named("q"))
				equal := d.Have(
					"maximality identifies the detected factor with m",
					"m = q",
					By(
						factorData.At(zeroNum, q),
						mIdeal,
						parts[2],
						ring_ideal.MaximalIdealProper.At(r, m),
						selected,
						ring_ideal.MaximalIdealMaximal.At(r, q, m)))
				d.Show(
					"the m coordinate of the deleted vector is zero",
					By(Normalized, equal, selected))
			}))

		// k is n + 1, and the product J at n escapes (a): some b in J lies outside it.
		n, successor := arg.ObtainAs[Nat](
			"write the least exponent as a successor",
			"∃n:num. k = suc(n)",
			By(Normalized, positiveK, peano.Cases.At(k)),
			Named("n"))
		smaller := arg.Have(
			"the predecessor is smaller than the least exponent",
			"n < k",
			By(Normalized, successor, nat_order.LessThanSucClause.At(n, n)))
		leastParts := arg.Conjuncts(
			least,
			"the least product lies in the principal ideal",
			"smaller exponents fail")
		escaped := arg.Have(
			"the predecessor product escapes the principal ideal",
			"¬(«ProductAt»(v, n) ⊆ «Principal»(a))",
			By(smaller, leastParts[1].At(n)))
		previousVector := arg.TermAs[Fun[Set[A], Nat]]("«Coordinate»(v, n)")
		jIdeal := arg.Have(
			"the predecessor product is integral",
			"ring_ideal(«R», «ProductAt»(v, n))",
			By(
				finiteSupports.At(n),
				idealFactors.At(n),
				IdealExponentProductIntegral.Read(ringS).At(previousVector)))
		J, jDef := arg.LetAs[Set[A]]("J", "«ProductAt»(v, n)")
		arg.Let("P", principal)
		P := arg.TermAs[Set[A]]("P")
		b, witness := arg.ObtainAs[A](
			"choose a predecessor-product element outside the principal ideal",
			"∃b:A. b ∈ J ∧ b ∉ P",
			BySets(escaped),
			Named("b"))
		bIn := arg.Have(
			"b lies in the subring and field",
			"b ∈ S ∧ b ∈ L.carrier",
			BySets(witness, jIdeal, ring_ideal.IdealSubset.At(r, J), sInL))

		// mJ is the product at k, inside (a): so b/a lies in (S : m), and not in S.
		incremented := arg.Have(
			"incrementing the predecessor vector gives the least vector",
			"(λq:set(A). COND(q = m, «Coordinate»(v, n, m) + 1, «Coordinate»(v, n, q))) = «Coordinate»(v, k)",
			Derive(func(d *Argument) {
				d.Do(Funext())
				d.FixAs[Set[A]]("q")
				d.Cases(d.TermAs[Bool]("q = m"))
				d.When(
					"the m coordinate increases from the predecessor to k",
					func(e *Argument, equal Fact) {
						e.Show(
							"the successor is the predecessor plus one",
							Simp(Fwd(equal)),
							ByArith(successor))
					})
				d.Otherwise(
					"all other coordinates keep their exponent",
					func(e *Argument, unequal Fact) {
						e.Show(
							"the unchanged coordinates agree",
							By(Normalized, unequal))
					})
			}))
		productStep := arg.Have(
			"the least product is m times the predecessor ideal",
			"«ProductAt»(v, k) = ideal_mul(«R», m, J)",
			Simp(Fwd(jDef), Rev(incremented)),
			By(
				mIdeal,
				finiteSupports.At(n),
				idealFactors.At(n),
				IdealExponentProductIncrement.Read(ringS).At(m, previousVector)))
		productContained := arg.Have(
			"m times the predecessor ideal lies in P",
			"ideal_mul(«R», m, J) ⊆ P",
			Simp(Rev(productStep)),
			By(leastParts[0]))
		productsInP := arg.Have(
			"b times every member of m lies in P",
			"∀z:A. z ∈ m ⇒ L.mul(b, z) ∈ P",
			Derive(func(d *Argument) {
				z := d.FixAs[A]("z")
				zIn := d.Assume()
				zCarrier := d.Have(
					"z lies in the subring and field",
					"z ∈ S ∧ z ∈ L.carrier",
					BySets(zIn, mInS, sInL))
				held := d.Have(
					"the two selected factors give a product element",
					"L.mul(z, b) ∈ ideal_mul(«R», m, J)",
					By(zIn, witness, ring_ideal.IdealMulHolds.At(r, m, J, z, b)))
				commuted := d.Have(
					"the two scalar factors commute",
					"L.mul(b, z) = L.mul(z, b)",
					ByArith(fieldRing, bIn, zCarrier))
				d.Show(
					"the product containment puts b times z in P",
					BySets(commuted, held, productContained))
			}))
		quotient := arg.TermAs[A]("L.div(b, a)")
		quotientIn := arg.Have(
			"the quotient lies in the field",
			"L.div(b, a) ∈ L.carrier",
			By(bIn, aIn, field.DivIn.Read(L).AsFact().At(b, a)))
		elements := arg.Have(
			"every principal element has a scalar coefficient and zero remainder",
			"∀y:A. y ∈ P ⇒ ∃r t:A. r ∈ S ∧ t = L.zero ∧ y = L.add(L.mul(r, a), t)",
			Simp(Fwd(expansion)),
			BySets())
		cancelDenominator := arg.Have(
			"multiplication by a clears the quotient",
			"L.mul(a, L.div(b, a)) = b",
			By(bIn, aIn, nonzero, field.DivLeftMulOn.Read(L).AsFact().At(b, a)))
		quotientStable := arg.Have(
			"the quotient sends m into S",
			"∀z:A. z ∈ m ⇒ L.mul(L.div(b, a), z) ∈ S",
			Derive(func(d *Argument) {
				z := d.FixAs[A]("z")
				zIn := d.Assume()
				zCarrier := d.Have(
					"z lies in the subring and field",
					"z ∈ S ∧ z ∈ L.carrier",
					BySets(zIn, mInS, sInL))
				bz := d.TermAs[A]("L.mul(b, z)")
				rElem, _, coefficient := d.Obtain2As[A, A](
					"write b times z using a principal coefficient",
					"∃r t:A. r ∈ S ∧ t = L.zero ∧ L.mul(b, z) = L.add(L.mul(r, a), t)",
					By(zIn, productsInP.At(z), elements.At(bz)),
					Named("r", "t"))
				rCarrier := d.Have(
					"the principal coefficient lies in the field",
					"r ∈ L.carrier",
					BySets(coefficient, sInL))
				regroup := d.Have(
					"regroup a with the quotient before multiplying z",
					"L.mul(a, L.mul(L.div(b, a), z)) = L.mul(L.mul(a, L.div(b, a)), z)",
					ByArith(fieldRing, aIn, quotientIn, zCarrier))
				scaled := d.Have(
					"the quotient product and coefficient agree after multiplication by a",
					"L.mul(a, L.mul(L.div(b, a), z)) = L.mul(a, r)",
					Simp(Fwd(regroup), Fwd(cancelDenominator)),
					Derive(func(e *Argument) {
						coefficientParts := e.Conjuncts(
							coefficient,
							"the coefficient lies in S",
							"the remainder is zero",
							"the principal equation holds")
						e.Show(
							"remove the zero remainder and commute the scalar factors",
							Simp(Fwd(coefficientParts[2]), Fwd(coefficientParts[1])),
							ByArith(fieldRing, aIn, rCarrier))
					}))
				quotientProduct := d.TermAs[A]("L.mul(L.div(b, a), z)")
				productCarrier := d.Have(
					"the quotient product lies in the field",
					"L.mul(L.div(b, a), z) ∈ L.carrier",
					By(quotientIn, zCarrier, comm_ring.MulIn.Read(fieldRing).AsFact().At(quotient, z)))
				equal := d.Have(
					"cancel the nonzero factor a",
					"L.mul(L.div(b, a), z) = r",
					By(
						aIn,
						nonzero,
						productCarrier,
						rCarrier,
						scaled,
						integral_domain.MulCancelLeft.Read(integral_domain.FieldIntegralDomain.Read(L)).AsFact().At(
							a, quotientProduct, rElem)))
				d.Show(
					"the quotient product is the coefficient in S",
					BySets(equal, coefficient))
			}))
		inInverse := arg.Have(
			"the quotient belongs to the inverse ideal",
			"L.div(b, a) ∈ fractional_inverse(field_ring(L), S, m)",
			Simp(Fwd(fractional_ideal.FractionalInverseDef)),
			BySets(quotientIn, quotientStable))
		outside := arg.Have(
			"the quotient lies outside S",
			"L.div(b, a) ∉ S",
			Derive(func(d *Argument) {
				denied := d.SupposeNot()
				inside := d.Have(
					"suppose the quotient belongs to S",
					"L.div(b, a) ∈ S",
					By(denied))
				held := d.Have(
					"its scalar multiple of a lies in P",
					"L.mul(L.div(b, a), a) ∈ P",
					By(inside, aInPrincipal, principalIdeal, ring_ideal.IdealMul.At(r, P, quotient, a)))
				cleared := d.Have(
					"the multiple is b",
					"L.mul(L.div(b, a), a) = b",
					By(bIn, aIn, nonzero, field.DivRightMulOn.Read(L).AsFact().At(b, a)))
				d.Show(
					"b would lie in the principal ideal",
					BySets(held, cleared, witness))
			}))
		scalars := arg.Have(
			"subring scalars send m into S",
			"∀s z:A. s ∈ S ∧ z ∈ m ⇒ L.mul(s, z) ∈ S",
			Derive(func(d *Argument) {
				s, z := d.FixAs[A]("s"), d.FixAs[A]("z")
				members := d.Assume()
				held := d.Have(
					"the ideal absorbs multiplication by the subring scalar",
					"L.mul(s, z) ∈ m",
					By(members, mIdeal, ring_ideal.IdealMul.At(r, m, s, z)))
				d.Show(
					"the resulting ideal element belongs to S",
					BySets(held, mInS))
			}))
		included := arg.Have(
			"S is contained in the inverse ideal",
			"S ⊆ fractional_inverse(field_ring(L), S, m)",
			Simp(Fwd(fractional_ideal.FractionalInverseDef)),
			BySets(sInL, scalars))
		arg.Show(
			"the inverse strictly contains S",
			BySets(included, inInverse, outside))
	}),
})}

// NonzeroIdealStabilizer — an ambient scalar stabilizing a nonzero ideal lies in
// the integrally closed subring: a fixed nonzero ideal element clears every power.
var NonzeroIdealStabilizer = nonzeroIdealStabilizerThm{family.Add(registry.ProofEntry{
	Name: "NonzeroIdealStabilizer",
	Key:  "prop_44961d6f9ad18020",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S I:set(A). ∀x:A.",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"∀H:set(A). " +
				"    ring_ideal(restrict_ring(field_ring(L), S), H) ∧ H ≠ {L.zero} ⇒ " +
				"    finite(left_cosets(L.add, S, H))",
			"integrally_closed_in(restrict_ring(field_ring(L), S), L.carrier)",
			"ring_ideal(restrict_ring(field_ring(L), S), I)",
			"I ≠ {L.zero}",
			"x ∈ L.carrier",
			"image(L.mul(x), I) ⊆ I",
		},
		Conclusion: "x ∈ S",
	}, func(a *Argument, L field.FieldFact[on.L], S, I *Expr[Set[A]], x *Expr[A], h Fact) {
		parts := a.Conjuncts(
			h,
			"S is a subring of L",
			"nonzero ideals have finite quotient",
			"the subring is integrally closed",
			"I is an ideal",
			"I is nonzero",
			"the scalar lies in the field",
			"multiplication by the scalar preserves I")
		subring, finiteQuotients, closed := parts[0], parts[1], parts[2]
		ideal, nontrivial, xIn, stable := parts[3], parts[4], parts[5], parts[6]
		fieldRing := field.RingOn.Read(L)
		fieldMonoid := comm_ring.MulMonoidOn.Read(fieldRing)
		xm := a.MemberOf[on.L](x, xIn)
		idealSubset := a.Have(
			"ideal elements lie in the subring",
			"I ⊆ S",
			By(ideal, ring_ideal.IdealSubset))
		c, nonzero := a.ObtainAs[A](
			"choose a nonzero ideal element",
			"∃c:A. c ∈ I ∧ c ≠ L.zero",
			BySets(nontrivial, ideal, ring_ideal.IdealZero),
			Named("c"))
		carrier := a.Have(
			"the chosen element lies in the subring and field",
			"c ∈ S ∧ c ∈ L.carrier",
			BySets(nonzero, idealSubset, comm_ring.SubringSubset.Read(subring)))
		powersStayInI := a.Have(
			"all powers multiplied by c stay in I",
			"∀j:num. c * monoid_pow(L.mul, L.one, x, j) ∈ I",
			Derive(func(b *Argument) {
				b.Induct("j")
				b.Base(
					"the zeroth power gives c",
					Simp(Fwd(comm_monoid.MonoidPowDef), Fwd(comm_monoid.RightIdentityOn.Read(fieldMonoid))),
					By(nonzero))
				b.Step(
					"stability carries one power to the next",
					func(b *Argument, ih Fact) {
						multiplied := b.Have(
							"multiply the ideal element once more by x",
							"x * (c * monoid_pow(L.mul, L.one, x, j)) ∈ I",
							BySets(ih, stable))
						regroup := b.Have(
							"the successor power regroups across c",
							"c * monoid_pow(L.mul, L.one, x, suc(j)) = x * (c * monoid_pow(L.mul, L.one, x, j))",
							Simp(Fwd(comm_monoid.MonoidPowDef)),
							ByArith(fieldRing, xIn, comm_monoid.PowIn.Read(fieldMonoid), carrier))
						b.Show(
							"the successor power stays in I",
							By(regroup, multiplied))
					})
			}))
		powersStayInS := a.Have(
			"c clears every power into the subring",
			"∀j:num. c * monoid_pow(L.mul, L.one, x, j) ∈ S",
			BySets(powersStayInI, idealSubset))
		integral := a.Have(
			"almost integrality gives integrality",
			"integral_over(restrict_ring(field_ring(L), S), x)",
			By(
				subring,
				finiteQuotients,
				nonzero,
				carrier,
				powersStayInS,
				AlmostIntegralIsIntegral.Read(L).At(S, xm, c)))
		integralClosedness := a.Unfolded(closed, integral_element.IntegrallyClosedDef)
		a.Show(
			"integral closedness places x in the subring",
			By(integral, xIn, integralClosedness.At(x)))
	}),
})}

// NonzeroMaximalInvertible — a nonzero maximal ideal is invertible: its
// product with the inverse is an integral ideal, and equality with the
// maximal ideal would make the strictly larger inverse stabilize it.
var NonzeroMaximalInvertible = nonzeroMaximalInvertibleThm{family.Add(registry.ProofEntry{
	Name: "NonzeroMaximalInvertible",
	Key:  "prop_ecedaf749bfa2217",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S m:set(A).",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"∀H:set(A). " +
				"    ring_ideal(restrict_ring(field_ring(L), S), H) ∧ H ≠ {L.zero} ⇒ " +
				"    finite(left_cosets(L.add, S, H))",
			"integrally_closed_in(restrict_ring(field_ring(L), S), L.carrier)",
			"maximal_ideal(restrict_ring(field_ring(L), S), m)",
			"m ≠ {L.zero}",
		},
		Conclusion: "invertible_fractional(field_ring(L), S, m)",
	}, func(a *Argument, L field.FieldFact[on.L], S, m *Expr[Set[A]], h Fact) {
		parts := a.Conjuncts(
			h,
			"S is a subring of L",
			"nonzero ideal quotients are finite",
			"S is integrally closed in L",
			"m is maximal",
			"m is nonzero")
		subringS, maximal := parts[0], parts[3]
		ring := a.Have(
			"S is a ring under L's operations",
			"comm_ring_on(restrict_ring(field_ring(L), S))",
			By(subringS, comm_ring.SubringRingOn.Read(field.RingOn.Read(L)).At(S)))
		ambient := a.TermAs[RingOps[A]]("field_ring(L)")
		inverse := a.TermAs[Set[A]]("fractional_inverse(field_ring(L), S, m)")
		product := a.TermAs[Set[A]](
			"fractional_mul(field_ring(L), S, m, fractional_inverse(field_ring(L), S, m))")
		fieldRing := field.RingOn.Read(L)

		ideal := a.Have(
			"m is an ideal of S",
			"ring_ideal(restrict_ring(field_ring(L), S), m)",
			By(maximal, ring_ideal.MaximalIdealIdeal))
		mInL := a.Have(
			"m lies in L",
			"m ⊆ L.carrier",
			BySets(ring_ideal.IdealSubset.Read(ideal), comm_ring.SubringSubset.Read(subringS)))
		mSubmodule := a.Have(
			"m is an S-submodule of L",
			"submodule(restrict_ring(field_ring(L), S), regular_module(field_ring(L)), m)",
			By(subringS, ideal, fractional_ideal.IntegralIdealFractional.Read(L).At(S, m)))
		inverseInL := a.Have(
			"the inverse lies in L",
			"fractional_inverse(field_ring(L), S, m) ⊆ L.carrier",
			By(fractional_ideal.FractionalInverseSubset.Read(L)))
		productSubmodule := a.Have(
			"the inverse product is an S-submodule of L",
			"submodule(restrict_ring(field_ring(L), S), "+
				"    regular_module(field_ring(L)), "+
				"    fractional_mul(field_ring(L), S, m, fractional_inverse(field_ring(L), S, m)))",
			By(subringS, mInL, inverseInL, fractional_ideal.FractionalMulSubmodule.Read(L)))
		generators := a.Have(
			"the product generators lie in S",
			"∀r x:A. r ∈ m ∧ x ∈ fractional_inverse(field_ring(L), S, m) ⇒ r * x ∈ S",
			Derive(func(b *Argument) {
				b.FixAs[A]("r")
				b.FixAs[A]("x")
				members := b.Assume()
				inField := b.Have(
					"both factors lie in L",
					"r ∈ L.carrier ∧ x ∈ L.carrier",
					BySets(members, mInL, inverseInL))
				reversed := b.Have(
					"the inverse sends m into S",
					"x * r ∈ S",
					BySets(members, fractional_ideal.FractionalInverseDef.At(ambient, S, m)))
				commute := b.Have(
					"the two factors commute",
					"r * x = x * r",
					ByArith(fieldRing, inField))
				b.Show(
					"each generator lies in S",
					commute.Rw(),
					By(reversed))
			}))
		productInS := a.Have(
			"the product lies in S",
			"fractional_mul(field_ring(L), S, m, fractional_inverse(field_ring(L), S, m)) ⊆ S",
			By(
				generators,
				subringS,
				fractional_ideal.SubringSubmodule.Read(L).At(S),
				fractional_ideal.FractionalMulLeast.Read(L)))
		productIdeal := a.Have(
			"the product is an ideal of S",
			"ring_ideal(restrict_ring(field_ring(L), S), "+
				"    fractional_mul(field_ring(L), S, m, fractional_inverse(field_ring(L), S, m)))",
			By(
				subringS,
				productSubmodule,
				productInS,
				fractional_ideal.IntegralIdealFractional.Read(L).At(S, product)))

		strict := a.Have(
			"the inverse strictly contains S",
			"S ⊆ fractional_inverse(field_ring(L), S, m) ∧ S ≠ fractional_inverse(field_ring(L), S, m)",
			By(h, MaximalInverseStrict.Read(L)))
		oneInInverse := a.Have(
			"the inverse holds one",
			"L.one ∈ fractional_inverse(field_ring(L), S, m)",
			BySets(strict, comm_ring.OneIn.Read(ring)))
		mInProduct := a.Have(
			"the product contains m",
			"m ⊆ fractional_mul(field_ring(L), S, m, fractional_inverse(field_ring(L), S, m))",
			Simp(Fwd(set_basic.SubsetDef)),
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				inM := b.Assume()
				xInL := b.Have(
					"this element of m lies in L",
					"x ∈ L.carrier",
					BySets(inM, mInL))
				unit := b.Have(
					"multiplication by one fixes x",
					"x * L.one = x",
					ByArith(fieldRing, xInL))
				generator := b.Have(
					"multiplication by one gives a product generator",
					"x * L.one ∈ fractional_mul(field_ring(L), S, m, fractional_inverse(field_ring(L), S, m))",
					By(
						inM,
						oneInInverse,
						fractional_ideal.FractionalMulHolds.Read(L).At(S, m, inverse, x, b.TermAs[A]("L.one"))))
				b.Show(
					"x lies in the product",
					By(unit, generator))
			}))
		dichotomy := a.Have(
			"maximality leaves equality with m or a product containing one",
			"fractional_mul(field_ring(L), S, m, fractional_inverse(field_ring(L), S, m)) = m ∨ "+
				"L.one ∈ fractional_mul(field_ring(L), S, m, fractional_inverse(field_ring(L), S, m))",
			By(productIdeal, mInProduct, ring_ideal.MaximalIdealMaximal.Read(maximal)))
		integralInverse := a.Have(
			"equality with m would put every inverse element in S",
			Statement{
				Hypotheses: []string{
					"fractional_mul(field_ring(L), S, m, fractional_inverse(field_ring(L), S, m)) = m",
				},
				Conclusion: "fractional_inverse(field_ring(L), S, m) ⊆ S",
			},
			Derive(func(b *Argument) {
				equalsM := b.Assume()
				b.Do(Simp(Fwd(set_basic.SubsetDef)))
				x := b.FixAs[A]("x")
				xInInverse := b.Assume()
				xInL := b.Have(
					"an inverse element lies in L",
					"x ∈ L.carrier",
					BySets(xInInverse, inverseInL))
				stabilizes := b.Have(
					"this inverse element preserves m",
					"∀y:A. y ∈ m ⇒ x * y ∈ m",
					Derive(func(c *Argument) {
						y := c.FixAs[A]("y")
						yInM := c.Assume()
						yInL := c.Have(
							"an element of m lies in L",
							"y ∈ L.carrier",
							BySets(yInM, mInL))
						commute := c.Have(
							"the inverse element commutes with y",
							"x * y = y * x",
							ByArith(fieldRing, xInL, yInL))
						generator := c.Have(
							"their product lies in the inverse product",
							"y * x ∈ fractional_mul(field_ring(L), S, m, fractional_inverse(field_ring(L), S, m))",
							By(yInM, xInInverse, fractional_ideal.FractionalMulHolds.Read(L).At(S, m, inverse, y, x)))
						c.Show(
							"the product lies in m",
							By(Normalized, commute, generator, equalsM))
					}))
				imageInM := b.Have(
					"multiplication by x maps m into itself",
					"image(L.mul(x), m) ⊆ m",
					BySets(stabilizes))
				b.Show(
					"the nonzero ideal stabilizer belongs to S",
					By(h, ideal, xInL, imageInM, NonzeroIdealStabilizer.Read(L).At(S, m, b.MemberOf[on.L](x, xInL))))
			}))
		strictProduct := a.Have(
			"strictness of the inverse rules out equality with m",
			"fractional_mul(field_ring(L), S, m, fractional_inverse(field_ring(L), S, m)) ≠ m",
			BySets(strict, integralInverse))
		unitProduct := a.Have(
			"so the product, holding one, is the unit ideal",
			"fractional_mul(field_ring(L), S, m, fractional_inverse(field_ring(L), S, m)) = S",
			By(strictProduct, dichotomy, productIdeal, ring_ideal.IdealOneIff.Read(ring)))
		a.Show(
			"m is invertible",
			By(unitProduct, mSubmodule, fractional_ideal.InvertibleFractionalDef))
	}),
})}

// DivideByInvertibleIdeal — dividing an ideal contained in an invertible integral
// ideal gives a nonzero integral ideal containing it, with the original ideal
// recovered by multiplication: monotonicity bounds the quotient by S, and
// associativity and the inverse equation cancel the divisor.
var DivideByInvertibleIdeal = divideByInvertibleIdealThm{family.Add(registry.ProofEntry{
	Name: "DivideByInvertibleIdeal",
	Key:  "prop_c2dac2264463d979",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S I M:set(A).",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"ring_ideal(restrict_ring(field_ring(L), S), I)",
			"I ≠ {L.zero}",
			"ring_ideal(restrict_ring(field_ring(L), S), M)",
			"I ⊆ M",
			"invertible_fractional(field_ring(L), S, M)",
		},
		Conclusion: "ring_ideal(restrict_ring(field_ring(L), S), «Quotient») ∧ " +
			"«Quotient» ≠ {L.zero} ∧ " +
			"I = fractional_mul(field_ring(L), S, M, «Quotient») ∧ " +
			"I ⊆ «Quotient»",
		Abbrev: Abbrev{
			{Name: "Quotient", Text: "fractional_mul(field_ring(L), " +
				"    S, " +
				"    I, " +
				"    fractional_inverse(field_ring(L), S, M))"},
		},
	}, func(a *Argument, L field.FieldFact[on.L], S, I, M *Expr[Set[A]], h Fact) {
		parts := a.Conjuncts(
			h,
			"S is a subring of L",
			"I is an ideal",
			"I is nonzero",
			"M is an ideal",
			"I lies in M",
			"M is invertible")
		subringS := parts[0]
		sInL := a.Have(
			"S lies in L",
			"S ⊆ L.carrier",
			By(comm_ring.SubringSubset.Read(subringS)))
		r := a.TermAs[RingOps[A]]("restrict_ring(field_ring(L), S)")
		ambientRing := a.TermAs[RingOps[A]]("field_ring(L)")
		inverse := a.TermAs[Set[A]]("fractional_inverse(field_ring(L), S, M)")
		J, jDef := a.LetAs[Set[A]](
			"J", "fractional_mul(field_ring(L), S, I, fractional_inverse(field_ring(L), S, M))")

		mInS := a.Have(
			"M lies in S",
			"M ⊆ S",
			By(parts[3], ring_ideal.IdealSubset.At(r, M)))
		iInL := a.Have(
			"I lies in the field",
			"I ⊆ L.carrier",
			BySets(parts[1], ring_ideal.IdealSubset.At(r, I), sInL))
		mInL := a.Have(
			"M lies in the field",
			"M ⊆ L.carrier",
			BySets(mInS, sInL))
		iFractional := a.Have(
			"I is an S-submodule of L",
			"submodule(restrict_ring(field_ring(L), S), regular_module(field_ring(L)), I)",
			By(subringS, parts[1], fractional_ideal.IntegralIdealFractional.Read(L).At(S, I)))
		inverseInL := a.Have(
			"the inverse lies in L",
			"fractional_inverse(field_ring(L), S, M) ⊆ L.carrier",
			By(fractional_ideal.FractionalInverseSubset.Read(L).At(S, M)))
		jFractional := a.Have(
			"J is an S-submodule of L",
			"submodule(restrict_ring(field_ring(L), S), regular_module(field_ring(L)), J)",
			By(
				Normalized,
				subringS,
				iInL,
				inverseInL,
				jDef,
				fractional_ideal.FractionalMulSubmodule.Read(L).At(S, I, inverse)))
		cancel := a.Have(
			"M times its inverse is S",
			"fractional_mul(field_ring(L), S, M, fractional_inverse(field_ring(L), S, M)) = S",
			By(parts[5], fractional_ideal.InvertibleFractionalDef.At(ambientRing, S, M)))
		bounded := a.Have(
			"multiplying I contained in M bounds J",
			"J ⊆ fractional_mul(field_ring(L), S, M, fractional_inverse(field_ring(L), S, M))",
			By(
				Normalized,
				parts[4],
				jDef,
				set_order.SubsetRefl,
				fractional_ideal.FractionalMulMono.Read(L).At(S, I, M, inverse, inverse)))
		jInS := a.Have(
			"J lies in S",
			"J ⊆ S",
			By(Normalized, bounded, cancel))
		sInInverse := a.Have(
			"S lies in the inverse because S times M lies in S",
			"S ⊆ fractional_inverse(field_ring(L), S, M)",
			BySets(
				sInL,
				mInS,
				fractional_ideal.FractionalInverseDef.At(ambientRing, S, M),
				comm_ring.SubringMul.Read(subringS)))

		integral := a.Have(
			"J is an integral ideal",
			"ring_ideal(restrict_ring(field_ring(L), S), J)",
			By(subringS, jInS, jFractional, fractional_ideal.IntegralIdealFractional.Read(L).At(S, J)))
		leftUnit := a.Have(
			"S acts as the unit on I",
			"fractional_mul(field_ring(L), S, S, I) = I",
			By(subringS, iFractional, fractional_ideal.FractionalMulOne.Read(L).At(S, I)))
		rightUnit := a.Have(
			"I times S is I",
			"fractional_mul(field_ring(L), S, I, S) = I",
			By(Normalized, sInL, iInL, leftUnit, fractional_ideal.FractionalMulComm.Read(L).At(S, I, S)))
		enlargesUnit := a.Have(
			"replacing S by the inverse enlarges the product",
			"fractional_mul(field_ring(L), S, I, S) ⊆ J",
			By(
				Normalized,
				sInInverse,
				jDef,
				set_order.SubsetRefl,
				fractional_ideal.FractionalMulMono.Read(L).At(S, I, I, S, inverse)))
		contains := a.Have(
			"J contains I",
			"I ⊆ J",
			By(Normalized, rightUnit, enlargesUnit))
		nonzero := a.Have(
			"an ideal containing the nonzero ideal I is nonzero",
			"J ≠ {L.zero}",
			BySets(contains, parts[2], parts[1], ring_ideal.IdealZero.At(r, I)))
		recovers := a.Have(
			"multiplication by M recovers I",
			"I = fractional_mul(field_ring(L), S, M, J)",
			CalcEq(
				Leg(
					a.TermAs[Set[A]]("fractional_mul(field_ring(L), S, I, S)"),
					"insert the scalar unit",
					Simp(Fwd(rightUnit)),
					Basic()),
				Leg(
					a.TermAs[Set[A]](
						"fractional_mul(field_ring(L), "+
							"    S, "+
							"    I, "+
							"    fractional_mul(field_ring(L), S, M, fractional_inverse(field_ring(L), S, M)))"),
					"replace S by M times its inverse",
					Simp(Fwd(cancel)),
					Basic()),
				Leg(
					a.TermAs[Set[A]](
						"fractional_mul(field_ring(L), "+
							"    S, "+
							"    fractional_mul(field_ring(L), S, I, M), "+
							"    fractional_inverse(field_ring(L), S, M))"),
					"associate the first two factors",
					By(
						subringS,
						iInL,
						mInL,
						inverseInL,
						fractional_ideal.FractionalMulAssoc.Read(L).At(S, I, M, inverse))),
				Leg(
					a.TermAs[Set[A]](
						"fractional_mul(field_ring(L), "+
							"    S, "+
							"    fractional_mul(field_ring(L), S, M, I), "+
							"    fractional_inverse(field_ring(L), S, M))"),
					"commute I and M",
					By(Normalized, iInL, mInL, fractional_ideal.FractionalMulComm.Read(L).At(S, I, M))),
				FinalLeg(
					"associate I with the inverse to form J",
					By(
						subringS,
						iInL,
						mInL,
						inverseInL,
						jDef,
						fractional_ideal.FractionalMulAssoc.Read(L).At(S, M, I, inverse)))))
		a.Show(
			"J is integral, nonzero, recovers I, and contains I",
			By(integral, nonzero, recovers, contains))
	}),
})}

// InvertibleMulCancel — an invertible fractional factor cancels from a product
// equation: multiply by its inverse and associate the resulting products.
var InvertibleMulCancel = invertibleMulCancelThm{family.Add(registry.ProofEntry{
	Name: "InvertibleMulCancel",
	Key:  "prop_d2a7d871ec459296",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S M X Y:set(A).",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"invertible_fractional(field_ring(L), S, M)",
			"submodule(restrict_ring(field_ring(L), S), regular_module(field_ring(L)), X)",
			"submodule(restrict_ring(field_ring(L), S), regular_module(field_ring(L)), Y)",
			"fractional_mul(field_ring(L), S, M, X) = fractional_mul(field_ring(L), S, M, Y)",
		},
		Conclusion: "X = Y",
	}, func(a *Argument, L field.FieldFact[on.L], S, M, X, Y *Expr[Set[A]], h Fact) {
		p := a.Conjuncts(
			h,
			"S is a subring of L",
			"M is invertible",
			"X is fractional",
			"Y is fractional",
			"their products with M agree")
		r := a.TermAs[RingOps[A]]("restrict_ring(field_ring(L), S)")
		ambientRing := a.TermAs[RingOps[A]]("field_ring(L)")
		vectors := a.TermAs[module_record.ModuleOps[A, A]]("regular_module(field_ring(L))")
		inverse := a.TermAs[Set[A]]("fractional_inverse(field_ring(L), S, M)")
		mInL := a.Have(
			"M lies in L",
			"M ⊆ L.carrier",
			By(
				p[1],
				fractional_ideal.InvertibleFractionalDef.At(ambientRing, S, M),
				submodule.SubmoduleSubset.At(r, vectors, M)))
		inverseInL := a.Have(
			"the inverse lies in L",
			"fractional_inverse(field_ring(L), S, M) ⊆ L.carrier",
			By(fractional_ideal.FractionalInverseSubset.Read(L).At(S, M)))
		leftInverse := a.Have(
			"the inverse times M is S",
			"fractional_mul(field_ring(L), S, fractional_inverse(field_ring(L), S, M), M) = S",
			By(
				Normalized,
				mInL,
				inverseInL,
				p[1],
				fractional_ideal.InvertibleFractionalDef.At(ambientRing, S, M),
				fractional_ideal.FractionalMulComm.Read(L).At(S, inverse, M)))
		a.Show(
			"multiply the given equation by the inverse of M",
			CalcEq(
				Leg(
					a.TermAs[Set[A]]("fractional_mul(field_ring(L), S, S, X)"),
					"insert the unit on X",
					By(Normalized, p[0], p[2], fractional_ideal.FractionalMulOne.Read(L).At(S, X))),
				Leg(
					a.TermAs[Set[A]](
						"fractional_mul(field_ring(L), "+
							"    S, "+
							"    fractional_mul(field_ring(L), S, fractional_inverse(field_ring(L), S, M), M), "+
							"    X)"),
					"replace S by the inverse product",
					Simp(Fwd(leftInverse)),
					Basic()),
				Leg(
					a.TermAs[Set[A]](
						"fractional_mul(field_ring(L), "+
							"    S, "+
							"    fractional_inverse(field_ring(L), S, M), "+
							"    fractional_mul(field_ring(L), S, M, X))"),
					"associate the product with X",
					By(
						p[0],
						inverseInL,
						mInL,
						p[2],
						submodule.SubmoduleSubset.At(r, vectors, X),
						fractional_ideal.FractionalMulAssoc.Read(L).At(S, inverse, M, X))),
				Leg(
					a.TermAs[Set[A]](
						"fractional_mul(field_ring(L), "+
							"    S, "+
							"    fractional_inverse(field_ring(L), S, M), "+
							"    fractional_mul(field_ring(L), S, M, Y))"),
					"use the equality of products",
					Simp(Fwd(p[4])),
					Basic()),
				Leg(
					a.TermAs[Set[A]](
						"fractional_mul(field_ring(L), "+
							"    S, "+
							"    fractional_mul(field_ring(L), S, fractional_inverse(field_ring(L), S, M), M), "+
							"    Y)"),
					"associate the inverse product",
					By(
						p[0],
						inverseInL,
						mInL,
						p[3],
						submodule.SubmoduleSubset.At(r, vectors, Y),
						fractional_ideal.FractionalMulAssoc.Read(L).At(S, inverse, M, Y))),
				Leg(
					a.TermAs[Set[A]]("fractional_mul(field_ring(L), S, S, Y)"),
					"cancel M against its inverse",
					Simp(Fwd(leftInverse)),
					Basic()),
				FinalLeg(
					"remove the unit on Y",
					By(p[0], p[3], fractional_ideal.FractionalMulOne.Read(L).At(S, Y)))))
	}),
})}

// IntegralFractionalProduct — the fractional product of two integral ideals is
// integral and lies in either factor: monotonicity against the scalar unit
// bounds it by the second factor, and commuting the factors by the first.
var IntegralFractionalProduct = integralFractionalProductThm{family.Add(registry.ProofEntry{
	Name: "IntegralFractionalProduct",
	Key:  "prop_e59605cdc8170f56",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S M N:set(A).",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"ring_ideal(restrict_ring(field_ring(L), S), M)",
			"ring_ideal(restrict_ring(field_ring(L), S), N)",
		},
		Conclusion: "ring_ideal(restrict_ring(field_ring(L), S), " +
			"    fractional_mul(field_ring(L), S, M, N)) ∧ " +
			"fractional_mul(field_ring(L), S, M, N) ⊆ M ∧ " +
			"fractional_mul(field_ring(L), S, M, N) ⊆ N",
	}, func(a *Argument, L field.FieldFact[on.L], S, M, N *Expr[Set[A]], h Fact) {
		p := a.Conjuncts(
			h,
			"S is a subring of L",
			"M is integral",
			"N is integral")
		sInL := a.Have(
			"S lies in L",
			"S ⊆ L.carrier",
			By(comm_ring.SubringSubset.Read(p[0])))
		product := a.TermAs[Set[A]]("fractional_mul(field_ring(L), S, M, N)")
		mFractional := a.Have(
			"M is fractional and lies in S",
			"submodule(restrict_ring(field_ring(L), S), regular_module(field_ring(L)), M) ∧ M ⊆ S",
			By(p[0], p[1], fractional_ideal.IntegralIdealFractional.Read(L).At(S, M)))
		nFractional := a.Have(
			"N is fractional and lies in S",
			"submodule(restrict_ring(field_ring(L), S), regular_module(field_ring(L)), N) ∧ N ⊆ S",
			By(p[0], p[2], fractional_ideal.IntegralIdealFractional.Read(L).At(S, N)))
		mInL := a.Have(
			"M lies in L",
			"M ⊆ L.carrier",
			BySets(mFractional, sInL))
		nInL := a.Have(
			"N lies in L",
			"N ⊆ L.carrier",
			BySets(nFractional, sInL))
		fractional := a.Have(
			"the product is fractional",
			"submodule(restrict_ring(field_ring(L), S), "+
				"    regular_module(field_ring(L)), "+
				"    fractional_mul(field_ring(L), S, M, N))",
			By(p[0], mInL, nInL, fractional_ideal.FractionalMulSubmodule.Read(L).At(S, M, N)))
		unitN := a.Have(
			"S acts as the unit on N",
			"fractional_mul(field_ring(L), S, S, N) = N",
			By(p[0], nFractional, fractional_ideal.FractionalMulOne.Read(L).At(S, N)))
		inN := a.Have(
			"M contained in S bounds its product by N",
			"fractional_mul(field_ring(L), S, M, N) ⊆ N",
			By(
				Normalized,
				mFractional,
				unitN,
				set_order.SubsetRefl,
				fractional_ideal.FractionalMulMono.Read(L).At(S, M, S, N, N)))
		unitM := a.Have(
			"S acts as the unit on M",
			"fractional_mul(field_ring(L), S, S, M) = M",
			By(p[0], mFractional, fractional_ideal.FractionalMulOne.Read(L).At(S, M)))
		commute := a.Have(
			"the two factors commute",
			"fractional_mul(field_ring(L), S, M, N) = fractional_mul(field_ring(L), S, N, M)",
			By(mInL, nInL, fractional_ideal.FractionalMulComm.Read(L).At(S, M, N)))
		inM := a.Have(
			"N contained in S bounds the commuted product by M",
			"fractional_mul(field_ring(L), S, M, N) ⊆ M",
			commute.Rw(),
			By(
				Normalized,
				nFractional,
				unitM,
				set_order.SubsetRefl,
				fractional_ideal.FractionalMulMono.Read(L).At(S, N, S, M, M)))
		inS := a.Have(
			"the product therefore lies in S",
			"fractional_mul(field_ring(L), S, M, N) ⊆ S",
			BySets(inN, nFractional))
		integral := a.Have(
			"the product is integral",
			"ring_ideal(restrict_ring(field_ring(L), S), fractional_mul(field_ring(L), S, M, N))",
			By(p[0], fractional, inS, fractional_ideal.IntegralIdealFractional.Read(L).At(S, product)))
		a.Show(
			"the fractional product is an integral ideal contained in both factors",
			By(integral, inM, inN))
	}),
})}

// IntegralMulAsFractional — integral and fractional ideal multiplication agree:
// each product is the least span containing the elementary products.
var IntegralMulAsFractional = integralMulAsFractionalThm{family.Add(registry.ProofEntry{
	Name: "IntegralMulAsFractional",
	Key:  "prop_542d535509fc84d7",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S I J:set(A).",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"ring_ideal(«R», I)",
			"ring_ideal(«R», J)",
		},
		Conclusion: "ideal_mul(«R», I, J) = fractional_mul(field_ring(L), S, I, J)",
		Abbrev: Abbrev{
			{Name: "G", Text: "{x * y:A | x:A, y:A | x ∈ I ∧ y ∈ J}"},
		},
	}, func(a *Argument, L field.FieldFact[on.L], S, I, J *Expr[Set[A]], h Fact) {
		p := a.Conjuncts(
			h,
			"S is a subring of L",
			"I is integral",
			"J is integral")
		subringS := p[0]
		ringS := a.Have(
			"S is a ring under L's operations",
			"comm_ring_on(«R»)",
			By(subringS, comm_ring.SubringRingOn.Read(field.RingOn.Read(L)).At(S)))
		r := a.TermAs[RingOps[A]]("«R»")
		generators := a.TermAs[Set[A]]("«G»")
		integralProduct := a.TermAs[Set[A]]("ideal_mul(«R», I, J)")
		fractionalProduct := a.TermAs[Set[A]]("fractional_mul(field_ring(L), S, I, J)")
		factorsInS := a.Have(
			"both factors lie in S",
			"I ⊆ S ∧ J ⊆ S",
			By(p[1], p[2], ring_ideal.IdealSubset.At(r, I), ring_ideal.IdealSubset.At(r, J)))
		generatorsInS := a.Have(
			"the elementary products lie in S",
			"«G» ⊆ S",
			BySets(comm_ring.MulIn.Read(ringS), factorsInS))
		fractionalIntegral := a.Have(
			"the fractional product is integral",
			"ring_ideal(«R», fractional_mul(field_ring(L), S, I, J))",
			By(subringS, p[1], p[2], IntegralFractionalProduct.Read(L).At(S, I, J)))
		productSpan := a.Have(
			"the ideal product spans the elementary products",
			"ideal_mul(«R», I, J) = ideal_span(«R», «G»)",
			By(ring_ideal.IdealMulDef.At(r, I, J)))
		generatorsInFractional := a.Have(
			"the fractional product holds every generator",
			"«G» ⊆ fractional_mul(field_ring(L), S, I, J)",
			BySets(fractional_ideal.FractionalMulHolds.Read(L).AsFact().At(S, I, J)))
		integralInFractional := a.Have(
			"the least ideal span lies in the fractional product",
			"ideal_mul(«R», I, J) ⊆ fractional_mul(field_ring(L), S, I, J)",
			By(
				productSpan,
				fractionalIntegral,
				generatorsInFractional,
				ring_ideal.SpanLeast.At(r, generators, fractionalProduct)))
		productIdeal := a.Have(
			"the ideal product is an ideal",
			"ring_ideal(«R», ideal_mul(«R», I, J))",
			By(productSpan, generatorsInS, ring_ideal.SpanIdeal.Read(ringS).At(generators)))
		productFractional := a.Have(
			"the ideal product is a fractional submodule",
			"submodule(«R», regular_module(field_ring(L)), ideal_mul(«R», I, J))",
			By(subringS, productIdeal, fractional_ideal.IntegralIdealFractional.Read(L).At(S, integralProduct)))
		generatorsHeld := a.Have(
			"the ideal product holds every elementary product",
			"∀x y:A. x ∈ I ∧ y ∈ J ⇒ x * y ∈ ideal_mul(«R», I, J)",
			Derive(func(b *Argument) {
				b.FixAs[A]("x")
				b.FixAs[A]("y")
				members := b.Assume()
				generator := b.Have(
					"this elementary product is a generator",
					"x * y ∈ «G»",
					BySets(members))
				b.Show(
					"the span contains this generator",
					BySets(generator, productSpan, ring_ideal.SpanContains.At(r, generators)))
			}))
		fractionalInIntegral := a.Have(
			"the least fractional span lies in the ideal product",
			"fractional_mul(field_ring(L), S, I, J) ⊆ ideal_mul(«R», I, J)",
			By(
				generatorsHeld,
				productFractional,
				fractional_ideal.FractionalMulLeast.Read(L).At(S, I, J, integralProduct)))
		a.Show(
			"the two products coincide",
			By(integralInFractional, fractionalInIntegral, set_order.SubsetAntisym))
	}),
})}

// IntegralPowAsFractional — every natural power of an integral ideal is the
// same under integral and fractional ideal multiplication: both zeroth powers
// are S, and each further factor multiplies an integral power, where the two
// products agree.
var IntegralPowAsFractional = integralPowAsFractionalThm{family.Add(registry.ProofEntry{
	Name: "IntegralPowAsFractional",
	Key:  "prop_93e745c5d4214626",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S I:set(A). ∀n:num.",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"ring_ideal(«R», I)",
		},
		Conclusion: "ideal_pow(«R», I, n) = monoid_pow(fractional_mul(field_ring(L), S), S, I, n)",
		Abbrev:     Abbrev{},
	}, func(a *Argument, L field.FieldFact[on.L], S, I *Expr[Set[A]], n *Expr[Nat], h Fact) {
		p := a.Conjuncts(
			h,
			"S is a subring of L",
			"I is integral")
		ringS := a.Have(
			"S is a ring under L's operations",
			"comm_ring_on(«R»)",
			By(p[0], comm_ring.SubringRingOn.Read(field.RingOn.Read(L)).At(S)))
		a.Induct(n)
		a.Base(
			"both zeroth powers are S",
			Simp(Fwd(ring_ideal.IdealPowZero), Fwd(ring_ideal.IdealPowSuc), Fwd(comm_monoid.MonoidPowDef)),
			Basic())
		a.Step(
			"one more factor I multiplies the integral power, the same product in either sense",
			func(b *Argument, ih Fact) {
				previous := b.TermAs[Set[A]]("ideal_pow(«R», I, n)")
				bridge := b.Have(
					"multiplying the previous power, which is integral, by I is one product in either sense",
					"ideal_mul(«R», I, ideal_pow(«R», I, n)) = "+
						"fractional_mul(field_ring(L), S, I, ideal_pow(«R», I, n))",
					By(
						p[0],
						p[1],
						ring_ideal.IdealPowIdeal.Read(ringS).At(I, n),
						IntegralMulAsFractional.Read(L).At(S, I, previous)))
				b.Show(
					"the successor powers agree",
					Simp(
						Fwd(ring_ideal.IdealPowZero),
						Fwd(ring_ideal.IdealPowSuc),
						Fwd(comm_monoid.MonoidPowDef),
						Rev(ih),
						Fwd(bridge)),
					Basic())
			})
	}),
})}

// IdealExponentProductAsFractional — a finitely supported exponent product of
// integral ideals at natural exponents is the fractional exponent product at
// the same exponents read as integers: both are folds from S over one support,
// and at a natural exponent the fractional step multiplies by the natural
// power, which on an integral ideal is the integral step. Each fold recurses
// over finite index sets in its own commutative monoid, the integral ideals and
// the fractional ideals, so induction over those sets carries the agreement of
// the folds, with the integrality of the integral one, to the support.
var IdealExponentProductAsFractional = idealExponentProductAsFractionalThm{family.Add(registry.ProofEntry{
	Name: "IdealExponentProductAsFractional",
	Key:  "prop_b766e46ebe83b577",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S:set(A). ∀v:(set(A) → num).",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"finite(fun_support(0, v))",
			"∀m:set(A). v(m) ≠ 0 ⇒ ring_ideal(«R», m)",
		},
		Conclusion: "ideal_exponent_product(«R», v) = " +
			"fractional_exponent_product(field_ring(L), S, λm:set(A). int_of_num(v(m)))",
		Abbrev: Abbrev{
			{Name: "Ideals", Text: "{I:set(A) | ring_ideal(«R», I)}"},
			{Name: "Fractionals", Text: "{M:set(A) | submodule(«R», regular_module(field_ring(L)), M)}"},
			{Name: "Powers", Text: "λm:set(A). ideal_pow(«R», m, v(m))"},
			{Name: "Step", Text: "λm:set(A). λJ:set(A). ideal_mul(«R», «Powers»(m), J)"},
			{Name: "FractionalStep", Text: "λm:set(A). λJ:set(A). " +
				"    fractional_mul(field_ring(L), " +
				"        S, " +
				"        monoid_pow(fractional_mul(field_ring(L), S), " +
				"            S, " +
				"            COND(int_of_num(0) ≤ int_of_num(v(m)), m, fractional_inverse(field_ring(L), S, m)), " +
				"            num_of_int(int_abs(v(m)))), " +
				"        J)"},
			{Name: "Fold", Text: "λE:set(set(A)). set_fold(«Step», E, S)"},
			{Name: "FractionalFold", Text: "λE:set(set(A)). set_fold(«FractionalStep», E, S)"},
		},
	}, func(a *Argument, L field.FieldFact[on.L], S *Expr[Set[A]], v *Arrow[Set[A], Nat], h Fact) {
		p := a.Conjuncts(
			h,
			"S is a subring of L",
			"the support is finite",
			"supported factors are ideals")
		subringS := p[0]
		ringS := a.Have(
			"S is a ring under L's operations",
			"comm_ring_on(«R»)",
			By(subringS, comm_ring.SubringRingOn.Read(field.RingOn.Read(L)).At(S)))
		ideals := a.TermAs[Set[Set[A]]]("«Ideals»")
		fractionals := a.TermAs[Set[Set[A]]]("«Fractionals»")
		step := a.TermAs[Fun2[Set[A], Set[A], Set[A]]]("«Step»")
		fractionalStep := a.TermAs[Fun2[Set[A], Set[A], Set[A]]]("«FractionalStep»")
		support := a.TermAs[Set[Set[A]]]("fun_support(0, v)")

		monoid := ring_ideal.IdealsCommMonoid.Read(ringS)
		unit := a.Have(
			"the unit S is an integral ideal",
			"S ∈ «Ideals»",
			By(comm_monoid.IdentityIn.Read(monoid)))
		powers := a.Have(
			"every exponent factor is an integral ideal",
			"∀m:set(A). «Powers»(m) ∈ «Ideals»",
			Derive(func(b *Argument) {
				m := b.FixAs[Set[A]]("m")
				b.Cases(b.TermAs[Bool]("v(m) = 0"))
				b.When(
					"a zero exponent contributes the unit ideal",
					func(c *Argument, zero Fact) {
						c.Show(
							"the zeroth power is S",
							Simp(
								Fwd(zero),
								Fwd(ring_ideal.IdealPowZero),
								Fwd(ring_ideal.IdealPowSuc),
								Fwd(comm_monoid.MonoidPowDef)),
							By(unit))
					})
				b.Otherwise(
					"a nonzero exponent has an ideal as its base",
					func(c *Argument, nonzero Fact) {
						c.Show(
							"powers of an ideal stay ideals",
							By(nonzero, p[2].At(m), ring_ideal.IdealPowIdeal.Read(ringS).At(m, v.Apply(m))))
					})
			}))
		closed := a.Have(
			"every integral step keeps an integral ideal integral",
			"∀m J:set(A). J ∈ «Ideals» ⇒ «Step»(m, J) ∈ «Ideals»",
			By(powers, comm_monoid.OpIn.Read(monoid)))
		commutes := a.Have(
			"distinct integral steps commute on integral ideals",
			"∀m n J:set(A). m ≠ n ∧ J ∈ «Ideals» ⇒ «Step»(m, «Step»(n, J)) = «Step»(n, «Step»(m, J))",
			By(powers, comm_monoid.LeftCommOn.Read(monoid)))
		recursion := a.Have(
			"the integral fold recurses over finite index sets",
			"«Fold»(∅) = S ∧ "+
				"(∀m:set(A). ∀E:set(set(A)). "+
				"    finite(E) ⇒ «Fold»(insert(m, E)) = COND(m ∈ E, «Fold»(E), «Step»(m, «Fold»(E))))",
			By(unit, closed, commutes, cardinality.FiniteRecursionWithin.At(step, S, ideals)))
		rules := a.Conjuncts(
			recursion,
			"the empty integral fold is S",
			"a fresh index takes one integral step")

		natural := a.Have(
			"at a natural exponent the fractional step multiplies by the natural power",
			"∀m J:set(A). "+
				"    «FractionalStep»(m, J) = "+
				"    fractional_mul(field_ring(L), S, monoid_pow(fractional_mul(field_ring(L), S), S, m, v(m)), J)",
			Simp(Fwd(int_embed.EmbedNonneg), Fwd(int_embed.OfNumAbs), Fwd(int_embed.OfNumRetract)),
			Basic())
		factors := a.Have(
			"the natural fractional powers are the integral powers",
			"∀m:set(A). monoid_pow(fractional_mul(field_ring(L), S), S, m, v(m)) = «Powers»(m)",
			Derive(func(b *Argument) {
				m := b.FixAs[Set[A]]("m")
				b.Cases(b.TermAs[Bool]("v(m) = 0"))
				b.When(
					"both zeroth powers are S",
					func(c *Argument, zero Fact) {
						c.Show(
							"the zeroth powers coincide",
							Simp(
								Fwd(zero),
								Fwd(ring_ideal.IdealPowZero),
								Fwd(ring_ideal.IdealPowSuc),
								Fwd(comm_monoid.MonoidPowDef)),
							Basic())
					})
				b.Otherwise(
					"a supported base is integral, and its powers agree",
					func(c *Argument, nonzero Fact) {
						c.Show(
							"the powers of an integral ideal agree",
							By(subringS, nonzero, p[2].At(m), IntegralPowAsFractional.Read(L).At(S, m, v.Apply(m))))
					})
			}))
		agree := a.Have(
			"on integral ideals the fractional step is the integral step",
			"∀m J:set(A). J ∈ «Ideals» ⇒ «FractionalStep»(m, J) = «Step»(m, J)",
			Derive(func(b *Argument) {
				m, J := b.FixAs[Set[A]]("m"), b.FixAs[Set[A]]("J")
				integral := b.Assume()
				power := b.TermAs[Set[A]]("«Powers»(m)")
				b.Show(
					"both multiply J by the integral power, one product in either sense",
					Simp(Fwd(natural), Fwd(factors)),
					By(subringS, powers.At(m), integral, IntegralMulAsFractional.Read(L).At(S, power, J)))
			}))

		fractionalMonoid := a.Have(
			"the fractional ideals form a commutative monoid",
			"comm_monoid_on(«Fractionals», fractional_mul(field_ring(L), S), S)",
			By(subringS, fractional_ideal.FractionalIdealsCommMonoid.Read(L).At(S)))
		fractionalPowers := a.Have(
			"every exponent factor is a fractional ideal",
			"∀m:set(A). «Powers»(m) ∈ «Fractionals»",
			Derive(func(b *Argument) {
				m := b.FixAs[Set[A]]("m")
				power := b.TermAs[Set[A]]("«Powers»(m)")
				b.Show(
					"an integral ideal is fractional",
					By(subringS, powers.At(m), fractional_ideal.IntegralIdealFractional.Read(L).At(S, power)))
			}))
		fractionalClosed := a.Have(
			"every fractional step keeps a fractional ideal fractional",
			"∀m J:set(A). J ∈ «Fractionals» ⇒ «FractionalStep»(m, J) ∈ «Fractionals»",
			Derive(func(b *Argument) {
				m, J := b.FixAs[Set[A]]("m"), b.FixAs[Set[A]]("J")
				fractional := b.Assume()
				power := b.TermAs[Set[A]]("«Powers»(m)")
				b.Show(
					"the product of two fractional ideals is fractional",
					Simp(Fwd(natural), Fwd(factors)),
					By(
						fractionalPowers.At(m),
						fractional,
						comm_monoid.OpIn.Read(fractionalMonoid).AsFact().At(power, J)))
			}))
		fractionalCommutes := a.Have(
			"distinct fractional steps commute on fractional ideals",
			Statement{
				Binders: "∀m n J:set(A).",
				Hypotheses: []string{
					"m ≠ n",
					"J ∈ «Fractionals»",
				},
				Conclusion: "«FractionalStep»(m, «FractionalStep»(n, J)) = " +
					"«FractionalStep»(n, «FractionalStep»(m, J))",
			},
			Derive(func(b *Argument) {
				m, n, J := b.FixAs[Set[A]]("m"), b.FixAs[Set[A]]("n"), b.FixAs[Set[A]]("J")
				guard := b.Assume()
				left, right := b.TermAs[Set[A]]("«Powers»(m)"), b.TermAs[Set[A]]("«Powers»(n)")
				b.Show(
					"left commutativity exchanges the two fractional factors",
					Simp(Fwd(natural), Fwd(factors)),
					By(
						fractionalPowers.At(m),
						fractionalPowers.At(n),
						guard,
						comm_monoid.LeftCommOn.Read(fractionalMonoid).AsFact().At(left, right, J)))
			}))
		fractionalRecursion := a.Have(
			"the fractional fold recurses over finite index sets",
			"«FractionalFold»(∅) = S ∧ "+
				"(∀m:set(A). ∀E:set(set(A)). "+
				"    finite(E) ⇒ "+
				"    «FractionalFold»(insert(m, E)) = "+
				"    COND(m ∈ E, «FractionalFold»(E), «FractionalStep»(m, «FractionalFold»(E))))",
			By(
				comm_monoid.IdentityIn.Read(fractionalMonoid),
				fractionalClosed,
				fractionalCommutes,
				cardinality.FiniteRecursionWithin.At(fractionalStep, S, fractionals)))
		fractionalRules := a.Conjuncts(
			fractionalRecursion,
			"the empty fractional fold is S",
			"a fresh index takes one fractional step")

		folds := a.Have(
			"over every finite index set the two folds agree and the integral one is integral",
			"∀E:set(set(A)). finite(E) ⇒ «Fold»(E) = «FractionalFold»(E) ∧ «Fold»(E) ∈ «Ideals»",
			ByInduction(finite_set.FiniteInductFresh,
				Case(
					"both empty folds are the integral unit S",
					By(Normalized, rules[0], fractionalRules[0], unit)),
				Case(
					"a fresh index takes agreeing steps on the integral fold",
					Derive(func(b *Argument) {
						m := b.FixAs[Set[A]]("m")
						E := b.FixAs[Set[Set[A]]]("E")
						ih := b.Conjuncts(
							b.Assume(),
							"the folds over E agree",
							"the fold over E is integral",
							"m is fresh",
							"E is finite")
						previous := b.TermAs[Set[A]]("«Fold»(E)")
						inserted := b.Have(
							"the integral fold takes one step at m",
							"«Fold»(insert(m, E)) = «Step»(m, «Fold»(E))",
							By(ih[2], ih[3], rules[1].At(m, E)))
						fractionalInserted := b.Have(
							"the fractional fold takes one step at m",
							"«FractionalFold»(insert(m, E)) = «FractionalStep»(m, «FractionalFold»(E))",
							By(ih[2], ih[3], fractionalRules[1].At(m, E)))
						b.Show(
							"on the integral fold over E the two steps agree and stay integral",
							By(inserted, fractionalInserted, ih[0], ih[1], agree.At(m, previous), closed.At(m, previous)))
					}))))
		supports := a.Have(
			"the integer exponents have the same support",
			"fun_support(int_of_num(0), λm:set(A). int_of_num(v(m))) = fun_support(0, v)",
			BySets(int_embed.OfNumEq))
		a.Show(
			"both exponent products are the folds over the finite support",
			Simp(Fwd(IdealExponentProductDef), Fwd(fractionalExponentProductDef), Fwd(supports)),
			By(p[1], folds.At(support)))
	}),
})}

// IdealExponentProductIntegral — a finite exponent product of ideals of a
// commutative ring is an ideal: every power and every finite fold stay in the
// monoid of ideals.
var IdealExponentProductIntegral = idealExponentProductIntegralThm{family.Add(registry.ProofEntry{
	Name: "IdealExponentProductIntegral",
	Key:  "prop_1096fa2610e405eb",
	Build: family.Theorem(Statement{
		Binders: "∀R:comm_ring_on(A). ∀v:(set(A) → num).",
		Hypotheses: []string{
			"finite(fun_support(0, v))",
			"∀m:set(A). v(m) ≠ 0 ⇒ ring_ideal(R, m)",
		},
		Conclusion: "ring_ideal(R, ideal_exponent_product(R, v))",
		Abbrev: Abbrev{
			{Name: "Ideals", Text: "{I:set(A) | ring_ideal(R, I)}"},
			{Name: "Powers", Text: "λm:set(A). ideal_pow(R, m, v(m))"},
			{Name: "Step", Text: "λm:set(A). λJ:set(A). ideal_mul(R, «Powers»(m), J)"},
			{Name: "Fold", Text: "λE:set(set(A)). set_fold(«Step», E, R.carrier)"},
		},
	}, func(a *Argument, R comm_ring.CommRingFact[on.R], v *Arrow[Set[A], Nat], h Fact) {
		p := a.Conjuncts(
			h,
			"the exponent support is finite",
			"each supported factor is an ideal")
		ideals := a.TermAs[Set[Set[A]]]("«Ideals»")
		step := a.TermAs[Fun2[Set[A], Set[A], Set[A]]]("«Step»")
		support := a.TermAs[Set[Set[A]]]("fun_support(0, v)")
		carrier := a.TermAs[Set[A]]("R.carrier")
		monoid := ring_ideal.IdealsCommMonoid.Read(R)
		unit := a.Have(
			"the unit belongs to the ideal carrier",
			"R.carrier ∈ «Ideals»",
			By(comm_monoid.IdentityIn.Read(monoid)))
		powers := a.Have(
			"every exponent factor belongs to the ideal carrier",
			"∀m:set(A). «Powers»(m) ∈ «Ideals»",
			Derive(func(b *Argument) {
				m := b.FixAs[Set[A]]("m")
				b.Cases(b.TermAs[Bool]("v(m) = 0"))
				b.When(
					"a zero exponent contributes the unit ideal",
					func(c *Argument, zero Fact) {
						c.Show(
							"the zeroth power is the carrier",
							Simp(Fwd(zero), Fwd(ring_ideal.IdealPowZero), Fwd(ring_ideal.IdealPowSuc)),
							By(unit))
					})
				b.Otherwise(
					"a nonzero exponent has an ideal as its base",
					func(c *Argument, nonzero Fact) {
						inCarrier := c.Have(
							"the supported base lies in the ideal carrier",
							"m ∈ «Ideals»",
							BySets(nonzero, p[1].At(m)))
						c.Show(
							"powers of an ideal stay ideals",
							By(inCarrier, ring_ideal.IdealPowIdeal.Read(R).At(m, v.Apply(m))))
					})
			}))
		closed := a.Have(
			"every fold step stays in the ideal carrier",
			"∀m J:set(A). J ∈ «Ideals» ⇒ «Step»(m, J) ∈ «Ideals»",
			By(powers, comm_monoid.OpIn.Read(monoid)))
		commutes := a.Have(
			"distinct fold steps commute on the ideal carrier",
			"∀m n J:set(A). m ≠ n ∧ J ∈ «Ideals» ⇒ «Step»(m, «Step»(n, J)) = «Step»(n, «Step»(m, J))",
			By(powers, comm_monoid.LeftCommOn.Read(monoid)))
		recursion := a.Have(
			"the fold has empty and insertion recursion on finite sets",
			"«Fold»(∅) = R.carrier ∧ "+
				"(∀m:set(A). ∀E:set(set(A)). "+
				"    finite(E) ⇒ «Fold»(insert(m, E)) = COND(m ∈ E, «Fold»(E), «Step»(m, «Fold»(E))))",
			By(unit, closed, commutes, cardinality.FiniteRecursionWithin.At(step, carrier, ideals)))
		rules := a.Conjuncts(
			recursion,
			"the empty fold is the carrier",
			"inserting an index takes the corresponding step")
		folds := a.Have(
			"every finite index fold is an ideal",
			"∀E:set(set(A)). finite(E) ⇒ «Fold»(E) ∈ «Ideals»",
			ByInduction(finite_set.FiniteInductFresh,
				Case(
					"the empty fold is the unit ideal",
					Simp(Fwd(rules[0])),
					By(unit)),
				Case(
					"adjoining a fresh index keeps the fold an ideal",
					Derive(func(b *Argument) {
						m := b.FixAs[Set[A]]("m")
						E := b.FixAs[Set[Set[A]]]("E")
						ih := b.Assume()
						previous := b.TermAs[Set[A]]("«Fold»(E)")
						inserted := b.Have(
							"a fresh insertion applies one fold step",
							"«Fold»(insert(m, E)) = «Step»(m, «Fold»(E))",
							By(ih, rules[1].At(m, E)))
						b.Show(
							"the step keeps the previous fold an ideal",
							Simp(Fwd(inserted)),
							By(ih, closed.At(m, previous)))
					}))))
		a.Show(
			"the finite support makes the exponent product an ideal",
			Simp(Fwd(IdealExponentProductDef)),
			BySets(p[0], folds.At(support)))
	}),
})}

// IdealExponentProductZero — the zero exponent vector has empty support,
// and its exponent product is the carrier for arbitrary ring operations.
var IdealExponentProductZero = idealExponentProductZeroThm{family.Add(registry.ProofEntry{
	Name: "IdealExponentProductZero",
	Key:  "prop_c6c11170b4d4f0b1",
	Build: family.Theorem(Statement{
		Binders:    "∀R:ring_ops(A).",
		Conclusion: "ideal_exponent_product(R, λm:set(A). 0) = R.carrier",
		Abbrev: Abbrev{
			{Name: "Step", Text: "λm:set(A). λJ:set(A). ideal_mul(R, R.carrier, J)"},
		},
	}, func(a *Argument, R *Expr[RingOps[A]]) {
		step := a.TermAs[Fun2[Set[A], Set[A], Set[A]]]("«Step»")
		carrier := a.TermAs[Set[A]]("R.carrier")
		support := a.Have(
			"the zero exponent vector has empty support",
			"fun_support(0, λm:set(A). 0) = ∅",
			BySets())
		commutes := a.Have(
			"the index-independent steps commute on every accumulator",
			"∀m n J:set(A). m ≠ n ⇒ «Step»(m, «Step»(n, J)) = «Step»(n, «Step»(m, J))",
			Basic())
		empty := a.Have(
			"the empty fold is the carrier",
			"set_fold(«Step», ∅, R.carrier) = R.carrier",
			By(commutes, cardinality.FiniteRecursion.At(step, carrier)))
		a.Show(
			"the zero product is its empty fold",
			Simp(
				Fwd(IdealExponentProductDef),
				Fwd(ring_ideal.IdealPowZero),
				Fwd(ring_ideal.IdealPowSuc),
				Fwd(support),
				Fwd(empty)),
			Basic())
	}),
})}

// IdealExponentProductSplit — one full power splits from a finite exponent
// product of ideals of a commutative ring, leaving the exponent at that ideal
// equal to zero: a zero exponent's power is the unit, and at a nonzero one the
// support is m adjoined to the rest's support, the fold takes the m step first,
// and on the rest's support the two step functions agree.
var IdealExponentProductSplit = idealExponentProductSplitThm{family.Add(registry.ProofEntry{
	Name: "IdealExponentProductSplit",
	Key:  "prop_4c96ac7e947c299d",
	Build: family.Theorem(Statement{
		Binders: "∀R:comm_ring_on(A). ∀v:(set(A) → num). ∀m:set(A).",
		Hypotheses: []string{
			"finite(fun_support(0, v))",
			"∀p:set(A). v(p) ≠ 0 ⇒ ring_ideal(R, p)",
		},
		Conclusion: "ideal_exponent_product(R, v) = " +
			"ideal_mul(R, ideal_pow(R, m, v(m)), ideal_exponent_product(R, «Delete»(v, m)))",
		Abbrev: Abbrev{
			{Name: "Ideals", Text: "{I:set(A) | ring_ideal(R, I)}"},
			{Name: "Powers", Text: "λp:set(A). ideal_pow(R, p, v(p))"},
			{Name: "Step", Text: "λp:set(A). λJ:set(A). ideal_mul(R, «Powers»(p), J)"},
			{Name: "RestStep", Text: "λp:set(A). λJ:set(A). " +
				"    ideal_mul(R, ideal_pow(R, p, «Delete»(v, m, p)), J)"},
		},
	}, func(
		a *Argument,
		R comm_ring.CommRingFact[on.R],
		v *Arrow[Set[A], Nat],
		m *Expr[Set[A]],
		h Fact,
	) {
		p := a.Conjuncts(
			h,
			"the support is finite",
			"supported factors are ideals")
		ideals := a.TermAs[Set[Set[A]]]("«Ideals»")
		step := a.TermAs[Fun2[Set[A], Set[A], Set[A]]]("«Step»")
		restStep := a.TermAs[Fun2[Set[A], Set[A], Set[A]]]("«RestStep»")
		restSupport := a.TermAs[Set[Set[A]]]("«RestSupport»")
		support := a.TermAs[Set[Set[A]]]("fun_support(0, v)")
		carrier := a.TermAs[Set[A]]("R.carrier")
		monoid := ring_ideal.IdealsCommMonoid.Read(R)
		unit := a.Have(
			"the unit belongs to the ideal carrier",
			"R.carrier ∈ «Ideals»",
			By(comm_monoid.IdentityIn.Read(monoid)))
		a.Cases(a.TermAs[Bool]("v(m) = 0"))
		a.When(
			"a zero exponent contributes only the unit",
			func(b *Argument, zero Fact) {
				unchanged := b.Have(
					"deleting a zero exponent leaves the exponent function",
					"«Delete»(v, m) = v",
					By(zero))
				integral := b.Have(
					"the exponent product belongs to the ideal carrier",
					"ideal_exponent_product(R, v) ∈ «Ideals»",
					BySets(h, IdealExponentProductIntegral.Read(R).At(v)))
				product := b.TermAs[Set[A]]("ideal_exponent_product(R, v)")
				b.Show(
					"the zeroth power acts as the unit on this product, an ideal",
					Simp(Fwd(unchanged), Fwd(zero), Fwd(ring_ideal.IdealPowZero), Fwd(ring_ideal.IdealPowSuc)),
					By(Normalized, integral, comm_monoid.LeftIdentityOn.Read(monoid).AsFact().At(product)))
			})
		a.Otherwise(
			"a nonzero exponent splits from its support",
			func(b *Argument, nonzero Fact) {
				supportSplit := b.Have(
					"the support is the deleted support with m adjoined",
					"fun_support(0, v) = insert(m, «RestSupport»)",
					BySets(nonzero))
				deletion := b.Have(
					"the deleted support omits m and lies in the original support",
					"m ∉ «RestSupport» ∧ «RestSupport» ⊆ fun_support(0, v)",
					BySets())
				finiteRest := b.Have(
					"the deleted support is finite",
					"finite(«RestSupport»)",
					By(p[0], deletion, finite_set.FiniteSubset.At(restSupport, support)))
				powers := b.Have(
					"every original exponent factor lies in the ideal carrier",
					"∀q:set(A). «Powers»(q) ∈ «Ideals»",
					Derive(func(c *Argument) {
						q := c.FixAs[Set[A]]("q")
						c.Cases(c.TermAs[Bool]("v(q) = 0"))
						c.When(
							"zero powers are the unit ideal",
							func(d *Argument, zero Fact) {
								d.Show(
									"the zeroth power is the carrier",
									Simp(Fwd(zero), Fwd(ring_ideal.IdealPowZero), Fwd(ring_ideal.IdealPowSuc)),
									By(unit))
							})
						c.Otherwise(
							"supported powers have an ideal as base",
							func(d *Argument, nonzero Fact) {
								base := d.Have(
									"the base lies in the ideal carrier",
									"q ∈ «Ideals»",
									BySets(nonzero, p[1].At(q)))
								d.Show(
									"the ideal monoid contains this power",
									By(base, ring_ideal.IdealPowIdeal.Read(R).At(q, v.Apply(q))))
							})
					}))
				restPowers := b.Have(
					"every residual exponent factor lies in the ideal carrier",
					"∀q:set(A). ideal_pow(R, q, «Delete»(v, m, q)) ∈ «Ideals»",
					Derive(func(c *Argument) {
						q := c.FixAs[Set[A]]("q")
						c.Cases(c.TermAs[Bool]("q = m"))
						c.When(
							"the deleted factor is the unit ideal",
							func(d *Argument, equal Fact) {
								d.Show(
									"the deleted exponent is zero",
									Simp(Fwd(equal), Fwd(ring_ideal.IdealPowZero), Fwd(ring_ideal.IdealPowSuc)),
									By(unit))
							})
						c.Otherwise(
							"other factors keep their exponent",
							func(d *Argument, unequal Fact) {
								d.Show(
									"the unchanged power is an ideal",
									Simp(Fwd(unequal)),
									By(powers.At(q)))
							})
					}))
				closed := b.Have(
					"original steps preserve the ideal carrier",
					"∀q J:set(A). J ∈ «Ideals» ⇒ «Step»(q, J) ∈ «Ideals»",
					By(powers, comm_monoid.OpIn.Read(monoid)))
				commutes := b.Have(
					"original steps commute on the ideal carrier",
					"∀q r J:set(A). q ≠ r ∧ J ∈ «Ideals» ⇒ «Step»(q, «Step»(r, J)) = «Step»(r, «Step»(q, J))",
					By(powers, comm_monoid.LeftCommOn.Read(monoid)))
				restClosed := b.Have(
					"residual steps preserve the ideal carrier",
					"∀q J:set(A). J ∈ «Ideals» ⇒ «RestStep»(q, J) ∈ «Ideals»",
					By(restPowers, comm_monoid.OpIn.Read(monoid)))
				restCommutes := b.Have(
					"residual steps commute on the ideal carrier",
					Statement{
						Binders: "∀q r J:set(A).",
						Hypotheses: []string{
							"q ≠ r",
							"J ∈ «Ideals»",
						},
						Conclusion: "«RestStep»(q, «RestStep»(r, J)) = «RestStep»(r, «RestStep»(q, J))",
					},
					By(restPowers, comm_monoid.LeftCommOn.Read(monoid)))
				recursion := b.Have(
					"original folds satisfy finite insertion recursion",
					"set_fold(«Step», ∅, R.carrier) = R.carrier ∧ "+
						"(∀q:set(A). ∀T:set(set(A)). "+
						"    finite(T) ⇒ "+
						"    set_fold(«Step», insert(q, T), R.carrier) = "+
						"    COND(q ∈ T, set_fold(«Step», T, R.carrier), «Step»(q, set_fold(«Step», T, R.carrier))))",
					By(unit, closed, commutes, cardinality.FiniteRecursionWithin.At(step, carrier, ideals)))
				rules := b.Conjuncts(
					recursion,
					"the empty fold is the carrier",
					"a finite insertion takes one step")
				inserted := b.Have(
					"adjoining m extracts its full power",
					"set_fold(«Step», insert(m, «RestSupport»), R.carrier) = "+
						"«Step»(m, set_fold(«Step», «RestSupport», R.carrier))",
					By(finiteRest, deletion, rules[1].At(m, restSupport)))
				agree := b.Have(
					"the step functions agree on every remaining index",
					"∀q:set(A). q ∈ «RestSupport» ⇒ «Step»(q) = «RestStep»(q)",
					Derive(func(c *Argument) {
						c.FixAs[Set[A]]("q")
						inRest := c.Assume()
						away := c.Have(
							"a remaining index differs from m",
							"q ≠ m",
							BySets(inRest))
						c.Show(
							"both step functions have the same exponent",
							Simp(Fwd(away)),
							Basic())
					}))
				residual := b.Have(
					"the residual folds agree",
					"set_fold(«Step», «RestSupport», R.carrier) = set_fold(«RestStep», «RestSupport», R.carrier)",
					By(
						finiteRest,
						unit,
						agree,
						closed,
						commutes,
						restClosed,
						restCommutes,
						cardinality.FoldOfAgreeingStepsWithin.At(restSupport, step, restStep, carrier, ideals)))
				b.Show(
					"finite insertion extracts the power and leaves the residual exponent product",
					Simp(Fwd(IdealExponentProductDef), Fwd(supportSplit), Fwd(inserted), Fwd(residual)),
					TrivialNormalized())
			})
	}),
})}

// IdealExponentProductInFactor — a finite exponent product of ideals of a
// commutative ring lies in each ideal it raises to a positive power: the full
// power splits from the product, the product of two ideals lies in each of
// them, and a positive power of m is m times a power of m.
var IdealExponentProductInFactor = idealExponentProductInFactorThm{family.Add(registry.ProofEntry{
	Name: "IdealExponentProductInFactor",
	Key:  "prop_13ba6ebfe73a81b",
	Build: family.Theorem(Statement{
		Binders: "∀R:comm_ring_on(A). ∀v:(set(A) → num). ∀m:set(A).",
		Hypotheses: []string{
			"finite(fun_support(0, v))",
			"∀p:set(A). v(p) ≠ 0 ⇒ ring_ideal(R, p)",
			"v(m) ≠ 0",
		},
		Conclusion: "ideal_exponent_product(R, v) ⊆ m",
	}, func(
		a *Argument,
		R comm_ring.CommRingFact[on.R],
		v *Arrow[Set[A], Nat],
		m *Expr[Set[A]],
		h Fact,
	) {
		p := a.Conjuncts(
			h,
			"the support is finite",
			"supported factors are ideals",
			"m has a positive exponent")
		support := a.TermAs[Set[Set[A]]]("fun_support(0, v)")
		restSupport := a.TermAs[Set[Set[A]]]("«RestSupport»")
		rest := a.TermAs[Fun[Set[A], Nat]]("«Delete»(v, m)")
		power := a.TermAs[Set[A]]("ideal_pow(R, m, v(m))")
		restProduct := a.TermAs[Set[A]]("ideal_exponent_product(R, «Delete»(v, m))")
		exponent := v.Apply(m)
		split := a.Have(
			"the full power of m splits from the product",
			"ideal_exponent_product(R, v) = "+
				"ideal_mul(R, ideal_pow(R, m, v(m)), ideal_exponent_product(R, «Delete»(v, m)))",
			By(p[0], p[1], IdealExponentProductSplit.Read(R).At(v, m)))
		restInside := a.Have(
			"erasing m keeps the support inside v's",
			"«RestSupport» ⊆ fun_support(0, v)",
			BySets())
		restIntegral := a.Have(
			"the product of the rest is an ideal",
			"ring_ideal(R, ideal_exponent_product(R, «Delete»(v, m)))",
			By(
				p[0],
				restInside,
				p[1],
				finite_set.FiniteSubset.At(restSupport, support),
				IdealExponentProductIntegral.Read(R).At(rest)))
		k, successor := a.ObtainAs[Nat](
			"the positive exponent of m is a successor",
			"∃k:num. v(m) = suc(k)",
			By(Normalized, p[2], peano.Cases.At(exponent)))
		lowerPower := a.TermAs[Set[A]]("ideal_pow(R, m, k)")
		powerInside := a.Have(
			"a positive power of m is m times a power of m, so lies in m",
			"ideal_pow(R, m, v(m)) ⊆ m",
			BySets(
				successor,
				p[2],
				p[1].At(m),
				ring_ideal.IdealPowSuc,
				ring_ideal.IdealPowIdeal.Read(R).At(m, k),
				ring_ideal.IdealMulSubsetInter.Read(R).At(m, lowerPower)))
		a.Show(
			"the product of the power and the rest lies in the power, which lies in m",
			split.Rw(),
			BySets(
				powerInside,
				restIntegral,
				p[2],
				p[1].At(m),
				ring_ideal.IdealPowIdeal.Read(R).At(m, exponent),
				ring_ideal.IdealMulSubsetInter.Read(R).At(power, restProduct)))
	}),
})}

// IdealExponentProductIncrement — raising one exponent by one multiplies a
// finite exponent product of ideals of a commutative ring by that ideal: split
// its full power, then reassociate.
var IdealExponentProductIncrement = idealExponentProductIncrementThm{family.Add(registry.ProofEntry{
	Name: "IdealExponentProductIncrement",
	Key:  "prop_4429f593cc81b543",
	Build: family.Theorem(Statement{
		Binders: "∀R:comm_ring_on(A). ∀m:set(A). ∀v:(set(A) → num).",
		Hypotheses: []string{
			"ring_ideal(R, m)",
			"finite(fun_support(0, v))",
			"∀p:set(A). v(p) ≠ 0 ⇒ ring_ideal(R, p)",
		},
		Conclusion: "ideal_exponent_product(R, «inc») = ideal_mul(R, m, ideal_exponent_product(R, v))",
		Abbrev: Abbrev{
			{Name: "Ideals", Text: "{I:set(A) | ring_ideal(R, I)}"},
			{Name: "inc", Text: "λp:set(A). COND(p = m, v(m) + 1, v(p))"},
			{Name: "IncSupport", Text: "fun_support(0, λp:set(A). «inc»(p))"},
			{Name: "Power", Text: "ideal_pow(R, m, v(m))"},
			{Name: "RestProduct", Text: "ideal_exponent_product(R, «Delete»(v, m))"},
		},
	}, func(
		a *Argument,
		R comm_ring.CommRingFact[on.R],
		m *Expr[Set[A]],
		v *Arrow[Set[A], Nat],
		h Fact,
	) {
		p := a.Conjuncts(
			h,
			"m is an ideal",
			"the support is finite",
			"supported factors are ideals")
		support := a.TermAs[Set[Set[A]]]("fun_support(0, v)")
		restSupport := a.TermAs[Set[Set[A]]]("«RestSupport»")
		inc := a.TermAs[Fun[Set[A], Nat]]("«inc»")
		deleted := a.TermAs[Fun[Set[A], Nat]]("«Delete»(v, m)")
		power := a.TermAs[Set[A]]("«Power»")
		restProduct := a.TermAs[Set[A]]("«RestProduct»")

		positive := a.Have(
			"the increased exponent is nonzero",
			"v(m) + 1 ≠ 0",
			ByArith())
		supportIncrement := a.Have(
			"the increased support adjoins m",
			"«IncSupport» = insert(m, fun_support(0, v))",
			BySets(positive))
		finiteInc := a.Have(
			"the increased support is finite",
			"finite(«IncSupport»)",
			Simp(Fwd(supportIncrement)),
			By(p[1], finite_set.FiniteInsert.At(m, support)))
		incIdeals := a.Have(
			"every increased supported factor is an ideal",
			"∀p:set(A). «inc»(p) ≠ 0 ⇒ ring_ideal(R, p)",
			By(p[0], p[2]))
		sameRest := a.Have(
			"deleting m leaves the same residual vector",
			"(λp:set(A). COND(p = m, 0, «inc»(p))) = «Delete»(v, m)",
			Basic())
		monoid := ring_ideal.IdealsCommMonoid.Read(R)
		baseIn := a.Have(
			"m belongs to the ideal carrier",
			"m ∈ «Ideals»",
			BySets(p[0]))
		powerIn := a.Have(
			"the extracted power belongs to the ideal carrier",
			"«Power» ∈ «Ideals»",
			By(baseIn, ring_ideal.IdealPowIdeal.Read(R).At(m, v.Apply(m))))
		restSubset := a.Have(
			"deletion only removes support",
			"«RestSupport» ⊆ fun_support(0, v)",
			BySets())
		finiteRest := a.Have(
			"the residual support is finite",
			"finite(«RestSupport»)",
			By(p[1], restSubset, finite_set.FiniteSubset.At(restSupport, support)))
		restIdeals := a.Have(
			"every residual supported factor is an ideal",
			"∀p:set(A). «Delete»(v, m, p) ≠ 0 ⇒ ring_ideal(R, p)",
			By(p[2]))
		restIn := a.Have(
			"the residual product belongs to the ideal carrier",
			"«RestProduct» ∈ «Ideals»",
			BySets(finiteRest, restIdeals, IdealExponentProductIntegral.Read(R).At(deleted)))

		originalSplit := a.Have(
			"split the original power from its product",
			"ideal_exponent_product(R, v) = ideal_mul(R, «Power», «RestProduct»)",
			By(p[1], p[2], IdealExponentProductSplit.Read(R).At(v, m)))
		incSplit := a.Have(
			"split the full m power from the increased product",
			"ideal_exponent_product(R, «inc») = "+
				"ideal_mul(R, ideal_pow(R, m, «inc»(m)), ideal_exponent_product(R, «Delete»(«inc», m)))",
			By(finiteInc, incIdeals, IdealExponentProductSplit.Read(R).At(inc, m)))
		increasedSplit := a.Have(
			"split the increased power with the same residual product",
			"ideal_exponent_product(R, «inc») = ideal_mul(R, ideal_pow(R, m, v(m) + 1), «RestProduct»)",
			Simp(Rev(sameRest)),
			By(Normalized, incSplit))
		successor := a.Have(
			"adding one gives the successor exponent",
			"v(m) + 1 = suc(v(m))",
			ByArith())
		nextPower := a.Have(
			"the increased power extracts one extra factor",
			"ideal_pow(R, m, v(m) + 1) = ideal_mul(R, m, «Power»)",
			Simp(Fwd(successor), Fwd(ring_ideal.IdealPowZero), Fwd(ring_ideal.IdealPowSuc)),
			Basic())
		regroup := a.Have(
			"associativity moves m outside the residual product",
			"ideal_mul(R, ideal_mul(R, m, «Power»), «RestProduct») = "+
				"ideal_mul(R, m, ideal_mul(R, «Power», «RestProduct»))",
			By(baseIn, powerIn, restIn, comm_monoid.AssocOn.Read(monoid).AsFact().At(m, power, restProduct)))
		a.Show(
			"the increased product is m times the original product",
			CalcEq(
				Leg(
					a.TermAs[Set[A]]("ideal_mul(R, ideal_pow(R, m, v(m) + 1), «RestProduct»)"),
					"extract the increased power",
					By(increasedSplit)),
				Leg(
					a.TermAs[Set[A]]("ideal_mul(R, ideal_mul(R, m, «Power»), «RestProduct»)"),
					"expand the successor power",
					Simp(Fwd(nextPower)),
					Basic()),
				Leg(
					a.TermAs[Set[A]]("ideal_mul(R, m, ideal_mul(R, «Power», «RestProduct»))"),
					"reassociate the three ideals",
					By(regroup)),
				FinalLeg(
					"restore the original exponent product",
					Simp(Fwd(originalSplit)),
					Basic())))
	}),
})}

// IdealExponentProductAdd — adding finitely supported natural exponent vectors
// multiplies their products of ideals of a commutative ring. Induct on the
// support of v, the second vector held arbitrary: the zero vector adds
// nothing, and its product is the unit; at a nonzero coordinate m the m power
// splits from both vectors and from their sum, the two powers combine in the
// ideal monoid, and the rests are the induction at v's rest against the second
// vector's rest.
var IdealExponentProductAdd = idealExponentProductAddThm{family.Add(registry.ProofEntry{
	Name: "IdealExponentProductAdd",
	Key:  "prop_49e3a402fb170eb9",
	Build: family.Theorem(Statement{
		Binders: "∀R:comm_ring_on(A). ∀v w:(set(A) → num).",
		Hypotheses: []string{
			"finite(fun_support(0, v))",
			"finite(fun_support(0, w))",
			"∀m:set(A). v(m) ≠ 0 ∨ w(m) ≠ 0 ⇒ ring_ideal(R, m)",
		},
		Conclusion: "ideal_exponent_product(R, λm:set(A). v(m) + w(m)) = " +
			"ideal_mul(R, ideal_exponent_product(R, v), ideal_exponent_product(R, w))",
		Abbrev: Abbrev{
			{Name: "Ideals", Text: "{I:set(A) | ring_ideal(R, I)}"},
			{Name: "Product", Text: "λI:set(A). λJ:set(A). ideal_mul(R, I, J)"},
			{Name: "ExponentProduct", Text: "λu:(set(A) → num). ideal_exponent_product(R, u)"},
			{Name: "Sum", Text: "λu:(set(A) → num). λz:(set(A) → num). λp:set(A). u(p) + z(p)"},
			{Name: "SupportOf", Text: "λu:(set(A) → num). fun_support(0, u)"},
			{Name: "Law", Text: "λu:(set(A) → num). λz:(set(A) → num). " +
				"    «ExponentProduct»(«Sum»(u, z)) = «Product»(«ExponentProduct»(u), «ExponentProduct»(z))"},
			{Name: "Motive", Text: "λu:(set(A) → num). ∀z:(set(A) → num). " +
				"    finite(fun_support(0, z)) ∧ (∀q:set(A). u(q) ≠ 0 ∨ z(q) ≠ 0 ⇒ ring_ideal(R, q)) ⇒ " +
				"    «Law»(u, z)"},
		},
	}, func(a *Argument, R comm_ring.CommRingFact[on.R], v, w *Arrow[Set[A], Nat], h Fact) {
		p := a.Conjuncts(
			h,
			"v has finite support",
			"w has finite support",
			"every factor of v or w is an ideal")
		monoid := ring_ideal.IdealsCommMonoid.Read(R)
		sumSupport := a.Have(
			"the sum is supported in the union of the two supports",
			"∀u z:(set(A) → num). «SupportOf»(«Sum»(u, z)) ⊆ «SupportOf»(u) ∪ «SupportOf»(z)",
			BySets(nat_arith.AddEqZero))
		rearrange := a.Have(
			"four ideals can be regrouped by pairs",
			Statement{
				Binders: "∀M N P Q:set(A).",
				Hypotheses: []string{
					"M ∈ «Ideals»",
					"N ∈ «Ideals»",
					"P ∈ «Ideals»",
					"Q ∈ «Ideals»",
				},
				Conclusion: "«Product»(«Product»(M, N), «Product»(P, Q)) = " +
					"«Product»(«Product»(M, P), «Product»(N, Q))",
			},
			Derive(func(b *Argument) {
				M, N, P, Q := b.FixAs[Set[A]]("M"), b.FixAs[Set[A]]("N"), b.FixAs[Set[A]]("P"), b.FixAs[Set[A]]("Q")
				factors := b.Assume()
				pq := b.TermAs[Set[A]]("«Product»(P, Q)")
				nq := b.TermAs[Set[A]]("«Product»(N, Q)")
				b.Show(
					"associate, exchange the middle factors, and associate back",
					CalcEq(
						Leg(
							b.TermAs[Set[A]]("«Product»(M, «Product»(N, «Product»(P, Q)))"),
							"expose the two middle factors",
							By(
								factors,
								comm_monoid.OpIn.Read(monoid).AsFact().At(P, Q),
								comm_monoid.AssocOn.Read(monoid).AsFact().At(M, N, pq))),
						Leg(
							b.TermAs[Set[A]]("«Product»(M, «Product»(P, «Product»(N, Q)))"),
							"exchange N and P",
							By(Normalized, factors, comm_monoid.LeftCommOn.Read(monoid).AsFact().At(N, P, Q))),
						FinalLeg(
							"regroup the two pairs",
							By(
								factors,
								comm_monoid.OpIn.Read(monoid).AsFact().At(N, Q),
								comm_monoid.AssocOn.Read(monoid).AsFact().At(M, P, nq)))))
			}))
		added := a.Have(
			"for every vector of finite support, addition holds against every admissible second vector",
			"∀u:(set(A) → num). finite(fun_support(0, u)) ⇒ «Motive»(u)",
			ByInduction(finite_set.FiniteInductSupport,
				Case(
					"the zero vector adds nothing, and its product is the unit",
					Derive(func(b *Argument) {
						z := b.FixAs[Fun[Set[A], Nat]]("z")
						given := b.Conjuncts(
							b.Assume(),
							"z has finite support",
							"every factor of z is an ideal")
						zFactors := b.Have(
							"z's supported factors are ideals",
							"∀q:set(A). z(q) ≠ 0 ⇒ ring_ideal(R, q)",
							BySets(given[1]))
						zIn := b.Have(
							"z's product is an ideal",
							"«ExponentProduct»(z) ∈ «Ideals»",
							BySets(given[0], zFactors, IdealExponentProductIntegral.Read(R).At(z)))
						zProduct := b.TermAs[Set[A]]("«ExponentProduct»(z)")
						b.Show(
							"the zero product is the carrier, the unit of the ideal monoid",
							Simp(Fwd(nat_arith.AddLeftZeroClause), Fwd(IdealExponentProductZero)),
							By(Normalized, zIn, comm_monoid.LeftIdentityOn.Read(monoid).AsFact().At(zProduct)))
					})),
				Case(
					"a nonzero coordinate m of u splits from u, from z and from their sum",
					Derive(func(b *Argument) {
						u := b.FixAs[Fun[Set[A], Nat]]("u")
						m := b.FixAs[Set[A]]("m")
						previous := b.Conjuncts(
							b.Assume(),
							"addition holds for the rest of u against every admissible vector",
							"u has an m factor",
							"u has finite support")
						z := b.FixAs[Fun[Set[A], Nat]]("z")
						given := b.Conjuncts(
							b.Assume(),
							"z has finite support",
							"every factor of u or z is an ideal")
						sum := b.TermAs[Fun[Set[A], Nat]]("«Sum»(u, z)")
						uDelete := b.TermAs[Fun[Set[A], Nat]]("«Delete»(u, m)")
						zDelete := b.TermAs[Fun[Set[A], Nat]]("«Delete»(z, m)")
						uPower := b.TermAs[Set[A]]("ideal_pow(R, m, u(m))")
						zPower := b.TermAs[Set[A]]("ideal_pow(R, m, z(m))")
						uResidual := b.TermAs[Set[A]]("«ExponentProduct»(«Delete»(u, m))")
						zResidual := b.TermAs[Set[A]]("«ExponentProduct»(«Delete»(z, m))")
						um, zm := b.TermAs[Nat]("u(m)"), b.TermAs[Nat]("z(m)")
						uSupport := b.TermAs[Set[Set[A]]]("«SupportOf»(u)")
						zSupport := b.TermAs[Set[Set[A]]]("«SupportOf»(z)")
						union := b.TermAs[Set[Set[A]]]("«SupportOf»(u) ∪ «SupportOf»(z)")
						mIn := b.Have(
							"m, supported in u, is an ideal",
							"m ∈ «Ideals»",
							BySets(previous[1], given[1]))
						uFactors := b.Have(
							"u's supported factors are ideals",
							"∀q:set(A). u(q) ≠ 0 ⇒ ring_ideal(R, q)",
							BySets(given[1]))
						zFactors := b.Have(
							"z's supported factors are ideals",
							"∀q:set(A). z(q) ≠ 0 ⇒ ring_ideal(R, q)",
							BySets(given[1]))
						sumFactors := b.Have(
							"the sum's supported factors are ideals",
							"∀q:set(A). «Sum»(u, z, q) ≠ 0 ⇒ ring_ideal(R, q)",
							BySets(given[1], nat_arith.AddEqZero))
						finiteUnion := b.Have(
							"the two supports have a finite union",
							"finite(«SupportOf»(u) ∪ «SupportOf»(z))",
							By(previous[2], given[0], finite_set.FiniteUnion.At(uSupport, zSupport)))
						finiteSum := b.Have(
							"the sum, supported inside that union, has finite support",
							"finite(«SupportOf»(«Sum»(u, z)))",
							By(
								finiteUnion,
								sumSupport.At(u, z),
								finite_set.FiniteSubset.At(b.TermAs[Set[Set[A]]]("«SupportOf»(«Sum»(u, z))"), union)))
						deletedInside := b.Have(
							"erasing m keeps each support inside the original",
							"«SupportOf»(«Delete»(u, m)) ⊆ «SupportOf»(u) ∧ «SupportOf»(«Delete»(z, m)) ⊆ «SupportOf»(z)",
							BySets())
						finiteDeleted := b.Have(
							"so both erased vectors have finite support",
							"finite(«SupportOf»(«Delete»(u, m))) ∧ finite(«SupportOf»(«Delete»(z, m)))",
							By(
								previous[2],
								given[0],
								deletedInside,
								finite_set.FiniteSubset.At(b.TermAs[Set[Set[A]]]("«SupportOf»(«Delete»(u, m))"), uSupport),
								finite_set.FiniteSubset.At(b.TermAs[Set[Set[A]]]("«SupportOf»(«Delete»(z, m))"), zSupport)))
						deletedFactors := b.Have(
							"every factor of either erased vector is an ideal",
							"∀q:set(A). «Delete»(u, m, q) ≠ 0 ∨ «Delete»(z, m, q) ≠ 0 ⇒ ring_ideal(R, q)",
							BySets(given[1]))
						eachDeleted := b.Have(
							"the supported factors of each erased vector are ideals",
							"(∀q:set(A). «Delete»(u, m, q) ≠ 0 ⇒ ring_ideal(R, q)) ∧ "+
								"(∀q:set(A). «Delete»(z, m, q) ≠ 0 ⇒ ring_ideal(R, q))",
							BySets(uFactors, zFactors))
						splitU := b.Have(
							"split the m power from the first product",
							"«ExponentProduct»(u) = «Product»(ideal_pow(R, m, u(m)), «ExponentProduct»(«Delete»(u, m)))",
							By(previous[2], uFactors, IdealExponentProductSplit.Read(R).At(u, m)))
						splitZ := b.Have(
							"split the m power from the second product",
							"«ExponentProduct»(z) = «Product»(ideal_pow(R, m, z(m)), «ExponentProduct»(«Delete»(z, m)))",
							By(given[0], zFactors, IdealExponentProductSplit.Read(R).At(z, m)))
						splitSum := b.Have(
							"split the combined m power from the sum product",
							"«ExponentProduct»(«Sum»(u, z)) = "+
								"«Product»(ideal_pow(R, m, «Sum»(u, z, m)), «ExponentProduct»(«Delete»(«Sum»(u, z), m)))",
							By(finiteSum, sumFactors, IdealExponentProductSplit.Read(R).At(sum, m)))
						deleteSum := b.Have(
							"erasing a coordinate commutes with adding exponents",
							"«Delete»(«Sum»(u, z), m) = «Sum»(«Delete»(u, m), «Delete»(z, m))",
							By(nat_arith.AddZero))
						residualIH := b.Have(
							"addition holds for the two erased vectors",
							"«Law»(«Delete»(u, m), «Delete»(z, m))",
							By(finiteDeleted, deletedFactors, previous[0].At(zDelete)))
						residualsIn := b.Have(
							"the two residual products are ideals",
							"«ExponentProduct»(«Delete»(u, m)) ∈ «Ideals» ∧ «ExponentProduct»(«Delete»(z, m)) ∈ «Ideals»",
							BySets(
								finiteDeleted,
								eachDeleted,
								IdealExponentProductIntegral.Read(R).At(uDelete),
								IdealExponentProductIntegral.Read(R).At(zDelete)))
						powersIn := b.Have(
							"the two extracted powers are ideals",
							"ideal_pow(R, m, u(m)) ∈ «Ideals» ∧ ideal_pow(R, m, z(m)) ∈ «Ideals»",
							By(mIn, ring_ideal.IdealPowIdeal.Read(R).At(m, um), ring_ideal.IdealPowIdeal.Read(R).At(m, zm)))
						b.Show(
							"combine the extracted powers and regroup the four factors",
							CalcEq(
								Leg(
									b.TermAs[Set[A]](
										"«Product»(ideal_pow(R, m, «Sum»(u, z, m)), «ExponentProduct»(«Delete»(«Sum»(u, z), m)))"),
									"split the sum product",
									By(splitSum)),
								Leg(
									b.TermAs[Set[A]](
										"«Product»(«Product»(ideal_pow(R, m, u(m)), ideal_pow(R, m, z(m))), "+
											"    «Product»(«ExponentProduct»(«Delete»(u, m)), «ExponentProduct»(«Delete»(z, m))))"),
									"add the powers and use induction on the residual products",
									By(mIn, ring_ideal.IdealPowAdd.Read(R).At(m, um, zm), deleteSum, residualIH)),
								Leg(
									b.TermAs[Set[A]](
										"«Product»(«Product»(ideal_pow(R, m, u(m)), «ExponentProduct»(«Delete»(u, m))), "+
											"    «Product»(ideal_pow(R, m, z(m)), «ExponentProduct»(«Delete»(z, m))))"),
									"regroup powers with their corresponding residual products",
									By(powersIn, residualsIn, rearrange.At(uPower, zPower, uResidual, zResidual))),
								FinalLeg(
									"reassemble the two original exponent products",
									By(splitU, splitZ))))
					}))))
		a.Show(
			"the motive at v, applied to w",
			By(p[0], p[1], p[2], added.At(v)))
	}),
})}

// InvertibleStableChainStep — when multiplication by a proper invertible ideal
// fixes I, multiplying a chain above I and appending S makes a longer chain.
// The product stays integral, cancellation keeps the old steps strict, and
// properness supplies the final step.
var InvertibleStableChainStep = invertibleStableChainStepThm{family.Add(registry.ProofEntry{
	Name: "InvertibleStableChainStep",
	Key:  "prop_49feb60ec49e8792",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S I M:set(A). ∀C:(num → set(A)). ∀n:num.",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"ring_ideal(restrict_ring(field_ring(L), S), M)",
			"M ≠ S",
			"invertible_fractional(field_ring(L), S, M)",
			"I = fractional_mul(field_ring(L), S, M, I)",
			"ideal_chain(restrict_ring(field_ring(L), S), I, C, n)",
		},
		Conclusion: "ideal_chain(restrict_ring(field_ring(L), S), " +
			"    I, " +
			"    λi:num. COND(i ≤ n, fractional_mul(field_ring(L), S, M, C(i)), S), " +
			"    n + 1)",
	}, func(
		a *Argument,
		L field.FieldFact[on.L],
		S, I, M *Expr[Set[A]],
		C *Arrow[Nat, Set[A]],
		n *Expr[Nat],
		h Fact,
	) {
		p := a.Conjuncts(
			h,
			"S is a subring of L",
			"M is integral",
			"M is proper",
			"M is invertible",
			"multiplication by M fixes I",
			"C is a chain from I to S")
		sInL := a.Have(
			"S lies in L",
			"S ⊆ L.carrier",
			By(comm_ring.SubringSubset.Read(p[0])))
		laws := a.Conjuncts(
			a.Unfolded(p[5], idealChainDef),
			"C starts at I",
			"C ends at S",
			"the terms of C are ideals",
			"each step of C is strict")
		r := a.TermAs[RingOps[A]]("restrict_ring(field_ring(L), S)")
		D, dDef := a.LetAs[Fun[Nat, Set[A]]](
			"D", "λi:num. COND(i ≤ n, fractional_mul(field_ring(L), S, M, C(i)), S)")
		low := a.Have(
			"through n the chain multiplies the old terms by M",
			"∀i:num. i ≤ n ⇒ D(i) = fractional_mul(field_ring(L), S, M, C(i))",
			Derive(func(b *Argument) {
				b.FixAs[Nat]("i")
				before := b.Assume()
				b.Do(Simp(Fwd(dDef)))
				// ByArith evaluates the arithmetic guard of the COND, here and at the closes on D below.
				b.Show(
					"the cutoff selects the product",
					ByArith(before))
			}))
		upper := a.Have(
			"after n the chain is S",
			"∀i:num. n < i ⇒ D(i) = S",
			Derive(func(b *Argument) {
				b.FixAs[Nat]("i")
				after := b.Assume()
				b.Do(Simp(Fwd(dDef)))
				b.Show(
					"the cutoff selects S",
					ByArith(after))
			}))
		starts := a.Have(
			"D starts at I because mI is I",
			"D(0) = I",
			ByArith(low.At(a.TermAs[Nat]("0")), laws[0], p[4]))
		ends := a.Have(
			"D ends at S one step later",
			"D(n + 1) = S",
			ByArith(upper))
		mData := a.Have(
			"M is fractional and lies in S",
			"submodule(restrict_ring(field_ring(L), S), regular_module(field_ring(L)), M) ∧ M ⊆ S",
			By(p[0], p[1], fractional_ideal.IntegralIdealFractional.Read(L).At(S, M)))
		mInL := a.Have(
			"M lies in L",
			"M ⊆ L.carrier",
			BySets(mData, sInL))
		leftUnit := a.Have(
			"S acts as the unit on M",
			"fractional_mul(field_ring(L), S, S, M) = M",
			By(p[0], mData, fractional_ideal.FractionalMulOne.Read(L).At(S, M)))
		rightUnit := a.Have(
			"M times S is M",
			"fractional_mul(field_ring(L), S, M, S) = M",
			By(Normalized, sInL, mInL, leftUnit, fractional_ideal.FractionalMulComm.Read(L).At(S, M, S)))
		penultimate := a.Have(
			"the penultimate term is M",
			"D(n) = M",
			ByArith(low.At(n), laws[1], rightUnit))
		ideals := a.Have(
			"all terms of D are integral ideals",
			"∀i:num. i ≤ n + 1 ⇒ ring_ideal(restrict_ring(field_ring(L), S), D(i))",
			Derive(func(b *Argument) {
				i := b.FixAs[Nat]("i")
				b.Assume()
				b.Cases(b.TermAs[Bool]("i ≤ n"))
				b.When(
					"an old index gives a product of integral ideals",
					func(c *Argument, before Fact) {
						c.Show(
							"the product is integral",
							By(
								Normalized,
								before,
								p[0],
								p[1],
								laws[2].At(i),
								low.At(i),
								IntegralFractionalProduct.Read(L).At(S, M, c.TermAs[Set[A]]("C(i)"))))
					})
				b.Otherwise(
					"a later index gives the scalar ring",
					func(c *Argument, after Fact) {
						c.Show(
							"S is an ideal of itself",
							ByArith(
								after,
								upper.At(i),
								p[0],
								comm_ring.SubringRingOn.Read(field.RingOn.Read(L)).At(S),
								ring_ideal.CarrierIdeal.At(r)))
					})
			}))
		strict := a.Have(
			"all steps of D are strict inclusions",
			"∀i:num. i < n + 1 ⇒ D(i) ⊆ D(i + 1) ∧ D(i) ≠ D(i + 1)",
			Derive(func(b *Argument) {
				i := b.FixAs[Nat]("i")
				inRange := b.Assume()
				b.Cases(b.TermAs[Bool]("i < n"))
				b.When(
					"multiplication preserves each old strict step",
					func(c *Argument, before Fact) {
						next := c.TermAs[Nat]("i + 1")
						ci, cj := c.TermAs[Set[A]]("C(i)"), c.TermAs[Set[A]]("C(i + 1)")
						bounds := c.Have(
							"both old indices lie in the chain",
							"i ≤ n ∧ i + 1 ≤ n",
							ByArith(before))
						oldIdeals := c.Have(
							"the adjacent old terms are ideals",
							"ring_ideal(restrict_ring(field_ring(L), S), C(i)) ∧ "+
								"ring_ideal(restrict_ring(field_ring(L), S), C(i + 1))",
							By(bounds, laws[2].At(i), laws[2].At(next)))
						fractional := c.Have(
							"both adjacent terms are fractional",
							"submodule(restrict_ring(field_ring(L), S), regular_module(field_ring(L)), C(i)) ∧ "+
								"submodule(restrict_ring(field_ring(L), S), regular_module(field_ring(L)), C(i + 1))",
							By(
								p[0],
								oldIdeals,
								fractional_ideal.IntegralIdealFractional.Read(L).At(S, ci),
								fractional_ideal.IntegralIdealFractional.Read(L).At(S, cj)))
						distinct := c.Have(
							"cancellation keeps their products distinct",
							"fractional_mul(field_ring(L), S, M, C(i)) ≠ fractional_mul(field_ring(L), S, M, C(i + 1))",
							By(p[0], p[3], fractional, before, laws[3].At(i), InvertibleMulCancel.Read(L).At(S, M, ci, cj)))
						c.Show(
							"monotonicity gives inclusion and cancellation makes it strict",
							By(
								bounds,
								before,
								laws[3].At(i),
								low.At(i),
								low.At(next),
								distinct,
								set_order.SubsetRefl,
								fractional_ideal.FractionalMulMono.Read(L).At(S, M, M, ci, cj)))
					})
				b.Otherwise(
					"the last step is M properly contained in S",
					func(c *Argument, last Fact) {
						atEnd := c.Have(
							"the remaining index is n",
							"i = n",
							ByArith(inRange, last))
						c.Do(atEnd.Rw())
						c.Show(
							"the appended step is strict",
							By(Normalized, penultimate, ends, mData, p[2]))
					})
			}))
		a.Show(
			"D is a chain one step longer",
			By(starts, ends, ideals, strict, idealChainDef.At(r, I, D, a.TermAs[Nat]("n + 1"))))
	}),
})}

// DivideByMaximalStrict — division by an invertible maximal ideal strictly
// enlarges a nonzero ideal of finite height: equality would fix I under
// multiplication and produce chains above I of every positive length.
var DivideByMaximalStrict = divideByMaximalStrictThm{family.Add(registry.ProofEntry{
	Name: "DivideByMaximalStrict",
	Key:  "prop_8411cac3d7ab1ffa",
	Reading: "This strictness uses ideal-chain height, " +
		"independently of quotient twisting or dimension formulas.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S I m:set(A).",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"ring_ideal(restrict_ring(field_ring(L), S), I)",
			"I ≠ {L.zero}",
			"maximal_ideal(restrict_ring(field_ring(L), S), m)",
			"I ⊆ m",
			"invertible_fractional(field_ring(L), S, m)",
			"finite_ideal_height(restrict_ring(field_ring(L), S), I)",
		},
		Conclusion: "I ≠ fractional_mul(field_ring(L), S, I, fractional_inverse(field_ring(L), S, m))",
	}, func(a *Argument, L field.FieldFact[on.L], S, I, m *Expr[Set[A]], h Fact) {
		p := a.Conjuncts(
			h,
			"S is a subring of L",
			"I is an ideal",
			"I is nonzero",
			"m is maximal",
			"I lies in m",
			"m is invertible",
			"I has finite height")
		ringS := a.Have(
			"S is a ring under L's operations",
			"comm_ring_on(restrict_ring(field_ring(L), S))",
			By(p[0], comm_ring.SubringRingOn.Read(field.RingOn.Read(L)).At(S)))
		r := a.TermAs[RingOps[A]]("restrict_ring(field_ring(L), S)")
		denied := a.SupposeNot()
		equal := a.Have(
			"suppose division leaves I unchanged",
			"I = fractional_mul(field_ring(L), S, I, fractional_inverse(field_ring(L), S, m))",
			By(denied))
		mIdeal := a.Have(
			"a maximal ideal is an ideal",
			"ring_ideal(restrict_ring(field_ring(L), S), m)",
			By(p[3], ring_ideal.MaximalIdealIdeal.At(r, m)))
		omitsOne := a.Have(
			"a maximal ideal omits one",
			"L.one ∉ m",
			By(p[3], ring_ideal.MaximalIdealProper.At(r, m)))
		one := a.Have(
			"one belongs to S",
			"L.one ∈ S",
			By(comm_ring.OneIn.Read(ringS)))
		mProper := a.Have(
			"m is properly contained in S",
			"m ≠ S",
			BySets(omitsOne, one))
		iProper := a.Have(
			"I also omits one",
			"I ≠ S",
			BySets(p[4], omitsOne, one))
		stable := a.Have(
			"division equality forces mI to equal I",
			"I = fractional_mul(field_ring(L), S, m, I)",
			By(
				Normalized,
				p[0],
				p[1],
				p[2],
				mIdeal,
				p[4],
				p[5],
				equal,
				DivideByInvertibleIdeal.Read(L).At(S, I, m)))
		chains := a.Have(
			"there are chains of every positive length",
			"∀n:num. ∃C:(num → set(A)). ideal_chain(restrict_ring(field_ring(L), S), I, C, n + 1)",
			Derive(func(b *Argument) {
				b.Binder("n")
				b.Induct("n")
				b.Base(
					"I properly contained in S is a chain of length one",
					func(c *Argument) {
						c.Take(c.TermAs[Fun[Nat, Set[A]]]("λi:num. COND(i = 0, I, S)"))
						c.Do(Unfold(idealChainDef), SplitConjAll(
							Case(
								"the last endpoint is S",
								ByArith()),
							Case(
								"both terms are ideals",
								Derive(func(d *Argument) {
									d.FixAs[Nat]("i")
									d.Assume()
									d.Cases(d.TermAs[Bool]("i = 0"))
									d.When(
										"at zero the term is I",
										func(e *Argument, zero Fact) {
											e.Show(
												"I is an ideal",
												ByArith(zero, p[1]))
										})
									d.Otherwise(
										"away from zero the term is S",
										func(e *Argument, nonzero Fact) {
											e.Show(
												"S is its own ideal",
												ByArith(nonzero, ringS, ring_ideal.CarrierIdeal.At(r)))
										})
								})),
							Case(
								"the sole step is the proper inclusion I into S",
								Derive(func(d *Argument) {
									d.FixAs[Nat]("i")
									inRange := d.Assume()
									zero := d.Have(
										"the sole index is zero",
										"i = 0",
										ByArith(inRange))
									d.Do(zero.Rw())
									d.Show(
										"I is properly contained in S",
										By(p[1], ring_ideal.IdealSubset.At(r, I), iProper))
								}))))
					})
				b.Step(
					"multiply the old chain by m and append S",
					func(c *Argument, ih Fact) {
						C, old := c.UnpackAs[Fun[Nat, Set[A]]](ih, "C")
						c.Take(
							c.TermAs[Fun[Nat, Set[A]]]("λi:num. COND(i ≤ n + 1, fractional_mul(field_ring(L), S, m, C(i)), S)"))
						length := c.Have(
							"the successor length is one more",
							"suc(n) + 1 = (n + 1) + 1",
							ByArith())
						c.Do(length.Rw())
						c.Show(
							"the extended chain has the required length",
							By(
								p[0],
								mIdeal,
								mProper,
								p[5],
								stable,
								old,
								InvertibleStableChainStep.Read(L).At(S, I, m, C, c.TermAs[Nat]("n + 1"))))
					})
			}))
		bound, bounded := a.UnpackAs[Nat](a.Unfolded(p[6], FiniteIdealHeightDef), "h")
		C, tooLong := a.UnpackAs[Fun[Nat, Set[A]]](chains.At(bound), "C")
		a.Show(
			"the chain of length h plus one contradicts the height bound",
			ByArith(bounded.At(C, a.TermAs[Nat]("h + 1")), tooLong))
	}),
})}

// IdealFactorizationExists — a nonzero ideal of finite height factors into
// invertible nonzero maximal ideals when its containing maximal ideals are
// invertible: division by a maximal ideal lowers height.
var IdealFactorizationExists = idealFactorizationExistsThm{family.Add(registry.ProofEntry{
	Name: "IdealFactorizationExists",
	Key:  "prop_465acf792b2d676b",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S I:set(A).",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"ring_ideal(restrict_ring(field_ring(L), S), I)",
			"I ≠ {L.zero}",
			"finite_ideal_height(restrict_ring(field_ring(L), S), I)",
			"∀m:set(A). " +
				"    maximal_ideal(restrict_ring(field_ring(L), S), m) ∧ I ⊆ m ⇒ " +
				"    invertible_fractional(field_ring(L), S, m)",
		},
		Conclusion: "∃v:(set(A) → num). " +
			"    finite(fun_support(0, v)) ∧ " +
			"    (∀m:set(A). " +
			"        v(m) ≠ 0 ⇒ " +
			"        maximal_ideal(restrict_ring(field_ring(L), S), m) ∧ " +
			"        m ≠ {L.zero} ∧ " +
			"        invertible_fractional(field_ring(L), S, m)) ∧ " +
			"    I = ideal_exponent_product(restrict_ring(field_ring(L), S), v)",
		Abbrev: Abbrev{
			{Name: "Good", Text: "λm:set(A). " +
				"    maximal_ideal(«R», m) ∧ m ≠ {L.zero} ∧ invertible_fractional(field_ring(L), S, m)"},
			{Name: "Factor", Text: "λH:set(A). ∃v:(set(A) → num). " +
				"    finite(fun_support(0, v)) ∧ " +
				"    (∀m:set(A). v(m) ≠ 0 ⇒ «Good»(m)) ∧ " +
				"    H = ideal_exponent_product(«R», v)"},
			{Name: "Admissible", Text: "λH:set(A). " +
				"    ring_ideal(«R», H) ∧ " +
				"    H ≠ {L.zero} ∧ " +
				"    finite_ideal_height(«R», H) ∧ " +
				"    (∀m:set(A). maximal_ideal(«R», m) ∧ H ⊆ m ⇒ invertible_fractional(field_ring(L), S, m))"},
		},
	}, func(a *Argument, L field.FieldFact[on.L], S, I *Expr[Set[A]], h Fact) {
		p := a.Conjuncts(
			h,
			"S is a subring of L",
			"I is integral",
			"I is nonzero",
			"I has finite height",
			"maximal ideals above I are invertible")
		subringS := p[0]
		ringS := a.Have(
			"S is a ring under L's operations",
			"comm_ring_on(«R»)",
			By(subringS, comm_ring.SubringRingOn.Read(field.RingOn.Read(L)).At(S)))
		r := a.TermAs[RingOps[A]]("«R»")
		indexed := a.Have(
			"every admissible ideal factors at its height",
			"∀n:num. ∀H:set(A). «Admissible»(H) ∧ ideal_height(«R», H) = n ⇒ «Factor»(H)",
			ByInduction(nat_order.StrongInduction,
				Case(
					"division reduces the height of every proper ideal",
					Derive(func(b *Argument) {
						b.FixAs[Nat]("n")
						ih := b.Assume()
						H := b.FixAs[Set[A]]("H")
						datum := b.Assume()
						d := b.Conjuncts(
							datum,
							"H is integral",
							"H is nonzero",
							"H has finite height",
							"maximal ideals above H are invertible",
							"H has height n")
						proper := b.Unless(
							b.Term("H = S"),
							"the unit ideal is the empty exponent product",
							Given(func(c *Argument, equal Fact) {
								empty := c.Have(
									"the zero vector has empty support",
									"fun_support(0, λm:set(A). 0) = ∅",
									BySets())
								finite := c.Have(
									"the zero vector has finite support",
									"finite(fun_support(0, λm:set(A). 0))",
									Simp(Fwd(empty)),
									By(finite_set.FiniteRules))
								unit := c.Have(
									"the zero exponent product is S",
									"ideal_exponent_product(«R», λm:set(A). 0) = S",
									Simp(
										Fwd(IdealExponentProductZero),
										Fwd(module_record.RestrictRingDef),
										Fwd(module_record.RingCarrierDef)),
									Basic())
								c.Take(c.TermAs[Fun[Set[A], Nat]]("λm:set(A). 0"))
								c.Show(
									"the zero vector factors the unit ideal",
									By(Normalized, finite, equal, unit))
							}))
						omitsOne := b.Have(
							"a proper ideal omits one",
							"L.one ∉ H",
							By(Normalized, d[0], proper, ring_ideal.IdealOneIff.Read(ringS).At(H)))
						m, above := b.ObtainAs[Set[A]](
							"choose a maximal ideal above H",
							"∃m:set(A). maximal_ideal(«R», m) ∧ H ⊆ m",
							By(d[0], omitsOne, ring_ideal.ExistsMaximalAbove.Read(ringS).At(H)),
							Named("m"))
						maximal := b.Conjuncts(
							above,
							"m is maximal",
							"m contains H")
						mIdeal := b.Have(
							"the maximal ideal is integral",
							"ring_ideal(«R», m)",
							By(maximal[0], ring_ideal.MaximalIdealIdeal.At(r, m)))
						mNonzero := b.Have(
							"a maximal ideal containing H is nonzero",
							"m ≠ {L.zero}",
							BySets(d[1], maximal[1], d[0], ring_ideal.IdealZero.At(r, H)))
						mInvertible := b.Have(
							"the local hypothesis makes m invertible",
							"invertible_fractional(field_ring(L), S, m)",
							By(maximal[0], maximal[1], d[3].At(m)))
						J, jDef := b.LetAs[Set[A]](
							"J", "fractional_mul(field_ring(L), S, H, fractional_inverse(field_ring(L), S, m))")
						division := b.Have(
							"division gives a larger nonzero integral ideal and recovers H",
							"ring_ideal(«R», J) ∧ J ≠ {L.zero} ∧ H = fractional_mul(field_ring(L), S, m, J) ∧ H ⊆ J",
							Simp(Fwd(jDef)),
							By(
								subringS,
								d[0],
								d[1],
								mIdeal,
								maximal[1],
								mInvertible,
								DivideByInvertibleIdeal.Read(L).At(S, H, m)))
						j := b.Conjuncts(
							division,
							"J is integral",
							"J is nonzero",
							"multiplying J by m recovers H",
							"J contains H")
						strict := b.Have(
							"division strictly enlarges H",
							"H ≠ J",
							Simp(Fwd(jDef)),
							By(
								subringS,
								d[0],
								d[1],
								maximal[0],
								maximal[1],
								mInvertible,
								d[2],
								DivideByMaximalStrict.Read(L).At(S, H, m)))
						descent := b.Have(
							"J has finite and strictly smaller height",
							"finite_ideal_height(«R», J) ∧ ideal_height(«R», J) < ideal_height(«R», H)",
							By(d[0], j[0], j[3], strict, d[2], IdealHeightStrict.Read(ringS).At(H, J)))
						heights := b.Conjuncts(
							descent,
							"J has finite height",
							"the height of J is smaller")
						jLocal := b.Have(
							"maximal ideals above J inherit the local invertibility condition",
							"∀q:set(A). maximal_ideal(«R», q) ∧ J ⊆ q ⇒ invertible_fractional(field_ring(L), S, q)",
							Derive(func(c *Argument) {
								q := c.FixAs[Set[A]]("q")
								containsJ := c.Assume()
								containsH := c.Have(
									"a maximal ideal above J also contains H",
									"H ⊆ q",
									BySets(j[3], containsJ))
								c.Show(
									"the hypothesis above H supplies invertibility",
									By(containsH, containsJ, d[3].At(q)))
							}))
						lower := b.Have(
							"the height of J is below the induction index",
							"ideal_height(«R», J) < n",
							ByArith(heights[1], d[4]))
						v, factors := b.ObtainAs[Fun[Set[A], Nat]](
							"factor J by the smaller-height induction hypothesis",
							"∃v:(set(A) → num). "+
								"    finite(fun_support(0, v)) ∧ "+
								"    (∀p:set(A). v(p) ≠ 0 ⇒ «Good»(p)) ∧ "+
								"    J = ideal_exponent_product(«R», v)",
							By(j[0], j[1], heights[0], jLocal, lower, ih.At(b.TermAs[Nat]("ideal_height(«R», J)"), J)),
							Named("v"))
						f := b.Conjuncts(
							factors,
							"v has finite support",
							"supported factors are maximal, nonzero and invertible",
							"v reconstructs J")
						bridge := b.Have(
							"integral and fractional multiplication agree for m and J",
							"ideal_mul(«R», m, J) = fractional_mul(field_ring(L), S, m, J)",
							By(subringS, mIdeal, j[0], IntegralMulAsFractional.Read(L).At(S, m, J)))
						recovers := b.Have(
							"m times J recovers H as an integral ideal product",
							"H = ideal_mul(«R», m, J)",
							Simp(Fwd(bridge)),
							By(j[2]))
						integralFactors := b.Have(
							"every supported factor of v is integral",
							"∀p:set(A). v(p) ≠ 0 ⇒ ring_ideal(«R», p)",
							By(f[1], Where(ring_ideal.MaximalIdealIdeal, "R", r)))
						mGood := b.Have(
							"m has all the required factor properties",
							"«Good»(m)",
							By(maximal[0], mNonzero, mInvertible))
						w, wDef := b.LetAs[Fun[Set[A], Nat]]("w", "λp:set(A). COND(p = m, v(m) + 1, v(p))")
						positive := b.Have(
							"the increased exponent is nonzero",
							"v(m) + 1 ≠ 0",
							ByArith())
						support := b.Have(
							"the increased support adjoins m",
							"fun_support(0, w) = insert(m, fun_support(0, v))",
							Simp(Fwd(wDef)),
							BySets(positive))
						finiteW := b.Have(
							"the increased vector has finite support",
							"finite(fun_support(0, w))",
							Simp(Fwd(support)),
							By(f[0], finite_set.FiniteInsert.At(m, b.TermAs[Set[Set[A]]]("fun_support(0, v)"))))
						goodW := b.Have(
							"every supported factor of the increased vector has the required properties",
							"∀p:set(A). w(p) ≠ 0 ⇒ «Good»(p)",
							Simp(Fwd(wDef)),
							Derive(func(c *Argument) {
								q := c.FixAs[Set[A]]("p")
								nonzero := c.Assume()
								c.Cases(c.TermAs[Bool]("p = m"))
								c.When(
									"the increased coordinate contributes m",
									func(e *Argument, equal Fact) {
										e.Show(
											"m has all required factor properties",
											Simp(Fwd(equal)),
											By(mGood))
									})
								c.Otherwise(
									"another coordinate retains its old factor",
									func(e *Argument, unequal Fact) {
										oldNonzero := e.Simplified(nonzero, Fwd(unequal))
										e.Show(
											"the original factor properties apply",
											By(Normalized, oldNonzero, f[1].At(q)))
									})
							}))
						increment := b.Have(
							"increasing the exponent multiplies the product by m",
							"ideal_exponent_product(«R», w) = ideal_mul(«R», m, ideal_exponent_product(«R», v))",
							Simp(Fwd(wDef)),
							By(mIdeal, f[0], integralFactors, IdealExponentProductIncrement.Read(ringS).At(m, v)))
						product := b.Have(
							"the increased exponent product is H",
							"H = ideal_exponent_product(«R», w)",
							Simp(Fwd(increment)),
							Simp(Rev(f[2])),
							By(recovers))
						b.Take(w)
						b.Show(
							"the increased vector factors H",
							By(finiteW, goodW, product))
					}))))
		a.Show(
			"apply height induction to the original ideal",
			By(p[1], p[2], p[3], p[4], indexed.At(a.TermAs[Nat]("ideal_height(«R», I)"), I)))
	}),
})}

// IdealFactorizationUnique — finite products of invertible maximal
// ideals have unique exponents: deletion isolates one maximal ideal, and
// cancellation compares its powers against residual products outside it.
var IdealFactorizationUnique = idealFactorizationUniqueThm{family.Add(registry.ProofEntry{
	Name: "IdealFactorizationUnique",
	Key:  "prop_b540ce85aaa9f569",
	Reading: "Only the ideals in each finite support are required to be maximal " +
		"and invertible; equality of their products determines every exponent.",
	Build: family.Sections(Statement{
		Binders: "∀L:field_on(A). ∀S:set(A). ∀v w:(set(A) → num).",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"finite(fun_support(0, v))",
			"∀m:set(A). " +
				"    v(m) ≠ 0 ⇒ " +
				"    maximal_ideal(restrict_ring(field_ring(L), S), m) ∧ " +
				"    invertible_fractional(field_ring(L), S, m)",
			"finite(fun_support(0, w))",
			"∀m:set(A). " +
				"    w(m) ≠ 0 ⇒ " +
				"    maximal_ideal(restrict_ring(field_ring(L), S), m) ∧ " +
				"    invertible_fractional(field_ring(L), S, m)",
			"ideal_exponent_product(restrict_ring(field_ring(L), S), v) = " +
				"ideal_exponent_product(restrict_ring(field_ring(L), S), w)",
		},
		Conclusion: "v = w",
		Abbrev: Abbrev{
			{Name: "Ideals", Text: "{I:set(A) | ring_ideal(«R», I)}"},
			{Name: "Product", Text: "λI:set(A). λJ:set(A). ideal_mul(«R», I, J)"},
			{Name: "VRest", Text: "λm:set(A). ideal_exponent_product(«R», «Delete»(v, m))"},
			{Name: "WRest", Text: "λm:set(A). ideal_exponent_product(«R», «Delete»(w, m))"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		comparePowers := ctx.Lemma(Statement{
			Binders: "∀L:field_on(A). ∀S m A₁ B₁:set(A). ∀a b:num.",
			Hypotheses: []string{
				"subring(field_ring(L), S)",
				"ring_ideal(«R», m)",
				"invertible_fractional(field_ring(L), S, m)",
				"ring_ideal(«R», A₁)",
				"ring_ideal(«R», B₁)",
				"¬(A₁ ⊆ m)",
				"¬(B₁ ⊆ m)",
				"ideal_mul(«R», ideal_pow(«R», m, a), A₁) = ideal_mul(«R», ideal_pow(«R», m, b), B₁)",
			},
			Conclusion: "a = b",
		}, func(a *Argument, L field.FieldFact[on.L], S, m, A1, B1 *Expr[Set[A]], h Fact) {
			p := a.Conjuncts(
				h,
				"S is a subring of L",
				"m is an ideal",
				"m is invertible",
				"A₁ is an ideal",
				"B₁ is an ideal",
				"m does not hold A₁",
				"m does not hold B₁")
			ringS := a.Have(
				"S is a ring under L's operations",
				"comm_ring_on(«R»)",
				By(p[0], comm_ring.SubringRingOn.Read(field.RingOn.Read(L)).At(S)))
			monoid := a.Have(
				"integral ideals form a commutative monoid",
				"comm_monoid_on(«Ideals», «Product», S)",
				By(ring_ideal.IdealsCommMonoid.Read(ringS)))
			members := a.Have(
				"the three ideals belong to the monoid carrier",
				"m ∈ «Ideals» ∧ A₁ ∈ «Ideals» ∧ B₁ ∈ «Ideals»",
				BySets(h))
			successorContained := a.Have(
				"a positive power times an integral ideal lies in m",
				"∀X:set(A). ∀k:num. ring_ideal(«R», X) ⇒ ideal_mul(«R», ideal_pow(«R», m, suc(k)), X) ⊆ m",
				Derive(func(b *Argument) {
					X, k := b.FixAs[Set[A]]("X"), b.FixAs[Nat]("k")
					integralX := b.Assume()
					power := b.TermAs[Set[A]]("ideal_pow(«R», m, k)")
					next := b.TermAs[Set[A]]("ideal_pow(«R», m, suc(k))")
					powers := b.Have(
						"both powers are integral",
						"ring_ideal(«R», ideal_pow(«R», m, k)) ∧ ring_ideal(«R», ideal_pow(«R», m, suc(k)))",
						BySets(
							members,
							ring_ideal.IdealPowIdeal.Read(ringS).At(m, k),
							ring_ideal.IdealPowIdeal.Read(ringS).At(m, b.TermAs[Nat]("suc(k)"))))
					powerInM := b.Have(
						"the successor power, m times the power at k, lies in its factor m",
						"ideal_pow(«R», m, suc(k)) ⊆ m",
						Simp(Fwd(ring_ideal.IdealPowZero), Fwd(ring_ideal.IdealPowSuc)),
						BySets(p[1], powers, ring_ideal.IdealMulSubsetInter.Read(ringS).At(m, power)))
					productInPower := b.Have(
						"its product with X lies in its own factor, the power",
						"ideal_mul(«R», ideal_pow(«R», m, suc(k)), X) ⊆ ideal_pow(«R», m, suc(k))",
						BySets(integralX, powers, ring_ideal.IdealMulSubsetInter.Read(ringS).At(next, X)))
					b.Show(
						"the product lies in m through the successor power",
						BySets(powerInM, productInPower))
				}))
			a.Show(
				"induction compares the two powers",
				ByInduction(peano.Induction,
					Case(
						"a zero exponent forces the other exponent to vanish",
						Derive(func(b *Argument) {
							bexp := b.FixAs[Nat]("b")
							equal := b.Assume()
							nonzero := b.Unless(
								b.Term("b = 0"),
								"two zero exponents agree",
								Given(func(c *Argument, zero Fact) {
									c.Show(
										"b is zero, as a is",
										By(zero))
								}))
							k, successor := b.ObtainAs[Nat](
								"a nonzero exponent has a predecessor",
								"∃k:num. b = suc(k)",
								By(Normalized, nonzero, peano.Cases.At(bexp)))
							unit := b.Have(
								"the zeroth power leaves the first residual unchanged",
								"ideal_mul(«R», ideal_pow(«R», m, 0), A₁) = A₁",
								Simp(Fwd(ring_ideal.IdealPowZero), Fwd(ring_ideal.IdealPowSuc)),
								By(members, comm_monoid.LeftIdentityOn.Read(monoid)))
							inside := b.Have(
								"a positive opposite exponent puts the first residual in m",
								"A₁ ⊆ m",
								BySets(equal, unit, successor, h, successorContained.At(B1, k)))
							b.Show(
								"the first residual cannot lie in m",
								By(inside, h))
						})),
					Case(
						"cancelling one common factor reduces both positive exponents",
						Derive(func(b *Argument) {
							n := b.FixAs[Nat]("n")
							ih := b.Assume()
							bexp := b.FixAs[Nat]("b")
							equal := b.Assume()
							nonzero := b.Unless(
								b.Term("b = 0"),
								"a zero opposite exponent puts the second residual in m",
								Given(func(c *Argument, zero Fact) {
									unit := c.Have(
										"the zeroth power leaves the second residual unchanged",
										"ideal_mul(«R», ideal_pow(«R», m, 0), B₁) = B₁",
										Simp(Fwd(ring_ideal.IdealPowZero), Fwd(ring_ideal.IdealPowSuc)),
										By(members, comm_monoid.LeftIdentityOn.Read(monoid)))
									inside := c.Have(
										"the positive first exponent puts the second residual in m",
										"B₁ ⊆ m",
										BySets(equal, unit, zero, h, successorContained.At(A1, n)))
									c.Show(
										"the second residual cannot lie in m",
										By(inside, h))
								}))
							k, successor := b.ObtainAs[Nat](
								"the other positive exponent has a predecessor",
								"∃k:num. b = suc(k)",
								By(Normalized, nonzero, peano.Cases.At(bexp)))
							powers := b.Have(
								"the predecessor powers lie in the ideal carrier",
								"ideal_pow(«R», m, n) ∈ «Ideals» ∧ ideal_pow(«R», m, k) ∈ «Ideals»",
								By(
									members,
									ring_ideal.IdealPowIdeal.Read(ringS).At(m, n),
									ring_ideal.IdealPowIdeal.Read(ringS).At(m, k)))
							U, uDef := b.LetAs[Set[A]]("U", "ideal_mul(«R», ideal_pow(«R», m, n), A₁)")
							V, vDef := b.LetAs[Set[A]]("V", "ideal_mul(«R», ideal_pow(«R», m, k), B₁)")
							integral := b.Have(
								"the predecessor residual products are integral",
								"ring_ideal(«R», U) ∧ ring_ideal(«R», V)",
								Simp(Fwd(uDef), Fwd(vDef)),
								BySets(
									powers,
									members,
									comm_monoid.OpIn.Read(monoid).AsFact().At(b.TermAs[Set[A]]("ideal_pow(«R», m, n)"), A1),
									comm_monoid.OpIn.Read(monoid).AsFact().At(b.TermAs[Set[A]]("ideal_pow(«R», m, k)"), B1)))
							first := b.Have(
								"the first successor product exposes m",
								"ideal_mul(«R», ideal_pow(«R», m, suc(n)), A₁) = ideal_mul(«R», m, U)",
								Simp(Fwd(uDef), Fwd(ring_ideal.IdealPowZero), Fwd(ring_ideal.IdealPowSuc)),
								By(powers, members, comm_monoid.AssocOn.Read(monoid)))
							second := b.Have(
								"the second successor product exposes m",
								"ideal_mul(«R», ideal_pow(«R», m, suc(k)), B₁) = ideal_mul(«R», m, V)",
								Simp(Fwd(vDef), Fwd(ring_ideal.IdealPowZero), Fwd(ring_ideal.IdealPowSuc)),
								By(powers, members, comm_monoid.AssocOn.Read(monoid)))
							common := b.Have(
								"the products with common first factor agree",
								"ideal_mul(«R», m, U) = ideal_mul(«R», m, V)",
								By(equal, second, first, successor))
							modules := b.Have(
								"both residual products are fractional submodules",
								"submodule(«R», regular_module(field_ring(L)), U) ∧ "+
									"submodule(«R», regular_module(field_ring(L)), V)",
								By(
									h,
									integral,
									fractional_ideal.IntegralIdealFractional.Read(L).At(S, U),
									fractional_ideal.IntegralIdealFractional.Read(L).At(S, V)))
							bridges := b.Have(
								"both common-factor products have their fractional reading",
								"ideal_mul(«R», m, U) = fractional_mul(field_ring(L), S, m, U) ∧ "+
									"ideal_mul(«R», m, V) = fractional_mul(field_ring(L), S, m, V)",
								By(
									integral,
									h,
									IntegralMulAsFractional.Read(L).At(S, m, U),
									IntegralMulAsFractional.Read(L).At(S, m, V)))
							fractional := b.Have(
								"the fractional products agree",
								"fractional_mul(field_ring(L), S, m, U) = fractional_mul(field_ring(L), S, m, V)",
								By(Normalized, bridges, common))
							cancelled := b.Have(
								"invertibility cancels m",
								"U = V",
								By(h, modules, fractional, InvertibleMulCancel.Read(L).At(S, m, U, V)))
							predecessors := b.Have(
								"the induction hypothesis equates the predecessors",
								"n = k",
								By(Normalized, cancelled, uDef, vDef, ih.At(k)))
							b.Show(
								"equal predecessors give equal successor exponents",
								ByArith(successor, predecessors))
						}))))
		})
		return ctx.Theorem(headline, func(
			a *Argument,
			L field.FieldFact[on.L],
			S *Expr[Set[A]],
			v, w *Arrow[Set[A], Nat],
			h Fact,
		) {
			pointwise := a.Have(
				"each maximal ideal has the same exponent",
				"∀m:set(A). v(m) = w(m)",
				Derive(func(b *Argument) {
					m := b.FixAs[Set[A]]("m")
					active := b.Unless(
						b.Term("v(m) = 0 ∧ w(m) = 0"),
						"two zero coordinates agree",
						Given(func(c *Argument, zeros Fact) {
							c.Show(
								"both coordinates are zero",
								By(Normalized, zeros))
						}))
					p := b.Conjuncts(
						h,
						"S is a subring of L",
						"v has finite support",
						"v has invertible maximal factors",
						"w has finite support",
						"w has invertible maximal factors",
						"the products agree")
					ringS := b.Have(
						"S is a ring under L's operations",
						"comm_ring_on(«R»)",
						By(p[0], comm_ring.SubringRingOn.Read(field.RingOn.Read(L)).At(S)))
					r := b.TermAs[RingOps[A]]("«R»")
					maximal := b.Have(
						"an active coordinate is maximal and invertible",
						"maximal_ideal(«R», m) ∧ invertible_fractional(field_ring(L), S, m)",
						By(active, p[2].At(m), p[4].At(m)))
					proper := b.Have(
						"m is an integral prime ideal omitting one",
						"ring_ideal(«R», m) ∧ prime_ideal(«R», m) ∧ L.one ∉ m",
						By(
							maximal,
							ring_ideal.MaximalIdealIdeal.At(r, m),
							ring_ideal.MaximalIdealProper.At(r, m),
							ring_ideal.MaximalIsPrime.Read(ringS).At(m)))
					residual := b.Have(
						"deleting m leaves an integral product outside m",
						Statement{
							Binders: "∀t:(set(A) → num).",
							Hypotheses: []string{
								"finite(fun_support(0, t))",
								"∀q:set(A). t(q) ≠ 0 ⇒ maximal_ideal(«R», q)",
							},
							Conclusion: "finite(fun_support(0, λq:set(A). «Delete»(t, m, q))) ∧ " +
								"ring_ideal(«R», ideal_exponent_product(«R», «Delete»(t, m))) ∧ " +
								"¬(ideal_exponent_product(«R», «Delete»(t, m)) ⊆ m)",
						},
						Derive(func(c *Argument) {
							c.FixAs[Fun[Set[A], Nat]]("t")
							given := c.Assume()
							u, uDef := c.LetAs[Fun[Set[A], Nat]]("u", "«Delete»(t, m)")
							support := c.Have(
								"the deleted support lies in the original support",
								"fun_support(0, u) ⊆ fun_support(0, t)",
								BySets(uDef))
							finite := c.Have(
								"the deleted support is finite",
								"finite(fun_support(0, u))",
								By(support, given, finite_set.FiniteSubset))
							factors := c.Have(
								"supported residual factors are maximal integral primes",
								"∀q:set(A). u(q) ≠ 0 ⇒ maximal_ideal(«R», q) ∧ ring_ideal(«R», q) ∧ prime_ideal(«R», q)",
								Derive(func(d *Argument) {
									q := d.FixAs[Set[A]]("q")
									positive := d.Assume()
									qMaximal := d.Have(
										"a supported residual factor is maximal",
										"maximal_ideal(«R», q)",
										BySets(positive, support, given))
									d.Show(
										"maximal factors are integral and prime",
										By(qMaximal, ring_ideal.MaximalIdealIdeal.At(r, q), ring_ideal.MaximalIsPrime.Read(ringS).At(q)))
								}))
							integral := c.Have(
								"the deleted product is integral",
								"ring_ideal(«R», ideal_exponent_product(«R», u))",
								By(finite, factors, IdealExponentProductIntegral.Read(ringS).At(u)))
							outside := c.Have(
								"the deleted product is not contained in m",
								"¬(ideal_exponent_product(«R», u) ⊆ m)",
								Derive(func(d *Argument) {
									inside := d.SupposeNot()
									q, divisor := d.ObtainAs[Set[A]](
										"a prime divisor would supply a supported factor inside m",
										"∃q:set(A). u(q) ≠ 0 ∧ q ⊆ m",
										By(proper, finite, factors, inside, IdealProductSubsetPrime.Read(ringS).At(m, u)))
									same := d.Have(
										"maximality identifies the divisor with m",
										"q = m",
										By(Normalized, factors.At(q), divisor, proper, ring_ideal.MaximalIdealMaximal.At(r, q, m)))
									d.Show(
										"the deleted coordinate cannot be supported",
										By(Normalized, same, uDef, divisor))
								}))
							c.Show(
								"the residual has finite support and an integral product outside m",
								By(finite, integral, outside))
						}))
					residuals := b.Have(
						"both residual products are integral and outside m",
						"ring_ideal(«R», «VRest»(m)) ∧ ¬(«VRest»(m) ⊆ m) ∧ ring_ideal(«R», «WRest»(m)) ∧ ¬(«WRest»(m) ⊆ m)",
						By(p[1], p[3], p[2], p[4], residual.At(v), residual.At(w)))
					integralFactors := b.Have(
						"both vectors have integral supported factors",
						"(∀q:set(A). v(q) ≠ 0 ⇒ ring_ideal(«R», q)) ∧ (∀q:set(A). w(q) ≠ 0 ⇒ ring_ideal(«R», q))",
						By(p[2], p[4], ring_ideal.MaximalIdealIdeal))
					splits := b.Have(
						"each product splits off the chosen coordinate",
						"ideal_exponent_product(«R», v) = ideal_mul(«R», ideal_pow(«R», m, v(m)), «VRest»(m)) ∧ "+
							"ideal_exponent_product(«R», w) = ideal_mul(«R», ideal_pow(«R», m, w(m)), «WRest»(m))",
						By(
							p[1],
							p[3],
							integralFactors,
							IdealExponentProductSplit.Read(ringS).At(v, m),
							IdealExponentProductSplit.Read(ringS).At(w, m)))
					b.Show(
						"the products agreeing, power comparison equates this coordinate",
						By(
							p[0],
							maximal,
							proper,
							residuals,
							p[5],
							splits,
							Read(comparePowers, L).At(
								S, m, b.TermAs[Set[A]]("«VRest»(m)"), b.TermAs[Set[A]]("«WRest»(m)"), v.Apply(m), w.Apply(m))))
				}))
			a.Show(
				"pointwise agreement gives equality of exponent vectors",
				By(Normalized, pointwise))
		})
	}),
})}

// NonzeroIdealInvertible — finite height and invertibility of nonzero maximal
// ideals make every nonzero ideal invertible: its finite maximal factorization
// is an invertible exponent product.
var NonzeroIdealInvertible = nonzeroIdealInvertibleThm{family.Add(registry.ProofEntry{
	Name: "NonzeroIdealInvertible",
	Key:  "prop_5af88ec519756c05",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S J:set(A).",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"∀H:set(A). " +
				"    ring_ideal(restrict_ring(field_ring(L), S), H) ∧ H ≠ {L.zero} ⇒ " +
				"    finite_ideal_height(restrict_ring(field_ring(L), S), H)",
			"∀m:set(A). " +
				"    maximal_ideal(restrict_ring(field_ring(L), S), m) ∧ m ≠ {L.zero} ⇒ " +
				"    invertible_fractional(field_ring(L), S, m)",
			"ring_ideal(restrict_ring(field_ring(L), S), J)",
			"J ≠ {L.zero}",
		},
		Conclusion: "invertible_fractional(field_ring(L), S, J)",
	}, func(a *Argument, L field.FieldFact[on.L], S *Expr[Set[A]], h Fact, J *Expr[Set[A]], j Fact) {
		p := a.Conjuncts(
			h,
			"S is a subring of L",
			"nonzero ideals have finite height",
			"nonzero maximal ideals are invertible")
		r := a.TermAs[RingOps[A]]("«R»")
		containing := a.Have(
			"every maximal ideal containing J is invertible",
			"∀m:set(A). maximal_ideal(«R», m) ∧ J ⊆ m ⇒ invertible_fractional(field_ring(L), S, m)",
			Derive(func(b *Argument) {
				m := b.FixAs[Set[A]]("m")
				above := b.Assume()
				nonzero := b.Have(
					"an ideal containing the nonzero ideal J is nonzero",
					"m ≠ {L.zero}",
					BySets(above, j, ring_ideal.IdealZero.At(r, J)))
				b.Show(
					"the global maximal-ideal hypothesis applies",
					By(nonzero, above, p[2].At(m)))
			}))
		v, factorization := a.ObtainAs[Fun[Set[A], Nat]](
			"factor J into invertible nonzero maximal ideals",
			"∃v:(set(A) → num). "+
				"    finite(fun_support(0, v)) ∧ "+
				"    (∀m:set(A). "+
				"        v(m) ≠ 0 ⇒ "+
				"        maximal_ideal(«R», m) ∧ m ≠ {L.zero} ∧ invertible_fractional(field_ring(L), S, m)) ∧ "+
				"    J = ideal_exponent_product(«R», v)",
			By(p[0], j, p[1].At(J), containing, IdealFactorizationExists.Read(L).At(S, J)))
		f := a.Conjuncts(
			factorization,
			"the factorization has finite support",
			"supported factors are invertible nonzero maximal ideals",
			"the exponent product equals J")
		integralFactors := a.Have(
			"supported factors are integral and invertible",
			"∀m:set(A). v(m) ≠ 0 ⇒ ring_ideal(«R», m) ∧ invertible_fractional(field_ring(L), S, m)",
			Derive(func(b *Argument) {
				m := b.FixAs[Set[A]]("m")
				supported := b.Assume()
				b.Show(
					"a maximal factor is an integral ideal",
					By(supported, f[1].At(m), ring_ideal.MaximalIdealIdeal.At(r, m)))
			}))
		invertible := a.Have(
			"the finite exponent product is invertible",
			"invertible_fractional(field_ring(L), S, ideal_exponent_product(«R», v))",
			By(p[0], f[0], integralFactors, IdealExponentProductInvertible.Read(L).At(S, v)))
		a.Show(
			"the factorization transfers invertibility to J",
			Simp(Fwd(f[2])),
			By(invertible))
	}),
})}

// IdealContainmentByExponents — for two finite exponent vectors supported on
// invertible maximal ideals, the product of v lies in the product of w exactly
// when every exponent of w is at most the matching exponent of v. Backward,
// factor out the nonnegative exponent difference; forward, cancel the common
// factors: a maximal factor left on the right would contain a product of
// maximal factors on the left distinct from it.
var IdealContainmentByExponents = idealContainmentByExponentsThm{family.Add(registry.ProofEntry{
	Name: "IdealContainmentByExponents",
	Key:  "prop_6884d229deaf20f8",
	Deps: []registry.EntryLike{IdealFactorizationUnique, IdealProductSubsetPrime},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀S:set(A). ∀v w:(set(A) → num).",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"finite(fun_support(0, v))",
			"∀m:set(A). " +
				"    v(m) ≠ 0 ⇒ " +
				"    maximal_ideal(restrict_ring(field_ring(L), S), m) ∧ " +
				"    invertible_fractional(field_ring(L), S, m)",
			"finite(fun_support(0, w))",
			"∀m:set(A). " +
				"    w(m) ≠ 0 ⇒ " +
				"    maximal_ideal(restrict_ring(field_ring(L), S), m) ∧ " +
				"    invertible_fractional(field_ring(L), S, m)",
		},
		Conclusion: "ideal_exponent_product(restrict_ring(field_ring(L), S), v) ⊆ " +
			"ideal_exponent_product(restrict_ring(field_ring(L), S), w) ⇔ " +
			"∀m:set(A). w(m) ≤ v(m)",
	},
		"For the reverse direction factor out the nonnegative exponent difference. "+
			"For the forward direction cancel common factors; a remaining maximal factor "+
			"on the right would contain a product of distinct maximal factors on the left."),
})}

// IdealExponentProductInvertible — a finite exponent product of invertible
// integral ideals is invertible: powers preserve invertibility, then induct on
// the support: the zero vector's product is the unit S, and at a nonzero
// coordinate m the full m power splits off, invertible, beside the product of
// the rest, invertible by the induction.
var IdealExponentProductInvertible = idealExponentProductInvertibleThm{family.Add(registry.ProofEntry{
	Name: "IdealExponentProductInvertible",
	Key:  "prop_d419466c7787306",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S:set(A). ∀v:(set(A) → num).",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"finite(fun_support(0, v))",
			"∀m:set(A). " +
				"    v(m) ≠ 0 ⇒ " +
				"    ring_ideal(restrict_ring(field_ring(L), S), m) ∧ invertible_fractional(field_ring(L), S, m)",
		},
		Conclusion: "invertible_fractional(field_ring(L), " +
			"    S, " +
			"    ideal_exponent_product(restrict_ring(field_ring(L), S), v))",
		Abbrev: Abbrev{
			{Name: "Motive", Text: "λu:(set(A) → num). " +
				"    (∀q:set(A). u(q) ≠ 0 ⇒ ring_ideal(«R», q) ∧ invertible_fractional(field_ring(L), S, q)) ⇒ " +
				"    invertible_fractional(field_ring(L), S, ideal_exponent_product(«R», u))"},
		},
	}, func(a *Argument, L field.FieldFact[on.L], S *Expr[Set[A]], v *Arrow[Set[A], Nat], h Fact) {
		p := a.Conjuncts(
			h,
			"S is a subring of L",
			"the support is finite",
			"supported factors are integral and invertible")
		subringS := p[0]
		ringS := a.Have(
			"S is a ring under L's operations",
			"comm_ring_on(restrict_ring(field_ring(L), S))",
			By(subringS, comm_ring.SubringRingOn.Read(field.RingOn.Read(L)).At(S)))
		unit := a.Have(
			"the scalar unit ideal is invertible",
			"invertible_fractional(field_ring(L), S, S)",
			By(subringS, fractional_ideal.SubringInvertible.Read(L).At(S)))
		powers := a.Have(
			"every natural fractional power of an invertible ideal is invertible",
			Statement{
				Binders: "∀m:set(A).",
				Hypotheses: []string{
					"invertible_fractional(field_ring(L), S, m)",
				},
				Conclusion: "∀n:num. " +
					"    invertible_fractional(field_ring(L), " +
					"        S, " +
					"        monoid_pow(fractional_mul(field_ring(L), S), S, m, n))",
			},
			Derive(func(b *Argument) {
				m := b.FixAs[Set[A]]("m")
				base := b.Assume()
				b.Binder("n")
				b.Induct("n")
				b.Base(
					"the zeroth power is the scalar unit ideal",
					Simp(Fwd(comm_monoid.MonoidPowDef)),
					By(unit))
				b.Step(
					"one more invertible factor preserves invertibility",
					func(c *Argument, ih Fact) {
						previous := c.TermAs[Set[A]]("monoid_pow(fractional_mul(field_ring(L), S), S, m, n)")
						c.Show(
							"the successor power is an invertible fractional product",
							Simp(Fwd(comm_monoid.MonoidPowDef)),
							By(subringS, base, ih, fractional_ideal.InvertibleProduct.Read(L).At(S, m, previous)))
					})
			}))
		products := a.Have(
			"every exponent product of finite support over invertible integral ideals is invertible",
			"∀u:(set(A) → num). finite(fun_support(0, u)) ⇒ «Motive»(u)",
			ByInduction(finite_set.FiniteInductSupport,
				Case(
					"the zero vector's product is the invertible unit",
					Derive(func(b *Argument) {
						b.Assume()
						b.Show(
							"the empty exponent product is S",
							Simp(
								Fwd(IdealExponentProductZero),
								Fwd(module_record.RestrictRingDef),
								Fwd(module_record.RingCarrierDef)),
							By(unit))
					})),
				Case(
					"a nonzero coordinate m contributes one invertible full power",
					Derive(func(b *Argument) {
						u := b.FixAs[Fun[Set[A], Nat]]("u")
						m := b.FixAs[Set[A]]("m")
						previous := b.Conjuncts(
							b.Assume(),
							"the rest of u has an invertible product when its factors are invertible",
							"u has an m factor",
							"u has finite support")
						factors := b.Assume()
						rest := b.TermAs[Fun[Set[A], Nat]]("«Delete»(u, m)")
						support := b.TermAs[Set[Set[A]]]("fun_support(0, u)")
						restSupport := b.TermAs[Set[Set[A]]]("fun_support(0, λq:set(A). «Delete»(u, m, q))")
						restProduct := b.TermAs[Set[A]]("ideal_exponent_product(«R», «Delete»(u, m))")
						power := b.TermAs[Set[A]]("ideal_pow(«R», m, u(m))")
						um := b.TermAs[Nat]("u(m)")
						base := b.Have(
							"m is integral and invertible",
							"ring_ideal(«R», m) ∧ invertible_fractional(field_ring(L), S, m)",
							By(previous[1], factors.At(m)))
						restFactors := b.Have(
							"the rest's supported factors are integral and invertible",
							Statement{
								Binders: "∀q:set(A).",
								Hypotheses: []string{
									"«Delete»(u, m, q) ≠ 0",
								},
								Conclusion: "ring_ideal(«R», q) ∧ invertible_fractional(field_ring(L), S, q)",
							},
							BySets(factors))
						residualInvertible := b.Have(
							"the motive at the rest makes its product invertible",
							"invertible_fractional(field_ring(L), S, ideal_exponent_product(«R», «Delete»(u, m)))",
							By(restFactors, previous[0]))
						ideals := b.Have(
							"each supported factor is integral",
							"∀q:set(A). u(q) ≠ 0 ⇒ ring_ideal(«R», q)",
							BySets(factors))
						restInside := b.Have(
							"the rest is supported inside u's support",
							"fun_support(0, λq:set(A). «Delete»(u, m, q)) ⊆ fun_support(0, u)",
							BySets())
						finiteRest := b.Have(
							"so its support is finite",
							"finite(fun_support(0, λq:set(A). «Delete»(u, m, q)))",
							By(previous[2], restInside, finite_set.FiniteSubset.At(restSupport, support)))
						restIdeals := b.Have(
							"each residual supported factor is integral",
							"∀q:set(A). «Delete»(u, m, q) ≠ 0 ⇒ ring_ideal(«R», q)",
							BySets(restFactors))
						residualIntegral := b.Have(
							"the residual exponent product is integral",
							"ring_ideal(«R», ideal_exponent_product(«R», «Delete»(u, m)))",
							By(finiteRest, restIdeals, IdealExponentProductIntegral.Read(ringS).At(rest)))
						powerIntegral := b.Have(
							"the extracted power is integral",
							"ring_ideal(«R», ideal_pow(«R», m, u(m)))",
							BySets(base, ring_ideal.IdealPowIdeal.Read(ringS).At(m, um)))
						powerInvertible := b.Have(
							"the extracted power is its fractional power, so invertible",
							"invertible_fractional(field_ring(L), S, ideal_pow(«R», m, u(m)))",
							By(subringS, base, IntegralPowAsFractional.Read(L).At(S, m, um), powers.At(m, um)))
						split := b.Have(
							"the full power splits from the exponent product",
							"ideal_exponent_product(«R», u) = "+
								"ideal_mul(«R», ideal_pow(«R», m, u(m)), ideal_exponent_product(«R», «Delete»(u, m)))",
							By(previous[2], ideals, IdealExponentProductSplit.Read(ringS).At(u, m)))
						bridge := b.Have(
							"the split integral product is a fractional product",
							"ideal_mul(«R», ideal_pow(«R», m, u(m)), ideal_exponent_product(«R», «Delete»(u, m))) = "+
								"fractional_mul(field_ring(L), "+
								"    S, "+
								"    ideal_pow(«R», m, u(m)), "+
								"    ideal_exponent_product(«R», «Delete»(u, m)))",
							By(
								subringS,
								residualIntegral,
								powerIntegral,
								IntegralMulAsFractional.Read(L).At(S, power, restProduct)))
						b.Show(
							"the two invertible factors give the product",
							Simp(Fwd(split), Fwd(bridge)),
							By(
								subringS,
								residualInvertible,
								powerInvertible,
								fractional_ideal.InvertibleProduct.Read(L).At(S, power, restProduct)))
					}))))
		a.Show(
			"the motive at v, whose support is finite",
			By(p[1], p[2], products.At(v)))
	}),
})}
