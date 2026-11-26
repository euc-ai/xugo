package valuation_order

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_embed"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_real_lift"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// UniqueExtremeOrderNonzero — a unique term of least order determines
// the order of a finite sum: the ring elements that are zero or of greater
// order are an additive monoid, which holds the rest of the sum, so the
// rest cannot cancel the distinguished term.
var UniqueExtremeOrderNonzero = uniqueExtremeOrderNonzeroThm{family.Add(registry.ProofEntry{
	Name: "UniqueExtremeOrderNonzero",
	Key:  "prop_df073a587ee68c38",
	Reading: "The conclusion reads v only at the nonzero sum and the nonzero term. Over a " +
		"ring with zero divisors the product law does constrain v(0); nothing here depends on it.",
	Build: family.Sections(Statement{
		Binders: "∀R:comm_ring_on(A). ∀v:(A → int). ∀E:set(B). ∀f:(B → A). ∀i:B.",
		Hypotheses: []string{
			"valuation_order(R, v)",
			"finite(E)",
			"i ∈ E",
			"∀j:B. j ∈ E ⇒ f(j) ∈ R.carrier",
			"f(i) ≠ R.zero",
			"∀j:B. j ∈ E ∧ j ≠ i ∧ f(j) ≠ R.zero ⇒ v(f(i)) < v(f(j))",
		},
		Conclusion: "module_sum(R.add, R.zero, E, f) ≠ R.zero ∧ " +
			"v(module_sum(R.add, R.zero, E, f)) = v(f(i))",
	}, func(ctx *Script, headline string) *GoalStackNode {
		higherSums := ctx.Lemma(Statement{
			Binders: "∀R:comm_ring_on(A). ∀v:(A → int). ∀t:int. ∀f:(B → A). ∀E:set(B).",
			Hypotheses: []string{
				"valuation_order(R, v)",
				"finite(E)",
				"∀j:B. j ∈ E ⇒ f(j) ∈ R.carrier ∧ (f(j) ≠ R.zero ⇒ t < v(f(j)))",
			},
			Conclusion: "module_sum(R.add, R.zero, E, f) = R.zero ∨ t < v(module_sum(R.add, R.zero, E, f))",
			Abbrev: Abbrev{
				{Name: "ZeroOrAbove", Text: "{z:A | z ∈ R.carrier ∧ (z = R.zero ∨ t < v(z))}"},
			},
		}, func(
			a *Argument,
			R comm_ring.CommRingFact[on.R],
			v *Arrow[A, Int],
			t *Expr[Int],
			f *Arrow[B, A],
			E *Expr[Set[B]],
			valuation, finite, terms Fact,
		) {
			additive := comm_ring.AddMonoidOn.Read(R)
			laws := a.Unfolded(valuation, ValuationOrderDef)
			closed := a.Have(
				"The ring elements that are zero or above the bound are closed under addition",
				"∀x y:A. x ∈ «ZeroOrAbove» ∧ y ∈ «ZeroOrAbove» ⇒ x + y ∈ «ZeroOrAbove»",
				Derive(func(b *Argument) {
					x := b.FixAs[A]("x")
					y := b.FixAs[A]("y")
					members := b.Assume()
					nonzero := b.Assuming(
						b.TermAs[Bool]("x ≠ R.zero ∧ y ≠ R.zero"),
						"A zero summand leaves the other summand",
						Given(func(c *Argument, zero Fact) {
							c.Show(
								"The sum is the other summand",
								By(
									Normalized,
									comm_monoid.LeftIdentityOn.Read(additive),
									comm_monoid.RightIdentityOn.Read(additive),
									zero,
									members))
						}))
					b.Show(
						"The ultrametric inequality keeps a nonzero sum above the bound",
						ByArith(nonzero, laws.At(x, y), members, comm_monoid.OpIn.Read(additive).AsFact().At(x, y)))
				}))
			monoid := a.Have(
				"These elements are a commutative monoid under the ring's addition",
				"comm_monoid_on(«ZeroOrAbove», R.add, R.zero)",
				Unfold(comm_monoid.CommMonoidOn),
				By(
					closed,
					comm_monoid.IdentityIn.Read(additive),
					comm_monoid.CommOn.Read(additive),
					comm_monoid.AssocOn.Read(additive),
					comm_monoid.LeftIdentityOn.Read(additive)))
			a.Show(
				"The finite sum of such elements is one of them",
				By(finite, terms, module.ModuleSumInMonoid.Read(monoid).At(E, f)))
		})
		return ctx.Theorem(headline,
			func(
				a *Argument,
				R comm_ring.CommRingFact[on.R],
				v *Arrow[A, Int],
				E *Expr[Set[B]],
				f *Arrow[B, A],
				i *Expr[B],
				valuation, finite, distinguishedIn, values, distinguishedNonzero, uniqueOrder Fact,
			) {
				additive := comm_ring.AddMonoidOn.Read(R)
				restIndices := a.TermAs[Set[B]]("delete(E, i)")
				rest, restDef := a.LetAs[A]("rest", "module_sum(R.add, R.zero, delete(E, i), f)")
				restBound := a.Have(
					"The rest of the sum is zero or of greater order",
					"rest = R.zero ∨ v(f(i)) < v(rest)",
					By(
						R,
						restDef,
						valuation,
						finite,
						values,
						uniqueOrder,
						At(higherSums, a.TermAs[RingOps[A]]("R"), v, v.Apply(f.Apply(i)), f, restIndices),
						finite_set.FiniteDeleteImp.At(E, i),
						set_basic.InDelete))
				peel := a.Have(
					"The whole sum is the distinguished term plus the rest",
					"module_sum(R.add, R.zero, E, f) = f(i) + rest",
					By(
						Normalized,
						restDef,
						finite,
						distinguishedIn,
						values,
						module.ModuleSumDeleteMonoid.Read(additive).At(E, i, f)))
				restIn := a.Have(
					"The rest lies in the ring carrier",
					"rest ∈ R.carrier",
					By(
						finite,
						values,
						restDef,
						module.ModuleSumInMonoid.Read(additive).At(restIndices, f),
						finite_set.FiniteDeleteImp.At(E, i),
						set_basic.InDelete))
				nonzeroRest := a.Assuming(
					a.TermAs[Bool]("rest ≠ R.zero"),
					"A zero rest leaves the distinguished term unchanged",
					Given(func(b *Argument, zeroRest Fact) {
						b.Show(
							"The whole sum has the distinguished term's value and order",
							By(
								Normalized,
								comm_monoid.RightIdentityOn.Read(additive),
								distinguishedNonzero,
								values.At(i),
								zeroRest,
								peel,
								distinguishedIn))
					}))
				laws := a.Unfolded(valuation, ValuationOrderDef)
				a.Show(
					"Unequal orders prevent cancellation and select the distinguished order",
					ByArith(
						nonzeroRest,
						distinguishedNonzero,
						laws.At(f.Apply(i), rest),
						values.At(i),
						peel,
						restIn,
						distinguishedIn,
						restBound))
			})
	}),
})}

// PowerOrder — a nonzero element of a field has nonzero powers, and the order of
// a power is the exponent times the order of the element: induction on the
// exponent, one being of order zero since it is its own square, and each new
// factor adding the order of the element.
var PowerOrder = powerOrderThm{family.Add(registry.ProofEntry{
	Name: "PowerOrder",
	Key:  "prop_4875442b02ac98a5",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀v:(A → int). ∀z:A. ∀n:num.",
		Hypotheses: []string{
			"valuation_order(field_ring(L), v)",
			"z ∈ L.carrier",
			"z ≠ L.zero",
		},
		Conclusion: "monoid_pow(L.mul, L.one, z, n) ≠ L.zero ∧ " +
			"v(monoid_pow(L.mul, L.one, z, n)) = &n * v(z)",
	}, func(
		a *Argument,
		L field.FieldFact[on.L],
		v *Arrow[A, Int],
		z *Expr[A],
		n *Expr[Nat],
		valuation, zIn, zNonzero Fact,
	) {
		ring := field.RingOn.Read(L)
		multiplicative := comm_ring.MulMonoidOn.Read(ring)
		laws := a.Unfolded(valuation, ValuationOrderDef)
		one := a.TermAs[A]("L.one")
		a.Induct(n)
		a.Base(
			"The empty product is one, nonzero and its own square, so of order zero",
			Simp(Fwd(comm_monoid.MonoidPowDef)),
			ByArith(
				laws.At(one, one),
				field.OneNotZeroOn.Read(L),
				comm_ring.OneIn.Read(ring),
				comm_monoid.LeftIdentityOn.Read(multiplicative)))
		a.Step(
			"One more factor keeps the product nonzero and adds the order of z",
			func(b *Argument, ih Fact) {
				power := b.TermAs[A]("monoid_pow(L.mul, L.one, z, n)")
				factor := b.Have(
					"z times its n-th power is nonzero, of the sum of the two orders",
					"z * monoid_pow(L.mul, L.one, z, n) ≠ L.zero ∧ "+
						"v(z * monoid_pow(L.mul, L.one, z, n)) = v(z) + &n * v(z)",
					By(
						zIn,
						zNonzero,
						ih,
						laws.At(z, power),
						comm_monoid.PowIn.Read(multiplicative).AsFact().At(z, n),
						field.MulEqZeroOn.Read(L).AsFact().At(z, power)))
				b.Show(
					"The cast of the successor distributes over the order of z",
					Simp(Fwd(comm_monoid.MonoidPowDef)),
					ByArith(factor, Scaled(v.Apply(z), int_embed.OfNumSuc.At(n))))
			})
	}),
})}

// DistinctOrdersSumNonzero — a finite sum, not all of whose terms vanish, is
// nonzero when its nonzero terms have pairwise different orders: the nonzero
// term of least order is the unique extreme term of UniqueExtremeOrderNonzero.
var DistinctOrdersSumNonzero = distinctOrdersSumNonzeroThm{family.Add(registry.ProofEntry{
	Name: "DistinctOrdersSumNonzero",
	Key:  "prop_e3c7f2bac998ef70",
	Build: family.Sections(Statement{
		Binders: "∀R:comm_ring_on(A). ∀v:(A → int). ∀E:set(B). ∀f:(B → A). ∀j:B.",
		Hypotheses: []string{
			"valuation_order(R, v)",
			"finite(E)",
			"∀i:B. i ∈ E ⇒ f(i) ∈ R.carrier",
			"j ∈ E",
			"f(j) ≠ R.zero",
			"injective_on(«support», λi:B. v(f(i)))",
		},
		Conclusion: "module_sum(R.add, R.zero, E, f) ≠ R.zero",
		Abbrev: Abbrev{
			{Name: "support", Text: "{i:B | i ∈ E ∧ f(i) ≠ R.zero}"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		leastOrder := ctx.Lemma(Statement{
			Binders:    "∀u:(B → int). ∀T:set(B). ∀j:B.",
			Hypotheses: []string{"finite(T)", "j ∈ T"},
			Conclusion: "∃m:B. m ∈ T ∧ (∀i:B. i ∈ T ⇒ u(m) ≤ u(i))",
		}, func(a *Argument, u *Arrow[B, Int], T *Expr[Set[B]], j *Expr[B], finite, member Fact) {
			inducted := a.Have(
				"Every finite set is empty or has a point of least value",
				"T = ∅ ∨ (∃m:B. m ∈ T ∧ (∀i:B. i ∈ T ⇒ u(m) ≤ u(i)))",
				ByInduction(finite_set.FiniteInductFresh, finite,
					Case(
						"The empty set is empty",
						Basic()),
					Case(
						"A new point is least, or the least point of the rest stays least",
						Derive(func(b *Argument) {
							x := b.FixAs[B]("x")
							b.FixAs[Set[B]]("s")
							carried := b.Conjuncts(
								b.Assume(),
								"s is empty or has a least point",
								"x is new to s",
								"s is finite")
							b.Do(Right())
							b.Cases(b.TermAs[Bool]("∀i:B. i ∈ s ⇒ u(x) ≤ u(i)"))
							b.When(
								"x lies below every point of s, so it is least",
								func(c *Argument, below Fact) {
									c.Take(x)
									c.Show(
										"x is a point of insert(x, s), below itself and all of s",
										Simp(Fwd(set_basic.ForallInInsert), Fwd(set_basic.InInsert)),
										ByArith(below))
								})
							b.Otherwise(
								"some point of s lies below x, so s has a least point, which stays least",
								func(c *Argument, notBelow Fact) {
									i, witness := c.ObtainAs[B](
										"Some point of s lies strictly below x",
										"∃i:B. i ∈ s ∧ u(i) < u(x)",
										By(notBelow, int_real_lift.NotLessEq))
									m, least := c.ObtainAs[B](
										"That point makes s nonempty, so s has a least point",
										"∃m:B. m ∈ s ∧ (∀i:B. i ∈ s ⇒ u(m) ≤ u(i))",
										BySets(carried[0], witness))
									parts := c.Conjuncts(
										least,
										"m lies in s",
										"m is least in s")
									c.Take(m)
									c.Show(
										"m lies in insert(x, s), below x through the point of s below x",
										Simp(Fwd(set_basic.ForallInInsert), Fwd(set_basic.InInsert)),
										ByArith(parts[1].At(i), parts[1], parts[0], witness))
								})
						}))))
			a.Show(
				"T has the point j, so it is not empty",
				BySets(inducted, member))
		})
		return ctx.Theorem(headline,
			func(
				a *Argument,
				R comm_ring.CommRingFact[on.R],
				v *Arrow[A, Int],
				E *Expr[Set[B]],
				f *Arrow[B, A],
				j *Expr[B],
				valuation, finite, values, jIn, jNonzero, distinct Fact,
			) {
				support := a.TermAs[Set[B]]("«support»")
				order := a.TermAs[Fun[B, Int]]("λi:B. v(f(i))")
				m, least := a.ObtainAs[B](
					"Some nonzero term has least order",
					"∃m:B. m ∈ «support» ∧ (∀i:B. i ∈ «support» ⇒ v(f(m)) ≤ v(f(i)))",
					By(
						jIn,
						jNonzero,
						At(leastOrder, order, support, j),
						finite,
						finite_set.FiniteRestrict.At(E, a.TermAs[Fun[B, Bool]]("λi:B. f(i) ≠ R.zero"))))
				parts := a.Conjuncts(
					least,
					"m indexes a nonzero term",
					"no nonzero term is of lesser order")
				injective := a.Unfolded(distinct, functions.InjectiveOnDef)
				unique := a.Have(
					"Every other nonzero term is of strictly greater order",
					"∀i:B. i ∈ E ∧ i ≠ m ∧ f(i) ≠ R.zero ⇒ v(f(m)) < v(f(i))",
					Derive(func(b *Argument) {
						i := b.FixAs[B]("i")
						other := b.Assume()
						b.Show(
							"Equal orders would make i the index m",
							ByArith(parts[1].At(i), injective.At(m, i), parts[0], other))
					}))
				a.Show(
					"The nonzero term of least order is the unique extreme term",
					By(R, valuation, finite, values, unique, parts[0], UniqueExtremeOrderNonzero))
			})
	}),
})}
