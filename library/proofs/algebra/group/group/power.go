// power.go — the powers of a member of a group on a set, and the
// exponents at which they lie in a subgroup.

package group

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_div_mod"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_divides"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/registry"
)

// PowIn — the powers of a member of a group on a set stay in its carrier.
// The induction of comm_monoid.PowIn — the identity at 0, one more factor of
// x at the step — uses no commutativity, and runs here on the group's own
// product and identity.
var PowIn = powInThm{family.Add(registry.ProofEntry{
	Name: "PowIn",
	Key:  "prop_84d8382ea328e3a3",
	Build: GroupOn.Law(Statement{
		Binders: "∀x:A. ∀n:num.",
		Hypotheses: []string{
			"x ∈ G.carrier",
		},
		Conclusion: "monoid_pow(G.mul, G.one, x, n) ∈ G.carrier",
	},
		func(a *Argument, grp GroupFact[on.G], x *Member[A, on.G], n *Expr[Nat]) {
			a.Induct(n)
			a.Base(
				"x ^ 0 is the identity, which lies in the carrier",
				Simp(Fwd(comm_monoid.MonoidPowDef)),
				By(OneIn, grp))
			a.Step(
				"x ^ suc(n) is x times x ^ n, both in the carrier",
				func(b *Argument, ih Fact) {
					b.Show(
						"a product of two members is a member",
						Simp(Fwd(comm_monoid.MonoidPowDef)),
						By(MulIn, grp, x, ih))
				})
		}),
})}

// PowOne — the first power of a member of a group on a set is the member:
// 1 is the successor of 0, and x times the identity is x. It is
// comm_monoid.PowOneOn for a product that need not commute.
var PowOne = powOneThm{family.Add(registry.ProofEntry{
	Name: "PowOne",
	Key:  "prop_9205bd00b5033a30",
	Build: GroupOn.Law(Statement{
		Binders: "∀x:A.",
		Hypotheses: []string{
			"x ∈ G.carrier",
		},
		Conclusion: "monoid_pow(G.mul, G.one, x, 1) = x",
	},
		func(a *Argument, grp GroupFact[on.G], x *Member[A, on.G]) {
			a.Show(
				"x ^ suc(0) is x times the identity",
				Simp(Fwd(nat_arith.OneIsSucZero)),
				Simp(Fwd(comm_monoid.MonoidPowDef)),
				By(RightIdentityOn, grp, x))
		}),
})}

// PowAdd — exponents add in a group on a set, whose product need not
// commute: by induction on m, the step reassociates one more factor of x
// past x ^ m, which associativity alone allows.
var PowAdd = powAddThm{family.Add(registry.ProofEntry{
	Name: "PowAdd",
	Key:  "prop_4a5efb6597f242aa",
	Build: GroupOn.Law(Statement{
		Binders: "∀x:A. ∀m n:num.",
		Hypotheses: []string{
			"x ∈ G.carrier",
		},
		Conclusion: "monoid_pow(G.mul, G.one, x, m + n) = " +
			"monoid_pow(G.mul, G.one, x, m) * monoid_pow(G.mul, G.one, x, n)",
	},
		func(a *Argument, grp GroupFact[on.G], x *Member[A, on.G], m, n *Expr[Nat]) {
			a.Induct(m)
			a.Base(
				"at m = 0 the sum is n, and x ^ 0 is the identity",
				Simp(Fwd(nat_arith.AddLeftZeroClause), Fwd(comm_monoid.MonoidPowDef)),
				By(LeftIdentityOn, grp, x, PowIn))
			a.Step(
				"one more factor of x, reassociated past x ^ m",
				func(b *Argument, ih Fact) {
					b.Show(
						"regroup x * (x ^ m * x ^ n)",
						Simp(Fwd(nat_arith.AddLeftSucClause), Fwd(comm_monoid.MonoidPowDef)),
						ih.Rw(),
						By(AssocOn, grp, x, PowIn))
				})
		}),
})}

// PowPow — in a group on a set a power of a power is the power at the
// product of the exponents: by induction on n, m · suc(n) being m + m · n,
// which PowAdd above splits without commuting a factor.
var PowPow = powPowThm{family.Add(registry.ProofEntry{
	Name: "PowPow",
	Key:  "prop_4f8bae77df45f6c7",
	Build: GroupOn.Law(Statement{
		Binders: "∀x:A. ∀m n:num.",
		Hypotheses: []string{
			"x ∈ G.carrier",
		},
		Conclusion: "monoid_pow(G.mul, G.one, monoid_pow(G.mul, G.one, x, m), n) = " +
			"monoid_pow(G.mul, G.one, x, m * n)",
	},
		func(a *Argument, grp GroupFact[on.G], x *Member[A, on.G], m, n *Expr[Nat]) {
			a.Induct(n)
			a.Base(
				"both powers are the identity, m · 0 being 0",
				Simp(Fwd(nat_arith.MulZero), Fwd(comm_monoid.MonoidPowDef)),
				Refl())
			a.Step(
				"one more factor of x ^ m, and m · suc(n) = m + m · n",
				func(b *Argument, ih Fact) {
					b.Show(
						"exponents add",
						Simp(Fwd(nat_arith.MulSuc), Fwd(comm_monoid.MonoidPowDef)),
						ih.Rw(),
						By(PowAdd, grp, x))
				})
		}),
})}

// OnePow — every power of the identity is the identity: by induction
// on n, one more factor of the identity changing nothing.
var OnePow = onePowThm{family.Add(registry.ProofEntry{
	Name: "OnePow",
	Key:  "prop_708646cca2201f9c",
	Build: GroupOn.Law("∀n:num. monoid_pow(G.mul, G.one, G.one, n) = G.one",
		func(a *Argument, grp GroupFact[on.G], n *Expr[Nat]) {
			a.Induct(n)
			a.Base(
				"G.one ^ 0 is the identity",
				Simp(Fwd(comm_monoid.MonoidPowDef)),
				Refl())
			a.Step(
				"one more factor of the identity changes nothing",
				func(b *Argument, ih Fact) {
					b.Show(
						"the identity times itself is the identity",
						Simp(Fwd(comm_monoid.MonoidPowDef)),
						ih.Rw(),
						By(LeftIdentityOn, grp, OneIn))
				})
		}),
})}

// PowInSubgroupIffDivides — the exponents at which the powers of a member
// g lie in a subgroup H are the multiples of a single exponent d. When
// some positive power of g lies in H, d is the least exponent of one: a
// multiple d · k gives (g ^ d) ^ k, a power of a member of H; and when
// g ^ n lies in H, n is d · q + r with r below d, and g ^ r is
// G.inv((g ^ d) ^ q) * g ^ n, again in H, so r is not positive. When no
// positive power of g lies in H, d is 0: only g ^ 0, the identity, does.
var PowInSubgroupIffDivides = powInSubgroupIffDividesThm{family.Add(registry.ProofEntry{
	Name: "PowInSubgroupIffDivides",
	Key:  "prop_c85bed32dea7bd1",
	Build: GroupOn.Law(Statement{
		Binders: "∀g:A. ∀H:set(A).",
		Hypotheses: []string{
			"g ∈ G.carrier",
			"subgroup(G, H)",
		},
		Conclusion: "∃d:num. ∀n:num. monoid_pow(G.mul, G.one, g, n) ∈ H ⇔ d ∣ n",
	},
		func(a *Argument, grp GroupFact[on.G], g *Member[A, on.G], H *Expr[Set[A]], subgroup Fact) {
			onH := a.Have(
				"H is a group under the operations of G",
				"group_on(restrict_group(G, H))",
				By(grp, subgroup, SubgroupGroupOn))
			a.Cases(a.Term("∃k:num. 0 < k ∧ monoid_pow(G.mul, G.one, g, k) ∈ H"))
			a.When(
				"some positive power of g lies in H: d is the least exponent of one",
				func(b *Argument, some Fact) {
					d, least := b.ObtainAs[Nat](
						"take the least positive d with g ^ d in H",
						"∃d:num. "+
							"    0 < d ∧ "+
							"    monoid_pow(G.mul, G.one, g, d) ∈ H ∧ "+
							"    (∀m:num. m < d ⇒ ¬(0 < m ∧ monoid_pow(G.mul, G.one, g, m) ∈ H))",
						By(
							some,
							nat_order.WellOrdering.At(
								b.TermAs[Set[Nat]]("λk:num. 0 < k ∧ monoid_pow(G.mul, G.one, g, k) ∈ H"))))
					parts := b.Conjuncts(
						least,
						"d is positive",
						"g ^ d lies in H",
						"no power of g at a positive exponent below d does")
					dm := b.MemberOf[on.Any](b.TermAs[A]("monoid_pow(G.mul, G.one, g, d)"), parts[1])
					b.Take(d)
					n := b.FixAs[Nat]("n")
					b.Iff()
					b.Backward(
						"at a multiple d · k of d, g ^ n is (g ^ d) ^ k, a power of a member of H",
						func(c *Argument, divides Fact) {
							k, multiple := c.UnpackAs[Nat](c.Unfolded(divides, nat_divides.DividesFactor), "k")
							c.Show(
								"g ^ (d · k) is (g ^ d) ^ k",
								multiple.Rw(),
								Simp(Rev(PowPow)),
								By(PowIn.Read(onH).At(dm, k)))
						})
					b.Forward(
						"when g ^ n lies in H, the remainder of n by d puts a power of g in H below d",
						func(c *Argument, inH Fact) {
							division := c.Have(
								"n is a multiple of d plus its remainder",
								"n = d * div(n, d) + rem(n, d)",
								ByArith(parts[0], nat_div_mod.Division.At(n, d)))
							split := c.Have(
								"so g ^ n is (g ^ d) ^ div(n, d) * g ^ rem(n, d)",
								"monoid_pow(G.mul, G.one, g, n) = "+
									"monoid_pow(G.mul, G.one, monoid_pow(G.mul, G.one, g, d), div(n, d)) * "+
									"monoid_pow(G.mul, G.one, g, rem(n, d))",
								Simp(Fwd(PowPow), Rev(PowAdd)),
								division.RwRev(),
								Basic())
							cancelled := c.Have(
								"and the factor (g ^ d) ^ div(n, d) cancels",
								"G.inv(monoid_pow(G.mul, G.one, monoid_pow(G.mul, G.one, g, d), div(n, d))) * "+
									"monoid_pow(G.mul, G.one, g, n) = "+
									"monoid_pow(G.mul, G.one, g, rem(n, d))",
								split.Rw(),
								By(grp, g, InvMulCancelLeftOn, PowIn))
							remainderIn := c.Have(
								"so g ^ rem(n, d) lies in H, a product of members of H",
								"monoid_pow(G.mul, G.one, g, rem(n, d)) ∈ H",
								cancelled.RwRev(),
								By(MulIn.Read(onH), InvIn.Read(onH), PowIn.Read(onH), inH, parts[1]))
							c.Show(
								"the remainder lies below d, so it is 0, and d divides n",
								By(
									remainderIn,
									parts[2].At(c.TermAs[Nat]("rem(n, d)")),
									parts[0],
									nat_div_mod.Division.At(n, d),
									nat_divides.DividesMod,
									nat_order.PosIffNonzero))
						})
				})
			a.Otherwise(
				"no positive power of g lies in H: d is 0",
				func(b *Argument, none Fact) {
					b.Take(b.TermAs[Nat]("0"))
					b.FixAs[Nat]("n")
					b.Iff()
					b.Forward(
						"g ^ n lies in H only when n is 0, which 0 divides",
						func(c *Argument, inH Fact) {
							c.Show(
								"n is not positive, so it is 0",
								By(none, inH, nat_order.PosIffNonzero, nat_divides.DividesZero))
						})
					b.Backward(
						"0 divides only 0, and g ^ 0 is the identity, which H holds",
						func(c *Argument, divides Fact) {
							c.Show(
								"g ^ 0 is the identity of G",
								By(divides, subgroup, nat_divides.ZeroDivides, comm_monoid.MonoidPowDef, SubgroupOne))
						})
				})
		}),
})}
