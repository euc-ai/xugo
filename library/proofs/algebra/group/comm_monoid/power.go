// power.go — the power of an element: x ^ n is x combined with itself
// n times, the identity when n = 0; the set of an element's powers; the
// laws of exponents; and a map that keeps the identity and the operation
// keeps powers.
//
// The power is a recursion on n and reads no carrier. Its laws are
// proved on a carrier set, the element a member — the powers of a member
// stay in the carrier (PowIn) — and each is stated beside it on the
// whole type as the view of that proof.

package comm_monoid

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/registry"
)

// MonoidPowDef — `x ^ n`: x combined with itself n times, by recursion
// on n. The operation and the identity are the constant's first two
// arguments and are implicit: under a law of this chapter they are the
// structure's components, and in a chapter bound to an instance they
// are the instance's.
var MonoidPowDef = monoidPowDefThm{family.Define(registry.DefEntry{
	Name:     "MonoidPowDef",
	Key:      "prop_c8e9070c193dc23e",
	Const:    "monoid_pow",
	Type:     "(A → A → A) → A → A → num → A",
	Implicit: []string{"op", "e"},
	Notation: "x ^ n",
	Equations: []string{
		"∀op:(A → A → A). ∀e x:A. monoid_pow(op, e, x, 0) = e",
		"∀op:(A → A → A). ∀e x:A. ∀n:num. monoid_pow(op, e, x, suc(n)) = op(x, monoid_pow(op, e, x, n))",
	},
})}

// MonoidPowersDef — `monoid_powers(op, e, x)`: the set of the powers of
// x, x ^ n for every n. It is the denominators of a localization at one
// element. The operation and the identity are implicit, as the power's
// are.
var MonoidPowersDef = monoidPowersDefThm{family.Define(registry.DefEntry{
	Name:     "MonoidPowersDef",
	Key:      "prop_9162d37694d873f6",
	Const:    "monoid_powers",
	Type:     "(A → A → A) → A → A → set(A)",
	Implicit: []string{"op", "e"},
	Equations: []string{
		"∀op:(A → A → A). ∀e x:A. monoid_powers(op, e, x) = {monoid_pow(op, e, x, n) | n:num | ⊤}",
	},
	Deps: []registry.EntryLike{MonoidPowDef},
})}

// PowIn — the powers of a member stay in the carrier: by induction on n,
// the identity at 0 and one more factor of x at the step.
var PowIn = powInThm{family.Add(registry.ProofEntry{
	Name: "PowIn",
	Key:  "prop_22e6e9718a5354ff",
	Build: CommMonoidOn.Law(Statement{
		Binders: "∀x:A. ∀n:num.",
		Hypotheses: []string{
			"x ∈ c",
		},
		Conclusion: "x ^ n ∈ c",
	},
		func(a *Argument, monoid CommMonoidFact[on.C], x *Member[A, on.C], n *Expr[Nat]) {
			a.Induct(n)
			a.Base(
				"x ^ 0 is the identity, which lies in c",
				Simp(Fwd(MonoidPowDef)),
				By(IdentityIn, monoid))
			a.Step(
				"x ^ suc(n) is x combined with x ^ n, both in c",
				func(d *Argument, ih Fact) {
					d.Do(Simp(Fwd(MonoidPowDef)), By(OpIn, monoid, x, ih))
				})
		}),
})}

// PowOneOn — the first power is the element: 1 is the successor of 0,
// and x combined with the identity is x.
var PowOneOn = powOneOnThm{family.Add(registry.ProofEntry{
	Name: "PowOneOn",
	Key:  "prop_7802ef4a78759a8d",
	Build: CommMonoidOn.Law(Statement{
		Binders: "∀x:A.",
		Hypotheses: []string{
			"x ∈ c",
		},
		Conclusion: "x ^ 1 = x",
	},
		func(a *Argument, monoid CommMonoidFact[on.C], x *Member[A, on.C]) {
			a.Show(
				"x ^ suc(0) is x combined with the identity",
				Simp(Fwd(nat_arith.OneIsSucZero)),
				Simp(Fwd(MonoidPowDef)),
				By(RightIdentityOn, monoid, x))
		}),
})}

// PowOne — PowOneOn on the whole type.
var PowOne = powOneThm{family.Add(registry.ProofEntry{
	Name:  "PowOne",
	Key:   "prop_68cd765b9626fafd",
	Build: CommMonoidAtUniverse.Law("∀x:A. x ^ 1 = x", PowOneOn),
})}

// PowTwoOn — the square: 2 is the successor of 1, so x ^ 2 is x combined
// with its first power.
var PowTwoOn = powTwoOnThm{family.Add(registry.ProofEntry{
	Name: "PowTwoOn",
	Key:  "prop_78d32b0ab369bef7",
	Build: CommMonoidOn.Law(Statement{
		Binders: "∀x:A.",
		Hypotheses: []string{
			"x ∈ c",
		},
		Conclusion: "x ^ 2 = op(x, x)",
	},
		func(a *Argument, monoid CommMonoidFact[on.C], x *Member[A, on.C]) {
			first := a.Have(
				"the first power is x",
				"x ^ 1 = x",
				By(PowOneOn, monoid, x))
			a.Show(
				"x ^ suc(1) is x combined with x ^ 1",
				Simp(Fwd(nat_arith.Two)),
				Simp(Fwd(MonoidPowDef)),
				first.Rw(),
				Basic())
		}),
})}

// PowTwo — PowTwoOn on the whole type.
var PowTwo = powTwoThm{family.Add(registry.ProofEntry{
	Name:  "PowTwo",
	Key:   "prop_f9bd0b37f52360f6",
	Build: CommMonoidAtUniverse.Law("∀x:A. x ^ 2 = op(x, x)", PowTwoOn),
})}

// PowAddOn — exponents add: by induction on m, the identity at m = 0
// and, at the step, one more factor of x reassociated past x ^ m.
var PowAddOn = powAddOnThm{family.Add(registry.ProofEntry{
	Name: "PowAddOn",
	Key:  "prop_c81ab9b28498be07",
	Build: CommMonoidOn.Law(Statement{
		Binders: "∀x:A. ∀m n:num.",
		Hypotheses: []string{
			"x ∈ c",
		},
		Conclusion: "x ^ (m + n) = op(x ^ m, x ^ n)",
	},
		func(a *Argument, monoid CommMonoidFact[on.C], x *Member[A, on.C], m, n *Expr[Nat]) {
			a.Induct(m)
			a.Base(
				"at m = 0 the sum is n, and x ^ 0 is the identity",
				Simp(Fwd(nat_arith.AddLeftZeroClause), Fwd(MonoidPowDef)),
				By(LeftIdentityOn, monoid, x, PowIn))
			a.Step(
				"one more factor of x, reassociated past x ^ m",
				func(d *Argument, ih Fact) {
					d.Do(Simp(
						Fwd(nat_arith.AddLeftSucClause),
						Fwd(MonoidPowDef)), ih.Rw(), By(AssocOn, monoid, x, PowIn))
				})
		}),
})}

// PowAdd — PowAddOn on the whole type.
var PowAdd = powAddThm{family.Add(registry.ProofEntry{
	Name:  "PowAdd",
	Key:   "prop_140d79063f16f4b3",
	Build: CommMonoidAtUniverse.Law("∀x:A. ∀m n:num. x ^ (m + n) = op(x ^ m, x ^ n)", PowAddOn),
})}

// MulPowOn — a power of a product is the product of the powers: by
// induction on n; the step regroups four factors, which the operation's
// commuting allows.
var MulPowOn = mulPowOnThm{family.Add(registry.ProofEntry{
	Name: "MulPowOn",
	Key:  "prop_8a4a8431f8352457",
	Build: CommMonoidOn.Law(Statement{
		Binders: "∀x y:A. ∀n:num.",
		Hypotheses: []string{
			"x ∈ c",
			"y ∈ c",
		},
		Conclusion: "op(x, y) ^ n = op(x ^ n, y ^ n)",
	},
		func(a *Argument, monoid CommMonoidFact[on.C], x, y *Member[A, on.C], n *Expr[Nat]) {
			a.Induct(n)
			a.Base(
				"all three powers are the identity, and the identity combined with itself is the identity",
				Simp(Fwd(MonoidPowDef)),
				By(LeftIdentityOn, monoid, IdentityIn))
			a.Step(
				"one more factor of x and of y, each moved beside its own power",
				func(d *Argument, ih Fact) {
					pass := d.Have(
						"y passes x ^ n",
						"op(y, op(x ^ n, y ^ n)) = op(x ^ n, op(y, y ^ n))",
						By(LeftCommOn, monoid, x, y, PowIn))
					d.Do(Simp(Fwd(MonoidPowDef)), ih.Rw(),
						CalcEq(
							Leg(
								d.TermAs[A]("op(x, op(y, op(x ^ n, y ^ n)))"),
								"reassociate",
								By(AssocOn, monoid, x, y, PowIn, OpIn)),
							Leg(
								d.TermAs[A]("op(x, op(x ^ n, op(y, y ^ n)))"),
								"y passes x ^ n",
								pass.Rw(),
								Basic()),
							FinalLeg(
								"reassociate back",
								By(AssocOn, monoid, x, y, PowIn, OpIn))))
				})
		}),
})}

// MulPow — MulPowOn on the whole type.
var MulPow = mulPowThm{family.Add(registry.ProofEntry{
	Name:  "MulPow",
	Key:   "prop_e37bb25e15842e4a",
	Build: CommMonoidAtUniverse.Law("∀x y:A. ∀n:num. op(x, y) ^ n = op(x ^ n, y ^ n)", MulPowOn),
})}

// PowPowOn — a power of a power is the power at the product of the
// exponents: by induction on n, m · suc(n) being m + m · n, which
// PowAddOn splits.
var PowPowOn = powPowOnThm{family.Add(registry.ProofEntry{
	Name: "PowPowOn",
	Key:  "prop_6f282bba924468d8",
	Build: CommMonoidOn.Law(Statement{
		Binders: "∀x:A. ∀m n:num.",
		Hypotheses: []string{
			"x ∈ c",
		},
		Conclusion: "(x ^ m) ^ n = x ^ (m * n)",
	},
		func(a *Argument, monoid CommMonoidFact[on.C], x *Member[A, on.C], m, n *Expr[Nat]) {
			a.Induct(n)
			a.Base(
				"both powers are the identity, m · 0 being 0",
				Simp(Fwd(nat_arith.MulZero), Fwd(MonoidPowDef)),
				Refl())
			a.Step(
				"one more factor of x ^ m, and m · suc(n) = m + m · n",
				func(d *Argument, ih Fact) {
					d.Do(Simp(Fwd(nat_arith.MulSuc), Fwd(MonoidPowDef)), ih.Rw(), By(PowAddOn, monoid, x))
				})
		}),
})}

// PowPow — PowPowOn on the whole type.
var PowPow = powPowThm{family.Add(registry.ProofEntry{
	Name:  "PowPow",
	Key:   "prop_5a462f4a71358e06",
	Build: CommMonoidAtUniverse.Law("∀x:A. ∀m n:num. (x ^ m) ^ n = x ^ (m * n)", PowPowOn),
})}

// IdentityPowOn — every power of the identity is the identity.
var IdentityPowOn = identityPowOnThm{family.Add(registry.ProofEntry{
	Name: "IdentityPowOn",
	Key:  "prop_1638f65c3543a7e2",
	Build: CommMonoidOn.Law("∀n:num. e ^ n = e",
		func(a *Argument, monoid CommMonoidFact[on.C], n *Expr[Nat]) {
			a.Induct(n)
			a.Base(
				"e ^ 0 is the identity",
				Simp(Fwd(MonoidPowDef)),
				Refl())
			a.Step(
				"one more factor of the identity changes nothing",
				func(d *Argument, ih Fact) {
					d.Do(Simp(Fwd(MonoidPowDef)), ih.Rw(), By(LeftIdentityOn, monoid, IdentityIn))
				})
		}),
})}

// IdentityPow — IdentityPowOn on the whole type.
var IdentityPow = identityPowThm{family.Add(registry.ProofEntry{
	Name:  "IdentityPow",
	Key:   "prop_3de15a3f7911bd26",
	Build: CommMonoidAtUniverse.Law("∀n:num. e ^ n = e", IdentityPowOn),
})}

// PowInverseOn — the powers of an inverse pair are an inverse pair: if x
// combined with y is the identity, so is xⁿ combined with yⁿ, the power
// of the product, which is a power of the identity.
var PowInverseOn = powInverseOnThm{family.Add(registry.ProofEntry{
	Name: "PowInverseOn",
	Key:  "prop_307b4431a1c7f317",
	Build: CommMonoidOn.Law(Statement{
		Binders: "∀x y:A. ∀n:num.",
		Hypotheses: []string{
			"x ∈ c",
			"y ∈ c",
			"op(x, y) = e",
		},
		Conclusion: "op(x ^ n, y ^ n) = e",
	},
		func(a *Argument, monoid CommMonoidFact[on.C], x, y *Expr[A], n *Expr[Nat], given Fact) {
			parts := a.Conjuncts(
				given,
				"x lies in c",
				"so does y",
				"x combined with y is the identity")
			xm, ym := a.MemberOf[on.C](x, parts[0]), a.MemberOf[on.C](y, parts[1])
			a.Show(
				"xⁿ combined with yⁿ is (x combined with y)ⁿ = eⁿ = e",
				CalcEq(
					Leg(
						a.TermAs[A]("op(x, y) ^ n"),
						"the product of the powers is the power of the product",
						By(MulPowOn, monoid, xm, ym)),
					Leg(
						a.TermAs[A]("e ^ n"),
						"x combined with y is the identity",
						parts[2].Rw(),
						Basic()),
					FinalLeg(
						"a power of the identity is the identity",
						By(IdentityPowOn, monoid)),
				))
		}),
})}

// PowInverse — PowInverseOn on the whole type.
var PowInverse = powInverseThm{family.Add(registry.ProofEntry{
	Name: "PowInverse",
	Key:  "prop_be4f5ac7b5e53d3a",
	Build: CommMonoidAtUniverse.Law(Statement{
		Binders: "∀x y:A. ∀n:num.",
		Hypotheses: []string{
			"op(x, y) = e",
		},
		Conclusion: "op(x ^ n, y ^ n) = e",
	}, PowInverseOn),
})}

// MapPow — a map that keeps the identity and carries the operation to a
// second operation carries powers to powers: h(x ^ n) is h(x) to the
// n-th power under the second operation. By induction on n; neither
// operation need commute or associate, so the statement asks for no
// structure, only the two equations.
var MapPow = mapPowThm{family.Add(registry.ProofEntry{
	Name: "MapPow",
	Key:  "prop_82140bfc29eaa8ca",
	Build: family.Theorem(Statement{
		Binders: "∀op:(A → A → A). ∀e:A. ∀op₂:(B → B → B). ∀e₂:B. ∀h:(A → B). ∀x:A. ∀n:num.",
		Hypotheses: []string{
			"h(e) = e₂",
			"∀u v:A. h(op(u, v)) = op₂(h(u), h(v))",
		},
		Conclusion: "h(x ^ n) = monoid_pow(op₂, e₂, h(x), n)",
	},
		func(a *Argument, op, e, op2, e2, h, x, n Term, hom Fact) {
			parts := a.Conjuncts(
				hom,
				"h keeps the identity",
				"h carries the operation")
			identity, carries := parts[0], parts[1]
			// The two powers live on two carriers. A definition used as a
			// Simp rule rewrites at its own type letter, so the second
			// carrier's clauses read it pinned at B.
			sourceZeroPower := a.Have(
				"x ^ 0 is the first identity",
				"x ^ 0 = e",
				Simp(Fwd(MonoidPowDef)),
				Refl())
			targetZeroPower := a.Have(
				"and h(x) to the 0-th power the second",
				"monoid_pow(op₂, e₂, h(x), 0) = e₂",
				Simp(Fwd(MonoidPowDef.Inst[B]())),
				Refl())
			a.Induct(n)
			a.Base(
				"both zeroth powers are identities, and h keeps the identity",
				sourceZeroPower.Rw(),
				targetZeroPower.Rw(),
				By(identity))
			a.Step(
				"h carries the one more factor of x to one more factor of h(x)",
				func(d *Argument, ih Fact) {
					sourceSuccessorPower := d.Have(
						"x ^ suc(n) is x combined with x ^ n",
						"x ^ suc(n) = op(x, x ^ n)",
						Simp(Fwd(MonoidPowDef)),
						Refl())
					targetSuccessorPower := d.Have(
						"and likewise on the second carrier",
						"monoid_pow(op₂, e₂, h(x), suc(n)) = op₂(h(x), monoid_pow(op₂, e₂, h(x), n))",
						Simp(Fwd(MonoidPowDef.Inst[B]())),
						Refl())
					product := d.Have(
						"h carries this product",
						"h(op(x, x ^ n)) = op₂(h(x), h(x ^ n))",
						By(carries))
					d.Do(sourceSuccessorPower.Rw(), targetSuccessorPower.Rw(), product.Rw(), ih.Rw(), Basic())
				})
		}),
})}
