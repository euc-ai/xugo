// laws.go — the pointwise laws: what the ring's algebra says at every
// index.
//
// Each law is one scalar law read entrywise. A proof opens the two
// sides pointwise (function extensionality), unfolds the vector
// operation to the scalar one it reads, and closes by the scalar law at
// the entry; the ring's sub-structure the law belongs to — the additive
// monoid or group, the multiplicative monoid — is projected once at the
// top of a body and cited beside the law.
//
// The additive laws, the subtraction law and the four laws of the
// scaling are proved so once, at a ring on a set c for sequences with
// every entry in c and scalars in c (the …On laws at the end of the
// file); the whole-type law is its carrier law's view at 𝕌, where every
// entry and every scalar lies.
//
// The additive laws assemble into the vectors' own additive group, and
// a law stated below it is read there instead — at the group chapter's
// laws, applied to vectors whole rather than to their entries. The laws
// assemble a second time, with the membership laws, into the module the
// n-vectors form on the set of them (ModuleOn); neither assembly reads an
// entry.

package vec_space

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/abelian_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/registry"
)

// AddComm — vector addition commutes: AddCommOn on the whole type.
var AddComm = addCommThm{family.Add(registry.ProofEntry{
	Name:  "AddComm",
	Key:   "prop_e9cc87b1b0caa0a3",
	Build: comm_ring.CommRingAtUniverse.Law("∀u v:(num → A). u + v = v + u", AddCommOn),
})}

// AddAssoc — vector addition associates, in the monoid's orientation:
// AddAssocOn on the whole type.
var AddAssoc = addAssocThm{family.Add(registry.ProofEntry{
	Name:  "AddAssoc",
	Key:   "prop_27cb1e3228d493fe",
	Build: comm_ring.CommRingAtUniverse.Law("∀u v w:(num → A). u + (v + w) = (u + v) + w", AddAssocOn),
})}

// AddLeftZero — the zero vector is a left identity: AddLeftZeroOn on the
// whole type.
var AddLeftZero = addLeftZeroThm{family.Add(registry.ProofEntry{
	Name:  "AddLeftZero",
	Key:   "prop_6cfbf1c08019e595",
	Build: comm_ring.CommRingAtUniverse.Law("∀u:(num → A). vec_zero + u = u", AddLeftZeroOn),
})}

// AddLeftNeg — the pointwise negation is a left inverse: AddLeftNegOn on
// the whole type.
var AddLeftNeg = addLeftNegThm{family.Add(registry.ProofEntry{
	Name:  "AddLeftNeg",
	Key:   "prop_f75d704b0ff52903",
	Build: comm_ring.CommRingAtUniverse.Law("∀u:(num → A). -u + u = vec_zero", AddLeftNegOn),
})}

// SmulAddLeft — the scalar action distributes over vector addition:
// SmulAddLeftOn on the whole type.
var SmulAddLeft = smulAddLeftThm{family.Add(registry.ProofEntry{
	Name: "SmulAddLeft",
	Key:  "prop_b7ff8442a5ad1255",
	Build: comm_ring.CommRingAtUniverse.Law(
		"∀c:A. ∀u v:(num → A). c • (u + v) = c • u + c • v", SmulAddLeftOn),
})}

// SmulAddRight — a sum of scalars acts as the sum of the actions:
// SmulAddRightOn on the whole type.
var SmulAddRight = smulAddRightThm{family.Add(registry.ProofEntry{
	Name: "SmulAddRight",
	Key:  "prop_5737a6dc7011d200",
	Build: comm_ring.CommRingAtUniverse.Law(
		"∀c d:A. ∀u:(num → A).(c + d) • u = c • u + d • u", SmulAddRightOn),
})}

// SmulMul — a product of scalars acts as the composite of the actions:
// SmulMulOn on the whole type.
var SmulMul = smulMulThm{family.Add(registry.ProofEntry{
	Name: "SmulMul",
	Key:  "prop_e6418d532de4f3f8",
	Build: comm_ring.CommRingAtUniverse.Law(
		"∀c d:A. ∀u:(num → A).(c * d) • u = c • (d • u)", SmulMulOn),
})}

// SmulOne — the ring's one acts as the identity: SmulOneOn on the whole
// type.
var SmulOne = smulOneThm{family.Add(registry.ProofEntry{
	Name:  "SmulOne",
	Key:   "prop_1069a14b1696de02",
	Build: comm_ring.CommRingAtUniverse.Law("∀u:(num → A). R.one • u = u", SmulOneOn),
})}

// NegIsSmul — the negation of a vector is the scalar action at minus
// one. A subspace is asked only to hold the sum and the scalar action,
// and this law is what makes it closed under differences as well.
var NegIsSmul = negIsSmulThm{family.Add(registry.ProofEntry{
	Name: "NegIsSmul",
	Key:  "prop_c53dd9ccb4ad6813",
	Build: comm_ring.CommRing.Law("∀u:(num → A). -u = -R.one • u",
		func(a *Argument, ring Fact, u Term) {
			a.Show(
				"entry by entry, the negated entry is minus one times the entry",
				Funext(),
				Unfold(VecNegDef),
				Unfold(VecScalarMulDef),
				By(comm_ring.NegOneMul, ring))
		}),
})}

// SmulZero — every scalar acts on the zero vector as the zero vector.
var SmulZero = smulZeroThm{family.Add(registry.ProofEntry{
	Name: "SmulZero",
	Key:  "prop_ad4f6d94cb6e7297",
	Build: comm_ring.CommRing.Law("∀c:A. c • vec_zero = vec_zero",
		func(a *Argument, ring Fact, c Term) {
			a.Show(
				"entry by entry, the scalar times zero is zero",
				Funext(),
				Unfold(VecScalarMulDef),
				Unfold(VecZeroDef),
				By(comm_ring.MulRightZero, ring))
		}),
})}

// ZeroSmul — the zero scalar acts on every vector as the zero vector.
var ZeroSmul = zeroSmulThm{family.Add(registry.ProofEntry{
	Name: "ZeroSmul",
	Key:  "prop_6abba6c8b3b8c476",
	Build: comm_ring.CommRing.Law("∀u:(num → A). R.zero • u = vec_zero",
		func(a *Argument, ring Fact, u Term) {
			a.Show(
				"entry by entry, zero times the entry is zero",
				Funext(),
				Unfold(VecScalarMulDef),
				Unfold(VecZeroDef),
				By(comm_ring.MulLeftZero, ring))
		}),
})}

// AbelianGroup — the vectors over any commutative ring form an abelian
// group under pointwise addition: the four laws above, assembled into
// the structure predicate, so that every law of the group chapter
// applies to vectors at any carrier by citing this member.
var AbelianGroup = abelianGroupThm{family.Add(registry.ProofEntry{
	Name: "AbelianGroup",
	Key:  "prop_e12d2ab49d111917",
	Build: comm_ring.CommRing.Law("abelian_group(mk_group(vec_add, vec_zero, vec_neg, 𝕌))",
		func(a *Argument, ring Fact) {
			a.Do(Unfold(abelian_group.AbelianGroup), Unfold(group.Group), SplitConjAll(
				Case(
					"associativity",
					By(AddAssoc, ring)),
				Case(
					"the zero vector is a left identity",
					By(AddLeftZero, ring)),
				Case(
					"the pointwise negation is a left inverse",
					By(AddLeftNeg, ring)),
				Case(
					"commutativity",
					By(AddComm, ring)),
			))
		}),
})}

// ModuleOn — the n-vectors over any commutative ring form a module on the
// set of them, at every n: the ring and the n-vectors are each one record
// value, the membership laws close the set under the three operations and
// the scaling, and the pointwise laws above are the axioms, holding for
// all vectors and so for the n-vectors. The proof unfolds the module,
// reads every part off the two packed values, unfolds the group on a set
// it conjoins, and closes one Case per conjunct of the two definitions,
// in their order; the first conjunct, the scalars as a ring on 𝕌, is the
// hypothesis read at 𝕌.
var ModuleOn = moduleOnThm{family.Add(registry.ProofEntry{
	Name: "ModuleOn",
	Key:  "prop_43f654159c2a9d99",
	Build: comm_ring.CommRing.Law("∀n:num. "+
		"    module_on(restrict_ring(R, 𝕌), "+
		"        mk_module(vec_add, vec_zero, vec_neg, vec_scalar_mul, {u:(num → A) | vec⟨n⟩(u)}))",
		func(a *Argument, ring Fact, n Term) {
			a.Do(Unfold(module.ModuleOn), Unfold(group.GroupOn), SplitConjAll(
				Case(
					"the scalars are a ring on the whole type",
					By(ring, comm_ring.CommRingOnUniverse)),
				Case(
					"the zero vector is an n-vector",
					BySets(VecZero)),
				Case(
					"a sum of n-vectors is an n-vector",
					BySets(VecAdd, ring)),
				Case(
					"so is a negation",
					BySets(VecNeg, ring)),
				Case(
					"addition associates",
					By(AddAssoc, ring)),
				Case(
					"the zero vector is a left identity",
					By(AddLeftZero, ring)),
				Case(
					"the negation is a left inverse",
					By(AddLeftNeg, ring)),
				Case(
					"addition commutes",
					By(AddComm, ring)),
				Case(
					"a scaled n-vector is an n-vector",
					BySets(VecSmul, ring)),
				Case(
					"a scalar distributes over a sum of vectors",
					By(SmulAddLeft, ring)),
				Case(
					"a sum of scalars distributes over a vector",
					By(SmulAddRight, ring)),
				Case(
					"scaling by a product is scaling twice",
					By(SmulMul, ring)),
				Case(
					"and one fixes every vector",
					By(SmulOne, ring)),
			))
		}),
})}

// SubAddNeg — subtraction is addition of the negation: SubAddNegOn on
// the whole type.
var SubAddNeg = subAddNegThm{family.Add(registry.ProofEntry{
	Name:  "SubAddNeg",
	Key:   "prop_c92df2d758420df8",
	Build: comm_ring.CommRingAtUniverse.Law("∀u v:(num → A). u - v = u + -v", SubAddNegOn),
})}

// SubEqZero — a difference vanishes exactly when the two vectors
// agree.
//
// Both directions come out of one group law. The difference is u plus
// the negation of v, so its vanishing says that u cancels -v; the
// summand that cancels an element is that element's negation and
// nothing else, so u is -(-v), and double negation leaves v.
var SubEqZero = subEqZeroThm{family.Add(registry.ProofEntry{
	Name: "SubEqZero",
	Key:  "prop_89aba6781e5c937d",
	Build: comm_ring.CommRing.Law("∀u v:(num → A). u - v = vec_zero ⇔ u = v",
		func(a *Argument, ring Fact, u, v *Expr[Fun[Nat, A]]) {
			vectors := abelian_group.Group.Read(AbelianGroup.Read(ring))

			// That group's components, at which the two laws below are
			// read: pointwise addition, the zero vector, pointwise
			// negation.
			vectorGroup := a.TermAs[group.GroupOps[Fun[Nat, A]]]("mk_group(vec_add, vec_zero, vec_neg, 𝕌)")
			negV := a.TermAs[Fun[Nat, A]]("-v")

			a.Show(
				"the difference is u + -v, the summand cancelling -v is -(-v), and that is v",
				Simp(Fwd(SubAddNeg)),
				By(vectors, group.InvUnique.At(vectorGroup, u, negV), group.InvInv.At(vectorGroup, v)))
		}),
})}

// AddSubCancel — what was subtracted, added back. The difference is a
// sum with the negation, so commuting and regrouping brings u beside
// its own negation; that inverse pair is the zero vector, which adds
// nothing to v. Nothing here is read entrywise: the additive laws above
// say everything the calculation uses.
var AddSubCancel = addSubCancelThm{family.Add(registry.ProofEntry{
	Name: "AddSubCancel",
	Key:  "prop_44955f1fdf3a570f",
	Build: comm_ring.CommRing.Law("∀u v:(num → A). u + (v - u) = v",
		func(a *Argument, ring Fact, u, v Term) {
			a.Show(
				"bring u next to its negation, and what the sum leaves is v",
				CalcEq(
					Leg(
						a.Term("u + (v + -u)"),
						"the difference is v with u negated",
						Congr(),
						By(SubAddNeg, ring)),
					Leg(
						a.Term("u + (-u + v)"),
						"where those two summands commute",
						Congr(),
						By(AddComm, ring)),
					Leg(
						a.Term("(u + -u) + v"),
						"regrouped, u stands beside its own negation",
						By(AddAssoc, ring)),
					Leg(
						a.Term("(-u + u) + v"),
						"an inverse pair either way round",
						Congr(),
						By(AddComm, ring)),
					Leg(
						a.Term("vec_zero + v"),
						"and an inverse pair is the zero vector",
						Congr(),
						By(AddLeftNeg, ring)),
					FinalLeg(
						"which is a left identity",
						By(AddLeftZero, ring)),
				))
		}),
})}

// AddSubCancelRight — what was added, subtracted again. The difference
// is a sum with the negation, so regrouping brings v beside its own
// negation; that inverse pair is the zero vector, which adds nothing to
// u. Like AddSubCancel, it is the additive laws above and nothing read
// entrywise.
var AddSubCancelRight = addSubCancelRightThm{family.Add(registry.ProofEntry{
	Name: "AddSubCancelRight",
	Key:  "prop_684f76dc92627521",
	Build: comm_ring.CommRing.Law("∀u v:(num → A).(u + v) - v = u",
		func(a *Argument, ring Fact, u, v *Arrow[Nat, A]) {
			a.Show(
				"bring v next to its negation, and what the sum leaves is u",
				CalcEq(
					Leg(
						a.Term("(u + v) + -v"),
						"subtracting v adds its negation",
						By(SubAddNeg, ring)),
					Leg(
						a.Term("u + (v + -v)"),
						"regrouped, v stands beside its negation",
						Symm(),
						By(AddAssoc, ring)),
					Leg(
						a.Term("u + (-v + v)"),
						"an inverse pair either way round",
						Congr(),
						By(AddComm, ring)),
					Leg(
						a.Term("u + vec_zero"),
						"and an inverse pair is the zero vector",
						Congr(),
						By(AddLeftNeg, ring)),
					Leg(
						a.Term("vec_zero + u"),
						"which commutes to the front",
						By(AddComm, ring)),
					FinalLeg(
						"where it is a left identity",
						By(AddLeftZero, ring)),
				))
		}),
})}

// AddCommOn — vector addition commutes at a ring on a set c, for
// sequences with every entry in c: at every index, one sum of two
// members of c, commuted. A ring on c gives its laws on c alone, so each
// law at the carrier asks every entry of its sequences to lie in c.
var AddCommOn = addCommOnThm{family.Add(registry.ProofEntry{
	Name: "AddCommOn",
	Key:  "prop_3558bb6651098623",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀u v:(num → A).",
		Hypotheses: []string{
			"∀i:num. u(i) ∈ R.carrier",
			"∀i:num. v(i) ∈ R.carrier",
		},
		Conclusion: "u + v = v + u",
	},
		func(a *Argument, ring comm_ring.CommRingFact[on.R], u, v *Arrow[Nat, A], entries Fact) {
			a.Show(
				"entry by entry, the two sides are one sum of members of c with its summands exchanged",
				Funext(),
				Simp(Fwd(VecAddDef)),
				By(entries, comm_monoid.CommOn.Read(comm_ring.AddMonoidOn.Read(ring))))
		}),
})}

// AddAssocOn — vector addition associates at a ring on c, for sequences
// with every entry in c.
var AddAssocOn = addAssocOnThm{family.Add(registry.ProofEntry{
	Name: "AddAssocOn",
	Key:  "prop_b7fbad544a8b4b0f",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀u v w:(num → A).",
		Hypotheses: []string{
			"∀i:num. u(i) ∈ R.carrier",
			"∀i:num. v(i) ∈ R.carrier",
			"∀i:num. w(i) ∈ R.carrier",
		},
		Conclusion: "u + (v + w) = u + v + w",
	},
		func(a *Argument, ring comm_ring.CommRingFact[on.R], u, v, w *Arrow[Nat, A], entries Fact) {
			a.Show(
				"entry by entry, the two sides are one triple sum of members of c regrouped",
				Funext(),
				Simp(Fwd(VecAddDef)),
				By(entries, comm_monoid.AssocOn.Read(comm_ring.AddMonoidOn.Read(ring))))
		}),
})}

// AddLeftZeroOn — the zero vector is a left identity at a ring on c, for
// a sequence with every entry in c.
var AddLeftZeroOn = addLeftZeroOnThm{family.Add(registry.ProofEntry{
	Name: "AddLeftZeroOn",
	Key:  "prop_c1ecca211051d660",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀u:(num → A).",
		Hypotheses: []string{
			"∀i:num. u(i) ∈ R.carrier",
		},
		Conclusion: "vec_zero + u = u",
	},
		func(a *Argument, ring comm_ring.CommRingFact[on.R], u *Arrow[Nat, A], entries Fact) {
			a.Show(
				"entry by entry, zero added on the left of a member of c changes nothing",
				Funext(),
				Simp(Fwd(VecAddDef), Fwd(VecZeroDef)),
				By(entries, comm_monoid.LeftIdentityOn.Read(comm_ring.AddMonoidOn.Read(ring))))
		}),
})}

// AddLeftNegOn — the pointwise negation is a left inverse at a ring on c,
// for a sequence with every entry in c.
var AddLeftNegOn = addLeftNegOnThm{family.Add(registry.ProofEntry{
	Name: "AddLeftNegOn",
	Key:  "prop_54643770623ef510",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀u:(num → A).",
		Hypotheses: []string{
			"∀i:num. u(i) ∈ R.carrier",
		},
		Conclusion: "-u + u = vec_zero",
	},
		func(a *Argument, ring comm_ring.CommRingFact[on.R], u *Arrow[Nat, A], entries Fact) {
			additive := abelian_group.GroupOn.Read(comm_ring.AddGroupOn.Read(ring))
			a.Show(
				"entry by entry, a member of c added to its negation is zero",
				Funext(),
				Simp(Fwd(VecAddDef), Fwd(VecNegDef), Fwd(VecZeroDef)),
				By(entries, group.LeftInverseOn.Read(additive)))
		}),
})}

// SubAddNegOn — subtraction is addition of the negation at a ring on c,
// for sequences with every entry in c: the ring's subtraction axiom on c,
// read at every index.
var SubAddNegOn = subAddNegOnThm{family.Add(registry.ProofEntry{
	Name: "SubAddNegOn",
	Key:  "prop_1ab65b257d3e8308",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀u v:(num → A).",
		Hypotheses: []string{
			"∀i:num. u(i) ∈ R.carrier",
			"∀i:num. v(i) ∈ R.carrier",
		},
		Conclusion: "u - v = u + -v",
	},
		func(a *Argument, ring comm_ring.CommRingFact[on.R], u, v *Arrow[Nat, A], entries Fact) {
			a.Show(
				"entry by entry, the difference of two members of c is the first plus the negated second",
				Funext(),
				Simp(Fwd(VecSubDef), Fwd(VecAddDef), Fwd(VecNegDef)),
				By(entries, comm_ring.SubAddNegOn.Read(ring)))
		}),
})}

// SmulAddLeftOn — scaling distributes over the sum at a ring on c, for a
// scalar in c and sequences with every entry in c: the ring's left
// distributive law on c, read at every index.
var SmulAddLeftOn = smulAddLeftOnThm{family.Add(registry.ProofEntry{
	Name: "SmulAddLeftOn",
	Key:  "prop_f81900884822ef6c",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀a:A. ∀u v:(num → A).",
		Hypotheses: []string{
			"a ∈ R.carrier",
			"∀i:num. u(i) ∈ R.carrier",
			"∀i:num. v(i) ∈ R.carrier",
		},
		Conclusion: "a • (u + v) = a • u + a • v",
	},
		func(
			arg *Argument,
			ring comm_ring.CommRingFact[on.R],
			a *Expr[A],
			u, v *Arrow[Nat, A],
			members Fact,
		) {
			arg.Show(
				"entry by entry, a member of c times a sum of two members of c distributes",
				Funext(),
				Simp(Fwd(VecScalarMulDef), Fwd(VecAddDef)),
				By(members, comm_ring.LeftDistribOn.Read(ring)))
		}),
})}

// SmulAddRightOn — a sum of scalars in c scales as the sum of the
// scalings, for a sequence with every entry in c: the ring's right
// distributive law on c, read at every index.
var SmulAddRightOn = smulAddRightOnThm{family.Add(registry.ProofEntry{
	Name: "SmulAddRightOn",
	Key:  "prop_bb01477b8cb025c5",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀a b:A. ∀u:(num → A).",
		Hypotheses: []string{
			"a ∈ R.carrier",
			"b ∈ R.carrier",
			"∀i:num. u(i) ∈ R.carrier",
		},
		Conclusion: "(a + b) • u = a • u + b • u",
	},
		func(
			arg *Argument,
			ring comm_ring.CommRingFact[on.R],
			a, b *Expr[A],
			u *Arrow[Nat, A],
			members Fact,
		) {
			arg.Show(
				"entry by entry, a sum of two members of c times a member of c distributes",
				Funext(),
				Simp(Fwd(VecScalarMulDef), Fwd(VecAddDef)),
				By(members, comm_ring.RightDistribOn.Read(ring)))
		}),
})}

// SmulMulOn — scaling by a product of scalars in c is scaling twice, for a
// sequence with every entry in c: at every index, associativity of the
// ring's product on c.
var SmulMulOn = smulMulOnThm{family.Add(registry.ProofEntry{
	Name: "SmulMulOn",
	Key:  "prop_3a7af314e6988469",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀a b:A. ∀u:(num → A).",
		Hypotheses: []string{
			"a ∈ R.carrier",
			"b ∈ R.carrier",
			"∀i:num. u(i) ∈ R.carrier",
		},
		Conclusion: "a * b • u = a • b • u",
	},
		func(
			arg *Argument,
			ring comm_ring.CommRingFact[on.R],
			a, b *Expr[A],
			u *Arrow[Nat, A],
			members Fact,
		) {
			arg.Show(
				"entry by entry, one triple product of members of c regrouped",
				Funext(),
				Simp(Fwd(VecScalarMulDef)),
				By(members, comm_monoid.AssocOn.Read(comm_ring.MulMonoidOn.Read(ring))))
		}),
})}

// SmulOneOn — scaling by one fixes a sequence with every entry in c: at
// every index, one is a left identity of the ring's product on c.
var SmulOneOn = smulOneOnThm{family.Add(registry.ProofEntry{
	Name: "SmulOneOn",
	Key:  "prop_ed5d66a3fa96418e",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀u:(num → A).",
		Hypotheses: []string{
			"∀i:num. u(i) ∈ R.carrier",
		},
		Conclusion: "R.one • u = u",
	},
		func(a *Argument, ring comm_ring.CommRingFact[on.R], u *Arrow[Nat, A], entries Fact) {
			a.Show(
				"entry by entry, one times a member of c is that member",
				Funext(),
				Simp(Fwd(VecScalarMulDef)),
				By(entries, comm_monoid.LeftIdentityOn.Read(comm_ring.MulMonoidOn.Read(ring))))
		}),
})}
